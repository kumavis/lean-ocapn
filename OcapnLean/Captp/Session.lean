import OcapnLean.Captp.Bootstrap
import OcapnLean.Captp.Run
import OcapnLean.Crypto
import OcapnLean.Netlayer.Tcp
import OcapnLean.Syrup.Extended

/-!
# Per-connection CapTP session

A session-aware handler that owns the per-connection state (handshake
flag, abort flag, our location, a per-session Ed25519 keypair, and an
export table) and knows how to respond to the top-level `op:*`
operations the test suite exercises.

This module covers:

  * `op:start-session` (with **real Ed25519 signatures**, both
    directions — we sign our `acceptable-location` and verify the
    client's),
  * `op:deliver to=<desc:export 0> [fetch SWISS] _ <resolve-me-desc>`:
    the proper *promise-style* `fetch` protocol — we allocate a fresh
    export position, bind it to the swissnum-named handler, and reply
    with `<op:deliver to=<desc:export RM> [fulfill <desc:import-object N>] …>`,
  * `op:deliver to=<desc:export N>` (N > 0): route to the export
    table, optionally fulfilling a resolve-me-desc with the handler's
    return value,
  * The **sturdyref enlivener** — the bootstrap object at
    `gi02I1qghIwPiKGKleCQAOhpy3ZtYRpB` — which parses an
    `<ocapn-sturdyref …>` argument, looks up the peer's host/port out
    of its hints dict, and spawns a task that opens a fresh outbound
    TCP connection and performs an `op:start-session` against it.
    This is what the crossed-hellos tests need to set up a second leg.

The richer subset (promise pipelining, three-party handoffs, GC
refcounts, `op:listen`, full crossed-hellos detection) extends
naturally from this scaffold but is intentionally out of scope here.
-/

namespace OcapnLean.Captp.Session

open OcapnLean OcapnLean.Captp OcapnLean.Captp.Bootstrap OcapnLean.Syrup
open Std.Net

/-! ## Constants and small helpers. -/

/-- The captp-version this implementation speaks. -/
def captpVersion : String := "1.0"

def opStartSessionSym : List UInt8 := "op:start-session".toUTF8.toList
def opDeliverSym      : List UInt8 := "op:deliver".toUTF8.toList
def opAbortSym        : List UInt8 := "op:abort".toUTF8.toList
def descExportSym     : List UInt8 := "desc:export".toUTF8.toList
def descImportObjSym  : List UInt8 := "desc:import-object".toUTF8.toList
def myLocationSym     : List UInt8 := "my-location".toUTF8.toList
def fetchSym          : List UInt8 := "fetch".toUTF8.toList
def fulfillSym        : List UInt8 := "fulfill".toUTF8.toList
def sturdyrefSym      : List UInt8 := "ocapn-sturdyref".toUTF8.toList
def peerSym           : List UInt8 := "ocapn-peer".toUTF8.toList
def tcpTestingOnlySym : List UInt8 := "tcp-testing-only".toUTF8.toList

/-- Convert a `ByteArray` to `List UInt8` for use in `ValueExt.bytes`. -/
@[inline] def baToList (ba : ByteArray) : List UInt8 := ba.toList

/-- Convert a `List UInt8` back to `ByteArray` for crypto calls. -/
@[inline] def listToBa (xs : List UInt8) : ByteArray := ByteArray.mk xs.toArray

/-! ## Wire builders. -/

/-- gcrypt-style `(public-key (ecc (curve Ed25519) (flags eddsa) (q
PK_BYTES)))`. The test suite's `CapTPPublicKey.from_syrup_record`
matches exactly this shape. -/
def buildSessionPubkey (pkBytes : List UInt8) : ValueExt :=
  .list
    [ .sym "public-key".toUTF8.toList
    , .list
        [ .sym "ecc".toUTF8.toList
        , .list [.sym "curve".toUTF8.toList, .sym "Ed25519".toUTF8.toList]
        , .list [.sym "flags".toUTF8.toList, .sym "eddsa".toUTF8.toList]
        , .list [.sym "q".toUTF8.toList, .bytes pkBytes]
        ]
    ]

/-- gcrypt-style `(sig-val (eddsa (r R_BYTES) (s S_BYTES)))`. Ed25519
signatures are 64 bytes total: the first 32 are `r`, the second 32
are `s`. -/
def buildLocationSig (sig : ByteArray) : ValueExt :=
  let r := sig.extract 0 32 |>.toList
  let s := sig.extract 32 64 |>.toList
  .list
    [ .sym "sig-val".toUTF8.toList
    , .list
        [ .sym "eddsa".toUTF8.toList
        , .list [.sym "r".toUTF8.toList, .bytes r]
        , .list [.sym "s".toUTF8.toList, .bytes s]
        ]
    ]

/-- The syrup bytes the per-session secret key signs to produce
`acceptable-location-sig`. Per the spec the payload is the syrup
encoding of `<my-location <acceptable-location-record>>`. -/
def locationSigningPayload (loc : ValueExt) : ByteArray :=
  listToBa (Encode.encodeExt (.record (.sym myLocationSym) [loc]))

/-- Build the `op:start-session` reply with real Ed25519 fields. -/
def buildStartSessionReply
    (pkBytes : List UInt8) (sig : ByteArray) (location : ValueExt) : ValueExt :=
  .record (.sym opStartSessionSym)
    [ .str captpVersion.toUTF8.toList
    , buildSessionPubkey pkBytes
    , location
    , buildLocationSig sig
    ]

/-- Build an `op:abort` with the given reason. -/
def buildAbort (reason : String) : ValueExt :=
  .record (.sym opAbortSym) [.str reason.toUTF8.toList]

/-- `<desc:export N>`. -/
def buildDescExport (pos : Nat) : ValueExt :=
  .record (.sym descExportSym) [.int (Int.ofNat pos)]

/-- `<desc:import-object N>`. -/
def buildDescImportObj (pos : Nat) : ValueExt :=
  .record (.sym descImportObjSym) [.int (Int.ofNat pos)]

/-- Build `<op:deliver <desc:export to> [fulfill <desc:import-object new>] False False>`. -/
def buildFulfillDeliver (toPos : Nat) (newImportPos : Nat) : ValueExt :=
  .record (.sym opDeliverSym)
    [ buildDescExport toPos
    , .list [.sym fulfillSym, buildDescImportObj newImportPos]
    , .bool false
    , .bool false
    ]

/-! ## Per-session handler type and state.

`SessionHandler` is what an export-position is bound to: it receives
the `args` of an inbound `op:deliver` and may return a value to
fulfill the caller's `resolve-me-desc` (or `none` for void).
-/

abbrev SessionHandler := List ValueExt → IO (Option ValueExt)

/-- Per-connection mutable state. -/
structure State where
  handshakeDone : IO.Ref Bool
  aborted       : IO.Ref Bool
  /-- Our `acceptable-location` value. -/
  ourLocation   : ValueExt
  /-- This session's Ed25519 public key (32 bytes). -/
  sessionPubkey : ByteArray
  /-- This session's Ed25519 secret key (64 bytes, libsodium combined). -/
  sessionSecret : ByteArray
  /-- The bootstrap registry shared by all sessions. -/
  registry      : Registry
  /-- Per-session export table. `exports[i]` is bound to wire
  position `i + 1`; position 0 is reserved for the bootstrap fetch
  handler and is not stored here. -/
  exports       : IO.Ref (Array SessionHandler)

namespace State

/-- Fresh session state for a new inbound connection. A new Ed25519
keypair is generated per connection (matching the spec's "per-session
keypair" rule). -/
def create (ourLocation : ValueExt) (registry : Registry) : IO State := do
  let handshakeDone ← IO.mkRef false
  let aborted       ← IO.mkRef false
  let (pk, sk)      ← Crypto.ed25519Keypair
  let exports       ← IO.mkRef (#[] : Array SessionHandler)
  pure { handshakeDone, aborted, ourLocation,
         sessionPubkey := pk, sessionSecret := sk,
         registry, exports }

/-- Allocate a fresh export position bound to `h`. Returns the wire
position (1-indexed). -/
def exportAllocate (st : State) (h : SessionHandler) : IO Nat := do
  let arr ← st.exports.get
  st.exports.set (arr.push h)
  pure (arr.size + 1)

/-- Look up the handler at wire position `pos`. Position 0 is the
bootstrap, which is dispatched specially and returns `none` here. -/
def exportLookup (st : State) (pos : Nat) : IO (Option SessionHandler) := do
  if pos = 0 then return none
  let arr ← st.exports.get
  return arr[pos - 1]?

end State

/-! ## Wire parsers. -/

/-- Recognise the captp-version in an incoming `op:start-session`. -/
def extractStartSessionVersion (v : ValueExt) : Option (List UInt8) :=
  match v with
  | .record (.sym lbl) (.str version :: _) =>
      if lbl = opStartSessionSym then some version else none
  | _ => none

/-- Pull the 4 fields out of an `op:start-session` record:
    `(version, pubkey-record, location, sig-record)`. -/
def extractStartSession (v : ValueExt) :
    Option (List UInt8 × ValueExt × ValueExt × ValueExt) :=
  match v with
  | .record (.sym lbl) [.str ver, pk, loc, sig] =>
      if lbl = opStartSessionSym then some (ver, pk, loc, sig) else none
  | _ => none

/-- Extract the 32-byte EdDSA pubkey `q` from a gcrypt-shaped
`(public-key (ecc … (q PK)))` record. -/
def extractPubkey : ValueExt → Option (List UInt8)
  | .list [_, .list [_, _, _, .list [_, .bytes q]]] => some q
  | _ => none

/-- Extract the 64-byte signature (`r ++ s`) from a gcrypt-shaped
`(sig-val (eddsa (r R) (s S)))` record. -/
def extractSig : ValueExt → Option (List UInt8)
  | .list [_, .list [_, .list [_, .bytes r], .list [_, .bytes s]]] =>
      some (r ++ s)
  | _ => none

/-- Verify that `sig` is a valid Ed25519 signature by `pk` over the
syrup encoding of `<my-location <loc>>`. Returns `false` if any
structural extraction fails (mismatched shapes, wrong byte lengths). -/
def verifyClientLocationSig
    (pkVal : ValueExt) (loc : ValueExt) (sigVal : ValueExt) : Bool :=
  match extractPubkey pkVal, extractSig sigVal with
  | some pkBytes, some sigBytes =>
      if pkBytes.length = 32 && sigBytes.length = 64 then
        Crypto.ed25519Verify
          (listToBa pkBytes)
          (locationSigningPayload loc)
          (listToBa sigBytes)
      else false
  | _, _ => false

/-- Parse `<op:deliver to args answer-pos resolve-me-desc>`. -/
def parseOpDeliver (v : ValueExt) :
    Option (ValueExt × List ValueExt × ValueExt × ValueExt) :=
  match v with
  | .record (.sym lbl) [to, .list args, ap, rmd] =>
      if lbl = opDeliverSym then some (to, args, ap, rmd) else none
  | _ => none

/-- Extract `N` from `<desc:export N>`. Returns `none` for negatives
or non-record shapes. -/
def extractExportPos (v : ValueExt) : Option Nat :=
  match v with
  | .record (.sym lbl) [.int n] =>
      if lbl = descExportSym && n ≥ 0 then some n.toNat else none
  | _ => none

/-- Extract `N` from `<desc:import-object N>`. -/
def extractImportObjPos (v : ValueExt) : Option Nat :=
  match v with
  | .record (.sym lbl) [.int n] =>
      if lbl = descImportObjSym && n ≥ 0 then some n.toNat else none
  | _ => none

/-! ## ASCII / dict / sturdyref parsing. -/

/-- An ASCII digit, as `UInt8`. -/
@[inline] def isAsciiDigit (b : UInt8) : Bool :=
  0x30 ≤ b && b ≤ 0x39

/-- Parse a non-empty run of ASCII decimal digits to a `Nat`. Returns
`none` on empty input or on any non-digit byte. -/
def parseAsciiNat (bs : List UInt8) : Option Nat :=
  if bs.isEmpty then none
  else
    let rec go : List UInt8 → Nat → Option Nat
      | [],        acc => some acc
      | b :: rest, acc =>
        if isAsciiDigit b then go rest (acc * 10 + (b.toNat - 0x30))
        else none
    go bs 0

/-- Parse an IPv4 dotted-quad like `"127.0.0.1"` (as UTF-8 bytes) into
its four octets. Returns `none` on any malformed segment or
out-of-range octet. -/
def parseIPv4 (s : List UInt8) : Option IPv4Addr := Id.run do
  let parts := (String.fromUTF8! ⟨s.toArray⟩).splitOn "."
  if parts.length ≠ 4 then return none
  let mut octs : Array UInt8 := #[]
  for p in parts do
    match p.toNat? with
    | none => return none
    | some n =>
      if n > 255 then return none
      octs := octs.push n.toUInt8
  match octs.toList with
  | [a, b, c, d] => return some { octets := #v[a, b, c, d] }
  | _            => return none

/-- Look up a string key in a syrup dict, returned as a flat list of
`[k1, v1, k2, v2, …]`. Returns the matching value's payload bytes
when the value is a string or symbol; `none` otherwise. -/
partial def lookupHintBytes : List ValueExt → List UInt8 → Option (List UInt8)
  | .str k :: v :: rest, key =>
      if k = key then
        match v with
        | .str bs => some bs
        | .sym bs => some bs
        | _       => none
      else lookupHintBytes rest key
  | .sym k :: v :: rest, key =>
      if k = key then
        match v with
        | .str bs => some bs
        | .sym bs => some bs
        | _       => none
      else lookupHintBytes rest key
  | _, _ => none

/-- Parse an `<ocapn-sturdyref <ocapn-peer 'tcp-testing-only ADDR HINTS> SWISS>`
into a `(SocketAddress, swiss-bytes)` pair. Only `tcp-testing-only`
is supported here. -/
def parseSturdyref (v : ValueExt) : Option (SocketAddress × List UInt8) :=
  match v with
  | .record (.sym sLbl)
      [ .record (.sym pLbl) [.sym transport, _addr, hintsVal]
      , .bytes swiss
      ] =>
    if sLbl ≠ sturdyrefSym then none
    else if pLbl ≠ peerSym then none
    else if transport ≠ tcpTestingOnlySym then none
    else
      let entries : Option (List ValueExt) :=
        match hintsVal with
        | .dict es => some es
        | .list es => some es
        | _        => none
      match entries with
      | none => none
      | some es =>
        match lookupHintBytes es "host".toUTF8.toList,
              lookupHintBytes es "port".toUTF8.toList with
        | some hostBs, some portBs =>
          match parseIPv4 hostBs, parseAsciiNat portBs with
          | some ip, some n =>
            if n < 65536 then
              some ({ addr := ip, port := n.toUInt16 } |> SocketAddress.v4, swiss)
            else none
          | _, _ => none
        | _, _ => none
  | _ => none

/-! ## Outbound op:start-session.

When the enlivener gets a sturdyref it can resolve, it spawns one of
these. We do a *one-shot* outbound handshake — connect, send a
freshly-signed `op:start-session`, and detach. The receiving side's
state machine takes over from there (the crossed-hellos tests handle
the rest). -/

/-- Open a TCP connection to `addr`, generate a per-session keypair,
sign our `ourLocation`, and write a valid `op:start-session` frame.
Does **not** wait for or close the connection — we leave it for the
peer to drive or shut down. -/
def outboundStartSession (addr : SocketAddress) (ourLocation : ValueExt) :
    IO Unit := do
  let net ← Netlayer.Tcp.connect addr
  let (pk, sk) ← Crypto.ed25519Keypair
  let payload := locationSigningPayload ourLocation
  let sig     := Crypto.ed25519Sign sk payload
  let frame   := buildStartSessionReply (baToList pk) sig ourLocation
  let bytes   := Encode.encodeExt frame
  net.send (ByteArray.mk bytes.toArray)
  IO.eprintln "[session][outbound] sent op:start-session"

/-! ## Bootstrap handlers — the ones that need session context.

The simple value-returning handlers live in `OcapnLean.Captp.Bootstrap`;
the **enlivener** needs the connection's `ourLocation` (to sign its
outbound location) so we construct it here. -/

/-- The sturdyref-enlivener handler: receives `[<ocapn-sturdyref …>]`,
parses the embedded peer, and spawns an outbound `op:start-session`
in a dedicated task. The caller used `resolve-me-desc=False`, so we
return `none` (no reply). -/
def mkEnlivenerHandler (st : State) : SessionHandler := fun args => do
  match args with
  | [sref] =>
    match parseSturdyref sref with
    | some (addr, _swiss) =>
      let loc := st.ourLocation
      let _ ← IO.asTask (prio := .dedicated) do
        try
          outboundStartSession addr loc
        catch e =>
          IO.eprintln s!"[session][enlivener] outbound failed: {e}"
      return none
    | none =>
      IO.eprintln "[session][enlivener] could not parse sturdyref"
      return none
  | _ =>
    IO.eprintln s!"[session][enlivener] expected 1 arg, got {args.length}"
    return none

/-- Convert one of `OcapnLean.Captp.Bootstrap`'s value-returning
handlers (`List ValueExt → IO ValueExt`) into a `SessionHandler`. -/
def liftBootstrapHandler (h : Bootstrap.Handler) : SessionHandler := fun args => do
  let v ← h args
  return some v

/-- Pick the handler to bind for a given swissnum. Returns `none` if
the swissnum isn't recognised. -/
def resolveSwissnum (st : State) (swiss : Swissnum) : Option SessionHandler :=
  if swiss = sturdyrefEnlivenerSwiss then
    some (mkEnlivenerHandler st)
  else
    (st.registry.lookup swiss).map liftBootstrapHandler

/-! ## Top-level frame dispatcher. -/

/-- Handle an incoming `op:deliver` after the handshake completes.
Returns the optional reply frame. -/
def dispatchOpDeliver (st : State) (frame : ValueExt) : IO (Option ValueExt) := do
  match parseOpDeliver frame with
  | none =>
    IO.eprintln s!"[session] post-handshake frame is not op:deliver; ignoring"
    return none
  | some (toVal, args, _ap, rmd) =>
    match extractExportPos toVal with
    | none =>
      IO.eprintln "[session] op:deliver to non-<desc:export …>; ignoring"
      return none
    | some 0 =>
      -- Bootstrap object: only `fetch` is supported.
      match args with
      | [.sym method, .bytes swiss] =>
        if method ≠ fetchSym then
          IO.eprintln s!"[session] bootstrap method {String.fromUTF8! ⟨method.toArray⟩} not supported"
          return none
        match resolveSwissnum st swiss with
        | none =>
          IO.eprintln "[session] fetch: unknown swissnum"
          return none
        | some h =>
          let newPos ← st.exportAllocate h
          match extractImportObjPos rmd with
          | none =>
            IO.eprintln "[session] fetch without resolve-me-desc; allocated but not replying"
            return none
          | some rmPos =>
            IO.eprintln s!"[session] fetch resolved → export pos {newPos}, fulfilling rm={rmPos}"
            return some (buildFulfillDeliver rmPos newPos)
      | _ =>
        IO.eprintln "[session] bootstrap call with unsupported args shape"
        return none
    | some n =>
      match ← st.exportLookup n with
      | none =>
        IO.eprintln s!"[session] op:deliver to unknown export position {n}"
        return none
      | some h =>
        let result ← h args
        match result, extractImportObjPos rmd with
        | some v, some rmPos =>
          -- Caller wants a fulfill back. For now we only wrap plain
          -- values; if the handler chose to return its own
          -- import-object descriptor it just rides through unchanged.
          return some (.record (.sym opDeliverSym)
            [ buildDescExport rmPos
            , .list [.sym fulfillSym, v]
            , .bool false
            , .bool false
            ])
        | _, _ => return none

/-- Top-level dispatcher for one frame. -/
def dispatch (st : State) (frame : ValueExt) : IO (Option ValueExt) := do
  if ← st.aborted.get then return none

  -- Handshake phase: we expect the first frame to be op:start-session.
  if !(← st.handshakeDone.get) then
    match extractStartSession frame with
    | some (version, clientPk, clientLoc, clientSig) =>
      if version ≠ captpVersion.toUTF8.toList then
        st.aborted.set true
        return some (buildAbort s!"unsupported captp version: {String.fromUTF8! ⟨version.toArray⟩}")
      else if ¬ verifyClientLocationSig clientPk clientLoc clientSig then
        IO.eprintln s!"[session] client signature failed verification; aborting"
        st.aborted.set true
        return some (buildAbort "invalid acceptable-location signature")
      else
        st.handshakeDone.set true
        let payload := locationSigningPayload st.ourLocation
        let sig     := Crypto.ed25519Sign st.sessionSecret payload
        let reply   := buildStartSessionReply (baToList st.sessionPubkey) sig st.ourLocation
        IO.eprintln s!"[session] handshake OK, replying with signed op:start-session"
        return some reply
    | none =>
      IO.eprintln s!"[session] first frame is not op:start-session; aborting"
      st.aborted.set true
      return some (buildAbort "expected op:start-session as first message")

  -- Post-handshake routing.
  dispatchOpDeliver st frame

/-- Run a session: build state, dispatch frames in a loop. -/
def run (conn : FramedConn) (registry : Registry) (ourLocation : ValueExt) :
    IO Unit := do
  let st ← State.create ourLocation registry
  runHandler conn (dispatch st)

end OcapnLean.Captp.Session
