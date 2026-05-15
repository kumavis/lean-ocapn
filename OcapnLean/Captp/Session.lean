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

  * **Crossed-hellos resolution** (Spec §"Crossed Hellos Resolution"):
    every outbound session our enlivener spawns is registered in a
    server-wide `OutboundRegistry` keyed by the remote peer's
    `(transport, address)`. When an inbound `op:start-session`
    arrives whose `acceptable-location` matches an entry, we compute
    each side's Public Identifier (`SHA-256(SHA-256(syrup(pubkey)))`)
    and abort the lower one.

The richer subset (promise pipelining, three-party handoffs, GC
refcounts, `op:listen`) extends naturally from this scaffold but is
intentionally out of scope here.
-/

namespace OcapnLean.Captp.Session

open OcapnLean OcapnLean.Captp OcapnLean.Captp.Bootstrap OcapnLean.Syrup
open Std.Net

/-! ## Constants and small helpers. -/

/-- The captp-version this implementation speaks. -/
def captpVersion : String := "1.0"

def opStartSessionSym  : List UInt8 := "op:start-session".toUTF8.toList
def opDeliverSym       : List UInt8 := "op:deliver".toUTF8.toList
def opAbortSym         : List UInt8 := "op:abort".toUTF8.toList
def opListenSym        : List UInt8 := "op:listen".toUTF8.toList
def descExportSym      : List UInt8 := "desc:export".toUTF8.toList
def descAnswerSym      : List UInt8 := "desc:answer".toUTF8.toList
def descImportObjSym   : List UInt8 := "desc:import-object".toUTF8.toList
def descImportPromiseSym : List UInt8 := "desc:import-promise".toUTF8.toList
def myLocationSym      : List UInt8 := "my-location".toUTF8.toList
def fetchSym           : List UInt8 := "fetch".toUTF8.toList
def fulfillSym         : List UInt8 := "fulfill".toUTF8.toList
def breakSym           : List UInt8 := "break".toUTF8.toList
def sturdyrefSym       : List UInt8 := "ocapn-sturdyref".toUTF8.toList
def peerSym            : List UInt8 := "ocapn-peer".toUTF8.toList
def tcpTestingOnlySym  : List UInt8 := "tcp-testing-only".toUTF8.toList

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

/-- `<desc:import-promise N>`. -/
def buildDescImportPromise (pos : Nat) : ValueExt :=
  .record (.sym descImportPromiseSym) [.int (Int.ofNat pos)]

/-- Build `<op:deliver <desc:export to> [fulfill <desc:import-object new>] False False>`. -/
def buildFulfillDeliver (toPos : Nat) (newImportPos : Nat) : ValueExt :=
  .record (.sym opDeliverSym)
    [ buildDescExport toPos
    , .list [.sym fulfillSym, buildDescImportObj newImportPos]
    , .bool false
    , .bool false
    ]

/-- Build `<op:deliver <desc:export to> [fulfill V] False False>`. Used
when a value-returning handler successfully produces `V` and the
caller asked us to deliver the resolution to its export `to`. -/
def buildFulfillValue (toPos : Nat) (v : ValueExt) : ValueExt :=
  .record (.sym opDeliverSym)
    [ buildDescExport toPos
    , .list [.sym fulfillSym, v]
    , .bool false
    , .bool false
    ]

/-- Build `<op:deliver <desc:export to> args False False>` — a plain
deliver-only message used by callback-style handlers (e.g. the
greeter, which delivers `["Hello"]` to the reference the caller
passed as its first arg). -/
def buildDeliverOnly (toPos : Nat) (args : List ValueExt) : ValueExt :=
  .record (.sym opDeliverSym)
    [ buildDescExport toPos
    , .list args
    , .bool false
    , .bool false
    ]

/-- Build `<op:deliver <desc:export to> [break r] False False>` — the
broken-promise notification (mirror of `buildFulfillValue`). -/
def buildBreakValue (toPos : Nat) (r : ValueExt) : ValueExt :=
  .record (.sym opDeliverSym)
    [ buildDescExport toPos
    , .list [.sym breakSym, r]
    , .bool false
    , .bool false
    ]

/-! ## Outbound session registry.

The server tracks every outbound session it has *initiated* (currently
only via the sturdyref enlivener) so that an inbound
`op:start-session` from the same remote peer can be recognised as a
crossed-hellos race and resolved per the spec.

The key is the `(transport, address)` pair extracted from the remote
`<ocapn-peer …>` record — that's what uniquely identifies a peer in
OCapN. The value carries the per-session pubkey we sent (needed to
compute our side's Public Identifier) and the open `FramedConn` so
the dispatcher can send `op:abort` on the right wire if our outbound
turns out to be the loser of a race.
-/

/-- A peer's identity for crossed-hellos matching: `(transport, address)`. -/
abbrev PeerKey := List UInt8 × List UInt8

/-- A still-open outbound session: the keypair we used to sign the
outbound `op:start-session`, the `FramedConn` we wrote it on, and an
abort flag set when crossed-hellos resolution kills it. -/
structure PendingOutbound where
  ourPubkey : ByteArray
  conn      : FramedConn
  aborted   : IO.Ref Bool

/-- Server-wide map of `PeerKey → PendingOutbound`. -/
abbrev OutboundRegistry := IO.Ref (List (PeerKey × PendingOutbound))

namespace OutboundRegistry

def create : IO OutboundRegistry := IO.mkRef []

def add (r : OutboundRegistry) (k : PeerKey) (v : PendingOutbound) : IO Unit :=
  r.modify ((k, v) :: ·)

def lookup (r : OutboundRegistry) (k : PeerKey) : IO (Option PendingOutbound) := do
  let xs ← r.get
  return (xs.find? (·.1 = k)).map (·.2)

def remove (r : OutboundRegistry) (k : PeerKey) : IO Unit :=
  r.modify (·.filter (·.1 ≠ k))

end OutboundRegistry

/-! ## Per-session handler type and state.

`SessionHandler` is what an export-position is bound to. It receives
the `args` of an inbound `op:deliver` plus the message's
`resolve-me-desc` (the slot the caller wants any reply delivered to)
and returns the list of frames to emit back on the connection. The
list can be empty (no observable output — useful for deliver-only
notifications and for handlers that do their work in a background
task, e.g. the sturdyref enlivener).

Common shapes a handler emits:

  * `[]`                                  no reply expected (rmd = false)
  * `[<op:deliver to=desc:export N
                  [fulfill V] _ _>]`      promise resolution to the caller
  * `[<op:deliver to=desc:export N
                  [V…] _ _>]`             generic deliver to a callback
                                          the caller passed in `args`
-/

/-- An invocation handler. Receives the message's `args`, the
caller's `resolve-me-desc`, and the caller's `answer-position`
(`some N` if pipelining was requested, `none` otherwise). Returns
the list of frames to emit on the same connection.

When the handler produces a fresh actor (e.g., the car factory
builder returns a car factory), it can optionally bind that actor's
export position to the pipelined `answerPos` via
`State.answersResolve`, so a follow-up `op:deliver
<desc:answer N>` routes directly to it. -/
abbrev SessionHandler :=
  List ValueExt → ValueExt → Option Nat → IO (List ValueExt)

/-! ## Promise machinery.

A promise lives in the same numbering space as an exported actor (so
the client can refer to it via `<desc:export N>`), but its semantics
are different: `op:listen` registers a notification target, and a
`resolver` actor flips it from pending to either fulfilled or broken.

The simplest representation that covers `op_listen`'s three tests:

  * `pending` — list of resolve-me-desc positions awaiting notification
  * `fulfilled v` — promise resolved to a value, future listens fire
                    immediately
  * `broken r` — promise broken with reason r, same idea

When the resolver actor flips the state, we drain the listener list
and emit a `<op:deliver <desc:export Lᵢ> [fulfill v] False False>`
(or `[break r]`) on the same connection for each. -/

inductive PromiseState
  | pending  (listeners : List Nat)
  | fulfilled (v : ValueExt)
  | broken   (r : ValueExt)
  deriving Inhabited

/-- An entry in a session's export table is either an exported actor
(invokable via `op:deliver`) or a promise (subject to `op:listen` /
the resolver-actor protocol). They share a single position namespace
because both kinds are referenced on the wire as `<desc:export N>`. -/
inductive Export
  | actor   (h : SessionHandler)
  | promise (state : IO.Ref PromiseState)

/-- An *answer* is the server-side state of a pipelined call. The
caller passed an `answer-position` and may follow up with messages
targeting `<desc:answer N>` before our handler has had a chance to
allocate the result actor. Three states are possible:

  * `pending` — handler hasn't completed yet (shouldn't be observed
    on a single-threaded per-connection event loop, but defined for
    completeness),
  * `resolved P` — the call returned an actor at export position `P`,
  * `broken r` — the call broke with reason `r`; future messages
    targeting this answer auto-break with the same reason. -/
inductive AnswerState
  | pending
  | resolved (exportPos : Nat)
  | broken   (r : ValueExt)

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
  exports       : IO.Ref (Array Export)
  /-- Server-wide outbound registry, shared across all sessions on
  this server. Read by the inbound handshake to spot crossed hellos;
  written by `runOutboundSession` (kicked off from the enlivener). -/
  outboundReg   : OutboundRegistry
  /-- Per-session answer table for promise pipelining. Position →
  current state. Pipelined `<desc:answer N>` recipients dispatch
  through this. -/
  answers       : IO.Ref (List (Nat × AnswerState))

namespace State

/-- Fresh session state for a new inbound connection. A new Ed25519
keypair is generated per connection (matching the spec's "per-session
keypair" rule). -/
def create (ourLocation : ValueExt) (registry : Registry)
    (outboundReg : OutboundRegistry) : IO State := do
  let handshakeDone ← IO.mkRef false
  let aborted       ← IO.mkRef false
  let (pk, sk)      ← Crypto.ed25519Keypair
  let exports       ← IO.mkRef (#[] : Array Export)
  let answers       ← IO.mkRef ([] : List (Nat × AnswerState))
  pure { handshakeDone, aborted, ourLocation,
         sessionPubkey := pk, sessionSecret := sk,
         registry, exports, outboundReg, answers }

/-- Bind an actor handler at a fresh export position. -/
def exportAllocateActor (st : State) (h : SessionHandler) : IO Nat := do
  let arr ← st.exports.get
  st.exports.set (arr.push (.actor h))
  pure (arr.size + 1)

/-- Bind a fresh promise at a new export position. Returns the
position and a ref to the promise's state. -/
def exportAllocatePromise (st : State) : IO (Nat × IO.Ref PromiseState) := do
  let stateRef ← IO.mkRef (PromiseState.pending [])
  let arr ← st.exports.get
  st.exports.set (arr.push (.promise stateRef))
  pure (arr.size + 1, stateRef)

/-- Look up the binding at wire position `pos`. Position 0 is the
bootstrap, dispatched specially. -/
def exportLookup (st : State) (pos : Nat) : IO (Option Export) := do
  if pos = 0 then return none
  let arr ← st.exports.get
  return arr[pos - 1]?

/-- Bind (or overwrite) the state of answer-position `pos`. -/
def answersResolve (st : State) (pos : Nat) (s : AnswerState) : IO Unit :=
  st.answers.modify fun xs =>
    (pos, s) :: xs.filter (·.1 ≠ pos)

/-- Look up the state of answer-position `pos`. Returns `pending` if
unknown — the same as if the caller submitted an answer position we
never saw, which lets the dispatcher emit a `break` reply uniformly. -/
def answersLookup (st : State) (pos : Nat) : IO AnswerState := do
  let xs ← st.answers.get
  return ((xs.find? (·.1 = pos)).map (·.2)).getD .pending

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

/-- Extract `N` from `<desc:answer N>` (the pipelining recipient form). -/
def extractAnswerPos (v : ValueExt) : Option Nat :=
  match v with
  | .record (.sym lbl) [.int n] =>
      if lbl = descAnswerSym && n ≥ 0 then some n.toNat else none
  | _ => none

/-- Extract a `Nat` from an op:deliver `answer-position` field, which
on the wire is either `.int N` (some N ≥ 0) or `.bool false` (no
pipelining). -/
def extractMaybeAnswerNat (v : ValueExt) : Option Nat :=
  match v with
  | .int n => if n ≥ 0 then some n.toNat else none
  | _      => none

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

/-- A peer record's address field is either a `str` or a `sym` —
extract the underlying bytes. -/
def peerAddrBytes : ValueExt → Option (List UInt8)
  | .str bs => some bs
  | .sym bs => some bs
  | _       => none

/-- Pull `(transport, address)` out of an `<ocapn-peer transport
address hints>` record — the canonical peer identity for
crossed-hellos matching. -/
def extractPeerKey (v : ValueExt) : Option PeerKey :=
  match v with
  | .record (.sym lbl) (.sym transport :: addr :: _) =>
      if lbl ≠ peerSym then none
      else (peerAddrBytes addr).map (fun a => (transport, a))
  | _ => none

/-- Parse an `<ocapn-sturdyref <ocapn-peer 'tcp-testing-only ADDR HINTS> SWISS>`
into `(SocketAddress, PeerKey, swiss-bytes)`. Only `tcp-testing-only`
is supported here. -/
def parseSturdyref (v : ValueExt) :
    Option (SocketAddress × PeerKey × List UInt8) :=
  match v with
  | .record (.sym sLbl)
      [ .record (.sym pLbl) [.sym transport, addr, hintsVal]
      , .bytes swiss
      ] =>
    if sLbl ≠ sturdyrefSym then none
    else if pLbl ≠ peerSym then none
    else if transport ≠ tcpTestingOnlySym then none
    else
      match peerAddrBytes addr with
      | none => none
      | some addrBs =>
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
                some ({ addr := ip, port := n.toUInt16 } |> SocketAddress.v4,
                      (transport, addrBs), swiss)
              else none
            | _, _ => none
          | _, _ => none
  | _ => none

/-! ## Public Identifier (spec §"Public Identifier").

The Public Identifier of a peer is `SHA-256(SHA-256(syrup(pubkey-record)))`
where `pubkey-record` is the gcrypt-shaped `(public-key (ecc …))` value.
We compare bytewise to resolve crossed hellos. -/

/-- Public Identifier of a peer given its on-wire pubkey record. -/
def publicIdentifier (pubkeyRec : ValueExt) : ByteArray :=
  Crypto.sha256d (listToBa (Encode.encodeExt pubkeyRec))

/-- Bytewise comparison of two `ByteArray`s — returns `.lt`/`.eq`/`.gt`.
Used to pick the loser of a crossed-hellos race. -/
def byteArrayCmp (a b : ByteArray) : Ordering :=
  let rec go (i : Nat) : Ordering :=
    if i ≥ a.size && i ≥ b.size then .eq
    else if i ≥ a.size then .lt
    else if i ≥ b.size then .gt
    else
      let av := a.get! i
      let bv := b.get! i
      if av < bv then .lt
      else if av > bv then .gt
      else go (i + 1)
    termination_by (a.size + b.size + 1 - i)
    decreasing_by
      simp_wf
      omega
  go 0

/-! ## Outbound op:start-session.

When the enlivener gets a sturdyref it can resolve, it spawns one of
these. The runtime:

  1. Open a TCP socket to the peer's hinted address.
  2. Generate a per-session Ed25519 keypair, sign our location, and
     write the outbound `op:start-session`.
  3. Register the open connection in the server's `OutboundRegistry`
     keyed by the peer's `(transport, address)` so the inbound
     handshake can spot a crossed-hellos race.
  4. Read frames from the peer until EOF or until we observe the
     `aborted` flag flipped by a crossed-hellos resolution. -/

partial def outboundReadLoop (conn : FramedConn) (pending : PendingOutbound) :
    IO Unit := do
  if ← pending.aborted.get then return ()
  match ← conn.readFrame with
  | none =>
    IO.eprintln "[session][outbound] EOF, closing"
    return ()
  | some f =>
    IO.eprintln s!"[session][outbound] received frame; continuing"
    -- Log only; we don't model the post-handshake outbound behaviour
    -- here. Concrete cases of interest:
    --   * `<op:start-session …>`     — peer's reply, OK
    --   * `<op:abort "Crossed …">`   — peer aborted us, drop the conn
    let _ := f
    outboundReadLoop conn pending

/-- Open a TCP connection to `addr`, perform the outbound handshake,
register the connection in `reg`, and drive the read loop until the
peer closes or we get aborted. -/
def runOutboundSession (addr : SocketAddress) (peerKey : PeerKey)
    (ourLocation : ValueExt) (reg : OutboundRegistry) : IO Unit := do
  let net ← Netlayer.Tcp.connect addr
  let conn ← FramedConn.of net
  let (pk, sk) ← Crypto.ed25519Keypair
  let aborted ← IO.mkRef false
  let pending : PendingOutbound := { ourPubkey := pk, conn, aborted }
  reg.add peerKey pending
  let payload := locationSigningPayload ourLocation
  let sig     := Crypto.ed25519Sign sk payload
  let frame   := buildStartSessionReply (baToList pk) sig ourLocation
  conn.writeFrame frame
  IO.eprintln "[session][outbound] sent op:start-session"
  try outboundReadLoop conn pending
  catch e => IO.eprintln s!"[session][outbound] read loop error: {e}"
  reg.remove peerKey
  try conn.close
  catch _ => pure ()

/-! ## Bootstrap handlers — the ones that need session context.

The simple value-returning handlers live in `OcapnLean.Captp.Bootstrap`;
the **enlivener** needs the connection's `ourLocation` (to sign its
outbound location) so we construct it here. -/

/-- The sturdyref-enlivener handler: receives `[<ocapn-sturdyref …>]`,
parses the embedded peer, and spawns an outbound `op:start-session`
in a dedicated task. The caller used `resolve-me-desc=False`, so we
emit no frames. -/
def mkEnlivenerHandler (st : State) : SessionHandler := fun args _rmd _ap => do
  match args with
  | [sref] =>
    match parseSturdyref sref with
    | some (addr, peerKey, _swiss) =>
      let loc := st.ourLocation
      let reg := st.outboundReg
      let _ ← IO.asTask (prio := .dedicated) do
        try
          runOutboundSession addr peerKey loc reg
        catch e =>
          IO.eprintln s!"[session][enlivener] outbound failed: {e}"
      return []
    | none =>
      IO.eprintln "[session][enlivener] could not parse sturdyref"
      return []
  | _ =>
    IO.eprintln s!"[session][enlivener] expected 1 arg, got {args.length}"
    return []

/-- The greeter handler. Spec contract: the caller passes one
argument — a reference to an object they want greeted — and the
greeter delivers the literal string `"Hello"` to it. The call has no
`resolve-me-desc`, only the callback in `args`. -/
def greeterHandler : SessionHandler := fun args _rmd _ap => do
  match args with
  | [cb] =>
    match extractImportObjPos cb with
    | some n =>
      return [buildDeliverOnly n [.str "Hello".toUTF8.toList]]
    | none =>
      IO.eprintln s!"[session][greeter] arg is not a <desc:import-object …>: {repr cb}"
      return []
  | _ =>
    IO.eprintln s!"[session][greeter] expected 1 arg, got {args.length}"
    return []

/-! ## Resolver and promise-resolver actors.

A *resolver* is an actor: when invoked via `op:deliver` with either
`[fulfill v]` or `[break r]`, it flips its associated promise into
the corresponding terminal state and notifies any already-listening
parties. -/

/-- Build the notification frames for the listeners of a promise that
just transitioned to a terminal `Resolution`. -/
def notifyListeners (listeners : List Nat) (resolutionTag : List UInt8)
    (value : ValueExt) : List ValueExt :=
  listeners.map fun listenerPos =>
    .record (.sym opDeliverSym)
      [ buildDescExport listenerPos
      , .list [.sym resolutionTag, value]
      , .bool false
      , .bool false
      ]

/-- The resolver actor handler: invoked by the client with
`[fulfill v]` or `[break r]`. It transitions the promise state and
returns frames to notify any registered listeners. -/
def mkResolverHandler (promiseRef : IO.Ref PromiseState) : SessionHandler :=
  fun args _rmd _ap => do
    match args with
    | [.sym tag, value] =>
      if tag = fulfillSym then
        let toNotify : List Nat ← promiseRef.modifyGet fun s =>
          match s with
          | .pending ls => (ls, .fulfilled value)
          | other       => ([], other)  -- already resolved, no-op
        return notifyListeners toNotify fulfillSym value
      else if tag = breakSym then
        let toNotify : List Nat ← promiseRef.modifyGet fun s =>
          match s with
          | .pending ls => (ls, .broken value)
          | other       => ([], other)
        return notifyListeners toNotify breakSym value
      else
        IO.eprintln s!"[session][resolver] unknown tag: {String.fromUTF8! ⟨tag.toArray⟩}"
        return []
    | _ =>
      IO.eprintln s!"[session][resolver] expected [tag, value], got {args.length} args"
      return []

/-- The promise-resolver bootstrap actor. When invoked (with no
arguments) it allocates a fresh promise plus a resolver actor, and
fulfills the caller's rmd with `[<desc:import-promise N_p>,
<desc:import-object N_r>]` so the caller can both watch the promise
(via `op:listen`) and resolve it (via `op:deliver` to the resolver). -/
def mkPromiseResolverHandler (st : State) : SessionHandler :=
  fun _args rmd _ap => do
    let (promisePos, promiseRef) ← st.exportAllocatePromise
    let resolverPos ← st.exportAllocateActor (mkResolverHandler promiseRef)
    IO.eprintln s!"[session][promise-resolver] allocated promise={promisePos} resolver={resolverPos}"
    match extractImportObjPos rmd with
    | some rmPos =>
      return [buildFulfillValue rmPos
        (.list [buildDescImportPromise promisePos,
                buildDescImportObj resolverPos])]
    | none =>
      IO.eprintln "[session][promise-resolver] no rmd; not replying"
      return []

/-! ## Car factory chain.

The test suite's `JadQ0++…` swissnum is a `Car factory builder`
actor. Invoking it (zero args) produces a `Car factory` actor.
Invoking the car factory with one arg `[color-sym, model-sym]`
produces a `Car` actor. Invoking the car (zero args) produces the
literal string `"Vroom! I am a {color} {model} car!"`.

Each step is its own freshly-allocated actor; pipelined calls flow
through `State.answers` so the client can chain messages without
waiting for resolutions. -/

def mkCarHandler (color model : List UInt8) : SessionHandler :=
  fun _args rmd _ap => do
    let s := "Vroom! I am a ".toUTF8.toList ++ color ++ " ".toUTF8.toList
             ++ model ++ " car!".toUTF8.toList
    match extractImportObjPos rmd with
    | some rmPos => return [buildFulfillValue rmPos (.str s)]
    | none       => return []

def mkCarFactoryHandler (st : State) : SessionHandler :=
  fun args rmd answerPos => do
    match args with
    | [.list [.sym color, .sym model]] =>
      let carPos ← st.exportAllocateActor (mkCarHandler color model)
      match answerPos with
      | some ap => st.answersResolve ap (.resolved carPos)
      | none => pure ()
      match extractImportObjPos rmd with
      | some rmPos => return [buildFulfillValue rmPos (buildDescImportObj carPos)]
      | none => return []
    | _ =>
      let reason : ValueExt := .str "invalid car spec".toUTF8.toList
      match answerPos with
      | some ap => st.answersResolve ap (.broken reason)
      | none => pure ()
      match extractImportObjPos rmd with
      | some rmPos => return [buildBreakValue rmPos reason]
      | none => return []

def mkCarFactoryBuilderHandler (st : State) : SessionHandler :=
  fun _args rmd answerPos => do
    let factoryPos ← st.exportAllocateActor (mkCarFactoryHandler st)
    match answerPos with
    | some ap => st.answersResolve ap (.resolved factoryPos)
    | none => pure ()
    match extractImportObjPos rmd with
    | some rmPos => return [buildFulfillValue rmPos (buildDescImportObj factoryPos)]
    | none => return []

/-- Convert one of `OcapnLean.Captp.Bootstrap`'s value-returning
handlers (`List ValueExt → IO ValueExt`) into a `SessionHandler` with
fulfill-on-rmd semantics. If `rmd` is `<desc:import-object N>`, the
handler's result `V` is wrapped in `<op:deliver <desc:export N>
[fulfill V] False False>`. Otherwise no frame is emitted. -/
def liftBootstrapHandler (h : Bootstrap.Handler) : SessionHandler :=
  fun args rmd _answerPos => do
    let v ← h args
    match extractImportObjPos rmd with
    | some rmPos => return [buildFulfillValue rmPos v]
    | none       => return []

/-- Pick the handler to bind for a given swissnum. Returns `none` if
the swissnum isn't recognised. The greeter, enlivener, and
promise-resolver need per-session context, so they're constructed
inline; pure value-returning handlers come from the
`Bootstrap.Registry`. -/
def resolveSwissnum (st : State) (swiss : Swissnum) : Option SessionHandler :=
  if swiss = sturdyrefEnlivenerSwiss then
    some (mkEnlivenerHandler st)
  else if swiss = greeterSwiss then
    some greeterHandler
  else if swiss = promiseResolverSwiss then
    some (mkPromiseResolverHandler st)
  else if swiss = carFactoryBuilderSwiss then
    some (mkCarFactoryBuilderHandler st)
  else
    (st.registry.lookup swiss).map liftBootstrapHandler

/-- Parse `<op:listen <to> <resolve-me-desc> <wants-partial>>`. -/
def parseOpListen (v : ValueExt) :
    Option (ValueExt × ValueExt × Bool) :=
  match v with
  | .record (.sym lbl) [to, rmd, .bool wp] =>
      if lbl = opListenSym then some (to, rmd, wp) else none
  | _ => none

/-! ## Top-level frame dispatcher. -/

/-- Handle an incoming `op:deliver` after the handshake completes.
Returns the frames to emit (possibly empty). -/
def dispatchOpDeliver (st : State) (frame : ValueExt) : IO (List ValueExt) := do
  match parseOpDeliver frame with
  | none =>
    IO.eprintln s!"[session] post-handshake frame is not op:deliver; ignoring"
    return []
  | some (toVal, args, apVal, rmd) =>
    let answerPos := extractMaybeAnswerNat apVal
    -- Recipient may be a `<desc:export N>` (direct call) or a
    -- `<desc:answer N>` (pipelined call). Try answer first.
    match extractAnswerPos toVal with
    | some n =>
      -- Pipelined: look up the answer's resolution.
      match ← st.answersLookup n with
      | .resolved exportPos =>
        match ← st.exportLookup exportPos with
        | some (.actor h) => do
          let frames ← h args rmd answerPos
          return frames
        | _ =>
          IO.eprintln s!"[session] pipelined op:deliver to export {exportPos} which is not an actor"
          return []
      | .broken r =>
        -- Auto-propagate the break: record this answer as broken too,
        -- and reply to rmd (if any) with a break notification.
        match answerPos with
        | some ap => st.answersResolve ap (.broken r)
        | none => pure ()
        match extractImportObjPos rmd with
        | some rmPos => return [buildBreakValue rmPos r]
        | none       => return []
      | .pending =>
        IO.eprintln s!"[session] op:deliver to pending <desc:answer {n}> — should not happen with TCP ordering"
        return []
    | none =>
    match extractExportPos toVal with
    | none =>
      IO.eprintln "[session] op:deliver to non-<desc:export …>; ignoring"
      return []
    | some 0 =>
      -- Bootstrap object: only `fetch` is supported.
      match args with
      | [.sym method, .bytes swiss] =>
        if method ≠ fetchSym then
          IO.eprintln s!"[session] bootstrap method {String.fromUTF8! ⟨method.toArray⟩} not supported"
          return []
        match resolveSwissnum st swiss with
        | none =>
          IO.eprintln "[session] fetch: unknown swissnum"
          return []
        | some h =>
          let newPos ← st.exportAllocateActor h
          match answerPos with
          | some ap => st.answersResolve ap (.resolved newPos)
          | none => pure ()
          match extractImportObjPos rmd with
          | none =>
            IO.eprintln "[session] fetch without resolve-me-desc; allocated but not replying"
            return []
          | some rmPos =>
            IO.eprintln s!"[session] fetch resolved → export pos {newPos}, fulfilling rm={rmPos}"
            return [buildFulfillDeliver rmPos newPos]
      | _ =>
        IO.eprintln "[session] bootstrap call with unsupported args shape"
        return []
    | some n =>
      match ← st.exportLookup n with
      | none =>
        IO.eprintln s!"[session] op:deliver to unknown export position {n}"
        return []
      | some (.actor h) => h args rmd answerPos
      | some (.promise _) =>
        IO.eprintln s!"[session] op:deliver to promise position {n} (pipelining via desc:export unsupported)"
        return []

/-- Handle an incoming `op:listen` after the handshake completes.
Registers the caller as a listener on the targeted promise, or — if
the promise is already resolved — fires the notification
immediately. -/
def dispatchOpListen (st : State) (frame : ValueExt) : IO (List ValueExt) := do
  match parseOpListen frame with
  | none =>
    IO.eprintln "[session] malformed op:listen frame"
    return []
  | some (toVal, rmd, _wantsPartial) =>
    match extractExportPos toVal, extractImportObjPos rmd with
    | some n, some rmPos =>
      match ← st.exportLookup n with
      | some (.promise promiseRef) =>
        promiseRef.modifyGet fun s =>
          match s with
          | .pending ls    => ([], .pending (rmPos :: ls))
          | .fulfilled v   =>
              ([.record (.sym opDeliverSym)
                  [ buildDescExport rmPos
                  , .list [.sym fulfillSym, v]
                  , .bool false, .bool false
                  ]], .fulfilled v)
          | .broken r      =>
              ([.record (.sym opDeliverSym)
                  [ buildDescExport rmPos
                  , .list [.sym breakSym, r]
                  , .bool false, .bool false
                  ]], .broken r)
      | _ =>
        IO.eprintln s!"[session] op:listen to non-promise position {n}"
        return []
    | _, _ =>
      IO.eprintln "[session] op:listen with unrecognised to/rmd shape"
      return []

/-- Top-level dispatcher for one frame. -/
def dispatch (st : State) (frame : ValueExt) : IO (List ValueExt) := do
  if ← st.aborted.get then return []

  -- Handshake phase: we expect the first frame to be op:start-session.
  if !(← st.handshakeDone.get) then
    match extractStartSession frame with
    | some (version, clientPk, clientLoc, clientSig) =>
      if version ≠ captpVersion.toUTF8.toList then
        st.aborted.set true
        return [buildAbort s!"unsupported captp version: {String.fromUTF8! ⟨version.toArray⟩}"]
      else if ¬ verifyClientLocationSig clientPk clientLoc clientSig then
        IO.eprintln s!"[session] client signature failed verification; aborting"
        st.aborted.set true
        return [buildAbort "invalid acceptable-location signature"]
      else
        -- Crossed-hellos check: if we have an outbound session pending
        -- to this same peer, compare Public Identifiers and abort the
        -- lower one (spec §"Crossed Hellos Resolution").
        let crossedAbort : Option ValueExt ←
          match extractPeerKey clientLoc with
          | none => pure none
          | some peerKey =>
            match ← st.outboundReg.lookup peerKey with
            | none => pure none
            | some pending =>
              let ourOutPk  := buildSessionPubkey (baToList pending.ourPubkey)
              let ourPubid  := publicIdentifier ourOutPk
              let theirPubid := publicIdentifier clientPk
              match byteArrayCmp ourPubid theirPubid with
              | .lt =>
                IO.eprintln "[session] crossed-hellos: outbound loses, aborting outbound"
                pending.aborted.set true
                try pending.conn.writeFrame (buildAbort "Crossed hellos mitigated")
                catch _ => pure ()
                st.outboundReg.remove peerKey
                pure none
              | .gt =>
                IO.eprintln "[session] crossed-hellos: inbound loses, aborting inbound"
                st.aborted.set true
                pure (some (buildAbort "Crossed hellos mitigated"))
              | .eq =>
                IO.eprintln "[session] crossed-hellos: identical pubids; aborting inbound"
                st.aborted.set true
                pure (some (buildAbort "Crossed hellos mitigated"))
        match crossedAbort with
        | some abortFrame => return [abortFrame]
        | none =>
          st.handshakeDone.set true
          let payload := locationSigningPayload st.ourLocation
          let sig     := Crypto.ed25519Sign st.sessionSecret payload
          let reply   := buildStartSessionReply (baToList st.sessionPubkey) sig st.ourLocation
          IO.eprintln s!"[session] handshake OK, replying with signed op:start-session"
          return [reply]
    | none =>
      -- Special case: an inbound `op:abort` before the handshake means
      -- the peer is unilaterally ending the conversation. We silently
      -- drop the connection rather than echoing our own `op:abort` back
      -- (the test suite expects the read side to time out, not to
      -- receive a counter-abort).
      match frame with
      | .record (.sym lbl) _ =>
        if lbl = opAbortSym then
          IO.eprintln "[session] received op:abort before handshake; closing"
          st.aborted.set true
          return []
        else
          IO.eprintln s!"[session] first frame is not op:start-session; aborting"
          st.aborted.set true
          return [buildAbort "expected op:start-session as first message"]
      | _ =>
        IO.eprintln s!"[session] first frame is not op:start-session; aborting"
        st.aborted.set true
        return [buildAbort "expected op:start-session as first message"]

  -- Post-handshake routing: pick the dispatcher by the frame's
  -- record label.
  match frame with
  | .record (.sym lbl) _ =>
    if lbl = opDeliverSym then dispatchOpDeliver st frame
    else if lbl = opListenSym then dispatchOpListen st frame
    else if lbl = opAbortSym then do
      IO.eprintln "[session] received op:abort; closing"
      st.aborted.set true
      return []
    else do
      IO.eprintln s!"[session] unsupported op after handshake: {String.fromUTF8! ⟨lbl.toArray⟩}"
      return []
  | _ =>
    IO.eprintln "[session] non-record frame after handshake; ignoring"
    return []

/-- Run a session: build state, dispatch frames in a loop. -/
def run (conn : FramedConn) (registry : Registry) (ourLocation : ValueExt)
    (outboundReg : OutboundRegistry) : IO Unit := do
  let st ← State.create ourLocation registry outboundReg
  runHandlerN conn (dispatch st)

end OcapnLean.Captp.Session
