import OcapnLean.Captp.Run
import OcapnLean.Captp.Session
import OcapnLean.Crypto
import OcapnLean.Netlayer.Tcp
import OcapnLean.Syrup.Extended

/-!
# CapTP client driver

A minimal Lean-side client capable of driving an OCapN peer (any
peer that speaks the same wire format we serve — `ocapn-lean`,
`@endo/ocapn`, `goblins`, ...). The protocol layer is the same as
`Captp.Session` but reorganised around *initiating* a session
rather than accepting one:

  * `Client.connect` — open the TCP socket and frame it.
  * `Client.handshake` — exchange `op:start-session` both ways.
  * `Client.fetch` — send `<op:deliver <desc:export 0>
    [fetch SWISS] False <desc:import-object N>>` and block for the
    fulfill, returning the freshly-imported export position.
  * `Client.deliver` — generic deliver with optional answer_position
    and resolve-me-desc; returns the rmd export position so the
    caller can later await its fulfill.
  * `Client.expectFulfill` / `Client.expectMessageTo` — small
    inbound matchers analogous to `utils/captp.py`.

This is the foundation for in-tree integration tests that don't
need a Python interpreter on the side. The first such test is
`scripts/ClientSmoke.lean`. -/

namespace OcapnLean.Captp.Client

open OcapnLean OcapnLean.Captp OcapnLean.Captp.Session OcapnLean.Syrup
open Std.Net

/-- One end of a client-side CapTP session. Holds the framed
connection, the per-session keypair, and small monotonically-
incrementing counters for the import / answer slots we hand out.
The `captpVersion` field defaults to `"1.0"` (the version
ocapn-lean and @endo/ocapn speak); set it to e.g.
`"goblins-0.16"` when driving a Goblins peer. -/
structure Session where
  conn          : FramedConn
  ourLocation   : ValueExt
  ourPubkey     : ByteArray
  ourSecret     : ByteArray
  captpVersion  : String := "1.0"
  peerPubkey    : IO.Ref (Option ValueExt)
  nextImportPos : IO.Ref Nat
  nextAnswerPos : IO.Ref Nat

namespace Session

/-- Open a TCP connection to `addr`, generate a fresh keypair, and
return a `Session` with all counters initialised. The handshake is
*not* run yet — call `handshake` next. Optional `captpVersion`
overrides the default `"1.0"` (use e.g. `"goblins-0.16"` for a
Goblins peer). -/
def connect (addr : SocketAddress) (ourLocation : ValueExt)
    (captpVersion : String := "1.0") : IO Session := do
  let net ← Netlayer.Tcp.connect addr
  let conn ← FramedConn.of net
  let (pk, sk) ← Crypto.ed25519Keypair
  pure { conn, ourLocation, ourPubkey := pk, ourSecret := sk,
         captpVersion,
         peerPubkey := ← IO.mkRef none,
         nextImportPos := ← IO.mkRef 0,
         nextAnswerPos := ← IO.mkRef 0 }

def close (s : Session) : IO Unit :=
  try s.conn.close catch _ => pure ()

/-- Allocate the next import position (analogue of Python
`CapTPSession.next_import_object.position`). -/
def nextImport (s : Session) : IO Nat :=
  s.nextImportPos.modifyGet fun n => (n, n + 1)

/-- Allocate the next answer position. -/
def nextAnswer (s : Session) : IO Nat :=
  s.nextAnswerPos.modifyGet fun n => (n, n + 1)

end Session

/-! ## Handshake. -/

/-- Build a `<op:start-session>` for *us* to send, using the
session's configured `captpVersion`. -/
def buildOurStartSession (s : Session) : ValueExt :=
  let payload := Session.locationSigningPayload s.ourLocation
  let sig := Crypto.ed25519Sign s.ourSecret payload
  .record (.sym Session.opStartSessionSym)
    [ .str s.captpVersion.toUTF8.toList
    , Session.buildSessionPubkey (Session.baToList s.ourPubkey)
    , s.ourLocation
    , Session.buildLocationSig sig
    ]

/-- Send our `op:start-session`, read the peer's, verify their
signature against the embedded `acceptable-location`. Stores their
pubkey in `s.peerPubkey` on success. Throws on any failure. The
peer must echo our `captpVersion`. -/
def handshake (s : Session) : IO Unit := do
  s.conn.writeFrame (buildOurStartSession s)
  match ← s.conn.readFrame with
  | none => throw (IO.userError "[client] EOF awaiting op:start-session")
  | some f =>
    match Session.extractStartSession f with
    | none => throw (IO.userError "[client] peer reply not op:start-session")
    | some (ver, theirPk, theirLoc, theirSig) =>
      if ver ≠ s.captpVersion.toUTF8.toList then
        throw (IO.userError s!"[client] captp version mismatch")
      else if ¬ Session.verifyClientLocationSig theirPk theirLoc theirSig then
        throw (IO.userError "[client] peer location signature failed")
      else
        s.peerPubkey.set (some theirPk)

/-! ## Sending. -/

def writeOpDeliver (s : Session) (toVal : ValueExt) (args : List ValueExt)
    (answerPos : Option Nat) (rmd : ValueExt) : IO Unit := do
  let frame : ValueExt :=
    .record (.sym Session.opDeliverSym)
      [ toVal
      , .list args
      , (match answerPos with
         | some n => .int (Int.ofNat n)
         | none   => .bool false)
      , rmd
      ]
  s.conn.writeFrame frame

/-- `<op:deliver <desc:export 0> [fetch swiss] False <desc:import-object N>>`.
Returns the import position `N` we used as `resolve-me-desc` (so
the caller can later await its fulfill). -/
def fetch (s : Session) (swiss : List UInt8) : IO Nat := do
  let importPos ← s.nextImport
  writeOpDeliver s (Session.buildDescExport 0)
    [.sym Session.fetchSym, .bytes swiss]
    none (Session.buildDescImportObj importPos)
  return importPos

/-- General `op:deliver`. Optionally allocate an answer slot and an
rmd slot; returns `(rmdPos, ansPos)` where each component is
`some n` iff the corresponding slot was allocated. (Position 0 is
a real slot, so we never coerce `none` to `0`.) -/
def deliver (s : Session) (toVal : ValueExt) (args : List ValueExt)
    (withAnswer : Bool := false) (withRmd : Bool := true) :
    IO (Option Nat × Option Nat) := do
  let rmdPos ← if withRmd then some <$> s.nextImport else pure none
  let ansPos ← if withAnswer then some <$> s.nextAnswer else pure none
  let rmd : ValueExt := match rmdPos with
    | some n => Session.buildDescImportObj n
    | none   => .bool false
  writeOpDeliver s toVal args ansPos rmd
  return (rmdPos, ansPos)

/-- Listen on a promise position. Returns the rmd we used. -/
def listen (s : Session) (promisePos : Nat) (wantsPartial : Bool := false) :
    IO Nat := do
  let rmdPos ← s.nextImport
  let frame : ValueExt :=
    .record (.sym Session.opListenSym)
      [ Session.buildDescExport promisePos
      , Session.buildDescImportObj rmdPos
      , .bool wantsPartial
      ]
  s.conn.writeFrame frame
  return rmdPos

/-! ## Receiving. -/

/-- Read frames until we see an `op:deliver` to `<desc:export
expectedTo>`. Returns the frame; throws on EOF or after `budgetMs`
of waiting (polled at 25ms intervals; budgets are approximate). -/
partial def expectMessageTo (s : Session) (expectedTo : Nat)
    (budgetMs : Nat := 10000) : IO ValueExt := do
  if budgetMs = 0 then throw (IO.userError s!"[client] timeout awaiting op:deliver to {expectedTo}")
  match ← s.conn.readFrame with
  | none => throw (IO.userError "[client] EOF awaiting op:deliver")
  | some f =>
    match Session.parseOpDeliver f with
    | some (toVal, _, _, _) =>
      match Session.extractExportPos toVal with
      | some n => if n = expectedTo then return f
                  else expectMessageTo s expectedTo (budgetMs - 25)
      | none => expectMessageTo s expectedTo (budgetMs - 25)
    | none => expectMessageTo s expectedTo (budgetMs - 25)

/-- Await a `[fulfill V]` on a particular rmd position; chases
import-promise resolutions automatically (like Python's
`expect_promise_resolution`). Returns the fulfill value `V`. -/
partial def expectFulfill (s : Session) (rmdPos : Nat)
    (budgetMs : Nat := 10000) : IO ValueExt := do
  let frame ← expectMessageTo s rmdPos budgetMs
  match Session.parseOpDeliver frame with
  | some (_, [.sym tag, value], _, _) =>
    if tag = Session.fulfillSym then
      -- If the resolution is itself a promise descriptor, listen and
      -- chase. Otherwise return the value verbatim.
      match value with
      | .record (.sym lbl) [.int n] =>
        if lbl = Session.descImportPromiseSym && n ≥ 0 then do
          let newRmd ← listen s n.toNat true
          expectFulfill s newRmd budgetMs
        else return value
      | _ => return value
    else
      let tagStr := String.fromUTF8! ⟨tag.toArray⟩
      throw (IO.userError s!"[client] expected fulfill, got tag \"{tagStr}\"")
  | _ => throw (IO.userError "[client] unexpected fulfill shape")

end OcapnLean.Captp.Client
