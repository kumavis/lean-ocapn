import OcapnLean.Captp.Bootstrap
import OcapnLean.Captp.Run
import OcapnLean.Syrup.Extended

/-!
# Per-connection CapTP session

A session-aware handler that owns the per-connection state (import,
export, answer-slot, refcount tables) and knows how to respond to the
top-level `op:*` operations the test suite exercises.

Scope of this commit: handshake + simple fetch + abort/error. The
state machine is deliberately incomplete — it's enough to drive
the simpler tests in `projects/ocapn-test-suite/tests/`:

  * `op_start_session.test_captp_remote_version`
  * `op_start_session.test_start_session_with_invalid_version`
  * `op_deliver` (the fetch-only subset)

The richer subset (promise pipelining, three-party handoffs, GC
refcounts, listen) extends naturally from this scaffold.

Cryptography is stubbed: we use deterministic placeholder bytes for
our session-pubkey, public-id, and location-signature. The
test-runner's `test_captp_remote_version` only checks that we echo
the captp-version `"1.0"`, so the placeholder is sufficient for that
test. Strict signature-verifying tests will need real Ed25519.
-/

namespace OcapnLean.Captp.Session

open OcapnLean OcapnLean.Captp OcapnLean.Captp.Bootstrap OcapnLean.Syrup

/-- The captp-version this implementation speaks. -/
def captpVersion : String := "1.0"

/-- The session symbol "op:start-session". -/
def opStartSessionSym : List UInt8 := "op:start-session".toUTF8.toList

/-- "op:deliver" -/
def opDeliverSym : List UInt8 := "op:deliver".toUTF8.toList

/-- "op:abort" -/
def opAbortSym : List UInt8 := "op:abort".toUTF8.toList

/-- "desc:export" -/
def descExportSym : List UInt8 := "desc:export".toUTF8.toList

/-- A placeholder 32-byte EdDSA public-key payload. Not real crypto. -/
def stubPubkey : List UInt8 :=
  List.replicate 32 0x00

/-- A placeholder 64-byte EdDSA signature. -/
def stubSignature : List UInt8 :=
  List.replicate 64 0x00

/-- Build an `op:start-session` reply with placeholder crypto fields.
The shape mirrors the test-runner's `OpStartSession` syrup record. -/
def buildStartSessionReply (location : ValueExt) : ValueExt :=
  .record (.sym opStartSessionSym)
    [ .str captpVersion.toUTF8.toList
    , .bytes stubPubkey            -- session-pubkey (stub)
    , location                     -- acceptable-location
    , .bytes stubSignature         -- acceptable-location-sig (stub)
    ]

/-- Build an `op:abort` with the given reason. -/
def buildAbort (reason : String) : ValueExt :=
  .record (.sym opAbortSym) [.str reason.toUTF8.toList]

/-- Per-connection mutable state. Currently just tracks whether we've
seen an op:start-session and the location we'd quote back to the peer.
The full set of tables (import/export/answer/refcount) will land
alongside the matching dispatcher arms. -/
structure State where
  handshakeDone   : IO.Ref Bool
  aborted         : IO.Ref Bool
  ourLocation     : ValueExt

namespace State

/-- Fresh session state for a new inbound connection. The location
echoes back what the peer told us. -/
def create (ourLocation : ValueExt) : IO State := do
  let handshakeDone ← IO.mkRef false
  let aborted       ← IO.mkRef false
  pure { handshakeDone, aborted, ourLocation }

end State

/-- Recognise the captp-version in an incoming `op:start-session`. -/
def extractStartSessionVersion (v : ValueExt) : Option (List UInt8) :=
  match v with
  | .record (.sym lbl) (.str version :: _) =>
      if lbl = opStartSessionSym then some version else none
  | _ => none

/-- Top-level dispatcher for one frame. -/
def dispatch (s : State) (registry : Registry) (frame : ValueExt) :
    IO (Option ValueExt) := do
  if ← s.aborted.get then return none

  -- Handshake phase: we expect the first frame to be op:start-session.
  if !(← s.handshakeDone.get) then
    match extractStartSessionVersion frame with
    | some version =>
      if version = captpVersion.toUTF8.toList then
        s.handshakeDone.set true
        return some (buildStartSessionReply s.ourLocation)
      else
        s.aborted.set true
        return some (buildAbort s!"unsupported captp version: {String.fromUTF8! ⟨version.toArray⟩}")
    | none =>
      -- First frame wasn't a start-session: abort.
      s.aborted.set true
      return some (buildAbort "expected op:start-session as first message")

  -- Post-handshake: route op:deliver/fetch via the bootstrap dispatcher.
  match ← dispatchFetch registry frame with
  | some reply => return some reply
  | none =>
    -- For now, anything else gets a soft abort.
    s.aborted.set true
    return some (buildAbort "unsupported op")

/-- Run a session: build state, dispatch frames in a loop. -/
def run (conn : FramedConn) (registry : Registry) (ourLocation : ValueExt) :
    IO Unit := do
  let st ← State.create ourLocation
  runHandler conn (dispatch st registry)

end OcapnLean.Captp.Session
