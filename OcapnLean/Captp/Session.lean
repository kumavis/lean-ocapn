import OcapnLean.Captp.Bootstrap
import OcapnLean.Captp.Run
import OcapnLean.Crypto
import OcapnLean.Syrup.Extended

/-!
# Per-connection CapTP session

A session-aware handler that owns the per-connection state (handshake
flag, abort flag, our location, and a per-session Ed25519 keypair)
and knows how to respond to the top-level `op:*` operations the test
suite exercises.

Scope of this commit: handshake with **real Ed25519 signatures** +
simple fetch + abort/error. The state machine is deliberately
incomplete — it's enough to drive:

  * `op_start_session.test_captp_remote_version`         ✓ ok
  * `op_start_session.test_start_session_with_invalid_version`  ✓ aborts
  * `op_start_session.test_start_session_with_invalid_signature` ✓ (with real sig)
  * `op_deliver` (the fetch-only subset)                ✓

The richer subset (promise pipelining, three-party handoffs, GC
refcounts, listen, op:abort termination) extends naturally from
this scaffold.
-/

namespace OcapnLean.Captp.Session

open OcapnLean OcapnLean.Captp OcapnLean.Captp.Bootstrap OcapnLean.Syrup

/-- The captp-version this implementation speaks. -/
def captpVersion : String := "1.0"

def opStartSessionSym : List UInt8 := "op:start-session".toUTF8.toList
def opDeliverSym      : List UInt8 := "op:deliver".toUTF8.toList
def opAbortSym        : List UInt8 := "op:abort".toUTF8.toList
def descExportSym     : List UInt8 := "desc:export".toUTF8.toList
def myLocationSym     : List UInt8 := "my-location".toUTF8.toList

/-- Convert a `ByteArray` to `List UInt8` for use in `ValueExt.bytes`. -/
@[inline] def baToList (ba : ByteArray) : List UInt8 := ba.toList

/-- Convert a `List UInt8` back to `ByteArray` for crypto calls. -/
@[inline] def listToBa (xs : List UInt8) : ByteArray := ByteArray.mk xs.toArray

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

namespace State

/-- Fresh session state for a new inbound connection. A new Ed25519
keypair is generated per connection (matching the spec's "per-session
keypair" rule). -/
def create (ourLocation : ValueExt) : IO State := do
  let handshakeDone ← IO.mkRef false
  let aborted       ← IO.mkRef false
  let (pk, sk)      ← Crypto.ed25519Keypair
  pure { handshakeDone, aborted, ourLocation, sessionPubkey := pk, sessionSecret := sk }

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
        let payload := locationSigningPayload s.ourLocation
        let sig     := Crypto.ed25519Sign s.sessionSecret payload
        let reply   := buildStartSessionReply (baToList s.sessionPubkey) sig s.ourLocation
        IO.eprintln s!"[session] handshake OK, replying with signed op:start-session"
        return some reply
      else
        s.aborted.set true
        return some (buildAbort s!"unsupported captp version: {String.fromUTF8! ⟨version.toArray⟩}")
    | none =>
      IO.eprintln s!"[session] first frame is not op:start-session; aborting"
      s.aborted.set true
      return some (buildAbort "expected op:start-session as first message")

  -- Post-handshake: route op:deliver/fetch via the bootstrap dispatcher.
  match ← dispatchFetch registry frame with
  | some reply => return some reply
  | none =>
    s.aborted.set true
    return some (buildAbort "unsupported op")

/-- Run a session: build state, dispatch frames in a loop. -/
def run (conn : FramedConn) (registry : Registry) (ourLocation : ValueExt) :
    IO Unit := do
  let st ← State.create ourLocation
  runHandler conn (dispatch st registry)

end OcapnLean.Captp.Session
