import OcapnLean.Crypto
import OcapnLean.Netlayer
import OcapnLean.Syrup.Extended
import OcapnLean.Ws

/-!
# WebSocket reference netlayer

Concrete `Netlayer` backed by `c/ws.c` (libwslay + in-house HTTP/1.1
upgrade handshake over plain TCP). Each `Netlayer.sendMessage` call
becomes one RFC 6455 binary frame; each `recvMessage?` returns the
next inbound non-control message.

## Two modes

* `Ws.connect` / `Ws.listen` — **raw** WebSocket: returns a
  `Netlayer` directly. Suitable for self-loopback testing and any
  peer that doesn't require designator authentication on top of the
  RFC 6455 handshake.

* `Ws.Authenticated.connect` / `Ws.Authenticated.listen` — adds the
  OCapN designator-auth dance documented in
  `projects/endo/packages/ocapn/src/netlayers/websocket.js:24-46`:

    1. Client sends `<init:peer-auth payload>` (a Syrup record
       carrying 32 random challenge bytes) as the very first
       binary frame after the WS handshake completes.
    2. Server signs the **received bytes verbatim** (the encoded
       `<init:peer-auth …>` record, not just the payload) with its
       long-lived *designator key*, and replies with
       `<desc:sig-envelope <init:peer-auth …> <sig-val …>>`.
    3. Client verifies the signature against the public key encoded
       in the remote peer URI's designator field.

  After step 3 both sides yield a normal message-oriented `Netlayer`
  carrying CapTP `op:start-session` and friends. Goblins ≥ v0.16 and
  Endo both require this dance — driving them with raw WS would
  read garbage on the first frame.
-/

namespace OcapnLean.Netlayer.Ws

open OcapnLean OcapnLean.Ws OcapnLean.Syrup OcapnLean.Syrup.Encode
     OcapnLean.Syrup.Decode

/-- RFC 6455 binary-frame opcode; what OCapN uses on the wire. -/
def binaryOpcode : UInt8 := 0x2

/-- Wrap a live `Ws.Conn` as a message-oriented `Netlayer`. -/
def fromConn (c : Conn) : Netlayer := {
  sendMessage  := fun bs => wsSend c bs binaryOpcode
  recvMessage? := wsRecv c
  close        := wsClose c
}

/-- Open a WebSocket client to `ws://host:port/path` and return it
as a raw `Netlayer` (no designator-auth). `path` defaults to `"/"`,
matching what the Goblins and Endo WebSocket impls bind. -/
def connect (host : String) (port : UInt16) (path : String := "/") :
    IO Netlayer := do
  let conn ← wsClientConnect host port path
  pure (fromConn conn)

/-- Bind+listen for inbound WebSocket connections on `bindAddr:port`.
Returns an `acceptOne : IO Netlayer` that the caller invokes to
accept the next connection (synchronously runs the server-side
RFC 6455 handshake; no designator-auth on the returned netlayer). -/
def listen (bindAddr : String := "127.0.0.1") (port : UInt16)
    (backlog : UInt32 := 8) : IO (IO Netlayer) := do
  let lfd ← wsListen bindAddr port backlog
  pure do
    let conn ← wsAccept lfd
    pure (fromConn conn)

/-! ## Designator-auth (OCapN-compatible) -/

namespace Authenticated

open OcapnLean.Crypto

/-- `<init:peer-auth payload-bytes>`. The wrapper exists so the
server's signing surface is typed — it only ever signs encoded
`init:peer-auth` records, preventing the dance from being used as
a generic signing oracle. -/
def buildInitPeerAuth (payload : ByteArray) : ValueExt :=
  .record (.sym "init:peer-auth".toUTF8.toList) [.bytes payload.toList]

/-- `<sig-val <eddsa <r r_value> <s s_value>>>` per the OCapN spec.
The signature is split into the first/second halves; both peers use
the same gcrypt-style structured shape (see Disagreement 2 in
`docs/INTEROP.md`). -/
def buildSigVal (sig : ByteArray) : ValueExt :=
  let half := sig.size / 2
  let r := sig.toList.take half
  let s := sig.toList.drop half
  .list
    [ .sym "sig-val".toUTF8.toList
    , .list
        [ .sym "eddsa".toUTF8.toList
        , .list [.sym "r".toUTF8.toList, .bytes r]
        , .list [.sym "s".toUTF8.toList, .bytes s]
        ]
    ]

/-- `<desc:sig-envelope <init:peer-auth …> <sig-val …>>`. -/
def buildSigEnvelope (inner : ValueExt) (sig : ByteArray) : ValueExt :=
  .record (.sym "desc:sig-envelope".toUTF8.toList) [inner, buildSigVal sig]

/-- Re-assemble the 64-byte Ed25519 signature from a structured
`<sig-val <eddsa <r …> <s …>>>` list. `none` on shape mismatch. -/
def extractSigBytes (v : ValueExt) : Option ByteArray :=
  match v with
  | .list
      [ .sym sv
      , .list
          [ .sym ed
          , .list [.sym _, .bytes r]
          , .list [.sym _, .bytes s]
          ]
      ] =>
    if sv = "sig-val".toUTF8.toList ∧ ed = "eddsa".toUTF8.toList then
      some ⟨(r ++ s).toArray⟩
    else none
  | _ => none

/-- Parse a `<desc:sig-envelope inner sig-val>` and extract the
inner record + the 64-byte signature. `none` on shape mismatch. -/
def parseSigEnvelope (v : ValueExt) : Option (ValueExt × ByteArray) :=
  match v with
  | .record (.sym lbl) [inner, sigVal] =>
    if lbl = "desc:sig-envelope".toUTF8.toList then
      (extractSigBytes sigVal).map fun sig => (inner, sig)
    else none
  | _ => none

/-! ### Legacy raw-bytevector challenge (Goblins ≤ v0.17)

Goblins ≤ v0.17 — including the version nixpkgs currently ships —
predates the typed `init:peer-auth` shape and uses a raw 64-byte
challenge instead. The client sends 64 random bytes verbatim
(no syrup wrapping), the server signs those 64 bytes with the
designator key and replies with a syrup-encoded `<sig-val …>`
list. See `goblins/ocapn/netlayer/websocket.scm:116-128` in the
v0.17 source tree. This was tightened in v0.18 (commit
`61c0247f4`) to use the typed record so the server only ever
signs typed payloads.

Both paths are kept so we can drive whatever's in the wild.
-/

/-- Goblins-v0.17-style client auth: send 64 random raw bytes,
expect a syrup `<sig-val …>` in reply, verify the signature over
the 64 bytes against `remoteDesignatorPub`. -/
def runClientAuthLegacy (conn : Conn) (remoteDesignatorPub : ByteArray) : IO Unit := do
  let challenge ← Crypto.randomBytes 64
  wsSend conn challenge binaryOpcode
  match ← wsRecv conn with
  | none => throw (IO.userError "[ws-auth-legacy] peer closed before reply")
  | some replyBytes =>
    match decodeExt replyBytes.toList with
    | none => throw (IO.userError "[ws-auth-legacy] reply not Syrup")
    | some (sigVal, _) =>
      match extractSigBytes sigVal with
      | none => throw (IO.userError "[ws-auth-legacy] reply not <sig-val …>")
      | some sig =>
        if sig.size ≠ 64 then
          throw (IO.userError s!"[ws-auth-legacy] sig wrong size: {sig.size}")
        else if ¬ Crypto.ed25519Verify remoteDesignatorPub challenge sig then
          throw (IO.userError "[ws-auth-legacy] sig invalid against remote designator")

/-- Goblins-v0.17-style server auth: receive 64 raw bytes, sign with
`designatorSecret`, reply with `<sig-val …>` syrup-encoded. -/
def runServerAuthLegacy (conn : Conn) (designatorSecret : ByteArray) : IO Unit := do
  match ← wsRecv conn with
  | none => throw (IO.userError "[ws-auth-legacy] EOF before challenge")
  | some challenge =>
    if challenge.size ≠ 64 then
      throw (IO.userError s!"[ws-auth-legacy] expected 64-byte challenge, got {challenge.size}")
    let sig := Crypto.ed25519Sign designatorSecret challenge
    let sigVal := buildSigVal sig
    let replyBytes : ByteArray := ⟨(encodeExt sigVal).toArray⟩
    wsSend conn replyBytes binaryOpcode

/-! ### Typed init:peer-auth (Endo / Goblins ≥ v0.18) -/

/-- Client side of the designator-auth dance. Runs after the WS
handshake; throws on failure (signature mismatch, malformed reply,
wrong sig length, …). -/
def runClientAuth (conn : Conn) (remoteDesignatorPub : ByteArray) : IO Unit := do
  let challenge ← Crypto.randomBytes 32
  let challengeRecord := buildInitPeerAuth challenge
  let challengeBytes : ByteArray := ⟨(encodeExt challengeRecord).toArray⟩
  wsSend conn challengeBytes binaryOpcode
  match ← wsRecv conn with
  | none => throw (IO.userError "[ws-auth] peer closed before reply")
  | some replyBytes =>
    match decodeExt replyBytes.toList with
    | none => throw (IO.userError "[ws-auth] reply not Syrup")
    | some (replyVal, _) =>
      match parseSigEnvelope replyVal with
      | none => throw (IO.userError "[ws-auth] reply not <desc:sig-envelope …>")
      | some (_inner, sig) =>
        if sig.size ≠ 64 then
          throw (IO.userError s!"[ws-auth] sig wrong size: {sig.size}")
        else if ¬ Crypto.ed25519Verify remoteDesignatorPub challengeBytes sig then
          throw (IO.userError "[ws-auth] sig invalid against remote designator")

/-- Server side. Reads one inbound binary frame, treats it as the
verbatim bytes to sign with `designatorSecret`, replies with the
sig-envelope. -/
def runServerAuth (conn : Conn) (designatorSecret : ByteArray) : IO Unit := do
  match ← wsRecv conn with
  | none => throw (IO.userError "[ws-auth] EOF before init:peer-auth")
  | some challengeBytes =>
    -- We don't need to inspect the inner record's shape; per the
    -- Endo reference impl we sign the bytes verbatim and echo the
    -- inner record back in the sig-envelope. Parse it just enough
    -- to put `inner` in the envelope.
    match decodeExt challengeBytes.toList with
    | none => throw (IO.userError "[ws-auth] inbound not Syrup")
    | some (inner, _) =>
      let sig := Crypto.ed25519Sign designatorSecret challengeBytes
      let envelope := buildSigEnvelope inner sig
      let envelopeBytes : ByteArray := ⟨(encodeExt envelope).toArray⟩
      wsSend conn envelopeBytes binaryOpcode

/-- Open a WebSocket client, run the OCapN designator-auth dance
with the named remote public key, and return the post-auth
`Netlayer`. The remote pubkey is whatever you decoded from the
`designator` segment of the peer's `ocapn://…` URI. -/
def connect (host : String) (port : UInt16) (path : String := "/")
    (remoteDesignatorPub : ByteArray) : IO Netlayer := do
  let conn ← wsClientConnect host port path
  try
    runClientAuth conn remoteDesignatorPub
    pure (fromConn conn)
  catch e =>
    wsClose conn
    throw e

/-- Listen-side counterpart. `designatorSecret` is the secret half
of the long-lived designator keypair that identifies this peer in
its `ocapn://` URI; generate it once with `Crypto.ed25519Keypair`
and persist the pair (or regenerate per process, for tests). -/
def listen (bindAddr : String := "127.0.0.1") (port : UInt16)
    (backlog : UInt32 := 8) (designatorSecret : ByteArray) :
    IO (IO Netlayer) := do
  let lfd ← wsListen bindAddr port backlog
  pure do
    let conn ← wsAccept lfd
    try
      runServerAuth conn designatorSecret
      pure (fromConn conn)
    catch e =>
      wsClose conn
      throw e

/-- `connect` variant speaking the Goblins ≤ v0.17 raw-bytevector
challenge (needed for the version nixpkgs currently ships). -/
def connectLegacy (host : String) (port : UInt16) (path : String := "/")
    (remoteDesignatorPub : ByteArray) : IO Netlayer := do
  let conn ← wsClientConnect host port path
  try
    runClientAuthLegacy conn remoteDesignatorPub
    pure (fromConn conn)
  catch e =>
    wsClose conn
    throw e

/-- `listen` variant speaking the Goblins ≤ v0.17 raw-bytevector
challenge. -/
def listenLegacy (bindAddr : String := "127.0.0.1") (port : UInt16)
    (backlog : UInt32 := 8) (designatorSecret : ByteArray) :
    IO (IO Netlayer) := do
  let lfd ← wsListen bindAddr port backlog
  pure do
    let conn ← wsAccept lfd
    try
      runServerAuthLegacy conn designatorSecret
      pure (fromConn conn)
    catch e =>
      wsClose conn
      throw e

end Authenticated

end OcapnLean.Netlayer.Ws
