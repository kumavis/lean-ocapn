import OcapnLean.Netlayer
import OcapnLean.Syrup.Extended

/-!
# Frame-aware CapTP event loop

Thin Syrup-decode wrapper over the message-oriented `Netlayer`. Each
`recvMessage?` from a netlayer already delivers one complete CapTP
message body (the transport — TCP, UDS, WebSocket — handles its own
wire framing), so all `FramedConn` does is `Syrup.decodeExt` /
`encodeExt`.

`runHandler` is a small event loop that reads one frame at a time,
dispatches it through a caller-supplied
`ValueExt → IO (Option ValueExt)` handler, and writes the optional
response back over the wire. `runHandlerN` is the multi-frame
variant used by `Captp.Session`.

This is the plumbing under a real CapTP peer. The handler is where
the actual `op:deliver` / `op:gc-exports` / etc. dispatch lives;
`OcapnLean.Captp.Bootstrap` (step 3) provides a reference handler
that recognises the test-suite's bootstrap objects.
-/

namespace OcapnLean.Captp

open OcapnLean.Netlayer OcapnLean.Syrup OcapnLean.Syrup.Decode

/-- A message-oriented netlayer plus the Syrup codec on top. -/
structure FramedConn where
  net : Netlayer

namespace FramedConn

/-- Build a fresh framed connection over an established netlayer.
Returns in `IO` for parity with the byte-buffered version this
replaced, so existing `← FramedConn.of net` call sites still
typecheck. -/
def of (net : Netlayer) : IO FramedConn := pure { net }

/-- Read one complete Syrup frame. Returns `none` on EOF; raises if
the transport delivers a message whose bytes do not decode as one
Syrup value. -/
def readFrame (c : FramedConn) : IO (Option ValueExt) := do
  match ← c.net.recvMessage? with
  | none => return none
  | some bs =>
    match decodeExt bs.toList with
    | some (v, _) => return some v
    | none =>
      throw (IO.userError "framed message did not decode as one Syrup value")

/-- Encode and send one Syrup frame over the netlayer. -/
def writeFrame (c : FramedConn) (v : ValueExt) : IO Unit := do
  c.net.sendMessage ⟨(Encode.encodeExt v).toArray⟩

/-- Close the connection. -/
def close (c : FramedConn) : IO Unit :=
  c.net.close

end FramedConn

/-- Run a Syrup-frame handler on a connection until the peer closes
the read side. The handler returns an optional response; if it
returns `none`, no frame is sent. -/
partial def runHandler (c : FramedConn)
    (handler : ValueExt → IO (Option ValueExt)) : IO Unit := do
  match ← c.readFrame with
  | none => pure ()                            -- clean EOF
  | some frame =>
    match ← handler frame with
    | none => pure ()
    | some reply => c.writeFrame reply
    runHandler c handler

/-- Multi-frame variant: handler returns a list of frames to emit on
the same connection. Used by `Captp.Session` whose handlers may need
to send several frames per inbound message (e.g. the greeter, which
delivers `"Hello"` to a callback the caller passed in). -/
partial def runHandlerN (c : FramedConn)
    (handler : ValueExt → IO (List ValueExt)) : IO Unit := do
  match ← c.readFrame with
  | none => pure ()
  | some frame =>
    let replies ← handler frame
    for r in replies do c.writeFrame r
    runHandlerN c handler

end OcapnLean.Captp
