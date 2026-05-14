import OcapnLean.Netlayer
import OcapnLean.Syrup.Extended

/-!
# Frame-aware CapTP event loop

Wraps a byte-level `Netlayer` with a Syrup-frame reader and writer
(`FramedConn`), then provides `runHandler` — a small event loop that
reads one Syrup frame at a time, dispatches it through a
caller-supplied `ValueExt → IO (Option ValueExt)` handler, and writes
the optional response back over the wire.

This is the plumbing under a real CapTP peer. The handler is where
the actual `op:deliver` / `op:gc-exports` / etc. dispatch lives;
`OcapnLean.Captp.Bootstrap` (step 3) provides a reference handler
that recognises the test-suite's bootstrap objects.

The framing strategy is: buffer incoming bytes in an `IO.Ref`; on
`readFrame`, try `Syrup.Decode.decodeExt` on the current buffer; if
it yields a value, advance the buffer past the consumed prefix; if
it doesn't, pull more bytes from the netlayer and retry. EOF (a
`none` from `recv?`) terminates the loop.
-/

namespace OcapnLean.Captp

open OcapnLean.Netlayer OcapnLean.Syrup OcapnLean.Syrup.Decode

/-- A netlayer connection wrapped with a byte buffer for Syrup framing. -/
structure FramedConn where
  net    : Netlayer
  bufRef : IO.Ref (List UInt8)

namespace FramedConn

/-- Build a fresh framed connection over an established netlayer. -/
def of (net : Netlayer) : IO FramedConn := do
  let bufRef ← IO.mkRef []
  pure { net, bufRef }

/-- The chunk size we request from the netlayer when refilling the
buffer. 4 KiB strikes a balance: large enough to amortise the recv
syscall, small enough to keep memory bounded for tiny messages. -/
def recvChunkSize : USize := 4096

/-- Read one complete Syrup frame. Returns `none` on EOF *and* an
empty buffer (clean close); raises if a partial frame is interrupted
by EOF. -/
partial def readFrame (c : FramedConn) : IO (Option ValueExt) := do
  let buf ← c.bufRef.get
  match decodeExt buf with
  | some (v, rest) =>
    c.bufRef.set rest
    return some v
  | none =>
    let chunk ← c.net.recv? recvChunkSize
    match chunk with
    | none =>
      if buf.isEmpty then return none
      else throw (IO.userError "EOF with partial Syrup frame in buffer")
    | some bs =>
      c.bufRef.set (buf ++ bs.toList)
      readFrame c

/-- Encode and send one Syrup frame over the netlayer. -/
def writeFrame (c : FramedConn) (v : ValueExt) : IO Unit := do
  let bytes := Encode.encodeExt v
  c.net.send (ByteArray.mk bytes.toArray)

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

end OcapnLean.Captp
