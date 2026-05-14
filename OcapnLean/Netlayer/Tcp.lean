import Std.Internal.Async.TCP
import OcapnLean.Netlayer

/-!
# TCP reference netlayer

Concrete `Netlayer` backed by Lean 4.24's libuv TCP API
(`Std.Internal.IO.Async.TCP.Socket.{Client,Server}`).

For OCapN's `tcp-testing-only` netlayer transport (the simplest one
supported by the test suite), Syrup-encoded bytes are streamed
directly over a TCP socket — no TLS, no extra framing. This module
provides the byte plumbing; framing and the CapTP state machine live
above.
-/

namespace OcapnLean.Netlayer.Tcp

open Std.Net
open Std.Internal.IO.Async

/-- The well-known IPv4 loopback address `127.0.0.1`. -/
def loopback : IPv4Addr := { octets := #v[127, 0, 0, 1] }

/-- Build an OCapN-style socket address `addr:port` (IPv4). -/
@[inline] def v4 (addr : IPv4Addr) (port : UInt16) : SocketAddress :=
  .v4 { addr := addr, port := port }

/-- Wrap an established client socket as a `Netlayer`. -/
def fromClient (c : TCP.Socket.Client) : Netlayer := {
  send := fun data => do
    let t ← c.send data
    t.block
  recv? := fun size => do
    let t ← c.recv? size.toUInt64
    t.block
  close := do
    let t ← c.shutdown
    t.block
}

/-- Connect to a remote OCapN peer over TCP. -/
def connect (addr : SocketAddress) : IO Netlayer := do
  let c ← TCP.Socket.Client.mk
  let t ← c.connect addr
  t.block
  pure (fromClient c)

/-- Bind+listen on `addr`. Returns an `acceptOne : IO Netlayer` that
the caller invokes to accept the next connection. The server socket
remains open across accepts until the program exits. -/
def listen (addr : SocketAddress) (backlog : UInt32 := 8) :
    IO (IO Netlayer) := do
  let server ← TCP.Socket.Server.mk
  server.bind addr
  server.listen backlog
  pure do
    let t ← server.accept
    let client ← t.block
    pure (fromClient client)

end OcapnLean.Netlayer.Tcp
