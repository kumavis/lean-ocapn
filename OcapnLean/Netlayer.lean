/-!
# Abstract netlayer interface

CapTP is netlayer-agnostic: any transport that delivers a reliable
in-order byte stream between two peers (TCP+TLS, Tor onion, libp2p,
…) is fair game. We capture the minimum surface as a plain record of
effectful operations — small enough that swapping transports is a
one-liner, but not so small that you have to ceremony every operation.

A concrete TCP implementation built on Lean 4's libuv-backed
`Std.Internal.IO.Async.TCP` lives in `OcapnLean.Netlayer.Tcp`.
-/

namespace OcapnLean.Netlayer

/-- A connected, bidirectional, in-order byte-stream endpoint.

`recv? size` returns up to `size` bytes; `none` indicates EOF (the
peer has closed its write side).

We keep the surface minimal — sending bytes, receiving bytes, and
shutting the connection. Sequence numbering, message framing, and the
CapTP state machine all live above this layer. -/
structure Netlayer where
  /-- Send bytes; blocks until the libuv runtime has the data. -/
  send  : ByteArray → IO Unit
  /-- Receive up to `size` bytes; `none` on EOF. -/
  recv? : USize → IO (Option ByteArray)
  /-- Half-close the connection (shutdown(2) on the write side). -/
  close : IO Unit

end OcapnLean.Netlayer
