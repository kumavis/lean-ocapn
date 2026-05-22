/-!
# Abstract netlayer interface

CapTP is netlayer-agnostic: any transport that delivers ordered,
reliable, *message-shaped* delivery between two peers (TCP+Syrup
framing, Tor onion, libp2p, WebSocket, …) is fair game. We capture
the minimum surface as a plain record of effectful operations:
**one CapTP message in, one CapTP message out**. Concrete transport
implementations are responsible for whatever wire framing they need
(length prefixes, RFC 6455 binary frames, raw Syrup back-to-back,
etc.) so that the abstract `Netlayer` always speaks in complete
messages.

A concrete TCP implementation lives in `OcapnLean.Netlayer.Tcp` and a
UDS one in `OcapnLean.Netlayer.Uds`. A WebSocket reference lives in
`OcapnLean.Netlayer.Ws` (M-future).
-/

namespace OcapnLean.Netlayer

/-- A connected, bidirectional, in-order **message-oriented** endpoint.

`recvMessage?` returns one complete CapTP message body (the bytes a
single `Syrup.decodeExt` consumes), or `none` for clean EOF. The
transport implementation handles whatever framing is needed under
the hood — `Netlayer` consumers never see partial frames.

Sequence numbering, CapTP state, etc. all live above this layer. -/
structure Netlayer where
  /-- Send one complete CapTP message. Blocks until the underlying
  transport has handed the bytes off. -/
  sendMessage  : ByteArray → IO Unit
  /-- Receive one complete CapTP message; `none` on clean EOF.
  Raises if a partial frame is interrupted (the transport sees an
  EOF mid-frame) or if the framing is malformed. -/
  recvMessage? : IO (Option ByteArray)
  /-- Half-close the connection (shutdown(2) on the write side). -/
  close        : IO Unit

end OcapnLean.Netlayer
