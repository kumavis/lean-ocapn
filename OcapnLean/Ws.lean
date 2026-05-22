/-!
# WebSocket FFI

Wraps the entry points exposed by `c/ws.c` (libwslay-backed
RFC 6455 frames + in-house HTTP upgrade handshake) as opaque IO
operations. Higher-level wrappers in `OcapnLean.Netlayer.Ws`
package these as the standard message-oriented `Netlayer`
interface so they slot into `Captp.Run` / `Captp.Session` /
`Captp.Client` unchanged.

`Conn` is an opaque handle backing a `ws_conn*` on the C side
(fd + wslay event context + a tiny recv-message slot). The
finaliser registered in `c/ws.c` frees the wslay context and
closes the fd when Lean GCs the Conn.

The `opcode` argument and result are the raw RFC 6455 opcodes:
  - `0x1` text
  - `0x2` binary (what OCapN uses)
  - control frames are handled internally and never surface here.
-/

namespace OcapnLean.Ws

/-- Opaque handle to a live WebSocket connection. -/
opaque ConnPointed : NonemptyType
def Conn : Type := ConnPointed.type
instance : Nonempty Conn := ConnPointed.property

/-- Open a TCP socket to `host:port`, perform the RFC 6455 client
handshake on `path`, and return a live `Conn`. Blocks until the
handshake completes. Raises on TCP error or handshake mismatch. -/
@[extern "ocapnlean_ws_client_connect"]
opaque wsClientConnect (host : @& String) (port : UInt16) (path : @& String) :
    IO Conn

/-- Bind+listen for inbound WebSocket connections. `bindAddr` is an
IPv4 dotted-decimal string (e.g. `"127.0.0.1"`). Returns the
listening fd. -/
@[extern "ocapnlean_ws_listen"]
opaque wsListen (bindAddr : @& String) (port : UInt16) (backlog : UInt32) :
    IO UInt32

/-- Accept one inbound connection from a listening fd and run the
RFC 6455 server-side handshake. -/
@[extern "ocapnlean_ws_accept"]
opaque wsAccept (listenFd : UInt32) : IO Conn

/-- Send one whole message (`opcode`/`bytes`). Use opcode `0x2`
(binary) for OCapN. Blocks until the bytes are off our send
buffer. -/
@[extern "ocapnlean_ws_send"]
opaque wsSend (conn : @& Conn) (bytes : @& ByteArray) (opcode : UInt8) :
    IO Unit

/-- Receive the next whole non-control message. Blocks until one
arrives. `none` on clean close (peer CLOSE or socket EOF). -/
@[extern "ocapnlean_ws_recv"]
opaque wsRecv (conn : @& Conn) : IO (Option ByteArray)

/-- Best-effort CLOSE frame + shutdown of the write side. The
underlying fd and wslay context are freed when the `Conn` is GC'd. -/
@[extern "ocapnlean_ws_close"]
opaque wsClose (conn : @& Conn) : IO Unit

end OcapnLean.Ws
