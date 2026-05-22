/-!
# Unix Domain Socket FFI

Wraps the minimal AF_UNIX socket calls from `c/uds.c`:

  * `udsConnect path` — `connect(2)` to a peer socket file.
  * `udsListen path backlog` — `bind(2)` + `listen(2)`.
  * `udsAccept fd` — blocking `accept(2)`; returns a connection fd.
  * `udsRead fd n` — blocking `read(2)` up to `n` bytes; `none` on EOF.
  * `udsWrite fd bs` — blocking `write(2)`, loops until all sent.
  * `udsClose fd` — `close(2)`.
  * `udsUnlink path` — `unlink(2)` (used by the listener to cleanup).

Lean exposes raw fds as `UInt32`. Higher-level wrappers in
`OcapnLean.Netlayer.Uds` package these as the standard `Netlayer`
interface so they slot into `Captp.Run` / `Captp.Session` /
`Captp.Client` unchanged. -/

namespace OcapnLean.Uds

@[extern "ocapnlean_uds_connect"]
opaque udsConnect (path : @& String) : IO UInt32

@[extern "ocapnlean_uds_listen"]
opaque udsListen (path : @& String) (backlog : UInt32) : IO UInt32

@[extern "ocapnlean_uds_accept"]
opaque udsAccept (listenFd : UInt32) : IO UInt32

@[extern "ocapnlean_uds_read"]
opaque udsRead (fd : UInt32) (maxBytes : USize) : IO (Option ByteArray)

@[extern "ocapnlean_uds_write"]
opaque udsWrite (fd : UInt32) (bytes : @& ByteArray) : IO Unit

@[extern "ocapnlean_uds_close"]
opaque udsClose (fd : UInt32) : IO Unit

@[extern "ocapnlean_uds_unlink"]
opaque udsUnlink (path : @& String) : IO Unit

end OcapnLean.Uds
