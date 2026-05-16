import OcapnLean.Netlayer
import OcapnLean.Netlayer.Tcp   -- reuse Framing + parser
import OcapnLean.Uds

/-!
# Unix Domain Socket reference netlayer

Concrete `Netlayer` backed by `c/uds.c` (libc AF_UNIX sockets).
Mirrors `OcapnLean.Netlayer.Tcp` but for UDS, which is the transport
that Goblins's [`testuds` netlayer][goblins-testuds] uses for
in-tree interop tests.

`testuds`'s convention is: both peers agree on a shared `netlayers/`
directory; each peer's listening socket is at
`<netlayers-dir>/<node-id>.sock`. To address a peer with node-id
`N`, you `connect()` to `<netlayers-dir>/N.sock`.

UDS in OCapN uses the same Syrup-framing options as TCP, so we
reuse `Netlayer.Tcp.Framing` + `readMessage`. Default is `.raw`,
matching Goblins testuds.

[goblins-testuds]: goblins/goblins/ocapn/netlayer/testuds.scm -/

namespace OcapnLean.Netlayer.Uds

open OcapnLean.Uds OcapnLean.Netlayer.Tcp

/-- Wrap an open UDS fd as a `Netlayer`. -/
def fromFd (fd : UInt32) (framing : Framing := .raw) : IO Netlayer := do
  let bufRef ← IO.mkRef ([] : List UInt8)
  let recv? : USize → IO (Option ByteArray) := fun size => udsRead fd size
  pure {
    sendMessage  := fun bytes => udsWrite fd (encodeForWire framing bytes)
    recvMessage? := readMessage framing recv? bufRef
    close        := udsClose fd
  }

/-- Connect to a peer at `path`. -/
def connect (path : String) (framing : Framing := .raw) : IO Netlayer := do
  let fd ← udsConnect path
  fromFd fd framing

/-- Bind+listen on `path`. Returns an `acceptOne : IO Netlayer` that
the caller invokes to accept the next connection. -/
def listen (path : String) (backlog : UInt32 := 8)
    (framing : Framing := .raw) : IO (IO Netlayer) := do
  let lfd ← udsListen path backlog
  return do
    let cfd ← udsAccept lfd
    fromFd cfd framing

/-- Goblins-style filename: `<dir>/<nodeId>.sock`. -/
@[inline] def testudsPath (dir nodeId : String) : String :=
  dir ++ "/" ++ nodeId ++ ".sock"

def testudsConnect (dir nodeId : String) : IO Netlayer :=
  connect (testudsPath dir nodeId)

def testudsListen (dir nodeId : String) (backlog : UInt32 := 8) :
    IO (IO Netlayer) :=
  listen (testudsPath dir nodeId) backlog

end OcapnLean.Netlayer.Uds
