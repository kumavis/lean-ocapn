import OcapnLean.Netlayer
import OcapnLean.Uds

/-!
# Unix Domain Socket reference netlayer

Concrete `Netlayer` backed by `c/uds.c` (libc AF_UNIX sockets).
Mirrors `OcapnLean.Netlayer.Tcp` but for UDS, which is the
transport that Goblins's [`testuds` netlayer][goblins-testuds] uses
for in-tree interop tests.

`testuds`'s convention is: both peers agree on a shared `netlayers/`
directory; each peer's listening socket is at
`<netlayers-dir>/<node-id>.sock`. To address a peer with node-id
`N`, you `connect()` to `<netlayers-dir>/N.sock`. We expose two
flavours of the same wrapper:

  * `Uds.connect path` / `Uds.listen path` — raw path-based API.
  * `Uds.testudsConnect dir nodeId` /
    `Uds.testudsListen dir nodeId` — Goblins-style convention layer.

[goblins-testuds]: goblins/goblins/ocapn/netlayer/testuds.scm -/

namespace OcapnLean.Netlayer.Uds

open OcapnLean.Uds

/-- Wrap an open UDS fd as a `Netlayer`. -/
def fromFd (fd : UInt32) : Netlayer := {
  send  := fun data => udsWrite fd data
  recv? := fun size => udsRead fd size
  close := udsClose fd
}

/-- Connect to a peer at `path`. -/
def connect (path : String) : IO Netlayer := do
  let fd ← udsConnect path
  return fromFd fd

/-- Bind+listen on `path`. Returns an `acceptOne : IO Netlayer`
that the caller invokes to accept the next connection. -/
def listen (path : String) (backlog : UInt32 := 8) :
    IO (IO Netlayer) := do
  let lfd ← udsListen path backlog
  return do
    let cfd ← udsAccept lfd
    return fromFd cfd

/-- Goblins-style filename: `<dir>/<nodeId>.sock`. -/
@[inline] def testudsPath (dir nodeId : String) : String :=
  dir ++ "/" ++ nodeId ++ ".sock"

def testudsConnect (dir nodeId : String) : IO Netlayer :=
  connect (testudsPath dir nodeId)

def testudsListen (dir nodeId : String) (backlog : UInt32 := 8) :
    IO (IO Netlayer) :=
  listen (testudsPath dir nodeId) backlog

end OcapnLean.Netlayer.Uds
