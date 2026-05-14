import OcapnLean.Captp.Session
import OcapnLean.Captp.Bootstrap
import OcapnLean.Netlayer.Tcp

/-!
# OCapN reference server entry point

Listens on a TCP port and serves the `ocapn-test-suite` bootstrap
objects from `OcapnLean.Captp.Bootstrap`. Each accepted connection
gets its own `Captp.Session.State` (fresh handshake, etc.) and is
driven by `Captp.Session.run`.

Run from the project root:

    lake exe ocapn-server                   # binds 127.0.0.1:22045
    lake exe ocapn-server -- --port 12345   # custom port

Cross-check against the test suite (in another terminal):

    cd projects/ocapn-test-suite
    ./test_runner.py \
      'ocapn://...tcp-testing-only?host=127.0.0.1&port=22045' \
      --test-module op_start_session
-/

open OcapnLean Netlayer Syrup Captp
open Std.Net

/-- Parse `--port N` out of the argv tail. Default 22045. -/
def parsePort : List String → UInt16
  | []                       => 22045
  | "--port" :: n :: _       => (n.toNat?.getD 22045).toUInt16
  | _ :: rest                => parsePort rest

/-- Our "location" — the `<ocapn-peer transport address hints>` record
the test suite expects. `address` is a unique identifier; `hints`
would be a Syrup dict in the upstream Python netlayer, but we don't
yet have dicts in ValueExt, so we send an empty list as a stand-in.
The OCapNPeer parser only checks the record label and argument
count, not the type of `hints`. -/
def ourLocation (_port : UInt16) : ValueExt :=
  .record (.sym "ocapn-peer".toUTF8.toList)
    [ .sym "tcp-testing-only".toUTF8.toList
    , .str "ocapnleandeadbeefdeadbeefdeadbeef".toUTF8.toList
    , .list []                        -- placeholder for hints dict
    ]

/-- Accept-forever loop. Each connection is handed to a dedicated
task; the main task immediately returns to accepting the next one. -/
partial def acceptLoop
    (acceptOne : IO Netlayer) (registry : Bootstrap.Registry)
    (loc : ValueExt) : IO Unit := do
  let net ← acceptOne
  let _ ← IO.asTask (prio := .dedicated) do
    try
      let conn ← FramedConn.of net
      Session.run conn registry loc
    catch e =>
      IO.eprintln s!"[server] connection error: {e}"
  acceptLoop acceptOne registry loc

def main (args : List String) : IO Unit := do
  let port := parsePort args
  let addr : SocketAddress := Tcp.v4 Tcp.loopback port
  IO.println s!"ocapn-server: listening on 127.0.0.1:{port}"
  let acceptOne ← Tcp.listen addr 32
  let registry := Bootstrap.defaultRegistry
  let loc := ourLocation port
  acceptLoop acceptOne registry loc
