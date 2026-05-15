import OcapnLean.Captp.Bootstrap
import OcapnLean.Captp.Client
import OcapnLean.Captp.Run
import OcapnLean.Captp.Session
import OcapnLean.Netlayer.Tcp
import OcapnLean.Syrup.Extended

/-!
Drive an *external* OCapN peer over `tcp-testing-only` using
`OcapnLean.Captp.Client`. Companion to `ClientSmoke.lean`, which
exercises the same code path against a self-hosted server in the
same Lean process. This script takes `--port N` and connects to
`127.0.0.1:N`.

We:

  1. Handshake.
  2. Fetch the echo-gc swissnum.
  3. Deliver `["hi", 1, false]` to the echo actor with a
     resolve-me-desc.
  4. Expect a fulfill whose payload re-encodes to the same Syrup
     bytes as our sent args.

The expected use is from CI: spin up `@endo/ocapn`'s test server on
port 22046, then run

    lake exe client-vs-external -- --port 22046

against it. The same script is also a small standalone integration
test against `ocapn-lean` itself.
-/

open OcapnLean OcapnLean.Captp OcapnLean.Captp.Session OcapnLean.Syrup
     Netlayer
open Std.Net

def parsePort : List String → UInt16
  | []                       => 22082
  | "--port" :: n :: _       => (n.toNat?.getD 22082).toUInt16
  | _ :: rest                => parsePort rest

def main (args : List String) : IO Unit := do
  let port := parsePort args
  let addr : SocketAddress := Tcp.v4 Tcp.loopback port
  IO.println s!"[external-smoke] connecting to 127.0.0.1:{port}"

  let clientLoc : ValueExt :=
    .record (.sym "ocapn-peer".toUTF8.toList)
      [ .sym "tcp-testing-only".toUTF8.toList
      , .str "extsmokebeefbeefbeefbeefbeefbeef".toUTF8.toList
      , .dict []                                 -- Endo's strict syrup
                                                 -- requires a dict here.
      ]
  let s ← Captp.Client.Session.connect addr clientLoc
  Captp.Client.handshake s
  IO.println "[external-smoke] handshake ok"

  let fetchRmd ← Captp.Client.fetch s Captp.Bootstrap.echoGcSwiss
  let echoRefVal ← Captp.Client.expectFulfill s fetchRmd
  let echoPos := match Captp.Session.extractImportObjPos echoRefVal with
                 | some n => n
                 | none => 0
  IO.println s!"[external-smoke] echo fetched at pos {echoPos}"

  let myArgs : List ValueExt :=
    [ .str "hi".toUTF8.toList, .int 1, .bool false ]
  let (some rmd, _) ← Captp.Client.deliver s
                   (Captp.Session.buildDescExport echoPos) myArgs
                   (withRmd := true)
    | throw (IO.userError "[external-smoke] deliver did not allocate an rmd slot")
  let result ← Captp.Client.expectFulfill s rmd
  IO.println s!"[external-smoke] echo returned"

  let expected := Encode.encodeExt (.list myArgs)
  let got := Encode.encodeExt result
  Captp.Client.Session.close s
  if got = expected then IO.println "OK"
  else
    IO.eprintln "FAIL: echoed value differs"
    IO.Process.exit 1
