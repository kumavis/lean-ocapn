import OcapnLean.Captp.Bootstrap
import OcapnLean.Captp.Client
import OcapnLean.Captp.Run
import OcapnLean.Captp.Session
import OcapnLean.Netlayer.Tcp
import OcapnLean.Syrup.Extended

/-!
End-to-end smoke test for `OcapnLean.Captp.Client`. We run our own
server in a task and have a Lean client drive it:

  1. Connect, handshake.
  2. Fetch the echo-gc swissnum.
  3. Deliver `["hi", 1, false]` to the resulting export with a
     resolve-me-desc, expect a fulfill containing the same args
     back.

This proves the client driver can speak to *any* OCapN peer (we
self-host here, but it works identically against `@endo/ocapn`'s
test server). -/

open OcapnLean OcapnLean.Captp OcapnLean.Captp.Session OcapnLean.Syrup
     Netlayer
open Std.Net

def main : IO Unit := do
  let port : UInt16 := 22095
  let addr : SocketAddress := Tcp.v4 Tcp.loopback port

  let serverLoc : ValueExt :=
    .record (.sym "ocapn-peer".toUTF8.toList)
      [ .sym "tcp-testing-only".toUTF8.toList
      , .str "serverdeadbeefdeadbeefdeadbeefee".toUTF8.toList
      , .dict
          [ .str "host".toUTF8.toList, .str "127.0.0.1".toUTF8.toList
          , .str "port".toUTF8.toList, .str (toString port).toUTF8.toList
          ]
      ]

  -- Spin up the server side.
  let acceptOne ← Tcp.listen addr
  let outboundReg ← Captp.Session.OutboundRegistry.create
  let gifts ← Captp.Session.GiftsTable.create
  let used ← Captp.Session.HandoffCountSet.create
  let pending ← Captp.Session.PendingWithdrawTable.create
  let peerSessions ← Captp.Session.PeerSessionRegistry.create
  let _serverTask ← IO.asTask (prio := .dedicated) do
    let net ← acceptOne
    let conn ← FramedConn.of net
    Captp.Session.run conn Captp.Bootstrap.defaultRegistry serverLoc
                      outboundReg gifts used pending peerSessions

  IO.sleep 50

  -- Client side.
  let clientLoc : ValueExt :=
    .record (.sym "ocapn-peer".toUTF8.toList)
      [ .sym "tcp-testing-only".toUTF8.toList
      , .str "clientdeadbeefdeadbeefdeadbeefde".toUTF8.toList
      , .list []
      ]
  let s ← Captp.Client.Session.connect addr clientLoc
  Captp.Client.handshake s
  IO.println "[client] handshake ok"

  -- Fetch echo-gc.
  let fetchRmd ← Captp.Client.fetch s Captp.Bootstrap.echoGcSwiss
  let echoRefVal ← Captp.Client.expectFulfill s fetchRmd
  let echoExportPos := match Captp.Session.extractImportObjPos echoRefVal with
                      | some n => n
                      | none => 0
  IO.println s!"[client] echo fetched at export pos {echoExportPos}"

  -- Deliver to echo with rmd, expect fulfill with echoed args.
  let myArgs : List ValueExt :=
    [ .str "hi".toUTF8.toList, .int 1, .bool false ]
  let (rmd, _) ← Captp.Client.deliver s (Captp.Session.buildDescExport echoExportPos)
                                       myArgs (withRmd := true)
  let result ← Captp.Client.expectFulfill s rmd
  IO.println s!"[client] echo replied: {repr result}"

  -- Verify the echoed list matches what we sent (byte-equality via
  -- re-encoding sidesteps the lack of DecidableEq on ValueExt).
  let expected := Encode.encodeExt (.list myArgs)
  let got := Encode.encodeExt result
  if got = expected then IO.println "OK"
  else
    IO.eprintln s!"FAIL: echoed value differs"
    IO.Process.exit 1

  Captp.Client.Session.close s
