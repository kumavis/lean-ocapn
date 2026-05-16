import OcapnLean.Captp.Bootstrap
import OcapnLean.Captp.Client
import OcapnLean.Captp.Run
import OcapnLean.Captp.Session
import OcapnLean.Captp.SturdyRefClient
import OcapnLean.Locators
import OcapnLean.Netlayer.Tcp
import OcapnLean.Syrup.Extended

/-!
End-to-end smoke test for `OcapnLean.Captp.SturdyRefClient`. We
self-host a server and drive it via a `SturdyRef` rather than a raw
`SocketAddress`, exercising:

  1. `SturdyRefClient.addressFromPeer` — host/port hint extraction.
  2. `SturdyRefClient.connectAndHandshake` — connection + handshake.
  3. `SturdyRefClient.fetch` — `[fetch swiss]` deliver + fulfill
     extraction, returning `(Session, importPos)`.
  4. A follow-up `Captp.Client.deliver` to confirm the returned
     session is live and the returned import position is the right
     value to address the imported object.

Same shape as `scripts/ClientSmoke.lean`, but goes through the
sturdyref layer.
-/

open OcapnLean OcapnLean.Captp OcapnLean.Captp.Session OcapnLean.Syrup
     OcapnLean.Locators Netlayer
open Std.Net

def main : IO Unit := do
  let port : UInt16 := 22097
  let addr : SocketAddress := Tcp.v4 Tcp.loopback port

  let serverDesignator : List UInt8 :=
    "sturdyrefsmokeserverbeefdeadbeef".toUTF8.toList
  let serverLoc : ValueExt :=
    .record (.sym "ocapn-peer".toUTF8.toList)
      [ .sym "tcp-testing-only".toUTF8.toList
      , .str serverDesignator
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

  -- Build a SturdyRef that points at the server we just started,
  -- and resolve the echo-gc swissnum through it.
  let sturdy : SturdyRef :=
    { peer :=
        { transport  := "tcp-testing-only".toUTF8.toList
        , designator := serverDesignator
        , hints := some
            [ ("host".toUTF8.toList, "127.0.0.1".toUTF8.toList)
            , ("port".toUTF8.toList, (toString port).toUTF8.toList) ] }
    , swiss := Captp.Bootstrap.echoGcSwiss }

  let (s, echoPos) ← Captp.SturdyRefClient.fetch sturdy
  IO.eprintln s!"[sturdyref-smoke] handshake + fetch ok, echo imported at pos {echoPos}"

  -- Drive the imported object: deliver an arg list with an rmd,
  -- expect a fulfill echoing the same args back.
  let myArgs : List ValueExt :=
    [ .str "hi".toUTF8.toList, .int 1, .bool false ]
  let (some rmd, _) ← Captp.Client.deliver s
                        (Captp.Session.buildDescExport echoPos)
                        myArgs (withRmd := true)
    | throw (IO.userError "[sturdyref-smoke] deliver did not allocate an rmd slot")
  let result ← Captp.Client.expectFulfill s rmd
  let expected := Encode.encodeExt (.list myArgs)
  let got := Encode.encodeExt result
  Captp.Client.Session.close s

  -- Round-trip the SturdyRef through `toUri` + `fromUri` as a
  -- structural check that the URI surface stays in sync with the
  -- in-memory `SturdyRef`. (A full second-fetch via
  -- `SturdyRefClient.fetchFromUri` would need an accept loop on
  -- the server side; the URI parser itself is exercised by
  -- `OcapnLean.Test.Locators`.)
  match sturdy.toUri.bind SturdyRef.fromUri with
  | none =>
    IO.eprintln "FAIL: SturdyRef did not round-trip through URI"
    IO.Process.exit 1
  | some sturdy' =>
    if sturdy'.peer.transport = sturdy.peer.transport ∧
       sturdy'.peer.designator = sturdy.peer.designator ∧
       sturdy'.swiss = sturdy.swiss then
      pure ()
    else
      IO.eprintln "FAIL: parsed SturdyRef differs from original"
      IO.Process.exit 1

  if got = expected then IO.println "OK"
  else
    IO.eprintln "FAIL: echoed value differs"
    IO.Process.exit 1
