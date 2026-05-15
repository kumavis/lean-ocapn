import OcapnLean.Captp.Bootstrap
import OcapnLean.Captp.Client
import OcapnLean.Captp.Run
import OcapnLean.Captp.Session
import OcapnLean.Netlayer.Uds
import OcapnLean.Syrup.Extended

/-!
End-to-end smoke for `OcapnLean.Netlayer.Uds`. Same shape as
`ClientSmoke.lean`, but uses Unix-domain sockets instead of TCP.

We use a `testuds`-style filename layout: a shared directory plus
`<nodeId>.sock` per peer. The server listens at
`<dir>/server.sock`; the client connects there. Drives the standard
echo round-trip and asserts byte equality.

Designed to be run alongside Goblins's `testuds` netlayer: if you
point Goblins at the same `<dir>` and give it a different node-id,
the two impls can exchange messages.
-/

open OcapnLean OcapnLean.Captp OcapnLean.Captp.Session OcapnLean.Syrup
     Netlayer

def main : IO Unit := do
  let dir : String := "/tmp/ocapn-lean-uds"
  IO.FS.createDirAll dir
  let serverNode : String := "server"
  let clientNode : String := "client"

  -- Make sure no leftover sockets from a prior crash linger.
  Uds.udsUnlink (Netlayer.Uds.testudsPath dir serverNode)
  Uds.udsUnlink (Netlayer.Uds.testudsPath dir clientNode)

  let serverLoc : ValueExt :=
    .record (.sym "ocapn-peer".toUTF8.toList)
      [ .sym "testuds".toUTF8.toList
      , .str serverNode.toUTF8.toList
      , .list []
      ]

  let acceptOne ← Netlayer.Uds.testudsListen dir serverNode
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

  -- Give the listener a tick to bind.
  IO.sleep 50

  -- Client side.
  let clientLoc : ValueExt :=
    .record (.sym "ocapn-peer".toUTF8.toList)
      [ .sym "testuds".toUTF8.toList
      , .str clientNode.toUTF8.toList
      , .list []
      ]
  let cliNet ← Netlayer.Uds.testudsConnect dir serverNode
  let cliConn ← FramedConn.of cliNet
  let (pk, sk) ← Crypto.ed25519Keypair
  let s : Captp.Client.Session :=
    { conn := cliConn
    , ourLocation := clientLoc
    , ourPubkey := pk
    , ourSecret := sk
    , peerPubkey := ← IO.mkRef none
    , nextImportPos := ← IO.mkRef 0
    , nextAnswerPos := ← IO.mkRef 0 }
  Captp.Client.handshake s
  IO.println "[uds-smoke] handshake ok"

  let fetchRmd ← Captp.Client.fetch s Captp.Bootstrap.echoGcSwiss
  let echoRefVal ← Captp.Client.expectFulfill s fetchRmd
  let echoPos := match Captp.Session.extractImportObjPos echoRefVal with
                 | some n => n
                 | none => 0
  IO.println s!"[uds-smoke] echo fetched at pos {echoPos}"

  let myArgs : List ValueExt :=
    [ .str "hi".toUTF8.toList, .int 1, .bool false ]
  let (some rmd, _) ← Captp.Client.deliver s
                   (Captp.Session.buildDescExport echoPos) myArgs
                   (withRmd := true)
    | throw (IO.userError "[uds-smoke] deliver did not allocate an rmd slot")
  let result ← Captp.Client.expectFulfill s rmd

  let expected := Encode.encodeExt (.list myArgs)
  let got := Encode.encodeExt result
  Captp.Client.Session.close s

  -- Cleanup: unlink the socket file.
  Uds.udsUnlink (Netlayer.Uds.testudsPath dir serverNode)

  if got = expected then IO.println "OK"
  else
    IO.eprintln "FAIL: echoed value differs"
    IO.Process.exit 1
