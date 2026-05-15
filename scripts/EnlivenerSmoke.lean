import OcapnLean.Captp.Bootstrap
import OcapnLean.Captp.Run
import OcapnLean.Captp.Session
import OcapnLean.Crypto
import OcapnLean.Netlayer.Tcp
import OcapnLean.Syrup.Extended

/-!
End-to-end smoke test for the **sturdyref-enlivener** bootstrap object.

Scenario, all in one Lean process:

  1. Spin up a primary ocapn-server on port 22091 (the one whose
     enlivener we will drive).

  2. Spin up an *other* server on port 22092 — this stands in for the
     test suite's `other_session`. It accepts one inbound connection
     and checks that the first frame is a syntactically valid
     `op:start-session` whose Ed25519 signature verifies under the
     embedded public key. Once verified, it signals success via an
     `IO.Ref`.

  3. As client: connect to the primary, do a real op:start-session
     handshake, then send

         <op:deliver <desc:export 0>
                     [fetch <sturdyref-enlivener-swiss>]
                     0 <desc:import-object 0>>

     Wait for the fulfill reply, extract the export position N, then
     send

         <op:deliver <desc:export N>
                     [<ocapn-sturdyref <ocapn-peer 'tcp-testing-only
                                           "other-addr-id"
                                           {host "127.0.0.1" port "22092"}>
                                       <other-swiss-bytes>>]
                     False False>

     The primary server's enlivener should then connect to the *other*
     server and send a signed `op:start-session`. The other server's
     verification ref flips to `true` and we report `OK`.

Run with:

    lake exe enlivener-smoke
-/

open OcapnLean Captp Captp.Session Netlayer Syrup Crypto
open Std.Net

/-! ## Wire helpers (mirrors Session.lean conventions). -/

def deliverFetchEnlivener : ValueExt :=
  .record (.sym "op:deliver".toUTF8.toList)
    [ .record (.sym "desc:export".toUTF8.toList) [.int 0]
    , .list [.sym "fetch".toUTF8.toList,
             .bytes Bootstrap.sturdyrefEnlivenerSwiss]
    , .int 0
    , .record (.sym "desc:import-object".toUTF8.toList) [.int 0]
    ]

/-- Build `<ocapn-sturdyref <ocapn-peer 'tcp-testing-only "<addr>" {host 127.0.0.1 port <port>}> <swiss>>`. -/
def mkSturdyref (port : UInt16) (swiss : List UInt8) : ValueExt :=
  let portStr := toString port
  .record (.sym "ocapn-sturdyref".toUTF8.toList)
    [ .record (.sym "ocapn-peer".toUTF8.toList)
        [ .sym "tcp-testing-only".toUTF8.toList
        , .str "other-addr-id-padded-to-32-bytesxxx".toUTF8.toList
        , .dict
            [ .str "host".toUTF8.toList, .str "127.0.0.1".toUTF8.toList
            , .str "port".toUTF8.toList, .str portStr.toUTF8.toList
            ]
        ]
    , .bytes swiss
    ]

def mkDeliverToEnlivener (exportPos : Nat) (sturdyref : ValueExt) : ValueExt :=
  .record (.sym "op:deliver".toUTF8.toList)
    [ .record (.sym "desc:export".toUTF8.toList) [.int (Int.ofNat exportPos)]
    , .list [sturdyref]
    , .bool false
    , .bool false
    ]

/-- Extract `N` from `<op:deliver <desc:export X> [fulfill <desc:import-object N>] _ _>`. -/
def extractFulfillImportPos (frame : ValueExt) : Option Nat :=
  match frame with
  | .record (.sym _)
      [ _, .list [.sym _ful, .record (.sym _imp) [.int n]], _, _ ] =>
    if n ≥ 0 then some n.toNat else none
  | _ => none

/-! ## The "other" server. -/

/-- Loop reading frames on `conn`. Verify the first is an op:start-session
with a valid signature; flip `okRef` to `true` if so. -/
partial def otherServerHandle (conn : FramedConn) (okRef : IO.Ref Bool) : IO Unit := do
  match ← conn.readFrame with
  | none => IO.eprintln "[other] EOF before any frame"
  | some frame =>
    match Session.extractStartSession frame with
    | none =>
      IO.eprintln s!"[other] first frame is not op:start-session: {repr frame}"
    | some (ver, pkVal, locVal, sigVal) =>
      let ok := Session.verifyClientLocationSig pkVal locVal sigVal
      IO.println s!"[other] op:start-session version={String.fromUTF8! ⟨ver.toArray⟩} sig-ok={ok}"
      if ok then
        okRef.set true

def main : IO Unit := do
  let primaryPort : UInt16 := 22091
  let otherPort   : UInt16 := 22092
  let primaryAddr : SocketAddress := Tcp.v4 Tcp.loopback primaryPort
  let otherAddr   : SocketAddress := Tcp.v4 Tcp.loopback otherPort

  let primaryLoc : ValueExt :=
    .record (.sym "ocapn-peer".toUTF8.toList)
      [ .sym "tcp-testing-only".toUTF8.toList
      , .str "primary-padded-to-32-bytes-xxxxxx".toUTF8.toList
      , .dict
          [ .str "host".toUTF8.toList, .str "127.0.0.1".toUTF8.toList
          , .str "port".toUTF8.toList, .str (toString primaryPort).toUTF8.toList
          ]
      ]

  -- Spin up primary server.
  let primaryAccept ← Tcp.listen primaryAddr
  let primaryOutboundReg ← Session.OutboundRegistry.create
  let primaryGifts ← Session.GiftsTable.create
  let primaryUsedCounts ← Session.HandoffCountSet.create
  let primaryPending ← Session.PendingWithdrawTable.create
  let primaryPeerSessions ← Session.PeerSessionRegistry.create
  let _primaryTask ← IO.asTask (prio := .dedicated) do
    let net ← primaryAccept
    let conn ← FramedConn.of net
    Captp.Session.run conn Bootstrap.defaultRegistry primaryLoc primaryOutboundReg primaryGifts primaryUsedCounts primaryPending primaryPeerSessions

  -- Spin up "other" server with an okRef.
  let okRef ← IO.mkRef false
  let otherAccept ← Tcp.listen otherAddr
  let otherTask ← IO.asTask (prio := .dedicated) do
    let net ← otherAccept
    let conn ← FramedConn.of net
    otherServerHandle conn okRef

  IO.sleep 50

  -- Client side: handshake with the primary.
  let (cliPk, cliSk) ← ed25519Keypair
  let helloLoc : ValueExt :=
    .record (.sym "ocapn-peer".toUTF8.toList)
      [ .sym "tcp-testing-only".toUTF8.toList
      , .str "clientdeadbeefdeadbeefdeadbeefde".toUTF8.toList
      , .dict []
      ]
  let cliSig := ed25519Sign cliSk (Session.locationSigningPayload helloLoc)
  let cliSigList := cliSig.toList
  let hello : ValueExt :=
    .record (.sym "op:start-session".toUTF8.toList)
      [ .str "1.0".toUTF8.toList
      , .list [.sym "public-key".toUTF8.toList,
               .list [.sym "ecc".toUTF8.toList,
                      .list [.sym "curve".toUTF8.toList, .sym "Ed25519".toUTF8.toList],
                      .list [.sym "flags".toUTF8.toList, .sym "eddsa".toUTF8.toList],
                      .list [.sym "q".toUTF8.toList, .bytes cliPk.toList]]]
      , helloLoc
      , .list [.sym "sig-val".toUTF8.toList,
               .list [.sym "eddsa".toUTF8.toList,
                      .list [.sym "r".toUTF8.toList, .bytes (cliSigList.take 32)],
                      .list [.sym "s".toUTF8.toList, .bytes (cliSigList.drop 32)]]]
      ]

  let cliNet ← Tcp.connect primaryAddr
  let cliConn ← FramedConn.of cliNet
  cliConn.writeFrame hello

  match ← cliConn.readFrame with
  | none => IO.eprintln "[client] no op:start-session reply"; IO.Process.exit 1
  | some _reply => IO.println "[client] handshake ok"

  -- Step 1: fetch the enlivener.
  cliConn.writeFrame deliverFetchEnlivener
  IO.println "[client] sent fetch(sturdyref-enlivener)"

  let exportPos : Nat ← do
    match ← cliConn.readFrame with
    | none => IO.eprintln "[client] no fulfill reply"; IO.Process.exit 1
    | some frame =>
      match extractFulfillImportPos frame with
      | some n =>
        IO.println s!"[client] fulfill: import-object pos {n}"
        pure n
      | none =>
        IO.eprintln s!"[client] unexpected fulfill shape: {repr frame}"
        IO.Process.exit 1

  -- Step 2: send op:deliver to the enlivener with a sturdyref pointing at
  -- the *other* server.
  let sref := mkSturdyref otherPort (List.replicate 32 0x61)  -- swiss = b"aaaa…"
  let envelope := mkDeliverToEnlivener exportPos sref
  cliConn.writeFrame envelope
  IO.println "[client] sent op:deliver enlivener(<sturdyref>)"

  -- Wait for other server to verify the inbound op:start-session.
  let _ ← IO.wait otherTask

  cliConn.close

  if (← okRef.get) then
    IO.println "OK — enlivener opened outbound and sent a signed op:start-session"
  else
    IO.eprintln "FAIL — other server did not see a valid op:start-session"
    IO.Process.exit 1
