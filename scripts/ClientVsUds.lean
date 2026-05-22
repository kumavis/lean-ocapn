import OcapnLean.Captp.Bootstrap
import OcapnLean.Captp.Client
import OcapnLean.Captp.Run
import OcapnLean.Captp.Session
import OcapnLean.Netlayer.Uds
import OcapnLean.Syrup.Extended

/-!
Drive an external OCapN peer over a Unix-domain socket using
`OcapnLean.Captp.Client`. Companion to `ClientVsExternal.lean`, but
for the `testuds` transport. Takes `--sock PATH` and connects there.

The expected use is to start a Goblins peer with the `testuds`
netlayer (see `scripts/goblins-testuds-server.scm`), then run

    lake exe client-vs-uds -- --sock /tmp/ocapn-lean-uds/goblins.sock

against it. Performs handshake, fetch echo, echo round-trip; OKs on
byte-equality.
-/

open OcapnLean OcapnLean.Captp OcapnLean.Captp.Session OcapnLean.Syrup
     Netlayer

structure CliArgs where
  sock    : String  := "/tmp/ocapn-lean-uds/server.sock"
  version : String  := "1.0"

partial def parseCli : List String → CliArgs → CliArgs
  | [],                  acc => acc
  | "--sock" :: p :: r,  acc => parseCli r { acc with sock := p }
  | "--version" :: v :: r, acc => parseCli r { acc with version := v }
  | _ :: r,              acc => parseCli r acc

def main (args : List String) : IO Unit := do
  let cli := parseCli args {}
  IO.println s!"[uds-vs] connecting to {cli.sock} (captp-version {cli.version})"

  let clientLoc : ValueExt :=
    .record (.sym "ocapn-peer".toUTF8.toList)
      [ .sym "testuds".toUTF8.toList
      , .str "ocapn-lean-client".toUTF8.toList
      , .dict []
      ]
  let net ← Netlayer.Uds.connect cli.sock
  let conn ← FramedConn.of net
  let (pk, sk) ← Crypto.ed25519Keypair
  let s : Captp.Client.Session :=
    { conn := conn
    , ourLocation := clientLoc
    , ourPubkey := pk
    , ourSecret := sk
    , captpVersion := cli.version
    , peerPubkey := ← IO.mkRef none
    , nextImportPos := ← IO.mkRef 0
    , nextAnswerPos := ← IO.mkRef 0 }
  Captp.Client.handshake s
  IO.println "[uds-vs] handshake ok"

  let fetchRmd ← Captp.Client.fetch s Captp.Bootstrap.echoGcSwiss
  let echoRefVal ← Captp.Client.expectFulfill s fetchRmd
  let echoPos := match Captp.Session.extractImportObjPos echoRefVal with
                 | some n => n
                 | none => 0
  IO.println s!"[uds-vs] echo fetched at pos {echoPos}"

  let myArgs : List ValueExt :=
    [ .str "hi".toUTF8.toList, .int 1, .bool false ]
  let (some rmd, _) ← Captp.Client.deliver s
                   (Captp.Session.buildDescExport echoPos) myArgs
                   (withRmd := true)
    | throw (IO.userError "[uds-vs] deliver did not allocate an rmd slot")
  let result ← Captp.Client.expectFulfill s rmd

  let expected := Encode.encodeExt (.list myArgs)
  let got := Encode.encodeExt result
  Captp.Client.Session.close s
  if got = expected then IO.println "OK"
  else
    IO.eprintln "FAIL: echoed value differs"
    IO.Process.exit 1
