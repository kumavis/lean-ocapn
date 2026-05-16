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

Pass `--frame netstring` to drive Ridley dobjects, which prefix each
frame with `<n>:` instead of speaking the de-facto raw-Syrup
convention. See `docs/INTEROP.md` "Disagreement 4".
-/

open OcapnLean OcapnLean.Captp OcapnLean.Captp.Session OcapnLean.Syrup
     Netlayer
open Std.Net

def parsePort : List String → UInt16
  | []                       => 22082
  | "--port" :: n :: _       => (n.toNat?.getD 22082).toUInt16
  | _ :: rest                => parsePort rest

def parseFrame : List String → IO Netlayer.Tcp.Framing
  | []                                => pure .raw
  | "--frame" :: "netstring" :: _     => pure .netstring
  | "--frame" :: "raw"       :: _     => pure .raw
  | "--frame" :: other       :: _     =>
      throw (IO.userError s!"--frame: expected 'raw' or 'netstring', got '{other}'")
  | _ :: rest                         => parseFrame rest

/-- `--captp-version V` overrides the version we send in
`op:start-session`. Default `"1.0"` (Python ref / Endo / ocapn-lean).
Ridley dobjects expects `"0.1"`. -/
def parseCaptpVersion : List String → String
  | []                              => "1.0"
  | "--captp-version" :: v :: _     => v
  | _ :: rest                       => parseCaptpVersion rest

/-- `--handshake-only` stops after the handshake completes. Useful for
peers (Ridley) that don't expose the test-suite swissnums. -/
def parseHandshakeOnly : List String → Bool
  | []                          => false
  | "--handshake-only" :: _     => true
  | _ :: rest                   => parseHandshakeOnly rest

/-- `--hints empty-dict|false` controls the third field of our
`<ocapn-peer …>` locator. Default `empty-dict` matches Endo's strict
parser. Pass `false` for Ridley dobjects: Ridley accepts both shapes
on parse but normalises empty-hints to `false` during signature
re-encoding, so an empty-dict locator fails its signature check.
See `docs/INTEROP.md` "Disagreement 3". -/
inductive HintsShape where | emptyDict | falseLit
deriving Repr

def parseHints : List String → IO HintsShape
  | []                                 => pure .emptyDict
  | "--hints" :: "empty-dict" :: _     => pure .emptyDict
  | "--hints" :: "false"      :: _     => pure .falseLit
  | "--hints" :: other        :: _     =>
      throw (IO.userError s!"--hints: expected 'empty-dict' or 'false', got '{other}'")
  | _ :: rest                          => parseHints rest

def main (args : List String) : IO Unit := do
  let port := parsePort args
  let framing ← parseFrame args
  let captpVersion := parseCaptpVersion args
  let handshakeOnly := parseHandshakeOnly args
  let hintsShape ← parseHints args
  let addr : SocketAddress := Tcp.v4 Tcp.loopback port
  let frameLabel := match framing with | .raw => "raw" | .netstring => "netstring"
  let hintsLabel := match hintsShape with | .emptyDict => "empty-dict" | .falseLit => "false"
  IO.println s!"[external-smoke] connecting to 127.0.0.1:{port} (framing={frameLabel}, captp={captpVersion}, hints={hintsLabel})"

  let hintsVal : ValueExt := match hintsShape with
    | .emptyDict => .dict []
    | .falseLit  => .bool false
  let clientLoc : ValueExt :=
    .record (.sym "ocapn-peer".toUTF8.toList)
      [ .sym "tcp-testing-only".toUTF8.toList
      , .str "extsmokebeefbeefbeefbeefbeefbeef".toUTF8.toList
      , hintsVal
      ]
  let s ← Captp.Client.Session.connect addr clientLoc
            (captpVersion := captpVersion) (framing := framing)
  Captp.Client.handshake s
  IO.println "[external-smoke] handshake ok"
  if handshakeOnly then
    Captp.Client.Session.close s
    IO.println "OK"
    return ()

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
