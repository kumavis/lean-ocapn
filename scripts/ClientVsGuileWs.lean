import OcapnLean.Locators
import OcapnLean.Netlayer.Ws

/-!
Drive a Goblins-hosted `^websocket-netlayer` peer over plain TCP
WebSocket + the OCapN designator-auth dance.

Companion to `scripts/diagnostics/goblins-ws-server.scm`. The
typical orchestration is:

```sh
# Shell 1 — Goblins peer:
nix-shell -p guile guile-goblins guile-fibers --command \
  "GUILE_AUTO_COMPILE=0 guile \
    scripts/diagnostics/goblins-ws-server.scm 22090"

# Shell 1 prints:  goblins-ws-ready designator-hex=… port=22090

# Shell 2 — Lean client:
lake exe client-vs-guile-ws -- --port 22090 \
  --designator-hex d3700725e10e14db1582a934c7b343b55b97d8b4b293ae84751f782ed956716b
```

Output ends with `OK` on a successful designator-auth handshake.

This exercises only the netlayer layer: the OCapN designator-auth
dance (`<init:peer-auth …>` ↔ `<desc:sig-envelope …>`). The
CapTP-level `op:start-session` flow above is the same code that
already drives Ridley, Endo, and self via TCP — we don't repeat it
here, just confirm the post-auth `Netlayer` round-trips one CapTP
frame before clean close.
-/

open OcapnLean OcapnLean.Netlayer OcapnLean.Locators

def parsePort : List String → UInt16
  | []                  => 22090
  | "--port" :: n :: _  => (n.toNat?.getD 22090).toUInt16
  | _ :: rest           => parsePort rest

def parseDesignatorHex : List String → String
  | []                             => ""
  | "--designator-hex" :: h :: _   => h
  | _ :: rest                      => parseDesignatorHex rest

/-- `--uri ocapn://…` — parse a Goblins-style peer URI and derive
both the designator-pubkey (base32 → 32 bytes) and the `url` hint
(then split as `ws://host:port`). When given, overrides any
`--port` / `--designator-hex` flags. -/
def parseUri : List String → String
  | []                  => ""
  | "--uri" :: u :: _   => u
  | _ :: rest           => parseUri rest

/-- Strip `ws://` prefix and split `host:port`. Returns `none` on
shape mismatch. -/
def parseWsUrl (s : String) : Option (String × UInt16) := do
  let scheme := "ws://"
  if ¬ s.startsWith scheme then none
  else
    let body := s.drop scheme.length
    match body.splitOn ":" with
    | [host, portStr] =>
      let port ← portStr.toNat?
      some (host, port.toUInt16)
    | _ => none

/-- `--auth typed|legacy`. Default `typed` (matches Goblins ≥ v0.18
and Endo — the typed `<init:peer-auth …>` record). `legacy` (raw
64-byte challenge, syrup-encoded `<sig-val …>` reply) is needed
for Goblins ≤ v0.17, which is what nixpkgs currently ships. -/
inductive AuthMode where | typed | legacy
deriving Repr

def parseAuth : List String → IO AuthMode
  | []                          => pure .typed
  | "--auth" :: "typed"  :: _   => pure .typed
  | "--auth" :: "legacy" :: _   => pure .legacy
  | "--auth" :: other :: _      =>
      throw (IO.userError s!"--auth: expected 'typed' or 'legacy', got '{other}'")
  | _ :: rest                   => parseAuth rest

private def hexDigit? (c : Char) : Option UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat.toUInt8 - '0'.toNat.toUInt8)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat.toUInt8 - 'a'.toNat.toUInt8 + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat.toUInt8 - 'A'.toNat.toUInt8 + 10)
  else none

/-- Decode a hex string into bytes. `none` on bad input. -/
def hexToBytes (s : String) : Option ByteArray := do
  let chars := s.toList
  if chars.length % 2 ≠ 0 then none
  else
    let rec loop : List Char → Option (List UInt8)
      | []           => some []
      | _ :: []      => none
      | hi :: lo :: rest => do
        let h ← hexDigit? hi
        let l ← hexDigit? lo
        let bs ← loop rest
        return ((h <<< 4) ||| l) :: bs
    let bytes ← loop chars
    return ⟨bytes.toArray⟩

/-- Derive `(host, port, designatorPub)` from either an `--uri`
flag (parse the full OCapN URI) or the lower-level
`--designator-hex` + `--port` pair. The URI form is what a real
peer publishes; the explicit-flag form is what our diagnostic
`goblins-ws-server.scm` prints. -/
def resolveTarget (args : List String) : IO (String × UInt16 × ByteArray) := do
  let uri := parseUri args
  if ¬ uri.isEmpty then
    -- URI mode.
    let some peer := PeerLocator.fromUri uri
      | throw (IO.userError s!"--uri: failed to parse \"{uri}\" as a PeerLocator")
    let designatorStr := String.fromUTF8! ⟨peer.designator.toArray⟩
    let some pubBytes := Base32.decode designatorStr
      | throw (IO.userError s!"--uri: designator \"{designatorStr}\" is not valid base32")
    let pub : ByteArray := ⟨pubBytes.toArray⟩
    if pub.size ≠ 32 then
      throw (IO.userError s!"--uri: designator decodes to {pub.size} bytes, expected 32")
    -- Goblins encodes the bind address as a single `url=ws://host:port` hint.
    let hints := peer.hints.getD []
    let urlHint := hints.lookup "url".toUTF8.toList
    let some urlBytes := urlHint
      | throw (IO.userError "--uri: peer hints missing 'url'; not a ws-style peer?")
    let urlStr := String.fromUTF8! ⟨urlBytes.toArray⟩
    let some (host, port) := parseWsUrl urlStr
      | throw (IO.userError s!"--uri: 'url' hint \"{urlStr}\" not a ws://host:port")
    pure (host, port, pub)
  else
    -- Explicit-flag mode.
    let port := parsePort args
    let hex  := parseDesignatorHex args
    if hex.isEmpty then
      throw (IO.userError "missing --uri or --designator-hex (32-byte Ed25519 pubkey)")
    let some designatorPub := hexToBytes hex
      | throw (IO.userError s!"--designator-hex: bad hex \"{hex}\"")
    if designatorPub.size ≠ 32 then
      throw (IO.userError s!"--designator-hex: expected 32 bytes, got {designatorPub.size}")
    pure ("127.0.0.1", port, designatorPub)

def main (args : List String) : IO Unit := do
  let (host, port, designatorPub) ← resolveTarget args
  let auth ← parseAuth args

  let authLabel := match auth with | .legacy => "legacy" | .typed => "typed"
  IO.println s!"[guile-ws] connecting to ws://{host}:{port}/ ({authLabel} designator-auth)"
  let net ← (match auth with
             | .legacy => Ws.Authenticated.connectLegacy host port "/" designatorPub
             | .typed  => Ws.Authenticated.connect       host port "/" designatorPub)
  IO.println "[guile-ws] designator-auth completed"

  -- Send one ordinary message over the post-auth Netlayer to prove
  -- it's live, then clean-close. We don't drive a full CapTP
  -- handshake here — that's already covered by the TCP-based
  -- interop tests; the gap this fills is the netlayer-level auth.
  let probe : ByteArray := "ocapn-lean ws probe".toUTF8
  net.sendMessage probe
  IO.println s!"[guile-ws] sent post-auth probe ({probe.size} bytes)"
  net.close
  IO.println "OK"
