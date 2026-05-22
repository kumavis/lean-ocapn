import OcapnLean.Crypto
import OcapnLean.Netlayer.Ws

/-!
Self-loopback smoke for `OcapnLean.Netlayer.Ws.Authenticated`.

Goes through the full OCapN designator-auth dance: server signs the
client's `<init:peer-auth …>` challenge with its long-lived
designator key, client verifies the signature, then both sides
exchange one ordinary message to prove the post-auth `Netlayer`
is live.

Run with `lake exe ws-auth-smoke`. Output ends with `OK`.
-/

open OcapnLean OcapnLean.Netlayer

def main : IO Unit := do
  let port : UInt16 := 23047

  -- Long-lived designator keypair for the server side.
  let (designatorPub, designatorSec) ← Crypto.ed25519Keypair

  let acceptOne ← Ws.Authenticated.listen "127.0.0.1" port 8 designatorSec
  let serverTask ← IO.asTask (prio := .dedicated) do
    let net ← acceptOne
    match ← net.recvMessage? with
    | none => IO.eprintln "[ws-auth-server] EOF before post-auth message"
    | some bs =>
      IO.println s!"[ws-auth-server] got post-auth message ({bs.size} bytes)"
      net.sendMessage bs
      net.close

  IO.sleep 100

  let client ← Ws.Authenticated.connect "127.0.0.1" port "/" designatorPub
  let payload : ByteArray := "ocapn after auth!".toUTF8
  client.sendMessage payload
  match ← client.recvMessage? with
  | none =>
    client.close
    IO.eprintln "[ws-auth-client] EOF awaiting echo"
    IO.Process.exit 1
  | some echoed =>
    client.close
    let _ ← IO.wait serverTask
    if echoed = payload then
      IO.println s!"[ws-auth-client] echo round-trip OK ({echoed.size} bytes)"
      IO.println "OK"
    else
      IO.eprintln "MISMATCH"
      IO.Process.exit 1
