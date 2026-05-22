import OcapnLean.Netlayer.Ws

/-!
Self-loopback smoke test for `OcapnLean.Netlayer.Ws`. Spawns an
accept-one server on `127.0.0.1:<port>`, connects a client from the
same process, sends one Syrup-encoded `<bytes>` message in each
direction (client → server, server echoes back), and verifies the
echo round-trips.

This exercises:
  - the C-side WebSocket handshake (Sec-WebSocket-Key / Accept,
    SHA-1 + base64 in `c/ws.c`),
  - libwslay binary frame encoding + masking + decoding,
  - the message-oriented `Netlayer` interface on top.

It does NOT exercise the OCapN designator-auth dance — that's
layered on for the Goblins interop test.

Run from the project root:

    lake exe ws-smoke

Successful output ends with `OK`.
-/

open OcapnLean.Netlayer

def main : IO Unit := do
  let port : UInt16 := 23046

  let acceptOne ← Ws.listen "127.0.0.1" port
  let serverTask ← IO.asTask (prio := .dedicated) do
    let net ← acceptOne
    match ← net.recvMessage? with
    | none =>
      IO.eprintln "[ws-server] EOF before message"
    | some bs =>
      IO.println s!"[ws-server] got {bs.size} bytes"
      net.sendMessage bs
      net.close

  IO.sleep 100

  let client ← Ws.connect "127.0.0.1" port
  let payload : ByteArray := "hello, ocapn ws!".toUTF8
  client.sendMessage payload
  match ← client.recvMessage? with
  | none =>
    client.close
    IO.eprintln "[ws-client] EOF awaiting echo"
    IO.Process.exit 1
  | some echoed =>
    client.close
    IO.println s!"[ws-client] sent {payload.size}, echoed back {echoed.size}"
    let _ ← IO.wait serverTask
    if echoed = payload then
      IO.println "OK"
    else
      IO.eprintln "MISMATCH"
      IO.Process.exit 1
