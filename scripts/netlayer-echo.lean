import OcapnLean.Netlayer.Tcp

/-!
Runtime smoke test for `OcapnLean.Netlayer.Tcp`. Spawns an accept-one
echo server on 127.0.0.1, connects from the same process, sends one
Syrup-bytes message and verifies it round-trips.

After the netlayer refactor (`Netlayer` is message-oriented; framing
is owned by the transport), each side speaks in complete CapTP-shaped
messages — so the netlayer self-loopback is exactly one
`sendMessage` + `recvMessage?` pair per direction. The payload here
is a valid Syrup-encoded `<bytes>` value so it can flow through the
default raw-Syrup framing.

Run from the project root:

    lake env lean --run scripts/netlayer-echo.lean

Successful output:

    [server] got 17 bytes
    [client] sent 17, echoed back 17
    OK
-/

open OcapnLean.Netlayer
open Std.Net

def main : IO Unit := do
  let addr : SocketAddress := Tcp.v4 Tcp.loopback 23045

  let acceptOne ← Tcp.listen addr
  let serverTask ← IO.asTask (prio := .dedicated) do
    let server ← acceptOne
    match ← server.recvMessage? with
    | none =>
      IO.eprintln "[server] EOF before message"
    | some bs =>
      IO.println s!"[server] got {bs.size} bytes"
      server.sendMessage bs
      server.close

  IO.sleep 50  -- let the listener settle

  -- A valid raw-Syrup message: the bytes literal `"hello, ocapn!"`
  -- encoded as a Syrup `<len>:<body>` byte value.
  let inner : ByteArray := "hello, ocapn!".toUTF8
  let payload : ByteArray :=
    ⟨((toString inner.size).toUTF8.toList ++ [0x3a]).toArray⟩ ++ inner

  let client ← Tcp.connect addr
  client.sendMessage payload
  match ← client.recvMessage? with
  | none =>
    client.close
    IO.eprintln "[client] EOF awaiting echo"
    IO.Process.exit 1
  | some echoed =>
    client.close
    IO.println s!"[client] sent {payload.size}, echoed back {echoed.size}"
    let _ ← IO.wait serverTask
    if echoed = payload then
      IO.println "OK"
    else
      IO.eprintln "MISMATCH"
      IO.Process.exit 1
