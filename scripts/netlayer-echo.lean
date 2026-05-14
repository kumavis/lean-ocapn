import OcapnLean.Netlayer.Tcp

/-!
Runtime smoke test for `OcapnLean.Netlayer.Tcp`. Spawns an accept-one
echo server on 127.0.0.1, connects from the same process, sends a
payload, and verifies it round-trips.

Run from the project root:

    lake env lean --run scripts/netlayer-echo.lean

Successful output:

    [server] got 13 bytes
    [client] sent 13, echoed back 13
    [client] payload : hello, ocapn!
    [client] echoed  : hello, ocapn!
    OK

Exits with code 1 if the bytes don't match.
-/

open OcapnLean.Netlayer
open Std.Net

def main : IO Unit := do
  let addr : SocketAddress := Tcp.v4 Tcp.loopback 23045

  let acceptOne ← Tcp.listen addr
  let serverTask ← IO.asTask (prio := .dedicated) do
    let server ← acceptOne
    let received := (← server.recv? 4096).getD ByteArray.empty
    IO.println s!"[server] got {received.size} bytes"
    server.send received
    server.close

  IO.sleep 50  -- let the listener settle

  let client ← Tcp.connect addr
  let payload : ByteArray := "hello, ocapn!".toUTF8
  client.send payload
  let echoed := (← client.recv? 4096).getD ByteArray.empty
  client.close
  IO.println s!"[client] sent {payload.size}, echoed back {echoed.size}"
  IO.println s!"[client] payload : {String.fromUTF8! payload}"
  IO.println s!"[client] echoed  : {String.fromUTF8! echoed}"

  let _ ← IO.wait serverTask

  if echoed = payload then
    IO.println "OK"
  else
    IO.eprintln "MISMATCH"
    IO.Process.exit 1
