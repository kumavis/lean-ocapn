import OcapnLean.Captp.Run
import OcapnLean.Netlayer.Tcp

/-!
Runtime smoke test for `OcapnLean.Captp.Run`: a frame-aware echo loop
running over real TCP, exchanging Syrup-encoded CapTP-shaped records.

Run from the project root:

    lake env lean --run scripts/captp-framed-echo.lean

Successful output ends with `OK`.
-/

open OcapnLean Netlayer Syrup Captp
open Std.Net

/-- The frame we send: an op:deliver-shaped record. -/
def deliverFrame : ValueExt :=
  .record (.sym "op:deliver".toUTF8.toList)
    [ .record (.sym "desc:export".toUTF8.toList) [.int 0]
    , .list [.sym "fetch".toUTF8.toList, .bytes [0x63, 0x61, 0x74]]
    , .int 3
    , .bool false
    ]

def main : IO Unit := do
  let addr : SocketAddress := Tcp.v4 Tcp.loopback 24045

  let acceptOne ← Tcp.listen addr
  let serverTask ← IO.asTask (prio := .dedicated) do
    let netS ← acceptOne
    let conn ← FramedConn.of netS
    -- Echo exactly one frame, verbatim.
    runHandler conn (fun frame => do
      IO.println s!"[server] received a frame, echoing back"
      return some frame)

  IO.sleep 50

  let netC ← Tcp.connect addr
  let conn ← FramedConn.of netC

  -- Send our frame.
  conn.writeFrame deliverFrame
  IO.println s!"[client] sent op:deliver-shaped record"

  -- Read the echo. The server's handler is a one-shot here because the
  -- client closes after receiving.
  match ← conn.readFrame with
  | none => IO.eprintln "[client] EOF before any frame"; IO.Process.exit 1
  | some echo =>
    IO.println s!"[client] received {repr echo} ..."
    conn.close
    -- We expect the bytes to round-trip exactly.
    if Encode.encodeExt echo = Encode.encodeExt deliverFrame then
      IO.println "OK"
    else
      IO.eprintln "MISMATCH"
      IO.Process.exit 1

  let _ ← IO.wait serverTask
