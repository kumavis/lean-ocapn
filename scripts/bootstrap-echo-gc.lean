import OcapnLean.Captp.Bootstrap
import OcapnLean.Captp.Run
import OcapnLean.Netlayer.Tcp

/-!
Runtime smoke test for `OcapnLean.Captp.Bootstrap`: a server speaking
the dispatcher serves the `Echo GC` bootstrap object; a client sends
an `op:deliver` that fetches it (in our simplified model, fetching
*and* invoking the resulting reference happen in one frame), and
verifies the response is the echoed args.

Run from the project root:

    lake env lean --run scripts/bootstrap-echo-gc.lean
-/

open OcapnLean Captp Captp.Bootstrap Netlayer Syrup
open Std.Net

/-- An op:deliver-shaped fetch of `Echo GC` with three sample args:
two ints and a string. Echo GC's contract is to return them as a list
in the same order. -/
def fetchEchoGc : ValueExt :=
  .record (.sym "op:deliver".toUTF8.toList)
    [ .record (.sym "desc:export".toUTF8.toList) [.int 0]
    , .list (.sym "fetch".toUTF8.toList ::
             .bytes echoGcSwiss :: [])
    , .int 1
    , .bool false
    ]

def main : IO Unit := do
  let addr : SocketAddress := Tcp.v4 Tcp.loopback 25045

  let acceptOne ← Tcp.listen addr
  let serverTask ← IO.asTask (prio := .dedicated) do
    let netS ← acceptOne
    let conn ← FramedConn.of netS
    runHandler conn (dispatchFetch defaultRegistry)

  IO.sleep 50

  let netC ← Tcp.connect addr
  let conn ← FramedConn.of netC

  conn.writeFrame fetchEchoGc
  IO.println "[client] sent op:deliver/fetch Echo-GC"

  match ← conn.readFrame with
  | none => IO.eprintln "[client] EOF before any frame"; IO.Process.exit 1
  | some result =>
    IO.println s!"[client] received: {repr result}"
    conn.close
    -- Echo GC returns its args as a list; with no args (since we only
    -- modelled `fetch` here), we expect `[]`.
    match result with
    | .list [] => IO.println "OK"
    | _        => IO.eprintln "UNEXPECTED"; IO.Process.exit 1

  let _ ← IO.wait serverTask
