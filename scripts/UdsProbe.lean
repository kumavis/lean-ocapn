import OcapnLean.Captp.Run
import OcapnLean.Netlayer.Uds
import OcapnLean.Syrup.Extended

/-! Tiny diagnostic: open a UDS connection to a peer and just read
the first frame they send, dump it. No outbound writes. -/

open OcapnLean OcapnLean.Captp OcapnLean.Syrup Netlayer

def main (args : List String) : IO Unit := do
  let path :=
    match args with
    | "--sock" :: p :: _ => p
    | _ => "/tmp/ocapn-lean-uds/goblins.sock"
  let net ← Netlayer.Uds.connect path
  let conn ← FramedConn.of net
  IO.println s!"[probe] connected; awaiting first frame from {path}"
  match ← conn.readFrame with
  | none => IO.println "[probe] EOF"
  | some f => IO.println s!"[probe] received: {repr f}"
  try conn.close catch _ => pure ()
