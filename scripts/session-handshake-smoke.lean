import OcapnLean.Captp.Bootstrap
import OcapnLean.Captp.Run
import OcapnLean.Captp.Session
import OcapnLean.Crypto
import OcapnLean.Netlayer.Tcp
import OcapnLean.Syrup.Extended

/-!
End-to-end Session smoke test: spin up an `ocapn-server`-style handler
on a local port, connect, send an `op:start-session`, decode the
reply, extract `(pubkey, signature)`, and **verify the signature**
against the location-signing payload.

This confirms the libsodium Ed25519 path is wired correctly through
`Captp.Session` — the same code path the upstream test suite's
`test_start_session_with_invalid_signature` exercises.

Run from the project root, with the precompiled .so preloaded so
the interpreter can find the FFI symbols:

    LD_PRELOAD=$PWD/.lake/build/lib/libOcapnLeanCrypto.so \
      lake env lean --run scripts/session-handshake-smoke.lean
-/

open OcapnLean Captp Captp.Session Netlayer Syrup Crypto
open Std.Net

/-- Extract the 32-byte pubkey `q` from a gcrypt-shaped pubkey
record `(public-key (ecc ... (q PK)))`. -/
def extractPubkey : ValueExt → Option (List UInt8)
  | .list [_, .list [_, _, _, .list [_, .bytes q]]] => some q
  | _ => none

/-- Extract the 64-byte signature from a gcrypt-shaped sig-val
record `(sig-val (eddsa (r R) (s S)))`. -/
def extractSig : ValueExt → Option (List UInt8)
  | .list [_, .list [_, .list [_, .bytes r], .list [_, .bytes s]]] => some (r ++ s)
  | _ => none

def main : IO Unit := do
  let port : UInt16 := 22090
  let addr : SocketAddress := Tcp.v4 Tcp.loopback port

  -- Build the same ocapn-peer location the server would emit.
  let serverLoc : ValueExt :=
    .record (.sym "ocapn-peer".toUTF8.toList)
      [ .sym "tcp-testing-only".toUTF8.toList
      , .str "ocapnleandeadbeefdeadbeefdeadbeef".toUTF8.toList
      , .list []
      ]

  -- Spin up the server side in a dedicated task.
  let acceptOne ← Tcp.listen addr
  let _serverTask ← IO.asTask (prio := .dedicated) do
    let net ← acceptOne
    let conn ← FramedConn.of net
    Session.run conn Bootstrap.defaultRegistry serverLoc

  IO.sleep 50

  -- Client side: build an op:start-session and send it.
  let cliFakePk : List UInt8 := List.replicate 32 0x00
  let cliFakeSig : List UInt8 := List.replicate 64 0x00
  let helloLoc : ValueExt :=
    .record (.sym "ocapn-peer".toUTF8.toList)
      [ .sym "tcp-testing-only".toUTF8.toList
      , .str "clientdeadbeefdeadbeefdeadbeefde".toUTF8.toList
      , .list []
      ]
  let hello : ValueExt :=
    .record (.sym "op:start-session".toUTF8.toList)
      [ .str "1.0".toUTF8.toList
      , .list [.sym "public-key".toUTF8.toList,
               .list [.sym "ecc".toUTF8.toList,
                      .list [.sym "curve".toUTF8.toList, .sym "Ed25519".toUTF8.toList],
                      .list [.sym "flags".toUTF8.toList, .sym "eddsa".toUTF8.toList],
                      .list [.sym "q".toUTF8.toList, .bytes cliFakePk]]]
      , helloLoc
      , .list [.sym "sig-val".toUTF8.toList,
               .list [.sym "eddsa".toUTF8.toList,
                      .list [.sym "r".toUTF8.toList, .bytes (cliFakeSig.take 32)],
                      .list [.sym "s".toUTF8.toList, .bytes (cliFakeSig.drop 32)]]]
      ]

  let net ← Tcp.connect addr
  let conn ← FramedConn.of net
  conn.writeFrame hello

  IO.println "[client] sent op:start-session; awaiting reply"
  match ← conn.readFrame with
  | none => IO.eprintln "[client] EOF, no reply"; IO.Process.exit 1
  | some reply =>
    IO.println s!"[client] got reply"
    match reply with
    | .record (.sym _lbl) [_, pkVal, locVal, sigVal] =>
      let some pkBytes := extractPubkey pkVal
        | IO.eprintln "[client] could not extract pubkey"; IO.Process.exit 1
      let some sigBytes := extractSig sigVal
        | IO.eprintln "[client] could not extract sig"; IO.Process.exit 1
      IO.println s!"[client] pk.size={pkBytes.length}  sig.size={sigBytes.length}"

      let payload := locationSigningPayload locVal
      let ok := ed25519Verify (ByteArray.mk pkBytes.toArray)
                              payload
                              (ByteArray.mk sigBytes.toArray)
      IO.println s!"[client] verify(pk, my-location∥loc, sig) = {ok}"
      conn.close
      if ok then
        IO.println "OK"
      else
        IO.eprintln "FAIL"
        IO.Process.exit 1
    | _ =>
      IO.eprintln s!"[client] unexpected reply shape: {repr reply}"
      IO.Process.exit 1
