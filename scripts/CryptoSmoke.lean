import OcapnLean.Crypto

/-!
Runtime smoke test for `OcapnLean.Crypto` (libsodium FFI).

Run from the project root:

    lake env lean --run scripts/crypto-smoke.lean

If the precompiled OcapnLeanCrypto .so isn't being auto-loaded by the
interpreter (older Lean versions), preload it explicitly:

    LD_PRELOAD=$PWD/.lake/build/lib/libOcapnLeanCrypto.so \
      lake env lean --run scripts/crypto-smoke.lean

Exits 0 on success, 1 on any verify mismatch.
-/

def main : IO Unit := do
  IO.println "[1] sha256(hello).size"
  let h := OcapnLean.Crypto.sha256 "hello".toUTF8
  IO.println s!"    = {h.size}; first bytes: {(h.toList.take 8).map (·.toNat)}"

  IO.println "[2] keypair"
  let (pk, sk) ← OcapnLean.Crypto.ed25519Keypair
  IO.println s!"    pk={pk.size}B sk={sk.size}B"

  IO.println "[3] sign + verify (good)"
  let msg : ByteArray := "test message".toUTF8
  let sig := OcapnLean.Crypto.ed25519Sign sk msg
  let ok := OcapnLean.Crypto.ed25519Verify pk msg sig
  IO.println s!"    sig={sig.size}B  verify={ok}"

  IO.println "[4] verify with tampered message"
  let bad := OcapnLean.Crypto.ed25519Verify pk "other".toUTF8 sig
  IO.println s!"    verify(tampered)={bad}"

  IO.println "[5] deterministic from seed"
  let seed : ByteArray := ByteArray.mk (Array.replicate 32 0x42)
  let (pk', sk') := OcapnLean.Crypto.ed25519KeypairFromSeed seed
  let sig' := OcapnLean.Crypto.ed25519Sign sk' msg
  let ok' := OcapnLean.Crypto.ed25519Verify pk' msg sig'
  IO.println s!"    deterministic verify={ok'}"

  if h.size = 32 && ok && !bad && ok' then
    IO.println "OK"
  else
    IO.eprintln "FAIL"
    IO.Process.exit 1
