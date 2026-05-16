/-!
# Cryptographic primitives — libsodium FFI

Wraps the four libsodium primitives the OCapN protocol needs:

  * `sha256 (data : ByteArray) : ByteArray`
    32-byte SHA-256 digest. Used for `Public Identifier` and
    `Session ID` derivation (`SHA256∘SHA256` per the CapTP spec).

  * `ed25519Keypair : IO (ByteArray × ByteArray)`
    Generates a fresh keypair. Returns `(pk 32B, sk 64B)`. The
    secret key is libsodium's "combined" format (seed ++ pubkey)
    that the other API entry points consume.

  * `ed25519KeypairFromSeed (seed : ByteArray) : ByteArray × ByteArray`
    Deterministic counterpart of the above; useful for tests and
    for re-deriving a known identity.

  * `ed25519Sign (sk msg : ByteArray) : ByteArray`
    Detached 64-byte Ed25519 signature. Modelled as pure since the
    signing function is deterministic given `(sk, msg)`.

  * `ed25519Verify (pk msg sig : ByteArray) : Bool`
    Detached verification. Returns `false` on any length mismatch.

The C shim lives in `c/crypto.c`; the lakefile compiles it and links
`-lsodium` into the precompiled `OcapnLean.Crypto` module so both
the executable (`lake exe ocapn-server`) and the interpreter
(`lake env lean --run …`) can call into it.
-/

namespace OcapnLean.Crypto

@[extern "ocapnlean_sha256"]
opaque sha256 (input : @& ByteArray) : ByteArray

@[extern "ocapnlean_ed25519_keypair"]
opaque ed25519Keypair : IO (ByteArray × ByteArray)

@[extern "ocapnlean_ed25519_keypair_from_seed"]
opaque ed25519KeypairFromSeed (seed : @& ByteArray) : ByteArray × ByteArray

@[extern "ocapnlean_ed25519_sign"]
opaque ed25519Sign (sk : @& ByteArray) (msg : @& ByteArray) : ByteArray

@[extern "ocapnlean_ed25519_verify"]
opaque ed25519Verify (pk : @& ByteArray) (msg : @& ByteArray) (sig : @& ByteArray) : Bool

/-- `n` cryptographically-random bytes from libsodium's CSPRNG.
Used for nonces (e.g. the WebSocket designator-auth challenge). -/
@[extern "ocapnlean_random_bytes"]
opaque randomBytes (n : USize) : IO ByteArray

/-- Convenience: double-SHA-256 (matches the spec's Public Identifier
derivation: `SHA-256(SHA-256(serialised pubkey))`). -/
def sha256d (input : ByteArray) : ByteArray :=
  sha256 (sha256 input)

end OcapnLean.Crypto
