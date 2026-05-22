/* OcapnLean — libsodium FFI shim.
 *
 * Wraps the four libsodium primitives needed by the CapTP protocol:
 *
 *   crypto_hash_sha256
 *   crypto_sign_ed25519_keypair
 *   crypto_sign_ed25519_detached
 *   crypto_sign_ed25519_verify_detached
 *
 * Built as part of the OcapnLean lake target; linked into the
 * downstream binaries via `moreLinkArgs := ["-lsodium"]`.
 */

#include <lean/lean.h>
#include <sodium.h>
#include <string.h>

/* libsodium requires sodium_init() to be called once before any
 * other API. We guard the first call so it's idempotent. */
static int g_sodium_ready = 0;

static int ensure_sodium(void) {
  if (g_sodium_ready) return 0;
  if (sodium_init() < 0) return -1;
  g_sodium_ready = 1;
  return 0;
}

/*------------------------------------------------------------------*/
/* SHA-256                                                          */
/*------------------------------------------------------------------*/

/* `sha256 : @& ByteArray -> ByteArray`
 * Pure function. Returns a fresh 32-byte ByteArray. */
LEAN_EXPORT lean_obj_res ocapnlean_sha256(b_lean_obj_arg input) {
  const size_t in_len = lean_sarray_size(input);
  const uint8_t *in_data = lean_sarray_cptr(input);

  lean_obj_res out = lean_alloc_sarray(1, 32, 32);
  uint8_t *out_data = lean_sarray_cptr(out);

  if (ensure_sodium() < 0) {
    memset(out_data, 0, 32);
    return out;
  }
  crypto_hash_sha256(out_data, in_data, in_len);
  return out;
}

/*------------------------------------------------------------------*/
/* Ed25519 keypair                                                  */
/*------------------------------------------------------------------*/

/* `ed25519Keypair : IO (ByteArray × ByteArray)`
 *
 * Returns `(pubkey 32B, privkey 64B)`.
 *
 * libsodium's "secret key" is 64 bytes: a 32-byte seed concatenated
 * with the public key. This is the format the rest of the libsodium
 * API consumes.
 *
 * The Lean wrapper passes `IO.RealWorld` as the first argument and
 * expects back an `IO.Result`. We wrap our pair with
 * `lean_io_result_mk_ok`. */
LEAN_EXPORT lean_obj_res ocapnlean_ed25519_keypair(lean_obj_arg /* io_state */) {
  lean_obj_res pk = lean_alloc_sarray(1, 32, 32);
  lean_obj_res sk = lean_alloc_sarray(1, 64, 64);

  if (ensure_sodium() < 0) {
    memset(lean_sarray_cptr(pk), 0, 32);
    memset(lean_sarray_cptr(sk), 0, 64);
  } else {
    crypto_sign_ed25519_keypair(lean_sarray_cptr(pk), lean_sarray_cptr(sk));
  }

  /* Build the pair (pk, sk) and wrap in IO.Result.ok. */
  lean_obj_res tup = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(tup, 0, pk);
  lean_ctor_set(tup, 1, sk);
  return lean_io_result_mk_ok(tup);
}

/* Derive a keypair from a 32-byte seed. Useful for tests and for
 * reproducing a known identity.
 *
 * `ed25519KeypairFromSeed : @& ByteArray -> ByteArray × ByteArray` (pure)
 *
 * If the input isn't exactly 32 bytes we return (zero-pk, zero-sk).
 */
LEAN_EXPORT lean_obj_res ocapnlean_ed25519_keypair_from_seed(b_lean_obj_arg seed_arr) {
  const size_t seed_len = lean_sarray_size(seed_arr);
  const uint8_t *seed = lean_sarray_cptr(seed_arr);

  lean_obj_res pk = lean_alloc_sarray(1, 32, 32);
  lean_obj_res sk = lean_alloc_sarray(1, 64, 64);

  if (seed_len != 32 || ensure_sodium() < 0) {
    memset(lean_sarray_cptr(pk), 0, 32);
    memset(lean_sarray_cptr(sk), 0, 64);
  } else {
    crypto_sign_ed25519_seed_keypair(lean_sarray_cptr(pk),
                                     lean_sarray_cptr(sk),
                                     seed);
  }

  lean_obj_res tup = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(tup, 0, pk);
  lean_ctor_set(tup, 1, sk);
  return tup;
}

/*------------------------------------------------------------------*/
/* Ed25519 sign                                                     */
/*------------------------------------------------------------------*/

/* `ed25519Sign : @& ByteArray -> @& ByteArray -> ByteArray`
 *                  privkey         message       64-byte signature
 *
 * Deterministic given (sk, msg); modelled as pure. If `sk` isn't
 * 64 bytes we return a zero signature (the caller's verify will fail). */
LEAN_EXPORT lean_obj_res ocapnlean_ed25519_sign(b_lean_obj_arg sk_arr,
                                                 b_lean_obj_arg msg_arr) {
  const size_t sk_len = lean_sarray_size(sk_arr);
  const size_t msg_len = lean_sarray_size(msg_arr);

  lean_obj_res sig = lean_alloc_sarray(1, 64, 64);
  uint8_t *sig_data = lean_sarray_cptr(sig);

  if (sk_len != 64 || ensure_sodium() < 0) {
    memset(sig_data, 0, 64);
    return sig;
  }

  unsigned long long siglen = 64;
  crypto_sign_ed25519_detached(sig_data, &siglen,
                               lean_sarray_cptr(msg_arr), msg_len,
                               lean_sarray_cptr(sk_arr));
  return sig;
}

/*------------------------------------------------------------------*/
/* Random bytes                                                     */
/*------------------------------------------------------------------*/

/* `randomBytes : USize -> IO ByteArray`
 * Returns `n` bytes from libsodium's CSPRNG (`randombytes_buf`).
 * Used for nonces (e.g. the WebSocket designator-auth challenge). */
LEAN_EXPORT lean_obj_res ocapnlean_random_bytes(size_t n, lean_obj_arg /*io*/) {
  lean_obj_res ba = lean_alloc_sarray(1, n, n);
  if (n == 0) return lean_io_result_mk_ok(ba);
  if (ensure_sodium() < 0) {
    /* libsodium init failed; surface a Lean IO error so callers can
     * notice rather than silently get zeros. */
    return lean_io_result_mk_error(
        lean_mk_io_user_error(lean_mk_string("randomBytes: sodium_init failed")));
  }
  randombytes_buf(lean_sarray_cptr(ba), n);
  return lean_io_result_mk_ok(ba);
}

/*------------------------------------------------------------------*/
/* Ed25519 verify                                                   */
/*------------------------------------------------------------------*/

/* `ed25519Verify : @& ByteArray -> @& ByteArray -> @& ByteArray -> Bool`
 *                    pubkey        message       signature
 *
 * Returns `Bool` (Lean encodes this as `uint8_t`). Returns false on
 * any size mismatch. */
LEAN_EXPORT uint8_t ocapnlean_ed25519_verify(b_lean_obj_arg pk_arr,
                                               b_lean_obj_arg msg_arr,
                                               b_lean_obj_arg sig_arr) {
  const size_t pk_len = lean_sarray_size(pk_arr);
  const size_t msg_len = lean_sarray_size(msg_arr);
  const size_t sig_len = lean_sarray_size(sig_arr);

  if (pk_len != 32 || sig_len != 64 || ensure_sodium() < 0) return 0;

  return crypto_sign_ed25519_verify_detached(lean_sarray_cptr(sig_arr),
                                              lean_sarray_cptr(msg_arr),
                                              msg_len,
                                              lean_sarray_cptr(pk_arr)) == 0;
}
