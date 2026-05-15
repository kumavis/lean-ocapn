# OCapN interop test results

The upstream OCapN [test suite](https://github.com/ocapn/ocapn-test-suite)
is a Python program that drives an OCapN peer over the
`tcp-testing-only` netlayer and asserts protocol-level behaviour. We
use it to validate that `ocapn-lean` speaks the protocol correctly
and — by also running the same suite against another implementation
— that the protocol itself has a single shared interpretation.

## Result summary _(2026-05-15)_

| Server impl   | op_start_session | op_deliver | op_abort | op_listen | op_gc | third_party_handoffs | **Total** |
|---|---|---|---|---|---|---|---|
| **ocapn-lean** (this repo) | 5/5 | 4/4 | 1/1 | 3/3 | 4/4 | 7/7 | **24/24** |
| **@endo/ocapn** (`projects/endo`) | 5/5 | 4/4 | 1/1 | 3/3 | 4/4 | 7/7 | **24/24** |

Both implementations pass the entire suite. The two share no code
paths — Endo is a TypeScript+SES implementation; ocapn-lean is a
Lean 4 implementation built on libsodium FFI. Identical pass-rate
against the same test suite is strong evidence that the wire-format
and message-sequencing decisions in `OcapnLean.Captp.Session` match
the consensus encoded in the upstream suite.

## Reproducing

### ocapn-lean

```sh
# In ocapn-lean repo root:
lake build ocapn-server
./.lake/build/bin/ocapn-server --port 22082 &

# In another shell (NixOS host):
nix-shell -p "python3.withPackages (p: with p; [ cryptography stem ])" \
  --command "cd projects/ocapn-test-suite && \
    python3 test_runner.py \
      'ocapn://a2ef69ddd5f84840970612ff660f5058.tcp-testing-only?host=127.0.0.1&port=22082'"
```

### @endo/ocapn

Endo lives at `projects/endo` (a read-only git submodule). To run
its OCapN test server we work in a writable copy and use a
downloaded yarn 4 binary (corepack can't symlink into the read-only
nix store):

```sh
# One-time setup:
rsync -a projects/endo/ ~/endo-work/
curl -fsSL https://repo.yarnpkg.com/4.13.0/packages/yarnpkg-cli/bin/yarn.js \
  -o /tmp/yarn4-bin/yarn.js

# Install + run:
nix-shell -p nodejs --command "\
  cd ~/endo-work && \
  YARN_NODE_LINKER=node-modules NODE_OPTIONS='--max-old-space-size=2048' \
    node /tmp/yarn4-bin/yarn.js install --mode=skip-build && \
  node --expose-gc ./packages/ocapn/test/python-test-suite/index.js"
```

Then the Python suite is run the same way, pointing at
`ocapn://<addr>.tcp-testing-only?host=127.0.0.1&port=22046`.

## Notes

* `tests.op_abort` runs in ~0.005s against Endo but takes ~60s
  against ocapn-lean. Both pass the assertion, but ocapn-lean's path
  leaves the TCP connection open after marking the session aborted
  (the Python client then times out reading rather than getting a
  clean connection close). A future commit can teach
  `Captp.Session` to close the socket once the aborted flag flips —
  cosmetic for the test but spec-aligned.

* Some test modules require both peers to keep state across multiple
  TCP connections from the same peer (the handoff exporter & gifter
  cases). These exercised the `Session.PeerSessionRegistry` and
  `Session.GiftsTable` plumbing we added in commits `58fcc6a` /
  `8ad615b` / `d78446e`.

* This validates ocapn-lean against the Python reference *and*
  against an independent TypeScript implementation. It does *not*
  yet validate ocapn-lean's behaviour as a CapTP **client** — our
  Lean impl is currently server-only.
