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

## Lean client → external server

The Lean-side client driver in `OcapnLean.Captp.Client` can also
*drive* any OCapN peer; see `scripts/ClientVsExternal.lean` /
`lake exe client-vs-external -- --port N`. Verified end-to-end:

| Server | Wire | Result |
|---|---|---|
| ocapn-lean (self)   | TCP | echo round-trip OK |
| @endo/ocapn         | TCP | echo round-trip OK |
| ocapn-lean (self)   | UDS | echo round-trip OK (`lake exe uds-smoke`) |

## Goblins (testuds)

We added a UDS netlayer (`OcapnLean.Netlayer.Uds` + `c/uds.c`)
specifically to interop with Guile-Goblins's
[`testuds`](goblins/goblins/ocapn/netlayer/testuds.scm) transport,
the simplest local-only netlayer Goblins ships with.

The Goblins side runs via `scripts/goblins-testuds-server.scm`:

    nix-shell -p guile guile-goblins guile-fibers --command \
      "guile scripts/goblins-testuds-server.scm"

That listens on `/tmp/ocapn-lean-uds/goblins.sock`. The Lean side
binary `lake exe client-vs-uds -- --sock <path> --version
goblins-0.16` connects, sends `op:start-session`, and awaits the
peer's reply.

**Status:** Lean self-host over UDS passes. Lean ↔ Goblins
handshake hangs at the receive step. Likely cause is that Goblins's
typed-record unmarshallers (`goblins/ocapn/captp-types.scm`)
need the `<op:start-session>` and `<ocapn-peer>` records to be
emitted with Goblins-specific marshalling tags rather than the
plain symbol-labelled records the spec defines. The on-wire bytes
look identical to a naked-spec reader (Python, @endo/ocapn, our own
impl), but Goblins's reader filters by marshaller association. A
follow-up commit would either:

  * teach our wire builder to emit goblins-compatible record tags,
    *or*
  * patch the goblins side to also accept naked spec records.

## Notes

* `tests.op_abort` was previously 60s under ocapn-lean (we left the
  TCP socket open after setting `aborted`) and 5ms under Endo. Fixed
  in commit `1b18c60` by closing the socket alongside the flag flip;
  now matches Endo's behaviour.

* Some test modules require both peers to keep state across multiple
  TCP connections from the same peer (the handoff exporter & gifter
  cases). These exercised the `Session.PeerSessionRegistry` and
  `Session.GiftsTable` plumbing we added in commits `58fcc6a` /
  `8ad615b` / `d78446e`.

* This validates ocapn-lean against the Python reference *and*
  against an independent TypeScript implementation. It does *not*
  yet validate ocapn-lean's behaviour as a CapTP **client** — our
  Lean impl is currently server-only.
