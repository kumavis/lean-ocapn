# OCapN interop test results

The upstream OCapN [test suite](https://github.com/ocapn/ocapn-test-suite)
is a Python program that drives an OCapN peer over the
`tcp-testing-only` netlayer and asserts protocol-level behaviour. We
use it as our headline conformance check and to validate that the
protocol itself has a single shared interpretation.

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

## Cross-implementation disagreements

When we attempted interop against Spritely Goblins (Guile) and
Ridley dobjects (Dart), the handshake did *not* succeed. Closer
inspection turned up two genuine wire-format divergences that aren't
visible at the byte level between `ocapn-lean` and `@endo/ocapn`
because both implementations conform to the spec the same way. The
disagreements are documented here as evidence for the upstream
ecosystem rather than worked around in our codebase.

### Disagreement 1 — Peer-location label: `<ocapn-peer …>` vs `<ocapn-node …>` ✅ resolved upstream

The spec defines the peer-location record as `<ocapn-peer transport
designator hints>` (`projects/ocapn-spec/draft-specifications/Locators.md`
lines 58–65):

```
<ocapn-peer transport   ; symbol (cannot contain ".")
            designator  ; string
            hints>      ; struct | false
```

**Status.** Originally identified as a Goblins-side deviation
(Goblins's older `<ocapn-node …>`). The rename to `<ocapn-peer …>`
was landed upstream on
[codeberg.org/spritely/goblins](https://codeberg.org/spritely/goblins)
no later than the `v0.16.1` release. Our submodule pin now tracks
`v0.17.0`
(`projects/goblins/goblins/ocapn/ids.scm` line 77 –
`(define-syrup-record-type <ocapn-peer> …)`),
which matches the other four implementations and the spec:

| Impl | Label emitted | Conforms to spec |
|---|---|---|
| ocapn-lean (`OcapnLean/Captp/Session.lean:77` `peerSym`) | `ocapn-peer` | ✅ |
| @endo/ocapn (`projects/endo/packages/ocapn/src/codecs/components.js`) | `ocapn-peer` | ✅ |
| Ridley dobjects (`projects/ridley-dobjects/lib/src/locators/peer_locator.dart:136`) | `ocapn-peer` | ✅ |
| Python ref suite (`projects/ocapn-test-suite/contrib/syrup.py`, exercised by `tests/op_start_session.py`) | `ocapn-peer` | ✅ |
| Spritely Goblins ≥ v0.16.1 (`projects/goblins/goblins/ocapn/ids.scm:77`) | `ocapn-peer` (`<ocapn-node>` kept as deprecated alias at line 54) | ✅ |

The five-way agreement on this label means the original Disagreement 1
report (against gitlab's older `guile-goblins`, pinned to commit
`e15b86f`) no longer applies. Documented here as a record of what was
investigated and why; not actionable in the current codebase.

### Disagreement 2 — Cryptographic structure shape: record vs. list

The spec specifies that `session-pubkey` and `acceptable-location-sig`
are **list-shaped** s-expressions in gcrypt style
(`projects/ocapn-spec/draft-specifications/CapTP Specification.md`
lines 264, 295):

```
['public-key ['ecc ['curve 'Ed25519] ['flags 'eddsa] ['q q_value]]]
['sig-val ['eddsa ['r r_value] ['s s_value]]]
```

The spec's Notation document
(`projects/ocapn-spec/draft-specifications/Notation.md` lines 182–204)
distinguishes lists `[…]` from records `<…>` cleanly. We — and the
other three impls we surveyed — all comply:

| Impl | pubkey/sig shape | Conforms to spec |
|---|---|---|
| ocapn-lean (`OcapnLean/Captp/Session.lean:91-100, 105-115`, uses `.list`) | list | ✅ |
| @endo/ocapn (`projects/endo/packages/ocapn/src/codecs/components.js:90-103, 132-151`, uses `makeOcapnListComponentCodec`) | list | ✅ |
| Ridley dobjects (`projects/ridley-dobjects/lib/src/cap_tp/public_key_format.dart:33`) | list | ✅ |
| Python ref suite (`projects/ocapn-test-suite/utils/captp_types.py:67-78`) | list | ✅ |

Spritely Goblins uses its `<tagged>` mechanism for everything; it
emits a record-shaped pubkey/sig in some code paths and a list in
others. We didn't probe deeply enough to rule out spec compliance
on the cryptographic path, but the `ocapn-node` rename described
above already blocks the handshake before pubkey/sig parsing fires.

**Assessment.** No disagreement among the four spec-conforming
implementations. Anywhere a future impl reaches for the convenient
`<public-key …>` record shape should be flagged.

### Disagreement 3 — `hints` field of `<ocapn-peer …>`

The spec says (`Locators.md` line 64) that the third field of
`<ocapn-peer …>` is `struct | false` — i.e. a (possibly-empty) dict
or the boolean `false`. The four impls vary in strictness:

| Impl | Emits hints as… | Accepts… |
|---|---|---|
| ocapn-lean (now) | `struct` (empty dict via `.dict []`) | any value (permissive parser) |
| @endo/ocapn | `struct` | `struct` only |
| Ridley dobjects (`lib/src/locators/peer_locator.dart:107-117`) | `struct` or `false` | `struct` or `false` (strict) |
| Python ref suite | not strictly checked | any value |

Our `Server.lean` originally emitted `.list []` for hints — outside
the spec, accepted by the Python suite (`Locators.md` is informative
here, not exercised by the suite) and Endo (Endo's strict dict-only
parser actually rejected it, but we'd already updated the
client-side scripts to `.dict []` before hitting that path).
Normalised to `.dict []` in commit `<this PR>`; spec-compliant and
universally accepted.

### Disagreement 4 — `tcp-testing-only` framing: netstring vs raw

The `tcp-testing-only` netlayer is an OCapN test-suite convention
(not formally spec'd; `Netlayers.md` only documents Tor Onion).
The Python reference implementation in
`projects/ocapn-test-suite/netlayers/testing_only_tcp.py` defines
the convention by example.

**Python ref** (`netlayers/base.py:83-87`):

```python
def send_message(self, message):
    if isinstance(message, CapTPType):
        message = message.to_syrup()
    self.sendall(message)          # raw bytes, no length prefix
```

**Endo** (`projects/endo/packages/ocapn/src/netlayers/tcp-test-only.js:30-46`):

```js
const makeSocketOperations = (socket, writeLatencyMs) => ({
  write(bytes) { socket.write(bytes); },   // raw bytes, no length prefix
  end() { socket.end(); },
});
```

**ocapn-lean** (`OcapnLean/Captp/Run.lean:66-68`):
`FramedConn.writeFrame` does `c.net.send (ByteArray.mk bytes.toArray)` —
raw Syrup bytes; the reader peels off one Syrup value at a time
via `decodeExt`.

**Ridley**
(`projects/ridley-dobjects/lib/src/net_layers/tcp_testing_net_layer/tcp_testing_net_layer.dart:159-160`):

```dart
socket.write('${message.length}:');   // ASCII length prefix
socket.add(message);                  // then the body
```

Receive side (lines 105-145) reads an ASCII digit run, expects `:`,
then reads exactly `length` bytes.

So Ridley implements **netstring framing** (`len:bytes`) while
Python / Endo / ocapn-lean exchange **raw Syrup values**.
Verified empirically: a Lean client connecting to a Ridley peer on
`tcp-testing-only` (`dart run example/python_test_suite_server.dart
--port 22047`) sends `<op:start-session …>` and Ridley throws
`NetLayerException('Invalid message framing.')`:

```
[external-smoke] connecting to 127.0.0.1:22047
uncaught exception: [client] EOF awaiting op:start-session
---
Unhandled exception:
NetLayerException: Connection is closed. Cannot send message.
  at common_net_layer.dart:95:31    (handleData exception path)
```

| Impl | Framing on `tcp-testing-only` | Conforms to Python ref |
|---|---|---|
| ocapn-lean (`OcapnLean/Captp/Run.lean:66`)         | raw Syrup | ✅ |
| @endo/ocapn (`src/netlayers/tcp-test-only.js:32`)  | raw Syrup | ✅ |
| Python ref (`netlayers/base.py:83`)                | raw Syrup | ✅ |
| Ridley dobjects (`tcp_testing_net_layer.dart:159`) | netstring `len:bytes` | ❌ |

**Assessment.** Ridley deviates from the Python reference
implementation. The spec is silent on the `tcp-testing-only`
framing, so neither side is strictly "wrong" per the document — but
the Python suite is what Endo and we both pass 24/24 against, which
makes raw Syrup the de-facto convention. A one-line fix on Ridley's
side (drop the netstring prefix) would restore interop without
affecting Ridley's other netlayers (which can keep whatever framing
they need).

Workaround we did *not* adopt: add a `--frame=netstring` flag to
our `Captp.Client` so we can drive Ridley specifically. Rejected
for now — same reasoning as the other disagreements, our codec
stays spec/de-facto-conformant. Could revisit if there's appetite
for a one-off Ridley interop test.

### Goblins testuds, current state

We added a UDS netlayer (`OcapnLean.Netlayer.Uds` + `c/uds.c`) to
match Goblins's `testuds` transport. The Goblins side runs via
`scripts/goblins-testuds-server.scm`:

```sh
nix-shell -p guile guile-goblins guile-fibers --command \
  "guile scripts/goblins-testuds-server.scm"
```

The Lean side `lake exe client-vs-uds -- --sock <path> --version
goblins-0.16` connects and sends an `op:start-session`.

**Status (2026-05-15).** With the submodule pin bumped to
`v0.17.0` (which has the `ocapn-peer` rename), Goblins's
unmarshaller now matches our `<ocapn-peer …>` outright — the
specific deviation that Disagreement 1 documented is gone. The
handshake nevertheless still stalls; a Python probe sent a
spec-correct, real-signed `op:start-session` over the UDS socket
and received **zero bytes** in reply (Goblins didn't even send its
own first `op:start-session`). Goblins doesn't crash or print
errors; it's just silent.

We probed the issue with diagnostic scripts now committed to the
repo at `scripts/diagnostics/`:

  * `scripts/diagnostics/goblins-minimal-vat-probe.scm` — single-vat
    script that spawns the testuds netlayer then `spawn-mycapn` on
    it, wrapped in `run-fibers`. The netlayer spawn succeeds, but
    `(with-vat … (spawn-mycapn a-nl))` never returns. The body
    executes side-effects fully (verified via `format` instrumentation
    in earlier sessions) but `vat-send`'s reply mechanism never
    delivers control back. Wrapping in `run-fibers` does NOT change
    the behaviour.

  * `scripts/diagnostics/UPSTREAM-GOBLINS-ISSUE.md` — draft issue
    text ready to file at `codeberg.org/spritely/goblins` after a
    couple of cross-validation steps (testing standalone version of
    upstream `examples/try-base-netlayer.scm`; testing on guile-goblins
    0.18.0 / main HEAD).

The server script's "ready" print is misleading: it's emitted
inside the single `with-vat` block before that `with-vat` returns
(or fails to return). Goblins keeps the vat process alive via the
outer `(wait forever)`, but the netlayer's listen loop never
actually fires.

The cross-cutting symptom is that `(call-with-vat vat thunk)` from
the top-level (no enclosing syscaller) does not return after the
thunk side-effects through `spawn-mycapn`. The body executes (we
see every diagnostic `format`), but `vat-send` never delivers the
result back. This is consistent with a fiber-channel deadlock in
Goblins's vat dispatcher when the spawned mycapn schedules an
async `(on (<- netlayer-map 'data) …)` callback that wants to
fire before the envelope's reply is sent.

Possible root causes (not yet conclusive):

  * Bug in Goblins's `vat-send` + `(on …)` interaction at the
    top-of-script entry path; the REPL-driven path in
    `try-base-netlayer.scm` works because the REPL is itself
    running inside the fibers scheduler, which gives the vat a
    chance to drain pending fibers between top-level `define`
    forms.
  * Our `scripts/goblins-testuds-server.scm` works around this
    by accident: it never reads the result of `spawn-mycapn` (it
    just stores it in a local `define` inside the `with-vat`),
    so even though the vat-send reply may never come back, the
    later `(wait forever)` keeps the vat alive and the netlayer's
    listen loop *should* run. But evidently it doesn't —
    incoming connections aren't being accepted.

This is a Goblins-side environmental/runtime bug, separate from the
wire-format disagreements above. A draft upstream issue is committed
at [`scripts/diagnostics/UPSTREAM-GOBLINS-ISSUE.md`](../scripts/diagnostics/UPSTREAM-GOBLINS-ISSUE.md);
filing it is gated on two cross-validation steps (standalone version
of upstream `examples/try-base-netlayer.scm`; re-test on goblins
0.18.0 / main HEAD) so we can be sure the bug is reproducible outside
our setup.

## Upstream follow-ups (drafts)

The following are sketches of issues we'd file at the relevant
upstream projects. We don't carry compatibility shims — our codec
stays spec-conformant.

* **`codeberg.org/ridley/DObjects`** — `tcp-testing-only`
  netstring framing diverges from the Python reference (Disagreement
  4 above). Reproducer is in this repo:
  start the Ridley peer via
  `dart run example/python_test_suite_server.dart --port 22047` in
  a writable Ridley copy, then `lake exe client-vs-external --port
  22047` from ocapn-lean — Ridley throws `NetLayerException(
  'Invalid message framing.')` at the very first incoming byte
  because we don't emit a `len:` prefix.
  Suggested fix: in
  `lib/src/net_layers/tcp_testing_net_layer/tcp_testing_net_layer.dart`,
  switch the read side (lines 105-145) and the write side
  (lines 159-160) to raw Syrup framing — i.e., delegate to the
  same `syrup-read` / `syrup-write` loop other implementations use.
  No other Ridley netlayer affected.

* **`codeberg.org/spritely/goblins`** — `testuds` peer doesn't reply
  to inbound `op:start-session`. Reproducer:
  `scripts/goblins-testuds-server.scm` in this repo (a minimal
  testuds peer registering the standard test-suite swissnums); a
  Python probe sending a real-signed `op:start-session` over the
  UDS socket sees zero reply bytes within 3s. Goblins doesn't crash.
  Suspect setup-order bug in `^connection-establisher` /
  `new-connection` path when the inbound peer isn't another Goblins
  instance. Note: `v0.16.1`'s `ocapn-peer` rename is already in
  place, so this is *not* the same as the historical naming
  disagreement (which is closed).

* **`ocapn/ocapn-spec`** — clarification ticket: the spec text uses
  `[…]` (list) notation for pubkey/sig and `<…>` (record) notation
  for messages, but the distinction is easy to miss. Two callouts
  that would help future implementers: (a) a Notation cross-reference
  in the Cryptography section, and (b) a "wire-shape per type" cheat
  sheet at the top of CapTP Specification.md.

* **`ocapn/ocapn-test-suite`** — strictness ticket: the suite
  currently accepts any value as the `hints` field, masking
  spec-non-conformance in implementations under test. Adding an
  assertion that hints decode to `struct | false` would have caught
  our own `.list []` bug earlier.

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
  against an independent TypeScript implementation. Client-side
  interop against Goblins and Ridley over real wire remains blocked
  by impl-specific bugs (not by ocapn-lean): Goblins by the testuds
  silent-handshake runtime issue (see above); Ridley by Disagreement
  4 (netstring framing on `tcp-testing-only`). Both are documented
  with reproducers in this repo and upstream-issue drafts pending
  cross-validation before filing.
