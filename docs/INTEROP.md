# OCapN interop test results

The upstream OCapN [test suite](https://github.com/ocapn/ocapn-test-suite)
is a Python program that drives an OCapN peer over the
`tcp-testing-only` netlayer and asserts protocol-level behaviour. We
use it as our headline conformance check and to validate that the
protocol itself has a single shared interpretation.

## Result summary _(2026-05-20)_

**Python suite as client → ocapn-lean as server** (the upstream
conformance suite). Run by `build-and-test` in CI on every push.

| op_start_session | op_deliver | op_abort | op_listen | op_gc | third_party_handoffs | **Total** |
|---|---|---|---|---|---|---|
| 5/5 | 4/4 | 1/1 | 3/3 | 4/4 | 7/7 | **24/24** |

**ocapn-lean as client → external server** (true Lean ↔ X interop).
Run by per-peer CI jobs.

| External peer | Scenarios exercised | CI job | Status |
|---|---|---|---|
| **@endo/ocapn** | echo round-trip, greeter callback, promise pipelining via Car Factory Builder | `interop-lean-vs-endo` | ✅ |
| **Spritely Goblins v0.17** (WS, legacy auth) | RFC 6455 handshake → designator-auth (raw 64-byte) → post-auth probe | `interop-goblins-ws` | ✅ |
| **Ridley dobjects** (TCP, netstring framing) | handshake completes with `--frame netstring --captp-version 0.1 --hints false` | `interop-ridley` | ✅ |

Both implementations of the conformance suite (ocapn-lean and
@endo/ocapn) pass it. The two share no code paths — Endo is a
TypeScript+SES implementation; ocapn-lean is Lean 4 on libsodium
FFI. And the new `interop-lean-vs-endo` job goes the *other* way:
the Lean client driver (`scripts/ClientVsEndo.lean`) connects to
Endo's test server and exercises the same well-known objects the
Python suite uses, validating bidirectional wire-format agreement —
not just same-direction pass rate.

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
| Spritely Goblins ≥ v0.16.1 (`projects/goblins/goblins/ocapn/ids.scm:76`) | `ocapn-peer` (`<ocapn-node>` kept as deprecated alias at line 54) | ✅ |

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
| ocapn-lean (`OcapnLean/Captp/Run.lean`)            | raw Syrup (default), `--frame netstring` opt-in | ✅ |
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

**What we did.** Added `Framing = .raw | .netstring` to
`OcapnLean/Captp/Run.lean` and plumbed an opt-in `--frame
netstring` flag through `client-vs-external` and `ocapn-server`.
Default stays `.raw` — every other peer (Python suite, Endo,
Goblins, ocapn-lean self) keeps working unchanged, including the
24/24 conformance run.

**Verified end-to-end against real Ridley** (2026-05-16) using a
small Dart probe in `scripts/diagnostics/ridley-tcp-test-server.dart`
that spins up Ridley's own `TCPTestingNetLayer`. Recipe:

```sh
# In one shell (inside the Ridley submodule, after dart pub get and
# placing the libsodium path file as the script comment describes):
dart run ridley-tcp-test-server.dart --port 22047

# In another:
lake exe client-vs-external -- --port 22047 \
  --frame netstring --captp-version 0.1 --hints false \
  --handshake-only
```

Both sides report success: `[external-smoke] handshake ok` on the
Lean side and
`PASS: framing + handshake interop verified end-to-end` on Ridley's.
The handshake exercises Ridley's netstring de-framer, Syrup
decoder, version check, and Ed25519 signature verification — and
the reverse path through framing for our reply. All three flags are
needed because Ridley diverges from the de-facto convention on
three orthogonal points (framing here, `captpVersion` 0.1 vs 1.0,
and the hints normalisation noted in Disagreement 3).

The flag is local to `tcp-testing-only`-style transports; it does
not change the spec-defined wire format anywhere else.

## Goblins WebSocket interop (working as of 2026-05-16)

Lean ↔ Goblins is verified end-to-end over the WebSocket netlayer
(`(goblins ocapn netlayer websocket)` on the Goblins side, our
`OcapnLean.Netlayer.Ws` on ours). This routes around the
testuds silent-handshake bug described below — WebSocket setup
doesn't deadlock the vat dispatcher the way `^testuds-netlayer`
does, so it works fine from a standalone Guile script.

**Verified against both Goblins versions** (2026-05-16):
- v0.17.0 (`nix-shell -p guile-goblins`, what nixpkgs ships) —
  works with `--auth legacy`.
- v0.18.0 (built from our submodule source via
  `nix-shell -p autoconf automake guile-fibers guile-gcrypt
  guile-gnutls guile-websocket … && cd projects/goblins &&
  ./bootstrap.sh && ./configure && make && ./pre-inst-env guile
  …`) — works with `--auth typed`. Legacy is rejected (`peer
  closed before reply`), confirming v0.18 enforces the typed
  shape only.

**Stack on each side:**

* Wire: plain TCP, then the RFC 6455 client/server handshake.
  Lean's TCP socket is plain POSIX (`c/ws.c`); RFC 6455 frame
  encoding / masking is delegated to **libwslay**. Goblins uses
  Guile's `(web socket)` modules.
* OCapN designator-auth: long-lived Ed25519 designator keypair
  per peer. Client sends a fresh challenge over the WebSocket;
  server signs it with the designator key and replies; client
  verifies against the public key embedded in the peer's
  `ocapn://` URI. **Two wire shapes coexist in the wild**:
  Goblins ≤ v0.17 (and the version nixpkgs currently ships) uses
  raw 64-byte challenges; v0.18+ (and Endo) uses a typed
  `<init:peer-auth …>` record. Both are implemented in
  `OcapnLean.Netlayer.Ws.Authenticated` — call `connectLegacy` for
  the former, `connect` for the latter. See the v0.18 commit
  `61c0247f4` "Make websocket netlayer sign typed record not raw
  bytes" in the upstream Goblins history.
* CapTP `op:start-session` and everything above: the same code we
  use over TCP and UDS (`Captp.Client.handshake`, `Captp.Session`,
  etc.). Reused unchanged thanks to the message-oriented
  `Netlayer` abstraction.

**Reproducer** (also wired into CI as the `interop-goblins-ws`
job):

```sh
# Shell 1 — start the Goblins peer:
nix-shell -p guile guile-goblins guile-fibers --command \
  "GUILE_AUTO_COMPILE=0 guile \
    scripts/diagnostics/goblins-ws-server.scm 22090"

# Shell 1 prints (single line):
# goblins-ws-ready designator-hex=8e9a17… port=22090

# Shell 2 — Lean client:
lake exe client-vs-guile-ws -- --port 22090 \
  --designator-hex 8e9a17... --auth legacy
```

Output ends with `OK` on success. The exchange validates:

  1. RFC 6455 client/server handshake (Sec-WebSocket-Key /
     Sec-WebSocket-Accept via SHA-1 + base64 in `c/ws.c`).
  2. libwslay binary-frame encode/decode + client masking.
  3. The Goblins-v0.17 designator-auth dance (raw 64-byte
     challenge → syrup-encoded `<sig-val …>` reply → Ed25519
     verification against the published designator pubkey).
  4. The Lean `Netlayer` interface returning a working
     post-auth message-oriented endpoint suitable for CapTP.

The Lean-side WebSocket implementation is approximately 500 lines
of C in `c/ws.c` (SHA-1 + base64 + HTTP upgrade + wslay glue) plus
~250 lines of Lean (`OcapnLean.Ws`, `OcapnLean.Netlayer.Ws`, the
`Authenticated` auth dance). New build dep: `libwslay`
(nixpkgs `wslay-1.1.1`, Ubuntu `libwslay-dev`).

### Goblins testuds, current state (2026-05-16 update)

Submodule now pinned at Goblins **v0.18.0** (was v0.17.0). The
testuds silent-handshake bug **still reproduces** in v0.18.0 —
`scripts/diagnostics/goblins-minimal-vat-probe.scm` hangs at
`[min] a-nl ok` exactly as it does in v0.17. Recipe:

```sh
cd projects/goblins
nix-shell -p autoconf automake guile guile-fibers guile-gcrypt \
  guile-gnutls guile-websocket pkg-config texinfo \
  --command "./bootstrap.sh && ./configure && make && \
    timeout 15 ./pre-inst-env guile --no-auto-compile \
      ../../scripts/diagnostics/goblins-minimal-vat-probe.scm"
# exits with 124 (timeout); output stops at "[min] a-nl ok"
```

That closes one of the two cross-validation TODOs in
`scripts/diagnostics/UPSTREAM-GOBLINS-ISSUE.md` (the
"test on v0.18 / main HEAD" line). The remaining TODO — porting
upstream's REPL-driven `examples/try-base-netlayer.scm` to a
standalone script — would distinguish "Goblins bug" from "how we
call it"; if the upstream example also hangs standalone, file
the issue. Original text below:



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
  because raw Syrup doesn't emit a `len:` prefix.
  Suggested fix: in
  `lib/src/net_layers/tcp_testing_net_layer/tcp_testing_net_layer.dart`,
  switch the read side (lines 105-145) and the write side
  (lines 159-160) to raw Syrup framing — i.e., delegate to the
  same `syrup-read` / `syrup-write` loop other implementations use.
  No other Ridley netlayer affected.

  In the meantime, ocapn-lean ships an opt-in `--frame netstring`
  flag (see Disagreement 4 above) that lets `client-vs-external`
  and `ocapn-server` interop with Ridley as it stands.

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
  interop against Ridley over real wire is now verified end-to-end:
  Lean handshakes successfully against Ridley's `TCPTestingNetLayer`
  via the opt-in `--frame netstring --captp-version 0.1 --hints
  false` combination (see Disagreement 4 above for the recipe).
  Default behaviour is unchanged — the spec/de-facto-conformant
  codec stays put; the flags are local to driving Ridley.
  Goblins is now interop-verified end-to-end over WebSocket
  (`scripts/diagnostics/goblins-ws-server.scm` + `lake exe
  client-vs-guile-ws --auth legacy`). The testuds path remains
  blocked by the silent-handshake runtime issue (see above) with
  a reproducer in this repo and an upstream issue draft pending
  cross-validation; the WebSocket route sidesteps that bug.
