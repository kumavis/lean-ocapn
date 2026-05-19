# `ocapn-lean` — Roadmap

> **Status:** draft, 2026-05-15. Companion to [PLAN.md](./PLAN.md).
> **Cadence:** each milestone closes when the named deliverables exist and
> `lake build` is green.

## Milestone M0 — Bootstrap _(done 2026-05-14)_

Goal: empty Veil project that builds.

- [x] elan installed, Lean 4.24.0 toolchain pinned
- [x] `lakefile.toml` declares Veil dependency
- [x] `lake update` resolves Veil + transitive deps (auto, smt)
- [x] `lake build` succeeds on `OcapnLean.lean` skeleton
- [x] Z3 4.15.4 and cvc5 1.3.1 fetched into `.lake/packages/veil/.lake/build/`
- [x] First Veil module compiles and `#check_invariants` runs

**Exit criteria met.**

## Milestone M1 — Data model and codec _(largely done 2026-05-15)_

Goal: faithful OCapN data model and Syrup encoder/decoder with proved
round-trip.

- [x] `OcapnLean/Model.lean` — algebraic value model
- [x] `OcapnLean/Syrup.lean` — encode/decode for bool, int, bytes
- [x] **Theorem** `Syrup.decode_encode : ∀ v, decode (encode v) = some v`
      — **universal** round-trip proved for the atomic subset
- [x] `OcapnLean/Syrup/Extended.lean` — encode/decode for strings,
      symbols, lists, records, dicts (sufficient for CapTP wire frames)
- [x] `OcapnLean/Syrup/RoundTripExt.lean` — atomic round-trips for
      `.bool`, `.int (both signs)`, `.bytes`, `.str`, `.sym`, plus empty
      `.list []` / `.dict []`
- [x] Cross-impl byte-parity vs the Python reference
      (13 `native_decide` fixtures: 9 base + 4 extended)
- [x] **Universal round-trip for containers — closed.**
      `decodeExt_encodeExt : ∀ v : ValueExt, decodeExt (encodeExt v)
      = some (v, [])` proved over arbitrarily nested
      `list` / `record` / `dict`. Proof goes via mutual induction
      on `@ValueExt.rec` with `motive_1 := RTValue v` and
      `motive_2 := RTListAll items` (a three-conjunct packaging of
      list-body / record-fields / dict-body round-trip). Each
      cons step in a body decoder reduces via the
      `decode{List,RecordFields,Dict}ItemsFuel_cons_step` lemmas
      after observing — through the head-byte analysis lemma
      `encodeExt_head_alt` — that no encoded value starts with a
      closing bracket. Sized-induction is no longer needed: the IH
      from `ValueExt.rec` quantifies over fuel/rest universally, so
      the same fuel suffices for both head and tail recursive
      calls. **Corollary**: `encodeExt_injective` — distinct
      `ValueExt`s have distinct encodings (follows directly via
      `decodeExt`).
- [x] **Float64** added to the codec
      (`OcapnLean.Syrup.ValueExt.float64 (bits : UInt64)`) per
      spec `Notation.md:99` — `D` + 8 bytes IEEE 754 big-endian.
      Stored as raw `UInt64` so NaN payloads and signed zeros
      round-trip without Lean's `Float`-equality collapsing them.
      `RoundTripExt.lean` proof updated for the new dispatch
      byte. Round-trip verified live against Endo by extending
      `client-vs-external`'s echo payload to include
      `.float64 0x3FF0_0000_0000_0000` (= +1.0); Endo's decoder
      handles it (`projects/endo/packages/ocapn/src/syrup/decode.js:25`)
      and the byte-equality check passes.
- [ ] **Skipped:** doubles, sets — not in the OCapN spec.
      Float64 *is* double-precision per `Model.md:114`; OCapN
      has no Set type.

## Milestone M2 — One-peer CapTP state machine in Veil _(largely done 2026-05-15)_

**Done already:**
- [x] `OcapnLean/Captp/Spec.lean` — Veil module with `exportNew`, `importNew`,
      `deliverWithAnswer`, `resolvePromise`, `breakPromise`, `abort`,
      `opGet`, `opIndex`, `opUntag`, `opListen`, `notifyListener` actions
- [x] **P8 bootstrap-at-zero** proved — `bootstrap_at_zero ✅` over all 11 actions
- [x] **P2 promise monotonicity** proved — 3 sub-clauses
      (`promise_monotone_fulfilled`, `promise_monotone_broken`,
      `promise_disjoint`), all ✅ across the action set
- [x] **`listen_notify_after_settle`** safety — a listener is only
      notified after its target has settled. Modelled via a
      `listening : pos → pos → Prop` subscription relation plus a
      `listenerNotified` settled-once witness; both auto-derived
      across all actions
- [x] Supporting invariants: `imported_functional`, `exported_functional`,
      `resolved_implies_slot`, `broken_implies_slot`,
      `listening_implies_slot`, `notified_implies_listening`,
      `notified_implies_settled`
- [x] 143/143 SMT theorems discharged

**Remaining:**
- [x] **P7 abort terminal** — `OcapnLean/Captp/Spec.lean` gains
      a `wasAborted` ghost flag set when `abort` fires; safety
      `abort_terminal: wasAborted ↔ ¬ alive` discharged over all
      11 actions (155 SMT theorems). Combined with the
      `require alive` precondition on every other action, this
      gives the full operational property: once `abort` fires,
      no further state-mutating action can succeed.

## Milestone M3 — E2E FIFO _(done 2026-05-14, ahead of schedule)_

**Goal:** prove **P1** from PLAN.md.

- [x] `OcapnLean/Captp/Channels.lean` (originally `Twoparty.lean` — renamed
      under M11 Phase A) — N-party `(src, dst)` FIFO channels, fail-stop
      FIFO in Miller's *Robust Composition* §19 sense
- [x] FIFO channel modelled with `pending`/`delivered`/`sentAt`/`deliveredAt`
      relations plus `sendCursor`/`recvCursor` per direction
- [x] **`safety [e2e_fifo]`** — "messages delivered in same order sent"
      mechanically discharged
- [x] Supporting inductive invariants (16 total), key ones:
  - `sentAt_injective` — at most one msg per (chan, seq)
  - `pending_at_or_above_recv` — pending msgs are at/ahead of recv cursor
  - `delivered_below_recv_cursor` — delivered msgs are behind recv cursor
  - `deliver_eq_send` — for delivered msgs, deliver-index = send-index
- [x] 48/48 SMT theorems discharged

## Milestone M4 — GC soundness + crossed-hellos _(done 2026-05-14)_

- [x] Distributed refcount invariants for `op:gc-exports`
      (`OcapnLean/Captp/Gc.lean`, 18 SMT thms)
- [x] **P4 (GC soundness)** discharged
- [x] **P5 (crossed-hellos determinism)** discharged
      (`OcapnLean/Captp/CrossedHellos.lean`, 12 SMT thms)
- [x] **Bounded model traces for GC stress** —
      `OcapnLean/Captp/Gc.lean` now exercises three concrete
      action sequences via `sat trace { … } by bmc_sat`: the
      happy-path round-trip, three in-flight ref-ships
      interleaved, and a send-and-dec interleaving that
      stress-tests `exporter_count_decomp` across multiple
      in-flight messages on the same position. SMT-discharged
      witnesses confirm the spec admits these scenarios
      concretely (complement to the *forall-states*
      `#check_invariants` induction).

## Milestone M5 — No-forgery (capability safety) _(done 2026-05-14)_

- [x] `reachableAuth` ghost relation capturing the transitive closure
      of authority-passing events
- [x] **P3 (no forgery)** discharged for the direct-send case
      (`OcapnLean/Captp/NoForgery.lean`, 8 SMT thms)
- [x] **Forwarding case** — `OcapnLean/Captp/NoForgeryForwarded.lean`.
      Adds a `forward` action whose precondition is `chainAuth s p r`
      (a ghost relation populated by `setupAuthority` and `receive`)
      instead of the strict `exported s p r` required by the
      direct-send module. Safety property strengthens to
      `imported D P R → ∃ S, exported S P R` (the original exporter
      may be anywhere along the chain, not just the immediate
      sender). Discharged: 20 SMT theorems across `setupAuthority`,
      `send`, `forward`, and `receive`

## Milestone M6 — Three-party handoffs _(done 2026-05-14)_

- [x] `OcapnLean/Captp/Threeparty.lean` — three peers, three pairwise
      sessions, gift deposit/withdraw modelled
- [x] **P6 (handoff non-replay)** discharged (6 SMT thms)
- [x] Cryptographic signatures treated as a trusted black box
      (`function validSig : pubkey → bytes → sig → Prop`)

## Milestone M7 — Executable implementation _(largely done 2026-05-14)_

Goal: an `IO`-effectful Lean implementation of CapTP plus a refinement
proof against `Captp.Spec`.

- [x] `OcapnLean/Captp/Impl.lean` — runnable handlers (`exportNew`,
      `importNew`, `abort`) with `bootstrapAtZero` proved in pure Lean
      over all transitions
- [x] `OcapnLean/Netlayer.lean` + `Netlayer/Tcp.lean` — abstract
      netlayer with libuv-backed TCP reference implementation
- [x] `OcapnLean/Captp/Run.lean` — Syrup-frame reader/writer
      (`FramedConn`) and `runHandler` event loop over `Netlayer`.
      Verified end-to-end via `scripts/captp-framed-echo.lean`
- [x] `OcapnLean/Captp/Refinement.lean` — explicit
      `simulates : Impl.State → SpecState → Prop` plus
      `initial_simulates`, `abort_refines`, and the lifting lemma
      `bootstrapAtZero_lifts` (Veil safety ⇒ impl safety)
- [x] `exportNew_refines` / `importNew_refines` proved
      (`OcapnLean/Captp/Refinement.lean:119-185`).
- [x] Lifting lemmas for the spec's other safety clauses
      (`importedFunctional_lifts`, `exportedFunctional_lifts`,
      `promiseMonotoneFulfilled_lifts`, `promiseMonotoneBroken_lifts`,
      `promiseDisjoint_lifts`, `listenNotifyAfterSettle_lifts`).
      The promise/listener ones are vacuous on the current impl
      (which doesn't track that state); they're stated so the
      bilateral guarantee is documented for when the impl grows
      those tables.
- [x] Lifts for the *extended* Veil modules:
      `crossedHellosUnique_lifts` (P5), `gcSound_lifts` (P4),
      `handoffNoReplay_lifts` (P6) — all in
      `OcapnLean/Captp/RefinementExtended.lean`.

## Milestone M8 — Interop _(done 2026-05-15)_

- [x] Syrup-layer interop: 13 `native_decide` byte-parity checks
      (9 base + 4 extended) vs Python reference impl
- [x] `OcapnLean/Captp/Bootstrap.lean` — registry of the
      ocapn-test-suite swissnums with reference handlers and
      `dispatchFetch`
- [x] `OcapnLean/Captp/Session.lean` + `OcapnLean.Server`
      (`lake exe ocapn-server`) — listens on TCP, accepts
      multiple connections, drives `Session.run` per connection
- [x] **Wire-level cross-impl interop confirmed**:
      `scripts/interop-invalid-handshake.py` exercises the
      handshake error paths under real Ed25519 crypto, and the
      Lean-as-client driver (`lake exe client-vs-external`) runs
      a full handshake + bootstrap-fetch + echo round-trip against
      any OCapN peer
- [x] **Full ocapn-test-suite passes: 24/24** under the upstream
      `test_runner.py`, covering all six test modules
      (`op_start_session` 5/5, `op_deliver` 4/4, `op_abort` 1/1,
      `op_listen` 3/3, `op_gc` 4/4, `third_party_handoffs` 7/7).
      Matches the @endo/ocapn TypeScript reference implementation's
      pass rate against the same suite (also 24/24) — strong
      independent-impl agreement on the wire format and
      message-sequencing decisions encoded in `Captp/Session.lean`
- [x] Cross-impl client-driving verified: Lean client → @endo/ocapn
      server runs full handshake + bootstrap-fetch + echo
      round-trip OK
- [x] **Cross-impl disagreements documented** in
      [`docs/INTEROP.md`](./INTEROP.md): four numbered disagreements
      with evidence (Disagreement 1 `ocapn-peer` rename ✅ resolved
      upstream v0.16.1; D2 list-shaped pubkey/sig ✅ four-way
      agreement; D3 hints field — we normalised to `.dict []`;
      D4 Ridley netstring framing vs raw Syrup — Ridley deviates
      from Python ref, upstream-issue draft pending)
- [x] Goblins testuds silent-handshake bug reproduced
      (`scripts/diagnostics/goblins-minimal-vat-probe.scm`) with
      draft upstream issue at
      `scripts/diagnostics/UPSTREAM-GOBLINS-ISSUE.md`

## Milestone M9 — Locator + sturdyref _(opened 2026-05-15)_

- [x] `OcapnLean/Locators.lean` — `PeerLocator` and `SturdyRef` structures
      with Syrup-record `toValueExt` / `fromValueExt` per
      `projects/ocapn-spec/draft-specifications/Locators.md`.
- [x] **Round-trip theorems** for peer locator and sturdyref:
      `fromValueExt (toValueExt p) = some p`, both proved.
- [x] **Sturdyref `fetch` semantics layer** —
      `OcapnLean/Captp/SturdyRefClient.lean` exposes
      `SturdyRefClient.fetch : SturdyRef → TransportProfile → IO
      (Session × Nat)`. Resolves `host`/`port` hints to a
      `SocketAddress`, runs `Captp.Client.handshake`, sends
      `[fetch swiss]` on `<desc:export 0>`, awaits the fulfill, and
      returns the imported object's position alongside the live
      session. `TransportProfile.default` matches the de-facto
      convention; `TransportProfile.ridley` bundles the Ridley
      framing / version / hints deviations. Smoke test at
      `scripts/SturdyRefSmoke.lean` (`lake exe sturdyref-smoke`)
      drives the layer against a self-hosted server end-to-end.
- [x] **URI parser** (`PeerLocator.fromUri` / `SturdyRef.fromUri`)
      with a tiny RFC 4648 base32 decoder for the ws-style
      designator segment and an RFC 3986 percent-decoder for hint
      values (Goblins emits `url=ws%3A%2F%2Fhost%3Aport`).
      `client-vs-guile-ws --uri ocapn://…` consumes the canonical
      URI form a Goblins peer publishes — driver no longer needs
      `--port` / `--designator-hex` as separate flags. Verified
      live against Goblins v0.17 + v0.18 (`scripts/diagnostics/goblins-ws-server.scm`
      now emits a `goblins-ws-uri uri=…` banner line via
      `ocapn-id->string`). Round-trip tests in
      `OcapnLean.Test.Locators` plus rejection-path tests.
- [x] Percent-encoder for `toUri` hint values
      (`PeerLocator.percentEncode`). Keys still must be URI-safe
      (they're identifiers like `host`, `port`, `url`); values
      are now `%XX`-encoded for non-URI-safe bytes. Closes the
      `fromUri ∘ toUri = some` loop for arbitrary hint values;
      see the `Test.Locators` round-trip example with
      `url=ws://127.0.0.1:22090` as a hint.
- [ ] **Deferred:** sturdyref persistence (on-disk store, with
      key-rotation policy). Orthogonal to the `fetch` layer above
      (which just consumes an in-memory `SturdyRef`). Skipped per
      project decision — not a near-term need.

## Milestone M10 — Hardening + paper _(2026-10-13)_

- [x] **All Veil checks pass in CI (fresh)** — new
      `verify-veil-fresh` job in `.github/workflows/ci.yml` caches
      `.lake/packages` only (the heavy toolchain deps) and forces
      project sources to recompile, so Lean re-elaborates every
      Veil module on every push and Z3/cvc5 actually re-discharge
      every `#check_invariants`. The job greps the build output
      for ✅/❌ ticks and the `Trusting the SMT solver for N
      theorems` warning, asserting `0 ❌`, `≥ 100 ✅`, and `≥ 100`
      SMT theorems — defensive sanity check that catches both
      Veil regressions and cache-poisoning scenarios. Local
      fresh-build (2026-05-16): 267 SMT theorems, 268 ✅, 0 ❌
      across the 7 Veil modules.
- [x] **Property-based fuzz for the Syrup codec** —
      `scripts/SyrupFuzz.lean` runs ~900 randomised round-trip
      cases against the byte-level `reEncode` predicate, covering
      bool (exhaustive), int, bytes, str, sym, float64, list of
      ints, record with one int field, dict with two fixed keys
      + varying value, and a list of records. Hand-rolled
      generator (`IO.rand`-based); `Plausible.Testable` synthesis
      didn't play nicely in IO do-blocks so a small per-property
      loop was the cleaner shape. Wired into the main CI smoke
      list as `./.lake/build/bin/syrup-fuzz`.
- [x] **`docs/VERIFICATION.md` — verification status report**
      summarising the current SMT discharge counts, trust
      footprint, cross-impl interop matrix, reproduction recipe,
      and known gaps. Pitched as a snapshot companion to
      `PLAN.md` (strategic) and `INTEROP.md` (interop matrix).

## Milestone M11 — End-to-end reference FIFO, shortening, and `op:flush` _(2026-05-18 opened)_

**Goal.** Upgrade the FIFO guarantee from *fail-stop FIFO* (per-CapTP-session,
what `Twoparty.lean`'s `e2e_fifo` proves today) to **end-to-end reference
FIFO** in Mark Miller's sense (Robust Composition §19) — per-sender,
per-logical-reference ordering that **survives promise shortening**.

The milestone is staged as three sub-phases (A → B → C) chosen so that the
model built in **A** admits the mutation in **B** and the synchronization
discipline in **C** as *additive extensions* rather than a rewrite. The
expected dramatic arc: A proves the property, B breaks it via a counter-trace,
C recovers it.

Vocabulary used throughout this milestone follows Miller's two-stage lifecycle
(send → delivery; no separate "process" stage). See
[`projects/ocapn-message-ordering/notes/`](../projects/ocapn-message-ordering/notes/) (vendored from [kumavis/ocapn#1](https://github.com/kumavis/ocapn/pull/1))
for the prose framing and the taxonomy of fail-stop FIFO vs end-to-end
reference FIFO vs causal order (Miller explicitly rejects causal order;
end-to-end reference FIFO is the right target).

### M11 Phase A — N-party reference-FIFO model with handoff _(landed 2026-05-19)_

Built a multi-vat channel model with references as first-class entities,
and proved **end-to-end reference FIFO** under the *immutable-routing* regime
(handoff adds new routing entries, never mutates existing ones).

**Design discipline for drop-in B/C:** `routesTo` is modeled as a
mutable relation from the start, even though Phase A's actions only add to
it. `routesTo_functional` is stated as a one-step constraint (∀ V R W1 W2,
routesTo V R W1 ∧ routesTo V R W2 → W1 = W2), not as an inductive equality
across states — so Phase B's mutating `shorten` can plug in without
re-stating the invariant.

- [x] **`OcapnLean/Captp/Channels.lean`** — renamed from `Twoparty.lean`.
      Docstring rewritten to use Miller's vocabulary (send → delivery; no
      separate "process" stage) and to call out the per-(src, dst)
      ordering as **fail-stop FIFO** rather than the unqualified
      "end-to-end reference FIFO" the original prose claimed. **48 SMT
      theorems** re-discharged unchanged (the `vat` sort was already
      uninterpreted/N-valued; the rename is prose-only).
- [x] **`OcapnLean/Captp/RefFifo.lean`** (new) — augments Channels with:
      - `type ref` (global identity, uninterpreted)
      - `function targetRef : msg → ref` (oracle: unassigned, opaque)
      - `relation routesTo : vat → ref → vat → Prop` (mutable, set by
        `setupRoute` and `handoff` in Phase A)
      - `relation sentBy : vat → msg → Prop` (origin tracking, channel-
        independent so it survives Phase C re-routing)
      - new actions `setupRoute` (primitive route population) and `handoff`
        (idempotent additive route propagation)
- [x] **`safety [ref_fifo]`** — per-sender, per-ref delivery order matches
      send order:
      ```
      sentBy S M1 ∧ sentBy S M2 ∧
      targetRef M1 = targetRef M2 ∧
      delivered S D1 M1 ∧ delivered S D2 M2 ∧
      sentAt S D1 M1 K1 ∧ sentAt S D2 M2 K2 ∧
      deliveredAt S D1 M1 J1 ∧ deliveredAt S D2 M2 J2 ∧
      K1 < K2 → J1 < J2
      ```
      Discharged via `routesTo_functional` + the bridge invariant
      `sentAt_via_route` (which forces D1 = D2 = routesTo S (targetRef M))
      reducing to `e2e_fifo` on the now-equal channel.
- [x] **`action handoff (g r e : vat) (rf : ref)`** — *additive only*:
      requires `routesTo g rf e` and `∀ W, routesTo r rf W → W = e`
      (idempotent / no conflict). Trivially preserves `ref_fifo` (no
      existing routing entry mutates → no in-flight msg changes channel
      mid-flight).
- [x] **`sat trace [three_party_handoff_happy]`** — Alice routes to Carol
      for R, sends m₁; hands R off to Bob; Bob sends m₂; Carol delivers
      both. SMT finds a concrete model with three distinct vats — witness
      that the spec admits the canonical 3-party reference handoff.
- [x] **`VERIFICATION.md` refreshed** — new total **377 SMT theorems**
      (was 267), now covering 9 named P-properties (was 8); the **+110**
      from `RefFifo.lean` and **+1** new `sat trace` witness for the
      3-party handoff.

**Module breakdown (Phase A delta):**
- Channels.lean: 48 thm (15 invariants + e2e_fifo, per init + send + deliver)
- RefFifo.lean: 110 thm (20 invariants + e2e_fifo + ref_fifo, per init +
  setupRoute + send + deliver + handoff) + 1 `sat trace` witness

### M11 Phase B — Promise shortening breaks `ref_fifo` _(counter-trace)_

Add promise shortening as a *mutating* update to `routesTo`. Demonstrate
formally (via `bmc_sat`) that without further synchronization, `ref_fifo`
fails. This is the forcing function for Phase C — and a standalone
contribution to the OCapN spec discussion (the failure mode in Veil rather
than handwave-y prose).

- [ ] **`OcapnLean/Captp/RefFifoShortening.lean`** (new module, imports
      `RefFifo`):
      - `relation isPromise : ref → Prop`
      - `relation resolvedTo : ref → vat → Prop`
      - `action shorten (V : vat) (P : ref)`:
        - require `isPromise P ∧ resolvedTo P newOwner ∧
          routesTo V P oldOwner`
        - **mutate:** `routesTo V P := newOwner` (overwrite, not add)
- [ ] **`sat trace { … } by bmc_sat`** demonstrating the Tribble race
      ([`notes/issue-11-promise-shortening.md`](../projects/ocapn-message-ordering/notes/issue-11-promise-shortening.md)
      § "Where ordering breaks"):
      Alice sends m₁ on P via Bob (slow), Bob resolves P to Carol,
      Alice `shorten`s P → Carol, Alice sends m₂ on P via Carol (fast);
      m₂ delivered at Carol before m₁ traverses A→B→C.
- [ ] **`#check_invariants`** with `[ref_fifo]` **fails** (as expected) —
      capture the failed SMT output as a regression artifact (a `#guard_msgs`
      that the failure mode is the Tribble case, not some other invariant
      collapse).
- [ ] **Document the protocol-level reading** in
      `OcapnLean/Captp/RefFifoShortening.lean`'s docstring: which spec
      semantics (`op:flush`, per-promise seq numbers, `delivered-after`) each
      restore the property, and which one Phase C will mechanize.

**Effort target:** ~3 days. The novel piece is using `bmc_sat` to *exhibit*
the violation as a concrete witness (Veil already supports this — see
`Gc.lean`'s `sat trace` examples).

### M11 Phase C — `op:flush` precondition restores `ref_fifo`

Strengthen `shorten`'s precondition to require the sender's old-channel
queue for that ref to be drained. Re-discharge `ref_fifo`. The wire-level
`op:flush` message is the *protocol mechanism* by which a vat observes the
precondition holds — at the spec level, only the precondition matters, so the
proof is decoupled from the wire shape.

- [ ] **Strengthen `shorten` in `RefFifoShortening.lean`** (or fork to
      `RefFifoShorteningFlushed.lean` if we want the Phase B counter-trace to
      keep `#check_invariants` failing as a regression artifact):
      ```
      action shorten (V) (P) = {
        require isPromise P ∧ resolvedTo P newOwner ∧ routesTo V P oldOwner
        require ∀ M, sentBy V M ∧ targetRef M = P ∧ ¬ delivered M → False
                                                           -- ↑ "flush"
        routesTo V P := newOwner
      }
      ```
      The new precondition is a **state predicate** — "no in-flight messages
      from V targeting P on the old channel." This is exactly what
      `op:flush` synchronizes the sender to observe on the wire.
- [ ] **`safety [ref_fifo]` re-discharged** under the strengthened action.
      The proof splits per-ref delivery into pre- and post-shortening eras;
      each era is governed by per-channel FIFO from `e2e_fifo`, with the
      flush precondition ensuring the eras don't interleave.
- [ ] **`sat trace`** witness of the well-behaved path (Alice flushes, then
      shortens, then sends m₂; Carol's delivery order matches send order).
- [ ] **`sat trace`** witness that *removing the flush guard* re-introduces
      the Tribble race — confirms the precondition is both necessary and
      sufficient at the spec level (`bmc_sat` finds the counter-example
      again).
- [ ] **Wire-level note (no impl work in this milestone):** document in the
      module's prose how `op:flush` (current proposal), per-promise sequence
      numbers, or `delivered-after` each correspond to *different protocol
      mechanisms* satisfying the same spec-level precondition. The
      mechanization is wire-format-agnostic.

**Effort target:** ~1 week. The era split adds 5–10 supporting invariants
around the "before/after shortening" boundary; SMT discharge should be
mechanical once those are stated correctly.

### M11 cross-cutting concerns

- **Not on the path:** wire-level implementation of `op:flush`,
  refinement from the new spec modules to `Captp/Impl.lean`. These are
  follow-up milestones (would need a multi-vat `Impl` runtime which doesn't
  exist yet).
- **Causal order:** explicitly **rejected** per Miller §19 ("E doesn't
  provide CAUSAL order because we don't know how to enforce it among
  mutually defensive machines"). End-to-end reference FIFO is the
  intentional ceiling.
- **Spec-drift dependency:** the OCapN spec doesn't yet mandate end-to-end
  reference FIFO (only per-session FIFO, `Netlayers.md:32`). M11 is
  *ahead* of the spec — the proof is intended as input to the
  pre-standardization discussion, not a refinement of an existing
  requirement.

## Continuous tracks (run alongside milestones)

- **CI.** GitHub Actions: `lake build` on push; cache `.lake/packages` and
  the elan toolchain.
- **Spec-drift watch.** `projects/ocapn-spec` is shallow-cloned; pull
  monthly and diff `draft-specifications/`. Open an issue for any change.
- **Implementation cross-checks.** When in doubt about spec semantics,
  compare behaviour of Goblins / Endo / DObjects in the read-only
  `projects/` clones.

## Risks and known unknowns

| Risk                                                                  | Mitigation                                                          |
| --------------------------------------------------------------------- | ------------------------------------------------------------------- |
| Veil non-EPR fragments needed for invariants                          | Fall back to interactive Lean tactic proofs (`prove_inv_inductive`) |
| Spec changes during the work (it's marked "draft, likely to change")  | Pin to a known commit; spec-drift watch                             |
| Refinement proof effort scales with action count                      | Start with smallest viable subset; expand                           |
| Z3 / cvc5 timeouts on complex invariants                              | Decompose with `solve_clause`; supply hand-written witnesses        |
| Veil 2.0 lands mid-project and changes the DSL                        | Track 1.x on `main`; opt into 2.0 only after M5                     |

## Versioning

Tag `v0.1.0` at M2, `v0.2.0` at M3 (FIFO), `v0.3.0` at M5 (no forgery),
`v0.4.0` at M6 (three-party), `v1.0.0-rc1` at M8 (interop).
