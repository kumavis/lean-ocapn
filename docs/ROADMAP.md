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

**Honest caveat surfaced during Phase A review:** the `ref_fifo` proved in
Phase A guarantees delivery order at the **immediate routing target**
(`routesTo[S, R]`), *not* at an eventual promise-resolution host reached
via forwarding. The canonical CapTP scenario "A sends to promise P on B,
P resolves to obj on C, all of A's msgs should arrive at C in order" is
**not** covered until Phase A.5 adds forwarding. (This was an oversight in
Phase A's original scoping — the model has no `forward` action and no
promise resolution, so msgs sent to a promise simply terminate at the
promise's holder in the spec.)

### M11 Phase A.5 — Promise resolution + forwarding (without shortening) _(landed 2026-05-19)_

Close the gap surfaced by Phase A's review. Model the CapTP behavior
that already exists **without** any shortening optimization: when a promise
`P` (held at B, routed to by sender A) resolves to an object hosted at C,
B forwards A's messages targeting `P` onward to C. End-to-end reference
FIFO at C must hold even though the messages cross **two** wire-level
channels (A→B and B→C).

This is the proof you'd want before any shortening discussion — it
captures the canonical promise scenario the user-facing FIFO guarantee
actually claims, and gives Phase B/C a meaningful baseline to compare
against (shortening optimizes *this* chain, not Phase A's direct-routing
sketch).

**Why it's a separate phase (not folded into A):** Phase A's `send` action
requires `∀ S' D' K, ¬ sentAt S' D' m K` (msg globally fresh). Forwarding
violates this — a msg appears on the wire **twice** (once on A→B by `send`,
once on B→C by `forward`). The model needs a parallel state
(`forwardedAt`) and a `forward` action with weaker preconditions, plus a
**forwarding-preserves-receive-order** invariant that doesn't exist in
Phase A. Cleanest to land as its own Veil module.

**Design discipline for drop-in B/C:** `forward`'s precondition is stated
in terms of the **state at B** (which msgs have been delivered, which
have been forwarded), not in terms of any wire-protocol mechanism. This
mirrors the Phase A pattern where `routesTo` is mutable from day one —
the spec-level proof commits to *what* must be true, not *how* the
implementation arranges it.

- [x] **`OcapnLean/Captp/RefFifoForwarding.lean`** (new module) — augments
      `RefFifo.lean`'s state with:
      - `relation isPromise : ref → Prop` — marks a ref as a promise
      - `relation resolvedTo : ref → vat → Prop` — promise resolved to a
        value hosted at this vat (functional, set once by `resolvePromise`)
      - `relation forwardedAt : vat → vat → msg → Nat → Prop` — B has
        forwarded m onto B→C wire at B's send-index K
      and adds three new actions:
      - `action declarePromise (p : ref)` — marks p as a promise
      - `action resolvePromise (b c : vat) (p : ref)` — B learns p
        resolved to a value at c; sets `resolvedTo p c` and
        `routesTo b p c` (B's own forwarding route for the promise)
      - `action forward (b c : vat) (m : msg)` — B re-emits a previously-
        delivered msg targeting a resolved promise onto B→C wire. Sets
        both `sentAt` and `forwardedAt` (so per-channel cursor logic still
        applies on B→C, plus we can identify "this wire-level send was a
        forward, not an origination").
- [x] **Weakened `send` precondition:** `∀ S' D' K, ¬ sentAt S' D' m K`
      ⇒ `∀ K, ¬ sentAt s d m K` (per-channel uniqueness, not global).
      Same msg can appear on multiple wires via forwarding; freshness at
      origination is enforced by `∀ S', ¬ sentBy S' m`.
- [x] **Weakened `sentAt_has_sentBy` invariant** ⇒
      `sentAt_originator_or_forwarded`: each sentAt entry is either an
      origination (`sentBy S M`) or a forwarding step
      (`forwardedAt S D M K`). Required new supporting invariant
      `sentAt_implies_originator` to rule out forwarding-cycle loopholes
      that don't bottom out in an origination.
- [x] **New invariant `forward_preserves_send_order`** (stated with
      originator's send-index `sentAt`, not deliveredAt — equivalent by
      per-channel FIFO, easier for SMT): for two msgs M1, M2 from the
      same originator S, same target ref, both forwarded by B to C,
      the forward-cursor order at B→C matches the originator's
      send-cursor order at S→B:
      ```
      sentBy S M1 ∧ sentBy S M2 ∧
      targetRef M1 = targetRef M2 ∧
      forwardedAt B C M1 K1 ∧ forwardedAt B C M2 K2 ∧
      sentAt S B M1 J1 ∧ sentAt S B M2 J2 ∧
      J1 < J2 → K1 < K2
      ```
      Discharged together with three supporting invariants surfaced
      during proof: `sent_implies_pending_or_delivered`,
      `earlier_send_delivered_when_later_send_delivered`, and
      `earlier_send_forwarded_when_later_send_forwarded` (the latter
      forces "if a later-sent msg is forwarded, the earlier-sent one
      must also be forwarded"). The deliver action's per-channel
      `sentAt s d m (recvCursor s d)` precondition chains to forward
      preservation via these.
- [x] **New safety `[ref_fifo_e2e]`** — per-sender, per-ref delivery
      order at the **resolution host** matches origination send order,
      across the forwarding chain. The hypothesis explicitly names the
      forwarding hop (`forwardedAt B C M_i`) — the canonical "msg
      traversed S→B→C through B's forwarding" scenario:
      ```
      sentBy S M1 ∧ sentBy S M2 ∧
      targetRef M1 = targetRef M2 ∧
      isPromise (targetRef M1) ∧
      resolvedTo (targetRef M1) C ∧
      sentAt S B M1 K1 ∧ sentAt S B M2 K2 ∧
      forwardedAt B C M1 KF1 ∧ forwardedAt B C M2 KF2 ∧
      delivered B C M1 ∧ delivered B C M2 ∧
      deliveredAt B C M1 N1 ∧ deliveredAt B C M2 N2 ∧
      K1 < K2 → N1 < N2
      ```
      Proof chain: A→B `e2e_fifo` (K1 < K2 → J1 < J2 at B) +
      `forward_preserves_send_order` (sentAt order → forwardedAt order
      at B→C) + B→C `e2e_fifo` (forward-cursor order → N1 < N2 at C).
- [x] **`sat trace [promise_resolve_and_forward]`** — the user's canonical
      scenario: A routes P→B, A sends m₁; A sends m₂; B receives m₁, m₂;
      B resolves P→C; B forwards m₁; B forwards m₂; C receives both.
      SMT finds a concrete model with three distinct vats and the full
      A→B→C chain.
- [x] **`sat trace [resolve_mid_stream]`** — variant where B's resolve
      fires *between* A's sends: A sends m₁; B receives m₁; B resolves
      P→C; A sends m₂ (still A→B because A doesn't know about the
      resolution); B receives m₂; B forwards m₁; B forwards m₂; C
      receives both. Confirms `ref_fifo_e2e` holds even when resolution
      interleaves with origination.
- [x] **`VERIFICATION.md` refreshed** — Phase A.5 adds **272 SMT
      theorems** and a new named safety `ref_fifo_e2e`. Cumulative total:
      377 → 649 (was 8 named P-properties + ref_fifo → now also
      ref_fifo_e2e = 10 named).

**Module breakdown (Phase A.5 delta):**
- RefFifoForwarding.lean: 272 thm (28 invariants + e2e_fifo + ref_fifo +
  ref_fifo_e2e, per init + setupRoute + declarePromise + resolvePromise +
  send + deliver + handoff + forward) + 2 `sat trace` witnesses.

**Relationship to Phase B:** Phase B's `shorten` mutates `routesTo[A, P]`
from B to C *at the sender's side*, bypassing the forwarding chain
entirely. With shortening, A sends directly A→C. The Tribble race is
"messages still in flight on A→B (pre-shorten) get overtaken by new
messages on A→C (post-shorten)." Phase A.5's `ref_fifo_e2e` is exactly
the property shortening breaks — so Phase A.5 must land first to give
Phase B a non-vacuous baseline to violate.

### M11 Phase A.6 — Impl-level refinement of ref FIFO _(opened 2026-05-19)_

Lift the spec-level FIFO proofs (Phases A and A.5) to the executable
implementation. Today `e2e_fifo`, `ref_fifo`, and `ref_fifo_e2e` are
properties of the Veil action model in `Channels.lean`, `RefFifo.lean`,
and `RefFifoForwarding.lean`. The runnable Lean code in `Captp/Impl.lean`
implements one peer's view of one session, and the existing refinement
layer (`Refinement.lean`, `RefinementExtended.lean`) connects only the
**single-peer** properties (P2, P4, P5, P6, P8). All three tiers of P1
remain **spec-only**.

**Why this matters:** the headline claim of M11 is "end-to-end reference
FIFO." Without impl refinement, that's only true of the Veil model — the
runnable Lean code is checked against other implementations on the wire
(interop tests, 24/24) but has no formal connection to the FIFO proof.
Once Phase A.6 lands, the headline holds of the runnable code itself
(modulo the trusted netlayer + Syrup codec, which are verified
separately — Syrup codec round-trip in M1, netlayer behavior in
interop tests).

**Scope:** impl-refinement of fail-stop FIFO (Channels), ref FIFO at
routing target (RefFifo), and ref FIFO across forwarding
(RefFifoForwarding). Phase B's counter-trace doesn't need refinement
(it's about violation, not preservation); Phase C's `op:flush` would
get its own follow-on impl-refinement phase (call it C.6) once the
spec is solid.

**Steps:**

- [ ] **`OcapnLean/Captp/Impl/MultiVat.lean`** (new) — N-vat
      compositional model. Today `Impl.State` is one peer's view of
      one session. This module wraps it into
      `MultiVatState := Map vat Impl.State` plus per-pair channel
      state mirroring the Veil model's
      `pending`/`delivered`/`sentAt`/`deliveredAt` relations. Channels
      are ordered queues of `Msg`s — the Lean side abstracts the
      TCP/WebSocket wire (which is the trusted netlayer's job to keep
      FIFO per-channel, as exercised by interop tests).
      An `MultiVatState.step` operation models one impl action (send,
      deliver, handoff) atomically.

- [ ] **`OcapnLean/Captp/RefinementMultiVat.lean`** (new) — simulation
      relation `simulates_multi : MultiVatState → Channels._st`,
      mapping each Impl-side cursor/queue to its Veil counterpart.
      Lifting lemmas for each Impl action (`Impl.send`, `Impl.deliver`)
      proving simulation-preservation. Headline: `e2e_fifo_lifts`
      — fail-stop FIFO at the impl level.

- [ ] **Augment `Impl.MultiVatState` with refs, routing, sentBy** —
      mirrors `RefFifo.lean`'s additions. Each vat's Impl already
      tracks *which* refs it has imported/exported via its
      import/export tables; this phase adds a `routesTo` map
      (`vat → ref → vat`, the routing decision per (vat, ref)) and a
      `sentBy` tracker (`msg → vat`, the originator). `targetRef`
      becomes a derived field on `Msg` (the `desc:export`/`desc:answer`
      position inside `op:deliver` resolved to a `ref` identity).

- [ ] **Refinement to `RefFifo.lean`** — extend `simulates_multi` to
      cover refs/routing/origin state. Lifting lemmas for
      `setupRoute`, `handoff`. Headline: `ref_fifo_lifts` — per-(sender,
      ref) FIFO at the routing target, at the impl level.

- [ ] **`OcapnLean/Captp/Impl/PromiseForwarding.lean`** (new) —
      adds the missing impl features for Phase A.5's claims:
      - **Promise table** — each vat tracks `isPromise : ref → Bool`
        and `resolvedTo : ref → Option vat`. Set when the peer learns
        the resolution (today's spec module `Captp.Spec` already has
        `resolvePromise`; this lifts it to the multi-vat impl).
      - **Forwarding loop** — when a delivered msg's target ref is a
        resolved promise routing through this vat, re-emit the msg
        onto the forwarding channel toward the resolution host.
        Implements the spec's `forward` action.
      - **Wire-protocol mapping** — real CapTP would re-emit as an
        `op:deliver` to a forwarded position; this phase models it as
        a direct re-emit on the new channel (the abstraction the spec
        already uses).

- [ ] **Refinement to `RefFifoForwarding.lean`** — extend
      `simulates_multi` to cover `isPromise`, `resolvedTo`, `forwardedAt`.
      Lifting lemmas for `declarePromise`, `resolvePromise`, `forward`.
      **Headline: `ref_fifo_e2e_lifts`** — end-to-end reference FIFO at
      the resolution host, at the impl level. This is the impl-level
      version of M11's user-facing claim.

- [ ] **End-to-end runtime test** — `scripts/MultiVatFifoSmoke.lean` or
      similar. Spin up three Impl peers (in-process via direct channels,
      or over TCP via netlayer), exercise the canonical scenario: A
      sends m₁, m₂ to a promise held at B; B resolves to C; B forwards
      both; C receives both in order. Runtime sanity belt on top of the
      formal refinement — analogous to how `client-smoke` and
      `sturdyref-smoke` exercise the single-peer impl.

- [ ] **VERIFICATION.md / PLAN.md refresh** — update the at-a-glance
      table and the per-module refinement matrix. After Phase A.6, the
      P1 row reads: "fail-stop FIFO, ref FIFO at routing target, ref
      FIFO across forwarding — all three proved at the spec level and
      refined to the multi-vat impl."

**Effort target:** ~4 weeks. Multi-vat composition (~1 week) is the
biggest single piece; promise resolution + forwarding in Impl (~1 week)
is mostly new impl code; refinement lemmas across three tiers (~1.5
weeks) borrow the pattern from `RefinementExtended.lean`; runtime test
+ docs (~0.5 week).

**Risks:**
- **Multi-vat impl model might diverge from real-world deployment.**
  Real CapTP runs each vat as a separate process with its own Impl.State;
  the multi-vat model collapses them into a single Lean value. This
  is fine for the *proof* (the proof is about the *protocol behavior*,
  not the process model) but means the runtime test must explicitly
  exercise the in-process abstraction.
- **Promise resolution in Impl is genuinely new code** — `Captp.Spec`
  has `resolvePromise` as a Veil action, but `Captp.Impl` has no
  promise table today. The impl-side promise table needs to handle:
  promise creation (`op:deliver` with `desc:export` positions),
  resolution (`desc:answer` or via the resolver capability), and
  forwarding (the loop driven by `resolvedTo` lookup at delivery time).
- **SMT discharge of refinement lemmas may be slower** — adding refs +
  routing + promises to the simulation relation adds quantifiers; some
  of the new lifting lemmas may need decomposition (the existing
  `*_lifts` are hand-written Lean tactic scripts, not SMT-discharged).

**Relationship to existing refinement:**
- `Refinement.lean` (single-peer): unchanged.
- `RefinementExtended.lean` (single-peer extended actions): unchanged.
- `RefinementMultiVat.lean` (new): the parallel for multi-vat properties.
- Both can coexist — the single-peer lifts continue to give P2, P4, P5,
  P6, P8 at the impl level; the new multi-vat lifts add the three P1
  tiers.

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
