# `ocapn-lean` — Roadmap

> **Status:** draft, 2026-05-14. Companion to [PLAN.md](./PLAN.md).
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

## Milestone M1 — Data model and codec _(2026-05-26)_

Goal: faithful OCapN data model and Syrup encoder/decoder with proved
round-trip.

- [ ] `OcapnLean/Model.lean` — `inductive Value` (Atom + Container + Reference + Error)
- [ ] `OcapnLean/Model/Equality.lean` — pass-invariant equality predicate
- [ ] `OcapnLean/Syrup.lean` — encode + decode functions
- [ ] **Theorem** `Syrup.decode_encode : ∀ v, decode (encode v) = some v`
- [ ] **Theorem** `Syrup.encode_canonical : ∀ b₁ b₂, decode b₁ = decode b₂ ≠ none → b₁ = b₂` (over the canonical subset)
- [ ] Property-based tests against `projects/syrup-ocapn/test-data/`

**Exit criteria:** Lean theorems above are proved; we can read and write
real Syrup bytes from the upstream test corpus.

## Milestone M2 — One-peer CapTP state machine in Veil _(partially done 2026-05-14)_

**Done already:**
- [x] `OcapnLean/Captp/Spec.lean` — Veil module with `exportNew`, `importNew`,
      `deliverWithAnswer`, `resolvePromise`, `breakPromise`, `abort` actions
- [x] **P8 bootstrap-at-zero** proved — `bootstrap_at_zero ✅` over all 6 actions
- [x] **P2 promise monotonicity** proved — 3 sub-clauses
      (`promise_monotone_fulfilled`, `promise_monotone_broken`,
      `promise_disjoint`), all ✅ across the action set
- [x] Supporting invariants: `imported_functional`, `exported_functional`,
      `resolved_implies_slot`, `broken_implies_slot`
- [x] 55/55 SMT theorems discharged

**Remaining:**
- [ ] Add `op:listen`, `op:get`, `op:index`, `op:untag` actions
- [ ] P7 abort terminal (needs history tracking — punted to a later milestone)

## Milestone M3 — E2E FIFO _(done 2026-05-14, ahead of schedule)_

**Goal:** prove **P1** from PLAN.md.

- [x] `OcapnLean/Captp/Twoparty.lean` — composition of two peers over
      explicit FIFO cursors
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

## Milestone M4 — GC soundness + crossed-hellos _(2026-07-07)_

- [ ] Distributed refcount invariants for `op:gc-exports`
- [ ] **P4 (GC soundness)** discharged
- [ ] **P5 (crossed-hellos determinism)** discharged
- [ ] Bounded model checks for GC stress scenarios via `sat trace { ... }`

## Milestone M5 — No-forgery (capability safety) _(2026-07-21)_

- [ ] Define `reachableAuth` as a `ghost relation` capturing the transitive
      closure of authority-passing events
- [ ] **P3 (no forgery)** discharged
- [ ] This is the hardest single-session proof; expect CTI iteration

## Milestone M6 — Three-party handoffs _(2026-08-04)_

- [ ] `OcapnLean/Captp/Threeparty.lean` — three peers, three pairwise sessions
- [ ] `desc:handoff-give`, `desc:handoff-receive`, gift deposit/withdraw modelled
- [ ] **P6 (handoff non-replay)** discharged
- [ ] Cryptographic signatures treated as a trusted black box
      (`function validSig : pubkey → bytes → sig → Prop`)

## Milestone M1 — Syrup codec _(largely done 2026-05-14)_

- [x] `OcapnLean/Syrup.lean` — encode/decode for bool, int, bytes
- [x] `decode_encode` — **universal** round-trip for the atomic subset
- [x] 16 concrete int/bytes round-trips by `native_decide`
      (redundant given the universal theorem, kept as documentation)
- [x] `OcapnLean/Syrup/Extended.lean` — encode/decode for strings,
      symbols, lists, records (sufficient for CapTP wire frames)
- [x] Cross-impl byte-parity vs the Python reference (4 new
      `native_decide` fixtures for sym/str/list/record)
- [ ] **Deferred:** universal round-trip proof for the container
      types. Requires structural induction over `ValueExt` (which
      nests through `List ValueExt`) and a `partial def → def`
      conversion with a fuel measure or wellfounded recursion.
      Conceptually straightforward but a chunk of work.
- [ ] **Deferred:** extend codec to floats, doubles, dicts, sets.

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
- [ ] **Deferred:** `exportNew_refines` / `importNew_refines`
      lemmas. Same shape as `abort_refines`; just need to mirror the
      table updates.
- [ ] **Deferred:** lifting lemmas for the other Veil safety clauses
      (promise monotonicity, table functionality). Mechanically
      similar to `bootstrapAtZero_lifts`.

## Milestone M8 — Interop _(largely done 2026-05-14)_

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
      any OCapN peer. (Earlier placeholder-crypto interop scripts
      were retired once the server began verifying signatures.)
- [x] **First ocapn-test-suite test passes against our server:**
      `tests.op_start_session.OpStartSessionTest.test_captp_remote_version`
      — `ok` under the upstream `test_runner.py`. This requires the
      server to: parse the inbound `op:start-session` (containing
      Syrup dict-shaped hints), reply with a properly-shaped
      `op:start-session` containing gcrypt-style
      `(public-key (ecc ...))` and `(sig-val (eddsa ...))`
      structures, and emit our location as a 3-arg `ocapn-peer`
      record.
- [ ] **Deferred:** the remaining `op_start_session` tests
      (`invalid_version`, `invalid_signature`, the two
      crossed-hellos tests). Requires:
      (a) Ed25519 signature verification on our side, plus a real
          private key for our own signature (currently stubbed
          to zero bytes — the strict tests reject this);
      (b) modelling the sturdyref-enlivener bootstrap object so
          the crossed-hellos tests can induce a return connection.
- [ ] **Deferred:** the other test modules (`op_deliver`,
      `op_gc`, `op_listen`, `op_abort`, `third_party_handoffs`).
      Each adds dispatch surface — promise pipelining, GC
      refcount tracking, three-party handoff verification, etc.
- [ ] **Deferred:** wire-level interop with Spritely Goblins /
      Endo / Ridley's DObjects. Each requires its own runtime:
      Goblins needs Guile (not installed), Endo a Yarn install of
      a large monorepo, DObjects a Dart SDK. The Python reference
      encoder doubling as a non-Lean impl already validates the
      most important interop guarantee (byte parity at the
      Syrup layer plus correct CapTP handshake semantics).

## Milestone M9 — Locator + sturdyref _(2026-09-15)_

- [ ] `OcapnLean/Locators.lean` — Locator parser/serializer
- [ ] Sturdyref persistence and `fetch` semantics
- [ ] Round-trip theorem for locators

## Milestone M10 — Hardening + paper _(2026-10-13)_

- [ ] All Veil checks pass in CI
- [ ] Fuzzing the impl against the spec via property-based tests
      (Lean's `slim_check` or similar)
- [ ] Short technical report / artifact for the OCapN community

## Proposed-spec extensions to track _(not on the milestone path yet)_

These are CapTP features that are **not in the current draft spec we
implement** (`projects/ocapn-spec/draft-specifications/CapTP
Specification.md`) but are under discussion in the OCapN
pre-standardization group. Slated here so they aren't lost; we'll
fold them into the relevant milestone once the spec language
stabilises.

### Promise shortening

When a promise `P1` resolves to another promise `P2`, the CapTP
session can collapse the chain — subsequent messages targeting `P1`
should be forwarded directly to `P2`'s eventual resolution rather
than hopping through `P1` first. This is the "promise shortening"
optimisation; conceptually closely related to E's "redirector"
behaviour.

**For ocapn-lean:**
- Extend `OcapnLean.Captp.Spec`'s promise table to model the
  forwarding pointer, then prove monotonicity (a shortened
  promise's settled value is invariant under further shortening).
- This is a natural extension of PLAN.md **P2** (promise
  monotonicity); the shortened-chain invariant is `chainResolved P V
  → all-along-chain V` — should fall to the same SMT pipeline.

### `op:flush`

A proposed operation that asks a peer to acknowledge it has
processed all preceding frames on the session before sending the
flush-reply. Used by the test suite (and by GC-sensitive protocols)
to gate on "all in-flight messages drained" without polling.

**For ocapn-lean:**
- New constructor in `OcapnLean.Captp.Messages.Op` once the wire
  shape is settled.
- Affects FIFO reasoning (**P1**): a flush-reply happens-after all
  earlier sends, which strengthens the FIFO statement to
  *delivery-completed-before* rather than just *delivered-before*.
- Affects GC reasoning (**P4**): a flush gives the exporter a
  durable "no in-flight references" witness, simplifying
  collection liveness arguments.

### Tracking

Watch `projects/ocapn-spec/draft-specifications/CapTP
Specification.md` for additions or new draft documents
(`promise-shortening.md`, `op-flush.md` are likely names). The
monthly spec-drift watch (see "Continuous tracks" above) is where
these would land first.

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
