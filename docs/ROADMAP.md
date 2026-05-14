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

## Milestone M7 — Executable implementation _(2026-08-18)_

Goal: an `IO`-effectful Lean implementation of CapTP plus a refinement
proof against `Captp.Spec`.

- [ ] `OcapnLean/Captp/Impl.lean` — runnable handlers
- [ ] `OcapnLean/Netlayer.lean` — `class Netlayer` + reference TCP/TLS impl
- [ ] `def simulates : Impl.State → Spec.State → Prop`
- [ ] One refinement lemma per action — about 10 lemmas total
- [ ] Executable demo: two local processes establishing a session, doing
      `fetch`, sending a deliver, getting a result back

## Milestone M8 — Interop _(2026-09-01)_

- [ ] `OcapnLean.Test.Interop` runs the public `ocapn-test-suite`
- [ ] Interop confirmed with **at least one** of:
  - Spritely Goblins (Guile)
  - Endo's `@endo/ocapn`
  - Ridley's DObjects (Dart)
- [ ] Document any spec ambiguities discovered

## Milestone M9 — Locator + sturdyref _(2026-09-15)_

- [ ] `OcapnLean/Locators.lean` — Locator parser/serializer
- [ ] Sturdyref persistence and `fetch` semantics
- [ ] Round-trip theorem for locators

## Milestone M10 — Hardening + paper _(2026-10-13)_

- [ ] All Veil checks pass in CI
- [ ] Fuzzing the impl against the spec via property-based tests
      (Lean's `slim_check` or similar)
- [ ] Short technical report / artifact for the OCapN community

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
