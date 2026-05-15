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
- [ ] **Deferred:** universal round-trip proof for the container types
      (`decodeExt_encodeExt : ∀ v : ValueExt`). Strong-induction attempt
      hit an algebraic obstruction at the singleton-list cons case where
      `(encL [v]).length = (encodeExt v).length`, so byte-length induction
      can't supply a strict `< k - 1` IH for the head. Resolution paths:
      custom well-founded recursion on a combined `(fuel, depth)` measure,
      OR weaken atomic helpers from `length + 1 ≤ fuel` to `length ≤ fuel`.
- [ ] **Deferred:** extend codec to floats, doubles, sets.

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

## Milestone M4 — GC soundness + crossed-hellos _(done 2026-05-14)_

- [x] Distributed refcount invariants for `op:gc-exports`
      (`OcapnLean/Captp/Gc.lean`, 18 SMT thms)
- [x] **P4 (GC soundness)** discharged
- [x] **P5 (crossed-hellos determinism)** discharged
      (`OcapnLean/Captp/CrossedHellos.lean`, 12 SMT thms)
- [ ] **Deferred:** bounded model checks for GC stress scenarios via
      `sat trace { ... }`

## Milestone M5 — No-forgery (capability safety) _(done 2026-05-14)_

- [x] `reachableAuth` ghost relation capturing the transitive closure
      of authority-passing events
- [x] **P3 (no forgery)** discharged for the direct-send case
      (`OcapnLean/Captp/NoForgery.lean`, 8 SMT thms)
- [ ] **Deferred:** forwarding case (a peer re-exporting an imported
      reference); same skeleton, additional ghost relation update on
      `desc:export` of an imported pos

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
- [ ] **Deferred:** `exportNew_refines` / `importNew_refines`
      lemmas. Same shape as `abort_refines`; just need to mirror the
      table updates.
- [ ] **Deferred:** lifting lemmas for the other Veil safety clauses
      (promise monotonicity, table functionality). Mechanically
      similar to `bootstrapAtZero_lifts`.

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
- [ ] **Deferred:** URI parser/serializer
      (`ocapn://<designator>.<transport>[?hints]…/s/<swiss>`). Needs
      RFC3986 escaping work; the in-band Syrup view above is what
      the rest of the codebase exercises.
- [ ] **Deferred:** sturdyref persistence + `fetch` semantics layer.
      Depends on `Captp.Session` machinery already in place;
      essentially wiring the `SturdyRef.peer` + `swiss` into an
      outbound `op:deliver <fetch swiss>` from `Captp.Client`.

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
