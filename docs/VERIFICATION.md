# `ocapn-lean` — verification status

A concrete snapshot of *what is mechanically verified* and *what
the trust footprint is*. Companion to:

* [`PLAN.md`](./PLAN.md) — the strategic plan and proof scoreboard
  (P1..P8).
* [`ROADMAP.md`](./ROADMAP.md) — milestone-by-milestone progress.
* [`INTEROP.md`](./INTEROP.md) — cross-impl wire interop matrix.

Last updated: 2026-05-19 (commit on `feat/captp-runtime-and-interop`).

## At a glance

| Layer | Verified properties | Discharger |
|---|---|---|
| **CapTP state machine** (Veil) | 10 named safety properties (P1–P8 + `ref_fifo` + `ref_fifo_e2e`) + 25+ supporting invariants, all preserved across all actions. Using Mark Miller's *Robust Composition* §19 vocabulary, `P1` now covers three layers: **fail-stop FIFO** (per (src, dst) channel, `Channels.lean`), **end-to-end reference FIFO at the routing target** (per (sender, ref) under immutable routing, `RefFifo.lean`), and **end-to-end reference FIFO across forwarding** (per (sender, ref) at the resolution host across the A→B→C chain, `RefFifoForwarding.lean`, M11 Phase A.5). | Z3 / cvc5 via Veil's SMT pipeline (`bv_decide` for the float64 atomic round-trip). |
| **Refinement: Veil ↔ Lean impl (single-peer)** | `simulates : Impl.State → SpecState → Prop` plus initial / abort / exportNew / importNew lemmas. Lifting lemmas: `bootstrapAtZero_lifts`, `importedFunctional_lifts`, `exportedFunctional_lifts`, `crossedHellosUnique_lifts`, `gcSound_lifts`, `handoffNoReplay_lifts`, plus four vacuous lifts for the spec's promise / listener fields the impl doesn't yet track. | Hand-written Lean tactic scripts. |
| **Refinement: Veil ↔ Lean impl (multi-vat, M11 Phase A.6)** | `simulatesChannels` / `simulatesRefFifo` / `simulatesRefFifoForwarding` relating `Impl.MultiVat.State` to abstract Veil-side `ChannelsState` / `RefFifoState` / `RefFifoForwardingState`. Canonical projection (`canonicalAbstract*`) gives the simulation by definition. Headline lifts: `e2e_fifo_lifts` (fail-stop FIFO), `ref_fifo_lifts` (per-(sender, ref) FIFO at routing target), `ref_fifo_e2e_lifts` (end-to-end per-(sender, ref) FIFO across A→B→C forwarding). | Hand-written Lean tactic scripts. |
| **Syrup codec** | Universal round-trip `decodeExt (encodeExt v) = some (v, [])` for **all** of `ValueExt` — atomic forms (bool, int, bytes, str, sym, float64) and arbitrarily nested containers (list, record, dict). Encoder injectivity (`encodeExt v₁ = encodeExt v₂ → v₁ = v₂`) follows as a corollary. Property-fuzz (`scripts/SyrupFuzz.lean`) provides a runtime sanity belt. | Lean (`decide` / `simp` / `bv_decide` / `ValueExt.rec` mutual induction). |
| **Locators** | Round-trip `fromValueExt ∘ toValueExt = some` for `PeerLocator` and `SturdyRef`. URI round-trip with percent-encoded hint values. | Lean (`simp`, `native_decide`). |
| **Cross-impl interop** | 24/24 against Python ref suite (this impl + @endo/ocapn). End-to-end TCP handshake against Ridley dobjects (with three opt-in flags for documented disagreements). End-to-end WebSocket handshake against Goblins v0.17 (legacy auth) and Goblins v0.18 (typed auth). | Runtime; gated in CI. |

## Veil SMT discharge counts (per module, fresh build)

| Module | SMT theorems | Named safety properties |
|---|---|---|
| `OcapnLean/Captp/Spec.lean` (P2, P7, P8) | 155 | `bootstrap_at_zero`, `promise_monotone_{fulfilled,broken}`, `promise_disjoint`, `listen_notify_after_settle`, `abort_terminal` |
| `OcapnLean/Captp/Channels.lean` (P1, fail-stop FIFO) | 48 | `e2e_fifo` |
| `OcapnLean/Captp/RefFifo.lean` (P1, end-to-end reference FIFO at routing target, M11 Phase A) | 110 | `e2e_fifo`, `ref_fifo` |
| `OcapnLean/Captp/RefFifoForwarding.lean` (P1, end-to-end reference FIFO across forwarding, M11 Phase A.5) | 272 | `e2e_fifo`, `ref_fifo`, `ref_fifo_e2e` |
| `OcapnLean/Captp/CrossedHellos.lean` (P5) | 12 | `crossed_hellos_unique` |
| `OcapnLean/Captp/Gc.lean` (P4) | 18 | `gc_sound` |
| `OcapnLean/Captp/NoForgery.lean` (P3 direct-send) | 8 | `no_forgery` |
| `OcapnLean/Captp/NoForgeryForwarded.lean` (P3 forwarding) | 20 | `no_forgery_forwarded` |
| `OcapnLean/Captp/Threeparty.lean` (P6) | 6 | `handoff_no_replay` |
| **Total** | **649** SMT theorems, 0 failures | 10 named P-properties |

Plus `Gc.lean` adds 4 `sat trace` witnesses (`bmc_sat`), `RefFifo.lean`
adds 1, and `RefFifoForwarding.lean` adds 2. The Phase A.5 witnesses
cover: the canonical promise-resolves-then-forward path (A routes P→B,
sends m₁, m₂; B resolves P→C; B forwards both; C delivers both), and
the resolve-mid-stream variant (A sends m₁; B delivers; B resolves P→C;
A sends m₂; B delivers; B forwards both in order; C delivers both in
order).

Re-verified from scratch on every CI push by the
`verify-veil-fresh` job (caches `.lake/packages` only; rebuilds
the project from sources so Veil re-invokes Z3/cvc5).

## Property fuzz (`scripts/SyrupFuzz.lean`)

`lake exe syrup-fuzz` runs ~900 random inputs against the codec
on every CI push:

```
bool: ✅ exhaustive (2 cases)
int: ✅ 100 cases, no counter-example
bytes: ✅ 100 cases, no counter-example
str: ✅ 100 cases, no counter-example
sym: ✅ 100 cases, no counter-example
float64: ✅ 100 cases, no counter-example
list of ints: ✅ 100 cases, no counter-example
record <op:deliver int>: ✅ 100 cases, no counter-example
dict {host=str, port=int}: ✅ 100 cases, no counter-example
list <record>: ✅ 100 cases, no counter-example
OK
```

Complements the formal proof for the multi-element container
cases the universal round-trip doesn't yet close, and (for the
atomic cases) provides a runtime check that the build's
elaborated proofs and the runtime decoder agree.

## Cross-impl wire-format interop (CI-gated)

| Direction | Wire | Result |
|---|---|---|
| Python ref → ocapn-lean | TCP raw Syrup | 24/24 (`build-and-test` job) |
| Python ref → @endo/ocapn | TCP raw Syrup | 24/24 (`interop-endo` job) |
| ocapn-lean → @endo/ocapn | TCP raw Syrup | full echo + float64 round-trip |
| ocapn-lean → Ridley dobjects | TCP netstring | handshake completes (`interop-ridley` job, needs `--frame netstring --captp-version 0.1 --hints false`) |
| ocapn-lean → Goblins v0.17 | WebSocket + legacy designator-auth | handshake completes + post-auth probe (`interop-goblins-ws` job) |
| ocapn-lean → Goblins v0.18 | WebSocket + typed designator-auth | handshake completes + post-auth probe (verified locally; CI uses nixpkgs-pinned v0.17) |

See [`INTEROP.md`](./INTEROP.md) for the disagreement-by-disagreement
breakdown and the upstream-issue drafts.

## Trust footprint

What we trust:

1. **Lean 4.24.0 kernel** — including its `decide`, `native_decide`,
   and `bv_decide` tactics. The `bv_decide` tactic does check the
   SAT/SMT result against the kernel via a `decide`-style witness;
   see Lean's documentation for the trust model.
2. **Veil's SMT pipeline** — Veil emits `Trusting the SMT solver
   for N theorems` warnings; those N theorems are taken on the
   word of Z3 / cvc5. The pinned solvers (Z3 4.15.4, cvc5 1.3.1)
   come from Veil's lakefile.
3. **libsodium** for the Ed25519 cryptographic primitives. We
   don't prove anything about the crypto itself; signature
   verification is a trusted external oracle, modelled in the
   Veil specs as a function `validSig : pubkey → bytes → sig →
   Prop`.
4. **libwslay** for RFC 6455 WebSocket frame parsing. Bug surface
   we don't own; OCapN designator-auth on top is implemented in
   Lean.

What we don't trust:

* The OCapN spec drafts themselves — we read them carefully but
  some clauses are ambiguous and our cross-impl interop tests
  are the ground-truth gate against drift.
* Other implementations' wire behaviour. The four documented
  cross-impl disagreements ([`INTEROP.md`](./INTEROP.md)) were
  uncovered exactly because we treat their behaviour as
  observation, not specification.

## Reproducing the verification

```sh
# Fresh-build everything (slow first time — toolchain deps).
lake clean && lake build

# Just re-verify Veil from scratch:
rm -rf .lake/build
lake build OcapnLean.Captp.Spec OcapnLean.Captp.Channels OcapnLean.Captp.RefFifo \
           OcapnLean.Captp.RefFifoForwarding \
           OcapnLean.Captp.CrossedHellos OcapnLean.Captp.Gc \
           OcapnLean.Captp.NoForgery OcapnLean.Captp.NoForgeryForwarded \
           OcapnLean.Captp.Threeparty

# Run the in-process smoke suite (covers the impl + codec end-to-end).
for t in crypto-smoke session-handshake-smoke enlivener-smoke \
         client-smoke sturdyref-smoke uds-smoke ws-smoke \
         ws-auth-smoke syrup-fuzz multi-vat-fifo-smoke; do
  ./.lake/build/bin/$t || exit 1
done

# Cross-impl interop (TCP self-loopback):
./.lake/build/bin/ocapn-server --port 22082 &
cd projects/ocapn-test-suite && python3 test_runner.py \
  'ocapn://a2ef69ddd5f84840970612ff660f5058.tcp-testing-only?host=127.0.0.1&port=22082'
```

CI does all of this on every push; see
[`.github/workflows/ci.yml`](../.github/workflows/ci.yml).

## Known gaps

* **`Captp.Impl` doesn't grow promises / forwarding at the runtime level.**
  M11 Phase A.6 added `Impl/PromiseForwarding.lean` with `resolvePromise`
  and `forward` as pure state-step functions; the refinement lifts use
  them via `simulatesRefFifoForwarding`. But the runtime
  (`Captp.Session`, `Captp.Run`) doesn't yet route incoming `op:deliver`
  msgs through the forwarding loop — the impl runs as single-peer
  today. Bridging is a separate runtime feature; the formal refinement
  already commits to *what* the impl must do if it implements
  forwarding, and the multi-vat smoke
  (`scripts/MultiVatFifoSmoke.lean`) exercises the state-step functions
  end-to-end.
* **Refinement for promise / listener tables.** The Veil spec
  tracks `promiseResolved`, `promiseBroken`, `listening`, and
  `listenerNotified`; the executable impl doesn't yet, so the
  corresponding refinement lifts are *vacuously true* on the
  current impl. They'll become substantive when the impl grows
  those tables.
* **Goblins testuds bug.** Still reproduces on v0.18; upstream
  issue draft pending one remaining cross-validation step
  (porting `examples/try-base-netlayer.scm` to a standalone
  script).
