# `ocapn-lean` — Plan

> **Status:** 7/8 named proofs of behavior mechanically discharged
> (last updated 2026-05-15). See §5 for the per-proof scoreboard.
> **Scope:** a Lean 4 implementation of the OCapN protocol with safety
> properties of the CapTP layer mechanically proved using
> [Veil](https://github.com/verse-lab/veil).

## 1. Goals

1. **Full OCapN implementation in Lean 4** — Syrup codec, the CapTP state
   machine (sessions, exports/imports, promises, three-party handoffs,
   distributed GC), a pluggable netlayer interface, and a reference TCP+TLS
   netlayer for interop with Goblins / Endo / Ridley's DObjects.

2. **Verified safety properties for the CapTP state machine** — expressed as
   inductive invariants on an abstract transition system written in Veil,
   discharged automatically by Z3/cvc5 with interactive Lean fall-back when
   the auto-solver gives up.

3. **A refinement relation tying the executable implementation to the verified
   spec** — so that what we ship in production is provably an inhabitant of
   the protocol whose properties we proved.

4. **Interop tests** — run [`ocapn-test-suite`](https://github.com/ocapn/ocapn-test-suite)
   against the executable.

We are **not** aiming for liveness proofs in this phase (Veil's liveness
support is on its roadmap). We are also not aiming for cryptographic
soundness proofs — EdDSA signature verification is taken as a trusted
external primitive.

## 2. Layering

The OCapN protocol decomposes naturally; we mirror that decomposition in
the Lean module structure:

```
                                   ┌──────────────────────────────────┐
   Layer 4: applications           │  user code: actors, sturdyrefs   │
                                   └──────────────────────────────────┘
                                   ┌──────────────────────────────────┐
   Layer 3: CapTP                  │  sessions, op:deliver, promises, │
                                   │  exports/imports, handoffs, GC   │
                                   └──────────────────────────────────┘
                                   ┌──────────────────────────────────┐
   Layer 2: Syrup codec            │  binary self-describing encoding │
                                   └──────────────────────────────────┘
                                   ┌──────────────────────────────────┐
   Layer 1: Netlayer (transport)   │  reliable in-order bytes (TCP,   │
                                   │  Tor onion, libp2p, …)           │
                                   └──────────────────────────────────┘
```

| Lean module                   | Responsibility                                                                  | Verification status (target)            |
| ----------------------------- | ------------------------------------------------------------------------------- | --------------------------------------- |
| `OcapnLean.Model`             | OCapN abstract data model: Atom / Container / Reference / Error                 | Pure Lean, structural                   |
| `OcapnLean.Syrup`             | Round-trip codec; `encode ∘ decode = id` and canonicalisation                   | Lean theorems (no Veil needed)          |
| `OcapnLean.Captp.Messages`    | Algebraic types for `op:*` and `desc:*` messages                                | Pure Lean                               |
| `OcapnLean.Captp.Spec`        | **Veil** module: state, transitions, invariants for one CapTP session pair      | Veil `#check_invariants`                |
| `OcapnLean.Captp.Channels`    | N-party `(src, dst)` FIFO channels — *fail-stop FIFO* (Miller §19)              | Veil `#check_invariants`                |
| `OcapnLean.Captp.RefFifo`     | Channels + refs + routing + handoff — *end-to-end reference FIFO at routing target* (M11 Phase A) | Veil `#check_invariants`                |
| `OcapnLean.Captp.RefFifoForwarding` | RefFifo + promise resolution + forwarding — *end-to-end reference FIFO across A→B→C forwarding* (M11 Phase A.5) | Veil `#check_invariants` |
| `OcapnLean.Captp.Impl.MultiVat` + `Impl.PromiseForwarding` | N-vat compositional impl model + promise / forwarding actions (M11 Phase A.6) | Pure-Lean state machine |
| `OcapnLean.Captp.RefinementMultiVat` | Multi-vat refinement: `simulatesChannels` / `simulatesRefFifo` / `simulatesRefFifoForwarding` + three headline lifts | Hand-written Lean refinement |
| `OcapnLean.Captp.Threeparty`  | Three-vat composition for handoff correctness                                   | Veil + Lean simulation                  |
| `OcapnLean.Captp.Impl`        | Executable `IO`-based implementation                                            | Refinement lemma against `Captp.Spec`   |
| `OcapnLean.Netlayer`          | Netlayer typeclass; reference TCP netlayer impl                                 | Property-based tests                    |
| `OcapnLean.Locators`          | OCapN locator parser/serializer                                                 | Round-trip Lean theorem                 |
| `OcapnLean.Test.Interop`      | Wire-level test harness against `ocapn-test-suite`                              | Runtime conformance                     |

## 3. The protocol surface we must model

Drawing from `projects/ocapn-spec/draft-specifications/CapTP Specification.md`:

**Operations:** `op:start-session`, `op:deliver`, `op:deliver-only` (a
`op:deliver` with `answer-pos=false` and `resolve-me-desc=false`), `op:listen`,
`op:abort`, `op:get`, `op:index`, `op:untag`, `op:gc-exports`, `op:gc-answers`.

> **Note:** an earlier informal list named `op:pick`; the current draft
> spec subsumes it under `op:get` / `op:index` / `op:untag`.

**Descriptors:** `desc:import-object`, `desc:import-promise`, `desc:export`,
`desc:answer`, `desc:sig-envelope`, `desc:handoff-give`, `desc:handoff-receive`.

**Identity:** EdDSA per-session keypairs, session-pubkey, Public Identifier
(SHA256∘SHA256 of serialised pubkey), Session ID, signed location attestation.

**Bootstrap methods:** `fetch`, `deposit-gift`, `withdraw-gift`.

## 4. Abstract state — what Veil sees

For the two-party CapTP module (`Captp.Spec`), the state of *one peer*'s view
of one session is (the analogous mirror lives on the other peer):

| Veil declaration                                    | Meaning                                                                |
| --------------------------------------------------- | ---------------------------------------------------------------------- |
| `type vat`                                          | Uninterpreted identifier of a vat (one per CapTP endpoint)             |
| `type pos` (positive integer abstracted)            | Position in the import / export / answer tables                        |
| `type oref`                                         | Local object reference                                                 |
| `relation imported : pos → oref → Prop`             | Peer's import table — what we've imported from the partner             |
| `relation exported : pos → oref → Prop`             | Our export table — what we've exposed to the partner                   |
| `relation answer   : pos → oref → Prop`             | Answer table — promises created by `op:deliver`                        |
| `function importRefcount : pos → Nat`               | Distributed GC refcount per import                                     |
| `function answerLive     : pos → Bool`              | Whether an answer slot is still alive                                  |
| `relation pending : Nat → CaptpMsg → Prop`          | Multiset of in-flight messages on the wire (Nat is a sequence number)  |
| `function nextSeqSend : Nat`                        | Next sequence number we will assign                                    |
| `function nextSeqRecv : Nat`                        | Next sequence number we expect to receive                              |
| `relation promiseResolved : pos → ResolvedValue`    | Has a promise been resolved to a value?                                |
| `relation promiseBroken   : pos → Error`            | Has a promise been broken?                                             |
| `relation sessionAlive : Bool`                      | False after `op:abort`                                                 |

The wire is modelled as a per-direction sequenced multiset (Veil idiom for
FIFO). For two peers the full module instantiates the above mirror.

## 5. Proposed proofs of behavior

The first three are top priority; the rest are sequenced behind them. Each
is stated as a `safety` clause plus the supporting `invariant` clauses.

**Scoreboard (2026-05-19, 649 SMT theorems passing — Spec 155, Channels 48,
RefFifo 110, RefFifoForwarding 272, Gc 18, CrossedHellos 12, NoForgery 8,
NoForgeryForwarded 20, Threeparty 6):**

| ID | Property | Status | Module |
| --- | --- | --- | --- |
| P1 | fail-stop FIFO (per-channel basis) | ✅ proved | `Captp/Channels.lean` |
| P1 | end-to-end reference FIFO at routing target (M11 Phase A) | ✅ proved (immutable-routing regime) | `Captp/RefFifo.lean` |
| P1 | end-to-end reference FIFO across A→B→C forwarding (M11 Phase A.5) | ✅ proved (no shortening) | `Captp/RefFifoForwarding.lean` |
| P2 | promise resolution monotonicity (×3) | ✅ proved | `Captp/Spec.lean` |
| P3 | no-forgery (direct-send case) | ✅ proved (forwarding deferred) | `Captp/NoForgery.lean` |
| P4 | GC soundness (wire-delta refcount) | ✅ proved | `Captp/Gc.lean` |
| P5 | crossed-hellos determinism | ✅ proved | `Captp/CrossedHellos.lean` |
| P6 | three-party handoff non-replay | ✅ proved | `Captp/Threeparty.lean` |
| P7 | abort terminal | ✅ proved (`wasAborted` ghost; safety `abort_terminal: wasAborted ↔ ¬ alive`) | `Captp/Spec.lean` |
| P8 | bootstrap-at-zero | ✅ proved | `Captp/Spec.lean` |

### P1. End-to-end reference FIFO (the headline proof)

**Statement.** For any two vats Alice and Bob with a single CapTP session,
the order in which `op:deliver` messages sent from Alice arrive at Bob's
*delivery point* (the local object referenced by `to-desc`) is the same as
the order in which Alice's application code invoked the send. Symmetrically
for the other direction.

**Why it's non-trivial.** The netlayer guarantees per-direction byte FIFO;
the *CapTP layer* is what we need to verify does not buffer, reorder, drop,
or duplicate `op:deliver` messages targeting the same export-position before
local dispatch. Promise pipelining, GC and answer-table cleanup interact in
ways that could plausibly reorder.

**Veil formulation.**

```lean
-- per-channel sequence numbers
function seqDeliveredFromTo : vat → vat → pos → Nat   -- last delivered seq

safety [fifo_per_target]
  ∀ A B P S1 S2,
    -- two deliver-events for the same (sender, target export) ordered on send
    sentDeliver A B P S1 ∧ sentDeliver A B P S2 ∧ S1 < S2 →
    -- delivered in that order at B's local target
    (deliveredLocally A B P S1 → deliveredLocally A B P S2 →
       seqDeliverIdx A B P S1 < seqDeliverIdx A B P S2)
```

**Inductive invariants we expect to need (sketch).**
- Sequence numbers on the wire are monotonically increasing per direction.
- For any in-flight delivery with sequence `n`, no delivery with sequence
  `< n` is still in flight (consumed-prefix invariant).
- The `delivered` projection at the receiver is a permutation-preserving
  prefix of the sent sequence.

This proof exercises Veil end-to-end: it requires composing two `Captp.Spec`
instances over a FIFO channel and lifting per-peer invariants through the
composition.

### P2. Promise resolution monotonicity

**Statement.** Once a promise at position `p` is resolved (`fulfill` with a
value `v`), it stays resolved with the same `v`. Symmetrically, once broken
with error `e`, it stays broken with `e`. A promise cannot be both
resolved and broken.

```lean
safety [promise_monotone_fulfilled]
  promiseResolvedAt P V1 T1 ∧ promiseResolvedAt P V2 T2 → V1 = V2
safety [promise_monotone_broken]
  promiseBrokenAt P E1 T1 ∧ promiseBrokenAt P E2 T2 → E1 = E2
safety [promise_disjoint]
  ¬ (promiseResolved P ∧ promiseBroken P)
```

This is a standard "decided-once" property analogous to Paxos's `accepted_once`.

### P3. No reference forgery (the C-list invariant)

**Statement.** A peer can hold an authoritative reference to an object only
if the partner has *sent* it that reference at some point in the session,
or it received it as the bootstrap object (position 0), or it was the
fulfilment of a promise transitively grounded in one of the above.

```lean
ghost relation reachableAuth : vat → oref → Prop :=
  -- transitive closure of (sent-or-bootstrap)
  ...
safety [no_forgery]
  imported P R → reachableAuth selfVat R
```

This is the unforgeability property that makes OCapN "capability-secure"
and is the *security* heart of the protocol.

### P4. GC soundness (no premature collection)

**Statement.** An object is only locally collected when its export
refcount has reached zero **and** all `wire-delta` increments sent by the
peer have been accounted for. We need this to be a stable property in the
face of crossed `op:gc-exports` and concurrent re-exports.

```lean
safety [gc_sound]
  collected R → ∀ P, exported P R → importRefcount P = 0
```

This is the classical distributed-refcount-no-spurious-decrement property
(Plainfossé–Shapiro 1995); we follow the established invariant pattern.

### P5. Crossed-hellos resolution is deterministic

**Statement.** When two peers simultaneously dial each other, exactly one
of the two prospective sessions survives, and both peers agree on which.
This is a small but observable correctness property.

```lean
safety [crossed_hellos_deterministic]
  startedSession A B S1 ∧ startedSession B A S2 ∧ active S1 ∧ active S2 → S1 = S2
```

### P6. Three-party handoff non-replay

**Statement.** A `desc:handoff-receive` with a given `handoff-count` is
honoured by the Exporter at most once, even under adversarial replay by a
third party that may intercept the certificate.

```lean
safety [handoff_no_replay]
  exporterHonoured G R hc T1 ∧ exporterHonoured G R hc T2 → T1 = T2
```

### P7. Session lifecycle determinism

**Statement.** `op:abort` is terminal: after receiving an abort, no further
deliveries succeed at this peer for this session; the export, import, and
answer tables are tombstoned.

```lean
safety [abort_terminal]
  aborted ∧ T1 < T2 → ¬ delivered T2
```

### P8. Bootstrap position invariant

**Statement.** Export position `0` always refers to the bootstrap object
throughout the lifetime of a session.

```lean
invariant [bootstrap_at_zero]
  sessionAlive → exported 0 bootstrapObject
```

## 6. The verified-implementation refinement

We follow the standard Veil pattern (see §7 of the
[Veil report](#)): a parallel `Captp.Impl` written in idiomatic Lean 4
(`def`s producing `IO`-effectful executables), and a forward simulation
proved by hand:

```lean
def simulates (impl : Captp.Impl.State) (spec : Captp.Spec.State) : Prop := ...

theorem deliver_refines :
  simulates impl spec →
  Captp.Impl.handleDeliver impl msg = .ok impl' →
  ∃ spec', Captp.Spec.deliver.tr spec spec' ∧ simulates impl' spec'
```

One such lemma per impl-level action; safety properties of `spec` lift to
the impl by composition.

## 7. Concrete proof-engineering plan

| Stage    | What gets proved                                                 | Veil-only? | Estimated effort |
| -------- | ---------------------------------------------------------------- | ---------- | ---------------- |
| **S0**   | Model+Syrup round-trip                                           | No (Lean)  | small            |
| **S1**   | Single-peer CapTP state machine, transitions well-formed         | Veil       | small            |
| **S2**   | P2 (promise monotone), P5 (crossed hellos), P7 (abort), P8       | Veil       | medium           |
| **S3**   | P1 (E2E FIFO) — two-peer composition                             | Veil       | medium-large     |
| **S4**   | P4 (GC soundness)                                                | Veil       | medium           |
| **S5**   | P3 (no forgery)                                                  | Veil       | large            |
| **S6**   | P6 (handoff replay-protection) on the three-peer composition     | Veil       | large            |
| **S7**   | Impl + refinement lemmas                                         | Lean       | large            |

We expect to add invariants iteratively as CTIs (counter-examples to
induction) come back from Z3/cvc5; this is the standard Veil workflow.

## 8. Out of scope (for now)

- Liveness (Veil v1 doesn't support it well; revisit when v2.0 lands).
- Cryptographic soundness of EdDSA (we trust signatures).
- Tor-onion-specific routing properties.
- Performance/throughput proofs.
- Side-channel resistance.

## 9. Glossary

- **vat** — a single CapTP endpoint, conceptually an event loop owning a set
  of local objects.
- **swissnum** — large unguessable bytestring used to authenticate access to
  a specific object via the bootstrap object's `fetch`.
- **sturdyref** — a long-lived reference (locator + swissnum) usable across
  sessions.
- **export-pos** — the position at which a peer has exported an object,
  unique within the session.
- **answer-pos** — the position at which a peer has promised an answer for a
  pipelined `op:deliver`, unique within the session.
- **3-party handoff** — Gifter → Receiver → Exporter dance that lets a peer
  pass along a reference to an object it doesn't itself own.

## 10. References (local mirrors)

- `projects/ocapn-spec/draft-specifications/CapTP Specification.md`
- `projects/ocapn-spec/draft-specifications/Netlayers.md`
- `projects/ocapn-spec/draft-specifications/Locators.md`
- `projects/ocapn-spec/draft-specifications/Model.md`
- `projects/ocapn-spec/implementation-guide/Implementation Guide.md`
- `projects/veil/Examples/Tutorial/Ring.lean` — canonical Veil example
- `projects/veil/Examples/IvyBench/` — protocol verification benchmarks
- `projects/syrup-ocapn/draft-specification.md`
