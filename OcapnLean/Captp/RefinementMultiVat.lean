import OcapnLean.Captp.Impl.MultiVat
-- We follow `RefinementExtended.lean`'s pattern of restating the Veil
-- safety as a Lean predicate over a parallel Lean state. We don't
-- import the Veil-generated `Channels.State` directly; the restatement
-- is intentionally decoupled so this module stays inspectable and the
-- lift theorem reads independently of Veil's elaboration details.

/-!
# Refinement: multi-vat **parallel Lean model** ↔ Veil spec (M11 Phase A.6)

`OcapnLean.Captp.Refinement` and `RefinementExtended` cover the
single-peer properties (P2, P4, P5, P6, P8) — genuine refinements of
`Captp.Impl` to `Captp.Spec`. This module covers the *multi-vat*
properties (the three P1 tiers) by relating the pure-Lean parallel
state machine `Impl.MultiVat` to the abstract Veil-side state shapes
from `Channels.lean`, `RefFifo.lean`, and `RefFifoForwarding.lean`.

> **Important caveat (M11 Phase A.7 gap).** The lifts in this module
> prove FIFO of the **parallel-Lean state machine** `Impl.MultiVat`,
> not of the runtime event loop. `Captp.Session.run` does not
> construct `Impl.MultiVat.State` values; it works with per-process
> `Impl.State`s and netlayer connections directly. Closing the gap
> from runtime to parallel model is M11 Phase A.7 — a runtime trace
> semantics + a projection + a step-preservation proof. Today the
> runtime is still trusted via cross-impl interop (24/24).

This file follows the same pattern as `RefinementExtended.lean`:

1. Define a Lean-side **abstract state** mirroring the relevant Veil
   module's relations.
2. Restate the Veil **safety property** as a Lean predicate.
3. Define a **simulation relation** between the executable's
   multi-vat state and the abstract state.
4. Prove a **lifting theorem**: simulation + Veil safety → impl-level
   property.

## What's covered here _(this commit)_

* **`e2e_fifo_lifts`** — fail-stop FIFO (per (src, dst) channel) lifted
  to `Impl.MultiVat.State`. Mirrors `Captp.Channels.safety [e2e_fifo]`.

The remaining tiers — `ref_fifo_lifts` (M11 Phase A.6 mid) and
`ref_fifo_e2e_lifts` (M11 Phase A.6 end) — will live in this same
file as the refs/routing and promise/forwarding sub-phases land.
-/

namespace OcapnLean.Captp.RefinementMultiVat

open OcapnLean.Captp.Impl.MultiVat

/-! ## Channels: fail-stop FIFO -/

/-- Abstract channel-state mirror of `CaptpChannels.State`, parameterised
by abstract vat / msg sorts. Each relation matches a Veil declaration. -/
structure ChannelsState (vat msg : Type) where
  sendCursor    : vat → vat → Nat
  recvCursor    : vat → vat → Nat
  pending       : vat → vat → msg → Prop
  delivered     : vat → vat → msg → Prop
  sentAt        : vat → vat → msg → Nat → Prop
  deliveredAt   : vat → vat → msg → Nat → Prop

/-- Veil's `safety [e2e_fifo]`, restated as a Lean predicate over the
abstract channel state. Per-(src, dst) channel FIFO — fail-stop FIFO in
Miller's *Robust Composition* §19 taxonomy. -/
def e2eFifo {vat msg : Type} (s : ChannelsState vat msg) : Prop :=
  ∀ S D M1 M2 K1 K2 J1 J2,
    s.delivered S D M1 ∧ s.delivered S D M2 ∧
    s.sentAt S D M1 K1 ∧ s.sentAt S D M2 K2 ∧
    s.deliveredAt S D M1 J1 ∧ s.deliveredAt S D M2 J2 ∧
    K1 < K2 → J1 < J2

/-- The simulation relation: the impl's multi-vat state matches the
abstract spec state. Each of the six Veil-side relations is pinned to
the corresponding `Impl.MultiVat` predicate. -/
def simulatesChannels (impl : State) (spec : ChannelsState Vat MsgId) : Prop :=
  (∀ s d,
    spec.sendCursor s d = (impl.channels s d).sendCursor ∧
    spec.recvCursor s d = (impl.channels s d).recvCursor) ∧
  (∀ s d m,     spec.pending s d m         ↔ pending impl s d m) ∧
  (∀ s d m,     spec.delivered s d m       ↔ delivered impl s d m) ∧
  (∀ s d m k,   spec.sentAt s d m k        ↔ sentAt impl s d m k) ∧
  (∀ s d m j,   spec.deliveredAt s d m j   ↔ deliveredAt impl s d m j)

/-- **Headline: `e2e_fifo` lifts to the impl.** Given a `simulatesChannels`
witness and the Veil-proved `e2eFifo` safety on the abstract spec, the
impl's per-channel delivery order matches send order. -/
theorem e2e_fifo_lifts
    (impl : State) (spec : ChannelsState Vat MsgId)
    (hsim : simulatesChannels impl spec)
    (hsafe : e2eFifo spec) :
    ∀ s d m1 m2 k1 k2 j1 j2,
      delivered impl s d m1 → delivered impl s d m2 →
      sentAt impl s d m1 k1 → sentAt impl s d m2 k2 →
      deliveredAt impl s d m1 j1 → deliveredAt impl s d m2 j2 →
      k1 < k2 → j1 < j2 := by
  obtain ⟨_, hpend, hdel, hsent, hdAt⟩ := hsim
  intro s d m1 m2 k1 k2 j1 j2
       hd1 hd2 hs1 hs2 hda1 hda2 hk
  exact hsafe s d m1 m2 k1 k2 j1 j2
    ⟨(hdel s d m1).mpr hd1, (hdel s d m2).mpr hd2,
     (hsent s d m1 k1).mpr hs1, (hsent s d m2 k2).mpr hs2,
     (hdAt s d m1 j1).mpr hda1, (hdAt s d m2 j2).mpr hda2,
     hk⟩

/-! ## Canonical projection — bridge from impl state to abstract spec

Every impl state induces a canonical abstract state by projection. The
simulation holds by definition, so the lift applies to any impl state
unconditionally (modulo the Veil-proved spec safety, which the runtime
trusts via `#check_invariants` discharge).
-/

/-- The canonical abstract `ChannelsState` projected from a multi-vat
impl state. Each field is the corresponding `Impl.MultiVat` projection. -/
def canonicalAbstract (impl : State) : ChannelsState Vat MsgId where
  sendCursor s d  := (impl.channels s d).sendCursor
  recvCursor s d  := (impl.channels s d).recvCursor
  pending s d m   := pending impl s d m
  delivered s d m := delivered impl s d m
  sentAt s d m k  := sentAt impl s d m k
  deliveredAt s d m j := deliveredAt impl s d m j

/-- The canonical projection always satisfies the simulation relation —
the bridge is definitional. -/
theorem canonical_simulatesChannels (impl : State) :
    simulatesChannels impl (canonicalAbstract impl) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s d; exact ⟨rfl, rfl⟩
  · intro s d m; exact Iff.rfl
  · intro s d m; exact Iff.rfl
  · intro s d m k; exact Iff.rfl
  · intro s d m j; exact Iff.rfl

/-- **End-user lift.** Combines `canonical_simulatesChannels` with
`e2e_fifo_lifts` — given the Veil-proved spec safety, any multi-vat impl
state has per-channel FIFO. This is the form the runtime / future
refinement consumers would use. -/
theorem e2e_fifo_at_impl
    (impl : State)
    (hsafe : e2eFifo (canonicalAbstract impl)) :
    ∀ s d m1 m2 k1 k2 j1 j2,
      delivered impl s d m1 → delivered impl s d m2 →
      sentAt impl s d m1 k1 → sentAt impl s d m2 k2 →
      deliveredAt impl s d m1 j1 → deliveredAt impl s d m2 j2 →
      k1 < k2 → j1 < j2 :=
  e2e_fifo_lifts impl (canonicalAbstract impl)
    (canonical_simulatesChannels impl) hsafe

/-! ## RefFifo: per-(sender, ref) FIFO at routing target

Mirrors `RefFifo.lean`'s additions (refs, routing, origin tracking).
The abstract Lean state extends `ChannelsState` with the new relations;
the lift theorem chains through `e2e_fifo_lifts` via routing
functionality. -/

/-- Abstract state-shape for `RefFifo.lean`: channel state +
refs/routing/origin tracking. -/
structure RefFifoState (vat msg ref : Type) extends ChannelsState vat msg where
  targetRef : msg → ref
  routesTo  : vat → ref → vat → Prop
  sentBy    : vat → msg → Prop

/-- Veil's `safety [ref_fifo]`, restated. Per-(sender, ref) delivery
order matches send order at the sender's immediate routing target. -/
def refFifo {vat msg ref : Type} (s : RefFifoState vat msg ref) : Prop :=
  ∀ S M1 M2 D1 D2 K1 K2 J1 J2,
    s.sentBy S M1 ∧ s.sentBy S M2 ∧
    s.targetRef M1 = s.targetRef M2 ∧
    s.delivered S D1 M1 ∧ s.delivered S D2 M2 ∧
    s.sentAt S D1 M1 K1 ∧ s.sentAt S D2 M2 K2 ∧
    s.deliveredAt S D1 M1 J1 ∧ s.deliveredAt S D2 M2 J2 ∧
    K1 < K2 → J1 < J2

/-- Simulation relation for `RefFifo`: extends `simulatesChannels` with
the new refs/routing/origin predicates. -/
def simulatesRefFifo (impl : State) (spec : RefFifoState Vat MsgId Ref) : Prop :=
  simulatesChannels impl spec.toChannelsState ∧
  (∀ m, spec.targetRef m = impl.targetRef m) ∧
  (∀ v r w, spec.routesTo v r w ↔ impl.routesTo v r = some w) ∧
  (∀ s m, spec.sentBy s m ↔ impl.sentBy m = some s)

/-- The canonical abstract `RefFifoState` projected from a multi-vat
impl state. -/
def canonicalAbstractRefFifo (impl : State) : RefFifoState Vat MsgId Ref where
  toChannelsState := canonicalAbstract impl
  targetRef m       := impl.targetRef m
  routesTo v r w    := impl.routesTo v r = some w
  sentBy s m        := impl.sentBy m = some s

/-- The canonical projection always simulates. -/
theorem canonical_simulatesRefFifo (impl : State) :
    simulatesRefFifo impl (canonicalAbstractRefFifo impl) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact canonical_simulatesChannels impl
  · intro m; rfl
  · intro v r w; exact Iff.rfl
  · intro s m; exact Iff.rfl

/-- **Headline: `ref_fifo` lifts to the impl.** -/
theorem ref_fifo_lifts
    (impl : State) (spec : RefFifoState Vat MsgId Ref)
    (hsim : simulatesRefFifo impl spec)
    (hsafe : refFifo spec) :
    ∀ s m1 m2 d1 d2 k1 k2 j1 j2,
      impl.sentBy m1 = some s → impl.sentBy m2 = some s →
      impl.targetRef m1 = impl.targetRef m2 →
      delivered impl s d1 m1 → delivered impl s d2 m2 →
      sentAt impl s d1 m1 k1 → sentAt impl s d2 m2 k2 →
      deliveredAt impl s d1 m1 j1 → deliveredAt impl s d2 m2 j2 →
      k1 < k2 → j1 < j2 := by
  obtain ⟨⟨_, _, hdel, hsent, hdAt⟩, htar, _hrt, hsB⟩ := hsim
  intro s m1 m2 d1 d2 k1 k2 j1 j2
       hsb1 hsb2 htr hd1 hd2 hs1 hs2 hda1 hda2 hk
  apply hsafe s m1 m2 d1 d2 k1 k2 j1 j2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact (hsB s m1).mpr hsb1
  · exact (hsB s m2).mpr hsb2
  · rw [htar m1, htar m2]; exact htr
  · exact (hdel s d1 m1).mpr hd1
  · exact (hdel s d2 m2).mpr hd2
  · exact (hsent s d1 m1 k1).mpr hs1
  · exact (hsent s d2 m2 k2).mpr hs2
  · exact (hdAt s d1 m1 j1).mpr hda1
  · exact (hdAt s d2 m2 j2).mpr hda2

/-- **End-user lift.** -/
theorem ref_fifo_at_impl
    (impl : State)
    (hsafe : refFifo (canonicalAbstractRefFifo impl)) :
    ∀ s m1 m2 d1 d2 k1 k2 j1 j2,
      impl.sentBy m1 = some s → impl.sentBy m2 = some s →
      impl.targetRef m1 = impl.targetRef m2 →
      delivered impl s d1 m1 → delivered impl s d2 m2 →
      sentAt impl s d1 m1 k1 → sentAt impl s d2 m2 k2 →
      deliveredAt impl s d1 m1 j1 → deliveredAt impl s d2 m2 j2 →
      k1 < k2 → j1 < j2 :=
  ref_fifo_lifts impl (canonicalAbstractRefFifo impl)
    (canonical_simulatesRefFifo impl) hsafe

/-! ## RefFifoForwarding: end-to-end ref FIFO across A→B→C forwarding

Mirrors `RefFifoForwarding.lean`. The abstract state extends `RefFifo`
with `isPromise`, `resolvedTo`, `forwardedAt`. The headline lift is
`ref_fifo_e2e_lifts`. -/

/-- Abstract state-shape for `RefFifoForwarding.lean`: refs/routing +
promises + forwarding ledger. -/
structure RefFifoForwardingState (vat msg ref : Type)
    extends RefFifoState vat msg ref where
  isPromise   : ref → Prop
  resolvedTo  : ref → vat → Prop
  forwardedAt : vat → vat → msg → Nat → Prop

/-- Veil's `safety [ref_fifo_e2e]`, restated. Per-(sender, ref)
delivery order at the resolution host matches origination send order,
across the A→B→C forwarding chain. -/
def refFifoE2e {vat msg ref : Type} (s : RefFifoForwardingState vat msg ref) : Prop :=
  ∀ S M1 M2 B C K1 K2 KF1 KF2 N1 N2,
    s.sentBy S M1 ∧ s.sentBy S M2 ∧
    s.targetRef M1 = s.targetRef M2 ∧
    s.isPromise (s.targetRef M1) ∧
    s.resolvedTo (s.targetRef M1) C ∧
    s.sentAt S B M1 K1 ∧ s.sentAt S B M2 K2 ∧
    s.forwardedAt B C M1 KF1 ∧ s.forwardedAt B C M2 KF2 ∧
    s.delivered B C M1 ∧ s.delivered B C M2 ∧
    s.deliveredAt B C M1 N1 ∧ s.deliveredAt B C M2 N2 ∧
    K1 < K2 → N1 < N2

/-- Simulation relation. Extends `simulatesRefFifo` with the promise
+ forwarding fields. -/
def simulatesRefFifoForwarding (impl : State)
    (spec : RefFifoForwardingState Vat MsgId Ref) : Prop :=
  simulatesRefFifo impl spec.toRefFifoState ∧
  (∀ r, spec.isPromise r ↔ impl.isPromise r = true) ∧
  (∀ r v, spec.resolvedTo r v ↔ impl.resolvedTo r = some v) ∧
  (∀ b c m k, spec.forwardedAt b c m k ↔ impl.forwardedAt b c m = some k)

/-- Canonical projection from impl multi-vat state to abstract
forwarding state. -/
def canonicalAbstractRefFifoForwarding (impl : State) :
    RefFifoForwardingState Vat MsgId Ref where
  toRefFifoState  := canonicalAbstractRefFifo impl
  isPromise r     := impl.isPromise r = true
  resolvedTo r v  := impl.resolvedTo r = some v
  forwardedAt b c m k := impl.forwardedAt b c m = some k

/-- Canonical projection always simulates. -/
theorem canonical_simulatesRefFifoForwarding (impl : State) :
    simulatesRefFifoForwarding impl (canonicalAbstractRefFifoForwarding impl) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact canonical_simulatesRefFifo impl
  · intro r; exact Iff.rfl
  · intro r v; exact Iff.rfl
  · intro b c m k; exact Iff.rfl

/-- **Headline: `ref_fifo_e2e` lifts to the impl.** End-to-end
per-(sender, ref) delivery order at the resolution host matches
origination send order, across the A→B→C forwarding chain. -/
theorem ref_fifo_e2e_lifts
    (impl : State) (spec : RefFifoForwardingState Vat MsgId Ref)
    (hsim : simulatesRefFifoForwarding impl spec)
    (hsafe : refFifoE2e spec) :
    ∀ s m1 m2 b c k1 k2 kf1 kf2 n1 n2,
      impl.sentBy m1 = some s → impl.sentBy m2 = some s →
      impl.targetRef m1 = impl.targetRef m2 →
      impl.isPromise (impl.targetRef m1) = true →
      impl.resolvedTo (impl.targetRef m1) = some c →
      sentAt impl s b m1 k1 → sentAt impl s b m2 k2 →
      impl.forwardedAt b c m1 = some kf1 → impl.forwardedAt b c m2 = some kf2 →
      delivered impl b c m1 → delivered impl b c m2 →
      deliveredAt impl b c m1 n1 → deliveredAt impl b c m2 n2 →
      k1 < k2 → n1 < n2 := by
  obtain ⟨⟨⟨_, _, hdel, hsent, hdAt⟩, htar, _, hsB⟩, hip, hrt, hfw⟩ := hsim
  intro s m1 m2 b c k1 k2 kf1 kf2 n1 n2
       hsb1 hsb2 htr hip_i hrt_i hs1 hs2 hf1 hf2 hd1 hd2 hda1 hda2 hk
  apply hsafe s m1 m2 b c k1 k2 kf1 kf2 n1 n2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hk⟩
  · exact (hsB s m1).mpr hsb1
  · exact (hsB s m2).mpr hsb2
  · rw [htar m1, htar m2]; exact htr
  · rw [htar m1]; exact (hip _).mpr hip_i
  · rw [htar m1]; exact (hrt _ c).mpr hrt_i
  · exact (hsent s b m1 k1).mpr hs1
  · exact (hsent s b m2 k2).mpr hs2
  · exact (hfw b c m1 kf1).mpr hf1
  · exact (hfw b c m2 kf2).mpr hf2
  · exact (hdel b c m1).mpr hd1
  · exact (hdel b c m2).mpr hd2
  · exact (hdAt b c m1 n1).mpr hda1
  · exact (hdAt b c m2 n2).mpr hda2

/-- **End-user lift.** Combines canonical projection with the lift;
applicable to any multi-vat impl state given the Veil-proved spec
safety. The headline impl-level claim of M11 Phase A.6 — end-to-end
reference FIFO across the A→B→C forwarding chain, at the runnable
Lean code. -/
theorem ref_fifo_e2e_at_impl
    (impl : State)
    (hsafe : refFifoE2e (canonicalAbstractRefFifoForwarding impl)) :
    ∀ s m1 m2 b c k1 k2 kf1 kf2 n1 n2,
      impl.sentBy m1 = some s → impl.sentBy m2 = some s →
      impl.targetRef m1 = impl.targetRef m2 →
      impl.isPromise (impl.targetRef m1) = true →
      impl.resolvedTo (impl.targetRef m1) = some c →
      sentAt impl s b m1 k1 → sentAt impl s b m2 k2 →
      impl.forwardedAt b c m1 = some kf1 → impl.forwardedAt b c m2 = some kf2 →
      delivered impl b c m1 → delivered impl b c m2 →
      deliveredAt impl b c m1 n1 → deliveredAt impl b c m2 n2 →
      k1 < k2 → n1 < n2 :=
  ref_fifo_e2e_lifts impl (canonicalAbstractRefFifoForwarding impl)
    (canonical_simulatesRefFifoForwarding impl) hsafe

/-! ## Concrete witness: the empty multi-vat state simulates the empty
spec state. Sanity check that the simulation relation is satisfiable. -/

/-- The "empty" abstract Channels state: every cursor at 0, every
relation False. Matches `Impl.MultiVat.initial`. -/
def emptyChannelsState : ChannelsState Vat MsgId where
  sendCursor _ _    := 0
  recvCursor _ _    := 0
  pending _ _ _     := False
  delivered _ _ _   := False
  sentAt _ _ _ _    := False
  deliveredAt _ _ _ _ := False

/-- The initial impl state simulates the empty spec state. -/
theorem initial_simulatesChannels :
    simulatesChannels initial emptyChannelsState := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s d; exact ⟨rfl, rfl⟩
  · intro s d m
    show False ↔ pending initial s d m
    constructor
    · intro h; exact h.elim
    · intro ⟨k, h⟩
      simp [initial, ChannelState.empty] at h
  · intro s d m
    show False ↔ delivered initial s d m
    constructor
    · intro h; exact h.elim
    · intro ⟨k, j, h⟩
      simp [initial, ChannelState.empty] at h
  · intro s d m k
    show False ↔ sentAt initial s d m k
    constructor
    · intro h; exact h.elim
    · intro h
      rcases h with h | ⟨j, h⟩
      all_goals simp [initial, ChannelState.empty] at h
  · intro s d m j
    show False ↔ deliveredAt initial s d m j
    constructor
    · intro h; exact h.elim
    · intro ⟨k, h⟩
      simp [initial, ChannelState.empty] at h

end OcapnLean.Captp.RefinementMultiVat
