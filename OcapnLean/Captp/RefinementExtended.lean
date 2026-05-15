import OcapnLean.Captp.CrossedHellos
import OcapnLean.Captp.Gc
import OcapnLean.Captp.Threeparty

/-!
# Refinement: lifting Veil safety onto the executable's new code paths

`OcapnLean.Captp.Refinement` covers the original single-peer impl
(`bootstrap_at_zero`, etc.) and shows that Veil's safety properties
lift onto `Captp.Impl`. This module does the same for the three
*new* Veil modules:

  * `CrossedHellos` (P5) — `crossed_hellos_unique`
  * `CaptpGc`        (P4) — `gc_sound`
  * `CaptpThreeparty`(P6) — `handoff_no_replay`

For each one we present:

  1. A pure-Lean *abstract simulation target* `*State` mirroring the
     Veil module's relations (so the lifting theorem can be stated
     without reaching into the Veil-generated structures directly).
  2. Helper `extend*` constructors that step the state forward in the
     same shape as the Veil action.
  3. *Lifting theorems* of the form

         hsafe : <Veil safety statement, restated in Lean>
         → <concrete property about the executable state>

     keyed by a `simulates_*` predicate the executable must satisfy.

In each case the executable's concrete state is exactly the shape
the Veil model assumes; the simulation lemmas are short and
inspectable, and the lifted property is something you can directly
check in unit tests against the running session.

The flow mirrors how `Refinement.bootstrapAtZero_lifts` already
works: given an established simulation, the *Lean* statement follows
from the *Veil* statement automatically. -/

namespace OcapnLean.Captp.RefinementExtended

/-! ## CrossedHellos: at most one active session direction per pair. -/

/-- Abstract crossed-hellos state. Mirror of the Veil
`CrossedHellos.State` instantiated at the `vat = α` we care about. -/
structure CrossedHellosState (α : Type) where
  initiated : α → α → Prop
  active    : α → α → Prop

/-- The Veil-level safety, restated. -/
def crossedHellosUnique {α : Type} (s : CrossedHellosState α) : Prop :=
  ∀ A B, s.active A B ∧ s.active B A → A = B

/-- A representation predicate: a list of `(initiator, responder)`
peer-key pairs faithfully populates the abstract `active` relation
when it has *no duplicate keys* (because at most one direction can
be live per pair in the executable). -/
def simulatesCrossedHellos {α : Type} [DecidableEq α]
    (peerSessions : List (α × α))
    (s : CrossedHellosState α) : Prop :=
  (∀ a b, (a, b) ∈ peerSessions ↔ s.active a b) ∧
  -- no key appears twice (the executable's registry enforces this
  -- via filter-on-add)
  peerSessions.Nodup

/-- Lift `crossed_hellos_unique` onto a concrete `peerSessions`
list. If the executable's registry simulates the abstract model and
the abstract model satisfies Veil's safety, then any two active
session directions between the same pair of peers must coincide. -/
theorem crossedHellosUnique_lifts
    {α : Type} [DecidableEq α]
    (peerSessions : List (α × α)) (s : CrossedHellosState α)
    (hsim : simulatesCrossedHellos peerSessions s)
    (hsafe : crossedHellosUnique s) :
    ∀ a b, (a, b) ∈ peerSessions → (b, a) ∈ peerSessions → a = b := by
  intro a b hab hba
  obtain ⟨hiff, _⟩ := hsim
  exact hsafe a b ⟨(hiff a b).mp hab, (hiff b a).mp hba⟩

/-! ## CaptpGc: collection only when all sub-counts are zero. -/

/-- Abstract GC state mirroring the Veil `CaptpGc` module. -/
structure GcState (pos : Type) where
  localCount     : pos → Nat
  inFlightSends  : pos → Nat
  inFlightDecs   : pos → Nat
  exporterCount  : pos → Nat
  collected      : pos → Prop

/-- Veil's `gc_sound` safety, restated. -/
def gcSound {pos : Type} (s : GcState pos) : Prop :=
  ∀ p, s.collected p →
    s.localCount p = 0 ∧ s.inFlightSends p = 0 ∧ s.inFlightDecs p = 0

/-- The executable currently does not track exporter-side wire
counts (we emit `op:gc-exports` reactively rather than maintain a
counter), so the simulation here is vacuous: no `collected` position
exists in the executable. The lifting theorem is therefore trivially
true; we state it to document the bilateral guarantee for when the
impl grows an exporter-side count. -/
def simulatesGc {pos : Type} (collectedPositions : List pos)
    (s : GcState pos) : Prop :=
  ∀ p, p ∈ collectedPositions ↔ s.collected p

/-- Lift `gc_sound`. Concretely: if a position appears in the
executable's `collectedPositions` set, all three sub-counts in the
abstract state are zero. (Holds vacuously when the executable has no
collected positions.) -/
theorem gcSound_lifts {pos : Type}
    (collectedPositions : List pos) (s : GcState pos)
    (hsim : simulatesGc collectedPositions s)
    (hsafe : gcSound s) :
    ∀ p, p ∈ collectedPositions →
      s.localCount p = 0 ∧ s.inFlightSends p = 0 ∧ s.inFlightDecs p = 0 := by
  intro p hp
  exact hsafe p ((hsim p).mp hp)

/-! ## CaptpThreeparty: handoff non-replay. -/

/-- Abstract three-party-handoff state. `receivedGift e r hc g`
records that Exporter `e` returned gift `g` to Receiver `r` under
handoff-count `hc`. -/
structure HandoffState (vat giftId : Type) where
  receivedGift : vat → vat → Nat → giftId → Prop

/-- Veil's `handoff_no_replay`: a (Exporter, Receiver, handoff-count)
triple uniquely determines the gift. -/
def handoffNoReplay {vat giftId : Type} (s : HandoffState vat giftId) : Prop :=
  ∀ E R H G1 G2,
    s.receivedGift E R H G1 ∧ s.receivedGift E R H G2 → G1 = G2

/-- Executable simulation: a list of fulfilled withdrawals (one row
per honoured `withdraw-gift`) faithfully populates `receivedGift`
when each `(exporterSid, receiverSid, handoffCount)` triple appears
at most once. The executable enforces this via the
`HandoffCountSet`: `markUsed` is called only after `hasBeenUsed`
returns `false`, so two fulfilled withdrawals on the same triple is
impossible. -/
def simulatesHandoff {vat giftId : Type} [DecidableEq vat] [DecidableEq giftId]
    (fulfilled : List (vat × vat × Nat × giftId))
    (s : HandoffState vat giftId) : Prop :=
  (∀ e r h g, (e, r, h, g) ∈ fulfilled ↔ s.receivedGift e r h g) ∧
  (∀ e r h g1 g2,
     (e, r, h, g1) ∈ fulfilled → (e, r, h, g2) ∈ fulfilled → g1 = g2)

/-- Lift `handoff_no_replay`: in the executable, replayed
`withdraw-gift` invocations on the same `(exporter-sid, receiver-sid,
handoff-count)` cannot produce two different gifts. -/
theorem handoffNoReplay_lifts {vat giftId : Type}
    [DecidableEq vat] [DecidableEq giftId]
    (fulfilled : List (vat × vat × Nat × giftId))
    (s : HandoffState vat giftId)
    (hsim : simulatesHandoff fulfilled s)
    (hsafe : handoffNoReplay s) :
    ∀ e r h g1 g2,
      (e, r, h, g1) ∈ fulfilled → (e, r, h, g2) ∈ fulfilled → g1 = g2 := by
  obtain ⟨hiff, _⟩ := hsim
  intro e r h g1 g2 h1 h2
  exact hsafe e r h g1 g2 ⟨(hiff e r h g1).mp h1, (hiff e r h g2).mp h2⟩

/-! ## Concrete-instance smoke check

A nullary check that the empty-registry case of the crossed-hellos
lift goes through. Concrete non-trivial instances are exercised in
the running server's runtime; see `INTEROP.md`. -/

example :
    ∀ a b, (a, b) ∈ ([] : List (Nat × Nat)) →
      (b, a) ∈ ([] : List (Nat × Nat)) → a = b := by
  intro _ _ h _
  exact absurd h (by simp)

end OcapnLean.Captp.RefinementExtended
