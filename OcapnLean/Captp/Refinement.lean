import OcapnLean.Captp.Impl
import OcapnLean.Captp.Spec

/-!
# Refinement: Impl ↔ Spec

Defines a forward simulation between the executable
`OcapnLean.Captp.Impl` and the Veil-verified abstract
`CaptpSinglePeer.State`. Once a simulation is established for every
action of the impl, the safety properties proved in Veil
(`bootstrap_at_zero`, `imported_functional`, `exported_functional`,
the two `promise_monotone_*` clauses, and `promise_disjoint`) lift
onto the impl by composition: any state reachable in the impl is
related to a state reachable in the spec, hence satisfies the
invariants.

This commit lays down:

  * the `simulates` relation;
  * a `specInitial` witness state corresponding to `Impl.initial`;
  * the initial refinement lemma `initial_simulates`;
  * the abort refinement lemma `abort_refines`.

The export/import action refinement lemmas (and the corresponding
inductive proof of safety lifting) build on this scaffolding and are
queued for a follow-up commit — the pattern is the same as
`abort_refines` once you also bookkeep the new entries into the
spec-side `exported` / `imported` relations.

We instantiate the spec's four sort parameters with `Nat`s (`pos`,
`oref`) and `Unit`s (`value`, `error`) — the impl does not yet
distinguish values or errors, so `Unit` is the natural "no info"
choice.
-/

namespace OcapnLean.Captp.Refinement

open CaptpSinglePeer

abbrev SpecState : Type :=
  State Nat Nat Unit Unit

/-- A spec state representing the impl's initial configuration: the
bootstrap object exported at position 0, all other tables empty, the
session alive. -/
def specInitial : SpecState where
  bootstrapPos    := Impl.bootstrapPos
  bootstrapObj    := Impl.bootstrapObj
  imported _ _    := False
  exported p r    := p = Impl.bootstrapPos ∧ r = Impl.bootstrapObj
  answerSlot _    := False
  promiseResolved _ _ := False
  promiseBroken _ _ := False
  alive           := True

/-- A spec state representing an *aborted* impl configuration. -/
def specAborted (spec : SpecState) : SpecState :=
  { spec with alive := False }

/-- The simulation relation. Pins the spec's "extra" fields
(`answerSlot`, `promiseResolved`, `promiseBroken`) to their empty
defaults because the impl does not yet track promise state. -/
def simulates (impl : Impl.State) (spec : SpecState) : Prop :=
  spec.bootstrapPos = Impl.bootstrapPos ∧
  spec.bootstrapObj = Impl.bootstrapObj ∧
  (∀ p r, spec.imported p r ↔ (p, r) ∈ impl.imported) ∧
  (∀ p r, spec.exported p r ↔ (p, r) ∈ impl.exported) ∧
  (∀ p,   ¬ spec.answerSlot p) ∧
  (∀ p v, ¬ spec.promiseResolved p v) ∧
  (∀ p e, ¬ spec.promiseBroken p e) ∧
  (spec.alive ↔ impl.alive = true)

/-- The initial states are related. -/
theorem initial_simulates : simulates Impl.initial specInitial := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p r; constructor <;> intro h <;> simp [specInitial, Impl.initial] at *
  · intro p r
    constructor
    · rintro ⟨rfl, rfl⟩
      simp [Impl.initial]
    · intro h
      simp [Impl.initial] at h
      exact ⟨h.1, h.2⟩
  · intro p; simp [specInitial]
  · intro p v; simp [specInitial]
  · intro p e; simp [specInitial]
  · simp [specInitial, Impl.initial]

/-- `abort` on both sides preserves `simulates`. -/
theorem abort_refines (impl : Impl.State) (spec : SpecState)
    (h : simulates impl spec) :
    simulates (Impl.abort impl) (specAborted spec) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, _⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h1
  · exact h2
  · intro p r
    show spec.imported p r ↔ (p, r) ∈ (Impl.abort impl).imported
    simpa [Impl.abort] using h3 p r
  · intro p r
    show spec.exported p r ↔ (p, r) ∈ (Impl.abort impl).exported
    simpa [Impl.abort] using h4 p r
  · exact h5
  · exact h6
  · exact h7
  · simp [specAborted, Impl.abort]

/-- The safety property `bootstrap_at_zero` from the Veil spec —
`alive → exported bootstrapPos bootstrapObj` — lifts onto any impl
state in the simulation relation. -/
theorem bootstrapAtZero_lifts (impl : Impl.State) (spec : SpecState)
    (hsim : simulates impl spec)
    (hsafe : spec.alive → spec.exported spec.bootstrapPos spec.bootstrapObj) :
    Impl.bootstrapAtZero impl := by
  intro halive
  obtain ⟨hbp, hbo, _himp, hexp, _ans, _pr, _pb, halive_iff⟩ := hsim
  have halive_spec : spec.alive := halive_iff.mpr halive
  have hexp_spec   : spec.exported spec.bootstrapPos spec.bootstrapObj :=
    hsafe halive_spec
  rw [hbp, hbo] at hexp_spec
  exact (hexp _ _).mp hexp_spec

end OcapnLean.Captp.Refinement
