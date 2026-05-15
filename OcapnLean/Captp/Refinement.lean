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
  listening _ _   := False
  listenerNotified _ _ := False
  alive           := True

/-- A spec state representing an *aborted* impl configuration. -/
def specAborted (spec : SpecState) : SpecState :=
  { spec with alive := False }

/-- A spec state representing a successful `exportNew` action on the
spec side: extend `exported` to also relate `(p, r)`. -/
def specExportNew (spec : SpecState) (p : Nat) (r : Nat) : SpecState :=
  { spec with exported := fun p' r' => spec.exported p' r' ∨ (p' = p ∧ r' = r) }

/-- A spec state representing a successful `importNew` action. -/
def specImportNew (spec : SpecState) (p : Nat) (r : Nat) : SpecState :=
  { spec with imported := fun p' r' => spec.imported p' r' ∨ (p' = p ∧ r' = r) }

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

/-- `exportNew` on both sides preserves `simulates`. -/
theorem exportNew_refines (impl impl' : Impl.State) (spec : SpecState)
    (p r : Nat)
    (h : simulates impl spec)
    (heq : Impl.exportNew impl p r = some impl') :
    simulates impl' (specExportNew spec p r) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  -- exportNew produces some when the three guards hold.
  unfold Impl.exportNew at heq
  split at heq
  · simp only [Option.some.injEq] at heq
    subst heq
    refine ⟨h1, h2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- imported is untouched
      intro p' r'
      simp
      exact h3 p' r'
    · -- exported: union with the new singleton
      intro p' r'
      show spec.exported p' r' ∨ (p' = p ∧ r' = r)
          ↔ (p', r') ∈ ((p, r) :: impl.exported)
      simp
      rw [h4 p' r']
      constructor
      · rintro (himp | ⟨rfl, rfl⟩)
        · exact Or.inr himp
        · exact Or.inl ⟨rfl, rfl⟩
      · rintro (⟨rfl, rfl⟩ | himp)
        · exact Or.inr ⟨rfl, rfl⟩
        · exact Or.inl himp
    · exact h5
    · exact h6
    · exact h7
    · -- alive unchanged
      exact h8
  · exact (Option.noConfusion heq)

/-- `importNew` on both sides preserves `simulates`. -/
theorem importNew_refines (impl impl' : Impl.State) (spec : SpecState)
    (p r : Nat)
    (h : simulates impl spec)
    (heq : Impl.importNew impl p r = some impl') :
    simulates impl' (specImportNew spec p r) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  unfold Impl.importNew at heq
  split at heq
  · simp only [Option.some.injEq] at heq
    subst heq
    refine ⟨h1, h2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p' r'
      show spec.imported p' r' ∨ (p' = p ∧ r' = r)
          ↔ (p', r') ∈ ((p, r) :: impl.imported)
      simp
      rw [h3 p' r']
      constructor
      · rintro (himp | ⟨rfl, rfl⟩)
        · exact Or.inr himp
        · exact Or.inl ⟨rfl, rfl⟩
      · rintro (⟨rfl, rfl⟩ | himp)
        · exact Or.inr ⟨rfl, rfl⟩
        · exact Or.inl himp
    · intro p' r'; simp; exact h4 p' r'
    · exact h5
    · exact h6
    · exact h7
    · exact h8
  · exact (Option.noConfusion heq)

------------------------------------------------------------------------
-- Lifting Veil-proved safety onto the impl
------------------------------------------------------------------------

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

/-- Veil's `imported_functional` invariant — `imported P R1 ∧ imported P R2
→ R1 = R2` — lifts onto the impl. -/
theorem importedFunctional_lifts (impl : Impl.State) (spec : SpecState)
    (hsim : simulates impl spec)
    (hsafe : ∀ P R1 R2, spec.imported P R1 ∧ spec.imported P R2 → R1 = R2) :
    ∀ p r1 r2, (p, r1) ∈ impl.imported → (p, r2) ∈ impl.imported → r1 = r2 := by
  obtain ⟨_, _, himp, _, _, _, _, _⟩ := hsim
  intro p r1 r2 h1 h2
  exact hsafe p r1 r2 ⟨(himp p r1).mpr h1, (himp p r2).mpr h2⟩

/-- Veil's `exported_functional` invariant lifts onto the impl. -/
theorem exportedFunctional_lifts (impl : Impl.State) (spec : SpecState)
    (hsim : simulates impl spec)
    (hsafe : ∀ P R1 R2, spec.exported P R1 ∧ spec.exported P R2 → R1 = R2) :
    ∀ p r1 r2, (p, r1) ∈ impl.exported → (p, r2) ∈ impl.exported → r1 = r2 := by
  obtain ⟨_, _, _, hexp, _, _, _, _⟩ := hsim
  intro p r1 r2 h1 h2
  exact hsafe p r1 r2 ⟨(hexp p r1).mpr h1, (hexp p r2).mpr h2⟩

/-- Veil's promise-monotonicity clauses lift onto the impl *vacuously*:
the impl does not track promise state, so the `simulates` relation
pins the spec's promise fields to their empty defaults. There is
nothing for the impl-side safety property to constrain, so the lift
is trivially true — but stating it documents the bilateral guarantee
for when the impl grows a promise table. -/
theorem promiseMonotoneFulfilled_lifts (impl : Impl.State) (spec : SpecState)
    (_hsim : simulates impl spec)
    (_hsafe : ∀ P V1 V2, spec.promiseResolved P V1 ∧ spec.promiseResolved P V2 → V1 = V2) :
    True := trivial

end OcapnLean.Captp.Refinement
