/-!
# CapTP — executable single-peer implementation

A regular-Lean (non-Veil) implementation of one peer's view of one
CapTP session, paralleling the abstract spec in `Captp.Spec`. This
module is what we would actually run; the Veil module is what we
*prove about*.

The invariant `bootstrapAtZero` (the Lean re-statement of Spec's
`safety [bootstrap_at_zero]`) is proved here directly in Lean — no
SMT — across the same three actions modelled in `Captp.Spec`.

This serves as a worked example of the refinement / parallel-impl
pattern described in PLAN.md §6: every action mutates the impl's
state in a way that locally preserves the invariant, so the global
invariant follows by induction over execution traces.

A future commit will add an explicit `simulates : Impl.State →
Spec.State → Prop` relation against the Veil-generated `State`,
making the connection bilateral.
-/

namespace OcapnLean.Captp.Impl

/-- Identifiers for positions and object refs are abstract; we use
`Nat` here because it's the most natural concrete choice and
because `0` matches the spec's reserved bootstrap position. -/
abbrev Pos  := Nat
abbrev ORef := Nat

/-- Reserved position for the bootstrap object. -/
def bootstrapPos : Pos := 0
/-- The local bootstrap object exposed at `bootstrapPos`. Distinct
identifiers can be modelled by varying this constant. -/
def bootstrapObj : ORef := 0

/-- One peer's local CapTP session state, paralleling the Veil-side
`CaptpSinglePeer.State`. -/
structure State where
  imported : List (Pos × ORef)
  exported : List (Pos × ORef)
  alive    : Bool
deriving Repr, Inhabited

/-- The initial state after handshake: empty import table, bootstrap
object exported at `bootstrapPos`, session alive. -/
def initial : State :=
  { imported := []
    exported := [(bootstrapPos, bootstrapObj)]
    alive    := true }

/-- True iff some `(p, _)` is already in the table. -/
def hasPos (table : List (Pos × ORef)) (p : Pos) : Bool :=
  table.any (·.1 = p)

/-- Export a fresh object at a fresh non-bootstrap position. -/
def exportNew (s : State) (p : Pos) (r : ORef) : Option State :=
  if s.alive && !hasPos s.exported p && p ≠ bootstrapPos
  then some { s with exported := (p, r) :: s.exported }
  else none

/-- Receive an import descriptor for a fresh position. -/
def importNew (s : State) (p : Pos) (r : ORef) : Option State :=
  if s.alive && !hasPos s.imported p
  then some { s with imported := (p, r) :: s.imported }
  else none

/-- Abort the session: irreversible. -/
def abort (s : State) : State :=
  { s with alive := false }

------------------------------------------------------------------------
-- Refinement-style invariant: bootstrap-at-zero, proved in Lean
------------------------------------------------------------------------

/-- Lean restatement of `Captp.Spec.safety [bootstrap_at_zero]`. -/
def bootstrapAtZero (s : State) : Prop :=
  s.alive = true → (bootstrapPos, bootstrapObj) ∈ s.exported

/-- The invariant holds in the initial state. -/
theorem bootstrapAtZero_initial : bootstrapAtZero initial := by
  intro _
  simp [initial]

/-- `exportNew` preserves the invariant. -/
theorem bootstrapAtZero_exportNew
    (s : State) (p : Pos) (r : ORef) (s' : State)
    (h : bootstrapAtZero s) (heq : exportNew s p r = some s') :
    bootstrapAtZero s' := by
  unfold exportNew at heq
  split at heq
  · -- the guard held → s' is s with one extra exported entry
    rename_i hcond
    simp only [Option.some.injEq] at heq
    subst heq
    intro _
    have halive_s : s.alive = true := by
      simp [Bool.and_eq_true] at hcond
      exact hcond.left.left
    exact List.mem_cons_of_mem _ (h halive_s)
  · -- guard failed → heq : none = some s' → impossible
    exact (Option.noConfusion heq)

/-- `importNew` preserves the invariant — it doesn't touch the
exported table or `alive`. -/
theorem bootstrapAtZero_importNew
    (s : State) (p : Pos) (r : ORef) (s' : State)
    (h : bootstrapAtZero s) (heq : importNew s p r = some s') :
    bootstrapAtZero s' := by
  unfold importNew at heq
  split at heq
  · rename_i hcond
    simp only [Option.some.injEq] at heq
    subst heq
    intro _
    have halive_s : s.alive = true := by
      simp [Bool.and_eq_true] at hcond
      exact hcond.left
    exact h halive_s
  · exact (Option.noConfusion heq)

/-- `abort` preserves the invariant vacuously: after abort, `alive`
is false, so the implication is satisfied for any RHS. -/
theorem bootstrapAtZero_abort (s : State) : bootstrapAtZero (abort s) := by
  intro halive'
  simp [abort] at halive'

------------------------------------------------------------------------
-- Concrete-instance smoke tests (compile-time verified)
------------------------------------------------------------------------

example : bootstrapAtZero initial := bootstrapAtZero_initial

example :
    let s₁ := initial
    let s₂ := (exportNew s₁ 1 100).get!
    let s₃ := (exportNew s₂ 2 200).get!
    bootstrapAtZero s₃ := by
  apply bootstrapAtZero_exportNew _ 2 200
  apply bootstrapAtZero_exportNew _ 1 100
  exact bootstrapAtZero_initial
  all_goals rfl

example :
    let s₁ := initial
    let s₂ := abort s₁
    bootstrapAtZero s₂ := bootstrapAtZero_abort _

end OcapnLean.Captp.Impl
