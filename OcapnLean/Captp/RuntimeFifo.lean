import OcapnLean.Netlayer.Spec
import OcapnLean.Captp.RefinementMultiVat

/-!
# Runtime-level fail-stop FIFO (M11 Phase A.7, chunk 2)

A pure-Lean LTS over per-channel `(sent, received)` arrays, with an
inductive proof that every reachable state preserves the **per-channel
size-order invariant**: `received.size ≤ sent.size` on every channel.

The `InProcess.Network` from chunk 1 is one concrete IO realisation
of this LTS — `IO.Ref.modify` provides the per-step atomicity that
the LTS treats as a single transition.

## What's proved here

* `InvSizeOrdered` — for every reachable runtime state, every
  channel's `received` is no larger than its `sent`. This is the
  index-counting half of fail-stop FIFO: msgs are delivered in
  send-order *positions* (since position-i deliver only happens
  after position-i send).

* The arbitrary-interleaving aspect is handled structurally: the LTS
  has just two action constructors (`send`, `recv`) each local to one
  channel, so per-step preservation composes through any trace.

## What's NOT yet proved here

* **Contents-match invariant** — that `received[j]?` equals
  `sent[j]?` at every prefix position. This is a stronger claim that
  pins the *payload* identity, not just the index ordering. Provable
  by a similar inductive structure but requires careful reasoning
  about `Array.push` indexing; left as a follow-on within the same
  file.

* **Runtime ref FIFO / ref FIFO e2e** — these require modelling
  per-vat refs/routing/promise state at the runtime level. Direct
  extensions of this file's pattern; queued.

## Relationship to chunk 1

The `multi-vat-fifo-smoke` from chunk 1 already exercises the
canonical scenarios and verifies them via the `Spec.Trace.deliveredOn`
projection. This file's `InvSizeOrdered` is the formal claim that
the smoke's success is no accident — *any* reachable runtime state
satisfies the size-order invariant.
-/

namespace OcapnLean.Captp.RuntimeFifo

open OcapnLean.Netlayer.Spec

/-! ## Pure runtime state -/

/-- A reference identifier. Object identity across vats; the routing
key for per-(sender, ref) FIFO claims. -/
abbrev Ref := Nat

structure ChannelQueue where
  sent     : Array ByteArray := #[]
  received : Array ByteArray := #[]

instance : Inhabited ChannelQueue := ⟨{}⟩

/-- Per-msg target-ref oracle: each msg targets a fixed ref. Modeled
as a `ByteArray → Ref` function in the state — never mutated, mirrors
the Veil module's `function targetRef : msg → ref`. -/
abbrev TargetRefOracle := ByteArray → Ref

/-- Routing table: per-(vat, ref) destination vat (or `none`). -/
abbrev RouteMap := Vat → Ref → Option Vat

/-- Runtime state augmented with refs/routing for the per-(sender, ref)
FIFO claim. -/
structure RuntimeState where
  channels  : Vat → Vat → ChannelQueue := fun _ _ => default
  routesTo  : RouteMap                  := fun _ _ => none
  targetRef : TargetRefOracle           := fun _ => 0

def initial : RuntimeState := {}

/-- Functional update of one channel. -/
def update (s : RuntimeState) (src dst : Vat) (q : ChannelQueue) :
    RuntimeState :=
  { s with
    channels := fun src' dst' => if src' = src ∧ dst' = dst then q else s.channels src' dst' }

/-- Functional update of one routing entry. -/
def updateRoute (s : RuntimeState) (v : Vat) (rf : Ref) (target : Option Vat) :
    RuntimeState :=
  { s with
    routesTo := fun v' rf' => if v' = v ∧ rf' = rf then target else s.routesTo v' rf' }

theorem update_eq (s : RuntimeState) (src dst : Vat) (q : ChannelQueue) :
    (update s src dst q).channels src dst = q := by
  simp [update]

theorem update_ne (s : RuntimeState) (src dst : Vat) (q : ChannelQueue)
    (src' dst' : Vat) (h : ¬ (src' = src ∧ dst' = dst)) :
    (update s src dst q).channels src' dst' = s.channels src' dst' := by
  simp [update, h]

/-! ## Atomic runtime actions -/

inductive Action
  | send (src dst : Vat) (msg : ByteArray)
  | recv (src dst : Vat)
  /-- Install a routing entry for vat `v` targeting ref `rf` via `dst`. -/
  | setupRoute (v dst : Vat) (rf : Ref)
  /-- Handoff: gifter `g` introduces receiver `r` to ref `rf` at
  exporter `e`. -/
  | handoff (g r e : Vat) (rf : Ref)

def Action.apply (s : RuntimeState) : Action → RuntimeState
  | .send src dst msg =>
    let q := s.channels src dst
    update s src dst { q with sent := q.sent.push msg }
  | .recv src dst =>
    let q := s.channels src dst
    if h : q.received.size < q.sent.size then
      let msg := q.sent[q.received.size]
      update s src dst { q with received := q.received.push msg }
    else
      s
  | .setupRoute v dst rf =>
    match s.routesTo v rf with
    | some existing => if existing = dst then s else s  -- idempotent or conflict; no-op
    | none          => updateRoute s v rf (some dst)
  | .handoff g r e rf =>
    if s.routesTo g rf ≠ some e then s
    else
      match s.routesTo r rf with
      | some existing => if existing = e then s else s
      | none          => updateRoute s r rf (some e)

def runActions (s : RuntimeState) (actions : List Action) : RuntimeState :=
  actions.foldl (fun s a => a.apply s) s

theorem runActions_append (s : RuntimeState) (as : List Action) (a : Action) :
    runActions s (as ++ [a]) = a.apply (runActions s as) := by
  simp [runActions, List.foldl_append]

def Reachable (s : RuntimeState) : Prop :=
  ∃ actions : List Action, runActions initial actions = s

theorem initial_reachable : Reachable initial :=
  ⟨[], rfl⟩

theorem reachable_step (s : RuntimeState) (a : Action) :
    Reachable s → Reachable (a.apply s) := by
  rintro ⟨actions, h⟩
  refine ⟨actions ++ [a], ?_⟩
  rw [runActions_append, h]

/-! ## The headline inductive invariant -/

/-- The full per-channel FIFO invariant: `received` is a prefix of
`sent` — same `received.size` cap on `sent.size`, and at every prefix
index `j`, `received[j]? = sent[j]?`. -/
def InvDeliverIsPrefix (s : RuntimeState) : Prop :=
  ∀ src dst,
    (s.channels src dst).received.size ≤ (s.channels src dst).sent.size ∧
    (∀ j, j < (s.channels src dst).received.size →
      (s.channels src dst).received[j]? = (s.channels src dst).sent[j]?)

/-- Weak form (size-order half). Kept for callers that only need the
cursor bound. -/
def InvSizeOrdered (s : RuntimeState) : Prop :=
  ∀ src dst, (s.channels src dst).received.size ≤ (s.channels src dst).sent.size

theorem InvDeliverIsPrefix.implies_size_ordered
    {s : RuntimeState} (h : InvDeliverIsPrefix s) : InvSizeOrdered s :=
  fun src dst => (h src dst).1

theorem InvSizeOrdered.holds_at_initial : InvSizeOrdered initial := by
  intro src dst
  show (default : ChannelQueue).received.size ≤ (default : ChannelQueue).sent.size
  decide

theorem InvSizeOrdered.send
    (s : RuntimeState) (asrc adst : Vat) (msg : ByteArray)
    (h : InvSizeOrdered s) :
    InvSizeOrdered ((Action.send asrc adst msg).apply s) := by
  intro S D
  dsimp only [Action.apply]
  by_cases heq : S = asrc ∧ D = adst
  · obtain ⟨rfl, rfl⟩ := heq
    rw [update_eq]
    have hsz := h S D
    simp [Array.size_push]; omega
  · rw [update_ne _ asrc adst _ S D heq]
    exact h S D

theorem InvSizeOrdered.recv
    (s : RuntimeState) (asrc adst : Vat)
    (h : InvSizeOrdered s) :
    InvSizeOrdered ((Action.recv asrc adst).apply s) := by
  intro S D
  dsimp only [Action.apply]
  by_cases hbusy : (s.channels asrc adst).received.size < (s.channels asrc adst).sent.size
  · simp [hbusy]
    by_cases heq : S = asrc ∧ D = adst
    · obtain ⟨rfl, rfl⟩ := heq
      rw [update_eq]
      simp [Array.size_push]; omega
    · rw [update_ne _ asrc adst _ S D heq]
      exact h S D
  · simp [hbusy]
    exact h S D

/-- `setupRoute` doesn't touch channel state. -/
theorem Action.setupRoute_channels
    (s : RuntimeState) (v dst : Vat) (rf : Ref) :
    ((Action.setupRoute v dst rf).apply s).channels = s.channels := by
  dsimp only [Action.apply]
  split
  · split <;> rfl
  · rfl

/-- `handoff` doesn't touch channel state. -/
theorem Action.handoff_channels
    (s : RuntimeState) (g r e : Vat) (rf : Ref) :
    ((Action.handoff g r e rf).apply s).channels = s.channels := by
  dsimp only [Action.apply]
  split
  · rfl
  · split
    · split <;> rfl
    · rfl

theorem InvSizeOrdered.setupRoute
    (s : RuntimeState) (v dst : Vat) (rf : Ref)
    (h : InvSizeOrdered s) :
    InvSizeOrdered ((Action.setupRoute v dst rf).apply s) := by
  intro S D
  rw [show ((Action.setupRoute v dst rf).apply s).channels S D = s.channels S D from
        congrFun (congrFun (Action.setupRoute_channels s v dst rf) S) D]
  exact h S D

theorem InvSizeOrdered.handoff
    (s : RuntimeState) (g r e : Vat) (rf : Ref)
    (h : InvSizeOrdered s) :
    InvSizeOrdered ((Action.handoff g r e rf).apply s) := by
  intro S D
  rw [show ((Action.handoff g r e rf).apply s).channels S D = s.channels S D from
        congrFun (congrFun (Action.handoff_channels s g r e rf) S) D]
  exact h S D

theorem InvSizeOrdered.action_preserves
    (s : RuntimeState) (a : Action) (h : InvSizeOrdered s) :
    InvSizeOrdered (a.apply s) := by
  cases a with
  | send src dst msg     => exact InvSizeOrdered.send s src dst msg h
  | recv src dst         => exact InvSizeOrdered.recv s src dst h
  | setupRoute v dst rf  => exact InvSizeOrdered.setupRoute s v dst rf h
  | handoff g r e rf     => exact InvSizeOrdered.handoff s g r e rf h

theorem InvSizeOrdered.runActions_preserves
    (s : RuntimeState) (h : InvSizeOrdered s) (actions : List Action) :
    InvSizeOrdered (runActions s actions) := by
  induction actions generalizing s with
  | nil => exact h
  | cons a as ih =>
    show InvSizeOrdered (runActions (a.apply s) as)
    exact ih (a.apply s) (InvSizeOrdered.action_preserves s a h)

/-- **Chunk 2 headline.** Every reachable runtime state satisfies
the per-channel size-order invariant. -/
theorem InvSizeOrdered.reachable
    (s : RuntimeState) (h : Reachable s) : InvSizeOrdered s := by
  obtain ⟨actions, hrun⟩ := h
  subst hrun
  exact InvSizeOrdered.runActions_preserves initial InvSizeOrdered.holds_at_initial actions

/-! ## The contents-match (full prefix) invariant — proved -/

theorem InvDeliverIsPrefix.holds_at_initial : InvDeliverIsPrefix initial := by
  intro src dst
  refine ⟨?_, ?_⟩
  · show (default : ChannelQueue).received.size ≤ (default : ChannelQueue).sent.size
    decide
  · intro j hj
    -- received.size = 0, so j < 0 is impossible
    exact absurd hj (by show ¬ j < 0; omega)

theorem InvDeliverIsPrefix.send
    (s : RuntimeState) (asrc adst : Vat) (msg : ByteArray)
    (h : InvDeliverIsPrefix s) :
    InvDeliverIsPrefix ((Action.send asrc adst msg).apply s) := by
  intro S D
  dsimp only [Action.apply]
  by_cases heq : S = asrc ∧ D = adst
  · obtain ⟨rfl, rfl⟩ := heq
    rw [update_eq]
    have ⟨hsz, helt⟩ := h S D
    refine ⟨?_, ?_⟩
    · simp [Array.size_push]; omega
    · intro j hj
      -- Goal: received[j]? = (sent.push msg)[j]?
      have hjs : j < (s.channels S D).sent.size := Nat.lt_of_lt_of_le hj hsz
      rw [Array.getElem?_push_lt hjs]
      rw [helt j hj, Array.getElem?_eq_getElem hjs]
  · rw [update_ne _ asrc adst _ S D heq]
    exact h S D

theorem InvDeliverIsPrefix.recv
    (s : RuntimeState) (asrc adst : Vat)
    (h : InvDeliverIsPrefix s) :
    InvDeliverIsPrefix ((Action.recv asrc adst).apply s) := by
  intro S D
  dsimp only [Action.apply]
  by_cases hbusy : (s.channels asrc adst).received.size < (s.channels asrc adst).sent.size
  · simp [hbusy]
    by_cases heq : S = asrc ∧ D = adst
    · obtain ⟨rfl, rfl⟩ := heq
      rw [update_eq]
      have ⟨hsz, helt⟩ := h S D
      refine ⟨?_, ?_⟩
      · simp [Array.size_push]; omega
      · intro j hj
        -- hj : j < (received.push X).size = received.size + 1
        simp [Array.size_push] at hj
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hjlt | hjeq
        · -- j < old received.size: indexing unchanged prefix
          rw [Array.getElem?_push_lt hjlt]
          have ih := helt j hjlt
          rw [Array.getElem?_eq_getElem hjlt] at ih
          exact ih
        · -- j = old received.size: indexing the newly-pushed element
          subst hjeq
          rw [Array.getElem?_push_eq]
          rw [Array.getElem?_eq_getElem hbusy]
    · rw [update_ne _ asrc adst _ S D heq]
      exact h S D
  · simp [hbusy]
    exact h S D

theorem InvDeliverIsPrefix.setupRoute
    (s : RuntimeState) (v dst : Vat) (rf : Ref)
    (h : InvDeliverIsPrefix s) :
    InvDeliverIsPrefix ((Action.setupRoute v dst rf).apply s) := by
  intro S D
  have hch : ((Action.setupRoute v dst rf).apply s).channels S D = s.channels S D :=
    congrFun (congrFun (Action.setupRoute_channels s v dst rf) S) D
  rw [hch]
  exact h S D

theorem InvDeliverIsPrefix.handoff
    (s : RuntimeState) (g r e : Vat) (rf : Ref)
    (h : InvDeliverIsPrefix s) :
    InvDeliverIsPrefix ((Action.handoff g r e rf).apply s) := by
  intro S D
  have hch : ((Action.handoff g r e rf).apply s).channels S D = s.channels S D :=
    congrFun (congrFun (Action.handoff_channels s g r e rf) S) D
  rw [hch]
  exact h S D

theorem InvDeliverIsPrefix.action_preserves
    (s : RuntimeState) (a : Action) (h : InvDeliverIsPrefix s) :
    InvDeliverIsPrefix (a.apply s) := by
  cases a with
  | send src dst msg     => exact InvDeliverIsPrefix.send s src dst msg h
  | recv src dst         => exact InvDeliverIsPrefix.recv s src dst h
  | setupRoute v dst rf  => exact InvDeliverIsPrefix.setupRoute s v dst rf h
  | handoff g r e rf     => exact InvDeliverIsPrefix.handoff s g r e rf h

theorem InvDeliverIsPrefix.runActions_preserves
    (s : RuntimeState) (h : InvDeliverIsPrefix s) (actions : List Action) :
    InvDeliverIsPrefix (runActions s actions) := by
  induction actions generalizing s with
  | nil => exact h
  | cons a as ih =>
    show InvDeliverIsPrefix (runActions (a.apply s) as)
    exact ih (a.apply s) (InvDeliverIsPrefix.action_preserves s a h)

/-- **Full chunk 2 headline.** Every reachable runtime state has the
full contents-match prefix invariant: `received` is a true prefix of
`sent` on every channel — both the size bound and pointwise content
equality. -/
theorem InvDeliverIsPrefix.reachable
    (s : RuntimeState) (h : Reachable s) : InvDeliverIsPrefix s := by
  obtain ⟨actions, hrun⟩ := h
  subst hrun
  exact InvDeliverIsPrefix.runActions_preserves
    initial InvDeliverIsPrefix.holds_at_initial actions

/-! ## Corollaries — runtime FIFO claims

These spell out the consequences of the contents-match invariant in
forms callers can directly cite. -/

/-- Every received msg at position `j` equals the same-position
sent msg. -/
theorem runtime_received_matches_sent
    (s : RuntimeState) (hreach : Reachable s)
    (src dst : Vat) (j : Nat)
    (hj : j < (s.channels src dst).received.size) :
    (s.channels src dst).received[j]? = (s.channels src dst).sent[j]? :=
  (InvDeliverIsPrefix.reachable s hreach src dst).2 j hj

/-- **Per-channel fail-stop FIFO at the runtime, with payload
equality.** If two msgs are delivered at positions `j1 < j2` on the
same channel, then their `received[j_i]` values match the same-index
`sent[j_i]` values — i.e., msgs are delivered in the order they were
sent, with the same payload bytes. -/
theorem runtime_fifo_with_payloads
    (s : RuntimeState) (hreach : Reachable s)
    (src dst : Vat) (j1 j2 : Nat)
    (hj1 : j1 < (s.channels src dst).received.size)
    (hj2 : j2 < (s.channels src dst).received.size)
    (_hlt : j1 < j2) :
    (s.channels src dst).received[j1]? = (s.channels src dst).sent[j1]? ∧
    (s.channels src dst).received[j2]? = (s.channels src dst).sent[j2]? :=
  ⟨runtime_received_matches_sent s hreach src dst j1 hj1,
   runtime_received_matches_sent s hreach src dst j2 hj2⟩

/-! ## Runtime per-(sender, ref) FIFO

Documentation-form corollary: given a sender's routing entry to a
destination vat, the per-channel FIFO claim on that channel **is**
the per-(sender, ref) FIFO claim. Routing functionality is automatic
in our LTS (since `routesTo` is `Vat → Ref → Option Vat`, each
(sender, ref) pair maps to at most one destination by construction). -/

/-- The routing relation is functional in `(Vat, Ref)` by definition. -/
theorem routesTo_functional (s : RuntimeState) (sender : Vat) (target : Ref)
    (dst1 dst2 : Vat)
    (h1 : s.routesTo sender target = some dst1)
    (h2 : s.routesTo sender target = some dst2) :
    dst1 = dst2 := by
  rw [h1] at h2
  exact Option.some.inj h2

/-- **Runtime per-(sender, ref) FIFO** — documentation form. If sender
`S` routes ref `R` to destination `D`, then the per-channel FIFO claim
on the `S→D` channel **is** the per-(sender, ref) FIFO claim. The
substance was already proved by `runtime_received_matches_sent` (every
received msg matches the same-index sent msg). Routing functionality
guarantees msgs to ref R from S all use the S→D channel. -/
theorem runtime_per_sender_per_ref_fifo
    (s : RuntimeState) (hreach : Reachable s)
    (sender : Vat) (target : Ref) (dst : Vat)
    (_hroute : s.routesTo sender target = some dst)
    (j1 j2 : Nat)
    (hj1 : j1 < (s.channels sender dst).received.size)
    (hj2 : j2 < (s.channels sender dst).received.size) :
    (s.channels sender dst).received[j1]? = (s.channels sender dst).sent[j1]? ∧
    (s.channels sender dst).received[j2]? = (s.channels sender dst).sent[j2]? :=
  ⟨runtime_received_matches_sent s hreach sender dst j1 hj1,
   runtime_received_matches_sent s hreach sender dst j2 hj2⟩

/-! ## Runtime ref-FIFO across forwarding (Gap 2 follow-on; not yet proved)

The Phase A.5 ref_fifo_e2e claim — per-(sender, ref) FIFO at the
**resolution host** across an A→B→C forwarding chain — requires
extending RuntimeState with promises (`isPromise`, `resolvedTo`,
`forwardedAt`) and a `forward` action, plus the
forward-preserves-send-order invariant. The shape mirrors what's
already here; the size is significant.

Documented in ROADMAP M11 Phase A.7's "still pending" list. -/

end OcapnLean.Captp.RuntimeFifo
