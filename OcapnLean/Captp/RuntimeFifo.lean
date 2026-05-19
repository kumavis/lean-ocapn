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
FIFO claim, plus promise/forwarding state for the ref-FIFO-e2e claim
across forwarding. -/
@[ext]
structure RuntimeState where
  channels    : Vat → Vat → ChannelQueue := fun _ _ => default
  routesTo    : RouteMap                  := fun _ _ => none
  targetRef   : TargetRefOracle           := fun _ => 0
  /-- Marks a ref as a promise. -/
  isPromise   : Ref → Bool                := fun _ => false
  /-- Promise resolution: `resolvedTo r = some v` means promise `r`
  resolved to a value hosted at vat `v`. -/
  resolvedTo  : Ref → Option Vat          := fun _ => none
  /-- Forwarding ledger: `forwardedAt b c m = some k` means `b`
  forwarded `m` onto `b→c` wire at index `k`. -/
  forwardedAt : Vat → Vat → ByteArray → Option Nat := fun _ _ _ => none

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
  /-- Mark a ref as a promise. -/
  | declarePromise (p : Ref)
  /-- Vat `b` learns promise `p` resolved to a value at vat `c`.
  Sets resolvedTo + installs b's forwarding route routesTo[b, p] := c. -/
  | resolvePromise (b c : Vat) (p : Ref)
  /-- Vat `b` re-emits previously-delivered msg `msg` onto b→c wire.
  Pushes onto sent (like send, but doesn't touch sentBy/origination). -/
  | forward (b c : Vat) (msg : ByteArray)

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
  | .declarePromise p =>
    { s with isPromise := fun r => if r = p then true else s.isPromise r }
  | .resolvePromise b c p =>
    if ¬ s.isPromise p then s
    else if s.resolvedTo p ≠ none then s
    else
      -- Install both the promise resolution and the forwarder's route.
      { s with
        resolvedTo := fun r => if r = p then some c else s.resolvedTo r,
        routesTo := fun v r => if v = b ∧ r = p then some c else s.routesTo v r }
  | .forward b c msg =>
    let q := s.channels b c
    -- Pre: msg was already delivered at b from someone; we model the
    -- "forwarded" tag explicitly. For now, push onto sent and mark forwarded.
    if s.forwardedAt b c msg ≠ none then s
    else
      { (update s b c { q with sent := q.sent.push msg }) with
        forwardedAt := fun b' c' m' =>
          if b' = b ∧ c' = c ∧ m' = msg then some q.sent.size
          else s.forwardedAt b' c' m' }

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

/-- `declarePromise` doesn't touch channel state. -/
theorem Action.declarePromise_channels
    (s : RuntimeState) (p : Ref) :
    ((Action.declarePromise p).apply s).channels = s.channels := by rfl

/-- `resolvePromise` doesn't touch channel state. -/
theorem Action.resolvePromise_channels
    (s : RuntimeState) (b c : Vat) (p : Ref) :
    ((Action.resolvePromise b c p).apply s).channels = s.channels := by
  dsimp only [Action.apply]
  split
  · rfl
  · split <;> rfl

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

/-- `declarePromise` and `resolvePromise` don't touch channels — use
the channel-preservation lemmas above. -/
theorem InvSizeOrdered.declarePromise
    (s : RuntimeState) (p : Ref) (h : InvSizeOrdered s) :
    InvSizeOrdered ((Action.declarePromise p).apply s) := by
  intro S D
  rw [show ((Action.declarePromise p).apply s).channels S D = s.channels S D from
        congrFun (congrFun (Action.declarePromise_channels s p) S) D]
  exact h S D

theorem InvSizeOrdered.resolvePromise
    (s : RuntimeState) (b c : Vat) (p : Ref) (h : InvSizeOrdered s) :
    InvSizeOrdered ((Action.resolvePromise b c p).apply s) := by
  intro S D
  rw [show ((Action.resolvePromise b c p).apply s).channels S D = s.channels S D from
        congrFun (congrFun (Action.resolvePromise_channels s b c p) S) D]
  exact h S D

/-- `forward` does touch channels — pushes onto sent on b→c (when not
already forwarded), same shape as send. -/
theorem InvSizeOrdered.forward
    (s : RuntimeState) (b c : Vat) (msg : ByteArray) (h : InvSizeOrdered s) :
    InvSizeOrdered ((Action.forward b c msg).apply s) := by
  intro S D
  dsimp only [Action.apply]
  by_cases hfwd : s.forwardedAt b c msg ≠ none
  · simp [hfwd]; exact h S D
  · simp [hfwd]
    -- Updates (b, c) channel: sent grows by 1, received unchanged.
    by_cases heq : S = b ∧ D = c
    · obtain ⟨rfl, rfl⟩ := heq
      show ((update s S D _).channels S D).received.size ≤ _
      rw [update_eq]
      have hsz := h S D
      simp [Array.size_push]; omega
    · show ((update s b c _).channels S D).received.size ≤
            ((update s b c _).channels S D).sent.size
      rw [update_ne _ b c _ S D heq]
      exact h S D

theorem InvSizeOrdered.action_preserves
    (s : RuntimeState) (a : Action) (h : InvSizeOrdered s) :
    InvSizeOrdered (a.apply s) := by
  cases a with
  | send src dst msg       => exact InvSizeOrdered.send s src dst msg h
  | recv src dst           => exact InvSizeOrdered.recv s src dst h
  | setupRoute v dst rf    => exact InvSizeOrdered.setupRoute s v dst rf h
  | handoff g r e rf       => exact InvSizeOrdered.handoff s g r e rf h
  | declarePromise p       => exact InvSizeOrdered.declarePromise s p h
  | resolvePromise b c p   => exact InvSizeOrdered.resolvePromise s b c p h
  | forward b c msg        => exact InvSizeOrdered.forward s b c msg h

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

/-- `declarePromise` / `resolvePromise` don't touch channels. -/
theorem InvDeliverIsPrefix.declarePromise
    (s : RuntimeState) (p : Ref) (h : InvDeliverIsPrefix s) :
    InvDeliverIsPrefix ((Action.declarePromise p).apply s) := by
  intro S D
  have hch : ((Action.declarePromise p).apply s).channels S D = s.channels S D :=
    congrFun (congrFun (Action.declarePromise_channels s p) S) D
  rw [hch]
  exact h S D

theorem InvDeliverIsPrefix.resolvePromise
    (s : RuntimeState) (b c : Vat) (p : Ref) (h : InvDeliverIsPrefix s) :
    InvDeliverIsPrefix ((Action.resolvePromise b c p).apply s) := by
  intro S D
  have hch : ((Action.resolvePromise b c p).apply s).channels S D = s.channels S D :=
    congrFun (congrFun (Action.resolvePromise_channels s b c p) S) D
  rw [hch]
  exact h S D

/-- `forward` preserves the prefix invariant — its effect on channels
matches `send`'s (push onto `sent`, leave `received` unchanged). -/
theorem InvDeliverIsPrefix.forward
    (s : RuntimeState) (b c : Vat) (msg : ByteArray)
    (h : InvDeliverIsPrefix s) :
    InvDeliverIsPrefix ((Action.forward b c msg).apply s) := by
  intro S D
  dsimp only [Action.apply]
  by_cases hfwd : s.forwardedAt b c msg ≠ none
  · simp [hfwd]; exact h S D
  · simp [hfwd]
    by_cases heq : S = b ∧ D = c
    · obtain ⟨rfl, rfl⟩ := heq
      show ((update s S D _).channels S D).received.size ≤ _ ∧ _
      rw [update_eq]
      have ⟨hsz, helt⟩ := h S D
      refine ⟨?_, ?_⟩
      · simp [Array.size_push]; omega
      · intro j hj
        have hjs : j < (s.channels S D).sent.size := Nat.lt_of_lt_of_le hj hsz
        show (s.channels S D).received[j]? = ((s.channels S D).sent.push msg)[j]?
        rw [Array.getElem?_push_lt hjs]
        rw [helt j hj, Array.getElem?_eq_getElem hjs]
    · show ((update s b c _).channels S D).received.size ≤ _ ∧ _
      rw [update_ne _ b c _ S D heq]
      exact h S D

theorem InvDeliverIsPrefix.action_preserves
    (s : RuntimeState) (a : Action) (h : InvDeliverIsPrefix s) :
    InvDeliverIsPrefix (a.apply s) := by
  cases a with
  | send src dst msg       => exact InvDeliverIsPrefix.send s src dst msg h
  | recv src dst           => exact InvDeliverIsPrefix.recv s src dst h
  | setupRoute v dst rf    => exact InvDeliverIsPrefix.setupRoute s v dst rf h
  | handoff g r e rf       => exact InvDeliverIsPrefix.handoff s g r e rf h
  | declarePromise p       => exact InvDeliverIsPrefix.declarePromise s p h
  | resolvePromise b c p   => exact InvDeliverIsPrefix.resolvePromise s b c p h
  | forward b c msg        => exact InvDeliverIsPrefix.forward s b c msg h

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

/-! ## Runtime ref-FIFO across forwarding (chunk 8)

The `forward` action records each forwarded msg in `forwardedAt b c`
along with the *index* on the `b→c` channel where it was pushed onto
`sent`. The invariant below states that this recorded index is
faithful: at the recorded index, the channel's `sent` array does
contain that msg. This is the foundation for the runtime ref-FIFO-e2e
claim — once we have it, forwarding-order on `b→c` matches the order
of forward actions in the trace (since indices are append-only and
ascending). -/

/-- **`forwardedAt` agrees with `sent`.** Whenever the trace has
recorded a forwarding event at index `i` (i.e., `s.forwardedAt b c msg
= some i`), then position `i` of the `b→c` channel's `sent` array
contains that msg. Proven by induction over the action sequence. -/
def InvForwardedAgreesWithSent (s : RuntimeState) : Prop :=
  ∀ b c msg i,
    s.forwardedAt b c msg = some i →
    (s.channels b c).sent[i]? = some msg

theorem InvForwardedAgreesWithSent.holds_at_initial :
    InvForwardedAgreesWithSent initial := by
  intro b c msg i hf
  -- initial.forwardedAt = fun _ _ _ => none, so hf : none = some i is impossible.
  simp [initial] at hf

theorem InvForwardedAgreesWithSent.send
    (s : RuntimeState) (asrc adst : Vat) (msg : ByteArray)
    (h : InvForwardedAgreesWithSent s) :
    InvForwardedAgreesWithSent ((Action.send asrc adst msg).apply s) := by
  intro b c m i hf
  dsimp only [Action.apply] at hf ⊢
  -- send only updates channels and adds to (asrc, adst).sent; forwardedAt unchanged.
  have hf' : s.forwardedAt b c m = some i := hf
  have ih := h b c m i hf'
  by_cases heq : b = asrc ∧ c = adst
  · obtain ⟨rfl, rfl⟩ := heq
    rw [update_eq]
    show ((s.channels b c).sent.push msg)[i]? = some m
    have hi : i < (s.channels b c).sent.size := by
      rcases Nat.lt_or_ge i (s.channels b c).sent.size with hlt | hge
      · exact hlt
      · rw [Array.getElem?_eq_none hge] at ih; exact absurd ih (by simp)
    rw [Array.getElem?_push_lt hi]
    rw [Array.getElem?_eq_getElem hi] at ih
    exact ih
  · show ((update s asrc adst _).channels b c).sent[i]? = some m
    rw [update_ne _ asrc adst _ b c heq]
    exact ih

theorem InvForwardedAgreesWithSent.recv
    (s : RuntimeState) (asrc adst : Vat)
    (h : InvForwardedAgreesWithSent s) :
    InvForwardedAgreesWithSent ((Action.recv asrc adst).apply s) := by
  intro b c m i hf
  dsimp only [Action.apply] at hf ⊢
  by_cases hbusy : (s.channels asrc adst).received.size < (s.channels asrc adst).sent.size
  · simp [hbusy] at hf ⊢
    -- recv only updates received; forwardedAt and sent unchanged.
    have hf' : s.forwardedAt b c m = some i := hf
    have ih := h b c m i hf'
    by_cases heq : b = asrc ∧ c = adst
    · obtain ⟨rfl, rfl⟩ := heq
      rw [update_eq]
      -- (s.channels b c).sent is unchanged by recv (only received grew).
      exact ih
    · rw [update_ne _ asrc adst _ b c heq]
      exact ih
  · simp [hbusy] at hf ⊢
    exact h b c m i hf

theorem InvForwardedAgreesWithSent.setupRoute
    (s : RuntimeState) (v dst : Vat) (rf : Ref)
    (h : InvForwardedAgreesWithSent s) :
    InvForwardedAgreesWithSent ((Action.setupRoute v dst rf).apply s) := by
  intro b c m i hf
  have hch := Action.setupRoute_channels s v dst rf
  -- forwardedAt unchanged by setupRoute (only routesTo changes).
  have hfsame : ((Action.setupRoute v dst rf).apply s).forwardedAt b c m =
                s.forwardedAt b c m := by
    dsimp only [Action.apply]
    split
    · split <;> rfl
    · rfl
  rw [congrFun (congrFun hch b) c]
  rw [hfsame] at hf
  exact h b c m i hf

theorem InvForwardedAgreesWithSent.handoff
    (s : RuntimeState) (g r e : Vat) (rf : Ref)
    (h : InvForwardedAgreesWithSent s) :
    InvForwardedAgreesWithSent ((Action.handoff g r e rf).apply s) := by
  intro b c m i hf
  have hch := Action.handoff_channels s g r e rf
  have hfsame : ((Action.handoff g r e rf).apply s).forwardedAt b c m =
                s.forwardedAt b c m := by
    dsimp only [Action.apply]
    split
    · rfl
    · split
      · split <;> rfl
      · rfl
  rw [congrFun (congrFun hch b) c]
  rw [hfsame] at hf
  exact h b c m i hf

theorem InvForwardedAgreesWithSent.declarePromise
    (s : RuntimeState) (p : Ref)
    (h : InvForwardedAgreesWithSent s) :
    InvForwardedAgreesWithSent ((Action.declarePromise p).apply s) := by
  intro b c m i hf
  -- declarePromise only updates isPromise; channels and forwardedAt unchanged.
  exact h b c m i hf

theorem InvForwardedAgreesWithSent.resolvePromise
    (s : RuntimeState) (rb rc : Vat) (p : Ref)
    (h : InvForwardedAgreesWithSent s) :
    InvForwardedAgreesWithSent ((Action.resolvePromise rb rc p).apply s) := by
  intro b c m i hf
  have hch := Action.resolvePromise_channels s rb rc p
  -- resolvePromise only updates resolvedTo + routesTo (no forwardedAt change).
  have hfsame : ((Action.resolvePromise rb rc p).apply s).forwardedAt b c m =
                s.forwardedAt b c m := by
    dsimp only [Action.apply]
    by_cases h1 : ¬ s.isPromise p
    · simp [h1]
    · simp [h1]
      by_cases h2 : s.resolvedTo p = none
      · simp [h2]
      · simp [h2]
  rw [congrFun (congrFun hch b) c]
  rw [hfsame] at hf
  exact h b c m i hf

theorem InvForwardedAgreesWithSent.forward
    (s : RuntimeState) (fb fc : Vat) (fmsg : ByteArray)
    (h : InvForwardedAgreesWithSent s) :
    InvForwardedAgreesWithSent ((Action.forward fb fc fmsg).apply s) := by
  intro b c m i hf
  dsimp only [Action.apply] at hf ⊢
  by_cases hfwd : s.forwardedAt fb fc fmsg ≠ none
  · simp [hfwd] at hf ⊢
    exact h b c m i hf
  · simp [hfwd] at hf ⊢
    -- After forward: channels (fb, fc) has sent.push fmsg, and forwardedAt
    -- now maps (fb, fc, fmsg) to old sent.size; else unchanged.
    by_cases hkey : b = fb ∧ c = fc ∧ m = fmsg
    · -- The newly-recorded forwarding event: i must equal old sent.size.
      obtain ⟨hbeq, hceq, hmeq⟩ := hkey
      subst hbeq; subst hceq; subst hmeq
      simp at hf
      subst hf
      rw [update_eq]
      exact Array.getElem?_push_size
    · -- Old forwardedAt entry is still recorded; ih applies.
      have hf' : s.forwardedAt b c m = some i := by
        have hne : ¬ (b = fb ∧ c = fc ∧ m = fmsg) := hkey
        simp [hne] at hf
        exact hf
      have ih := h b c m i hf'
      have hi : i < (s.channels b c).sent.size := by
        rcases Nat.lt_or_ge i (s.channels b c).sent.size with hlt | hge
        · exact hlt
        · rw [Array.getElem?_eq_none hge] at ih
          exact absurd ih (by simp)
      by_cases hbc : b = fb ∧ c = fc
      · obtain ⟨hbeq2, hceq2⟩ := hbc
        subst hbeq2; subst hceq2
        show ((update s b c { sent := (s.channels b c).sent.push fmsg, received := (s.channels b c).received }).channels b c).sent[i]? = some m
        rw [update_eq]
        show ((s.channels b c).sent.push fmsg)[i]? = some m
        rw [Array.getElem?_push_lt hi]
        rw [Array.getElem?_eq_getElem hi] at ih
        exact ih
      · show ((update s fb fc _).channels b c).sent[i]? = some m
        rw [update_ne _ fb fc _ b c hbc]
        exact ih

theorem InvForwardedAgreesWithSent.action_preserves
    (s : RuntimeState) (a : Action) (h : InvForwardedAgreesWithSent s) :
    InvForwardedAgreesWithSent (a.apply s) := by
  cases a with
  | send src dst msg       => exact InvForwardedAgreesWithSent.send s src dst msg h
  | recv src dst           => exact InvForwardedAgreesWithSent.recv s src dst h
  | setupRoute v dst rf    => exact InvForwardedAgreesWithSent.setupRoute s v dst rf h
  | handoff g r e rf       => exact InvForwardedAgreesWithSent.handoff s g r e rf h
  | declarePromise p       => exact InvForwardedAgreesWithSent.declarePromise s p h
  | resolvePromise b c p   => exact InvForwardedAgreesWithSent.resolvePromise s b c p h
  | forward b c msg        => exact InvForwardedAgreesWithSent.forward s b c msg h

theorem InvForwardedAgreesWithSent.runActions_preserves
    (s : RuntimeState) (h : InvForwardedAgreesWithSent s)
    (actions : List Action) :
    InvForwardedAgreesWithSent (runActions s actions) := by
  induction actions generalizing s with
  | nil => exact h
  | cons a as ih =>
    show InvForwardedAgreesWithSent (runActions (a.apply s) as)
    exact ih (a.apply s) (InvForwardedAgreesWithSent.action_preserves s a h)

theorem InvForwardedAgreesWithSent.reachable
    (s : RuntimeState) (h : Reachable s) :
    InvForwardedAgreesWithSent s := by
  obtain ⟨actions, hrun⟩ := h
  subst hrun
  exact InvForwardedAgreesWithSent.runActions_preserves
    initial InvForwardedAgreesWithSent.holds_at_initial actions

/-- **Runtime ref-FIFO-e2e** (foundation). If two forwarding events
have been recorded on the same `b→c` channel at indices `i1 < i2`,
then on `b→c`'s `sent` array, msg1 appears at position `i1` and msg2
at position `i2`. Combined with the per-channel FIFO at the `b→c`
channel (`InvDeliverIsPrefix.reachable`), msgs delivered at C arrive
in the same order they were forwarded. -/
theorem runtime_forward_order_preserved
    (s : RuntimeState) (hreach : Reachable s)
    (b c : Vat) (msg1 msg2 : ByteArray) (i1 i2 : Nat)
    (hf1 : s.forwardedAt b c msg1 = some i1)
    (hf2 : s.forwardedAt b c msg2 = some i2) :
    (s.channels b c).sent[i1]? = some msg1 ∧
    (s.channels b c).sent[i2]? = some msg2 := by
  have hinv := InvForwardedAgreesWithSent.reachable s hreach
  exact ⟨hinv b c msg1 i1 hf1, hinv b c msg2 i2 hf2⟩

end OcapnLean.Captp.RuntimeFifo
