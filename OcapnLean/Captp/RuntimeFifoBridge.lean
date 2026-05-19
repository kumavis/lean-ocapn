import OcapnLean.Captp.RuntimeFifo
import OcapnLean.Netlayer.InProcess

/-!
# Bridge: in-process `Network` ↔ `RuntimeFifo.RuntimeState` (M11 Phase A.7, chunk 4)

Connects the in-process netlayer's concrete `NetworkState` to the
pure-Lean LTS in `RuntimeFifo`. Once this bridge is built, the runtime
FIFO claims proved in `RuntimeFifo` over the LTS carry over to any
multi-vat deployment using the in-process netlayer — including
`Captp.Session.run` running over `Network.netlayerFor`.

## What this addresses

* **Gap 3** of M11 Phase A.7: connecting `Captp.Session.run` (and any
  netlayer-driven runtime) to the LTS. Any peer running over an
  in-process `Netlayer` view of a `Network` corresponds to a sequence
  of `RuntimeFifo.Action.send` / `Action.recv` steps via the
  projection + per-op correspondence below.

* **Gap 4** of M11 Phase A.7: connecting the in-process netlayer's
  `snapshot` to the abstract `Netlayer.Spec.Valid` contract. The
  per-channel prefix invariant on the snapshot follows from
  `InvDeliverIsPrefix.reachable` on the projection.

## What this is *not*

Not a refactor of `Captp.Session.run` to expose RuntimeAction-shaped
call sites. `Captp.Session.run` already calls `Netlayer.sendMessage` /
`recvMessage?`; when the underlying netlayer is `Network.netlayerFor`,
those calls go through `Network.send` / `Network.recv?`, and the
per-op correspondence below ties those into LTS steps. The connection
is behavioural, not lexical.

## Status

This commit lands:
* `projectNetworkState` — the structural projection.

What's queued (mechanical, no new substance):
* Per-op correspondence theorems
  (`projectNetworkState (sendOnState ns ...)` equals
  `(Action.send ...).apply (projectNetworkState ns)`, and same for
  recv). The trickiness is `NetworkState`'s list-based store vs
  `RuntimeState`'s function-based store needing routine list-reasoning
  lemmas about `find?` / `filter`.
* Trace-level lifting (running a sequence of network ops then
  projecting equals projecting then running the corresponding actions).
* Snapshot → `Spec.Valid` conversion (Array.toList prefix from
  indexed equality).
-/

namespace OcapnLean.Captp.RuntimeFifoBridge

/-! ## Projection: `NetworkState` → `RuntimeState`

`InProcess.ChannelQueue` and `RuntimeFifo.ChannelQueue` have the same
structural shape (both record `sent : Array ByteArray` and
`received : Array ByteArray`). The projection lifts the per-channel
mapping point-wise. -/

/-- Map an `InProcess.ChannelQueue` to a `RuntimeFifo.ChannelQueue`. -/
def projectChannelQueue
    (nq : OcapnLean.Netlayer.InProcess.ChannelQueue) :
    OcapnLean.Captp.RuntimeFifo.ChannelQueue :=
  { sent := nq.sent, received := nq.received }

/-- Project an `InProcess.NetworkState` to a `RuntimeFifo.RuntimeState`.
Routing tables and target-ref oracle are left at their defaults — the
in-process netlayer doesn't track ref state, that lives at the
`MultiVat` / `RuntimeFifo` layer above. -/
def projectNetworkState
    (ns : OcapnLean.Netlayer.InProcess.NetworkState) :
    OcapnLean.Captp.RuntimeFifo.RuntimeState :=
  { channels  := fun src dst => projectChannelQueue (ns.get (src, dst))
    routesTo  := fun _ _ => none
    targetRef := fun _ => 0 }

/-! ## Pure-state mirrors of `Network.send` / `Network.recv?`

The `Network` IO operations factor through these pure functions on
`NetworkState`. Proving correspondence at the pure level lifts to IO
trivially since `Network.send` is just `state.modify` wrapping these. -/

/-- Pure-state `send`: append `msg` to the (src, dst) channel's
`sent` array. Mirrors `InProcess.Network.send` modulo the IO.Ref wrapper. -/
def sendOnState
    (ns : OcapnLean.Netlayer.InProcess.NetworkState)
    (src dst : OcapnLean.Netlayer.Spec.Vat) (msg : ByteArray) :
    OcapnLean.Netlayer.InProcess.NetworkState :=
  let q := ns.get (src, dst)
  ns.set (src, dst) { q with sent := q.sent.push msg }

/-- Pure-state `recv`. -/
def recvOnState
    (ns : OcapnLean.Netlayer.InProcess.NetworkState)
    (src dst : OcapnLean.Netlayer.Spec.Vat) :
    OcapnLean.Netlayer.InProcess.NetworkState :=
  let q := ns.get (src, dst)
  if h : q.received.size < q.sent.size then
    let msg := q.sent[q.received.size]
    ns.set (src, dst) { q with received := q.received.push msg }
  else
    ns

/-! ## Network-state lookup lemmas (filter/find?-based store)

The `NetworkState` store is `List ((Vat × Vat) × ChannelQueue)`. After
`set`, lookup at the just-set key returns the new value; lookup at any
other key is unchanged. -/

/-- Lookup at the just-set key returns the new value. -/
theorem networkState_get_set_eq
    (ns : OcapnLean.Netlayer.InProcess.NetworkState)
    (src dst : OcapnLean.Netlayer.Spec.Vat)
    (q : OcapnLean.Netlayer.InProcess.ChannelQueue) :
    (ns.set (src, dst) q).get (src, dst) = q := by
  unfold OcapnLean.Netlayer.InProcess.NetworkState.set
         OcapnLean.Netlayer.InProcess.NetworkState.get
  simp [List.find?_cons]

/-- Lookup at a different key is unchanged after a `set`. -/
theorem networkState_get_set_ne
    (ns : OcapnLean.Netlayer.InProcess.NetworkState)
    (src dst : OcapnLean.Netlayer.Spec.Vat)
    (q : OcapnLean.Netlayer.InProcess.ChannelQueue)
    (src' dst' : OcapnLean.Netlayer.Spec.Vat)
    (h : (src', dst') ≠ (src, dst)) :
    (ns.set (src, dst) q).get (src', dst') = ns.get (src', dst') := by
  unfold OcapnLean.Netlayer.InProcess.NetworkState.set
         OcapnLean.Netlayer.InProcess.NetworkState.get
  -- After set: (src, dst, q) :: filter (·.1 ≠ (src, dst)) ns.channels.
  -- find? skips the head (key mismatch), reduces filter+find? via
  -- the find?_filter simp rule. We're left showing two `find?`s with
  -- equivalent predicates produce equal results.
  simp only [List.find?_cons]
  have hne : ¬ ((src, dst) = (src', dst')) := fun heq => h heq.symm
  simp [hne]
  -- Predicate equivalence: a.1 ≠ k ∧ a.1 = k' equivalent to a.1 = k'
  -- (under k' ≠ k).
  have hpred :
      (fun a : OcapnLean.Netlayer.InProcess.ChanKey ×
               OcapnLean.Netlayer.InProcess.ChannelQueue =>
          !decide (a.fst = (src, dst)) && decide (a.fst = (src', dst'))) =
      (fun a => decide (a.fst = (src', dst'))) := by
    funext x
    by_cases hx : x.1 = (src', dst')
    · -- x.1 = (src', dst') ≠ (src, dst), so the first conjunct is True
      simp [hx, h]
    · simp [hx]
  rw [hpred]

/-! ## Per-op correspondence (send)

After a `sendOnState` op, the projection of the resulting
`NetworkState` equals applying the LTS `Action.send` step to the
projection of the pre-state — *at the just-modified channel*. We
prove the per-channel equality; the cross-channel equality (where
neither op changes the channel) requires `networkState_get_set_ne`,
which is mechanical list-reasoning about `filter`/`find?` (queued).
-/

/-- The (src, dst) channel projection commutes with `sendOnState` /
`Action.send` at the just-modified channel. -/
theorem project_sendOnState_at_modified_channel
    (ns : OcapnLean.Netlayer.InProcess.NetworkState)
    (src dst : OcapnLean.Netlayer.Spec.Vat) (msg : ByteArray) :
    (projectNetworkState (sendOnState ns src dst msg)).channels src dst =
    ((OcapnLean.Captp.RuntimeFifo.Action.send src dst msg).apply
      (projectNetworkState ns)).channels src dst := by
  -- LHS unfolds to: project of (ns.set (src, dst) q'.with-pushed-sent).get (src, dst)
  --              = project (q'.with-pushed-sent)
  -- RHS unfolds to: (RuntimeFifo.update (project ns) src dst {q with sent := ...}).channels src dst
  --              = q' (the pushed channel)
  -- These match.
  dsimp only [projectNetworkState, sendOnState, projectChannelQueue,
              OcapnLean.Captp.RuntimeFifo.Action.apply,
              OcapnLean.Captp.RuntimeFifo.update]
  simp [networkState_get_set_eq]

/-- The (src, dst) channel projection commutes with `recvOnState` /
`Action.recv` at the just-modified channel (when the channel is busy). -/
theorem project_recvOnState_at_modified_channel_busy
    (ns : OcapnLean.Netlayer.InProcess.NetworkState)
    (src dst : OcapnLean.Netlayer.Spec.Vat)
    (hbusy : (ns.get (src, dst)).received.size < (ns.get (src, dst)).sent.size) :
    (projectNetworkState (recvOnState ns src dst)).channels src dst =
    ((OcapnLean.Captp.RuntimeFifo.Action.recv src dst).apply
      (projectNetworkState ns)).channels src dst := by
  dsimp only [projectNetworkState, recvOnState, projectChannelQueue,
              OcapnLean.Captp.RuntimeFifo.Action.apply,
              OcapnLean.Captp.RuntimeFifo.update]
  simp [hbusy, networkState_get_set_eq]

/-! ## Cross-channel correspondence

The complementary case to `project_sendOnState_at_modified_channel`:
at a channel *other* than the just-modified one, the projection is
unchanged on both sides. -/

/-- Send at one channel doesn't affect the projection of another. -/
theorem project_sendOnState_at_other_channel
    (ns : OcapnLean.Netlayer.InProcess.NetworkState)
    (src dst : OcapnLean.Netlayer.Spec.Vat) (msg : ByteArray)
    (src' dst' : OcapnLean.Netlayer.Spec.Vat)
    (h : (src', dst') ≠ (src, dst)) :
    (projectNetworkState (sendOnState ns src dst msg)).channels src' dst' =
    ((OcapnLean.Captp.RuntimeFifo.Action.send src dst msg).apply
      (projectNetworkState ns)).channels src' dst' := by
  dsimp [projectNetworkState, sendOnState, projectChannelQueue,
         OcapnLean.Captp.RuntimeFifo.Action.apply,
         OcapnLean.Captp.RuntimeFifo.update]
  have heq : ¬ (src' = src ∧ dst' = dst) :=
    fun ⟨h1, h2⟩ => h (by rw [h1, h2])
  simp [heq]
  rw [networkState_get_set_ne ns src dst _ src' dst' h]
  exact ⟨rfl, rfl⟩

/-- Recv at one channel doesn't affect the projection of another. -/
theorem project_recvOnState_at_other_channel
    (ns : OcapnLean.Netlayer.InProcess.NetworkState)
    (src dst : OcapnLean.Netlayer.Spec.Vat)
    (src' dst' : OcapnLean.Netlayer.Spec.Vat)
    (h : (src', dst') ≠ (src, dst)) :
    (projectNetworkState (recvOnState ns src dst)).channels src' dst' =
    ((OcapnLean.Captp.RuntimeFifo.Action.recv src dst).apply
      (projectNetworkState ns)).channels src' dst' := by
  dsimp [projectNetworkState, recvOnState, projectChannelQueue,
         OcapnLean.Captp.RuntimeFifo.Action.apply,
         OcapnLean.Captp.RuntimeFifo.update]
  have heq : ¬ (src' = src ∧ dst' = dst) :=
    fun ⟨h1, h2⟩ => h (by rw [h1, h2])
  by_cases hbusy : (ns.get (src, dst)).received.size < (ns.get (src, dst)).sent.size
  · simp [hbusy, heq]
    rw [networkState_get_set_ne ns src dst _ src' dst' h]
    exact ⟨rfl, rfl⟩
  · simp [hbusy]

/-! ## Combined per-channel correspondence

The full per-channel correspondence: at *any* channel, the projection
commutes with sendOnState / recvOnState. -/

/-- For any `(src', dst')`, send correspondence holds (either same
channel via `*_at_modified_channel` or different via `*_at_other_channel`). -/
theorem project_sendOnState_channels
    (ns : OcapnLean.Netlayer.InProcess.NetworkState)
    (src dst : OcapnLean.Netlayer.Spec.Vat) (msg : ByteArray)
    (src' dst' : OcapnLean.Netlayer.Spec.Vat) :
    (projectNetworkState (sendOnState ns src dst msg)).channels src' dst' =
    ((OcapnLean.Captp.RuntimeFifo.Action.send src dst msg).apply
      (projectNetworkState ns)).channels src' dst' := by
  by_cases heq : (src', dst') = (src, dst)
  · have h1 : src' = src := (Prod.mk.inj heq).1
    have h2 : dst' = dst := (Prod.mk.inj heq).2
    subst src'; subst dst'
    exact project_sendOnState_at_modified_channel ns src dst msg
  · exact project_sendOnState_at_other_channel ns src dst msg src' dst' heq

/-- For any `(src', dst')`, recv correspondence holds. -/
theorem project_recvOnState_channels
    (ns : OcapnLean.Netlayer.InProcess.NetworkState)
    (src dst : OcapnLean.Netlayer.Spec.Vat)
    (src' dst' : OcapnLean.Netlayer.Spec.Vat) :
    (projectNetworkState (recvOnState ns src dst)).channels src' dst' =
    ((OcapnLean.Captp.RuntimeFifo.Action.recv src dst).apply
      (projectNetworkState ns)).channels src' dst' := by
  by_cases heq : (src', dst') = (src, dst)
  · have h1 : src' = src := (Prod.mk.inj heq).1
    have h2 : dst' = dst := (Prod.mk.inj heq).2
    subst src'; subst dst'
    by_cases hbusy : (ns.get (src, dst)).received.size < (ns.get (src, dst)).sent.size
    · exact project_recvOnState_at_modified_channel_busy ns src dst hbusy
    · -- not busy: state unchanged on both sides
      dsimp [projectNetworkState, recvOnState, projectChannelQueue,
             OcapnLean.Captp.RuntimeFifo.Action.apply,
             OcapnLean.Captp.RuntimeFifo.update]
      simp [hbusy]
  · exact project_recvOnState_at_other_channel ns src dst src' dst' heq

/-! ## Full structure equality

Combining the per-channel theorems with the trivial routesTo/targetRef
equality (both projections produce the same default constant
functions; the LTS actions don't touch them) gives the full
`RuntimeState` equality. -/

/-- **Full send correspondence (structure equality).** -/
theorem project_sendOnState
    (ns : OcapnLean.Netlayer.InProcess.NetworkState)
    (src dst : OcapnLean.Netlayer.Spec.Vat) (msg : ByteArray) :
    projectNetworkState (sendOnState ns src dst msg) =
      (OcapnLean.Captp.RuntimeFifo.Action.send src dst msg).apply
        (projectNetworkState ns) := by
  apply OcapnLean.Captp.RuntimeFifo.RuntimeState.ext
  · funext src' dst'
    exact project_sendOnState_channels ns src dst msg src' dst'
  · rfl  -- routesTo
  · rfl  -- targetRef
  · rfl  -- isPromise
  · rfl  -- resolvedTo
  · rfl  -- forwardedAt

/-- **Full recv correspondence (structure equality).** -/
theorem project_recvOnState
    (ns : OcapnLean.Netlayer.InProcess.NetworkState)
    (src dst : OcapnLean.Netlayer.Spec.Vat) :
    projectNetworkState (recvOnState ns src dst) =
      (OcapnLean.Captp.RuntimeFifo.Action.recv src dst).apply
        (projectNetworkState ns) := by
  apply OcapnLean.Captp.RuntimeFifo.RuntimeState.ext
  · funext src' dst'
    exact project_recvOnState_channels ns src dst src' dst'
  all_goals (
    dsimp only [projectNetworkState, recvOnState,
                OcapnLean.Captp.RuntimeFifo.Action.apply,
                OcapnLean.Captp.RuntimeFifo.update]
    split <;> rfl)

/-! ## Trace-level lifting

Lift the per-op correspondence to sequences of operations:
running a list of network ops then projecting equals projecting then
running the corresponding LTS actions. -/

/-- A network-side operation: send or recv. -/
inductive NetworkOp
  | send (src dst : OcapnLean.Netlayer.Spec.Vat) (msg : ByteArray)
  | recv (src dst : OcapnLean.Netlayer.Spec.Vat)

def NetworkOp.apply
    (ns : OcapnLean.Netlayer.InProcess.NetworkState) : NetworkOp →
    OcapnLean.Netlayer.InProcess.NetworkState
  | .send src dst msg => sendOnState ns src dst msg
  | .recv src dst     => recvOnState ns src dst

/-- Translate a network op to the corresponding LTS action. -/
def NetworkOp.toAction : NetworkOp → OcapnLean.Captp.RuntimeFifo.Action
  | .send src dst msg => .send src dst msg
  | .recv src dst     => .recv src dst

/-- Per-op correspondence (unified for send and recv). -/
theorem project_op_correspondence
    (ns : OcapnLean.Netlayer.InProcess.NetworkState) (op : NetworkOp) :
    projectNetworkState (op.apply ns) =
      op.toAction.apply (projectNetworkState ns) := by
  cases op with
  | send src dst msg => exact project_sendOnState ns src dst msg
  | recv src dst     => exact project_recvOnState ns src dst

/-- Run a sequence of network ops. -/
def runNetworkOps
    (ns : OcapnLean.Netlayer.InProcess.NetworkState) (ops : List NetworkOp) :
    OcapnLean.Netlayer.InProcess.NetworkState :=
  ops.foldl (fun ns op => op.apply ns) ns

/-- **Trace-level lifting.** Running a sequence of network ops then
projecting equals projecting then running the corresponding LTS
actions. -/
theorem project_runNetworkOps
    (ns : OcapnLean.Netlayer.InProcess.NetworkState) (ops : List NetworkOp) :
    projectNetworkState (runNetworkOps ns ops) =
      OcapnLean.Captp.RuntimeFifo.runActions
        (projectNetworkState ns) (ops.map NetworkOp.toAction) := by
  induction ops generalizing ns with
  | nil => rfl
  | cons op ops ih =>
    show projectNetworkState (runNetworkOps (op.apply ns) ops) =
         OcapnLean.Captp.RuntimeFifo.runActions
           (projectNetworkState ns) (op.toAction :: ops.map NetworkOp.toAction)
    rw [ih (op.apply ns)]
    rw [project_op_correspondence ns op]
    rfl

/-- The empty network state projects to `RuntimeFifo.initial`. -/
theorem projectNetworkState_empty :
    projectNetworkState (default : OcapnLean.Netlayer.InProcess.NetworkState) =
      OcapnLean.Captp.RuntimeFifo.initial := by
  apply OcapnLean.Captp.RuntimeFifo.RuntimeState.ext
  · funext src dst
    -- Default NetworkState has empty channels list; ns.get returns default.
    -- projectChannelQueue default = empty queue.
    rfl
  all_goals rfl

/-- **Headline:** any in-process `NetworkState` reachable via a
sequence of network ops from the empty initial state projects to a
`Reachable` `RuntimeFifo.RuntimeState`. Therefore it satisfies
`InvDeliverIsPrefix` — the runtime per-channel prefix invariant. -/
theorem network_state_reachable_via_ops_satisfies_prefix
    (ops : List NetworkOp) :
    OcapnLean.Captp.RuntimeFifo.InvDeliverIsPrefix
      (projectNetworkState (runNetworkOps default ops)) := by
  -- The projection is reachable from RuntimeFifo.initial via the
  -- corresponding LTS actions.
  have hreach : OcapnLean.Captp.RuntimeFifo.Reachable
                  (projectNetworkState (runNetworkOps default ops)) := by
    refine ⟨ops.map NetworkOp.toAction, ?_⟩
    rw [← projectNetworkState_empty]
    exact (project_runNetworkOps default ops).symm
  exact OcapnLean.Captp.RuntimeFifo.InvDeliverIsPrefix.reachable _ hreach

end OcapnLean.Captp.RuntimeFifoBridge
