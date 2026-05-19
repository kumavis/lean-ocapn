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
  simp

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

/-! ## Gap D: per-channel `<+: ` claim (List.IsPrefix on arrays' toList)

From `InvDeliverIsPrefix` (size bound + indexed equality on Array
`sent` / `received`), derive that `received.toList` is a prefix of
`sent.toList` (in the `List.IsPrefix` sense, i.e., `<+:`). This is
the bridge from index-based reasoning to list-based prefix reasoning,
which the `Netlayer.Spec.Valid` contract uses via `List.isPrefixOf`.
-/

/-- Pure-Lean lemma: given arrays where `received.size ≤ sent.size`
and per-index equality holds, `received.toList` is a prefix of
`sent.toList`. -/
theorem array_received_prefix_of_sent
    (received sent : Array ByteArray)
    (hsz : received.size ≤ sent.size)
    (helt : ∀ j, j < received.size → received[j]? = sent[j]?) :
    received.toList <+: sent.toList := by
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem?
  intro i
  by_cases hi : i < received.size
  · -- i < received.size: both sides reduce to sent[i]?
    have hi' : i < received.toList.length := by
      simpa [Array.length_toList] using hi
    rw [List.getElem?_take_of_lt hi']
    simp only [Array.getElem?_toList]
    exact helt i hi
  · -- i ≥ received.size: both sides are none
    have hge : received.size ≤ i := Nat.le_of_not_lt hi
    have hlhs : received.toList[i]? = none := by
      simp only [Array.getElem?_toList]
      exact Array.getElem?_eq_none hge
    have hrhs : (sent.toList.take received.toList.length)[i]? = none := by
      apply List.getElem?_eq_none
      rw [List.length_take]
      simp [Array.length_toList]
      omega
    rw [hlhs, hrhs]

/-- **Per-channel snapshot prefix** (the substance of Gap D). At any
state reachable via `runNetworkOps` from the empty initial state, on
every channel `(src, dst)`, the `received` array's `toList` is a
prefix of the `sent` array's `toList`. -/
theorem network_snapshot_per_channel_prefix
    (ops : List NetworkOp)
    (src dst : OcapnLean.Netlayer.Spec.Vat) :
    ((runNetworkOps default ops).get (src, dst)).received.toList <+:
    ((runNetworkOps default ops).get (src, dst)).sent.toList := by
  have hinv := network_state_reachable_via_ops_satisfies_prefix ops
  have ⟨hsz, helt⟩ := hinv src dst
  -- (projectNetworkState ns).channels src dst = projectChannelQueue (ns.get (src, dst))
  -- projectChannelQueue preserves .sent and .received.
  exact array_received_prefix_of_sent _ _ hsz helt

/-! ## Pure-state mirror of `Network.snapshot`

`Network.snapshot` reads the IO.Ref and emits sent events first
(across all channels in channel-list order), then received events.
Here's the pure-state version operating directly on `NetworkState`. -/

/-- The pure analogue of `Network.snapshot` — emit all sent events
first, then all received events. Within a channel, order is preserved
(array order). -/
def NetworkState.toTrace
    (ns : OcapnLean.Netlayer.InProcess.NetworkState) :
    OcapnLean.Netlayer.Spec.Trace :=
  let sentEvts :=
    ns.channels.flatMap (fun (kv : OcapnLean.Netlayer.InProcess.ChanKey ×
                                  OcapnLean.Netlayer.InProcess.ChannelQueue) =>
      kv.2.sent.toList.map (OcapnLean.Netlayer.Spec.Event.sent kv.1.1 kv.1.2))
  let recvEvts :=
    ns.channels.flatMap (fun (kv : OcapnLean.Netlayer.InProcess.ChanKey ×
                                  OcapnLean.Netlayer.InProcess.ChannelQueue) =>
      kv.2.received.toList.map (OcapnLean.Netlayer.Spec.Event.received kv.1.1 kv.1.2))
  sentEvts ++ recvEvts

/-! ## Well-formedness: channel-list keys are pairwise distinct

`NetworkState.set` filters the existing list to remove the target key
before prepending the new entry, so the channel list never has two
entries with the same key. The default state has an empty list,
trivially well-formed. -/

/-- A `NetworkState` is well-formed if its `channels` list has
pairwise-distinct keys. Preserved by `set`; vacuously true at `default`. -/
def NetworkState.WF (ns : OcapnLean.Netlayer.InProcess.NetworkState) : Prop :=
  ns.channels.Pairwise (fun a b => a.1 ≠ b.1)

theorem NetworkState.default_wf :
    NetworkState.WF (default : OcapnLean.Netlayer.InProcess.NetworkState) := by
  show List.Pairwise _ ([] : List _)
  exact List.Pairwise.nil

theorem NetworkState.set_preserves_wf
    (ns : OcapnLean.Netlayer.InProcess.NetworkState)
    (k : OcapnLean.Netlayer.InProcess.ChanKey)
    (q : OcapnLean.Netlayer.InProcess.ChannelQueue)
    (h : NetworkState.WF ns) :
    NetworkState.WF (ns.set k q) := by
  unfold NetworkState.WF OcapnLean.Netlayer.InProcess.NetworkState.set
  apply List.Pairwise.cons
  · intro a ha
    rw [List.mem_filter] at ha
    -- ha.2 : decide (a.1 ≠ k) = true  → a.1 ≠ k
    have ha2 : a.1 ≠ k := by simpa using ha.2
    -- goal: k ≠ a.1
    exact (Ne.symm ha2)
  · exact List.Pairwise.filter _ h

theorem NetworkState.sendOnState_preserves_wf
    (ns : OcapnLean.Netlayer.InProcess.NetworkState)
    (src dst : OcapnLean.Netlayer.Spec.Vat) (msg : ByteArray)
    (h : NetworkState.WF ns) :
    NetworkState.WF (sendOnState ns src dst msg) :=
  NetworkState.set_preserves_wf _ _ _ h

theorem NetworkState.recvOnState_preserves_wf
    (ns : OcapnLean.Netlayer.InProcess.NetworkState)
    (src dst : OcapnLean.Netlayer.Spec.Vat)
    (h : NetworkState.WF ns) :
    NetworkState.WF (recvOnState ns src dst) := by
  unfold recvOnState
  by_cases hbusy : (ns.get (src, dst)).received.size < (ns.get (src, dst)).sent.size
  · simp [hbusy]
    exact NetworkState.set_preserves_wf _ _ _ h
  · simp [hbusy]
    exact h

theorem NetworkState.runNetworkOps_preserves_wf
    (ns : OcapnLean.Netlayer.InProcess.NetworkState)
    (h : NetworkState.WF ns) (ops : List NetworkOp) :
    NetworkState.WF (runNetworkOps ns ops) := by
  induction ops generalizing ns with
  | nil => exact h
  | cons op rest ih =>
    show NetworkState.WF (runNetworkOps (op.apply ns) rest)
    apply ih
    cases op with
    | send src dst msg =>
      exact NetworkState.sendOnState_preserves_wf _ _ _ _ h
    | recv src dst =>
      exact NetworkState.recvOnState_preserves_wf _ _ _ h

theorem NetworkState.runNetworkOps_default_wf (ops : List NetworkOp) :
    NetworkState.WF (runNetworkOps default ops) :=
  NetworkState.runNetworkOps_preserves_wf _ NetworkState.default_wf ops

/-! ## Trace extraction: `sentOn` / `receivedOn` of `toTrace`

Given `WF ns`, the trace's `sentOn` and `receivedOn` filters extract
exactly the matching channel's `sent` / `received` array as a list.
Proof: each channel entry contributes either its full sent/received
list (if its key matches) or nothing; `WF` rules out two matching
entries, so the flatMap concatenation reduces to exactly one entry's
contribution (or `[]` when no key matches, in which case `ns.get`
returns the default empty queue). -/

/-- Filter a map of `Event.sent` over a list of msgs: keeps everything if
the (s, d) pair matches the filter, else nothing. -/
private theorem filterMap_sentOn_eventSent
    (xs : List ByteArray) (a b src dst : OcapnLean.Netlayer.Spec.Vat) :
    (xs.map (OcapnLean.Netlayer.Spec.Event.sent a b)).filterMap
      (OcapnLean.Netlayer.Spec.Event.asSentOn src dst)
    = if a = src ∧ b = dst then xs else [] := by
  rw [List.filterMap_map]
  have h_comp : OcapnLean.Netlayer.Spec.Event.asSentOn src dst ∘
                OcapnLean.Netlayer.Spec.Event.sent a b
              = fun msg => if a = src ∧ b = dst then some msg else none := by
    funext msg
    simp [Function.comp, OcapnLean.Netlayer.Spec.Event.asSentOn]
  rw [h_comp]
  by_cases h : a = src ∧ b = dst <;> simp [h]

/-- A map of `Event.received` events contributes nothing to a `sentOn` filter. -/
private theorem filterMap_sentOn_eventReceived
    (xs : List ByteArray) (a b src dst : OcapnLean.Netlayer.Spec.Vat) :
    (xs.map (OcapnLean.Netlayer.Spec.Event.received a b)).filterMap
      (OcapnLean.Netlayer.Spec.Event.asSentOn src dst)
    = [] := by
  rw [List.filterMap_map]
  have h_comp : OcapnLean.Netlayer.Spec.Event.asSentOn src dst ∘
                OcapnLean.Netlayer.Spec.Event.received a b
              = fun _ => none := by
    funext msg
    simp [Function.comp, OcapnLean.Netlayer.Spec.Event.asSentOn]
  rw [h_comp]
  simp

/-- A map of `Event.received` events filters correctly for `receivedOn`. -/
private theorem filterMap_receivedOn_eventReceived
    (xs : List ByteArray) (a b src dst : OcapnLean.Netlayer.Spec.Vat) :
    (xs.map (OcapnLean.Netlayer.Spec.Event.received a b)).filterMap
      (OcapnLean.Netlayer.Spec.Event.asReceivedOn src dst)
    = if a = src ∧ b = dst then xs else [] := by
  rw [List.filterMap_map]
  have h_comp : OcapnLean.Netlayer.Spec.Event.asReceivedOn src dst ∘
                OcapnLean.Netlayer.Spec.Event.received a b
              = fun msg => if a = src ∧ b = dst then some msg else none := by
    funext msg
    simp [Function.comp, OcapnLean.Netlayer.Spec.Event.asReceivedOn]
  rw [h_comp]
  by_cases h : a = src ∧ b = dst <;> simp [h]

/-- A map of `Event.sent` events contributes nothing to a `receivedOn` filter. -/
private theorem filterMap_receivedOn_eventSent
    (xs : List ByteArray) (a b src dst : OcapnLean.Netlayer.Spec.Vat) :
    (xs.map (OcapnLean.Netlayer.Spec.Event.sent a b)).filterMap
      (OcapnLean.Netlayer.Spec.Event.asReceivedOn src dst)
    = [] := by
  rw [List.filterMap_map]
  have h_comp : OcapnLean.Netlayer.Spec.Event.asReceivedOn src dst ∘
                OcapnLean.Netlayer.Spec.Event.sent a b
              = fun _ => none := by
    funext msg
    simp [Function.comp, OcapnLean.Netlayer.Spec.Event.asReceivedOn]
  rw [h_comp]
  simp

/-- Under WF, `sentOn` of the flatMap of sent-events extracts the matching
channel's `sent.toList`. -/
private theorem flatMap_sentEvts_sentOn
    (l : List (OcapnLean.Netlayer.InProcess.ChanKey ×
               OcapnLean.Netlayer.InProcess.ChannelQueue))
    (hpw : l.Pairwise (fun a b => a.1 ≠ b.1))
    (src dst : OcapnLean.Netlayer.Spec.Vat) :
    (l.flatMap (fun kv => kv.2.sent.toList.map
        (OcapnLean.Netlayer.Spec.Event.sent kv.1.1 kv.1.2))).filterMap
      (OcapnLean.Netlayer.Spec.Event.asSentOn src dst)
    = (match l.find? (·.1 = (src, dst)) with
       | some kv => kv.2.sent.toList
       | none    => []) := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    obtain ⟨head_dist, tail_pw⟩ := List.pairwise_cons.mp hpw
    have ihtail := ih tail_pw
    simp only [List.flatMap_cons, List.filterMap_append]
    rw [filterMap_sentOn_eventSent]
    rw [ihtail]
    by_cases hk : head.1 = (src, dst)
    · simp [hk]
      have hfind : tail.find? (·.1 = (src, dst)) = none := by
        apply List.find?_eq_none.mpr
        intro b hb hbeq
        have hne : head.1 ≠ b.1 := head_dist b hb
        apply hne
        have hb_eq : b.1 = (src, dst) := by simpa using hbeq
        rw [hk, hb_eq]
      rw [hfind]
    · have hknot : ¬ (head.1.1 = src ∧ head.1.2 = dst) := by
        intro ⟨h1, h2⟩
        exact hk (Prod.ext h1 h2)
      simp [hknot, hk]

/-- Symmetric form for `receivedOn`. -/
private theorem flatMap_recvEvts_receivedOn
    (l : List (OcapnLean.Netlayer.InProcess.ChanKey ×
               OcapnLean.Netlayer.InProcess.ChannelQueue))
    (hpw : l.Pairwise (fun a b => a.1 ≠ b.1))
    (src dst : OcapnLean.Netlayer.Spec.Vat) :
    (l.flatMap (fun kv => kv.2.received.toList.map
        (OcapnLean.Netlayer.Spec.Event.received kv.1.1 kv.1.2))).filterMap
      (OcapnLean.Netlayer.Spec.Event.asReceivedOn src dst)
    = (match l.find? (·.1 = (src, dst)) with
       | some kv => kv.2.received.toList
       | none    => []) := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    obtain ⟨head_dist, tail_pw⟩ := List.pairwise_cons.mp hpw
    have ihtail := ih tail_pw
    simp only [List.flatMap_cons, List.filterMap_append]
    rw [filterMap_receivedOn_eventReceived]
    rw [ihtail]
    by_cases hk : head.1 = (src, dst)
    · simp [hk]
      have hfind : tail.find? (·.1 = (src, dst)) = none := by
        apply List.find?_eq_none.mpr
        intro b hb hbeq
        have hne : head.1 ≠ b.1 := head_dist b hb
        apply hne
        have hb_eq : b.1 = (src, dst) := by simpa using hbeq
        rw [hk, hb_eq]
      rw [hfind]
    · have hknot : ¬ (head.1.1 = src ∧ head.1.2 = dst) := by
        intro ⟨h1, h2⟩
        exact hk (Prod.ext h1 h2)
      simp [hknot, hk]

/-- Helper: the flatMap of received-events under a `sentOn` filter reduces to []. -/
private theorem flatMap_recvEvts_sentOn_eq_nil
    (l : List (OcapnLean.Netlayer.InProcess.ChanKey ×
               OcapnLean.Netlayer.InProcess.ChannelQueue))
    (src dst : OcapnLean.Netlayer.Spec.Vat) :
    (l.flatMap (fun kv => kv.2.received.toList.map
        (OcapnLean.Netlayer.Spec.Event.received kv.1.1 kv.1.2))).filterMap
      (OcapnLean.Netlayer.Spec.Event.asSentOn src dst)
    = [] := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp only [List.flatMap_cons, List.filterMap_append, ih,
               filterMap_sentOn_eventReceived, List.append_nil]

/-- Helper: the flatMap of sent-events under a `receivedOn` filter reduces to []. -/
private theorem flatMap_sentEvts_receivedOn_eq_nil
    (l : List (OcapnLean.Netlayer.InProcess.ChanKey ×
               OcapnLean.Netlayer.InProcess.ChannelQueue))
    (src dst : OcapnLean.Netlayer.Spec.Vat) :
    (l.flatMap (fun kv => kv.2.sent.toList.map
        (OcapnLean.Netlayer.Spec.Event.sent kv.1.1 kv.1.2))).filterMap
      (OcapnLean.Netlayer.Spec.Event.asReceivedOn src dst)
    = [] := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp only [List.flatMap_cons, List.filterMap_append, ih,
               filterMap_receivedOn_eventSent, List.append_nil]

/-- The `sentOn` projection of `toTrace` reduces to the channel queue's
`sent.toList`. -/
theorem toTrace_sentOn_of_wf
    (ns : OcapnLean.Netlayer.InProcess.NetworkState)
    (h : NetworkState.WF ns)
    (src dst : OcapnLean.Netlayer.Spec.Vat) :
    (NetworkState.toTrace ns).sentOn src dst = (ns.get (src, dst)).sent.toList := by
  unfold NetworkState.toTrace OcapnLean.Netlayer.Spec.Trace.sentOn
  rw [List.filterMap_append]
  rw [flatMap_recvEvts_sentOn_eq_nil, List.append_nil]
  rw [flatMap_sentEvts_sentOn _ h src dst]
  unfold OcapnLean.Netlayer.InProcess.NetworkState.get
  cases hf : ns.channels.find? (·.1 = (src, dst)) with
  | none => rfl
  | some kv => rfl

/-- The `receivedOn` projection of `toTrace` reduces to the channel queue's
`received.toList`. -/
theorem toTrace_receivedOn_of_wf
    (ns : OcapnLean.Netlayer.InProcess.NetworkState)
    (h : NetworkState.WF ns)
    (src dst : OcapnLean.Netlayer.Spec.Vat) :
    (NetworkState.toTrace ns).receivedOn src dst = (ns.get (src, dst)).received.toList := by
  unfold NetworkState.toTrace OcapnLean.Netlayer.Spec.Trace.receivedOn
  rw [List.filterMap_append]
  rw [flatMap_sentEvts_receivedOn_eq_nil, List.nil_append]
  rw [flatMap_recvEvts_receivedOn _ h src dst]
  unfold OcapnLean.Netlayer.InProcess.NetworkState.get
  cases hf : ns.channels.find? (·.1 = (src, dst)) with
  | none => rfl
  | some kv => rfl

/-! ## Headline: snapshot of a reachable in-process network is `Spec.Valid` -/

/-- **The full Gap D claim.** Any in-process `NetworkState` reachable
from the empty initial state via a sequence of `NetworkOp`s produces a
`toTrace` that satisfies the abstract netlayer contract `Spec.Valid` —
per-channel FIFO + no-loss + no-spontaneous, all wrapped in the
`received <+: sent` prefix relation per channel. -/
theorem network_snapshot_valid (ops : List NetworkOp) :
    OcapnLean.Netlayer.Spec.Valid
      (NetworkState.toTrace (runNetworkOps default ops)) := by
  refine ⟨?_⟩
  intro src dst
  have hwf := NetworkState.runNetworkOps_default_wf ops
  rw [toTrace_sentOn_of_wf _ hwf src dst]
  rw [toTrace_receivedOn_of_wf _ hwf src dst]
  exact network_snapshot_per_channel_prefix ops src dst

end OcapnLean.Captp.RuntimeFifoBridge
