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

end OcapnLean.Captp.RuntimeFifoBridge
