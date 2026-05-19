import Veil

set_option linter.dupNamespace false

/-!
# CapTP end-to-end reference FIFO — M11 Phase A

Upgrades the per-channel **fail-stop FIFO** of `OcapnLean.Captp.Channels`
to **end-to-end reference FIFO** in Mark Miller's *Robust Composition*
§19 sense, under the *immutable-routing* regime (handoff adds new
routing entries; promise shortening — which mutates routing — is the
Phase B / C extension).

## Vocabulary (Miller §19)

Two-stage lifecycle:

* **send** — a sender vat S enqueues a message on the wire. Recorded
  by `sentAt S D M K` (S→D channel, message M assigned send-index K).
  Origin is also flagged in `sentBy S M`.
* **delivery** — the destination vat D receives M off the wire. Recorded
  by `delivered S D M` and `deliveredAt S D M J` (delivery-index J).

(Miller does not separate "receive" from "invoke" — for a single-
threaded vat run-to-completion, the queue is FIFO and the two coincide.
This model conflates them into the single `delivered` event.)

## What this module proves

Two safety properties, mechanically discharged across all actions:

* **`e2e_fifo`** — fail-stop FIFO (per (src, dst) channel). Carried
  from `Channels.lean`, re-stated against the augmented state.
* **`ref_fifo`** — **end-to-end reference FIFO**. For any sender S
  and reference R, if S sends `m₁` then `m₂` both targeting R, and both
  are delivered, then `m₁` is delivered before `m₂` — across **any**
  channel routing they end up on. (Under Phase A's immutable routing,
  same-sender + same-ref implies same-channel by `routesTo_functional`,
  so this reduces to `e2e_fifo`. Phase B will mutate routing and break
  this reduction; Phase C will restore it via `op:flush`-style
  precondition.)

## Design discipline for Phase B / C drop-in

The `routesTo : vat → ref → vat → Prop` state is modeled as a
**mutable** relation from the start. Phase A's `handoff` action only
**adds** entries (and only when no conflicting entry already exists);
the `routesTo_functional` invariant is stated as a one-step constraint
across **any** assignment shape, not as an immutability invariant that
Phase B would need to weaken.

Likewise, `sentBy S M` tracks origin **independently** of the channel
the msg ends up on. This survives a Phase C `shorten` that re-routes
post-shortening msgs without changing the sender.

## Headline statement (Miller-style)

> For any sender vat S and reference R, if S sent `m₁` then `m₂` both
> targeting R, and both messages were delivered, then the delivery of
> `m₁` happened before the delivery of `m₂` at R's host vat.
-/

veil module CaptpRefFifo

------------------------------------------------------------------------
-- Uninterpreted sorts
------------------------------------------------------------------------

type vat
type msg
type ref

------------------------------------------------------------------------
-- References and routing (M11 Phase A additions)
------------------------------------------------------------------------

-- Each msg has a (state-independent) target reference. Modeled as a
-- mutable function we never assign — Veil leaves the initial value
-- unconstrained per-run, giving us a fixed-but-arbitrary oracle.
function targetRef : msg → ref

-- Routing: V routes messages targeting R via the V→W channel.
-- Mutable from the start (Phase A only adds; Phase B will mutate).
relation routesTo : vat → ref → vat → Prop

-- Origin tracking. Survives Phase C re-routing because it doesn't
-- depend on the channel.
relation sentBy : vat → msg → Prop

------------------------------------------------------------------------
-- Per (src, dst) channel state (carried from Channels.lean)
------------------------------------------------------------------------

function sendCursor : vat → vat → Nat
function recvCursor : vat → vat → Nat

relation pending   : vat → vat → msg → Prop
relation delivered : vat → vat → msg → Prop

relation sentAt      : vat → vat → msg → Nat → Prop
relation deliveredAt : vat → vat → msg → Nat → Prop

#gen_state

after_init {
  sendCursor S D := 0;
  recvCursor S D := 0;
  pending S D M := False;
  delivered S D M := False;
  sentAt S D M K := False;
  deliveredAt S D M K := False;
  routesTo V R W := False;
  sentBy S M := False
}

------------------------------------------------------------------------
-- Actions
------------------------------------------------------------------------

-- A vat installs an initial route for a reference it hosts or holds.
-- This is the "primitive" routing-table population that isn't routed
-- through a handoff (e.g. the bootstrap object at session start).
-- Idempotent: re-running for the same (v, rf, dst) is a no-op;
-- conflicting (v, rf, dst') is forbidden by precondition.
action setupRoute (v dst : vat) (rf : ref) = {
  require ∀ W, routesTo v rf W → W = dst
  routesTo v rf dst := True
}

-- A peer hands a fresh message to the CapTP layer for transmission.
-- The destination D is determined by the sender's routing table for
-- targetRef(m). The msg must be fresh (never sent on any channel,
-- never originated by any sender).
action send (s d : vat) (m : msg) = {
  require routesTo s (targetRef m) d
  require ¬ pending s d m
  require ¬ delivered s d m
  require ∀ S' D' K, ¬ sentAt S' D' m K       -- never sent anywhere
  require ∀ S', ¬ sentBy S' m                  -- never originated
  pending s d m := True
  sentAt s d m (sendCursor s d) := True
  sendCursor s d := (sendCursor s d) + 1
  sentBy s m := True
}

-- The destination peer delivers the FIFO head to its local target.
-- Per-channel FIFO is enforced by requiring the msg's send-index
-- to equal the current recv-cursor.
action deliver (s d : vat) (m : msg) = {
  require pending s d m
  require sentAt s d m (recvCursor s d)
  pending s d m := False
  delivered s d m := True
  deliveredAt s d m (recvCursor s d) := True
  recvCursor s d := (recvCursor s d) + 1
}

-- Handoff: gifter `g` introduces receiver `r` to reference `rf` (hosted
-- at exporter `e`). Additive — only fires when `r` doesn't already have
-- a conflicting route. Phase A's no-mutation discipline is captured
-- in the precondition (same-target idempotent; different-target
-- forbidden). Phase B's `shorten` will overwrite.
action handoff (g r e : vat) (rf : ref) = {
  require routesTo g rf e                     -- gifter knows the route
  require ∀ W, routesTo r rf W → W = e         -- idempotent / no conflict
  routesTo r rf e := True
}

------------------------------------------------------------------------
-- Safety properties
------------------------------------------------------------------------

-- Carried from Channels.lean. Per-(src, dst) channel FIFO ("fail-stop
-- FIFO" in Miller's taxonomy).
safety [e2e_fifo]
  delivered S D M1 ∧ delivered S D M2 ∧
  sentAt S D M1 K1 ∧ sentAt S D M2 K2 ∧
  deliveredAt S D M1 J1 ∧ deliveredAt S D M2 J2 ∧
  K1 < K2 →
  J1 < J2

-- M11 Phase A headline: end-to-end reference FIFO under immutable
-- routing. Per-sender, per-reference: two msgs from the same sender
-- targeting the same reference are delivered in send order.
safety [ref_fifo]
  sentBy S M1 ∧ sentBy S M2 ∧
  targetRef M1 = targetRef M2 ∧
  delivered S D1 M1 ∧ delivered S D2 M2 ∧
  sentAt S D1 M1 K1 ∧ sentAt S D2 M2 K2 ∧
  deliveredAt S D1 M1 J1 ∧ deliveredAt S D2 M2 J2 ∧
  K1 < K2 →
  J1 < J2

------------------------------------------------------------------------
-- Supporting invariants — channel layer (16 from Channels.lean)
------------------------------------------------------------------------

invariant [recv_le_send]
  recvCursor S D ≤ sendCursor S D

invariant [sentAt_functional]
  sentAt S D M K1 ∧ sentAt S D M K2 → K1 = K2

invariant [sentAt_injective]
  sentAt S D M1 K ∧ sentAt S D M2 K → M1 = M2

invariant [deliveredAt_functional]
  deliveredAt S D M K1 ∧ deliveredAt S D M K2 → K1 = K2

invariant [deliveredAt_injective]
  deliveredAt S D M1 J ∧ deliveredAt S D M2 J → M1 = M2

invariant [pending_has_send_index]
  pending S D M → ∃ K, sentAt S D M K

invariant [delivered_has_send_index]
  delivered S D M → ∃ K, sentAt S D M K

invariant [delivered_has_deliver_index]
  delivered S D M → ∃ J, deliveredAt S D M J

invariant [deliveredAt_implies_delivered]
  deliveredAt S D M J → delivered S D M

invariant [pending_delivered_disjoint]
  pending S D M ∧ delivered S D M → False

invariant [sentAt_below_cursor]
  sentAt S D M K → K < sendCursor S D

invariant [deliveredAt_below_cursor]
  deliveredAt S D M J → J < recvCursor S D

invariant [pending_at_or_above_recv]
  pending S D M ∧ sentAt S D M K → recvCursor S D ≤ K

invariant [delivered_below_recv_cursor]
  delivered S D M ∧ sentAt S D M K → K < recvCursor S D

invariant [deliver_eq_send]
  delivered S D M ∧ sentAt S D M K ∧ deliveredAt S D M J → K = J

------------------------------------------------------------------------
-- Supporting invariants — refs / routing layer (M11 Phase A additions)
------------------------------------------------------------------------

-- `routesTo` is functional in (V, R): each vat routes each ref to at
-- most one destination. **Load-bearing for `ref_fifo`** — combined
-- with `sentAt_via_route`, this is what guarantees same-sender +
-- same-ref ⇒ same-channel under Phase A's no-mutation regime.
invariant [routesTo_functional]
  routesTo V R W1 ∧ routesTo V R W2 → W1 = W2

-- A msg that has been originated by some sender has appeared on the
-- wire at that sender's outbound side.
invariant [sentBy_has_sent_at]
  sentBy S M → ∃ D K, sentAt S D M K

-- Conversely, every wire-level send has an origin record. (The send
-- action establishes both jointly.)
invariant [sentAt_has_sentBy]
  sentAt S D M K → sentBy S M

-- A msg's wire-level channel matches the sender's routing for its
-- target ref. **The bridge from `e2e_fifo` to `ref_fifo`**: combined
-- with `routesTo_functional`, this gives same-sender + same-ref ⇒
-- same-channel (so per-channel FIFO from `e2e_fifo` carries over).
invariant [sentAt_via_route]
  sentAt S D M K → routesTo S (targetRef M) D

-- Origin is functional in M: a msg has at most one originator.
-- (Together with `sentBy_has_sent_at` and `sentAt_via_route`, this
-- pins down channel-of-send by sender alone.)
invariant [sentBy_functional]
  sentBy S1 M ∧ sentBy S2 M → S1 = S2

#gen_spec

#check_invariants

------------------------------------------------------------------------
-- Bounded model traces: 3-party handoff happy path
------------------------------------------------------------------------

/-! A canonical 3-party reference-passing scenario:

  1. Alice sets up a route to Carol for ref R (`setupRoute`).
  2. Alice sends m₁ targeting R (uses Alice→Carol channel).
  3. Alice hands R off to Bob (`handoff`, Bob now also routes R via Carol).
  4. Bob sends m₂ targeting R (uses Bob→Carol channel).
  5. Carol delivers m₁ (from Alice).
  6. Carol delivers m₂ (from Bob).

The final assert pins three distinct vats appearing in the trace, both
msgs targeting the same ref, and Carol delivering both. SMT finds
concrete vats/refs/msgs that satisfy the entire sequence — concrete
evidence that the spec admits this scenario.
-/
#guard_msgs(drop warning, drop info) in
sat trace [three_party_handoff_happy] {
  setupRoute
  send
  handoff
  send
  deliver
  deliver
  assert (∃ (a b c : vat) (m1 m2 : msg) (j1 j2 : Nat),
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    delivered a c m1 ∧ delivered b c m2 ∧
    sentBy a m1 ∧ sentBy b m2 ∧
    targetRef m1 = targetRef m2 ∧
    deliveredAt a c m1 j1 ∧ deliveredAt b c m2 j2)
} by { bmc_sat }

end CaptpRefFifo
