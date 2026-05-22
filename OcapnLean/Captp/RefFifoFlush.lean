import Veil

set_option linter.dupNamespace false

/-!
# End-to-end ref FIFO restored by a flush precondition — M11 Phase C

Phase B (`RefFifoShortening`) and Phase B' (`RefFifoPromiseResolution`)
each mechanise a distinct path-change race that violates end-to-end
reference FIFO at the resolution host:

* **Phase B** — Alice's explicit `shorten` mutates her route mid-flight.
* **Phase B'** — Alice's `learnResolution` (the natural sender-side
  response to learning a promise resolved) mutates her route, even
  without an explicit shortening operation.

Both races have the same shape at the spec level: **Alice changes her
route for ref P from `oldT` to `newT` while she still has in-flight
msgs targeting P on the `oldT` route**. The msgs on the old wire
race the msgs on the new wire at the destination.

The OCapN issue-11 discussion proposes `op:flush` as the wire-level
mechanism that prevents this race. Ridley's v3 (2026-04-29) is
Bob-initiated: when Bob is ready to shorten, he asks Alice to flush
her sends targeting P, Alice swaps her export-table entry and replies
"flush done", then Bob does a normal 3PH which leverages B↔C FIFO to
sequence the gift behind already-forwarded msgs.

But **v3's trigger is narrower than the race**: v3 fires on a
*Bob-initiated shortening event*. The Phase B' race (promise
resolution to a ref on a different vat → Alice updates her route
*without* an explicit shortening event) is not addressed by v3 as
currently proposed. cwebber's 2026-05-19 comments and kumavis's
2026-05-22 generalization on issue #11 make this explicit: "we
technically need op:flush even without promise shortening to get
e2e ref fifo (or e-order)."

## What this module commits

A **spec-level abstraction** of what any conforming flush protocol
must establish, applied to **both** path-change actions:

```veil
require ∀ M K,
  sentBy v M ∧ targetRef M = p ∧ sentAt v oldT M K ∧
  ¬ delivered v oldT M → False
```

i.e., at the moment Alice's route for P mutates from `oldT` to
`newT`, no Alice-originated msg targeting P is in flight on the
`v → oldT` channel. This is *exactly* the invariant that v3's
flush-done acknowledgement guarantees for the shortening case — but
applied uniformly to any path change.

The action is named `pathChangeWithFlush` to make the precondition's
role explicit; structurally it subsumes both Phase B's `shorten` and
Phase B's `learnResolution`. The wire-level protocol that establishes
the precondition (op:flush v3, sequence numbers, Cap'n Proto-style
embargo) is *decoupled* from the proof — any protocol that ensures
the precondition holds restores e2e FIFO at the spec level.

## What this gets us

* **End-to-end ref FIFO across path changes** as a discharged safety
  (the strengthened form using cross-channel cursors
  `originatedAt` / `receivedAtV`, which Phases B and B' exhibited as
  *failing* without the precondition).
* A clear statement of what the spec must guarantee, independent of
  which wire protocol delivers it.
* Foundation for a follow-up module that *mechanises v3 explicitly*
  and proves it establishes this precondition for the shortening case,
  surfacing the gap that v3 leaves open for the resolution case.

## Relationship to Phases B and B'

Phase B and B' are the *unguarded* shapes — what happens when the
spec permits route mutation without a flush gate. They exhibit the
race via `bmc_sat`. Phase C re-imposes the gate and recovers the
safety. The unguarded modules remain in the tree as regression
artifacts and as the upstream-discussion contribution.
-/

veil module CaptpRefFifoFlush

------------------------------------------------------------------------
-- Uninterpreted sorts
------------------------------------------------------------------------

type vat
type msg
type ref

------------------------------------------------------------------------
-- State (mirror of RefFifoForwarding + cross-channel cursors)
------------------------------------------------------------------------

function targetRef : msg → ref
relation routesTo : vat → ref → vat → Prop
relation sentBy : vat → msg → Prop

relation isPromise : ref → Prop
relation resolvedTo : ref → vat → Prop
relation forwardedAt : vat → vat → msg → Nat → Prop

function sendCursor : vat → vat → Nat
function recvCursor : vat → vat → Nat

relation pending   : vat → vat → msg → Prop
relation delivered : vat → vat → msg → Prop

relation sentAt      : vat → vat → msg → Nat → Prop
relation deliveredAt : vat → vat → msg → Nat → Prop

function originateCursor   : vat → Nat
function deliverArrCursor  : vat → Nat
relation originatedAt      : vat → msg → Nat → Prop
relation receivedAtV       : vat → msg → Nat → Prop

#gen_state

after_init {
  sendCursor S D := 0;
  recvCursor S D := 0;
  pending S D M := False;
  delivered S D M := False;
  sentAt S D M K := False;
  deliveredAt S D M K := False;
  routesTo V R W := False;
  sentBy S M := False;
  isPromise R := False;
  resolvedTo R W := False;
  forwardedAt B C M K := False;
  originateCursor S := 0;
  deliverArrCursor V := 0;
  originatedAt S M K := False;
  receivedAtV V M K := False
}

------------------------------------------------------------------------
-- Actions: unchanged from RefFifoForwarding
------------------------------------------------------------------------

action setupRoute (v dst : vat) (rf : ref) = {
  require ∀ W, routesTo v rf W → W = dst
  routesTo v rf dst := True
}

action declarePromise (p : ref) = {
  isPromise p := True
}

action resolvePromise (b c : vat) (p : ref) = {
  require isPromise p
  require ∀ W, ¬ resolvedTo p W
  require ∀ W, routesTo b p W → W = c
  resolvedTo p c := True
  routesTo b p c := True
}

action send (s d : vat) (m : msg) = {
  require routesTo s (targetRef m) d
  require ¬ pending s d m
  require ¬ delivered s d m
  require ∀ K, ¬ sentAt s d m K
  require ∀ S', ¬ sentBy S' m
  pending s d m := True
  sentAt s d m (sendCursor s d) := True
  sendCursor s d := (sendCursor s d) + 1
  sentBy s m := True
  originatedAt s m (originateCursor s) := True
  originateCursor s := (originateCursor s) + 1
}

action deliver (s d : vat) (m : msg) = {
  require pending s d m
  require sentAt s d m (recvCursor s d)
  pending s d m := False
  delivered s d m := True
  deliveredAt s d m (recvCursor s d) := True
  recvCursor s d := (recvCursor s d) + 1
  if ∀ R, ¬ receivedAtV d m R then
    receivedAtV d m (deliverArrCursor d) := True
    deliverArrCursor d := (deliverArrCursor d) + 1
}

action handoff (g r e : vat) (rf : ref) = {
  require routesTo g rf e
  require ∀ W, routesTo r rf W → W = e
  routesTo r rf e := True
}

action forward (b c : vat) (m : msg) = {
  require isPromise (targetRef m)
  require resolvedTo (targetRef m) c
  require routesTo b (targetRef m) c
  require ∃ s, delivered s b m
  require ¬ pending b c m
  require ¬ delivered b c m
  require ∀ K, ¬ sentAt b c m K
  require ∀ K, ¬ forwardedAt b c m K
  require ∀ s m' k' k_orig,
    sentBy s m ∧ sentBy s m' ∧
    targetRef m' = targetRef m ∧
    sentAt s b m k_orig ∧
    sentAt s b m' k' ∧ k' < k_orig ∧
    delivered s b m'
    → ∃ k, forwardedAt b c m' k
  pending b c m := True
  sentAt b c m (sendCursor b c) := True
  forwardedAt b c m (sendCursor b c) := True
  sendCursor b c := (sendCursor b c) + 1
}

------------------------------------------------------------------------
-- The Phase C action: route mutation gated by the flush precondition
------------------------------------------------------------------------

-- Generalizes Phase B's `shorten` and Phase B's `learnResolution`:
-- both are route mutations on the sender side, and both create the
-- same race when permitted without a flush. This action requires the
-- flush precondition — at the moment of mutation, no V-originated
-- msg targeting P is in flight on V→oldT — and is therefore safe.
--
-- The wire protocol that establishes the precondition is decoupled
-- from this spec-level guarantee. Op:flush v3 (Bob-initiated, with
-- export-table swap + flush-done rendezvous + 3PH FIFO sequencing)
-- is one realization; per-promise sequence numbers and Cap'n
-- Proto-style embargoes are others. Any protocol whose effect is
-- "V has no in-flight on V→oldT for P at mutation time" satisfies
-- the precondition.
action pathChangeWithFlush (v : vat) (p : ref) (oldT newT : vat) = {
  require isPromise p
  require resolvedTo p newT
  require routesTo v p oldT
  require oldT ≠ newT
  -- The flush precondition: every V-originated msg targeting P that
  -- was sent on the V→oldT channel has been delivered. No msg from V
  -- is still in flight on the old route for this ref.
  require ∀ M K,
    sentBy v M ∧ targetRef M = p ∧
    sentAt v oldT M K ∧ ¬ delivered v oldT M
    → False
  routesTo v p oldT := False
  routesTo v p newT := True
}

------------------------------------------------------------------------
-- Safety: the forwarder-only ref_fifo_e2e (carried from Phase A.5)
------------------------------------------------------------------------

safety [e2e_fifo]
  delivered S D M1 ∧ delivered S D M2 ∧
  sentAt S D M1 K1 ∧ sentAt S D M2 K2 ∧
  deliveredAt S D M1 J1 ∧ deliveredAt S D M2 J2 ∧
  K1 < K2 →
  J1 < J2

safety [ref_fifo]
  sentBy S M1 ∧ sentBy S M2 ∧
  targetRef M1 = targetRef M2 ∧
  delivered S D1 M1 ∧ delivered S D2 M2 ∧
  sentAt S D1 M1 K1 ∧ sentAt S D2 M2 K2 ∧
  deliveredAt S D1 M1 J1 ∧ deliveredAt S D2 M2 J2 ∧
  K1 < K2 →
  J1 < J2

safety [ref_fifo_e2e]
  sentBy S M1 ∧ sentBy S M2 ∧
  targetRef M1 = targetRef M2 ∧
  isPromise (targetRef M1) ∧
  resolvedTo (targetRef M1) C ∧
  sentAt S B M1 K1 ∧ sentAt S B M2 K2 ∧
  forwardedAt B C M1 KF1 ∧ forwardedAt B C M2 KF2 ∧
  delivered B C M1 ∧ delivered B C M2 ∧
  deliveredAt B C M1 N1 ∧ deliveredAt B C M2 N2 ∧
  K1 < K2 →
  N1 < N2

------------------------------------------------------------------------
-- Supporting invariants (carried from RefFifoForwarding)
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

invariant [routesTo_functional]
  routesTo V R W1 ∧ routesTo V R W2 → W1 = W2

invariant [sentBy_has_sent_at]
  sentBy S M → ∃ D K, sentAt S D M K

invariant [sentBy_functional]
  sentBy S1 M ∧ sentBy S2 M → S1 = S2

invariant [sentAt_originator_or_forwarded]
  sentAt S D M K → sentBy S M ∨ forwardedAt S D M K

invariant [sentAt_implies_originator]
  sentAt S D M K → ∃ S', sentBy S' M

invariant [forwardedAt_functional]
  forwardedAt B C M K1 ∧ forwardedAt B C M K2 → K1 = K2

invariant [forwardedAt_implies_sentAt]
  forwardedAt B C M K → sentAt B C M K

invariant [resolvedTo_functional]
  resolvedTo P V1 ∧ resolvedTo P V2 → V1 = V2

invariant [forwarded_targets_resolved]
  forwardedAt B C M K → isPromise (targetRef M) ∧ resolvedTo (targetRef M) C

invariant [forwarded_was_delivered_at_forwarder]
  forwardedAt B C M K → ∃ S, delivered S B M ∧ ∃ J, deliveredAt S B M J

invariant [forwarder_routes_to_resolution]
  forwardedAt B C M K → routesTo B (targetRef M) C

invariant [sent_implies_pending_or_delivered]
  sentAt S D M K → pending S D M ∨ delivered S D M

invariant [earlier_send_delivered_when_later_send_delivered]
  sentAt S D M1 K1 ∧ sentAt S D M2 K2 ∧ K1 < K2 ∧
  delivered S D M2 → delivered S D M1

invariant [earlier_send_forwarded_when_later_send_forwarded]
  sentBy S M1 ∧ sentBy S M2 ∧
  targetRef M1 = targetRef M2 ∧
  sentAt S B M1 J1 ∧ sentAt S B M2 J2 ∧ J1 < J2 ∧
  forwardedAt B C M2 K2 →
  ∃ K1, forwardedAt B C M1 K1

invariant [forward_preserves_send_order]
  sentBy S M1 ∧ sentBy S M2 ∧
  targetRef M1 = targetRef M2 ∧
  forwardedAt B C M1 K1 ∧ forwardedAt B C M2 K2 ∧
  sentAt S B M1 J1 ∧ sentAt S B M2 J2 ∧
  J1 < J2 → K1 < K2

-- Cross-channel cursor invariants
invariant [originatedAt_functional]
  originatedAt S M O1 ∧ originatedAt S M O2 → O1 = O2

invariant [originatedAt_injective]
  originatedAt S M1 O ∧ originatedAt S M2 O → M1 = M2

invariant [originatedAt_below_cursor]
  originatedAt S M O → O < originateCursor S

invariant [originatedAt_implies_sentBy]
  originatedAt S M O → sentBy S M

invariant [sentBy_implies_originatedAt]
  sentBy S M → ∃ O, originatedAt S M O

invariant [receivedAtV_functional]
  receivedAtV V M R1 ∧ receivedAtV V M R2 → R1 = R2

invariant [receivedAtV_injective]
  receivedAtV V M1 R ∧ receivedAtV V M2 R → M1 = M2

invariant [receivedAtV_below_cursor]
  receivedAtV V M R → R < deliverArrCursor V

invariant [receivedAtV_implies_delivered_somewhere]
  receivedAtV V M R → ∃ S, delivered S V M

invariant [delivered_implies_receivedAtV]
  delivered S V M → ∃ R, receivedAtV V M R

invariant [same_channel_send_matches_origination]
  sentAt S D M1 K1 ∧ sentAt S D M2 K2 ∧
  originatedAt S M1 O1 ∧ originatedAt S M2 O2 ∧
  K1 < K2 → O1 < O2

invariant [same_channel_origination_matches_send]
  sentAt S D M1 K1 ∧ sentAt S D M2 K2 ∧
  originatedAt S M1 O1 ∧ originatedAt S M2 O2 ∧
  O1 < O2 → K1 < K2

#gen_spec

#check_invariants

------------------------------------------------------------------------
-- Bounded model trace: the post-Phase B / B' restored happy path
------------------------------------------------------------------------

/-! ### Flushed path change works without breaking e2e FIFO.

Demonstrates the protocol in action. Alice sends m₁ on the old route,
m₁ is delivered (clearing the in-flight precondition), Alice then
mutates her route via `pathChangeWithFlush` and sends m₂ on the new
route. Both arrive at the resolution host in send-order. -/
set_option maxHeartbeats 1000000 in
#guard_msgs(drop warning, drop info) in
sat trace [flushed_path_change_preserves_order] {
  declarePromise
  setupRoute
  send                      -- A sends m₁ on A→B
  deliver                   -- B delivers m₁ (clearing in-flight on A→B)
  resolvePromise            -- B resolves P → C
  pathChangeWithFlush       -- A flushes + mutates route (precondition: no in-flight)
  send                      -- A sends m₂ on A→C
  deliver                   -- C delivers m₂
  forward                   -- B forwards m₁ to C
  deliver                   -- C delivers m₁
  assert (∃ (a b c : vat) (m1 m2 : msg),
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    sentBy a m1 ∧ sentBy a m2 ∧
    targetRef m1 = targetRef m2 ∧
    delivered b c m1 ∧
    delivered a c m2)
} by { bmc_sat }

end CaptpRefFifoFlush
