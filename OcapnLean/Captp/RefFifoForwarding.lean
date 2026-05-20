import Veil

set_option linter.dupNamespace false
-- Print counter-examples for any safety/invariant that fails inductively.
-- Helps diagnose CI failures without a local SMT-capable build.
set_option veil.printCounterexamples true
-- Bump from the 5s default — the strengthened ref_fifo_e2e chain
-- (cross-channel cursors + forwarding + per-channel FIFO) needs more
-- SMT budget to discharge.
set_option veil.smt.timeout 60

/-!
# CapTP end-to-end reference FIFO with forwarding — M11 Phase A.5

Closes the gap surfaced by Phase A's review. `RefFifo.lean` proves
per-(sender, ref) delivery order *at the sender's immediate routing
target* — but the canonical CapTP scenario is "A sends to promise P
on B, P resolves to obj on C, all of A's messages should arrive at C
in order." Phase A's model has neither promises nor forwarding, so it
doesn't actually cover this case.

This module adds:

* **Promises** as a kind of ref (`isPromise`, `resolvedTo`).
* A **`forward` action** that lets the promise-holder B re-emit a
  delivered msg onto its outbound channel toward the resolution host C.
* A **`forward_preserves_recv_order` invariant** — the novel proof
  obligation: B's forward-cursor order matches B's receive-cursor order
  for msgs from the same originator.
* A new safety **`ref_fifo_e2e`** — per-(sender, ref) delivery order
  at the **resolution host**, across the A→B→C forwarding chain.

The pre-existing `ref_fifo` (per-sender, per-ref, at the immediate
routing target) is carried unchanged — it still holds for A's
deliveries at B.

## Vocabulary

We use Miller's two-stage send → delivery lifecycle throughout.
"Forwarding" is what we call the act of B re-emitting onto a new wire
without itself originating a fresh message; the wire-level send still
goes through `sentAt`, but the originator (`sentBy`) is unchanged.

## Design notes — Phase B/C drop-in

* `forward`'s precondition is stated in terms of **state at B**
  (`deliveredAt`, `forwardedAt`) — not in terms of any wire protocol
  the impl uses to learn that state. Matches Phase A's discipline.

* `resolvedTo` and `routesTo` for the forwarder are set by
  `resolvePromise` as a single atomic event. Phase B's `shorten` will
  later mutate `routesTo` for the *sender*, bypassing the forwarding
  chain entirely.

## Model changes vs RefFifo.lean

* **`send`** — `∀ S' D' K, ¬ sentAt S' D' m K` (global freshness) is
  weakened to `∀ K, ¬ sentAt s d m K` (per-channel uniqueness). The
  same msg may now appear on multiple wires (A→B via `send`, B→C via
  `forward`). Origination freshness is still enforced by
  `∀ S', ¬ sentBy S' m`.
* **`sentAt_has_sentBy`** — split into `sentAt_originator_or_forwarded`:
  every `sentAt S D M K` is either an origination (`sentBy S M`) or
  a forwarding step (`forwardedAt S D M K`).
* **`sentAt_via_route`** still holds: each wire-level send (originated
  or forwarded) uses the sender's routing for the target ref. For
  forwarders, the route is installed by `resolvePromise`.
-/

veil module CaptpRefFifoForwarding

------------------------------------------------------------------------
-- Uninterpreted sorts
------------------------------------------------------------------------

type vat
type msg
type ref

------------------------------------------------------------------------
-- References, routing, origin (carried from RefFifo.lean)
------------------------------------------------------------------------

function targetRef : msg → ref
relation routesTo : vat → ref → vat → Prop
relation sentBy : vat → msg → Prop

------------------------------------------------------------------------
-- Promises and forwarding (Phase A.5 additions)
------------------------------------------------------------------------

relation isPromise : ref → Prop
relation resolvedTo : ref → vat → Prop
relation forwardedAt : vat → vat → msg → Nat → Prop

------------------------------------------------------------------------
-- Per (src, dst) channel state (carried from Channels.lean)
------------------------------------------------------------------------

function sendCursor : vat → vat → Nat
function recvCursor : vat → vat → Nat

relation pending   : vat → vat → msg → Prop
relation delivered : vat → vat → msg → Prop

relation sentAt      : vat → vat → msg → Nat → Prop
relation deliveredAt : vat → vat → msg → Nat → Prop

------------------------------------------------------------------------
-- Per-vat global origination + arrival counters (M11 Phase A.5 strong form)
------------------------------------------------------------------------
--
-- The per-channel cursors above can't compare ordering across channels:
-- if S sent M1 on S→B at cursor 0 and M2 on S→C at cursor 0, neither
-- "M1 sent first" nor "M2 sent first" is expressible in per-channel
-- terms. For `ref_fifo_e2e` to capture per-(sender, ref) order at the
-- resolution host across the A→B→C forwarding chain — and to break
-- meaningfully when Phase B's `shorten` lets m₂ bypass B via a fast
-- path — we need cross-channel ordering at each vat's boundary.
--
-- `originateCursor S` is S's global send count (incremented on every
-- `send`). `originatedAt S M K` records that S originated M as its
-- K-th send.
--
-- `deliverArrCursor V` is V's global arrival count (incremented on
-- every `deliver` where V is the destination). `receivedAtV V M K`
-- records that V received M as its K-th arrival from anywhere.
--
-- Together these let `ref_fifo_e2e` say: "msgs S originates targeting
-- a promise resolved to C arrive at C in S's origination order,
-- regardless of which intermediate vat each msg passed through."

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
-- Actions
------------------------------------------------------------------------

-- Install an initial route for a reference (e.g. the bootstrap object).
-- Idempotent / non-conflicting.
action setupRoute (v dst : vat) (rf : ref) = {
  require ∀ W, routesTo v rf W → W = dst
  routesTo v rf dst := True
}

-- Declare that a ref is a promise. (Promises and non-promises are
-- distinct; resolving requires `isPromise` to be set.)
action declarePromise (p : ref) = {
  isPromise p := True
}

-- The promise's holder B learns that p has resolved to a value hosted
-- at c. Sets `resolvedTo` and installs B's forwarding route. Resolves
-- at most once.
action resolvePromise (b c : vat) (p : ref) = {
  require isPromise p
  require ∀ W, ¬ resolvedTo p W                 -- not already resolved
  require ∀ W, routesTo b p W → W = c           -- B's route is idempotent
  resolvedTo p c := True
  routesTo b p c := True
}

-- Originate a send. Per-channel freshness (the same msg may later
-- appear on another wire via `forward`), but originator freshness is
-- still enforced.
action send (s d : vat) (m : msg) = {
  require routesTo s (targetRef m) d
  require ¬ pending s d m
  require ¬ delivered s d m
  require ∀ K, ¬ sentAt s d m K                 -- never on this wire
  require ∀ S', ¬ sentBy S' m                    -- never originated
  pending s d m := True
  sentAt s d m (sendCursor s d) := True
  sendCursor s d := (sendCursor s d) + 1
  sentBy s m := True
  -- Cross-channel send-order tracking at S.
  originatedAt s m (originateCursor s) := True
  originateCursor s := (originateCursor s) + 1
}

-- Receive a msg from the head of the channel.
--
-- A msg may arrive at the same vat multiple times via different source
-- channels (e.g., when multiple intermediaries route the same ref to
-- the same resolution host — both can forward). Real CapTP dedupes at
-- the receiver. We mirror that by only setting `receivedAtV` on the
-- FIRST arrival of M at D; subsequent arrivals are recorded only at
-- the per-channel `deliveredAt` level.
action deliver (s d : vat) (m : msg) = {
  require pending s d m
  require sentAt s d m (recvCursor s d)
  pending s d m := False
  delivered s d m := True
  deliveredAt s d m (recvCursor s d) := True
  recvCursor s d := (recvCursor s d) + 1
  -- First-arrival-only: set receivedAtV and bump deliverArrCursor only
  -- if M has never arrived at D before. This keeps receivedAtV
  -- functional in (V, M).
  if ∀ R, ¬ receivedAtV d m R then
    receivedAtV d m (deliverArrCursor d) := True
    deliverArrCursor d := (deliverArrCursor d) + 1
}

-- Handoff: additive routing extension (carried from RefFifo.lean).
action handoff (g r e : vat) (rf : ref) = {
  require routesTo g rf e
  require ∀ W, routesTo r rf W → W = e
  routesTo r rf e := True
}

-- Forward: B re-emits a previously delivered msg targeting a resolved
-- promise onto B→C wire. Preconditions enforce per-(originator, ref)
-- receive-order preservation: only fire when all earlier-received
-- same-originator same-target-ref msgs are already forwarded.
action forward (b c : vat) (m : msg) = {
  require isPromise (targetRef m)
  require resolvedTo (targetRef m) c
  require routesTo b (targetRef m) c
  require ∃ s, delivered s b m
  require ¬ pending b c m
  require ¬ delivered b c m
  require ∀ K, ¬ sentAt b c m K                 -- not yet on B→C
  require ∀ K, ¬ forwardedAt b c m K             -- not yet forwarded
  -- The novel constraint: forward in originator's send-order, per
  -- (originator, ref). For any msg m' from the same originator s as
  -- m, sent on s→b channel earlier than m, targeting the same
  -- promise, and already delivered at b: m' must already be forwarded
  -- before m can be forwarded. (Per-channel FIFO bridges send-order
  -- and receive-order at b, so this also captures receive-order.)
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
-- Safety properties
------------------------------------------------------------------------

-- Carried from Channels.lean / RefFifo.lean. Per-(src, dst) channel
-- FIFO ("fail-stop FIFO" in Miller's taxonomy).
safety [e2e_fifo]
  delivered S D M1 ∧ delivered S D M2 ∧
  sentAt S D M1 K1 ∧ sentAt S D M2 K2 ∧
  deliveredAt S D M1 J1 ∧ deliveredAt S D M2 J2 ∧
  K1 < K2 →
  J1 < J2

-- Carried from RefFifo.lean. Per-(sender, ref) delivery order at the
-- sender's IMMEDIATE routing target.
safety [ref_fifo]
  sentBy S M1 ∧ sentBy S M2 ∧
  targetRef M1 = targetRef M2 ∧
  delivered S D1 M1 ∧ delivered S D2 M2 ∧
  sentAt S D1 M1 K1 ∧ sentAt S D2 M2 K2 ∧
  deliveredAt S D1 M1 J1 ∧ deliveredAt S D2 M2 J2 ∧
  K1 < K2 →
  J1 < J2

-- M11 Phase A.5 headline. End-to-end per-(sender, ref) delivery order
-- AT THE RESOLUTION HOST — across the A→B→C forwarding chain. This is
-- the user-facing CapTP guarantee: A's messages targeting promise P
-- arrive at C in A's origination order, regardless of which path
-- (direct A→C, or A→B→C via forwarding) each msg actually traversed.
--
-- The hypothesis uses S's global origination order (`originatedAt`)
-- and C's global arrival order (`receivedAtV`) — NOT per-channel
-- cursors. Per-channel cursors are independent counters across
-- channels (the sentAt index on S→B and on S→C both start at 0), so
-- the older `sentAt S B M_i K_i` formulation could not compare msgs
-- that took different paths. Cross-channel cursors do.
--
-- Without shortening (this module), routes are immutable + functional
-- per (sender, ref), so all of S's msgs targeting P funnel through the
-- unique route to the next hop, then through B's per-receive-order
-- forward to C. Per-channel FIFO at each hop chains through.
--
-- Phase B adds a `shorten` action that mutates `routesTo`, letting
-- some of S's msgs take a fast path bypassing the forwarder. This
-- formulation breaks under that mutation — see
-- `RefFifoShortening.lean`'s `ref_fifo_e2e_strong_violated_by_shorten`
-- bmc_sat witness. Phase C will restore it via an `op:flush`
-- precondition.
safety [ref_fifo_e2e]
  sentBy S M1 ∧ sentBy S M2 ∧
  targetRef M1 = targetRef M2 ∧
  isPromise (targetRef M1) ∧
  resolvedTo (targetRef M1) C ∧
  originatedAt S M1 O1 ∧ originatedAt S M2 O2 ∧
  receivedAtV C M1 R1 ∧ receivedAtV C M2 R2 ∧
  O1 < O2 →
  R1 < R2

------------------------------------------------------------------------
-- Supporting invariants — channel layer (15 from Channels.lean)
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
-- Supporting invariants — refs / routing layer (carried from RefFifo)
------------------------------------------------------------------------

invariant [routesTo_functional]
  routesTo V R W1 ∧ routesTo V R W2 → W1 = W2

invariant [sentBy_has_sent_at]
  sentBy S M → ∃ D K, sentAt S D M K

invariant [sentAt_via_route]
  sentAt S D M K → routesTo S (targetRef M) D

invariant [sentBy_functional]
  sentBy S1 M ∧ sentBy S2 M → S1 = S2

-- Weakened from RefFifo.lean's `sentAt_has_sentBy`: every wire-level
-- send is either an origination (`sentBy`) or a forwarding step
-- (`forwardedAt`). For Phase A.5 these are the only two action shapes
-- that ever set `sentAt`.
invariant [sentAt_originator_or_forwarded]
  sentAt S D M K → sentBy S M ∨ forwardedAt S D M K

-- Every msg that has ever appeared on a wire has an originator. This
-- rules out spurious forwarding chains that never bottom out in an
-- origination — the counter-example loophole where forwarding can
-- "create" a msg out of nothing by chasing back through its own
-- forwarded delivery.
invariant [sentAt_implies_originator]
  sentAt S D M K → ∃ S', sentBy S' M

------------------------------------------------------------------------
-- Supporting invariants — forwarding layer (Phase A.5 additions)
------------------------------------------------------------------------

-- forwardedAt is functional in (B, C, M): a msg is forwarded onto
-- each (B, C) channel at most once.
invariant [forwardedAt_functional]
  forwardedAt B C M K1 ∧ forwardedAt B C M K2 → K1 = K2

-- Every forward is also a wire-level send on the same (B, C) channel
-- at the same cursor.
invariant [forwardedAt_implies_sentAt]
  forwardedAt B C M K → sentAt B C M K

-- Resolution is functional: a promise resolves to at most one host.
invariant [resolvedTo_functional]
  resolvedTo P V1 ∧ resolvedTo P V2 → V1 = V2

-- Any forwarded msg targets a promise that has resolved to the
-- forwarding destination.
invariant [forwarded_targets_resolved]
  forwardedAt B C M K → isPromise (targetRef M) ∧ resolvedTo (targetRef M) C

-- Any forwarded msg was previously delivered at the forwarder.
invariant [forwarded_was_delivered_at_forwarder]
  forwardedAt B C M K → ∃ S, delivered S B M ∧ ∃ J, deliveredAt S B M J

-- Forwarder's routing for the promise points to the resolution host.
invariant [forwarder_routes_to_resolution]
  forwardedAt B C M K → routesTo B (targetRef M) C

-- Every sent msg is either pending (in flight) or delivered. Combined
-- with the cursor invariants below, this lets SMT conclude that any
-- msg with sentAt K < recvCursor must be delivered.
invariant [sent_implies_pending_or_delivered]
  sentAt S D M K → pending S D M ∨ delivered S D M

-- Per-channel deliver-mechanism FIFO: if a later-sent msg is delivered,
-- the earlier-sent (same channel) msg is also delivered. (Follows from
-- the deliver action's `sentAt s d m (recvCursor s d)` precondition
-- combined with monotonic recvCursor + sent_implies_pending_or_delivered.)
invariant [earlier_send_delivered_when_later_send_delivered]
  sentAt S D M1 K1 ∧ sentAt S D M2 K2 ∧ K1 < K2 ∧
  delivered S D M2 → delivered S D M1

-- **The novel invariant — Part 1**: if a later-sent msg has been
-- forwarded, the earlier-sent (same originator, same ref) msg must
-- also have been forwarded. (Discharged by `forward`'s precondition
-- requiring earlier-delivered same-(S, ref) msgs to be already
-- forwarded; combined with the per-channel deliver invariant above,
-- this forces earlier-sent msgs to be forwarded before later-sent
-- can be.)
invariant [earlier_send_forwarded_when_later_send_forwarded]
  sentBy S M1 ∧ sentBy S M2 ∧
  targetRef M1 = targetRef M2 ∧
  sentAt S B M1 J1 ∧ sentAt S B M2 J2 ∧ J1 < J2 ∧
  forwardedAt B C M2 K2 →
  ∃ K1, forwardedAt B C M1 K1

-- **The novel invariant — Part 2**: forwarding preserves per-(originator,
-- ref) send order. For two msgs M1, M2 from the same originator S,
-- targeting the same ref, both sent on S→B by S, both forwarded
-- by B to C — the forward-cursor order at B→C matches the send-
-- cursor order at S→B. This is the bridge that lifts `ref_fifo`
-- (at B) to `ref_fifo_e2e` (at C); combined with per-channel FIFO
-- on S→B it also implies receive-order preservation at B.
invariant [forward_preserves_send_order]
  sentBy S M1 ∧ sentBy S M2 ∧
  targetRef M1 = targetRef M2 ∧
  forwardedAt B C M1 K1 ∧ forwardedAt B C M2 K2 ∧
  sentAt S B M1 J1 ∧ sentAt S B M2 J2 ∧
  J1 < J2 → K1 < K2

------------------------------------------------------------------------
-- Supporting invariants — global origination + arrival cursors
------------------------------------------------------------------------

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

-- Bridge 1: per-channel deliver-order matches global arrival-order on the
-- SAME source channel. Both cursors monotonic; deliver on the same
-- channel bumps both in lock-step.
invariant [same_channel_deliver_matches_arrival]
  deliveredAt S V M1 J1 ∧ deliveredAt S V M2 J2 ∧
  receivedAtV V M1 R1 ∧ receivedAtV V M2 R2 ∧
  J1 < J2 → R1 < R2

-- Bridge 2: per-channel send-order matches global origination-order at
-- the sender (forward direction).
invariant [same_channel_send_matches_origination]
  sentAt S D M1 K1 ∧ sentAt S D M2 K2 ∧
  originatedAt S M1 O1 ∧ originatedAt S M2 O2 ∧
  K1 < K2 → O1 < O2

-- Bridge 2b: converse — origination-order at sender matches per-channel
-- send-order on the same destination. Needed so `ref_fifo_e2e`'s
-- antecedent O1 < O2 can be translated to K1 < K2 on the unique route.
invariant [same_channel_origination_matches_send]
  sentAt S D M1 K1 ∧ sentAt S D M2 K2 ∧
  originatedAt S M1 O1 ∧ originatedAt S M2 O2 ∧
  O1 < O2 → K1 < K2

-- Bridge 3: forwarding preserves global origination-order. The analog
-- of `forward_preserves_send_order` lifted to global cursors. Combined
-- with `same_channel_*_matches_*` invariants, this chains the slow
-- A→B→C path through to `ref_fifo_e2e`.
invariant [forward_preserves_origination_order]
  sentBy S M1 ∧ sentBy S M2 ∧
  targetRef M1 = targetRef M2 ∧
  forwardedAt B C M1 K1 ∧ forwardedAt B C M2 K2 ∧
  originatedAt S M1 O1 ∧ originatedAt S M2 O2 ∧
  O1 < O2 → K1 < K2

#gen_spec

#check_invariants

------------------------------------------------------------------------
-- Bounded model traces
------------------------------------------------------------------------

/-! ### Happy path: A→P→B resolves to C; all of A's msgs reach C in order.

A routes P→B, sends m₁ and m₂; B receives both; B resolves P→C; B
forwards m₁ and m₂; C receives both. The final assert pins down that
the originator A appears, the resolution host C appears, two distinct
msgs targeted the same promise, and both made it through the chain.
-/
set_option maxHeartbeats 1000000 in
#guard_msgs(drop warning, drop info) in
sat trace [promise_resolve_and_forward] {
  declarePromise
  setupRoute
  send
  send
  deliver
  deliver
  resolvePromise
  forward
  forward
  deliver
  deliver
  assert (∃ (a b c : vat) (m1 m2 : msg) (n1 n2 : Nat),
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    sentBy a m1 ∧ sentBy a m2 ∧
    targetRef m1 = targetRef m2 ∧
    isPromise (targetRef m1) ∧
    resolvedTo (targetRef m1) c ∧
    delivered b c m1 ∧ delivered b c m2 ∧
    deliveredAt b c m1 n1 ∧ deliveredAt b c m2 n2)
} by { bmc_sat }

/-! ### Resolve interleaved: P resolves *between* A's sends.

A sends m₁; B receives m₁; B resolves P→C (installs forwarding route);
A sends m₂ (still A→B because A doesn't know about the resolution);
B receives m₂; B forwards m₁ then m₂; C receives both in order.
Confirms `ref_fifo_e2e` holds even when resolution interleaves with
origination.
-/
set_option maxHeartbeats 1000000 in
#guard_msgs(drop warning, drop info) in
sat trace [resolve_mid_stream] {
  declarePromise
  setupRoute
  send
  deliver
  resolvePromise
  send
  deliver
  forward
  forward
  deliver
  deliver
  assert (∃ (a b c : vat) (m1 m2 : msg) (n1 n2 : Nat),
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    sentBy a m1 ∧ sentBy a m2 ∧
    targetRef m1 = targetRef m2 ∧
    delivered b c m1 ∧ delivered b c m2 ∧
    deliveredAt b c m1 n1 ∧ deliveredAt b c m2 n2)
} by { bmc_sat }

end CaptpRefFifoForwarding
