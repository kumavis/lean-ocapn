import Veil

set_option linter.dupNamespace false

/-!
# CapTP promise shortening breaks `ref_fifo` — M11 Phase B

Mirror of `RefFifoForwarding.lean` plus a `shorten` action that
mutates `routesTo` for the sender directly (bypassing the
forwarder). This module **demonstrates** the failure mode that
motivates Phase C's `op:flush` precondition.

## Design

Phase A.5's `RefFifoForwarding.lean` lifts msgs sent on the slow path
(A→B→C via forwarding) into a per-(sender, ref) FIFO claim at the
resolution host C. That claim **assumes the sender's route to the
promise is immutable for the lifetime of any in-flight msg**.
Shortening violates that assumption: the sender can be told the
promise resolved and overwrite its own route, then send subsequent
msgs on the fast path (A→C directly) that race past the in-flight
slow-path msg.

To exhibit the violation while keeping Phase A.5's existing proofs
intact, this module is **a separate Veil module** rather than a
modification to `RefFifoForwarding`. The shortening behaviour is
**gated by a state flag** `shorteningEnabled` so that the original
Phase A.5 scenarios remain reachable without engaging shortening at
all. Phase A's existing modules (`RefFifoForwarding.lean`) continue
to discharge `#check_invariants` as before — this module **does not**
re-discharge them, since shortening breaks them by construction.

## What this module commits

* `relation shorteningEnabled : Prop` — state flag (initially false).
* `action enableShortening` — sets the flag to true.
* `action shorten (v p oldT newT)` — when the flag is enabled,
  overwrites `routesTo v p` from `oldT` to `newT`. The old route
  binding is *cleared* and the new one installed atomically. The
  precondition does **not** require the old wire to be drained — that
  is precisely the Phase C strengthening.
* A `bmc_sat` trace exhibiting the **Tribble race**: A sends m₁ on
  the slow path (A→B), B resolves P→C, A shortens, A sends m₂ on the
  fast path (A→C), C receives m₂ first, then m₁ arrives via B's
  forward. The witness asserts: `sentBy A m₁ ∧ sentBy A m₂ ∧
  targetRef m₁ = targetRef m₂ ∧ delivered _ C m₁ ∧ delivered _ C m₂ ∧
  deliveredAt _ C m₂ N₂ ∧ deliveredAt B C m₁ N₁ ∧ N₂ < N₁` — m₂
  delivered at C before m₁, despite both targeting the same ref from
  the same originator. The shortened state shows
  `sentAt A B m₁ K ∧ ¬ routesTo A (targetRef m₁) B` — the residual
  in-flight send that has lost its routing witness, the precise
  condition Phase C's `op:flush` precludes.

## What this module does *not* commit

* `#check_invariants` — Phase B is about **exhibiting the failure**,
  not re-discharging safety under shortening. The safeties carried
  here are stated for reference but not SMT-discharged in this
  module; their violation under shortening is the point. Phase C
  will re-add `#check_invariants` over a strengthened `shorten`.
* `safety [ref_fifo_e2e]` — also stated in comments only; the
  Tribble race witness is what shows it fails.

## Relationship to Phase C

Phase C will fork this module to `RefFifoShorteningFlushed.lean`,
add the precondition `∀ M K, sentBy V M ∧ targetRef M = P ∧
  sentAt V oldT M K ∧ ¬ delivered V oldT M → False` (no in-flight
msgs from V via the old route), re-add `#check_invariants`, and
include both happy-path and pathological-but-prevented `bmc_sat`
traces.
-/

veil module CaptpRefFifoShortening

------------------------------------------------------------------------
-- Uninterpreted sorts
------------------------------------------------------------------------

type vat
type msg
type ref

------------------------------------------------------------------------
-- State (carried from RefFifoForwarding.lean)
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

-- Cross-channel origination + arrival cursors (mirror of
-- RefFifoForwarding.lean's strengthened formulation). These let the
-- bmc_sat witness below assert the failure of the strengthened
-- `ref_fifo_e2e` directly: m₁ originated before m₂ at A, but m₂
-- arrived at C before m₁.
function originateCursor   : vat → Nat
function deliverArrCursor  : vat → Nat
relation originatedAt      : vat → msg → Nat → Prop
relation receivedAtV       : vat → msg → Nat → Prop

------------------------------------------------------------------------
-- Phase B addition: shortening flag
------------------------------------------------------------------------

relation shorteningEnabled : Prop

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
  receivedAtV V M K := False;
  shorteningEnabled := False
}

------------------------------------------------------------------------
-- Actions carried unchanged from RefFifoForwarding.lean
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
  -- Mirror of RefFifoForwarding's cross-channel origination tracking.
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
  -- Mirror of RefFifoForwarding's cross-channel arrival tracking.
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
  -- Receive-order preservation at the forwarder: any earlier-sent
  -- same-(originator, ref) msg already delivered at B must already
  -- be forwarded before m can be.
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
-- Phase B additions: enableShortening + shorten
------------------------------------------------------------------------

-- One-shot flag enable. Once set, `shorten` can fire.
action enableShortening = {
  shorteningEnabled := True
}

-- The mutating route update. Overwrites `routesTo v p` from `oldT` to
-- `newT` atomically: clear the old binding and install the new one.
-- Phase B has NO drained-wire precondition — that's exactly what
-- Phase C will add.
action shorten (v : vat) (p : ref) (oldT newT : vat) = {
  require shorteningEnabled
  require routesTo v p oldT
  require isPromise p
  require resolvedTo p newT
  require oldT ≠ newT
  routesTo v p oldT := False
  routesTo v p newT := True
}

#gen_spec

------------------------------------------------------------------------
-- Bounded model trace: the Tribble race
------------------------------------------------------------------------

/-! ### Tribble race: shortening lets m₂ overtake m₁ at C.

Scenario:
1. A sets up route P → B (slow path).
2. A sends m₁ on A→B (in flight; later forwarded by B to C).
3. B receives m₁.
4. B declares P a promise and resolves P → C (installs B's
   forwarding route).
5. `enableShortening` — the flag is flipped.
6. A shortens its route to P: now A's route for P is C (not B).
7. A sends m₂ on A→C (fast path, bypasses B entirely).
8. C delivers m₂ first.
9. B forwards m₁ to C.
10. C delivers m₁ second.

The final assert pins three concrete vats A ≠ B ≠ C, m₁ and m₂ both
originated by A targeting the same promise, both ending up at C, but
m₂ arrives at C **before** m₁ — i.e. send-order at A is reversed at
the delivery point C. This is the **Tribble race** in mechanized
form: the failure mode that Phase C's `op:flush` precludes.
-/
set_option maxHeartbeats 1000000 in
#guard_msgs(drop warning, drop info) in
sat trace [tribble_race] {
  declarePromise
  setupRoute
  send
  deliver
  resolvePromise
  enableShortening
  shorten
  send
  deliver
  forward
  deliver
  assert (∃ (a b c : vat) (m1 m2 : msg) (n1 n2 : Nat),
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    sentBy a m1 ∧ sentBy a m2 ∧
    targetRef m1 = targetRef m2 ∧
    isPromise (targetRef m1) ∧
    resolvedTo (targetRef m1) c ∧
    -- m₁ arrives at C via B's forward (slow path).
    delivered b c m1 ∧ deliveredAt b c m1 n1 ∧
    -- m₂ arrives at C directly from A (fast path, post-shorten).
    delivered a c m2 ∧ deliveredAt a c m2 n2 ∧
    -- The race ordering: m₂ delivered at C before m₁.
    n2 < n1)
} by { bmc_sat }

/-! ### Shortening drops the in-flight wire's routing witness.

Standalone witness: after shortening, the original A→B `sentAt` fact
for m₁ persists in state, but the route that justified it
(`routesTo A P B`) has been cleared. This is the exact invariant
loss — `sentAt_via_route` from `RefFifoForwarding.lean` would be
violated here — that Phase C's `op:flush` precondition prevents by
requiring the old wire be drained before `shorten` can fire.
-/
set_option maxHeartbeats 1000000 in
#guard_msgs(drop warning, drop info) in
sat trace [shorten_drops_route_witness] {
  declarePromise
  setupRoute
  send
  resolvePromise
  enableShortening
  shorten
  assert (∃ (a b : vat) (p : ref) (m : msg) (k : Nat),
    a ≠ b ∧
    sentBy a m ∧
    targetRef m = p ∧
    isPromise p ∧
    sentAt a b m k ∧
    -- The witness: the route that justified the in-flight send is gone.
    ¬ routesTo a p b)
} by { bmc_sat }

/-! ### Strong-form ref_fifo_e2e violation (the headline counter-trace)

The strengthened `ref_fifo_e2e` from `RefFifoForwarding.lean` uses
S's global origination cursor and C's global arrival cursor instead
of per-channel cursors. This trace exhibits A originating m₁ before
m₂ (`O1 < O2`), both ending up at C, but m₂ arriving BEFORE m₁ at C
(`R2 < R1`) — a direct violation of the strengthened formulation.

This is the mechanical contribution: a concrete bmc_sat witness that
naive shortening violates the user-facing per-(sender, ref) delivery
order at the resolution host. Phase C's `op:flush` precondition will
restore the safety by requiring the old wire to drain before the
sender can shorten.
-/
set_option maxHeartbeats 1000000 in
#guard_msgs(drop warning, drop info) in
sat trace [ref_fifo_e2e_violated_by_shorten] {
  declarePromise
  setupRoute
  send                  -- A sends m₁ on A→B (slow path); O1 = 0.
  deliver               -- B receives m₁.
  resolvePromise        -- B resolves P→C, installs routesTo B P C.
  enableShortening
  shorten               -- A's route: A→B → A→C (mutating).
  send                  -- A sends m₂ on A→C (fast path); O2 = 1.
  deliver               -- C receives m₂; R2 = 0 at C.
  forward               -- B forwards m₁ to C.
  deliver               -- C receives m₁; R1 = 1 at C.
  assert (∃ (a b c : vat) (m1 m2 : msg) (o1 o2 r1 r2 : Nat),
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    sentBy a m1 ∧ sentBy a m2 ∧
    targetRef m1 = targetRef m2 ∧
    isPromise (targetRef m1) ∧
    resolvedTo (targetRef m1) c ∧
    originatedAt a m1 o1 ∧ originatedAt a m2 o2 ∧
    receivedAtV c m1 r1 ∧ receivedAtV c m2 r2 ∧
    -- The violation: A originated m₁ first, but C received m₂ first.
    o1 < o2 ∧ r2 < r1)
} by { bmc_sat }

/-! ### Old vacuity witness (kept for reference)

The original per-channel `ref_fifo_e2e` formulation conditioned on
both msgs traversing the same `(forwarder, dest)` pair — under
shortening m₂ bypasses B, so the antecedent fails and the safety is
vacuously true. Kept as evidence of WHY the strengthening above was
necessary.
-/
set_option maxHeartbeats 1000000 in
#guard_msgs(drop warning, drop info) in
sat trace [race_with_old_e2e_safety_vacuous] {
  declarePromise
  setupRoute
  send
  deliver
  resolvePromise
  enableShortening
  shorten
  send
  deliver
  forward
  deliver
  assert (∃ (a b c : vat) (m1 m2 : msg),
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    sentBy a m1 ∧ sentBy a m2 ∧
    targetRef m1 = targetRef m2 ∧
    (∃ k1, sentAt a b m1 k1) ∧
    (∃ kf1, forwardedAt b c m1 kf1) ∧
    delivered b c m1 ∧
    (∃ k2, sentAt a c m2 k2) ∧
    delivered a c m2 ∧
    -- m₂ is NOT on the A→B channel; not forwarded by B.
    (∀ k, ¬ sentAt a b m2 k) ∧
    (∀ kf, ¬ forwardedAt b c m2 kf))
} by { bmc_sat }

end CaptpRefFifoShortening
