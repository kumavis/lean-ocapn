import Veil

set_option linter.dupNamespace false

/-!
# Promise resolution as a path-change race — M11 Phase B'

A sibling of `RefFifoShortening.lean`. Where Phase B mechanises the
**Tribble race under explicit `shorten`**, this module mechanises a
*subtler* race: the sender (Alice) learns a promise has resolved and
updates its own route accordingly, **without any `shorten` action**.

The race source is just promise resolution to a ref hosted on a
different vat than the promise-host:

> "you get e2e ref fifo from p2p fifo up until a path change. but
> even just promise resolution to a ref in a different vat than the
> promise host is a path change. promise shortening is also a path
> change. so we technically need op:flush even without promise
> shortening to get e2e ref fifo (or e-order)"

The concrete instance: Alice sends to a promise P held by Bob. P
resolves to a ref hosted **back on Alice**. Alice learns the
resolution (via `op:listen` or similar in the spec) and updates her
own route for P from A→B to A→A. Subsequent A→P sends go directly
to A; the still-in-flight A→B→A msg via Bob's forward arrives later.
At Alice, the second-sent msg is delivered first.

## What this module commits

* `action learnResolution v p c` — when v learns p resolved to c, sets
  `routesTo v p := c`. Unlike Phase B's `shorten`, no flag gates this:
  the spec permits the sender to update routes on learning resolution
  (via `op:listen` notification or similar). The mutation is the same
  shape as `shorten`'s — clear the old binding, install the new — but
  the framing here is "learning", not "explicit shortening."

* A `bmc_sat` trace `promise_resolves_to_alice_race` exhibiting the
  full scenario above and asserting `O1 < O2 ∧ R2 < R1` using the
  cross-channel cursors imported from RefFifoForwarding's state.

## Relationship to RefFifoShortening

Functionally, `learnResolution` is the same atomic mutation as
`shorten`. The reason for a separate module is **what's being
demonstrated**, not what's being computed:

* `RefFifoShortening.lean` says: "if the spec permits naive
  `shorten`, the race emerges." Phase C's `op:flush` precondition
  addresses this.
* `RefFifoPromiseResolution.lean` says: "even without `shorten`, the
  *natural sender-side route-update on learning resolution* is itself
  a path change and exhibits the same race." Phase C's `op:flush` is
  the same fix — it gates EITHER route mutation behind drained-wire
  preconditions.

These are two doors to the same room. Either entry point is enough
to motivate `op:flush`; both being demonstrated tightens the
spec-level argument.

## What this module does *not* commit

* `#check_invariants` — like Phase B, the module's purpose is
  exhibiting violation, not re-discharging safety under route
  mutation. Phase C will introduce a flush-gated `learnResolution`
  with `#check_invariants` re-enabled over the strengthened
  preconditions.
-/

veil module CaptpRefFifoPromiseResolution

------------------------------------------------------------------------
-- Uninterpreted sorts
------------------------------------------------------------------------

type vat
type msg
type ref

------------------------------------------------------------------------
-- State (mirrors RefFifoForwarding.lean's strong form)
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

-- Cross-channel cursors (from RefFifoForwarding's strong form).
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
-- Actions (mirror of RefFifoForwarding plus `learnResolution`)
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
  -- First-arrival-only dedup at d (real CapTP semantics).
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
-- The Phase B' addition: learnResolution
------------------------------------------------------------------------

-- v learns that promise p has resolved to c, and updates its own route
-- for p from whatever-was-there to c. Mirrors what `op:listen` plus
-- sender-side route bookkeeping does in the wild. No flag — this is
-- the natural, spec-permitted sender-side update on learning a
-- resolution. The mutation is the same shape as Phase B's `shorten`,
-- but the framing is "learning", not "explicit shortening."
action learnResolution (v : vat) (p : ref) (oldT newT : vat) = {
  require isPromise p
  require resolvedTo p newT
  require routesTo v p oldT
  require oldT ≠ newT
  routesTo v p oldT := False
  routesTo v p newT := True
}

#gen_spec

------------------------------------------------------------------------
-- Bounded model trace: promise-resolves-to-Alice race
------------------------------------------------------------------------

/-! ### Promise resolves back to Alice; Alice's learning is a path change.

Scenario (matching the user's note):
1. Alice sets up route P → Bob (slow path).
2. Alice sends m₁ targeting P → goes A→B (still pending at Bob).
3. Bob delivers m₁.
4. Bob declares P a promise and resolves P → **Alice** (the resolved-to
   ref lives back on Alice's own vat).
5. **`learnResolution`** — Alice learns the resolution and updates her
   own route: routesTo A P := A.
6. Alice sends m₂ targeting P → now goes A→A (local).
7. Alice delivers m₂ via A→A (first arrival at Alice).
8. Bob forwards m₁ to Alice on B→A wire.
9. Alice delivers m₁ via B→A (second arrival at Alice).

End state: m₁ originated first (O1 < O2), m₂ arrived first at Alice
(R2 < R1). The cross-channel cursors from RefFifoForwarding's
state make this race visible at the `originatedAt` / `receivedAtV`
relation level.

No `shorten` action invoked. The route mutation is entirely
attributable to Alice's natural response to learning P resolved.
-/
#guard_msgs(drop warning, drop info) in
sat trace [promise_resolves_to_alice_race] {
  declarePromise
  setupRoute
  send                  -- m₁ on A→B; O1 at A
  deliver               -- B receives m₁
  resolvePromise        -- P resolves to A (resolvedTo p a, routesTo b p := a)
  learnResolution       -- A updates: routesTo a p := a (no shorten!)
  send                  -- m₂ on A→A; O2 at A
  deliver               -- A receives m₂ locally; R2 at A
  forward               -- B forwards m₁ to A
  deliver               -- A receives m₁ via B→A; R1 at A
  assert (∃ (a b : vat) (m1 m2 : msg) (o1 o2 r1 r2 : Nat),
    a ≠ b ∧
    sentBy a m1 ∧ sentBy a m2 ∧
    targetRef m1 = targetRef m2 ∧
    isPromise (targetRef m1) ∧
    resolvedTo (targetRef m1) a ∧
    originatedAt a m1 o1 ∧ originatedAt a m2 o2 ∧
    receivedAtV a m1 r1 ∧ receivedAtV a m2 r2 ∧
    -- The violation: a originated m₁ first (O1 < O2), but
    -- received m₂ first locally (R2 < R1).
    o1 < o2 ∧ r2 < r1)
} by { bmc_sat }

end CaptpRefFifoPromiseResolution
