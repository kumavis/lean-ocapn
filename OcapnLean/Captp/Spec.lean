import Veil

set_option linter.dupNamespace false

/-!
# CapTP single-peer abstract spec (Veil)

Single peer's view of one CapTP session, at the abstraction level needed
for the first batch of safety proofs from PLAN.md:

  * **P8** bootstrap-at-zero — the bootstrap object is always exported at
    the bootstrap position while the session is alive.
  * **P2** promise resolution monotonicity — a resolved promise stays
    resolved with the same value; a broken promise stays broken with the
    same reason; the two are disjoint.

Tables and refcounts are abstracted to uninterpreted sorts and relations to
keep the verification conditions in (or near) EPR.

The two-peer composition for the FIFO proof (P1) lives in
`OcapnLean.Captp.Twoparty`.
-/

veil module CaptpSinglePeer

-- Uninterpreted sorts.
type pos          -- "positive integer" abstracted; we treat 0 as bootstrap
type oref         -- local object reference
type value        -- a passable value (Atom / Container / Reference, opaque)
type error        -- a rejection reason

-- A distinguished bootstrap position and bootstrap object.
immutable individual bootstrapPos : pos
immutable individual bootstrapObj : oref

-- Mutable state.
relation imported : pos → oref → Prop
relation exported : pos → oref → Prop
-- An answer slot is occupied by a pending promise.
relation answerSlot : pos → Prop
-- A promise has been resolved to a value. The witness encoded as relation
-- so we can quantify over it in P2.
relation promiseResolved : pos → value → Prop
-- A promise has been broken with a rejection reason.
relation promiseBroken : pos → error → Prop
individual alive : Prop

#gen_state

after_init {
  imported P R := False;
  exported P R := False;
  exported bootstrapPos bootstrapObj := True;
  answerSlot P := False;
  promiseResolved P V := False;
  promiseBroken P E := False;
  alive := True
}

-- Export an object at a fresh position (not the bootstrap slot).
action exportNew (p : pos) (r : oref) = {
  require alive
  require ¬ ∃ R, exported p R
  require p ≠ bootstrapPos
  exported p r := True
}

-- Receive an import descriptor from the peer for some position.
action importNew (p : pos) (r : oref) = {
  require alive
  require ¬ ∃ R, imported p R
  imported p r := True
}

-- Deliver a message to a remote target, allocating a fresh answer slot
-- for the pending promise.  (op:deliver with answer-pos)
action deliverWithAnswer (target : pos) (newAnswer : pos) = {
  require alive
  require ∃ R, exported target R
  require ¬ answerSlot newAnswer
  require ∀ V, ¬ promiseResolved newAnswer V
  require ∀ E, ¬ promiseBroken newAnswer E
  answerSlot newAnswer := True
}

-- Resolve a previously-allocated answer-slot promise with a value.
action resolvePromise (p : pos) (v : value) = {
  require alive
  require answerSlot p
  require ∀ V, ¬ promiseResolved p V
  require ∀ E, ¬ promiseBroken p E
  promiseResolved p v := True
}

-- Break a previously-allocated answer-slot promise with an error.
action breakPromise (p : pos) (e : error) = {
  require alive
  require answerSlot p
  require ∀ V, ¬ promiseResolved p V
  require ∀ E, ¬ promiseBroken p E
  promiseBroken p e := True
}

-- The session aborts.
action abort = {
  require alive
  alive := False
}

-- `op:get to-desc field-name answer-pos` — read a named field of the
-- target. Same state-machine shape as `deliverWithAnswer`: allocates a
-- fresh answer-slot for the pending promise. The field-name itself
-- is application-level data and opaque to the safety properties.
action opGet (target : pos) (newAnswer : pos) = {
  require alive
  require ∃ R, exported target R
  require ¬ answerSlot newAnswer
  require ∀ V, ¬ promiseResolved newAnswer V
  require ∀ E, ¬ promiseBroken newAnswer E
  answerSlot newAnswer := True
}

-- `op:index to-desc idx answer-pos` — index into the target. Same
-- state-machine shape as `deliverWithAnswer`; the index is opaque.
action opIndex (target : pos) (newAnswer : pos) = {
  require alive
  require ∃ R, exported target R
  require ¬ answerSlot newAnswer
  require ∀ V, ¬ promiseResolved newAnswer V
  require ∀ E, ¬ promiseBroken newAnswer E
  answerSlot newAnswer := True
}

-- `op:untag to-desc label answer-pos` — strip a tag wrapper from the
-- target. Same state-machine shape as `deliverWithAnswer`; the label
-- is opaque.
action opUntag (target : pos) (newAnswer : pos) = {
  require alive
  require ∃ R, exported target R
  require ¬ answerSlot newAnswer
  require ∀ V, ¬ promiseResolved newAnswer V
  require ∀ E, ¬ promiseBroken newAnswer E
  answerSlot newAnswer := True
}

------------------------------------------------------------------------
-- Safety properties
------------------------------------------------------------------------

-- Safety [P8]: the bootstrap object always lives at the bootstrap position
-- while the session is alive.
safety [bootstrap_at_zero]
  alive → exported bootstrapPos bootstrapObj

-- Safety [P2a]: promise resolution is monotone in the value.  Once a
-- promise is resolved to V1 it stays resolved to V1; in particular no
-- second value V2 can also appear.
safety [promise_monotone_fulfilled]
  promiseResolved P V1 ∧ promiseResolved P V2 → V1 = V2

-- Safety [P2b]: promise breakage is monotone in the rejection reason.
safety [promise_monotone_broken]
  promiseBroken P E1 ∧ promiseBroken P E2 → E1 = E2

-- Safety [P2c]: a promise is not both resolved and broken.
safety [promise_disjoint]
  promiseResolved P V → ¬ promiseBroken P E

------------------------------------------------------------------------
-- Supporting invariants
------------------------------------------------------------------------

-- Imports are functional.
invariant [imported_functional]
  imported P R1 ∧ imported P R2 → R1 = R2

-- Exports are functional.
invariant [exported_functional]
  exported P R1 ∧ exported P R2 → R1 = R2

-- A resolved promise must come from an allocated answer slot.
invariant [resolved_implies_slot]
  promiseResolved P V → answerSlot P

-- A broken promise must come from an allocated answer slot.
invariant [broken_implies_slot]
  promiseBroken P E → answerSlot P

#gen_spec

#check_invariants

end CaptpSinglePeer
