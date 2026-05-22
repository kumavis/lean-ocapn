import Veil

set_option linter.dupNamespace false

/-!
# Crossed-hellos resolution

When two peers attempt to open a session to each other simultaneously,
the CapTP spec says exactly one of the two prospective sessions must
survive, and both peers must agree on which. The winner is chosen by
bytewise comparison of the two Public Identifiers — the larger one wins.

This module proves **P5** from PLAN.md:

> safety [crossed_hellos_unique]
>   active A B ∧ active B A → A = B

That is: there is at most one active session direction between any pair
of distinct vats.

The model abstracts the bytewise comparison of public identifiers as a
`TotalOrder` over the `vat` sort, since the only structural property of
the comparison used by the resolution rule is totality + antisymmetry.
-/

veil module CrossedHellos

type vat

-- Public identifiers are totally ordered (abstracts the bytewise compare).
instantiate ord : TotalOrder vat

open TotalOrder

-- A vat has initiated a session attempt toward another vat.
relation initiated : vat → vat → Prop
-- A session direction is active (the connection survived the handshake).
relation active : vat → vat → Prop

#gen_state

after_init {
  initiated A B := False;
  active A B := False
}

-- A vat starts a fresh outbound connection.
action initiate (self other : vat) = {
  require self ≠ other
  require ¬ initiated self other
  require ¬ active self other
  require ¬ active other self
  initiated self other := True
}

-- Promote a single (uncrossed) initiation to an active session.
-- This fires when only one side has initiated (the other has not).
action promoteUncrossed (self other : vat) = {
  require self ≠ other
  require initiated self other
  require ¬ initiated other self
  require ¬ active self other
  require ¬ active other self
  active self other := True
}

-- Resolve a crossed-hellos race: both sides have initiated. The vat
-- with the larger public identifier wins; the loser's initiation is
-- discarded (the connection it would have backed is aborted).
action resolveCrossed (a b : vat) = {
  require a ≠ b
  require initiated a b
  require initiated b a
  require ¬ active a b
  require ¬ active b a
  -- Bytewise compare: total + antisymmetric, so either le b a or le a b
  -- (one strict due to a ≠ b). The larger pubid keeps its outbound.
  if le b a then
    active a b := True;
    initiated b a := False
  else
    active b a := True;
    initiated a b := False
}

------------------------------------------------------------------------
-- Safety: P5 — at most one active session direction per vat pair
------------------------------------------------------------------------

safety [crossed_hellos_unique]
  active A B ∧ active B A → A = B

------------------------------------------------------------------------
-- Supporting invariants
------------------------------------------------------------------------

-- No self-loops.
invariant [no_self_active]
  active A A → False
invariant [no_self_initiated]
  initiated A A → False

#gen_spec

#check_invariants

end CrossedHellos
