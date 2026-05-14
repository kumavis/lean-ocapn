import Veil

/-!
# Three-party handoff non-replay — P6

Three-party handoffs let a *Gifter* introduce the *Receiver* to a
reference owned by the *Exporter*. The flow:

1. Gifter deposits a gift at Exporter (an `op:deliver` with `deposit-gift`).
2. Gifter sends a signed `desc:handoff-give` to Receiver.
3. Receiver wraps that into a `desc:handoff-receive` (with a `handoff-count`)
   and sends it to Exporter's bootstrap via `withdraw-gift`.
4. Exporter validates, and if all checks pass returns the gift.

The **replay-protection** rule (CapTP spec §desc:handoff-receive):

> The `handoff-count` MUST be a non-negative integer that has NOT been
> used before in the **Exporter-Receiver** session.

This module proves **P6** from PLAN.md: a `desc:handoff-receive` with a
given `(Exporter, Receiver, handoff-count)` triple is honoured by the
Exporter at most once, even under adversarial replay.

Signature verification is abstracted out: we model only sessions in
which the cryptographic checks have already passed — i.e. the
`pendingReceive` relation represents *authentic* receive requests.
Any adversary capable of forging a `desc:handoff-receive` would
violate the underlying EdDSA assumption, which is outside Veil's scope.
-/

veil module CaptpThreeparty

type vat
type giftId

-- A `desc:handoff-receive` request that has reached the Exporter and
-- passed signature validation. An adversary can submit the same
-- (e, r, hc) tuple any number of times by re-broadcasting it.
relation pendingReceive : vat → vat → Nat → giftId → Prop

-- The Exporter has honoured this (Receiver, handoff-count) pair.
relation honoured : vat → vat → Nat → Prop

-- The Receiver got back the gift identified by `giftId` for the given
-- (Exporter, handoff-count). The non-replay property is functionality
-- of this relation in its first three arguments.
relation receivedGift : vat → vat → Nat → giftId → Prop

#gen_state

after_init {
  pendingReceive E R H G := False;
  honoured E R H := False;
  receivedGift E R H G := False
}

-- An (authenticated) `desc:handoff-receive` shows up at the Exporter.
-- Adversarial replay is captured by allowing this action to fire
-- multiple times with the same (e, r, hc) — there is no guard against it.
action submitReceive (e r : vat) (hc : Nat) (gid : giftId) = {
  pendingReceive e r hc gid := True
}

-- The Exporter honours a previously-submitted receive. The guard
-- `¬ honoured e r hc` is the replay-protection rule from the spec.
action exporterHonour (e r : vat) (hc : Nat) (gid : giftId) = {
  require pendingReceive e r hc gid
  require ¬ honoured e r hc
  honoured e r hc := True
  receivedGift e r hc gid := True
}

------------------------------------------------------------------------
-- Safety: P6 — three-party handoff non-replay
------------------------------------------------------------------------

-- For any (Exporter, Receiver, handoff-count) triple, the Receiver
-- gets back at most one gift. Replaying the receive cannot cause a
-- second gift to materialise.
safety [handoff_no_replay]
  receivedGift E R H G1 ∧ receivedGift E R H G2 → G1 = G2

------------------------------------------------------------------------
-- Supporting inductive invariant
------------------------------------------------------------------------

-- The receivedGift relation is grounded in honoured: every record of a
-- gift returned came from a successful exporter-honour, which then
-- prevents further honour for the same (e, r, hc).
invariant [received_implies_honoured]
  receivedGift E R H G → honoured E R H

#gen_spec

#check_invariants

end CaptpThreeparty
