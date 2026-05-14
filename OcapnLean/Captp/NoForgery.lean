import Veil

/-!
# Capability unforgeability — P3 no-forgery

A peer can hold an authoritative reference to an object only if some
peer that *had* authority over it explicitly sent it. There is no
"forging" a reference into one's import table.

This module proves **P3** from PLAN.md in its *direct-send* form: we
model `vat -> exported` and `vat -> imported` tables and a wire between
peers. References enter the imported table only via the wire, and only
through a `send` action gated on the sender's `exported` table.

We **do not** model forwarding here (i.e. an imported reference being
re-sent by its holder). Forwarding requires transitive-closure
reasoning over chains of sends, which is not EPR and would need a
ghost provenance relation. That generalisation is left to a future
module dedicated to three-party handoffs (PLAN P6).
-/

veil module CaptpNoForgery

type vat
type pos
type oref

-- `exported s p r`: vat `s` claims authority over object `r` at
-- position `p`. Authority is established by a trusted setup action
-- (the only way authority can enter the system).
relation exported : vat → pos → oref → Prop
-- `imported d p r`: vat `d` holds reference `(p, r)` in its import
-- table — i.e. it received a ref to `r` at position `p` from a peer.
relation imported : vat → pos → oref → Prop
-- `onWire s d p r`: a message in flight from `s` to `d` carries the
-- binding `(p, r)`.
relation onWire   : vat → vat → pos → oref → Prop

#gen_state

after_init {
  exported V P R := False;
  imported V P R := False;
  onWire S D P R := False
}

-- Trusted bootstrap: a vat declares authority for its own local object.
-- This is the only way authority enters the system; everything else
-- proves no new authority can be forged.
action setupAuthority (v : vat) (p : pos) (r : oref) = {
  exported v p r := True
}

-- A vat sends a reference it has authority over to another vat.
-- Gating on `exported s p r` is the structural source of unforgeability.
action send (s d : vat) (p : pos) (r : oref) = {
  require s ≠ d
  require exported s p r
  onWire s d p r := True
}

-- Receiver consumes an in-flight reference and adds it to its imports.
action receive (s d : vat) (p : pos) (r : oref) = {
  require onWire s d p r
  imported d p r := True
}

------------------------------------------------------------------------
-- Safety: P3 — no forgery
------------------------------------------------------------------------

-- Every reference in a vat's import table was sent by *some* peer that
-- had authority over it.  This rules out a vat "summoning" a reference
-- it never received from anyone.
safety [no_forgery]
  imported D P R → ∃ S, exported S P R

------------------------------------------------------------------------
-- Supporting inductive invariant
------------------------------------------------------------------------

-- A message in flight is always backed by the sender's `exported`
-- authority.  This is the inductive heart: it follows from the
-- guard on `send`, and `receive` only consumes the wire entry without
-- producing new wire entries.
invariant [wire_implies_exported]
  onWire S D P R → exported S P R

#gen_spec

#check_invariants

end CaptpNoForgery
