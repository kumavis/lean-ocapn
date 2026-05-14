import Veil

/-!
# Distributed garbage collection — P4 GC soundness

CapTP's `op:gc-exports` distributes reference counting between peers.
The exporter holds a count of how many outstanding references the
remote peer has to a given export position; the remote peer signals
"I'm done with N copies" via `op:gc-exports` with `(pos, wire-delta)`.

This module proves **P4** from PLAN.md:

> An object is only locally collected when its export refcount has
> reached zero AND all wire-deltas have been accounted for.

We decompose the exporter's refcount into three monotonic quantities:

* `localCount p` — how many references the peer currently holds
* `inFlightSends p` — exporter has shipped this many ref copies that
  haven't yet been received by the peer
* `inFlightDecs p` — peer has shipped this many `op:gc-exports`
  decrements that haven't yet been applied by the exporter
* `exporterCount p = localCount p + inFlightSends p + inFlightDecs p`

The soundness property: when the exporter collects (which it may do
only when its own count is zero), all three of those sub-counts are
zero — so no peer-held ref, no in-flight ship, and no in-flight
decrement reference the collected position.
-/

veil module CaptpGc

type pos

function localCount      : pos → Nat
function inFlightSends   : pos → Nat
function inFlightDecs    : pos → Nat
function exporterCount   : pos → Nat
relation collected       : pos → Prop

#gen_state

after_init {
  localCount P := 0;
  inFlightSends P := 0;
  inFlightDecs P := 0;
  exporterCount P := 0;
  collected P := False
}

-- The exporter ships a fresh reference copy to the peer.
action exporterSendRef (p : pos) = {
  require ¬ collected p
  exporterCount p := exporterCount p + 1
  inFlightSends p := inFlightSends p + 1
}

-- The peer receives a shipped reference and increments its local holding.
action peerRecvRef (p : pos) = {
  require inFlightSends p > 0
  inFlightSends p := inFlightSends p - 1
  localCount p := localCount p + 1
}

-- The peer releases one local copy and ships a decrement to the exporter.
action peerSendDec (p : pos) = {
  require localCount p > 0
  localCount p := localCount p - 1
  inFlightDecs p := inFlightDecs p + 1
}

-- The exporter applies a wire-delta decrement.
action exporterRecvDec (p : pos) = {
  require inFlightDecs p > 0
  inFlightDecs p := inFlightDecs p - 1
  exporterCount p := exporterCount p - 1
}

-- The exporter collects the local object backing the export position.
action collect (p : pos) = {
  require ¬ collected p
  require exporterCount p = 0
  collected p := True
}

------------------------------------------------------------------------
-- Safety: P4 — GC soundness
------------------------------------------------------------------------

-- When a position is collected, the peer holds no references, no
-- ref-ship is in flight, and no decrement is in flight.
safety [gc_sound]
  collected P → localCount P = 0 ∧ inFlightSends P = 0 ∧ inFlightDecs P = 0

------------------------------------------------------------------------
-- Supporting inductive invariants
------------------------------------------------------------------------

-- The defining equation: the exporter's count is the sum of the three
-- sub-counts.  This is the inductive heart of P4.
invariant [exporter_count_decomp]
  exporterCount P = localCount P + inFlightSends P + inFlightDecs P

-- A collected position has zero exporter-count (and stays zero).
invariant [collected_zero]
  collected P → exporterCount P = 0

#gen_spec

#check_invariants

end CaptpGc
