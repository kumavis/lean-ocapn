import Veil

set_option linter.dupNamespace false

/-!
# CapTP two-peer composition — end-to-end reference FIFO

This module models *two* CapTP peers (vats) connected by per-direction
reliable in-order channels, abstracted at the level of `op:deliver`
messages and the cursors that drive them.

The headline safety property is **P1** from PLAN.md:

> For any two vats Alice and Bob, the order in which `op:deliver` messages
> sent from Alice arrive at Bob's local delivery point is the same as the
> order in which Alice's application code invoked the send.

The model is intentionally minimal — it abstracts the payload of each
message and concentrates only on the send/deliver-order property. Later
modules will refine the message contents.
-/

veil module CaptpTwoparty

-- Uninterpreted sorts.
type vat
type msg

-- Per (src,dst) channel cursors.
function sendCursor : vat → vat → Nat
function recvCursor : vat → vat → Nat

-- Wire state: a multiset of messages currently in flight, indexed by
-- the sequence number assigned at send time.
relation pending   : vat → vat → msg → Prop
relation delivered : vat → vat → msg → Prop

-- Per-message metadata: when it was sent (immutable once set).  We
-- represent this as a relation `sentAt s d m k` meaning "message m on
-- channel s→d was assigned send-index k".  Functional and immutable.
relation sentAt      : vat → vat → msg → Nat → Prop
-- And similarly when it was delivered locally.
relation deliveredAt : vat → vat → msg → Nat → Prop

#gen_state

after_init {
  sendCursor S D := 0;
  recvCursor S D := 0;
  pending S D M := False;
  delivered S D M := False;
  sentAt S D M K := False;
  deliveredAt S D M K := False
}

-- A peer hands a fresh message to the CapTP layer for transmission.
-- The message is enqueued on the wire at the current send-cursor, and
-- the cursor advances.
action send (s d : vat) (m : msg) = {
  require ¬ pending s d m
  require ¬ delivered s d m
  require ∀ K, ¬ sentAt s d m K       -- m has never been used on this channel
  pending s d m := True
  sentAt s d m (sendCursor s d) := True
  sendCursor s d := (sendCursor s d) + 1
}

-- The destination peer delivers the next message at the head of the
-- channel to its local target.  FIFO is enforced by requiring the
-- message's send-index to equal the current recv-cursor.
action deliver (s d : vat) (m : msg) = {
  require pending s d m
  require sentAt s d m (recvCursor s d)
  pending s d m := False
  delivered s d m := True
  deliveredAt s d m (recvCursor s d) := True
  recvCursor s d := (recvCursor s d) + 1
}

------------------------------------------------------------------------
-- Safety: the headline P1 end-to-end FIFO property
------------------------------------------------------------------------

-- If two messages were both delivered, the one sent first was delivered
-- first.  (Stated as: their delivery indices are in the same order as
-- their send indices.)
safety [e2e_fifo]
  delivered S D M1 ∧ delivered S D M2 ∧
  sentAt S D M1 K1 ∧ sentAt S D M2 K2 ∧
  deliveredAt S D M1 J1 ∧ deliveredAt S D M2 J2 ∧
  K1 < K2 →
  J1 < J2

------------------------------------------------------------------------
-- Supporting inductive invariants
------------------------------------------------------------------------

-- Cursor sanity: recv never overtakes send.
invariant [recv_le_send]
  recvCursor S D ≤ sendCursor S D

-- sentAt is functional in the index: each message has at most one send
-- index per channel.
invariant [sentAt_functional]
  sentAt S D M K1 ∧ sentAt S D M K2 → K1 = K2

-- sentAt is *injective* in the message: at most one message has any
-- given send-index per channel.  This is the key fact that turns FIFO
-- send into FIFO deliver.
invariant [sentAt_injective]
  sentAt S D M1 K ∧ sentAt S D M2 K → M1 = M2

-- deliveredAt is functional in the index.
invariant [deliveredAt_functional]
  deliveredAt S D M K1 ∧ deliveredAt S D M K2 → K1 = K2

-- deliveredAt is injective in the message.
invariant [deliveredAt_injective]
  deliveredAt S D M1 J ∧ deliveredAt S D M2 J → M1 = M2

-- For pending or delivered messages, sentAt is defined.
invariant [pending_has_send_index]
  pending S D M → ∃ K, sentAt S D M K
invariant [delivered_has_send_index]
  delivered S D M → ∃ K, sentAt S D M K

-- For delivered messages, deliveredAt is defined.
invariant [delivered_has_deliver_index]
  delivered S D M → ∃ J, deliveredAt S D M J

-- No orphan deliver-indices: deliveredAt only fires for delivered msgs.
invariant [deliveredAt_implies_delivered]
  deliveredAt S D M J → delivered S D M

-- A delivered message is not still pending.
invariant [pending_delivered_disjoint]
  pending S D M ∧ delivered S D M → False

-- Send-cursor frontier: every used send index is strictly less than
-- the current sendCursor.
invariant [sentAt_below_cursor]
  sentAt S D M K → K < sendCursor S D

-- Recv-cursor frontier: every used deliver index is strictly less
-- than the current recvCursor.
invariant [deliveredAt_below_cursor]
  deliveredAt S D M J → J < recvCursor S D

-- The head of the queue: every pending message has a send-index ≥ the
-- current recvCursor (because messages with send-index < recvCursor
-- have already been delivered).
invariant [pending_at_or_above_recv]
  pending S D M ∧ sentAt S D M K → recvCursor S D ≤ K

-- Delivered messages had send-index < recvCursor.
invariant [delivered_below_recv_cursor]
  delivered S D M ∧ sentAt S D M K → K < recvCursor S D

-- Crucially: for delivered messages, the deliver-index equals the
-- send-index.  This is the inductive heart of the FIFO proof.
invariant [deliver_eq_send]
  delivered S D M ∧ sentAt S D M K ∧ deliveredAt S D M J → K = J

#gen_spec

#check_invariants

end CaptpTwoparty
