import OcapnLean.Netlayer

/-!
# Netlayer axiomatic spec (M11 Phase A.7)

The abstract contract the `Netlayer` interface implicitly promises.
Stated over a Lean-level *trace* of operations — `sent` / `received`
events on each (src, dst) ordered channel. Concrete netlayer
implementations either prove they satisfy the spec (the in-process
netlayer in `OcapnLean.Netlayer.InProcess`) or are trusted to satisfy
it (TCP/UDS/WS — verified via cross-impl interop tests).

The contract is the **only thing trusted** about a netlayer in the
Phase A.7 runtime FIFO proof. Everything downstream
(`MultiVat`-projected FIFO, `ref_fifo_e2e` at the runtime) follows
from the contract + the Veil-proved safety on the projection.

## What the spec promises

For each ordered `(src, dst)` channel:

1. **Per-channel FIFO**: msgs received at `dst` from `src` appear in
   the same order `src` sent them.
2. **No loss**: every msg `src` sent to `dst` is eventually received
   at `dst` (modulo `close` — closing terminates delivery).
3. **No spontaneous msgs**: every msg received at `dst` from `src`
   was previously sent by `src` to `dst`. (Crucial: messages don't
   appear out of nothing.)

Asynchrony — arbitrary but finite latency — is **not** stated as a
positive property; it's the absence of a synchronous-delivery
constraint. The spec deliberately does not say "send returns only
after delivery"; that would forbid the realistic case of in-flight
msgs.

## Why this is the right trusted boundary

The properties above are exactly what TCP guarantees per-connection
(via sequence numbers + retransmission). WebSocket inherits them
from TCP. Unix-domain sockets inherit them from the kernel. So the
trust we'd previously assigned to "the runtime correctly implements
FIFO" reduces to "TCP correctly implements FIFO," which is a much
narrower and better-studied claim.

For in-process netlayers (used in the M11 multi-vat smoke), this
contract is **provable** in Lean — see
`OcapnLean.Netlayer.InProcess.spec_satisfied`.
-/

namespace OcapnLean.Netlayer.Spec

/-- Vat identifier — matches `Impl.MultiVat.Vat`. -/
abbrev Vat := Nat

/-- One observable event on the netlayer's per-channel history. The
sender / receiver are abstracted as vat ids; the msg is the wire
payload. -/
inductive Event
  | sent      (src dst : Vat) (msg : ByteArray)
  | received  (src dst : Vat) (msg : ByteArray)
deriving Inhabited

/-- The trace of events on a netlayer is a list ordered by causal
sequence within each peer (each peer's history is a linear sequence
of sends and recvs; the global trace is one possible interleaving). -/
abbrev Trace := List Event

/-- Per-event extractor: yields the msg if this event is a `sent` from
`src` to `dst`, else `none`. Used by `Trace.sentOn`. -/
def Event.asSentOn (src dst : Vat) : Event → Option ByteArray
  | .sent s d msg     => if s = src ∧ d = dst then some msg else none
  | .received _ _ _   => none

/-- Per-event extractor: yields the msg if this event is a `received` from
`src` to `dst`, else `none`. Used by `Trace.receivedOn`. -/
def Event.asReceivedOn (src dst : Vat) : Event → Option ByteArray
  | .sent _ _ _           => none
  | .received s d msg     => if s = src ∧ d = dst then some msg else none

/-- The send-history of a particular `(src, dst)` channel as
extracted from a trace. -/
def Trace.sentOn (t : Trace) (src dst : Vat) : List ByteArray :=
  t.filterMap (Event.asSentOn src dst)

/-- The receive-history of a particular `(src, dst)` channel as
extracted from a trace. -/
def Trace.receivedOn (t : Trace) (src dst : Vat) : List ByteArray :=
  t.filterMap (Event.asReceivedOn src dst)

/-- The Netlayer contract on a trace. Per-channel FIFO + no loss
(modulo "eventually" — formulated here as "receive history is a
*prefix* of send history" at every observation point) + no spontaneous
msgs (implied by the prefix relation). -/
structure Valid (t : Trace) : Prop where
  /-- For every channel, the received sequence is a prefix of the
  sent sequence at every observation point. This combines FIFO,
  no-loss-mid-trace, and no-spontaneous into one clean statement.
  "Eventually delivered" is the limit claim — observed at any finite
  point, the received prefix may be shorter than the sent sequence
  (msgs in flight), but it never reorders or skips. -/
  receivedIsPrefix :
    ∀ src dst, (t.receivedOn src dst) <+: (t.sentOn src dst)

/-- The empty trace is trivially valid. -/
theorem Valid.empty : Valid [] := by
  refine ⟨?_⟩
  intro src dst
  simp [Trace.receivedOn, Trace.sentOn]

end OcapnLean.Netlayer.Spec
