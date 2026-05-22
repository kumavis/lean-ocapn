import OcapnLean.Netlayer
import OcapnLean.Netlayer.Spec

/-!
# ObservableNetlayer — netlayer with introspection (M11 Phase A.7)

Extends the base `Netlayer` with an introspection method that exposes
the per-channel send/receive history. Used by the runtime FIFO proof
to bridge from concrete netlayer state to abstract `MultiVat.State`.

**Why a separate subtype:** the production `Netlayer` (TCP/UDS/WS)
shouldn't grow an introspection method — those impls don't naturally
hold an inspectable Lean-side history; the channel state lives in the
OS kernel / network. Observable is provided only by impls that can
honestly answer the introspection question, primarily the in-process
netlayer used for the Phase A.7 smoke + runtime proof.
-/

namespace OcapnLean.Netlayer

open OcapnLean.Netlayer.Spec

/-- A netlayer whose per-channel history is observable from Lean. -/
structure ObservableNetlayer where
  /-- The underlying message-oriented endpoint. -/
  net : Netlayer
  /-- Snapshot the global event history. Concrete impls return the
  current append-only trace of `sent` / `received` events. -/
  snapshot : IO Trace

/-- Sugar: send a msg via the wrapped netlayer. -/
@[inline] def ObservableNetlayer.sendMessage
    (n : ObservableNetlayer) (bytes : ByteArray) : IO Unit :=
  n.net.sendMessage bytes

/-- Sugar: receive a msg via the wrapped netlayer. -/
@[inline] def ObservableNetlayer.recvMessage?
    (n : ObservableNetlayer) : IO (Option ByteArray) :=
  n.net.recvMessage?

/-- Sugar: close. -/
@[inline] def ObservableNetlayer.close (n : ObservableNetlayer) : IO Unit :=
  n.net.close

/-! ## Projection: Spec.Trace → channel state

These helpers extract per-channel cursors / pending / delivered
information from a Spec.Trace. They're the bridge from the abstract
trace (which any `ObservableNetlayer` can produce) to the data shape
the FIFO proof talks about. -/

namespace Spec

/-- For a given `(src, dst)` channel, count the number of msgs sent
on that channel. This is the channel's `sendCursor`. -/
def Trace.sendCount (t : Trace) (src dst : Vat) : Nat :=
  (t.sentOn src dst).length

/-- For a given `(src, dst)` channel, count the number of msgs
received on that channel. This is the channel's `recvCursor`. -/
def Trace.recvCount (t : Trace) (src dst : Vat) : Nat :=
  (t.receivedOn src dst).length

/-- The pending (in-flight) msgs on `(src, dst)`: the suffix of the
sent list past the receive count. Each msg is paired with its
send-index. -/
def Trace.pendingOn (t : Trace) (src dst : Vat) :
    List (ByteArray × Nat) :=
  let sent := t.sentOn src dst
  let r    := t.recvCount src dst
  sent.drop r |>.zipIdx r

/-- The delivered msgs on `(src, dst)`: the prefix of the sent list
up to the receive count. Each msg is paired with `(sendIdx, recvIdx)`
which (by per-channel FIFO) coincide. -/
def Trace.deliveredOn (t : Trace) (src dst : Vat) :
    List (ByteArray × Nat × Nat) :=
  let sent := t.sentOn src dst
  let r    := t.recvCount src dst
  (sent.take r).zipIdx |>.map (fun (msg, i) => (msg, i, i))

end Spec

end OcapnLean.Netlayer
