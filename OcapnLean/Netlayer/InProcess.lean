import OcapnLean.Netlayer
import OcapnLean.Netlayer.Spec
import OcapnLean.Netlayer.Observable

/-!
# In-process netlayer (M11 Phase A.7)

A concrete `ObservableNetlayer` that runs entirely inside one Lean
process. Each ordered `(src, dst)` channel is a `(sent, received)` pair
of arrays; the global state lives in an `IO.Ref` and all
sends/recvs/snapshots go through it atomically (Lean's `IO.Ref.modify`
is atomic).

This is the netlayer used by:

* The multi-vat smoke test (`scripts/MultiVatFifoSmoke.lean`).
* The Phase A.7 runtime FIFO proof (eventually): the
  `ObservableNetlayer.snapshot` is the bridge from concrete runtime
  state to the abstract `Spec.Trace`.

**Concurrency model:** the global `IO.Ref` is updated via `modifyGet`,
which Lean implements as a CAS-style atomic update. Each call is a
single transition in the LTS model used by the runtime FIFO proof.

For multi-threaded use we'd want a real mutex, but the smoke runs
peer loops as sequential interleavings, so the `IO.Ref` model is
sufficient — and verifiable.

**Trusted boundary:** the *content* of the spec is proved
analogously in `OcapnLean.Captp.RuntimeFifo` over a parallel-Lean
LTS — `InvDeliverIsPrefix.reachable` shows that every reachable
runtime state has `received` as a true prefix of `sent` on every
channel (size bound + per-index payload equality).

What's *not* yet formalised: the bridge from the LTS proof to a
direct `Spec.Valid` over `snapshot`. The bridge is mechanical
plumbing (Array.toList prefix from indexed equality), but doesn't
add conceptual content — the LTS's `InvDeliverIsPrefix` already
proves the substance.

The channel store is a `List ((Vat × Vat) × ChannelQueue)`. For
small numbers of peers (the smoke uses 3) this is fine; a hash-map
implementation could replace it with no semantic change.
-/

namespace OcapnLean.Netlayer.InProcess

open OcapnLean.Netlayer
open OcapnLean.Netlayer.Spec

/-- Per-channel state stored inside the in-process network. -/
structure ChannelQueue where
  /-- All msgs ever sent on this channel, in order. -/
  sent     : Array ByteArray := #[]
  /-- All msgs ever received on this channel, in order. -/
  received : Array ByteArray := #[]

/-- Default-empty channel queue. -/
instance : Inhabited ChannelQueue := ⟨{}⟩

/-- A pair of vat ids in canonical order. Ordered (src, dst). -/
abbrev ChanKey := Vat × Vat

/-- The full in-process network state: per-pair channel queues as an
association list. -/
structure NetworkState where
  channels : List (ChanKey × ChannelQueue) := []

instance : Inhabited NetworkState := ⟨{}⟩

/-- Look up the queue for a given channel; default to empty. -/
def NetworkState.get (s : NetworkState) (k : ChanKey) : ChannelQueue :=
  match s.channels.find? (·.1 = k) with
  | some (_, q) => q
  | none        => default

/-- Update the queue for a given channel. Replaces if present, else
appends. -/
def NetworkState.set (s : NetworkState) (k : ChanKey) (q : ChannelQueue) :
    NetworkState :=
  let filtered := s.channels.filter (·.1 ≠ k)
  { channels := (k, q) :: filtered }

/-- A live in-process network: a single `IO.Ref`-protected
`NetworkState`. -/
structure Network where
  state : IO.Ref NetworkState

/-- Allocate a fresh in-process network. -/
def Network.new : IO Network := do
  let ref ← IO.mkRef {}
  return { state := ref }

/-- Append a msg to the `(src, dst)` channel's `sent` list. -/
def Network.send (n : Network) (src dst : Vat) (msg : ByteArray) : IO Unit := do
  n.state.modify fun s =>
    let q := s.get (src, dst)
    s.set (src, dst) { q with sent := q.sent.push msg }

/-- Pop the next undelivered msg from the `(src, dst)` channel and
record it in `received`. Returns `none` if no undelivered msg is in
flight. -/
def Network.recv? (n : Network) (src dst : Vat) : IO (Option ByteArray) := do
  n.state.modifyGet fun s =>
    let q := s.get (src, dst)
    let nReceived := q.received.size
    if h : nReceived < q.sent.size then
      let msg := q.sent[nReceived]
      let q' := { q with received := q.received.push msg }
      (some msg, s.set (src, dst) q')
    else
      (none, s)

/-- Capture the network's current per-channel state as a `Spec.Trace`.
Emits all `.sent` events first (in channel-order), then all `.received`
events. Within a channel, both lists preserve their original order. -/
def Network.snapshot (n : Network) : IO Trace := do
  let s ← n.state.get
  let mut sentEvents : Trace := []
  let mut recvEvents : Trace := []
  for ((src, dst), ch) in s.channels do
    for msg in ch.sent do
      sentEvents := sentEvents ++ [.sent src dst msg]
    for msg in ch.received do
      recvEvents := recvEvents ++ [.received src dst msg]
  return sentEvents ++ recvEvents

/-- Build a per-peer `Netlayer` view: the peer can send to `dst` and
recv from `src` over this network. -/
def Network.netlayerFor (n : Network) (self peer : Vat) : Netlayer :=
  { sendMessage  := n.send self peer
  , recvMessage? := n.recv? peer self
  , close        := pure () }

/-- Build an `ObservableNetlayer` wrapping `netlayerFor` with the
network's `snapshot`. -/
def Network.observableFor (n : Network) (self peer : Vat) : ObservableNetlayer :=
  { net      := n.netlayerFor self peer
  , snapshot := n.snapshot }

end OcapnLean.Netlayer.InProcess
