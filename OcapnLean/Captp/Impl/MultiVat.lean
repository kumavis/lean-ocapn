import OcapnLean.Captp.Impl

/-!
# CapTP impl — N-vat compositional model (M11 Phase A.6)

`OcapnLean.Captp.Impl` models a single peer's view of one CapTP session.
This module wraps it into an N-vat composition so we can talk about
multi-vat properties (the three P1 tiers — fail-stop FIFO, ref FIFO at
routing target, ref FIFO across forwarding) at the impl level.

## What's modeled here

* **Per-vat impl state**: each vat owns one `Impl.State` (its local
  import/export tables, alive flag, etc.).
* **Per-pair channels**: for each ordered (src, dst) pair of vats, a
  channel state recording in-flight pending msgs, delivered msgs, and
  per-channel cursors.

Channels are modeled at the *protocol* abstraction level — ordered
queues of opaque `MsgId`s plus cursors — rather than at the byte/wire
level. The TCP/WebSocket netlayer is trusted to keep per-channel FIFO,
as verified by the interop test suite.

## What's *not* modeled here (yet)

* **Refs, routing, origin tracking** — added in Phase A.6's refs/routing
  step (mirroring `RefFifo.lean`'s state additions).
* **Promises, resolution, forwarding** — added in
  `Impl/PromiseForwarding.lean` (mirroring `RefFifoForwarding.lean`).
* **A runnable event loop** — this module is pure-Lean state + step
  functions; the existing `Captp.Session` / `Captp.Run` provide the
  runnable single-peer event loop. A multi-vat runtime test
  (`scripts/MultiVatFifoSmoke.lean`) wires three of those single-peer
  runtimes together via in-process channels for end-to-end exercise.

## Why this is the right level for the proof

The refinement story decomposes:

  1. **Spec-level**: `Channels.lean` proves fail-stop FIFO over the
     abstract relations.
  2. **Multi-vat impl model (this file)**: a concrete Lean state where
     each cursor and queue is a `Nat` / `List`, and `send` / `deliver`
     are total functions.
  3. **Refinement (`RefinementMultiVat.lean`)**: a simulation relation
     mapping (2) to (1)'s abstract state, plus lifting lemmas that turn
     spec-level FIFO into impl-level FIFO.
  4. **Wire-level (`Captp.Session`, `Captp.Run`, `Netlayer`)**: trusted
     to faithfully realise (2)'s atomic actions on real bytes. Verified
     by interop tests, not formal refinement.
-/

namespace OcapnLean.Captp.Impl.MultiVat

/-- Vat identifier. Abstract; we use `Nat` for executability. -/
abbrev Vat := Nat

/-- Opaque message identifier. The protocol-level abstraction — at the
wire level a msg has a payload, target ref, etc., but for FIFO reasoning
we only need msg identity and the order of appearance on each channel. -/
abbrev MsgId := Nat

/-- Opaque reference identifier. Object identity across vats; used as
the routing key. -/
abbrev Ref := Nat

/-- State of one directed channel from a `src` vat to a `dst` vat.

The two lists `pending` and `delivered` together hold every msg ever
*sent* on this channel:

* `pending` — msgs in flight (sent but not yet delivered), in FIFO
  order (head = next to deliver).
* `delivered` — msgs already delivered, paired with their send-index
  and deliver-index.

Cursors `sendCursor` / `recvCursor` are the next index to assign on
send / next index to expect on deliver. Together they enforce the
per-channel FIFO invariant. -/
structure ChannelState where
  /-- Next index to assign when sending. -/
  sendCursor : Nat
  /-- Next index to expect when receiving. -/
  recvCursor : Nat
  /-- In-flight msgs with the send-index they were assigned. Head-of-list
  is the next to deliver. -/
  pending : List (MsgId × Nat)
  /-- Delivered msgs with `(msgId, sendIdx, deliverIdx)`. -/
  delivered : List (MsgId × Nat × Nat)
deriving Repr, Inhabited

/-- Empty channel — both cursors at 0, no msgs in flight or delivered. -/
def ChannelState.empty : ChannelState :=
  { sendCursor := 0, recvCursor := 0, pending := [], delivered := [] }

/-- N-vat compositional state: per-vat `Impl.State` (peers' local view)
plus per-ordered-pair `ChannelState` (the wire between two vats), plus
the refs/routing/origin tracking introduced for ref-FIFO reasoning. -/
structure State where
  /-- Each vat's local single-peer Impl state. Functions to allow
  unbounded vat universe; for any vat not yet activated, the default
  is `Impl.initial`. -/
  peers : Vat → Impl.State
  /-- Channels indexed by `(src, dst)`. The default (for never-used
  pairs) is the empty channel. -/
  channels : Vat → Vat → ChannelState
  /-- Routing table: `routesTo v r = some w` means vat `v` routes msgs
  targeting ref `r` via the `v→w` channel. `none` means no route yet
  installed. Functional by construction (the type is `Option Vat`). -/
  routesTo : Vat → Ref → Option Vat
  /-- Origin tracking: `sentBy m = some v` means msg `m` was originated
  by vat `v`. `none` means msg hasn't been originated yet. Functional
  by construction. -/
  sentBy : MsgId → Option Vat
  /-- Target-ref oracle: each msg targets a specific ref. Fixed per
  msg (we never mutate this); analogous to the Veil module's
  `function targetRef : msg → ref`. -/
  targetRef : MsgId → Ref
  /-- Promises (a kind of ref). Used by the resolvePromise / forward
  actions in `Impl/PromiseForwarding.lean`. -/
  isPromise : Ref → Bool
  /-- Resolution: `resolvedTo r = some v` means promise `r` has resolved
  to a value hosted at vat `v`. Set once (functional by construction). -/
  resolvedTo : Ref → Option Vat
  /-- Forwarding ledger: `forwardedAt b c m` records the send-cursor
  index at which `b` forwarded `m` onto the `b→c` wire. `none` when
  not yet forwarded. -/
  forwardedAt : Vat → Vat → MsgId → Option Nat

/-- Initial multi-vat state: every vat in its `Impl.initial`
configuration, every channel empty, no routes installed, no msgs
originated. `targetRef` is whatever oracle the caller supplies — we
default to `0` (all msgs target a single ref); concrete uses can
override the field. -/
def initial : State where
  peers _      := Impl.initial
  channels _ _ := ChannelState.empty
  routesTo _ _ := none
  sentBy _     := none
  targetRef _  := 0
  isPromise _  := false
  resolvedTo _ := none
  forwardedAt _ _ _ := none

/-- True iff `msg` is currently in flight or already delivered on the
`src → dst` channel. Used by `send`'s per-channel uniqueness guard. -/
def msgKnown (chan : ChannelState) (msg : MsgId) : Bool :=
  chan.pending.any (·.1 = msg) || chan.delivered.any (·.1 = msg)

/-- Update only the `(src, dst)` channel. -/
def updateChannel (s : State) (src dst : Vat) (chan : ChannelState) : State :=
  { s with
    channels := fun s' d' => if s' = src ∧ d' = dst then chan else s.channels s' d' }

/-! ## Actions — mirror the Veil module's `send` / `deliver`. -/

/-- Update only the per-vat routing table. -/
def updateRoutes (s : State) (v : Vat) (rf : Ref) (target : Option Vat) : State :=
  { s with routesTo := fun v' r' => if v' = v ∧ r' = rf then target else s.routesTo v' r' }

/-- `setupRoute v dst rf`: vat `v` installs a routing entry — msgs
targeting `rf` will go via the `v→dst` channel. Idempotent (overwrites
a same-target entry; fails on a conflicting one). Mirrors the Veil
`setupRoute` action. -/
def setupRoute (s : State) (v dst : Vat) (rf : Ref) : Option State :=
  match s.routesTo v rf with
  | some existing => if existing = dst then some s else none
  | none          => some (updateRoutes s v rf (some dst))

/-- `handoff g r e rf`: gifter `g` introduces receiver `r` to ref `rf`
(hosted at exporter `e`). Adds `r → e` routing for `rf`, but only if
`r` doesn't already have a conflicting route (idempotent / additive).
Mirrors the Veil `handoff` action. -/
def handoff (s : State) (g r e : Vat) (rf : Ref) : Option State :=
  if s.routesTo g rf ≠ some e then none  -- gifter must know the route
  else
    match s.routesTo r rf with
    | some existing => if existing = e then some s else none
    | none          => some (updateRoutes s r rf (some e))

/-- `send src dst msg`: vat `src` puts `msg` onto its outbound channel
to `dst`. Fails (returns `none`) if any of the Veil-side preconditions
are unmet: msg already on this wire / msg already originated /
sender's routing for the msg's target ref doesn't match `dst`. -/
def send (s : State) (src dst : Vat) (msg : MsgId) : Option State :=
  let chan := s.channels src dst
  if msgKnown chan msg then none
  else if s.sentBy msg ≠ none then none  -- never originated
  else if s.routesTo src (s.targetRef msg) ≠ some dst then none  -- not routed
  else
    let chan' : ChannelState :=
      { chan with
        sendCursor := chan.sendCursor + 1,
        pending := chan.pending ++ [(msg, chan.sendCursor)] }
    some { (updateChannel s src dst chan') with
           sentBy := fun m => if m = msg then some src else s.sentBy m }

/-- `deliver src dst msg`: vat `dst` consumes the next pending msg on
the `src → dst` channel and records it as delivered. The msg must match
the head of pending — per-channel FIFO is enforced at the action site
(mirrors the Veil precondition `sentAt s d m (recvCursor s d)`). -/
def deliver (s : State) (src dst : Vat) (msg : MsgId) : Option State :=
  let chan := s.channels src dst
  match chan.pending with
  | (msg', sendIdx) :: rest =>
    if msg' = msg then
      let chan' : ChannelState :=
        { chan with
          recvCursor := chan.recvCursor + 1,
          pending := rest,
          delivered := chan.delivered ++ [(msg', sendIdx, chan.recvCursor)] }
      some (updateChannel s src dst chan')
    else
      none
  | [] => none

/-! ## Wire-level lookups for the simulation relation.

These project the impl-level channel state into "is this msg pending? /
delivered? / sent-at index? / delivered-at index?" predicates that match
the shape of the Veil module's relations. The refinement file uses
these as the bridge between concrete impl state and abstract spec
state. -/

/-- `pending s d m`: msg `m` is in flight on the `src → dst` channel. -/
def pending (s : State) (src dst : Vat) (msg : MsgId) : Prop :=
  ∃ k, (msg, k) ∈ (s.channels src dst).pending

/-- `delivered s d m`: msg `m` has been delivered on `src → dst`. -/
def delivered (s : State) (src dst : Vat) (msg : MsgId) : Prop :=
  ∃ k j, (msg, k, j) ∈ (s.channels src dst).delivered

/-- `sentAt s d m k`: msg `m` was assigned send-index `k` on
`src → dst`. (Either in-flight or already delivered.) -/
def sentAt (s : State) (src dst : Vat) (msg : MsgId) (k : Nat) : Prop :=
  (msg, k) ∈ (s.channels src dst).pending ∨
  (∃ j, (msg, k, j) ∈ (s.channels src dst).delivered)

/-- `deliveredAt s d m j`: msg `m` was delivered at index `j` on
`src → dst`. -/
def deliveredAt (s : State) (src dst : Vat) (msg : MsgId) (j : Nat) : Prop :=
  ∃ k, (msg, k, j) ∈ (s.channels src dst).delivered

end OcapnLean.Captp.Impl.MultiVat
