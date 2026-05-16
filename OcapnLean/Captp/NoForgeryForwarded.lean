import Veil

set_option linter.dupNamespace false

/-!
# Capability unforgeability — forwarding case (M5 deferred)

Sister module to `OcapnLean.Captp.NoForgery`, extending its
direct-send result to the case where a peer that has already
*received* a reference can re-send it to a third peer. The
direct-send module models `send` as gated on the sender's
`exported` table; this one adds a `forward` action gated on the
sender's `imported` table.

We follow the spec model used elsewhere: positions are preserved
along a send chain (each session preserves the position labelling
of the inbound side; in a real OCapN session the wire's `desc:export
N` is the position the *sender* is using). That keeps the safety
property simple:

  * **direct-send case** (`NoForgery.lean`):
    `imported D P R → exported D' P R` — the position `P` of the
    imported reference matches some peer's `exported` at the same
    position.
  * **forwarding case** (this module):
    `imported D P R → ∃ S, exported S P R` — same conclusion, but
    the peer that holds the `exported` claim no longer needs to be
    the immediate sender; it's some peer along the chain.

The single ghost relation `chainAuth s p r` records that vat `s`
holds a chain of authority over `(p, r)` back to some original
exporter at the same position. It's set on either `setupAuthority`
or `receive`, and it's what gates `forward`.
-/

veil module CaptpNoForgeryForwarded

type vat
type pos
type oref

-- Trusted-bootstrap authority assertion: vat `s` itself exported
-- the local object `r` at position `p`. The unique entry-point for
-- authority into the system.
relation exported : vat → pos → oref → Prop
-- Wire snapshot: a message in flight from `s` to `d` carries the
-- binding `(p, r)`.
relation onWire   : vat → vat → pos → oref → Prop
-- A vat's import table: refs it has *received* from a peer.
relation imported : vat → pos → oref → Prop
-- Ghost: vat `s` has a legitimate chain of authority over `(p, r)`,
-- either by being the original exporter at that position or by
-- having received a chain of forwards starting from one. This is
-- the relation `forward` is gated on.
relation chainAuth : vat → pos → oref → Prop

#gen_state

after_init {
  exported V P R := False;
  imported V P R := False;
  onWire S D P R := False;
  chainAuth V P R := False
}

-- The single trusted entry-point for authority: vat `v` declares
-- it exports its own local object `r` at position `p`. Both the
-- direct-send and forwarding paths derive from this.
action setupAuthority (v : vat) (p : pos) (r : oref) = {
  exported v p r := True;
  chainAuth v p r := True
}

-- Direct send: vat `s` has authority via its own `exported` claim.
-- (Mirror of the direct-send module's `send`; also writes
-- `chainAuth` so the inductive invariant `wire_implies_chain`
-- can rely on a uniform precondition shared with `forward`.)
action send (s d : vat) (p : pos) (r : oref) = {
  require s ≠ d
  require exported s p r
  onWire s d p r := True;
  chainAuth s p r := True
}

-- Forwarded send: vat `s` has authority via the inductive `chainAuth`
-- relation. This is the new path. `s` may or may not be the original
-- exporter — anywhere along the chain is fair game.
action forward (s d : vat) (p : pos) (r : oref) = {
  require s ≠ d
  require chainAuth s p r
  onWire s d p r := True
}

-- Receiver consumes an in-flight ref into both `imported` (for
-- application use) and `chainAuth` (so it can in turn forward).
action receive (s d : vat) (p : pos) (r : oref) = {
  require onWire s d p r
  imported d p r := True;
  chainAuth d p r := True
}

------------------------------------------------------------------------
-- Safety: forwarding-case no-forgery
------------------------------------------------------------------------

-- Imported ref ⇒ *some* peer exported it (possibly not the
-- immediate sender). This is the forwarding-case strengthening of
-- the direct-send module's `no_forgery` safety property.
safety [no_forgery_forwarded]
  imported D P R → ∃ S, exported S P R

------------------------------------------------------------------------
-- Supporting inductive invariants
------------------------------------------------------------------------

-- The chain-of-authority relation is always backed by some original
-- exporter. Set inductively at `setupAuthority` (with `S = V`) and
-- preserved by `receive` (which only extends `chainAuth` from an
-- `onWire` entry that itself is backed by a chain entry).
invariant [chain_implies_some_exported]
  chainAuth V P R → ∃ S, exported S P R

-- Anything on the wire was emitted by a vat with a chain of
-- authority over it. Holds because both `send` and `forward`
-- imply the sender has `chainAuth` (`send` adds it via the same
-- `setupAuthority` that sets `exported`; `forward` requires it
-- explicitly).
invariant [wire_implies_chain]
  onWire S D P R → chainAuth S P R

-- Every imported ref carries a chain of authority. Preserved by
-- `receive`: it sets both `imported` and `chainAuth` from an
-- `onWire` entry whose chainAuth is already established by
-- `wire_implies_chain`.
invariant [imported_implies_chain]
  imported D P R → chainAuth D P R

#gen_spec

#check_invariants

end CaptpNoForgeryForwarded
