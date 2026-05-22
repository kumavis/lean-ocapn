import OcapnLean.Captp.Impl.MultiVat

/-!
# CapTP impl — promise resolution + forwarding (M11 Phase A.6)

Adds the impl-side counterparts of the Veil actions introduced in
`RefFifoForwarding.lean`:

* **`declarePromise`** — mark a ref as a promise.
* **`resolvePromise`** — vat `b` learns that promise `p` resolved to
  a value hosted at vat `c`; installs `routesTo[b, p] := c` so future
  forwarding lookups succeed.
* **`forward`** — vat `b` re-emits a previously-delivered msg targeting
  a resolved promise onto its forwarding channel (`b→c`).

These mirror the Veil action shapes precisely; the refinement file
`RefinementMultiVat.lean` proves `ref_fifo_e2e_lifts` on top.

## What's still trusted to the runtime

The impl-side **`forward` action's preconditions** include the
forwarding-preserves-order constraint
(`∀ M' K' K_orig, sentBy s M' = some s → ... → forwardedAt b c M' ≠ none`).
At Lean we expose this as a Boolean check; at runtime, a single-threaded
vat naturally satisfies it by forwarding msgs in receive order. The
runtime smoke test
(`scripts/MultiVatFifoSmoke.lean` — planned) exercises this.

The wire-protocol mapping (how the actual CapTP `op:deliver` with a
`desc:answer` target is converted into a forward) lives in
`Captp.Session` / `Captp.Run` and is trusted via interop tests.
-/

namespace OcapnLean.Captp.Impl.MultiVat

/-- Mark a ref as a promise. Idempotent (re-running has no effect). -/
def declarePromise (s : State) (p : Ref) : State :=
  { s with isPromise := fun r => if r = p then true else s.isPromise r }

/-- Vat `b` learns that promise `p` resolved to a value hosted at vat
`c`. Sets `resolvedTo p := some c` and installs `routesTo[b, p] := c`
so that subsequent forwarding lookups succeed.

Fails (`none`) if:
- `p` isn't declared a promise
- `p` is already resolved (to anything)
- `b` already routes `p` to a different vat than `c`. -/
def resolvePromise (s : State) (b c : Vat) (p : Ref) : Option State :=
  if ¬ s.isPromise p then none
  else if s.resolvedTo p ≠ none then none
  else
    match s.routesTo b p with
    | some existing => if existing = c then none  -- already resolved, no-op
                       else none                   -- conflict
    | none =>
      some { s with
             resolvedTo := fun r => if r = p then some c else s.resolvedTo r,
             routesTo := fun v r => if v = b ∧ r = p then some c else s.routesTo v r }

/-- True iff `msg` was previously delivered at `b` (from any sender). -/
def deliveredAtForwarder (s : State) (b : Vat) (msg : MsgId) : Bool :=
  (List.range 16).any fun srcIdx =>  -- bounded scan; sufficient for finite vats
    (s.channels srcIdx b).delivered.any (·.1 = msg)

/-- `forward b c m`: vat `b` re-emits previously-delivered msg `m`
onto the `b→c` wire. Fails if any precondition is unmet:
- `m`'s target ref isn't a promise resolved at `c`
- `b` doesn't route `m`'s target ref to `c`
- `m` already on `b→c` or already forwarded by `b` to `c`
- `m` not yet delivered at `b` from any sender
- forwarding-preserves-order is checked via the explicit ledger
  `forwardedAt` (Lean caller is responsible for sequencing). -/
def forward (s : State) (b c : Vat) (m : MsgId) : Option State :=
  let rf := s.targetRef m
  if ¬ s.isPromise rf then none
  else if s.resolvedTo rf ≠ some c then none
  else if s.routesTo b rf ≠ some c then none
  else
    let chan := s.channels b c
    if msgKnown chan m then none
    else if s.forwardedAt b c m ≠ none then none
    else if ¬ deliveredAtForwarder s b m then none
    else
      let chan' : ChannelState :=
        { chan with
          sendCursor := chan.sendCursor + 1,
          pending := chan.pending ++ [(m, chan.sendCursor)] }
      some { (updateChannel s b c chan') with
             forwardedAt := fun b' c' m' =>
               if b' = b ∧ c' = c ∧ m' = m then some chan.sendCursor
               else s.forwardedAt b' c' m' }

end OcapnLean.Captp.Impl.MultiVat
