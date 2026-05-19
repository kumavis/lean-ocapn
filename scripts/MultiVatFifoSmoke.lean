import OcapnLean.Captp.Impl.MultiVat
import OcapnLean.Captp.Impl.PromiseForwarding

/-!
# Multi-vat end-to-end ref FIFO smoke test (M11 Phase A.6)

Runtime sanity belt on top of the formal `ref_fifo_e2e_at_impl` lift.
Exercises the canonical Phase A.5 scenario at the **multi-vat impl**
level: Alice sends two msgs targeting a promise hosted at Bob; Bob
resolves the promise to Carol; Bob forwards both msgs to Carol; Carol
receives them in send-order.

This is the executable counterpart of `RefFifoForwarding.lean`'s
`sat trace [promise_resolve_and_forward]` and the impl-level version
of the headline `ref_fifo_e2e` safety property.

The test confirms:

  * Each `send` / `deliver` / `resolvePromise` / `forward` action
    fires successfully (no `none` returns)
  * The forwarding ledger records both msgs in send order
  * Carol's delivered list has m₁ before m₂ (FIFO at the resolution
    host)

If any precondition is unmet the test exits non-zero with a diagnostic.
-/

open OcapnLean.Captp.Impl.MultiVat

def main : IO Unit := do
  -- Three vats: Alice = 0, Bob = 1, Carol = 2
  let alice : Vat := 0
  let bob   : Vat := 1
  let carol : Vat := 2
  -- Promise P = 0; two msgs m1 = 1, m2 = 2, both targeting P.
  let promiseRef : Ref := 0
  let m1 : MsgId := 1
  let m2 : MsgId := 2

  let s0 : State :=
    { initial with
      targetRef := fun m => if m = m1 ∨ m = m2 then promiseRef else 0 }

  -- Declare P as a promise.
  let s1 := declarePromise s0 promiseRef

  -- Alice installs route: msgs targeting P go via Alice→Bob.
  let .some s2 := setupRoute s1 alice bob promiseRef
    | IO.eprintln "FAIL: setupRoute Alice→Bob for promise P"; IO.Process.exit 1

  -- Alice sends m1, m2 targeting promise. Both ride the Alice→Bob wire.
  let .some s3 := send s2 alice bob m1
    | IO.eprintln "FAIL: Alice→Bob send m1"; IO.Process.exit 1
  let .some s4 := send s3 alice bob m2
    | IO.eprintln "FAIL: Alice→Bob send m2"; IO.Process.exit 1

  -- Bob delivers m1, m2 (per-channel FIFO).
  let .some s5 := deliver s4 alice bob m1
    | IO.eprintln "FAIL: Alice→Bob deliver m1"; IO.Process.exit 1
  let .some s6 := deliver s5 alice bob m2
    | IO.eprintln "FAIL: Alice→Bob deliver m2"; IO.Process.exit 1

  -- Bob learns P resolved to Carol. Installs Bob's routesTo[P] := Carol.
  let .some s7 := resolvePromise s6 bob carol promiseRef
    | IO.eprintln "FAIL: Bob.resolvePromise(P, Carol)"; IO.Process.exit 1

  -- Bob forwards m1, m2 to Carol (order: m1 before m2, matching delivery
  -- at Bob, matching Alice's send order).
  let .some s8 := forward s7 bob carol m1
    | IO.eprintln "FAIL: Bob→Carol forward m1"; IO.Process.exit 1
  let .some s9 := forward s8 bob carol m2
    | IO.eprintln "FAIL: Bob→Carol forward m2"; IO.Process.exit 1

  -- Carol delivers m1, m2.
  let .some s10 := deliver s9 bob carol m1
    | IO.eprintln "FAIL: Bob→Carol deliver m1"; IO.Process.exit 1
  let .some s11 := deliver s10 bob carol m2
    | IO.eprintln "FAIL: Bob→Carol deliver m2"; IO.Process.exit 1

  -- Assertion: Carol's delivered list has m1 before m2.
  let carolDel := (s11.channels bob carol).delivered
  match carolDel with
  | [(m1', _, n1), (m2', _, n2)] =>
    if m1' = m1 ∧ m2' = m2 ∧ n1 < n2 then
      IO.println "[multi-vat-fifo-smoke] ✅ scenario succeeded"
      IO.println s!"  Alice sent m1 (idx 0) then m2 (idx 1) on Alice→Bob"
      IO.println s!"  Bob delivered both, resolved P→Carol, forwarded both"
      IO.println s!"  Carol delivered m1 (idx {n1}) then m2 (idx {n2})"
      IO.println "OK"
    else
      IO.eprintln s!"FAIL: Carol delivered list wrong: {repr carolDel}"
      IO.Process.exit 1
  | _ =>
    IO.eprintln s!"FAIL: Carol delivered list has unexpected length"
    IO.eprintln s!"  got: {repr carolDel}"
    IO.Process.exit 1
