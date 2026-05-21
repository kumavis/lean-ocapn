import OcapnLean.Captp.Bootstrap
import OcapnLean.Captp.Client
import OcapnLean.Captp.Run
import OcapnLean.Captp.Session
import OcapnLean.Netlayer.Tcp
import OcapnLean.Syrup.Extended

/-!
# Lean ↔ Endo interop driver

Drives the Lean `Captp.Client` against the **@endo/ocapn** test server
over `tcp-testing-only`. Replaces the older `interop-endo` CI job
that was actually `python-suite ↔ endo` (a parity check) and never
exercised any ocapn-lean code.

The scenarios below correspond to the canonical CapTP wire-shape
exercises that any conforming peer should support. Each scenario
reuses the same well-known objects the upstream Python test suite
uses (`projects/ocapn-test-suite/README.md`), so the driver can be
pointed at any peer that exposes those objects — Endo for now, and
in principle Goblins / Ridley once they expose the same swissnums.

## Scenarios

1. **Echo round-trip** — `<op:deliver echo [args…] False rmd>`,
   expect `[fulfill [args…]]`. Validates: handshake, fetch, deliver
   with rmd, expectFulfill, Syrup byte round-trip.
2. **Greeter callback** — `<op:deliver greeter [listener] False False>`,
   expect a separate `<op:deliver listener ["Hello"] False False>`.
   Validates: bidirectional delivery, callback to an import position
   we allocated.
3. **Promise pipelining** — fetch the Car Factory Builder, deliver to
   it with an *answer* slot (not rmd), then **pipeline** a send to
   `<desc:answer that-slot>` BEFORE awaiting the first answer.
   Resolve and check both. Validates: answer-position handling,
   pipelined sends before the target resolves.

Each scenario prints `[interop-endo] <name> ok` on success. The
script exits 0 on full pass, 1 on any failure. Run as:

    lake exe client-vs-endo -- --port 22046
-/

open OcapnLean OcapnLean.Captp OcapnLean.Captp.Session OcapnLean.Syrup
     Netlayer
open Std.Net

def parsePort : List String → UInt16
  | []                       => 22046
  | "--port" :: n :: _       => (n.toNat?.getD 22046).toUInt16
  | _ :: rest                => parsePort rest

/-- Stable test-side OCapN designator (32 ASCII bytes). Used in the
`<ocapn-peer …>` locator we send during the handshake. -/
def testClientDesignator : String :=
  "leaninteropbeefbeefbeefbeefbeef!"

def buildClientLocator : ValueExt :=
  .record (.sym "ocapn-peer".toUTF8.toList)
    [ .sym "tcp-testing-only".toUTF8.toList
    , .str testClientDesignator.toUTF8.toList
    , .dict []
    ]

/-- `<desc:answer N>` constructor (no helper in Session.lean yet). -/
def buildDescAnswer (pos : Nat) : ValueExt :=
  .record (.sym Session.descAnswerSym) [.int (Int.ofNat pos)]

/-! ## Scenario runners. -/

/-- Scenario 1 — echo round-trip. -/
def runEchoRoundtrip (s : Captp.Client.Session) : IO Unit := do
  let fetchRmd ← Captp.Client.fetch s Captp.Bootstrap.echoGcSwiss
  let echoRefVal ← Captp.Client.expectFulfill s fetchRmd
  let echoPos := match Session.extractImportObjPos echoRefVal with
                 | some n => n
                 | none   => 0
  let args : List ValueExt :=
    [ .str "hi".toUTF8.toList, .int 1, .bool false
    , .float64 0x3FF0_0000_0000_0000 ]
  let (some rmd, _) ← Captp.Client.deliver s
                       (Session.buildDescExport echoPos) args
                       (withRmd := true)
    | throw (IO.userError "[interop-endo] echo: deliver did not allocate rmd")
  let got ← Captp.Client.expectFulfill s rmd
  let expected := Encode.encodeExt (.list args)
  let actual   := Encode.encodeExt got
  if expected ≠ actual then
    throw (IO.userError s!"[interop-endo] echo: round-trip mismatch")
  IO.println "[interop-endo] echo round-trip ok"

/-- Scenario 2 — greeter callback. We allocate an import-object position
for our listener, send `greeter [our-listener]`, and await a deliver
TO our listener with payload `["Hello"]`. -/
def runGreeterCallback (s : Captp.Client.Session) : IO Unit := do
  let fetchRmd ← Captp.Client.fetch s Captp.Bootstrap.greeterSwiss
  let greeterRefVal ← Captp.Client.expectFulfill s fetchRmd
  let greeterPos := match Session.extractImportObjPos greeterRefVal with
                    | some n => n
                    | none   => 0
  let listenerPos ← s.nextImport
  let (_, _) ← Captp.Client.deliver s
                 (Session.buildDescExport greeterPos)
                 [ Session.buildDescImportObj listenerPos ]
                 (withRmd := false)
  -- Endo's greeter calls back to our listener with `["Hello"]`.
  let callback ← Captp.Client.expectMessageTo s listenerPos
  match Session.parseOpDeliver callback with
  | some (_, args, _, _) =>
    -- We accept any args shape that contains the string "Hello" — Endo
    -- might wrap differently. Check at least one arg is the bytes/str "Hello".
    let helloBytes := "Hello".toUTF8.toList
    let hasHello := args.any fun
      | .str s => s = helloBytes
      | .bytes s => s = helloBytes
      | _ => false
    unless hasHello do
      throw (IO.userError s!"[interop-endo] greeter: callback args did not include \"Hello\"")
    IO.println "[interop-endo] greeter callback ok"
  | none => throw (IO.userError "[interop-endo] greeter: callback was not a parseable op:deliver")

/-- Scenario 3 — promise pipelining via Car Factory Builder.

The full 3-hop chain from `projects/ocapn-test-suite/tests/op_deliver.py`'s
`test_deliver_promise_pipeline`:

  1. Deliver to `carFactoryBuilder` (no args), allocate answer slot
     for the resulting car-factory ref.
  2. **Pipelined:** deliver to `<desc:answer factoryAns>` with
     `[[color, model]]` args, allocate answer slot for the car ref.
  3. **Pipelined again:** deliver to `<desc:answer carAns>` with
     no args + an rmd. Expect a fulfill of `"Vroom! I am a {color}
     {model} car!"`.

The receiver must accept each send addressed at the still-unresolved
answer of the previous step and propagate the actual delivery
through the chain in order. -/
def runPipelineCarFactory (s : Captp.Client.Session) : IO Unit := do
  let fetchRmd ← Captp.Client.fetch s Captp.Bootstrap.carFactoryBuilderSwiss
  let builderRefVal ← Captp.Client.expectFulfill s fetchRmd
  let builderPos := match Session.extractImportObjPos builderRefVal with
                    | some n => n
                    | none   => 0
  -- Step 1: deliver to builder with answer slot for the factory ref.
  let (_, some factoryAns) ← Captp.Client.deliver s
                              (Session.buildDescExport builderPos) []
                              (withAnswer := true) (withRmd := false)
    | throw (IO.userError "[interop-endo] pipeline: builder deliver did not allocate answer slot")
  -- Step 2: PIPELINED — deliver to <desc:answer factoryAns>. The
  -- car-factory handler expects exactly one arg shaped as
  -- `[<color-sym>, <model-sym>]` (a single 2-element list).
  let color := "red".toUTF8.toList
  let model := "zoomracer".toUTF8.toList
  let (_, some carAns) ← Captp.Client.deliver s
                          (buildDescAnswer factoryAns)
                          [ .list [.sym color, .sym model] ]
                          (withAnswer := true) (withRmd := false)
    | throw (IO.userError "[interop-endo] pipeline: factory deliver did not allocate answer slot")
  -- Step 3: PIPELINED AGAIN — deliver to <desc:answer carAns> with
  -- no args + an rmd. The car responds with the "Vroom! …" string.
  let (some driveRmd, _) ← Captp.Client.deliver s
                            (buildDescAnswer carAns) []
                            (withRmd := true)
    | throw (IO.userError "[interop-endo] pipeline: drive deliver did not allocate rmd")
  let result ← Captp.Client.expectFulfill s driveRmd
  match result with
  | .str bytes =>
    let strActual := String.fromUTF8! ⟨bytes.toArray⟩
    let expected := s!"Vroom! I am a red zoomracer car!"
    if strActual = expected then
      IO.println s!"[interop-endo] pipelining ok ({strActual})"
    else
      throw (IO.userError s!"[interop-endo] pipeline: car string mismatch: got {strActual}")
  | _ =>
    throw (IO.userError s!"[interop-endo] pipeline: expected string result")

def main (args : List String) : IO Unit := do
  let port := parsePort args
  let addr : SocketAddress := Tcp.v4 Tcp.loopback port
  IO.println s!"[interop-endo] connecting to 127.0.0.1:{port}"
  let s ← Captp.Client.Session.connect addr buildClientLocator
            (captpVersion := "1.0") (framing := .raw)
  Captp.Client.handshake s
  IO.println "[interop-endo] handshake ok"
  try
    runEchoRoundtrip s
    runGreeterCallback s
    runPipelineCarFactory s
  catch e =>
    Captp.Client.Session.close s
    IO.eprintln s!"FAIL: {e}"
    IO.Process.exit 1
  Captp.Client.Session.close s
  IO.println "OK"
