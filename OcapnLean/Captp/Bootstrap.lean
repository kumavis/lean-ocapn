import OcapnLean.Captp.Run
import OcapnLean.Syrup.Extended

/-!
# Bootstrap object registry

The OCapN test suite expects an implementation to expose a fixed set
of objects at well-known swissnums (see
`projects/ocapn-test-suite/README.md`). This module provides:

  * the swissnum constants the test suite uses,
  * a small `Registry` mapping swissnums to handlers,
  * reference handler implementations for the simplest objects
    (`Echo GC`, `Greeter`, `Car Factory builder` / `Car Factory` /
    `Car`),
  * a dispatcher that recognises `op:deliver` of the form
        `<op:deliver <desc:export 0> [fetch <swissnum>] ...>`
    and routes the call to the registry, returning a result value the
    `runHandler` event loop forwards to the wire.

The dispatcher is intentionally minimal — it doesn't model the
session's export/answer tables, GC ref-counting, three-party
handoffs, or any of the structure needed for the full test suite to
pass. It is enough to demonstrate that end-to-end CapTP-shaped
message exchange now flows through verified-spec code and
reference-impl plumbing.
-/

namespace OcapnLean.Captp.Bootstrap

open OcapnLean.Syrup OcapnLean.Captp

/-- A swissnum is the ASCII bytes spelling out the test-suite's
identifier. -/
abbrev Swissnum := List UInt8

/-- Reference swissnums from `projects/ocapn-test-suite/README.md`. -/
def carFactoryBuilderSwiss : Swissnum := "JadQ0++RzsD4M+40uLxTWVaVqM10DcBJ".toUTF8.toList
def echoGcSwiss            : Swissnum := "IO58l1laTyhcrgDKbEzFOO32MDd6zE5w".toUTF8.toList
def greeterSwiss           : Swissnum := "VMDDd1voKWarCe2GvgLbxbVFysNzRPzx".toUTF8.toList
def promiseResolverSwiss   : Swissnum := "IokCxYmMj04nos2JN1TDoY1bT8dXh6Lr".toUTF8.toList
def sturdyrefEnlivenerSwiss: Swissnum := "gi02I1qghIwPiKGKleCQAOhpy3ZtYRpB".toUTF8.toList

/-- A handler interprets a list of arguments and returns a value. -/
abbrev Handler := List ValueExt → IO ValueExt

/-- Swissnum → Handler routing table. -/
structure Registry where
  bindings : List (Swissnum × Handler)

namespace Registry

/-- Look up a swissnum in the registry. -/
def lookup (r : Registry) (s : Swissnum) : Option Handler :=
  (r.bindings.find? (·.1 = s)).map (·.2)

/-- Add (or shadow) a binding. -/
def add (r : Registry) (s : Swissnum) (h : Handler) : Registry :=
  { bindings := (s, h) :: r.bindings }

end Registry

/-! ## Reference handler implementations. -/

/-- Echo GC: return arguments in the same order. -/
def echoGc : Handler := fun args => pure (.list args)

/-- Greeter: ignore the argument (would normally forward "Hello"
to it via another `op:deliver`); for now, just return unit-ish. -/
def greeter : Handler := fun _ => pure (.bool true)

/-- Render a `Car` value as the string the test expects. -/
def renderCar (color model : List UInt8) : ValueExt :=
  let s := "Vroom! I'm a ".toUTF8.toList ++ color ++ " ".toUTF8.toList
           ++ model ++ " car!".toUTF8.toList
  .str s

/-- Car Factory: given a sequence of `[model, color]` pairs, return a
list of car descriptions. (A full impl would return live references,
not strings; this is enough to demonstrate dispatch.) -/
def carFactory : Handler := fun args =>
  match args with
  | [.list pairs] => do
    let cars : List ValueExt ← pairs.mapM fun pair => do
      match pair with
      | .list [.sym model, .sym color] => pure (renderCar color model)
      | _ => throw (IO.userError "Car Factory: expected [model-sym, color-sym] pairs")
    pure (.list cars)
  | _ => throw (IO.userError "Car Factory: expected a single list argument")

/-- Car Factory builder: no args, returns the Car Factory. We model the
returned reference as a tagged value `<'car-factory>` for now; a full
impl would mint a fresh export position. -/
def carFactoryBuilder : Handler := fun _ =>
  pure (.record (.sym "car-factory".toUTF8.toList) [])

/-- The default registry, populated with the simple handlers. -/
def defaultRegistry : Registry :=
  { bindings :=
    [ (carFactoryBuilderSwiss, carFactoryBuilder)
    , (echoGcSwiss,            echoGc)
    , (greeterSwiss,           greeter)
    ] }

/-! ## Dispatcher. -/

/-- Try to interpret an incoming frame as
        `<op:deliver <desc:export 0> [fetch swissnum] _ _>`
and route to the registry. Returns `none` if the frame doesn't match
this exact shape — the event loop is then free to drop it (a real
impl would emit an `op:abort` or similar). -/
def dispatchFetch (r : Registry) : ValueExt → IO (Option ValueExt)
  | .record (.sym lbl) [.record (.sym dlbl) [.int 0], .list args, _, _] =>
    if lbl ≠ "op:deliver".toUTF8.toList then pure none
    else if dlbl ≠ "desc:export".toUTF8.toList then pure none
    else
      match args with
      | .sym method :: rest =>
        if method = "fetch".toUTF8.toList then
          match rest with
          | [.bytes swiss] =>
            match r.lookup swiss with
            | some h => do
              let result ← h []
              pure (some result)
            | none => pure none
          | _ => pure none
        else
          -- Method other than fetch: look up the swissnum currently
          -- bound to position 0 (the bootstrap object). For our minimal
          -- impl, we just dispatch the method-and-args via the
          -- registry's first matching handler.
          pure none
      | _ => pure none
  | _ => pure none

end OcapnLean.Captp.Bootstrap
