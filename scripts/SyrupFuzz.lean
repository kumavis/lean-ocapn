import OcapnLean.Syrup.Extended

/-!
# Hand-rolled property fuzz for the Syrup codec (M10)

Complements the universal-round-trip proof framework in
`OcapnLean.Syrup.RoundTripExt` with randomised property tests.
The proof framework discharges all 10 atomic value-form cases
(bool, int, bytes, str, sym, float64, list-nil, dict-nil) and
provides the size foundation; this script provides a runtime
sanity check that exercises the codec at random across the
atomic shapes the proof already covers, plus the non-empty
containers the proof doesn't yet.

Implementation note: this is a hand-rolled fuzzer (using
`IO.rand` + `IO.toEIO` style) rather than `Plausible.Testable`.
Plausible's `Testable` instance synthesis is finicky in IO
do-blocks (the prop's metavariable doesn't resolve before the
typeclass search fires); a small random generator + the
existing byte-level `reEncode` helper is enough to get the
property-test coverage we want without that elaboration
gymnastics.

Each property runs `defaultFuzzCases` random inputs (100 by
default). The script exits non-zero on any counter-example.
-/

open OcapnLean.Syrup OcapnLean.Syrup.Encode OcapnLean.Syrup.Decode

/-- Number of random inputs per property. -/
def defaultFuzzCases : Nat := 100

/-! ## Small random generators (uniformly distributed within the
chosen range; not crypto-grade — we just want broad codec coverage). -/

/-- A uniformly random `Int` in `[-bound, bound]`. -/
def randomInt (bound : Nat := 1000000) : IO Int := do
  let n ← IO.rand 0 (2 * bound)
  pure (Int.ofNat n - Int.ofNat bound)

/-- A uniformly random `UInt8`. -/
def randomByte : IO UInt8 := do
  let n ← IO.rand 0 255
  pure n.toUInt8

/-- A list of uniformly random bytes whose length is uniformly
chosen in `[0, maxLen]`. -/
def randomBytes (maxLen : Nat := 64) : IO (List UInt8) := do
  let len ← IO.rand 0 maxLen
  let mut acc : List UInt8 := []
  for _ in [0:len] do
    acc := (← randomByte) :: acc
  pure acc

/-- A uniformly random 64-bit word. Constructs the bit pattern
byte-by-byte so we span the entire `UInt64` range (including
NaN payloads and signed zeros once interpreted as `Float`). -/
def randomUInt64 : IO UInt64 := do
  let mut bits : UInt64 := 0
  for _ in [0:8] do
    let b ← randomByte
    bits := bits * 256 + b.toUInt64
  pure bits

/-! ## Fuzz harness -/

/-- Run a property `n` times against `gen`-produced inputs. Returns
`true` if no counter-example is found in the budget. -/
def fuzz {α : Type} (label : String) (gen : IO α) (toVal : α → ValueExt)
    (n : Nat := defaultFuzzCases) : IO Bool := do
  for i in [0:n] do
    let x ← gen
    let v := toVal x
    let bytes := encodeExt v
    let result := reEncode bytes
    if result ≠ some (bytes, []) then
      IO.eprintln s!"[syrup-fuzz] {label}: ❌ counter-example at attempt {i}"
      return false
  IO.println s!"[syrup-fuzz] {label}: ✅ {n} cases, no counter-example"
  pure true

def main : IO Unit := do
  let mut ok := true

  -- bool: 2 inhabitants only — exhaust both.
  let allBools : List Bool := [false, true]
  for b in allBools do
    let v := ValueExt.bool b
    let bytes := encodeExt v
    if reEncode bytes ≠ some (bytes, []) then
      IO.eprintln s!"[syrup-fuzz] bool: ❌ failed on {b}"
      ok := false
  IO.println s!"[syrup-fuzz] bool: ✅ exhaustive (2 cases)"

  -- int: random ints, both signs.
  ok := (← fuzz "int" randomInt ValueExt.int) && ok

  -- bytes / str / sym: same wire shape (length-prefixed bytes).
  ok := (← fuzz "bytes" randomBytes ValueExt.bytes) && ok
  ok := (← fuzz "str"   randomBytes ValueExt.str)   && ok
  ok := (← fuzz "sym"   randomBytes ValueExt.sym)   && ok

  -- float64: random 64-bit bit patterns. Spans NaN payloads,
  -- signed zeros, subnormals, ±Inf — the surface `bv_decide`
  -- closes algebraically.
  ok := (← fuzz "float64" randomUInt64 ValueExt.float64) && ok

  -- list of ints: exercises the multi-element container path
  -- the formal proof doesn't yet close.
  let listGen : IO ValueExt := do
    let len ← IO.rand 0 16
    let mut items : List ValueExt := []
    for _ in [0:len] do
      items := .int (← randomInt 1000) :: items
    pure (ValueExt.list items)
  ok := (← fuzz "list of ints" listGen id) && ok

  -- record with a fixed label and one int field: exercises the
  -- record-body decoder.
  let recordGen : IO ValueExt := do
    let n ← randomInt
    pure (.record (.sym "op:deliver".toUTF8.toList) [.int n])
  ok := (← fuzz "record <op:deliver int>" recordGen id) && ok

  -- dict with two fixed keys and a varying int value: exercises
  -- the dict-body decoder.
  let dictGen : IO ValueExt := do
    let port ← randomInt
    pure (ValueExt.dict
      [.str "host".toUTF8.toList, .str "127.0.0.1".toUTF8.toList,
       .str "port".toUTF8.toList, .int port])
  ok := (← fuzz "dict {host=str, port=int}" dictGen id) && ok

  -- Mixed nested container: a list whose items are records.
  -- Exercises the interaction between the list-body decoder and
  -- the record sub-value decoder.
  let nestedGen : IO ValueExt := do
    let len ← IO.rand 0 8
    let mut items : List ValueExt := []
    for _ in [0:len] do
      let n ← randomInt 100
      items := .record (.sym "item".toUTF8.toList) [.int n] :: items
    pure (ValueExt.list items)
  ok := (← fuzz "list <record>" nestedGen id) && ok

  if ok then
    IO.println "OK"
  else
    IO.eprintln "FAIL: Syrup codec round-trip counter-example"
    IO.Process.exit 1
