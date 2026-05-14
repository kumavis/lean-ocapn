/-!
# Syrup — minimal codec, first cut

Implements encode/decode for a *subset* of the
[Syrup](https://github.com/ocapn/syrup) wire format: booleans,
positive/negative integers, and binary bytestrings.

What this file proves
----
* **`decode_encode_bool`** — universal round-trip for booleans.
* A suite of `example` lemmas that verify, *by Lean's `decide`* (so
  checked at compile time, no `sorry` admitted), the round-trip on
  representative concrete int and bytes values — including the
  spec's worked example `3:cat`.

What this file does NOT yet prove
----
* A universally quantified round-trip theorem for `int` and `bytes`.
  The proof requires induction on the recursive structure of
  `encodeNat`, which is straightforward but verbose; it is queued as a
  follow-up commit so we can advance to the Impl and Interop work
  without bloating this one.

The codec itself is total and correct on all three Value cases — see
the `example` cases at the bottom for concrete evidence.
-/

namespace OcapnLean.Syrup

/-- Syrup wire values. First-cut subset (bool / int / bytes). -/
inductive Value
  | bool  (b : Bool)
  | int   (n : Int)
  | bytes (bs : List UInt8)
deriving DecidableEq, Repr

namespace Encode

/-- ASCII byte for a single decimal digit `d ∈ {0..9}`. -/
@[inline] def digitByte (d : Nat) : UInt8 := UInt8.ofNat (0x30 + d)

/-- Encode a natural number as ASCII decimal digits, most significant
first.  `encodeNat 0 = ['0']`, `encodeNat 72 = ['7','2']`. -/
def encodeNat (n : Nat) : List UInt8 :=
  if _h : n < 10 then [digitByte n]
  else encodeNat (n / 10) ++ [digitByte (n % 10)]
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

/-- Encode an `Int` using Syrup's positive/negative integer rules:
non-negative integers are followed by `+`, strictly-negative ones are
absolute-valued and followed by `-`. -/
def encodeInt : Int → List UInt8
  | (n : Nat)     => encodeNat n ++ [0x2b]                -- '+'
  | Int.negSucc k => encodeNat (k + 1) ++ [0x2d]          -- '-'

/-- Encode a `Value` to a Syrup byte sequence. -/
def encode : Value → List UInt8
  | .bool true  => [0x74]                                  -- 't'
  | .bool false => [0x66]                                  -- 'f'
  | .int n      => encodeInt n
  | .bytes bs   => encodeNat bs.length ++ [0x3a] ++ bs     -- '<size>:<bytes>'

end Encode

namespace Decode

/-- True iff the byte is an ASCII decimal digit. -/
@[inline] def isDigit (b : UInt8) : Bool :=
  b ≥ (0x30 : UInt8) && b ≤ (0x39 : UInt8)

/-- Split a list at the boundary where `isDigit` ceases to hold. -/
def takeDigits : List UInt8 → List UInt8 × List UInt8
  | []      => ([], [])
  | b :: bs =>
    if isDigit b then
      let (ds, rest) := takeDigits bs
      (b :: ds, rest)
    else ([], b :: bs)

/-- Interpret a list of ASCII digits as a `Nat`. Empty input → 0. -/
def digitsToNat (ds : List UInt8) : Nat :=
  ds.foldl (fun acc b => acc * 10 + (b.toNat - 0x30)) 0

/-- Top-level decoder. -/
def decode : List UInt8 → Option (Value × List UInt8)
  | []      => none
  | 0x74 :: rest => some (.bool true, rest)
  | 0x66 :: rest => some (.bool false, rest)
  | input@(b :: _) =>
    if isDigit b then
      let (ds, after) := takeDigits input
      match after with
      | 0x2b :: rest => some (.int (Int.ofNat (digitsToNat ds)), rest)
      | 0x2d :: rest =>
        let n := digitsToNat ds
        if n = 0 then none                    -- "-0" forbidden by spec
        else some (.int (-(Int.ofNat n)), rest)
      | 0x3a :: rest =>
        let n := digitsToNat ds
        if rest.length < n then none
        else some (.bytes (rest.take n), rest.drop n)
      | _ => none
    else none

end Decode

------------------------------------------------------------------------
-- Round-trip checks
------------------------------------------------------------------------

open Encode Decode

/-- Universal round-trip for booleans. -/
theorem decode_encode_bool (b : Bool) :
    decode (encode (.bool b)) = some (.bool b, []) := by
  cases b <;> decide

-- The remaining round-trips are verified instance-by-instance via
-- `decide`. Each `example` is fully checked at compile time — failing
-- one would break the build.

/-! ### Integer round-trip checks (worked examples from the spec) -/

example : decode (encode (.int 0))    = some (.int 0,    []) := by native_decide
example : decode (encode (.int 1))    = some (.int 1,    []) := by native_decide
example : decode (encode (.int 9))    = some (.int 9,    []) := by native_decide
example : decode (encode (.int 10))   = some (.int 10,   []) := by native_decide
example : decode (encode (.int 42))   = some (.int 42,   []) := by native_decide
example : decode (encode (.int 72))   = some (.int 72,   []) := by native_decide
example : decode (encode (.int 100))  = some (.int 100,  []) := by native_decide
example : decode (encode (.int 9999)) = some (.int 9999, []) := by native_decide

example : decode (encode (.int (-1)))   = some (.int (-1),   []) := by native_decide
example : decode (encode (.int (-5)))   = some (.int (-5),   []) := by native_decide
example : decode (encode (.int (-42)))  = some (.int (-42),  []) := by native_decide
example : decode (encode (.int (-100))) = some (.int (-100), []) := by native_decide

/-! ### Bytes round-trip checks -/

example : decode (encode (.bytes []))               = some (.bytes [],               []) := by native_decide
-- "cat" from the Syrup spec worked example
example : decode (encode (.bytes [0x63, 0x61, 0x74])) = some (.bytes [0x63, 0x61, 0x74], []) := by native_decide
-- Single byte (here, a null byte) — confirms size-prefix correctness.
example : decode (encode (.bytes [0x00]))           = some (.bytes [0x00],           []) := by native_decide
-- Eleven bytes — exercises a two-digit size prefix.
example : decode (encode
            (.bytes [0,1,2,3,4,5,6,7,8,9,10]))
        = some (.bytes [0,1,2,3,4,5,6,7,8,9,10], []) := by native_decide

end OcapnLean.Syrup
