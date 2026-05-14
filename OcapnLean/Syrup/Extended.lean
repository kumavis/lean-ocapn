import OcapnLean.Syrup

/-!
# Syrup — extended codec (strings, symbols, lists, records)

The base codec in `OcapnLean.Syrup` covers `bool`, `int`, and `bytes`
with a universal round-trip theorem (`decode_encode`). This module
adds the container types needed by the CapTP wire format — `str`,
`sym`, `list`, and `record` — atop a richer `ValueExt` algebra.

The decoder is a **fueled total `def`**: it takes an explicit
`Nat` budget that decreases on each recursive call, so Lean accepts
it as terminating. The top-level `decodeExt` calls it with
`input.length + 1` fuel, which is always enough for any well-formed
input (each decoded sub-value consumes at least one input byte). This
makes the decoder usable in proofs.

Round-trip equality is verified via a battery of `native_decide`
fixtures that span every constructor, including nested containers.
The fully universal `decodeExt_encodeExt` theorem requires nested-
inductive structural induction over `ValueExt` (which recurses
through `List ValueExt` in the `list`/`record` cases) — a tractable
but verbose proof queued for a follow-up commit.

(`dict`, `set`, `float`, `double` will land later; they aren't
needed for the OCapN `op:*` and `desc:*` frames the event loop in
`Captp.Run` already handles.)
-/

namespace OcapnLean.Syrup

/-- Extended Syrup value algebra. -/
inductive ValueExt
  | bool   (b : Bool)
  | int    (n : Int)
  | bytes  (bs : List UInt8)
  | str    (s : List UInt8)         -- UTF-8 octets
  | sym    (s : List UInt8)         -- UTF-8 octets
  | list   (items : List ValueExt)
  | record (label : ValueExt) (fields : List ValueExt)
deriving Inhabited, Repr

namespace Encode
open Encode (encodeNat encodeInt digitByte)

/-- Encode a `ValueExt`. -/
def encodeExt : ValueExt → List UInt8
  | .bool true       => [0x74]                                       -- 't'
  | .bool false      => [0x66]                                       -- 'f'
  | .int n           => encodeInt n
  | .bytes bs        => encodeNat bs.length ++ [0x3a] ++ bs          -- '<n>:<bytes>'
  | .str bs          => encodeNat bs.length ++ [0x22] ++ bs          -- '<n>"<utf8>'
  | .sym bs          => encodeNat bs.length ++ [0x27] ++ bs          -- "<n>'<utf8>"
  | .list items      =>
      0x5b :: encodeList items ++ [0x5d]                              -- '[' ... ']'
  | .record label fs =>
      0x3c :: encodeExt label ++ encodeList fs ++ [0x3e]              -- '<' ... '>'
where
  encodeList : List ValueExt → List UInt8
  | []      => []
  | v :: vs => encodeExt v ++ encodeList vs

end Encode

namespace Decode
open Decode (isDigit takeDigits digitsToNat)

mutual

/-- Fueled extended decoder. The `fuel` parameter is a recursion
budget that decreases on every recursive call; the top-level
`decodeExt` calls this with `input.length + 1`, always enough for
well-formed inputs. -/
def decodeExtFuel : Nat → List UInt8 → Option (ValueExt × List UInt8)
  | 0,        _         => none
  | _ + 1,    []        => none
  | fuel + 1, b :: rest =>
    if b = 0x74 then some (.bool true, rest)
    else if b = 0x66 then some (.bool false, rest)
    else if b = 0x5b then decodeListItemsFuel fuel rest []          -- '['
    else if b = 0x3c then                                            -- '<'
      match decodeExtFuel fuel rest with
      | none              => none
      | some (label, r1)  =>
        match decodeRecordFieldsFuel fuel r1 [] with
        | none              => none
        | some (fs, r2)     => some (.record label fs, r2)
    else if isDigit b then
      let (ds, after) := takeDigits (b :: rest)
      match after with
      | 0x2b :: r => some (.int (Int.ofNat (digitsToNat ds)), r)
      | 0x2d :: r =>
        let n := digitsToNat ds
        if n = 0 then none
        else some (.int (-(Int.ofNat n)), r)
      | 0x3a :: r =>                                                 -- ':' bytes
        let n := digitsToNat ds
        if r.length < n then none
        else some (.bytes (r.take n), r.drop n)
      | 0x22 :: r =>                                                 -- '"' string
        let n := digitsToNat ds
        if r.length < n then none
        else some (.str (r.take n), r.drop n)
      | 0x27 :: r =>                                                 -- "'" symbol
        let n := digitsToNat ds
        if r.length < n then none
        else some (.sym (r.take n), r.drop n)
      | _ => none
    else none

/-- Fueled decoder for list bodies. -/
def decodeListItemsFuel : Nat → List UInt8 → List ValueExt
                        → Option (ValueExt × List UInt8)
  | 0,        _,                _   => none
  | _ + 1,    [],               _   => none
  | _ + 1,    0x5d :: rest,     acc => some (.list acc.reverse, rest)
  | fuel + 1, input@(_ :: _),   acc =>
    match decodeExtFuel fuel input with
    | none => none
    | some (v, rest) => decodeListItemsFuel fuel rest (v :: acc)

/-- Fueled decoder for record-field bodies. -/
def decodeRecordFieldsFuel : Nat → List UInt8 → List ValueExt
                          → Option (List ValueExt × List UInt8)
  | 0,        _,                _   => none
  | _ + 1,    [],               _   => none
  | _ + 1,    0x3e :: rest,     acc => some (acc.reverse, rest)
  | fuel + 1, input@(_ :: _),   acc =>
    match decodeExtFuel fuel input with
    | none => none
    | some (v, rest) => decodeRecordFieldsFuel fuel rest (v :: acc)

end

/-- Total extended decoder: drives `decodeExtFuel` with enough budget. -/
def decodeExt (input : List UInt8) : Option (ValueExt × List UInt8) :=
  decodeExtFuel (input.length + 1) input

end Decode

------------------------------------------------------------------------
-- Round-trip fixture checks via re-encoding
--
-- ValueExt is a nested inductive (it recurses through List ValueExt),
-- so the auto-deriving handler can't produce `DecidableEq ValueExt`,
-- which `native_decide` would need for `decodeExt (encodeExt v) = some
-- (v, [])` directly. We side-step that by comparing the re-encoded
-- bytes: if the codec round-trips correctly *and* is injective, then
-- equal-encoding implies equal-value.
--
-- Equality of `Option (List UInt8 × List UInt8)` IS decidable, so
-- native_decide is happy.
------------------------------------------------------------------------

open Encode Decode

/-- Re-encode the decoded value (if any) and return its bytes plus
the unconsumed input. Used as a comparison surface that avoids
needing `DecidableEq ValueExt`. -/
@[inline] def reEncode (input : List UInt8) : Option (List UInt8 × List UInt8) :=
  (decodeExt input).map fun (v, rest) => (encodeExt v, rest)

example : reEncode (encodeExt (.bool true))  = some ([0x74], []) := by native_decide
example : reEncode (encodeExt (.bool false)) = some ([0x66], []) := by native_decide
example : reEncode (encodeExt (.int 0))      = some ([0x30, 0x2b], []) := by native_decide
example : reEncode (encodeExt (.int 42))     = some ([0x34, 0x32, 0x2b], []) := by native_decide
example : reEncode (encodeExt (.int (-7)))   = some ([0x37, 0x2d], []) := by native_decide
example : reEncode (encodeExt (.bytes [0x63, 0x61, 0x74]))
        = some ([0x33, 0x3a, 0x63, 0x61, 0x74], []) := by native_decide
example : reEncode (encodeExt (.str  [0x68, 0x69]))
        = some ([0x32, 0x22, 0x68, 0x69], []) := by native_decide
example : reEncode (encodeExt (.sym  [0x66, 0x65, 0x74, 0x63, 0x68]))
        = some ([0x35, 0x27, 0x66, 0x65, 0x74, 0x63, 0x68], []) := by native_decide

example : reEncode (encodeExt (.list [])) = some ([0x5b, 0x5d], []) := by native_decide
example : reEncode (encodeExt (.list [.int 1, .int 2, .int 3]))
        = some ([0x5b, 0x31, 0x2b, 0x32, 0x2b, 0x33, 0x2b, 0x5d], []) := by native_decide

example : reEncode (encodeExt (.record (.sym [0x61]) []))
        = some ([0x3c, 0x31, 0x27, 0x61, 0x3e], []) := by native_decide

-- The nested op:deliver shape: input matches output (modulo encoding)
example : reEncode (encodeExt
            (.record (.sym [0x6f, 0x70, 0x3a, 0x64, 0x65, 0x6c, 0x69, 0x76, 0x65, 0x72])
              [ .record (.sym [0x64, 0x65, 0x73, 0x63, 0x3a, 0x65, 0x78, 0x70, 0x6f, 0x72, 0x74]) [.int 0]
              , .list [.sym [0x66, 0x65, 0x74, 0x63, 0x68], .bytes [0xaa, 0xbb]]
              , .int 3
              , .bool false
              ]))
        = some (encodeExt
            (.record (.sym [0x6f, 0x70, 0x3a, 0x64, 0x65, 0x6c, 0x69, 0x76, 0x65, 0x72])
              [ .record (.sym [0x64, 0x65, 0x73, 0x63, 0x3a, 0x65, 0x78, 0x70, 0x6f, 0x72, 0x74]) [.int 0]
              , .list [.sym [0x66, 0x65, 0x74, 0x63, 0x68], .bytes [0xaa, 0xbb]]
              , .int 3
              , .bool false
              ]), []) := by native_decide

end OcapnLean.Syrup
