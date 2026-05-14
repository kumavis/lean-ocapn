import OcapnLean.Syrup

/-!
# Syrup — extended codec (strings, symbols, lists, records)

The base codec in `OcapnLean.Syrup` covers `bool`, `int`, and `bytes`
with a universal round-trip theorem (`decode_encode`). This module
adds the container types needed by the CapTP wire format — `str`,
`sym`, `list`, and `record` — atop a richer `ValueExt` algebra.

The container decoder uses `partial def`, since termination depends
on the input shrinking with each recursive call (a property the
parser maintains but isn't trivially structural). We retain
**runtime** correctness via byte-level fixture tests cross-checked
against the upstream Python reference; the formal round-trip proof
for containers is queued behind the verified-event-loop work.

(`dict`, `set`, `float`, `double` will land in a follow-up commit;
they are not needed for the OCapN `op:*` and `desc:*` frames whose
encoding we exercise in step 1.)
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

/-- Extended decoder. `partial def` because termination follows from
the byte-level shrinking the parser ensures at runtime but which isn't
structurally evident to Lean. Round-trip equality is verified via
`native_decide` fixtures rather than universal proof. -/
partial def decodeExt : List UInt8 → Option (ValueExt × List UInt8)
  | []        => none
  | b :: rest =>
    if b = 0x74 then some (.bool true, rest)
    else if b = 0x66 then some (.bool false, rest)
    else if b = 0x5b then decodeListItems rest []          -- '['
    else if b = 0x3c then                                   -- '<'
      match decodeExt rest with
      | none              => none
      | some (label, r1)  =>
        match decodeRecordFields r1 [] with
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
      | 0x3a :: r =>                                        -- ':' bytes
        let n := digitsToNat ds
        if r.length < n then none
        else some (.bytes (r.take n), r.drop n)
      | 0x22 :: r =>                                        -- '"' string
        let n := digitsToNat ds
        if r.length < n then none
        else some (.str (r.take n), r.drop n)
      | 0x27 :: r =>                                        -- "'" symbol
        let n := digitsToNat ds
        if r.length < n then none
        else some (.sym (r.take n), r.drop n)
      | _ => none
    else none

/-- Decode list items until the `]` terminator. -/
partial def decodeListItems : List UInt8 → List ValueExt
                            → Option (ValueExt × List UInt8)
  | [], _ => none
  | 0x5d :: rest, acc => some (.list acc.reverse, rest)
  | input, acc =>
    match decodeExt input with
    | none => none
    | some (v, rest) => decodeListItems rest (v :: acc)

/-- Decode record fields until the `>` terminator. -/
partial def decodeRecordFields : List UInt8 → List ValueExt
                              → Option (List ValueExt × List UInt8)
  | [], _ => none
  | 0x3e :: rest, acc => some (acc.reverse, rest)
  | input, acc =>
    match decodeExt input with
    | none => none
    | some (v, rest) => decodeRecordFields rest (v :: acc)

end

end Decode

end OcapnLean.Syrup
