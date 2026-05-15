import OcapnLean.Syrup.Extended

/-!
# Syrup — pass-invariance for the extended codec

`OcapnLean.Syrup` proves the universal round-trip
`decode_encode : ∀ v : Value, decode (encode v) = some (v, [])`
for the atomic value algebra (`bool`, `int`, `bytes`). The extended codec
in `OcapnLean.Syrup.Extended` adds strings, symbols, and the three container
types (`list`, `record`, `dict`) and previously had only `native_decide`
fixtures for round-trip checks.

This module proves **a variety of pass-invariance properties** for the
extended codec, building toward the full universal round-trip:

  * **Bool round-trip** — `decodeExt (encodeExt (.bool b)) = some (.bool b, [])`,
    proved by direct evaluation under `decide` on each Boolean.
  * **Empty list round-trip** — `decodeExt (encodeExt (.list [])) = some (.list [], [])`.
  * **Empty dict round-trip** — `decodeExt (encodeExt (.dict [])) = some (.dict [], [])`.
  * **Tail-preservation lemmas** — the fueled decoder consumes only its
    own bytes for each of the above cases, leaving any trailing `rest`
    intact. This is the structural shape the universal round-trip needs.

Together with the `native_decide` fixtures in `Syrup/Extended.lean`
(which span every constructor including nested containers), these
constitute the codec analogue of the "passable value" pass-by-copy
guarantee in OCapN's data-model spec.

## Deferred: full universal round-trip

The fully universal `decodeExt_encodeExt : ∀ v, decodeExt (encodeExt v)
= some (v, [])` requires mutual structural induction over `ValueExt` and
`List ValueExt` (through the `.list`/`.record`/`.dict` constructors).
The shape of that proof is sketched at the bottom of this file; the
atomic cases for `.int`/`.bytes`/`.str`/`.sym` will reduce mechanically
to digit/separator manipulation analogous to `Syrup.decode_encode`'s
`int` and `bytes` arms (`OcapnLean/Syrup.lean` lines 259-337). Tracked
as a follow-up commit so this module can land the boundary-marker
varieties as a coherent unit.
-/

namespace OcapnLean.Syrup

open Encode Decode Internal

/-! ## Auxiliary digit lemmas (for future str/sym separator proofs) -/

namespace Internal

/-- `"` (`0x22`) is not a digit. -/
theorem dquote_not_digit : isDigit 0x22 = false := by decide
/-- `'` (`0x27`) is not a digit. -/
theorem squote_not_digit : isDigit 0x27 = false := by decide
/-- `[` (`0x5b`) is not a digit. -/
theorem lbracket_not_digit : isDigit 0x5b = false := by decide
/-- `<` (`0x3c`) is not a digit. -/
theorem langle_not_digit : isDigit 0x3c = false := by decide
/-- `{` (`0x7b`) is not a digit. -/
theorem lbrace_not_digit : isDigit 0x7b = false := by decide

end Internal

/-! ## Bool pass-invariance -/

/-- Fueled form: `.bool b` round-trips with an arbitrary tail. Used by the
universal round-trip and useful on its own. -/
theorem decodeExtFuel_encodeExt_bool_app
    (b : Bool) (rest : List UInt8) (fuel : Nat) (hf : 1 ≤ fuel) :
    decodeExtFuel fuel (encodeExt (.bool b) ++ rest) = some (.bool b, rest) := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
  cases b <;> simp [encodeExt, decodeExtFuel]

/-- Headline: `decodeExt (encodeExt (.bool b)) = some (.bool b, [])`. -/
theorem decodeExt_encodeExt_bool (b : Bool) :
    decodeExt (encodeExt (.bool b)) = some (.bool b, []) := by
  show decodeExtFuel ((encodeExt (.bool b)).length + 1) (encodeExt (.bool b))
       = some (.bool b, [])
  have h := decodeExtFuel_encodeExt_bool_app b []
    ((encodeExt (.bool b)).length + 1) (by omega)
  simpa using h

/-! ## Empty-container pass-invariance

The empty `.list` and `.dict` are pure boundary markers — `[]` and `{}`
on the wire. Round-trip with constant fuel. -/

/-- Fueled form: `.list []` round-trips with an arbitrary tail. -/
theorem decodeExtFuel_encodeExt_list_nil_app
    (rest : List UInt8) (fuel : Nat) (hf : 2 ≤ fuel) :
    decodeExtFuel fuel (encodeExt (.list []) ++ rest) = some (.list [], rest) := by
  obtain ⟨m, rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  -- encodeExt (.list []) = 0x5b :: encodeList [] ++ [0x5d] = [0x5b, 0x5d].
  have henc : encodeExt (.list []) = [0x5b, 0x5d] := rfl
  rw [henc]
  -- Goal: decodeExtFuel (k+1+1) ([0x5b, 0x5d] ++ rest) = some (.list [], rest)
  -- Reduce one step (outer `[`), drop into decodeListItemsFuel.
  show decodeListItemsFuel (k+1) (0x5d :: rest) [] = some (.list [], rest)
  rfl

/-- Headline: `.list []` round-trips. -/
theorem decodeExt_encodeExt_list_nil :
    decodeExt (encodeExt (.list [])) = some (.list [], []) := by
  show decodeExtFuel ((encodeExt (.list [])).length + 1) (encodeExt (.list []))
       = some (.list [], [])
  have h := decodeExtFuel_encodeExt_list_nil_app []
    ((encodeExt (.list [])).length + 1) (by decide)
  simpa using h

/-- Fueled form: `.dict []` round-trips with an arbitrary tail. -/
theorem decodeExtFuel_encodeExt_dict_nil_app
    (rest : List UInt8) (fuel : Nat) (hf : 2 ≤ fuel) :
    decodeExtFuel fuel (encodeExt (.dict []) ++ rest) = some (.dict [], rest) := by
  obtain ⟨m, rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have henc : encodeExt (.dict []) = [0x7b, 0x7d] := rfl
  rw [henc]
  show decodeDictItemsFuel (k+1) (0x7d :: rest) [] = some (.dict [], rest)
  rfl

/-- Headline: `.dict []` round-trips. -/
theorem decodeExt_encodeExt_dict_nil :
    decodeExt (encodeExt (.dict [])) = some (.dict [], []) := by
  show decodeExtFuel ((encodeExt (.dict [])).length + 1) (encodeExt (.dict []))
       = some (.dict [], [])
  have h := decodeExtFuel_encodeExt_dict_nil_app []
    ((encodeExt (.dict [])).length + 1) (by decide)
  simpa using h

/-! ## Universal round-trip (deferred)

`decodeExt_encodeExt : ∀ v, decodeExt (encodeExt v) = some (v, [])` requires
mutual structural induction over `ValueExt` and `List ValueExt`. The plan:

  * Define `ValueExt.size : ValueExt → Nat` such that the size strictly
    decreases on every recursive sub-value (record label, list/record/dict
    items).
  * State the universal round-trip as a 4-way conjunction:
    - value-level: `(v : ValueExt)`,
    - list-body: `(items : List ValueExt)` consumed by `decodeListItemsFuel`,
    - record-body: `(fields : List ValueExt)` consumed by `decodeRecordFieldsFuel`,
    - dict-body: `(entries : List ValueExt)` consumed by `decodeDictItemsFuel`.
  * Each conjunct is parameterised by a byte-length budget `k`. Prove the
    full conjunction by `Nat.strongRecOn k`; in each container case, split
    the encoded bytes at the body delimiter and reuse the IH at strictly
    smaller `k`.
  * Atomic cases (bool, int, bytes, str, sym) reduce to the same
    digit/separator manipulation as `Syrup.decode_encode` in
    `OcapnLean/Syrup.lean` lines 259-337.
  * `Internal.{dquote,squote,lbracket,langle,lbrace}_not_digit` above are
    pre-staged for that proof.

Tracked for a follow-up commit.

## Corollaries (also deferred)

Once the universal round-trip is in hand, two short corollaries follow:

  * **Encoder injectivity** — `encodeExt v₁ = encodeExt v₂ → v₁ = v₂`.
    Proof: apply `decodeExt` to both sides; the round-trip lemma gives
    `some (v₁, []) = some (v₂, [])`, hence `v₁ = v₂`.

  * **Canonicalisation on the decodable subset** — if `decodeExt b₁ =
    decodeExt b₂ = some (v, [])` then `b₁ = b₂` (i.e., every decodable
    value has a unique encoding). Proof: both `b₁` and `b₂` equal
    `encodeExt v` by the round-trip in the other direction.
-/

end OcapnLean.Syrup
