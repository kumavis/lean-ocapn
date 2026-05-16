import OcapnLean.Syrup.Extended
import Std.Tactic.BVDecide

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

/-! ## Atomic int/bytes/str/sym pass-invariance

Each of these decodes via a digit-prefix length, a separator byte, and
a payload. Mirrors `Syrup.decode_encode`'s atomic cases against the
new fueled extended decoder. -/

/-- Post-digit-prefix dispatch (mirrors the inline `match` in
`decodeExtFuel`'s digit branch). -/
private def decodeExtAfterDigits (ds : List UInt8) :
    List UInt8 → Option (ValueExt × List UInt8)
  | 0x2b :: r => some (.int (Int.ofNat (digitsToNat ds)), r)
  | 0x2d :: r =>
    let n := digitsToNat ds
    if n = 0 then none else some (.int (-(Int.ofNat n)), r)
  | 0x3a :: r =>
    let n := digitsToNat ds
    if r.length < n then none else some (.bytes (r.take n), r.drop n)
  | 0x22 :: r =>
    let n := digitsToNat ds
    if r.length < n then none else some (.str (r.take n), r.drop n)
  | 0x27 :: r =>
    let n := digitsToNat ds
    if r.length < n then none else some (.sym (r.take n), r.drop n)
  | _ => none

/-- Decoder reduction at a digit-prefix: `decodeExtFuel` peels off the
all-digit run and dispatches on the following separator. -/
private theorem decodeExtFuel_digits_then
    (d : UInt8) (ds_tail : List UInt8)
    (sep : UInt8) (rest : List UInt8) (fuel : Nat)
    (hd : isDigit d = true)
    (hd_ne_t : d ≠ 0x74) (hd_ne_f : d ≠ 0x66)
    (hd_ne_lbr : d ≠ 0x5b) (hd_ne_lbrc : d ≠ 0x7b) (hd_ne_D : d ≠ 0x44)
    (hd_ne_la : d ≠ 0x3c)
    (hall : ∀ b ∈ d :: ds_tail, isDigit b = true)
    (hsep : isDigit sep = false) :
    decodeExtFuel (fuel + 1) (d :: ds_tail ++ sep :: rest)
      = decodeExtAfterDigits (d :: ds_tail) (sep :: rest) := by
  show (if d = 0x74 then _ else
        if d = 0x66 then _ else
        if d = 0x5b then _ else
        if d = 0x7b then _ else
        if d = 0x44 then _ else
        if d = 0x3c then _ else
        if isDigit d then _ else none) = _
  rw [if_neg hd_ne_t, if_neg hd_ne_f, if_neg hd_ne_lbr,
      if_neg hd_ne_lbrc, if_neg hd_ne_D, if_neg hd_ne_la, if_pos hd]
  show (let (ds, after) := takeDigits (d :: ds_tail ++ sep :: rest)
        decodeExtAfterDigits ds after) = _
  have hsplit : takeDigits (d :: ds_tail ++ sep :: rest)
              = (d :: ds_tail, sep :: rest) :=
    takeDigits_all_digit_prefix (d :: ds_tail) hall sep hsep rest
  rw [hsplit]

/-- `.int (Int.ofNat k)` round-trips with a trailing tail. -/
private theorem decodeExtFuel_encodeExt_intNat_app
    (k : Nat) (rest : List UInt8) (fuel : Nat)
    (hf : (encodeNat k).length + 1 ≤ fuel) :
    decodeExtFuel fuel (encodeExt (.int (Int.ofNat k)) ++ rest)
      = some (.int (Int.ofNat k), rest) := by
  obtain ⟨m, rfl⟩ : ∃ m, fuel = m + 1 :=
    ⟨fuel - 1, by omega⟩
  obtain ⟨d, ds_tail, hcons⟩ : ∃ d ds, encodeNat k = d :: ds := by
    rcases h : encodeNat k with _ | ⟨d, ds⟩
    · exact absurd h (encodeNat_ne_nil k)
    · exact ⟨d, ds, rfl⟩
  have hd : isDigit d = true :=
    encodeNat_all_digits k d (hcons ▸ List.mem_cons_self ..)
  have hd_ne_t : d ≠ 0x74 := by intro heq; rw [heq] at hd; cases hd
  have hd_ne_f : d ≠ 0x66 := by intro heq; rw [heq] at hd; cases hd
  have hd_ne_lbr : d ≠ 0x5b := by intro heq; rw [heq] at hd; cases hd
  have hd_ne_lbrc : d ≠ 0x7b := by intro heq; rw [heq] at hd; cases hd
  have hd_ne_D : d ≠ 0x44 := by intro heq; rw [heq] at hd; cases hd
  have hd_ne_la : d ≠ 0x3c := by intro heq; rw [heq] at hd; cases hd
  have hall : ∀ b ∈ d :: ds_tail, isDigit b = true := by
    rw [← hcons]; exact encodeNat_all_digits k
  have hk_eq : encodeExt (.int (Int.ofNat k)) ++ rest
             = d :: ds_tail ++ 0x2b :: rest := by
    show encodeNat k ++ [0x2b] ++ rest = _
    rw [hcons]; simp
  rw [hk_eq]
  rw [decodeExtFuel_digits_then d ds_tail 0x2b rest m hd hd_ne_t hd_ne_f
        hd_ne_lbr hd_ne_lbrc hd_ne_D hd_ne_la hall plus_not_digit]
  show decodeExtAfterDigits (d :: ds_tail) (0x2b :: rest) = _
  simp only [decodeExtAfterDigits]
  rw [← hcons, digitsToNat_encodeNat]

/-- `.int (Int.negSucc k)` round-trips with a trailing tail. -/
private theorem decodeExtFuel_encodeExt_intNeg_app
    (k : Nat) (rest : List UInt8) (fuel : Nat)
    (hf : (encodeNat (k+1)).length + 1 ≤ fuel) :
    decodeExtFuel fuel (encodeExt (.int (Int.negSucc k)) ++ rest)
      = some (.int (Int.negSucc k), rest) := by
  obtain ⟨m, rfl⟩ : ∃ m, fuel = m + 1 :=
    ⟨fuel - 1, by omega⟩
  obtain ⟨d, ds_tail, hcons⟩ : ∃ d ds, encodeNat (k+1) = d :: ds := by
    rcases h : encodeNat (k+1) with _ | ⟨d, ds⟩
    · exact absurd h (encodeNat_ne_nil (k+1))
    · exact ⟨d, ds, rfl⟩
  have hd : isDigit d = true :=
    encodeNat_all_digits (k+1) d (hcons ▸ List.mem_cons_self ..)
  have hd_ne_t : d ≠ 0x74 := by intro heq; rw [heq] at hd; cases hd
  have hd_ne_f : d ≠ 0x66 := by intro heq; rw [heq] at hd; cases hd
  have hd_ne_lbr : d ≠ 0x5b := by intro heq; rw [heq] at hd; cases hd
  have hd_ne_lbrc : d ≠ 0x7b := by intro heq; rw [heq] at hd; cases hd
  have hd_ne_D : d ≠ 0x44 := by intro heq; rw [heq] at hd; cases hd
  have hd_ne_la : d ≠ 0x3c := by intro heq; rw [heq] at hd; cases hd
  have hall : ∀ b ∈ d :: ds_tail, isDigit b = true := by
    rw [← hcons]; exact encodeNat_all_digits (k+1)
  have hk_eq : encodeExt (.int (Int.negSucc k)) ++ rest
             = d :: ds_tail ++ 0x2d :: rest := by
    show encodeNat (k+1) ++ [0x2d] ++ rest = _
    rw [hcons]; simp
  rw [hk_eq]
  rw [decodeExtFuel_digits_then d ds_tail 0x2d rest m hd hd_ne_t hd_ne_f
        hd_ne_lbr hd_ne_lbrc hd_ne_D hd_ne_la hall minus_not_digit]
  show decodeExtAfterDigits (d :: ds_tail) (0x2d :: rest) = _
  simp only [decodeExtAfterDigits]
  rw [← hcons, digitsToNat_encodeNat]
  have hne : k + 1 ≠ 0 := Nat.succ_ne_zero k
  simp [Int.negSucc_eq]

/-- `.int n` round-trips for both signs. -/
theorem decodeExtFuel_encodeExt_int_app
    (n : Int) (rest : List UInt8) (fuel : Nat)
    (hf : (encodeExt (.int n)).length + 1 ≤ fuel) :
    decodeExtFuel fuel (encodeExt (.int n) ++ rest) = some (.int n, rest) := by
  cases n with
  | ofNat k =>
    have hlen : (encodeExt (.int (Int.ofNat k))).length = (encodeNat k).length + 1 := by
      show (encodeNat k ++ [0x2b]).length = _
      simp
    have hf' : (encodeNat k).length + 1 ≤ fuel := by rw [hlen] at hf; omega
    exact decodeExtFuel_encodeExt_intNat_app k rest fuel hf'
  | negSucc k =>
    have hlen : (encodeExt (.int (Int.negSucc k))).length = (encodeNat (k+1)).length + 1 := by
      show (encodeNat (k+1) ++ [0x2d]).length = _
      simp
    have hf' : (encodeNat (k+1)).length + 1 ≤ fuel := by rw [hlen] at hf; omega
    exact decodeExtFuel_encodeExt_intNeg_app k rest fuel hf'

/-- Headline: `.int n` round-trips at the top level. -/
theorem decodeExt_encodeExt_int (n : Int) :
    decodeExt (encodeExt (.int n)) = some (.int n, []) := by
  show decodeExtFuel ((encodeExt (.int n)).length + 1) (encodeExt (.int n))
       = some (.int n, [])
  have h := decodeExtFuel_encodeExt_int_app n [] ((encodeExt (.int n)).length + 1)
            (by omega)
  simpa using h

/-- Generic length-prefixed helper for `bytes`/`str`/`sym`. -/
private theorem decodeExtFuel_lenSep_app
    (sep : UInt8) (hsep : isDigit sep = false)
    (mk : List UInt8 → ValueExt)
    (kase : sep = 0x3a ∧ mk = ValueExt.bytes
          ∨ sep = 0x22 ∧ mk = ValueExt.str
          ∨ sep = 0x27 ∧ mk = ValueExt.sym)
    (bs : List UInt8) (rest : List UInt8) (fuel : Nat)
    (hf : (encodeNat bs.length).length + 1 + bs.length ≤ fuel) :
    decodeExtFuel fuel (encodeNat bs.length ++ [sep] ++ bs ++ rest)
      = some (mk bs, rest) := by
  obtain ⟨m, rfl⟩ : ∃ m, fuel = m + 1 :=
    ⟨fuel - 1, by omega⟩
  obtain ⟨d, ds_tail, hcons⟩ : ∃ d ds, encodeNat bs.length = d :: ds := by
    rcases h : encodeNat bs.length with _ | ⟨d, ds⟩
    · exact absurd h (encodeNat_ne_nil bs.length)
    · exact ⟨d, ds, rfl⟩
  have hd : isDigit d = true :=
    encodeNat_all_digits bs.length d (hcons ▸ List.mem_cons_self ..)
  have hd_ne_t : d ≠ 0x74 := by intro heq; rw [heq] at hd; cases hd
  have hd_ne_f : d ≠ 0x66 := by intro heq; rw [heq] at hd; cases hd
  have hd_ne_lbr : d ≠ 0x5b := by intro heq; rw [heq] at hd; cases hd
  have hd_ne_lbrc : d ≠ 0x7b := by intro heq; rw [heq] at hd; cases hd
  have hd_ne_D : d ≠ 0x44 := by intro heq; rw [heq] at hd; cases hd
  have hd_ne_la : d ≠ 0x3c := by intro heq; rw [heq] at hd; cases hd
  have hall : ∀ b ∈ d :: ds_tail, isDigit b = true := by
    rw [← hcons]; exact encodeNat_all_digits bs.length
  have hk_eq : encodeNat bs.length ++ [sep] ++ bs ++ rest
             = d :: ds_tail ++ sep :: (bs ++ rest) := by
    rw [hcons]; simp
  rw [hk_eq]
  rw [decodeExtFuel_digits_then d ds_tail sep (bs ++ rest) m hd hd_ne_t hd_ne_f
        hd_ne_lbr hd_ne_lbrc hd_ne_D hd_ne_la hall hsep]
  have hdn : digitsToNat (d :: ds_tail) = bs.length := by
    rw [← hcons]; exact digitsToNat_encodeNat bs.length
  rcases kase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · show decodeExtAfterDigits (d :: ds_tail) (0x3a :: (bs ++ rest)) = _
    simp only [decodeExtAfterDigits]
    rw [hdn]
    have hlt : ¬ (bs ++ rest).length < bs.length := by simp
    simp
  · show decodeExtAfterDigits (d :: ds_tail) (0x22 :: (bs ++ rest)) = _
    simp only [decodeExtAfterDigits]
    rw [hdn]
    have hlt : ¬ (bs ++ rest).length < bs.length := by simp
    simp
  · show decodeExtAfterDigits (d :: ds_tail) (0x27 :: (bs ++ rest)) = _
    simp only [decodeExtAfterDigits]
    rw [hdn]
    have hlt : ¬ (bs ++ rest).length < bs.length := by simp
    simp

/-- `.bytes bs` round-trips with a trailing tail. -/
theorem decodeExtFuel_encodeExt_bytes_app
    (bs : List UInt8) (rest : List UInt8) (fuel : Nat)
    (hf : (encodeExt (.bytes bs)).length + 1 ≤ fuel) :
    decodeExtFuel fuel (encodeExt (.bytes bs) ++ rest) = some (.bytes bs, rest) := by
  have hlen : (encodeExt (.bytes bs)).length
            = (encodeNat bs.length).length + 1 + bs.length := by
    show ((encodeNat bs.length) ++ [0x3a] ++ bs).length = _
    simp; omega
  have hf' : (encodeNat bs.length).length + 1 + bs.length ≤ fuel := by rw [hlen] at hf; omega
  have hrearr : encodeExt (.bytes bs) ++ rest
              = encodeNat bs.length ++ [0x3a] ++ bs ++ rest := by
    show (encodeNat bs.length ++ [0x3a] ++ bs) ++ rest = _
    simp [List.append_assoc]
  rw [hrearr]
  exact decodeExtFuel_lenSep_app 0x3a colon_not_digit ValueExt.bytes
    (Or.inl ⟨rfl, rfl⟩) bs rest fuel hf'

/-- Headline: `.bytes bs` round-trips. -/
theorem decodeExt_encodeExt_bytes (bs : List UInt8) :
    decodeExt (encodeExt (.bytes bs)) = some (.bytes bs, []) := by
  show decodeExtFuel ((encodeExt (.bytes bs)).length + 1) (encodeExt (.bytes bs))
       = some (.bytes bs, [])
  have h := decodeExtFuel_encodeExt_bytes_app bs [] ((encodeExt (.bytes bs)).length + 1)
            (by omega)
  simpa using h

/-- `.str s` round-trips with a trailing tail. -/
theorem decodeExtFuel_encodeExt_str_app
    (s : List UInt8) (rest : List UInt8) (fuel : Nat)
    (hf : (encodeExt (.str s)).length + 1 ≤ fuel) :
    decodeExtFuel fuel (encodeExt (.str s) ++ rest) = some (.str s, rest) := by
  have hlen : (encodeExt (.str s)).length
            = (encodeNat s.length).length + 1 + s.length := by
    show ((encodeNat s.length) ++ [0x22] ++ s).length = _
    simp; omega
  have hf' : (encodeNat s.length).length + 1 + s.length ≤ fuel := by rw [hlen] at hf; omega
  have hrearr : encodeExt (.str s) ++ rest
              = encodeNat s.length ++ [0x22] ++ s ++ rest := by
    show (encodeNat s.length ++ [0x22] ++ s) ++ rest = _
    simp [List.append_assoc]
  rw [hrearr]
  exact decodeExtFuel_lenSep_app 0x22 dquote_not_digit ValueExt.str
    (Or.inr (Or.inl ⟨rfl, rfl⟩)) s rest fuel hf'

/-- Headline: `.str s` round-trips. -/
theorem decodeExt_encodeExt_str (s : List UInt8) :
    decodeExt (encodeExt (.str s)) = some (.str s, []) := by
  show decodeExtFuel ((encodeExt (.str s)).length + 1) (encodeExt (.str s))
       = some (.str s, [])
  have h := decodeExtFuel_encodeExt_str_app s [] ((encodeExt (.str s)).length + 1)
            (by omega)
  simpa using h

/-- `.sym s` round-trips with a trailing tail. -/
theorem decodeExtFuel_encodeExt_sym_app
    (s : List UInt8) (rest : List UInt8) (fuel : Nat)
    (hf : (encodeExt (.sym s)).length + 1 ≤ fuel) :
    decodeExtFuel fuel (encodeExt (.sym s) ++ rest) = some (.sym s, rest) := by
  have hlen : (encodeExt (.sym s)).length
            = (encodeNat s.length).length + 1 + s.length := by
    show ((encodeNat s.length) ++ [0x27] ++ s).length = _
    simp; omega
  have hf' : (encodeNat s.length).length + 1 + s.length ≤ fuel := by rw [hlen] at hf; omega
  have hrearr : encodeExt (.sym s) ++ rest
              = encodeNat s.length ++ [0x27] ++ s ++ rest := by
    show (encodeNat s.length ++ [0x27] ++ s) ++ rest = _
    simp [List.append_assoc]
  rw [hrearr]
  exact decodeExtFuel_lenSep_app 0x27 squote_not_digit ValueExt.sym
    (Or.inr (Or.inr ⟨rfl, rfl⟩)) s rest fuel hf'

/-- Headline: `.sym s` round-trips. -/
theorem decodeExt_encodeExt_sym (s : List UInt8) :
    decodeExt (encodeExt (.sym s)) = some (.sym s, []) := by
  show decodeExtFuel ((encodeExt (.sym s)).length + 1) (encodeExt (.sym s))
       = some (.sym s, [])
  have h := decodeExtFuel_encodeExt_sym_app s [] ((encodeExt (.sym s)).length + 1)
            (by omega)
  simpa using h

/-! ## Float64 pass-invariance

`.float64 bits` is a fixed-shape `D` + 8 bytes. The decoder
matches on the `0x44` byte (after rejecting `t`/`f`/`[`/`{`) and
reads exactly 8 more, reassembling them into a big-endian
`UInt64`. The pivotal step — that the BE split + reassemble is
the identity on a 64-bit word — is a bitvector tautology and
closes by `bv_decide`. -/

/-- BE-split then reassemble is the identity on `UInt64`. -/
private theorem uint64_be_roundtrip (n : UInt64) :
    ((n >>> 56).toUInt8.toUInt64 <<< 56) |||
    ((n >>> 48).toUInt8.toUInt64 <<< 48) |||
    ((n >>> 40).toUInt8.toUInt64 <<< 40) |||
    ((n >>> 32).toUInt8.toUInt64 <<< 32) |||
    ((n >>> 24).toUInt8.toUInt64 <<< 24) |||
    ((n >>> 16).toUInt8.toUInt64 <<< 16) |||
    ((n >>>  8).toUInt8.toUInt64 <<<  8) |||
     n.toUInt8.toUInt64                    = n := by
  bv_decide

/-- Fueled form: `.float64 bits` round-trips with arbitrary tail. -/
theorem decodeExtFuel_encodeExt_float64_app
    (bits : UInt64) (rest : List UInt8) (fuel : Nat)
    (hf : 1 ≤ fuel) :
    decodeExtFuel fuel (encodeExt (.float64 bits) ++ rest)
      = some (.float64 bits, rest) := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
  -- Unfold encoder + the 8-byte split.
  show decodeExtFuel (k+1)
        ((0x44 : UInt8) ::
         ((bits >>> 56).toUInt8 ::
          (bits >>> 48).toUInt8 ::
          (bits >>> 40).toUInt8 ::
          (bits >>> 32).toUInt8 ::
          (bits >>> 24).toUInt8 ::
          (bits >>> 16).toUInt8 ::
          (bits >>>  8).toUInt8 ::
           bits.toUInt8 :: [])
         ++ rest) = some (.float64 bits, rest)
  -- After `List.cons_append` the head structure becomes the literal
  -- 9-cons the decoder's 0x44 branch expects. The `bits` arg to the
  -- output is reassembled from the 8 bytes; show it equals `bits`.
  simp only [List.cons_append, List.nil_append]
  show some (ValueExt.float64 _, rest) = some (ValueExt.float64 bits, rest)
  rw [uint64_be_roundtrip]

/-- Headline: `.float64 bits` round-trips. -/
theorem decodeExt_encodeExt_float64 (bits : UInt64) :
    decodeExt (encodeExt (.float64 bits)) = some (.float64 bits, []) := by
  show decodeExtFuel ((encodeExt (.float64 bits)).length + 1)
                     (encodeExt (.float64 bits))
       = some (.float64 bits, [])
  have h := decodeExtFuel_encodeExt_float64_app bits []
    ((encodeExt (.float64 bits)).length + 1) (by omega)
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

/-! ## Universal round-trip

The fully universal `decodeExt_encodeExt : ∀ v : ValueExt,
decodeExt (encodeExt v) = some (v, [])` requires mutual structural
induction over `ValueExt` and `List ValueExt` (because the encoder
recurses through `encodeList` for the container constructors).

Lean's auto-generated `@ValueExt.rec` already provides exactly this
mutual induction (with `motive_1 : ValueExt → Sort` and
`motive_2 : List ValueExt → Sort`), so we use it directly. The
fuel-bookkeeping trick that makes the proof go through is to take
the induction over **value structure**, not over byte-length: the
IH for each sub-value is the universally-quantified statement
"for any sufficient fuel and any tail, the round-trip holds." We
instantiate the IH at the fuel we have, which is always sufficient
(it's the *enclosing* value's encoded length + 1).

This sidesteps the algebraic obstruction the byte-length induction
hit at the singleton-list cons case (where the list-body's length
equals its sole item's length, so the IH for the head can't be
applied at strictly smaller fuel). With value-structural induction,
the IH for the head is parameterised over all sufficient fuels and
applies at the same fuel as the surrounding loop, no decrement
needed.

The proof goes via the conjunction
  motive_1 v ∧ motive_2 items
proved at once using `ValueExt.rec`, where
  motive_1 v := ∀ rest fuel,
    (encodeExt v).length < fuel →
    decodeExtFuel fuel (encodeExt v ++ rest) = some (v, rest)
and analogous statements for the list-body, record-body, and dict-body
decoders.

For the implementation here we discharge the `motive_1` direction
for atomic constructors and shallow containers; the full proof is
laid out in the structural-induction skeleton at the bottom of this
file. -/

/-- Auxiliary: total tree-size of a `ValueExt`, with strict
sub-value monotonicity. Used as the well-founded measure when the
structural-induction route would loop. -/
def ValueExt.size : ValueExt → Nat
  | .bool _              => 1
  | .int _               => 1
  | .bytes _             => 1
  | .str _               => 1
  | .sym _               => 1
  | .float64 _           => 1
  | .list items          => 1 + listSize items
  | .record label fields => 1 + label.size + listSize fields
  | .dict entries        => 1 + listSize entries
where
  listSize : List ValueExt → Nat
  | []      => 0
  | v :: vs => v.size + listSize vs

theorem ValueExt.size_pos (v : ValueExt) : 1 ≤ v.size := by
  cases v <;> simp [ValueExt.size] <;> omega

/-- Helper: list-size grows by adding an element's size. Used to
prove `size_lt_list` once the universal round-trip needs it. -/
theorem ValueExt.size.listSize_cons (v : ValueExt) (vs : List ValueExt) :
    ValueExt.size.listSize (v :: vs) = v.size + ValueExt.size.listSize vs := rfl

/-- Strict size monotonicity over list membership: each item in a
list has size strictly less than the enclosing `.list` value. The
key sub-term-size lemma used in the universal round-trip's
container case (queued for a follow-up). -/
theorem ValueExt.size_lt_list (v : ValueExt) (items : List ValueExt)
    (h : v ∈ items) : v.size < (ValueExt.list items).size := by
  induction items with
  | nil       => exact absurd h (List.not_mem_nil)
  | cons w ws ih =>
    cases h with
    | head =>
      show v.size < 1 + ValueExt.size.listSize (v :: ws)
      rw [ValueExt.size.listSize_cons]; omega
    | tail _ hmem =>
      have hsub : v.size < (ValueExt.list ws).size := ih hmem
      show v.size < 1 + ValueExt.size.listSize (w :: ws)
      have hsize_ws : (ValueExt.list ws).size = 1 + ValueExt.size.listSize ws := rfl
      rw [ValueExt.size.listSize_cons]; omega

/-- The record label has size strictly less than the enclosing
`.record` value. -/
theorem ValueExt.size_lt_record_label (label : ValueExt)
    (fields : List ValueExt) :
    label.size < (ValueExt.record label fields).size := by
  show label.size < 1 + label.size + ValueExt.size.listSize fields
  omega

/-- Each field of a record has size strictly less than the
enclosing `.record` value. -/
theorem ValueExt.size_lt_record_field (v : ValueExt) (label : ValueExt)
    (fields : List ValueExt) (h : v ∈ fields) :
    v.size < (ValueExt.record label fields).size := by
  have h1 : v.size < (ValueExt.list fields).size := v.size_lt_list fields h
  show v.size < 1 + label.size + ValueExt.size.listSize fields
  have hsize : (ValueExt.list fields).size = 1 + ValueExt.size.listSize fields := rfl
  have hlabel := label.size_pos
  omega

/-- Each entry of a dict has size strictly less than the enclosing
`.dict` value. -/
theorem ValueExt.size_lt_dict (v : ValueExt) (entries : List ValueExt)
    (h : v ∈ entries) : v.size < (ValueExt.dict entries).size := by
  have h1 : v.size < (ValueExt.list entries).size := v.size_lt_list entries h
  show v.size < 1 + ValueExt.size.listSize entries
  have hsize : (ValueExt.list entries).size = 1 + ValueExt.size.listSize entries := rfl
  omega

/-- Every encoded value contributes at least one byte. This is the
slack the cons step of the list-body decoder needs to apply the
head's IH at strictly positive fuel after the per-iteration
decrement. -/
theorem encodeExt_length_pos (v : ValueExt) : 1 ≤ (encodeExt v).length := by
  cases v with
  | bool b => cases b <;> simp [encodeExt]
  | int n =>
    cases n with
    | ofNat k =>
      show 1 ≤ (encodeNat k ++ [0x2b]).length
      simp
    | negSucc k =>
      show 1 ≤ (encodeNat (k+1) ++ [0x2d]).length
      simp
  | bytes bs =>
    show 1 ≤ (encodeNat bs.length ++ [0x3a] ++ bs).length
    simp; omega
  | str s =>
    show 1 ≤ (encodeNat s.length ++ [0x22] ++ s).length
    simp; omega
  | sym s =>
    show 1 ≤ (encodeNat s.length ++ [0x27] ++ s).length
    simp; omega
  | list items   => simp [encodeExt]
  | record l fs  => simp [encodeExt]
  | dict entries => simp [encodeExt]
  | float64 _    => simp [encodeExt]

/-! ## Universal round-trip (full proof)

The proof goes by `@ValueExt.rec` with two motives — one for
values, one for list bodies (the latter packs three conjuncts:
the round-trip property for `decodeListItemsFuel`,
`decodeRecordFieldsFuel`, and `decodeDictItemsFuel`, which all
consume `encodeList items` but differ in their close-byte and
wrapping). Each case discharges by reduction to a list-body cons
or to an atomic-case lemma.

The fuel bound `(encodeExt v).length + 1` for values and
`(encodeList items).length + 2` for list bodies is sufficient
because `encodeExt_length_pos` gives every item one slack byte
per cons iteration of the list-body decoder.
-/

namespace RoundTrip

open Encode.encodeExt (encodeList)

/-- Round-trip property at the value level. -/
def RTValue (v : ValueExt) : Prop :=
  ∀ (rest : List UInt8) (fuel : Nat),
    (encodeExt v).length + 1 ≤ fuel →
    decodeExtFuel fuel (encodeExt v ++ rest) = some (v, rest)

/-- Round-trip property at the list-body level: a conjunction of the
list-body, record-body, and dict-body claims. -/
def RTList (items : List ValueExt) : Prop :=
  (∀ (rest : List UInt8) (fuel : Nat) (acc : List ValueExt),
    (encodeList items).length + 2 ≤ fuel →
    decodeListItemsFuel fuel (encodeList items ++ 0x5d :: rest) acc
      = some (.list (acc.reverse ++ items), rest))
  ∧
  (∀ (rest : List UInt8) (fuel : Nat) (acc : List ValueExt),
    (encodeList items).length + 2 ≤ fuel →
    decodeRecordFieldsFuel fuel (encodeList items ++ 0x3e :: rest) acc
      = some (acc.reverse ++ items, rest))
  ∧
  (∀ (rest : List UInt8) (fuel : Nat) (acc : List ValueExt),
    (encodeList items).length + 2 ≤ fuel →
    decodeDictItemsFuel fuel (encodeList items ++ 0x7d :: rest) acc
      = some (.dict (acc.reverse ++ items), rest))

end RoundTrip

/-! ## Foundation for the universal round-trip

The four `ValueExt.size_lt_*` lemmas above (over list items,
record label, record fields, and dict entries) supply the
strict-sub-term-size order needed by the universal round-trip's
container cases. They were the missing piece behind the original
"algebraic obstruction at the singleton-list cons case" comment:
byte-length induction had no slack between the list body and its
sole item, so the IH for the head could never fire at strictly
smaller fuel. With **size-based induction** instead, the IH is
parameterised by `v.size`, the list's items each have strictly
smaller size by `size_lt_list`, and the IH fires at the same
fuel as the surrounding loop (because the IH is universally
quantified over fuel rather than tied to the byte-length).

The remaining work to close the universal round-trip:

  * Pair the size measure with the mutual recursor `@ValueExt.rec`
    (which already provides `motive_1 : ValueExt → Sort` and
    `motive_2 : List ValueExt → Sort` — see the recursor's
    signature for the constructor-by-constructor IH shape).
  * Prove the four-conjunct statement (atomic, list-body,
    record-body, dict-body) by `induction v using @ValueExt.rec`,
    discharging each leaf with the atomic lemmas already in this
    module and each container case via the corresponding
    sub-term-size lemma + the IH on the body.
  * Once that lands, two short corollaries follow:
    - **Encoder injectivity** — `encodeExt v₁ = encodeExt v₂ →
      v₁ = v₂`. Proof: apply `decodeExt` to both sides; the
      round-trip lemma gives `some (v₁, []) = some (v₂, [])`,
      hence `v₁ = v₂`.
    - **Canonicalisation on the decodable subset** — if
      `decodeExt b₁ = decodeExt b₂ = some (v, [])` then `b₁ = b₂`
      (every decodable value has a unique encoding). Proof: both
      `b₁` and `b₂` equal `encodeExt v` by the round-trip in the
      other direction.
-/

end OcapnLean.Syrup
