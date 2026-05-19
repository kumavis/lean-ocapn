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

/-! ## Multi-element container round-trip

Closed by mutual induction over `ValueExt` and `List ValueExt`
using the auto-generated `@ValueExt.rec`. The motive split is

  * `motive_1 v := RTValue v` — value-level round-trip
  * `motive_2 items := RTListAll items` — the three body-decoder
    round-trips packaged together (list `]`, record `>`, dict `}`)

Each cons step in the body decoders reduces via the step lemmas
below, after observing that the head byte of `encodeExt head`
is never one of the closing brackets (`]`, `>`, `}`).
-/

namespace RoundTrip

open Encode.encodeExt (encodeList)

/-! ### Step lemmas — single-step reduction for each body decoder
when the head byte is not the body's closer. -/

/-- List-body decoder: one cons step (head byte ≠ `]`). -/
theorem decodeListItemsFuel_cons_step
    (fuel : Nat) (b : UInt8) (tail : List UInt8) (acc : List ValueExt)
    (hb : b ≠ 0x5d) :
    decodeListItemsFuel (fuel + 1) (b :: tail) acc
      = Option.bind (decodeExtFuel fuel (b :: tail))
                    (fun p => decodeListItemsFuel fuel p.2 (p.1 :: acc)) := by
  rw [decodeListItemsFuel.eq_def]
  by_cases hb' : b = 0x5d
  · exact absurd hb' hb
  · simp only []
    cases h : decodeExtFuel fuel (b :: tail) with
    | none => rfl
    | some p => cases p with | mk v rest => rfl

/-- Record-fields decoder: one cons step (head byte ≠ `>`). -/
theorem decodeRecordFieldsFuel_cons_step
    (fuel : Nat) (b : UInt8) (tail : List UInt8) (acc : List ValueExt)
    (hb : b ≠ 0x3e) :
    decodeRecordFieldsFuel (fuel + 1) (b :: tail) acc
      = Option.bind (decodeExtFuel fuel (b :: tail))
                    (fun p => decodeRecordFieldsFuel fuel p.2 (p.1 :: acc)) := by
  rw [decodeRecordFieldsFuel.eq_def]
  by_cases hb' : b = 0x3e
  · exact absurd hb' hb
  · simp only []
    cases h : decodeExtFuel fuel (b :: tail) with
    | none => rfl
    | some p => cases p with | mk v rest => rfl

/-- Dict-body decoder: one cons step (head byte ≠ `}`). -/
theorem decodeDictItemsFuel_cons_step
    (fuel : Nat) (b : UInt8) (tail : List UInt8) (acc : List ValueExt)
    (hb : b ≠ 0x7d) :
    decodeDictItemsFuel (fuel + 1) (b :: tail) acc
      = Option.bind (decodeExtFuel fuel (b :: tail))
                    (fun p => decodeDictItemsFuel fuel p.2 (p.1 :: acc)) := by
  rw [decodeDictItemsFuel.eq_def]
  by_cases hb' : b = 0x7d
  · exact absurd hb' hb
  · simp only []
    cases h : decodeExtFuel fuel (b :: tail) with
    | none => rfl
    | some p => cases p with | mk v rest => rfl

/-! ### Head-byte analysis

The first byte of every `encodeExt v` lies in
`{0x74, 0x66, 0x5b, 0x3c, 0x7b, 0x44}` or is an ASCII digit — and
none of those is `0x5d` / `0x3e` / `0x7d`. Used to dispatch a
container's body decoder past the cons step when the head item is
about to be decoded. -/

theorem encodeExt_head_alt (v : ValueExt) (b : UInt8) (tail : List UInt8)
    (h : encodeExt v = b :: tail) :
    b = 0x74 ∨ b = 0x66 ∨ b = 0x5b ∨ b = 0x3c ∨ b = 0x7b ∨ b = 0x44
    ∨ isDigit b = true := by
  cases v with
  | bool x => cases x <;> (simp [encodeExt] at h; obtain ⟨rfl, _⟩ := h; simp)
  | int n =>
    cases n with
    | ofNat k =>
      have henc : encodeExt (.int (Int.ofNat k)) = encodeNat k ++ [0x2b] := rfl
      rw [henc] at h
      obtain ⟨d, ds, hcons⟩ : ∃ d ds, encodeNat k = d :: ds := by
        rcases h2 : encodeNat k with _ | ⟨d, ds⟩
        · exact absurd h2 (encodeNat_ne_nil k)
        · exact ⟨d, ds, rfl⟩
      rw [hcons] at h
      simp at h
      obtain ⟨rfl, _⟩ := h
      right; right; right; right; right; right
      exact encodeNat_all_digits k d (hcons ▸ List.mem_cons_self ..)
    | negSucc k =>
      have henc : encodeExt (.int (Int.negSucc k)) = encodeNat (k+1) ++ [0x2d] := rfl
      rw [henc] at h
      obtain ⟨d, ds, hcons⟩ : ∃ d ds, encodeNat (k+1) = d :: ds := by
        rcases h2 : encodeNat (k+1) with _ | ⟨d, ds⟩
        · exact absurd h2 (encodeNat_ne_nil (k+1))
        · exact ⟨d, ds, rfl⟩
      rw [hcons] at h
      simp at h
      obtain ⟨rfl, _⟩ := h
      right; right; right; right; right; right
      exact encodeNat_all_digits (k+1) d (hcons ▸ List.mem_cons_self ..)
  | bytes bs =>
    have henc : encodeExt (.bytes bs) = encodeNat bs.length ++ [0x3a] ++ bs := rfl
    rw [henc] at h
    obtain ⟨d, ds, hcons⟩ : ∃ d ds, encodeNat bs.length = d :: ds := by
      rcases h2 : encodeNat bs.length with _ | ⟨d, ds⟩
      · exact absurd h2 (encodeNat_ne_nil bs.length)
      · exact ⟨d, ds, rfl⟩
    rw [hcons] at h
    simp at h
    obtain ⟨rfl, _⟩ := h
    right; right; right; right; right; right
    exact encodeNat_all_digits bs.length d (hcons ▸ List.mem_cons_self ..)
  | str s =>
    have henc : encodeExt (.str s) = encodeNat s.length ++ [0x22] ++ s := rfl
    rw [henc] at h
    obtain ⟨d, ds, hcons⟩ : ∃ d ds, encodeNat s.length = d :: ds := by
      rcases h2 : encodeNat s.length with _ | ⟨d, ds⟩
      · exact absurd h2 (encodeNat_ne_nil s.length)
      · exact ⟨d, ds, rfl⟩
    rw [hcons] at h
    simp at h
    obtain ⟨rfl, _⟩ := h
    right; right; right; right; right; right
    exact encodeNat_all_digits s.length d (hcons ▸ List.mem_cons_self ..)
  | sym s =>
    have henc : encodeExt (.sym s) = encodeNat s.length ++ [0x27] ++ s := rfl
    rw [henc] at h
    obtain ⟨d, ds, hcons⟩ : ∃ d ds, encodeNat s.length = d :: ds := by
      rcases h2 : encodeNat s.length with _ | ⟨d, ds⟩
      · exact absurd h2 (encodeNat_ne_nil s.length)
      · exact ⟨d, ds, rfl⟩
    rw [hcons] at h
    simp at h
    obtain ⟨rfl, _⟩ := h
    right; right; right; right; right; right
    exact encodeNat_all_digits s.length d (hcons ▸ List.mem_cons_self ..)
  | list _ => simp [encodeExt] at h; obtain ⟨rfl, _⟩ := h; simp
  | record _ _ => simp [encodeExt] at h; obtain ⟨rfl, _⟩ := h; simp
  | dict _ => simp [encodeExt] at h; obtain ⟨rfl, _⟩ := h; simp
  | float64 _ => simp [encodeExt] at h; obtain ⟨rfl, _⟩ := h; simp

theorem encodeExt_head_ne_rbracket (v : ValueExt) (b : UInt8) (tail : List UInt8)
    (h : encodeExt v = b :: tail) : b ≠ 0x5d := by
  intro habs
  rcases encodeExt_head_alt v b tail h with h1|h1|h1|h1|h1|h1|h1
  all_goals first | (rw [habs] at h1; cases h1) | (rw [habs] at h1; simp [isDigit] at h1)

theorem encodeExt_head_ne_rangle (v : ValueExt) (b : UInt8) (tail : List UInt8)
    (h : encodeExt v = b :: tail) : b ≠ 0x3e := by
  intro habs
  rcases encodeExt_head_alt v b tail h with h1|h1|h1|h1|h1|h1|h1
  all_goals first | (rw [habs] at h1; cases h1) | (rw [habs] at h1; simp [isDigit] at h1)

theorem encodeExt_head_ne_rbrace (v : ValueExt) (b : UInt8) (tail : List UInt8)
    (h : encodeExt v = b :: tail) : b ≠ 0x7d := by
  intro habs
  rcases encodeExt_head_alt v b tail h with h1|h1|h1|h1|h1|h1|h1
  all_goals first | (rw [habs] at h1; cases h1) | (rw [habs] at h1; simp [isDigit] at h1)

/-! ### Motives and main theorem -/

/-- Round-trip property at the value level. -/
def RTValue (v : ValueExt) : Prop :=
  ∀ (rest : List UInt8) (fuel : Nat),
    (encodeExt v).length + 1 ≤ fuel →
    decodeExtFuel fuel (encodeExt v ++ rest) = some (v, rest)

/-- Round-trip property for list bodies (`]`-terminated). -/
def RTListBody (items : List ValueExt) : Prop :=
  ∀ (rest : List UInt8) (fuel : Nat) (acc : List ValueExt),
    (encodeList items).length + 2 ≤ fuel →
    decodeListItemsFuel fuel (encodeList items ++ 0x5d :: rest) acc
      = some (.list (acc.reverse ++ items), rest)

/-- Round-trip property for record fields (`>`-terminated). -/
def RTRecordFields (items : List ValueExt) : Prop :=
  ∀ (rest : List UInt8) (fuel : Nat) (acc : List ValueExt),
    (encodeList items).length + 2 ≤ fuel →
    decodeRecordFieldsFuel fuel (encodeList items ++ 0x3e :: rest) acc
      = some (acc.reverse ++ items, rest)

/-- Round-trip property for dict bodies (`}`-terminated). -/
def RTDictBody (items : List ValueExt) : Prop :=
  ∀ (rest : List UInt8) (fuel : Nat) (acc : List ValueExt),
    (encodeList items).length + 2 ≤ fuel →
    decodeDictItemsFuel fuel (encodeList items ++ 0x7d :: rest) acc
      = some (.dict (acc.reverse ++ items), rest)

/-- Conjunction used as `motive_2` in the mutual induction. -/
def RTListAll (items : List ValueExt) : Prop :=
  RTListBody items ∧ RTRecordFields items ∧ RTDictBody items

/-- **Universal round-trip — value-level.** For every extended Syrup
value `v`, `decodeExtFuel` consumes exactly `encodeExt v` and leaves
the trailing `rest` untouched (given sufficient fuel). -/
theorem encodeExt_rt (v : ValueExt) : RTValue v := by
  refine @ValueExt.rec
    (motive_1 := fun v => RTValue v)
    (motive_2 := fun items => RTListAll items)
    ?bool ?int ?bytes ?str ?sym ?list ?record ?dict ?float64
    ?listNil ?listCons v
  -- bool
  case bool =>
    intro b rest fuel _
    exact decodeExtFuel_encodeExt_bool_app b rest fuel (by omega)
  -- int
  case int =>
    intro n rest fuel hf
    exact decodeExtFuel_encodeExt_int_app n rest fuel hf
  -- bytes
  case bytes =>
    intro bs rest fuel hf
    exact decodeExtFuel_encodeExt_bytes_app bs rest fuel hf
  -- str
  case str =>
    intro s rest fuel hf
    exact decodeExtFuel_encodeExt_str_app s rest fuel hf
  -- sym
  case sym =>
    intro s rest fuel hf
    exact decodeExtFuel_encodeExt_sym_app s rest fuel hf
  -- float64
  case float64 =>
    intro bits rest fuel _
    exact decodeExtFuel_encodeExt_float64_app bits rest fuel (by omega)
  -- list: use RTListBody from motive_2
  case list =>
    intro items ih rest fuel hf
    have henc : encodeExt (.list items) = 0x5b :: encodeList items ++ [0x5d] := rfl
    rw [henc]
    obtain ⟨m, rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
    show decodeExtFuel (m + 1) ((0x5b :: encodeList items ++ [0x5d]) ++ rest)
          = some (.list items, rest)
    have hreduce : decodeExtFuel (m + 1) ((0x5b :: encodeList items ++ [0x5d]) ++ rest)
                 = decodeListItemsFuel m (encodeList items ++ 0x5d :: rest) [] := by
      show (if (0x5b : UInt8) = 0x74 then _ else
            if (0x5b : UInt8) = 0x66 then _ else
            if (0x5b : UInt8) = 0x5b then _ else _) = _
      rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
      congr 1
      simp [List.append_assoc]
    rw [hreduce]
    have hflen : (encodeList items).length + 2 ≤ m := by
      have henclen : (encodeExt (.list items)).length
                   = (encodeList items).length + 2 := by
        show (0x5b :: encodeList items ++ [0x5d]).length = _
        simp
      omega
    simpa using ih.1 rest m [] hflen
  -- record
  case record =>
    intro label fields ih_label ih_fields rest fuel hf
    have henc : encodeExt (.record label fields)
              = 0x3c :: encodeExt label ++ encodeList fields ++ [0x3e] := rfl
    rw [henc]
    obtain ⟨m, rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
    show decodeExtFuel (m + 1) ((0x3c :: encodeExt label ++ encodeList fields ++ [0x3e]) ++ rest)
          = some (.record label fields, rest)
    have hreduce : decodeExtFuel (m + 1)
                     ((0x3c :: encodeExt label ++ encodeList fields ++ [0x3e]) ++ rest)
                = (match decodeExtFuel m (encodeExt label ++ encodeList fields ++ [0x3e] ++ rest) with
                   | none => none
                   | some (l, r1) =>
                     match decodeRecordFieldsFuel m r1 [] with
                     | none => none
                     | some (fs, r2) => some (.record l fs, r2)) := by
      show (if (0x3c : UInt8) = 0x74 then _ else
            if (0x3c : UInt8) = 0x66 then _ else
            if (0x3c : UInt8) = 0x5b then _ else
            if (0x3c : UInt8) = 0x7b then _ else
            if (0x3c : UInt8) = 0x44 then _ else
            if (0x3c : UInt8) = 0x3c then _ else _) = _
      rw [if_neg (by decide), if_neg (by decide), if_neg (by decide),
          if_neg (by decide), if_neg (by decide), if_pos rfl]
      congr 1 <;> simp [List.append_assoc]
    rw [hreduce]
    have hlabel_len : (encodeExt label).length + 1 ≤ m := by
      have henclen : (encodeExt (.record label fields)).length
                   = (encodeExt label).length + (encodeList fields).length + 2 := by
        show (0x3c :: encodeExt label ++ encodeList fields ++ [0x3e]).length = _
        simp; omega
      omega
    have hlabel := ih_label (encodeList fields ++ [0x3e] ++ rest) m hlabel_len
    have hlabel' : decodeExtFuel m (encodeExt label ++ encodeList fields ++ [0x3e] ++ rest)
                 = some (label, encodeList fields ++ [0x3e] ++ rest) := by
      have : encodeExt label ++ encodeList fields ++ [0x3e] ++ rest
           = encodeExt label ++ (encodeList fields ++ [0x3e] ++ rest) := by
        simp [List.append_assoc]
      rw [this]
      exact hlabel
    rw [hlabel']
    simp only []
    have hfields_len : (encodeList fields).length + 2 ≤ m := by
      have henclen : (encodeExt (.record label fields)).length
                   = (encodeExt label).length + (encodeList fields).length + 2 := by
        show (0x3c :: encodeExt label ++ encodeList fields ++ [0x3e]).length = _
        simp; omega
      have := encodeExt_length_pos label
      omega
    have hfields := ih_fields.2.1 rest m [] hfields_len
    have hfields' : decodeRecordFieldsFuel m (encodeList fields ++ [0x3e] ++ rest) []
                  = some (fields, rest) := by
      have hrearr : encodeList fields ++ [0x3e] ++ rest
                  = encodeList fields ++ 0x3e :: rest := by simp
      rw [hrearr]
      simpa using hfields
    rw [hfields']
  -- dict
  case dict =>
    intro entries ih rest fuel hf
    have henc : encodeExt (.dict entries) = 0x7b :: encodeList entries ++ [0x7d] := rfl
    rw [henc]
    obtain ⟨m, rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
    show decodeExtFuel (m + 1) ((0x7b :: encodeList entries ++ [0x7d]) ++ rest)
          = some (.dict entries, rest)
    have hreduce : decodeExtFuel (m + 1) ((0x7b :: encodeList entries ++ [0x7d]) ++ rest)
                 = decodeDictItemsFuel m (encodeList entries ++ 0x7d :: rest) [] := by
      show (if (0x7b : UInt8) = 0x74 then _ else
            if (0x7b : UInt8) = 0x66 then _ else
            if (0x7b : UInt8) = 0x5b then _ else
            if (0x7b : UInt8) = 0x7b then _ else _) = _
      rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
      congr 1
      simp [List.append_assoc]
    rw [hreduce]
    have hflen : (encodeList entries).length + 2 ≤ m := by
      have henclen : (encodeExt (.dict entries)).length
                   = (encodeList entries).length + 2 := by
        show (0x7b :: encodeList entries ++ [0x7d]).length = _
        simp
      omega
    simpa using ih.2.2 rest m [] hflen
  -- motive_2 nil: RTListAll []
  case listNil =>
    have hflen : (encodeList ([] : List ValueExt)).length = 0 := rfl
    refine ⟨?_, ?_, ?_⟩
    · intro rest fuel acc hf
      rw [hflen] at hf
      show decodeListItemsFuel fuel ([] ++ 0x5d :: rest) acc = _
      simp only [List.nil_append, List.append_nil]
      obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      rfl
    · intro rest fuel acc hf
      rw [hflen] at hf
      show decodeRecordFieldsFuel fuel ([] ++ 0x3e :: rest) acc = _
      simp only [List.nil_append, List.append_nil]
      obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      rfl
    · intro rest fuel acc hf
      rw [hflen] at hf
      show decodeDictItemsFuel fuel ([] ++ 0x7d :: rest) acc = _
      simp only [List.nil_append, List.append_nil]
      obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      rfl
  -- motive_2 cons: RTListAll (head :: tail) from RTValue head + RTListAll tail
  case listCons =>
    intro head tail ih_head ih_tail
    refine ⟨?_, ?_, ?_⟩
    · -- RTListBody (head :: tail)
      intro rest fuel acc hf
      have henc : encodeList (head :: tail) = encodeExt head ++ encodeList tail := rfl
      rw [henc]
      obtain ⟨b, et, hheq⟩ : ∃ b et, encodeExt head = b :: et := by
        rcases h : encodeExt head with _ | ⟨b, et⟩
        · have := encodeExt_length_pos head; rw [h] at this; simp at this
        · exact ⟨b, et, rfl⟩
      have hne : b ≠ 0x5d := encodeExt_head_ne_rbracket head b et hheq
      rw [hheq]
      obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by
        have : (encodeExt head ++ encodeList tail).length + 2 ≤ fuel := hf
        omega⟩
      have hrearr : (b :: et ++ encodeList tail) ++ 0x5d :: rest
                  = b :: (et ++ encodeList tail ++ 0x5d :: rest) := by simp
      rw [hrearr]
      rw [decodeListItemsFuel_cons_step k b _ acc hne]
      have hhead_len : (encodeExt head).length + 1 ≤ k := by
        have : (encodeExt head ++ encodeList tail).length + 2 ≤ k + 1 := hf
        simp at this
        have := encodeExt_length_pos head
        omega
      have hhead := ih_head (encodeList tail ++ 0x5d :: rest) k hhead_len
      have hhead' : decodeExtFuel k (b :: (et ++ encodeList tail ++ 0x5d :: rest))
                  = some (head, encodeList tail ++ 0x5d :: rest) := by
        have : b :: (et ++ encodeList tail ++ 0x5d :: rest)
             = (b :: et) ++ (encodeList tail ++ 0x5d :: rest) := by simp
        rw [this, ← hheq]; exact hhead
      rw [hhead']
      simp only [Option.bind]
      have htail_len : (encodeList tail).length + 2 ≤ k := by
        have : (encodeExt head ++ encodeList tail).length + 2 ≤ k + 1 := hf
        simp at this
        have := encodeExt_length_pos head
        omega
      have htail := ih_tail.1 rest k (head :: acc) htail_len
      have : (head :: acc).reverse ++ tail = acc.reverse ++ head :: tail := by simp
      rw [this] at htail
      exact htail
    · -- RTRecordFields (head :: tail)
      intro rest fuel acc hf
      have henc : encodeList (head :: tail) = encodeExt head ++ encodeList tail := rfl
      rw [henc]
      obtain ⟨b, et, hheq⟩ : ∃ b et, encodeExt head = b :: et := by
        rcases h : encodeExt head with _ | ⟨b, et⟩
        · have := encodeExt_length_pos head; rw [h] at this; simp at this
        · exact ⟨b, et, rfl⟩
      have hne : b ≠ 0x3e := encodeExt_head_ne_rangle head b et hheq
      rw [hheq]
      obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by
        have : (encodeExt head ++ encodeList tail).length + 2 ≤ fuel := hf
        omega⟩
      have hrearr : (b :: et ++ encodeList tail) ++ 0x3e :: rest
                  = b :: (et ++ encodeList tail ++ 0x3e :: rest) := by simp
      rw [hrearr]
      rw [decodeRecordFieldsFuel_cons_step k b _ acc hne]
      have hhead_len : (encodeExt head).length + 1 ≤ k := by
        have : (encodeExt head ++ encodeList tail).length + 2 ≤ k + 1 := hf
        simp at this
        have := encodeExt_length_pos head
        omega
      have hhead := ih_head (encodeList tail ++ 0x3e :: rest) k hhead_len
      have hhead' : decodeExtFuel k (b :: (et ++ encodeList tail ++ 0x3e :: rest))
                  = some (head, encodeList tail ++ 0x3e :: rest) := by
        have : b :: (et ++ encodeList tail ++ 0x3e :: rest)
             = (b :: et) ++ (encodeList tail ++ 0x3e :: rest) := by simp
        rw [this, ← hheq]; exact hhead
      rw [hhead']
      simp only [Option.bind]
      have htail_len : (encodeList tail).length + 2 ≤ k := by
        have : (encodeExt head ++ encodeList tail).length + 2 ≤ k + 1 := hf
        simp at this
        have := encodeExt_length_pos head
        omega
      have htail := ih_tail.2.1 rest k (head :: acc) htail_len
      have : (head :: acc).reverse ++ tail = acc.reverse ++ head :: tail := by simp
      rw [this] at htail
      exact htail
    · -- RTDictBody (head :: tail)
      intro rest fuel acc hf
      have henc : encodeList (head :: tail) = encodeExt head ++ encodeList tail := rfl
      rw [henc]
      obtain ⟨b, et, hheq⟩ : ∃ b et, encodeExt head = b :: et := by
        rcases h : encodeExt head with _ | ⟨b, et⟩
        · have := encodeExt_length_pos head; rw [h] at this; simp at this
        · exact ⟨b, et, rfl⟩
      have hne : b ≠ 0x7d := encodeExt_head_ne_rbrace head b et hheq
      rw [hheq]
      obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by
        have : (encodeExt head ++ encodeList tail).length + 2 ≤ fuel := hf
        omega⟩
      have hrearr : (b :: et ++ encodeList tail) ++ 0x7d :: rest
                  = b :: (et ++ encodeList tail ++ 0x7d :: rest) := by simp
      rw [hrearr]
      rw [decodeDictItemsFuel_cons_step k b _ acc hne]
      have hhead_len : (encodeExt head).length + 1 ≤ k := by
        have : (encodeExt head ++ encodeList tail).length + 2 ≤ k + 1 := hf
        simp at this
        have := encodeExt_length_pos head
        omega
      have hhead := ih_head (encodeList tail ++ 0x7d :: rest) k hhead_len
      have hhead' : decodeExtFuel k (b :: (et ++ encodeList tail ++ 0x7d :: rest))
                  = some (head, encodeList tail ++ 0x7d :: rest) := by
        have : b :: (et ++ encodeList tail ++ 0x7d :: rest)
             = (b :: et) ++ (encodeList tail ++ 0x7d :: rest) := by simp
        rw [this, ← hheq]; exact hhead
      rw [hhead']
      simp only [Option.bind]
      have htail_len : (encodeList tail).length + 2 ≤ k := by
        have : (encodeExt head ++ encodeList tail).length + 2 ≤ k + 1 := hf
        simp at this
        have := encodeExt_length_pos head
        omega
      have htail := ih_tail.2.2 rest k (head :: acc) htail_len
      have : (head :: acc).reverse ++ tail = acc.reverse ++ head :: tail := by simp
      rw [this] at htail
      exact htail

end RoundTrip

/-! ## Top-level universal round-trip + corollaries -/

/-- **Top-level universal round-trip.** For every extended Syrup
value `v`, the round-trip `decodeExt (encodeExt v) = some (v, [])`
holds. -/
theorem decodeExt_encodeExt (v : ValueExt) :
    decodeExt (encodeExt v) = some (v, []) := by
  show decodeExtFuel ((encodeExt v).length + 1) (encodeExt v) = some (v, [])
  have h := RoundTrip.encodeExt_rt v [] ((encodeExt v).length + 1) (by omega)
  simpa using h

/-- **Encoder injectivity.** Two values with the same encoding are
equal. (Follows directly from the round-trip via decode.) -/
theorem encodeExt_injective {v₁ v₂ : ValueExt}
    (h : encodeExt v₁ = encodeExt v₂) : v₁ = v₂ := by
  have h1 := decodeExt_encodeExt v₁
  have h2 := decodeExt_encodeExt v₂
  rw [h] at h1
  rw [h1] at h2
  simpa using h2

end OcapnLean.Syrup
