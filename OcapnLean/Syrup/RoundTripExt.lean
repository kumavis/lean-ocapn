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
    (hd_ne_lbr : d ≠ 0x5b) (hd_ne_lbrc : d ≠ 0x7b) (hd_ne_la : d ≠ 0x3c)
    (hall : ∀ b ∈ d :: ds_tail, isDigit b = true)
    (hsep : isDigit sep = false) :
    decodeExtFuel (fuel + 1) (d :: ds_tail ++ sep :: rest)
      = decodeExtAfterDigits (d :: ds_tail) (sep :: rest) := by
  show (if d = 0x74 then _ else
        if d = 0x66 then _ else
        if d = 0x5b then _ else
        if d = 0x7b then _ else
        if d = 0x3c then _ else
        if isDigit d then _ else none) = _
  rw [if_neg hd_ne_t, if_neg hd_ne_f, if_neg hd_ne_lbr,
      if_neg hd_ne_lbrc, if_neg hd_ne_la, if_pos hd]
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
  have hd_ne_la : d ≠ 0x3c := by intro heq; rw [heq] at hd; cases hd
  have hall : ∀ b ∈ d :: ds_tail, isDigit b = true := by
    rw [← hcons]; exact encodeNat_all_digits k
  have hk_eq : encodeExt (.int (Int.ofNat k)) ++ rest
             = d :: ds_tail ++ 0x2b :: rest := by
    show encodeNat k ++ [0x2b] ++ rest = _
    rw [hcons]; simp
  rw [hk_eq]
  rw [decodeExtFuel_digits_then d ds_tail 0x2b rest m hd hd_ne_t hd_ne_f
        hd_ne_lbr hd_ne_lbrc hd_ne_la hall plus_not_digit]
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
  have hd_ne_la : d ≠ 0x3c := by intro heq; rw [heq] at hd; cases hd
  have hall : ∀ b ∈ d :: ds_tail, isDigit b = true := by
    rw [← hcons]; exact encodeNat_all_digits (k+1)
  have hk_eq : encodeExt (.int (Int.negSucc k)) ++ rest
             = d :: ds_tail ++ 0x2d :: rest := by
    show encodeNat (k+1) ++ [0x2d] ++ rest = _
    rw [hcons]; simp
  rw [hk_eq]
  rw [decodeExtFuel_digits_then d ds_tail 0x2d rest m hd hd_ne_t hd_ne_f
        hd_ne_lbr hd_ne_lbrc hd_ne_la hall minus_not_digit]
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
  have hd_ne_la : d ≠ 0x3c := by intro heq; rw [heq] at hd; cases hd
  have hall : ∀ b ∈ d :: ds_tail, isDigit b = true := by
    rw [← hcons]; exact encodeNat_all_digits bs.length
  have hk_eq : encodeNat bs.length ++ [sep] ++ bs ++ rest
             = d :: ds_tail ++ sep :: (bs ++ rest) := by
    rw [hcons]; simp
  rw [hk_eq]
  rw [decodeExtFuel_digits_then d ds_tail sep (bs ++ rest) m hd hd_ne_t hd_ne_f
        hd_ne_lbr hd_ne_lbrc hd_ne_la hall hsep]
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
