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

/-- Inner decoder once we know the first byte is a digit: read the
digit run, then dispatch on the separator. -/
def decodeAfterDigits (ds : List UInt8) : List UInt8 → Option (Value × List UInt8)
  | []          => none
  | 0x2b :: r   => some (.int (Int.ofNat (digitsToNat ds)), r)
  | 0x2d :: r   =>
    let n := digitsToNat ds
    if n = 0 then none                              -- "-0" forbidden by spec
    else some (.int (-(Int.ofNat n)), r)
  | 0x3a :: r   =>
    let n := digitsToNat ds
    if r.length < n then none
    else some (.bytes (r.take n), r.drop n)
  | _ :: _      => none

/-- Top-level decoder. -/
def decode : List UInt8 → Option (Value × List UInt8)
  | []        => none
  | b :: rest =>
    if b = 0x74 then some (.bool true, rest)
    else if b = 0x66 then some (.bool false, rest)
    else if isDigit b then
      let (ds, after) := takeDigits (b :: rest)
      decodeAfterDigits ds after
    else none

end Decode

------------------------------------------------------------------------
-- Helper lemmas
------------------------------------------------------------------------

namespace Internal
open Encode Decode

/-- `digitByte d` (for `d < 10`) reads back as `0x30 + d`. -/
theorem digitByte_toNat (d : Nat) (h : d < 10) :
    (digitByte d).toNat = 0x30 + d := by
  unfold digitByte
  have hlt : 0x30 + d < 256 := by omega
  simp [UInt8.toNat_ofNat, Nat.mod_eq_of_lt hlt]

/-- Each ASCII digit byte is `isDigit`. -/
theorem digitByte_isDigit (d : Nat) (h : d < 10) :
    isDigit (digitByte d) = true := by
  match d, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ =>
    decide

/-- Each ASCII digit byte is not `0x74` (`'t'`). -/
theorem digitByte_ne_t (d : Nat) (h : d < 10) : digitByte d ≠ 0x74 := by
  match d, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ =>
    decide

/-- Each ASCII digit byte is not `0x66` (`'f'`). -/
theorem digitByte_ne_f (d : Nat) (h : d < 10) : digitByte d ≠ 0x66 := by
  match d, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ =>
    decide

/-- Every byte in `encodeNat n` is an ASCII digit. -/
theorem encodeNat_all_digits : ∀ n, ∀ b ∈ encodeNat n, isDigit b = true := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    unfold encodeNat
    split
    · rename_i hlt
      intro b hb
      simp at hb; subst hb
      exact digitByte_isDigit n hlt
    · rename_i hge
      have hlt10 : n % 10 < 10 := Nat.mod_lt n (by decide)
      have hdiv : n / 10 < n := Nat.div_lt_self (by omega) (by decide)
      intro b hb
      rw [List.mem_append] at hb
      rcases hb with hb | hb
      · exact ih (n / 10) hdiv b hb
      · simp at hb; subst hb; exact digitByte_isDigit (n % 10) hlt10

/-- `encodeNat n` is never empty (even `n=0` gives `['0']`). -/
theorem encodeNat_ne_nil (n : Nat) : encodeNat n ≠ [] := by
  unfold encodeNat
  split <;> simp

/-- The first byte of `encodeNat n` is a digit (so not `'t'`, `'f'`). -/
theorem encodeNat_head_isDigit (n : Nat) :
    ∀ b bs, encodeNat n = b :: bs → isDigit b = true :=
  fun b bs hcons => encodeNat_all_digits n b (hcons ▸ List.mem_cons_self ..)

/-- `digitsToNat` distributes over append-of-singleton. -/
theorem digitsToNat_append_singleton (xs : List UInt8) (b : UInt8) :
    digitsToNat (xs ++ [b]) = digitsToNat xs * 10 + (b.toNat - 0x30) := by
  simp [digitsToNat, List.foldl_append]

/-- The decoder side of the natural-number round-trip. -/
theorem digitsToNat_encodeNat : ∀ n, digitsToNat (encodeNat n) = n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    unfold encodeNat
    split
    · rename_i hlt
      simp [digitsToNat, digitByte_toNat n hlt]
    · rename_i hge
      have hlt10 : n % 10 < 10 := Nat.mod_lt n (by decide)
      have hdiv : n / 10 < n := Nat.div_lt_self (by omega) (by decide)
      rw [digitsToNat_append_singleton, ih (n / 10) hdiv,
          digitByte_toNat (n % 10) hlt10]
      have hsub : (0x30 : Nat) + n % 10 - 0x30 = n % 10 := by omega
      rw [hsub]
      omega

/-- `takeDigits` on a list whose prefix `ds` is all digits and which
hits a non-digit `b` first cleanly splits at the boundary. -/
theorem takeDigits_all_digit_prefix
    (ds : List UInt8) (h : ∀ d ∈ ds, isDigit d = true)
    (b : UInt8) (hb : isDigit b = false) (rest : List UInt8) :
    takeDigits (ds ++ b :: rest) = (ds, b :: rest) := by
  induction ds with
  | nil => simp [takeDigits, hb]
  | cons d ds ih =>
    have hd : isDigit d = true := h d (by simp)
    have hds : ∀ d' ∈ ds, isDigit d' = true :=
      fun d' hd' => h d' (by simp [hd'])
    simp [takeDigits, hd, ih hds]

/-- `+` (`0x2b`) is not a digit. -/
theorem plus_not_digit : isDigit 0x2b = false := by decide
/-- `-` (`0x2d`) is not a digit. -/
theorem minus_not_digit : isDigit 0x2d = false := by decide
/-- `:` (`0x3a`) is not a digit. -/
theorem colon_not_digit : isDigit 0x3a = false := by decide

end Internal

------------------------------------------------------------------------
-- Round-trip theorems
------------------------------------------------------------------------

open Encode Decode Internal

/-- Universal round-trip for booleans. -/
theorem decode_encode_bool (b : Bool) :
    decode (encode (.bool b)) = some (.bool b, []) := by
  cases b <;> decide

/-- A helper: when `ds` is an all-digit non-empty prefix and `next`
starts with a known separator, the decoder takes the digit run and
defers to `decodeAfterDigits`. -/
private theorem decode_digits_then
    (d : UInt8) (ds_tail : List UInt8)
    (sep : UInt8) (rest : List UInt8)
    (hd : isDigit d = true)
    (hd_ne_t : d ≠ 0x74) (hd_ne_f : d ≠ 0x66)
    (hall : ∀ b ∈ d :: ds_tail, isDigit b = true)
    (hsep : isDigit sep = false) :
    decode (d :: ds_tail ++ sep :: rest)
    = decodeAfterDigits (d :: ds_tail) (sep :: rest) := by
  -- The decoder reduces to `decodeAfterDigits ds after` once we
  -- discharge the byte tests.
  show (if d = 0x74 then _ else
        if d = 0x66 then _ else
        if isDigit d then _ else none) = _
  rw [if_neg hd_ne_t, if_neg hd_ne_f, if_pos hd]
  show (let (ds, after) := takeDigits (d :: ds_tail ++ sep :: rest)
        decodeAfterDigits ds after) = _
  have hsplit : takeDigits (d :: ds_tail ++ sep :: rest)
              = (d :: ds_tail, sep :: rest) :=
    takeDigits_all_digit_prefix (d :: ds_tail) hall sep hsep rest
  rw [hsplit]

/-- Universal round-trip. -/
theorem decode_encode : ∀ v : Value, decode (encode v) = some (v, []) := by
  intro v
  cases v with
  | bool b => exact decode_encode_bool b
  | int n =>
    cases n with
    | ofNat k =>
      -- encode (.int k) = encodeNat k ++ [0x2b]
      show decode (encodeNat k ++ [0x2b]) = some (.int (Int.ofNat k), [])
      obtain ⟨d, ds_tail, hcons⟩ : ∃ d ds, encodeNat k = d :: ds := by
        rcases h : encodeNat k with _ | ⟨d, ds⟩
        · exact absurd h (encodeNat_ne_nil k)
        · exact ⟨d, ds, rfl⟩
      -- Reshape the goal to expose the (digit :: tail) ++ [sep] form.
      have hk_eq : encodeNat k ++ [0x2b] = d :: ds_tail ++ [0x2b] := by
        rw [hcons]
      rw [hk_eq]
      -- The digit-properties we need.
      have hd : isDigit d = true := by
        have := encodeNat_all_digits k
        exact this d (hcons ▸ List.mem_cons_self ..)
      -- For ≠'t' and ≠'f', we use the structure of encodeNat to find d = digitByte _.
      -- Easier: argue from `isDigit d = true` directly.
      have hd_ne_t : d ≠ 0x74 := by intro heq; rw [heq] at hd; cases hd
      have hd_ne_f : d ≠ 0x66 := by intro heq; rw [heq] at hd; cases hd
      have hall : ∀ b ∈ d :: ds_tail, isDigit b = true := by
        rw [← hcons]; exact encodeNat_all_digits k
      rw [decode_digits_then d ds_tail 0x2b [] hd hd_ne_t hd_ne_f hall plus_not_digit]
      show decodeAfterDigits (d :: ds_tail) (0x2b :: []) = _
      simp only [decodeAfterDigits]
      rw [← hcons, digitsToNat_encodeNat]
    | negSucc k =>
      show decode (encodeNat (k+1) ++ [0x2d]) = some (.int (Int.negSucc k), [])
      obtain ⟨d, ds_tail, hcons⟩ : ∃ d ds, encodeNat (k+1) = d :: ds := by
        rcases h : encodeNat (k+1) with _ | ⟨d, ds⟩
        · exact absurd h (encodeNat_ne_nil (k+1))
        · exact ⟨d, ds, rfl⟩
      have hk_eq : encodeNat (k+1) ++ [0x2d] = d :: ds_tail ++ [0x2d] := by
        rw [hcons]
      rw [hk_eq]
      have hd : isDigit d = true := by
        have := encodeNat_all_digits (k+1)
        exact this d (hcons ▸ List.mem_cons_self ..)
      have hd_ne_t : d ≠ 0x74 := by intro heq; rw [heq] at hd; cases hd
      have hd_ne_f : d ≠ 0x66 := by intro heq; rw [heq] at hd; cases hd
      have hall : ∀ b ∈ d :: ds_tail, isDigit b = true := by
        rw [← hcons]; exact encodeNat_all_digits (k+1)
      rw [decode_digits_then d ds_tail 0x2d [] hd hd_ne_t hd_ne_f hall minus_not_digit]
      show decodeAfterDigits (d :: ds_tail) (0x2d :: []) = _
      simp only [decodeAfterDigits]
      rw [← hcons, digitsToNat_encodeNat]
      have hne : k + 1 ≠ 0 := Nat.succ_ne_zero k
      simp [hne, Int.negSucc_eq]
  | bytes bs =>
    show decode (encodeNat bs.length ++ [0x3a] ++ bs) = some (.bytes bs, [])
    -- Rearrange [0x3a] ++ bs to (0x3a :: bs).
    have hrearr : encodeNat bs.length ++ [0x3a] ++ bs
                = encodeNat bs.length ++ (0x3a :: bs) := by simp
    rw [hrearr]
    obtain ⟨d, ds_tail, hcons⟩ : ∃ d ds, encodeNat bs.length = d :: ds := by
      rcases h : encodeNat bs.length with _ | ⟨d, ds⟩
      · exact absurd h (encodeNat_ne_nil bs.length)
      · exact ⟨d, ds, rfl⟩
    have hk_eq : encodeNat bs.length ++ (0x3a :: bs)
               = d :: ds_tail ++ (0x3a :: bs) := by rw [hcons]
    rw [hk_eq]
    have hd : isDigit d = true := by
      have := encodeNat_all_digits bs.length
      exact this d (hcons ▸ List.mem_cons_self ..)
    have hd_ne_t : d ≠ 0x74 := by intro heq; rw [heq] at hd; cases hd
    have hd_ne_f : d ≠ 0x66 := by intro heq; rw [heq] at hd; cases hd
    have hall : ∀ b ∈ d :: ds_tail, isDigit b = true := by
      rw [← hcons]; exact encodeNat_all_digits bs.length
    rw [decode_digits_then d ds_tail 0x3a bs hd hd_ne_t hd_ne_f hall colon_not_digit]
    show decodeAfterDigits (d :: ds_tail) (0x3a :: bs) = _
    simp only [decodeAfterDigits]
    rw [← hcons, digitsToNat_encodeNat]
    -- The if-guard `rest.length < n` evaluates to `bs.length < bs.length = False`.
    simp

/-- Integer specialisation. -/
theorem decode_encode_int (n : Int) :
    decode (encode (.int n)) = some (.int n, []) :=
  decode_encode (.int n)

/-- Bytestring specialisation. -/
theorem decode_encode_bytes (bs : List UInt8) :
    decode (encode (.bytes bs)) = some (.bytes bs, []) :=
  decode_encode (.bytes bs)

-- The 16 concrete `example` lemmas below are now redundant with
-- `decode_encode`, but they're kept as documentation and a sanity
-- belt — any breakage in `decode_encode` would also break them, and
-- they read more legibly than a universal theorem when debugging.

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
