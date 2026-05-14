/-!
# OCapN Abstract Data Model

Mirrors `projects/ocapn-spec/draft-specifications/Model.md`. This module
declares the algebra of OCapN *passable values* without committing to any
wire encoding — the Syrup codec lives in `OcapnLean.Syrup`.

The four top-level categories are **Atom**, **Container**, **Reference**,
and **Error**. References are split into **Target** (a local or remote
object) and **Promise** (an eventually-settled return value).
-/

namespace OcapnLean

/-- An OCapN floating-point value. Distinguishes ±0 and collapses all NaNs
to a single canonical bit-pattern; matches the Model spec. -/
structure Float64 where
  bits : UInt64
deriving DecidableEq, Repr

namespace Float64
def nan : Float64 := ⟨0x7ff8_0000_0000_0000⟩
def posInf : Float64 := ⟨0x7ff0_0000_0000_0000⟩
def negInf : Float64 := ⟨0xfff0_0000_0000_0000⟩
def posZero : Float64 := ⟨0x0000_0000_0000_0000⟩
def negZero : Float64 := ⟨0x8000_0000_0000_0000⟩

def isNaN (f : Float64) : Bool :=
  (f.bits &&& 0x7ff0_0000_0000_0000) == 0x7ff0_0000_0000_0000 &&
  (f.bits &&& 0x000f_ffff_ffff_ffff) != 0
end Float64

/-- Atoms are values that cannot contain or refer to other values. -/
inductive Atom
  | undefined
  | null
  | bool (b : Bool)
  | int (n : Int)
  | float (f : Float64)
  | str (s : String)
  | bytes (bs : ByteArray)
  | sym (name : String)

instance : Repr Atom where
  reprPrec a _ := match a with
    | .undefined => "undefined"
    | .null      => "null"
    | .bool b    => repr b
    | .int n     => repr n
    | .float f   => "float " ++ repr f
    | .str s     => repr s
    | .bytes bs  => "bytes(" ++ toString bs.size ++ ")"
    | .sym s     => "sym " ++ repr s

/-- A reference is either a Target (object) or a Promise. References are
opaque to the data model; their identity lives in the CapTP layer. We
parameterise the value type by the reference handle type. -/
inductive Ref (R : Type)
  | target  (r : R)
  | promise (r : R)
deriving Repr

/-- A passable value, parameterised by the reference handle type `R`. -/
inductive Value (R : Type)
  | atom    (a : Atom)
  | list    (xs : List (Value R))
  | struct  (fields : List (String × Value R))
  | tagged  (tag : String) (v : Value R)
  | ref     (r : Ref R)
  | error   (reason : Value R) -- spec leaves error contents open; payload is a sub-value

end OcapnLean
