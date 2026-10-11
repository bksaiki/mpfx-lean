import Mpfx.Format.Defs

/-!
# FPy values (Figure 10)

Numbers, records, lists, booleans and rounding contexts.
-/

namespace Fpy

open Mpfx

/-- Numbers: the extended reals `ℝ ∪ {±∞, NaN}`. -/
abbrev Num := WithSpecial ℝ

abbrev Label := String

/-- Values. `real` is the real context `R`, and `ctx fs` is the context built
from the record with fields `fs`. -/
inductive Val where
  | bool (b : Bool)
  | num (n : Num)
  | list (vs : List Val)
  | record (fs : List (Label × Val))
  | real
  | ctx (fs : List (Label × Val))

end Fpy
