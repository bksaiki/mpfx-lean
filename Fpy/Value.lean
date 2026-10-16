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
from the record with fields `fs`. A record is an association list; projection
reads the first field with the label. -/
inductive Val where
  | bool (b : Bool)
  | num (n : Num)
  | list (vs : List Val)
  | record (fs : List (Label × Val))
  | real
  | ctx (fs : List (Label × Val))

/-- `R` and `ctx fs` are contexts. -/
def Val.IsCtx : Val → Prop
  | .real | .ctx _ => True
  | _ => False

end Fpy
