import Fpy.Ops

/-!
# Special values of the FPy operators
-/

namespace FpyTest

open Fpy Mpfx

local notation "nan" => (WithSpecial.special Special.nan : Num)
local notation "posInf" => (WithSpecial.special (Special.inf false) : Num)
local notation "negInf" => (WithSpecial.special (Special.inf true) : Num)

example : Num.div (.finite 1) (.finite 0) = posInf := by simp [Num.div]
example : Num.div (.finite (-1)) (.finite 0) = negInf := by simp [Num.div]
example : Num.div (.finite 0) (.finite 0) = nan := by simp [Num.div]
example : Num.div (.finite 1) posInf = .finite 0 := rfl
example : Num.mul posInf (.finite 0) = nan := by simp [Num.mul]
example : Num.add posInf negInf = nan := rfl
example : Num.sqrt (.finite (-1)) = nan := by simp [Num.sqrt]
example : Num.sqrt negInf = nan := rfl

example : Num.logb (.finite 8) = .finite 3 := by
  have : Nat.log 2 8 = 3 := Nat.log_pow (by norm_num) 3
  simp [Num.logb, this]
example : Num.logb (.finite 0) = negInf := by simp [Num.logb]
example : Num.logb negInf = posInf := rfl
example : Num.exp2 negInf = .finite 0 := rfl

example : Num.min nan (.finite 0) = nan := rfl
example : Num.min (.finite 0) negInf = negInf := rfl
example : Num.min (.finite 0) posInf = .finite 0 := rfl
example : Num.max (.finite 0) posInf = posInf := rfl

example : Num.lt negInf (.finite 0) = true := rfl
example : Num.lt nan (.finite 0) = false := rfl
example : Num.eq nan nan = false := rfl
example : Num.le posInf posInf = true := rfl

end FpyTest
