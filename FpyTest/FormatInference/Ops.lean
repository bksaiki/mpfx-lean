import Fpy.FormatInference.Ops

/-!
# Precision in the abstract operators
-/

namespace FpyTest

open Fpy Mpfx

/-- A value with quantum `1` and magnitude at most `7` needs 3 digits. -/
example : Format.bitsFor 7 0 = 3 := by
  have : Nat.clog 2 8 = 3 := Nat.clog_pow 2 3 (by norm_num)
  simpa [Format.bitsFor] using this

/-- A power of two adds no digits to a product… -/
example : precMul ((1 : ℕ) : Prec) ((5 : ℕ) : Prec) = ((5 : ℕ) : Prec) := by
  simp [precMul]

/-- …while other factors add their precisions. -/
example : precMul ((3 : ℕ) : Prec) ((5 : ℕ) : Prec) = ((8 : ℕ) : Prec) := by
  simp only [precMul]
  rw [if_neg (by decide)]
  rfl

end FpyTest
