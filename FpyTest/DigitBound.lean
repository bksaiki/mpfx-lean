import Fpy.DigitBound.Table
import FpyTest.Rewrite.Lower

/-!
# Table 2

D-Arith's premise for `x + y` under `R`, from Table 2's rows; and a witness that
the draft's `IEEE754(es, nb, rm)` row, `μ ≤ m + 1`, fails below the smallest
subnormal: rounding `2⁻¹¹` up into E4M3 gives `2⁻⁹`.
-/

namespace FpyTest

open Fpy Fpy.DigitBound Mpfx

example {decode : List (Label × Val) → Option RoundCtx} (l₁ m₁ l₂ m₂ : EInt) :
    ArithOK decode (some .real) .add [(.const l₁, .const m₁, none), (.const l₂, .const m₂, none)]
      0 2 (bounds 0 (.min (.const l₁) (.const l₂)) (.add (.max (.const m₁) (.const m₂))
        (.const (1 : ℤ))) ⟨trivial, trivial⟩ ⟨⟨trivial, trivial⟩, trivial⟩ ++ [])
      (.var 1) (.var 0) :=
  ArithOK.comp (opOK_add (.inl rfl) (by exact ⟨trivial, trivial⟩)
    (by exact ⟨⟨trivial, trivial⟩, trivial⟩)) rndOK_real
    (fresh_bounds 0 _ _) (Fresh.nil 2) fun _ h => by obtain rfl := Option.mem_some_iff.mp h; trivial

theorem log_two_zpow (z : ℤ) : Int.log 2 ((2 : ℝ) ^ z) = z := by
  simpa using Int.log_zpow (R := ℝ) (b := 2) (by norm_num) z

/-- RTP into E4M3 sends `2⁻¹¹` to `2⁻⁹`. -/
theorem rtp_e4m3 :
    ((rndUnbounded e4m3 .toPositive (2 ^ (-11 : ℤ)) (not_isUndefined_toPositive _) :
      Mpfx.Dyadic) : ℝ) = 2 ^ (-9 : ℤ) := by
  rw [RoundsFinite.unique_toPositive (rndUnbounded_satisfies _ _ _ _) (rndUp_spec _ _), rndUp_eq,
    canonicalExp_expFinite (p := 4) rfl rfl (by positivity), abs_of_pos (by positivity),
    log_two_zpow]
  norm_num

theorem draft_ieee_rm_bound :
    msbOf (.finite ((rndUnbounded e4m3 .toPositive (2 ^ (-11 : ℤ))
      (not_isUndefined_toPositive _) : Mpfx.Dyadic) : ℝ)) = ((-9 : ℤ) : EInt) ∧
    msbOf (.finite ((2 : ℝ) ^ (-11 : ℤ))) + ((1 : ℤ) : EInt) = ((-10 : ℤ) : EInt) := by
  rw [rtp_e4m3, msbOf_of_ne_zero (by positivity), msbOf_of_ne_zero (by positivity),
    abs_of_pos (by positivity), abs_of_pos (by positivity), log_two_zpow, log_two_zpow,
    coe_add_coe]
  norm_num

end FpyTest
