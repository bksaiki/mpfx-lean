import Mpfx.Rounding.Special

/-!
# Special-value and overflow tables

The standard tables against IEEE 754 §7.4, and specials through `rnd`.
-/

namespace Mpfx

variable {F : FiniteFormat} {S : SpecialMap F.toFormat} {x : ℝ} (hb : F.b ≠ ⊤)
  (hinf : ∀ negative, Special.inf negative ∈ F.specials)

/-! ### IEEE 754 §7.4 overflow -/

example (tb : TieBreak) (h : ¬ F.IsUndefined (.nearest tb))
    (hov : Overflows F (.nearest tb) x) (hx : 0 < x) :
    rnd F S (OverflowMap.ieee F (.nearest tb) hb hinf) (.nearest tb) (.finite x) =
      .value (.special (.inf false)) := by
  rw [rnd_of_overflows_pos h hov hx]; rfl

example (h : ¬ F.IsUndefined (.nearest .toEven))
    (hov : Overflows F (.nearest .toEven) x) (hx : x < 0) :
    rnd F S (OverflowMap.ieee F (.nearest .toEven) hb hinf) (.nearest .toEven) (.finite x) =
      .value (.special (.inf true)) := by
  rw [rnd_of_overflows_neg h hov hx]; rfl

example (hov : Overflows F .toZero x) (hx : 0 < x) :
    rnd F S (OverflowMap.ieee F .toZero hb hinf) .toZero (.finite x) =
      .value (.finite (F.maxFinite hb)) := by
  rw [rnd_of_overflows_pos (not_isUndefined_toZero F) hov hx]; rfl

example (hov : Overflows F .toZero x) (hx : x < 0) :
    rnd F S (OverflowMap.ieee F .toZero hb hinf) .toZero (.finite x) =
      .value (.finite (-F.maxFinite hb)) := by
  rw [rnd_of_overflows_neg (not_isUndefined_toZero F) hov hx]; rfl

example (hov : Overflows F .toPositive x) (hx : 0 < x) :
    rnd F S (OverflowMap.ieee F .toPositive hb hinf) .toPositive (.finite x) =
      .value (.special (.inf false)) := by
  rw [rnd_of_overflows_pos (not_isUndefined_toPositive F) hov hx]; rfl

example (hov : Overflows F .toPositive x) (hx : x < 0) :
    rnd F S (OverflowMap.ieee F .toPositive hb hinf) .toPositive (.finite x) =
      .value (.finite (-F.maxFinite hb)) := by
  rw [rnd_of_overflows_neg (not_isUndefined_toPositive F) hov hx]; rfl

example (hov : Overflows F .toNegative x) (hx : 0 < x) :
    rnd F S (OverflowMap.ieee F .toNegative hb hinf) .toNegative (.finite x) =
      .value (.finite (F.maxFinite hb)) := by
  rw [rnd_of_overflows_pos (not_isUndefined_toNegative F) hov hx]; rfl

example (hov : Overflows F .toNegative x) (hx : x < 0) :
    rnd F S (OverflowMap.ieee F .toNegative hb hinf) .toNegative (.finite x) =
      .value (.special (.inf true)) := by
  rw [rnd_of_overflows_neg (not_isUndefined_toNegative F) hov hx]; rfl

/-! ### Saturation and NaN -/

example (rm : RoundingMode) (h : ¬ F.IsUndefined rm) (hov : Overflows F rm x)
    (hx : 0 < x) :
    rnd F S (OverflowMap.saturate F hb) rm (.finite x) = .value (.finite (F.maxFinite hb)) := by
  rw [rnd_of_overflows_pos h hov hx]; rfl

example (hnan : Special.nan ∈ F.specials) (rm : RoundingMode) (h : ¬ F.IsUndefined rm)
    (hov : Overflows F rm x) (hx : x < 0) :
    rnd F S (OverflowMap.toNaN F.toFormat hnan) rm (.finite x) = .value (.special .nan) := by
  rw [rnd_of_overflows_neg h hov hx]; rfl

/-! ### Special inputs -/

/-- Under `SpecialMap.exact`, specials are fixed points of `rnd`. -/
example (O : OverflowMap F.toFormat) (rm : RoundingMode) (h : ∀ s, s ∈ F.specials)
    (s : Special) :
    rnd F (SpecialMap.exact F.toFormat h) O rm (.special s) = .value (.special s) := rfl

example (O : OverflowMap F.toFormat) (rm : RoundingMode) (hnan : Special.nan ∈ F.specials) :
    rnd F (SpecialMap.saturate F hb hnan) O rm (.special (.inf true)) =
      .value (.finite (-F.maxFinite hb)) := rfl

example (O : OverflowMap F.toFormat) (rm : RoundingMode) (hnan : Special.nan ∈ F.specials) :
    rnd F (SpecialMap.saturate F hb hnan) O rm (.special .nan) = .value (.special .nan) := rfl

/-- Special inputs stay defined even when the mode is undefined. -/
example (O : OverflowMap F.toFormat) (rm : RoundingMode) (hnan : Special.nan ∈ F.specials) :
    rnd F (SpecialMap.toNaN F.toFormat hnan) O rm (.special (.inf false)) =
      .value (.special .nan) := rfl

end Mpfx
