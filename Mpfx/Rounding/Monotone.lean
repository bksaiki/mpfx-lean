import Mpfx.Rounding.Basic

/-!
# Monotonicity of rounding

Every mode is monotone: `x ≤ x'` gives `rnd x ≤ rnd x'` (`RoundsFinite.mono`).
The directed modes are monotone by their extremal property, and the modes
toward and away from zero by sign. For round-to-odd and the nearest modes, a
crossing pair puts both inputs in one gap (`IsFaithfulRound.cross`), where
parity alternation, resp. the distances to the gap's ends, forbids it.
-/

namespace Mpfx

theorem RoundsFinite.mono_toNegative {F : FiniteFormat} {x x' : ℝ} {y y' : Dyadic}
    (hx : x ≤ x') (hy : RoundsFinite F .toNegative x y)
    (hy' : RoundsFinite F .toNegative x' y') : (y : ℝ) ≤ y' :=
  hy'.2.2 y hy.1 (hy.2.1.trans hx)

theorem RoundsFinite.mono_toPositive {F : FiniteFormat} {x x' : ℝ} {y y' : Dyadic}
    (hx : x ≤ x') (hy : RoundsFinite F .toPositive x y)
    (hy' : RoundsFinite F .toPositive x' y') : (y : ℝ) ≤ y' :=
  hy.2.2 y' hy'.1 (hx.trans hy'.2.1)

/-- Faithful roundings that cross put both inputs in one gap: `y'` rounds `x`
and `x'` down, `y` rounds both up, and `y' ≤ x ≤ x' < y`. -/
theorem IsFaithfulRound.cross {F : FiniteFormat} {x x' : ℝ} {y y' : Dyadic} (hx : x ≤ x')
    (hy : IsFaithfulRound F x y) (hy' : IsFaithfulRound F x' y') (hlt : (y' : ℝ) < y) :
    RoundsFinite F .toPositive x y ∧ RoundsFinite F .toPositive x' y ∧
      RoundsFinite F .toNegative x y' ∧ RoundsFinite F .toNegative x' y' ∧
        x' < y ∧ (y' : ℝ) ≤ x := by
  rcases hy with ⟨hym, hyx, -⟩ | ⟨hym, hxy, hymin⟩ <;>
    rcases hy' with ⟨hym', hyx', hymax'⟩ | ⟨hym', hxy', hymin'⟩
  · exact absurd (hymax' y hym (hyx.trans hx)) (not_le.mpr hlt)
  · exact absurd (hyx.trans (hx.trans hxy')) (not_le.mpr hlt)
  · have hx'y : x' < y := lt_of_not_ge fun h => absurd (hymax' y hym h) (not_le.mpr hlt)
    have hy'x : (y' : ℝ) ≤ x :=
      le_of_not_gt fun h => absurd (hymin y' hym' h.le) (not_le.mpr hlt)
    exact ⟨⟨hym, hxy, hymin⟩, ⟨hym, hx'y.le, fun z hz hz' => hymin z hz (hx.trans hz')⟩,
      ⟨hym', hy'x, fun z hz hz' => hymax' z hz (hz'.trans hx)⟩, ⟨hym', hyx', hymax'⟩,
      hx'y, hy'x⟩
  · exact absurd (hymin y' hym' (hx.trans hxy')) (not_le.mpr hlt)

/-- **Rounding is monotone**, in every mode. -/
theorem RoundsFinite.mono {F : FiniteFormat} {rm : RoundingMode} (h : ¬ F.IsUndefined rm)
    {x x' : ℝ} {y y' : Dyadic} (hx : x ≤ x') (hy : RoundsFinite F.unbounded rm x y)
    (hy' : RoundsFinite F.unbounded rm x' y') : (y : ℝ) ≤ y' := by
  -- Equal inputs round equally; otherwise a crossing pair brackets both in one gap.
  have same : x = x' → (y : ℝ) ≤ y' := fun hxx => by
    subst hxx; rw [RoundsFinite.unique h hy hy']
  cases rm with
  | toNegative => exact mono_toNegative hx hy hy'
  | toPositive => exact mono_toPositive hx hy hy'
  | toZero =>
    rcases le_total 0 x with hx0 | hx0
    · exact mono_toNegative hx ((toNegative_iff_toZero_of_nonneg _ hx0 y).mpr hy)
        ((toNegative_iff_toZero_of_nonneg _ (hx0.trans hx) y').mpr hy')
    rcases le_total x' 0 with hx0' | hx0'
    · exact mono_toPositive hx ((toPositive_iff_toZero_of_nonpos _ (hx.trans hx0') y).mpr hy)
        ((toPositive_iff_toZero_of_nonpos _ hx0' y').mpr hy')
    · exact (hy.isFaithfulRound.nonpos hx0).trans (hy'.isFaithfulRound.nonneg hx0')
  | awayZero =>
    rcases le_total 0 x with hx0 | hx0
    · exact mono_toPositive hx ((toPositive_iff_awayZero_of_nonneg _ hx0 y).mpr hy)
        ((toPositive_iff_awayZero_of_nonneg _ (hx0.trans hx) y').mpr hy')
    rcases le_total x' 0 with hx0' | hx0'
    · exact mono_toNegative hx ((toNegative_iff_awayZero_of_nonpos _ (hx.trans hx0') y).mpr hy)
        ((toNegative_iff_awayZero_of_nonpos _ hx0' y').mpr hy')
    · exact (hy.isFaithfulRound.nonpos hx0).trans (hy'.isFaithfulRound.nonneg hx0')
  | toOdd =>
    rcases eq_or_lt_of_le hx with hxx | hxx
    · exact same hxx
    by_contra hlt
    obtain ⟨-, hu', -, hd', hx'y, hy'x⟩ := hy.2.1.cross hx hy'.2.1 (lt_of_not_ge hlt)
    exact (isOdd_alternate_of_bracketing h hd' hu' (lt_of_le_of_lt hy'x hxx).ne').mp
      (hy.2.2 (lt_of_le_of_lt hx hx'y).ne) (hy'.2.2 (lt_of_le_of_lt hy'x hxx).ne')
  | nearest tb =>
    rcases eq_or_lt_of_le hx with hxx | hxx
    · exact same hxx
    by_contra hlt
    obtain ⟨-, hu', hd, -, hx'y, hy'x⟩ := hy.isFaithfulRound.cross hx hy'.isFaithfulRound
      (lt_of_not_ge hlt)
    have h₁ := hy.nearest_min hd.1 (isFaithfulRound_iff_directed.mpr (.inl hd))
    have h₂ := hy'.nearest_min hu'.1 (isFaithfulRound_iff_directed.mpr (.inr hu'))
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)] at h₁
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)] at h₂
    linarith

end Mpfx
