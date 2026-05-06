import Mpfx.Rounding

/-!
# Correct double rounding

The seven theorems from §5.2 / Fig. 9 of the paper. Proofs follow Appendix A.

Each theorem is stated *spec-relationally*: given that `z` is the rounding of
`x` in `F₂` and `w` is the rounding of `z` in `F₁`, conclude that `w` is also
the rounding of `x` in `F₁`. This matches the paper's reasoning style and
sidesteps having to define `rnd` constructively.

The overflow conditions on `b` from Fig. 9 are not needed in this formulation:
they ensure that the rounded values *exist*, not that the relationship holds.
The spec form takes existence of `z` and `w` as hypotheses.
-/

namespace Mpfx

namespace AbstractFormat

/-- **rnd-RTZ-RTZ** (Fig. 9). If `F₁ ⊆ F₂` and the chained RTZ-rounding
`(F₂, RTZ) ; (F₁, RTZ)` produces results `z` and `w`, then `w` is also the
RTZ-rounding of `x` in `F₁` directly. -/
theorem rndRTZ_RTZ {F₁ F₂ : AbstractFormat} (hsub : F₁ ⊆ F₂)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsRTZ F₂ x z) (hw : RoundsRTZ F₁ (z : ℝ) w) :
    RoundsRTZ F₁ x w := by
  obtain ⟨hzF, hzbnd, hzsign, hzmax⟩ := hz
  obtain ⟨hwF, hwbnd, hwsign, hwmax⟩ := hw
  refine ⟨hwF, le_trans hwbnd hzbnd, ?_, ?_⟩
  · -- w * x ≥ 0
    rcases lt_trichotomy ((z : ℝ)) 0 with hzlt | hzeq | hzgt
    · -- z < 0
      have hx_le : x ≤ 0 := by
        by_contra hxlt
        push Not at hxlt
        linarith [mul_neg_of_neg_of_pos hzlt hxlt]
      have hw_le : (w : ℝ) ≤ 0 := by
        by_contra hwlt
        push Not at hwlt
        linarith [mul_neg_of_pos_of_neg hwlt hzlt]
      exact mul_nonneg_iff.mpr (Or.inr ⟨hw_le, hx_le⟩)
    · -- z = 0
      have hw_eq : (w : ℝ) = 0 := by
        have h : |(w : ℝ)| ≤ 0 := by rw [hzeq, abs_zero] at hwbnd; exact hwbnd
        exact abs_nonpos_iff.mp h
      rw [hw_eq]; simp
    · -- z > 0
      have hx_ge : 0 ≤ x := by
        by_contra hxlt
        push Not at hxlt
        linarith [mul_neg_of_pos_of_neg hzgt hxlt]
      have hw_ge : 0 ≤ (w : ℝ) := by
        by_contra hwlt
        push Not at hwlt
        linarith [mul_neg_of_neg_of_pos hwlt hzgt]
      exact mul_nonneg hw_ge hx_ge
  · -- maximality
    intro y hyF₁ hybnd hysign
    have hyF₂ : y ∈ F₂ := hsub y hyF₁
    have hyz_le : |(y : ℝ)| ≤ |(z : ℝ)| := hzmax y hyF₂ hybnd hysign
    have hyz_sign : 0 ≤ (y : ℝ) * (z : ℝ) := by
      rcases lt_trichotomy ((z : ℝ)) 0 with hzlt | hzeq | hzgt
      · have hx_le : x ≤ 0 := by
          by_contra hxlt; push Not at hxlt
          linarith [mul_neg_of_neg_of_pos hzlt hxlt]
        -- if x = 0, then |z| ≤ |x| = 0 forces z = 0, contradiction
        have hx_lt : x < 0 := by
          rcases lt_or_eq_of_le hx_le with hlt | heq
          · exact hlt
          · exfalso
            have : |(z : ℝ)| ≤ 0 := by rw [heq, abs_zero] at hzbnd; exact hzbnd
            have hzz : (z : ℝ) = 0 := abs_nonpos_iff.mp this
            linarith
        have hy_le : (y : ℝ) ≤ 0 := by
          by_contra hylt; push Not at hylt
          linarith [mul_neg_of_pos_of_neg hylt hx_lt]
        exact mul_nonneg_iff.mpr (Or.inr ⟨hy_le, hzlt.le⟩)
      · have hy_eq : (y : ℝ) = 0 := by
          rw [hzeq, abs_zero] at hyz_le
          exact abs_nonpos_iff.mp hyz_le
        rw [hy_eq, zero_mul]
      · have hx_ge : 0 ≤ x := by
          by_contra hxlt; push Not at hxlt
          linarith [mul_neg_of_pos_of_neg hzgt hxlt]
        have hx_pos : 0 < x := by
          rcases lt_or_eq_of_le hx_ge with hgt | heq
          · exact hgt
          · exfalso
            have : |(z : ℝ)| ≤ 0 := by rw [← heq, abs_zero] at hzbnd; exact hzbnd
            have hzz : (z : ℝ) = 0 := abs_nonpos_iff.mp this
            linarith
        have hy_ge : 0 ≤ (y : ℝ) := by
          by_contra hylt; push Not at hylt
          linarith [mul_neg_of_neg_of_pos hylt hx_pos]
        exact mul_nonneg hy_ge hzgt.le
    exact hwmax y hyF₁ hyz_le hyz_sign

/-- Sign-flip symmetry for RAZ rounding: rounding `x` to `y` under RAZ in `F`
is equivalent to rounding `-x` to `-y`. Uses `neg_mem` (every format is closed
under negation). -/
theorem RoundsRAZ.neg {F : AbstractFormat} {x : ℝ} {y : Dyadic}
    (h : RoundsRAZ F x y) : RoundsRAZ F (-x) (-y) := by
  obtain ⟨hyF, hbnd, hsign, hmin⟩ := h
  refine ⟨neg_mem hyF, ?_, ?_, ?_⟩
  · change |(-x)| ≤ |((-y : Dyadic) : ℝ)|
    push_cast
    rw [abs_neg, abs_neg]
    exact hbnd
  · change ((-y : Dyadic) : ℝ) * (-x) ≥ 0
    push_cast
    have : -(y : ℝ) * -x = (y : ℝ) * x := by ring
    rw [this]
    exact hsign
  · intro z hzF hzbnd hzsign
    rw [abs_neg] at hzbnd
    -- Apply maximality to `-z`: `(-z) ∈ F`, `|(-z)| = |z| ≥ |x|`, `(-z)*x = -(z*x) ≥ 0`
    have hnz : (-z) ∈ F := neg_mem hzF
    have h1 : |x| ≤ |((-z : Dyadic) : ℝ)| := by
      push_cast; rw [abs_neg]; exact hzbnd
    have h2 : 0 ≤ ((-z : Dyadic) : ℝ) * x := by
      push_cast
      have hzs : 0 ≤ (z : ℝ) * (-x) := hzsign
      linarith
    have key := hmin (-z) hnz h1 h2
    change |((-y : Dyadic) : ℝ)| ≤ |(z : ℝ)|
    have : |((-z : Dyadic) : ℝ)| = |(z : ℝ)| := by push_cast; rw [abs_neg]
    have : |((-y : Dyadic) : ℝ)| = |(y : ℝ)| := by push_cast; rw [abs_neg]
    push_cast
    rw [abs_neg]
    have hyz : |(y : ℝ)| ≤ |((-z : Dyadic) : ℝ)| := key
    rwa [show |((-z : Dyadic) : ℝ)| = |(z : ℝ)| from by push_cast; rw [abs_neg]] at hyz

/-- **rnd-RAZ-RAZ** (Fig. 9), case `0 < x`. The general theorem follows by
symmetry (`neg_mem`) and the trivial `x = 0` case. -/
theorem rndRAZ_RAZ_pos {F₁ F₂ : AbstractFormat} (hsub : F₁ ⊆ F₂)
    {x : ℝ} (hx : 0 < x) {z w : Dyadic}
    (hz : RoundsRAZ F₂ x z) (hw : RoundsRAZ F₁ (z : ℝ) w) :
    RoundsRAZ F₁ x w := by
  obtain ⟨hzF, hzbnd, hzsign, hzmin⟩ := hz
  obtain ⟨hwF, hwbnd, hwsign, hwmin⟩ := hw
  -- |x| ≤ |z| and 0 < x give 0 < z
  have hx_abs : |x| = x := abs_of_pos hx
  have hz_pos : 0 < (z : ℝ) := by
    have : 0 < |(z : ℝ)| := lt_of_lt_of_le (by rwa [hx_abs]) hzbnd
    rcases lt_or_gt_of_ne (abs_pos.mp this) with h | h
    · -- z < 0: contradicts z * x ≥ 0 with x > 0
      exfalso
      linarith [mul_neg_of_neg_of_pos h hx]
    · exact h
  have hz_abs : |(z : ℝ)| = (z : ℝ) := abs_of_pos hz_pos
  -- |w| ≥ |z| and 0 < z give 0 < w
  have hw_pos : 0 < (w : ℝ) := by
    have hw_pos' : 0 < |(w : ℝ)| := lt_of_lt_of_le (by rwa [hz_abs]) hwbnd
    rcases lt_or_gt_of_ne (abs_pos.mp hw_pos') with h | h
    · exfalso
      linarith [mul_neg_of_neg_of_pos h hz_pos]
    · exact h
  have hw_abs : |(w : ℝ)| = (w : ℝ) := abs_of_pos hw_pos
  refine ⟨hwF, ?_, ?_, ?_⟩
  · -- |x| ≤ |w|: |x| ≤ |z| ≤ |w|
    exact le_trans hzbnd hwbnd
  · -- w * x ≥ 0
    exact le_of_lt (mul_pos hw_pos hx)
  · -- minimality
    intro y hyF₁ hybnd hysign
    have hyF₂ : y ∈ F₂ := hsub y hyF₁
    have hzy_le : |(z : ℝ)| ≤ |(y : ℝ)| := hzmin y hyF₂ hybnd hysign
    -- y has same sign as x or is 0
    have hy_sign : 0 ≤ (y : ℝ) := by
      rcases mul_nonneg_iff.mp hysign with ⟨hyge, _⟩ | ⟨_, hxle⟩
      · exact hyge
      · linarith
    -- y ≥ 0 and y * z ≥ 0 (since z > 0)
    have hyz_sign : 0 ≤ (y : ℝ) * (z : ℝ) := mul_nonneg hy_sign hz_pos.le
    exact hwmin y hyF₁ hzy_le hyz_sign

/-- **rnd-RAZ-RAZ** (Fig. 9). General version, all `x ∈ ℝ`. Combines the
positive case, negative case (via `RoundsRAZ.neg`), and the `x = 0` case
(uses `neg_mem` to handle elements of `F₁` whose sign opposes `z`). -/
theorem rndRAZ_RAZ {F₁ F₂ : AbstractFormat} (hsub : F₁ ⊆ F₂)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsRAZ F₂ x z) (hw : RoundsRAZ F₁ (z : ℝ) w) :
    RoundsRAZ F₁ x w := by
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · -- x < 0: flip via RoundsRAZ.neg, apply positive case, flip back
    have hz' : RoundsRAZ F₂ (-x) (-z) := RoundsRAZ.neg hz
    have hw' : RoundsRAZ F₁ ((-z : Dyadic) : ℝ) (-w) := by
      have := RoundsRAZ.neg hw
      change RoundsRAZ F₁ (-(z : ℝ)) (-w) at this
      have hcoe : ((-z : Dyadic) : ℝ) = -(z : ℝ) := by push_cast; rfl
      rw [hcoe]; exact this
    have hresult := rndRAZ_RAZ_pos hsub (neg_pos.mpr hx_neg) hz' hw'
    have := RoundsRAZ.neg hresult
    rwa [neg_neg, neg_neg] at this
  · -- x = 0: w must be the minimum |·| in F₁ overall
    subst hx_zero
    obtain ⟨hzF, _, _, hzmin⟩ := hz
    obtain ⟨hwF, _, hwsign, hwmin⟩ := hw
    refine ⟨hwF, by simp, by simp, ?_⟩
    intro y hyF₁ _ _
    have hyF₂ : y ∈ F₂ := hsub y hyF₁
    -- `z` is min |·| in F₂ (constraints at x = 0 are trivial)
    have hzy : |(z : ℝ)| ≤ |(y : ℝ)| := hzmin y hyF₂ (by simp) (by simp)
    -- Apply hwmin to `y` if `y * z ≥ 0`, else to `-y`.
    by_cases hyz : 0 ≤ (y : ℝ) * (z : ℝ)
    · exact hwmin y hyF₁ hzy hyz
    · push Not at hyz
      have hny : (-y) ∈ F₁ := neg_mem hyF₁
      have h1 : |(z : ℝ)| ≤ |((-y : Dyadic) : ℝ)| := by
        push_cast; rw [abs_neg]; exact hzy
      have h2 : 0 ≤ ((-y : Dyadic) : ℝ) * (z : ℝ) := by
        push_cast; linarith
      have key := hwmin (-y) hny h1 h2
      have : |((-y : Dyadic) : ℝ)| = |(y : ℝ)| := by push_cast; rw [abs_neg]
      rwa [this] at key
  · -- x > 0
    exact rndRAZ_RAZ_pos hsub hx_pos hz hw

/-- **rnd-RTO-RTO** (Fig. 9), trivial case `x ∈ F₁`. The full theorem (for
`x ∉ F₁`) requires Lemma 5.3 (RTO digit-padding preserves bracketing) and is
deferred. With `2 ≤ p` for both formats. -/
theorem rndRTO_RTO_of_mem {F₁ F₂ : AbstractFormat} (hsub : F₁ ⊆ F₂)
    {x : Dyadic} (hx : x ∈ F₁)
    {z w : Dyadic}
    (hz : RoundsRTO F₂ (x : ℝ) z) (hw : RoundsRTO F₁ (z : ℝ) w) :
    RoundsRTO F₁ (x : ℝ) w := by
  have hxF₂ : x ∈ F₂ := hsub x hx
  have hz_eq : z = x := RoundsRTO.unique_of_mem hxF₂ hz
  rw [hz_eq] at hw
  have hw_eq : w = x := RoundsRTO.unique_of_mem hx hw
  rw [hw_eq]
  exact RoundsRTO.of_mem hx

end AbstractFormat

end Mpfx
