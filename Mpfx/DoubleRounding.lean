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

/-- Sign-flip symmetry for RTZ rounding. -/
theorem RoundsRTZ.neg {F : AbstractFormat} {x : ℝ} {y : Dyadic}
    (h : RoundsRTZ F x y) : RoundsRTZ F (-x) (-y) := by
  obtain ⟨hyF, hbnd, hsign, hmax⟩ := h
  refine ⟨neg_mem hyF, ?_, ?_, ?_⟩
  · change |((-y : Dyadic) : ℝ)| ≤ |(-x)|
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
    have hnz : (-z) ∈ F := neg_mem hzF
    have h1 : |((-z : Dyadic) : ℝ)| ≤ |x| := by push_cast; rw [abs_neg]; exact hzbnd
    have h2 : 0 ≤ ((-z : Dyadic) : ℝ) * x := by
      push_cast
      have hzs : 0 ≤ (z : ℝ) * (-x) := hzsign
      linarith
    have key := hmax (-z) hnz h1 h2
    have habs1 : |((-z : Dyadic) : ℝ)| = |(z : ℝ)| := by push_cast; rw [abs_neg]
    have habs2 : |((-y : Dyadic) : ℝ)| = |(y : ℝ)| := by push_cast; rw [abs_neg]
    rw [habs1] at key
    rw [habs2]
    exact key

/-- Sign-flip symmetry for RTO rounding. -/
theorem RoundsRTO.neg {F : AbstractFormat} {x : ℝ} {y : Dyadic}
    (h : RoundsRTO F x y) : RoundsRTO F (-x) (-y) := by
  obtain ⟨hyF, hadj, hodd_imp⟩ := h
  refine ⟨neg_mem hyF, ?_, ?_⟩
  · -- RoundsDown ↔ RoundsUp under negation
    rcases hadj with hRD | hRU
    · right
      obtain ⟨_, hyx, hmax⟩ := hRD
      refine ⟨neg_mem hyF, ?_, ?_⟩
      · push_cast; linarith
      · intro z hzF hxz
        push_cast
        have hnzF : (-z) ∈ F := neg_mem hzF
        have h1 : ((-z : Dyadic) : ℝ) ≤ x := by push_cast; linarith
        have key := hmax (-z) hnzF h1
        push_cast at key; linarith
    · left
      obtain ⟨_, hxy, hmin⟩ := hRU
      refine ⟨neg_mem hyF, ?_, ?_⟩
      · push_cast; linarith
      · intro z hzF hzx
        push_cast
        have hnzF : (-z) ∈ F := neg_mem hzF
        have h1 : x ≤ ((-z : Dyadic) : ℝ) := by push_cast; linarith
        have key := hmin (-z) hnzF h1
        push_cast at key; linarith
  · intro hxne
    have hxne' : x ≠ (y : ℝ) := by
      intro h_eq
      apply hxne
      rw [h_eq]; push_cast; rfl
    exact (hodd_imp hxne').neg

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

/-- **rnd-RTO-RTO** (Fig. 9), general case `x ∈ ℝ`. With the format-parameterized
`IsOdd`, the parity transfer is automatic — `IsOdd F₁ w'` is intrinsic to
`(F₁, w')` and doesn't depend on whether we got `w'` by rounding from `z` or
from `x`. The only bookkeeping is the adjacency transfer (Lemma 5.3 + 4-way
case split) and ruling out `z ∈ F₁`.

`hzgt` is the F₂ rounding precision at `z` (the rounded value), used in
Lemma 5.3 to rule out `z ∈ F₁`. -/
theorem rndRTO_RTO {F₁ F₂ : AbstractFormat} {w : ℕ}
    (hsub : F₁ ⊆ F₂)
    (hp_F₁ : F₁.p = (w : ℕ∞))
    {x : ℝ}
    {z w' : Dyadic}
    (hz : RoundsRTO F₂ x z)
    (hw : RoundsRTO F₁ (z : ℝ) w')
    (hzgt : x ≠ (z : ℝ) → (w : ℤ) < numDigits F₂.p F₂.exp (z : ℝ)) :
    RoundsRTO F₁ x w' := by
  obtain ⟨hzF₂, hz_adj, hz_odd_imp⟩ := hz
  obtain ⟨hw'F₁, hw_adj, hw_odd_imp⟩ := hw
  rcases eq_or_ne ((z : ℝ)) x with hzx | hzx
  · -- z = x: hw is essentially the goal
    rw [hzx] at hw_adj hw_odd_imp
    refine ⟨hw'F₁, hw_adj, ?_⟩
    intro hxne
    exact hw_odd_imp hxne
  · -- z ≠ x: use Lemma 5.3 to derive z ∉ F₁
    have hxne : x ≠ (z : ℝ) := fun h => hzx h.symm
    have hgt : (w : ℤ) < numDigits F₂.p F₂.exp (z : ℝ) := hzgt hxne
    have hz_not_F₁ : z ∉ F₁ := by
      intro hzF₁
      have hz_prec : Dyadic.precisionAtMost (w : ℕ∞) z := by
        have ⟨hzP, _, _⟩ := hzF₁
        rwa [hp_F₁] at hzP
      exact (RoundsRTO.ne_of_precisionAtMost (w := w)
              ⟨hzF₂, hz_adj, hz_odd_imp⟩ hxne hgt hz_prec) rfl
    have hz_ne_w' : (z : ℝ) ≠ (w' : ℝ) := by
      intro h_eq
      apply hz_not_F₁
      rw [show z = w' from Subtype.ext h_eq]
      exact hw'F₁
    refine ⟨hw'F₁, ?_, ?_⟩
    · -- Adjacency: 4 cases on (hz_adj, hw_adj)
      rcases hz_adj with hzRD | hzRU
      · rcases hw_adj with hwRD | hwRU
        · left
          obtain ⟨_, hwz, hw_max⟩ := hwRD
          have hzx_le := hzRD.2.1
          refine ⟨hw'F₁, le_trans hwz hzx_le, ?_⟩
          intro v hvF₁ hvx
          have hv_le_z : (v : ℝ) ≤ (z : ℝ) := hzRD.2.2 v (hsub _ hvF₁) hvx
          exact hw_max v hvF₁ hv_le_z
        · obtain ⟨_, hzw, hw_min⟩ := hwRU
          by_cases hw'_le_x : (w' : ℝ) ≤ x
          · exfalso
            have hw_le_z : (w' : ℝ) ≤ (z : ℝ) := hzRD.2.2 w' (hsub _ hw'F₁) hw'_le_x
            have : (w' : ℝ) = (z : ℝ) := le_antisymm hw_le_z hzw
            exact hz_ne_w' this.symm
          · push Not at hw'_le_x
            right
            refine ⟨hw'F₁, hw'_le_x.le, ?_⟩
            intro v hvF₁ hxv
            exact hw_min v hvF₁ (le_trans hzRD.2.1 hxv)
      · rcases hw_adj with hwRD | hwRU
        · obtain ⟨_, hwz, hw_max⟩ := hwRD
          by_cases hw'_le_x : (w' : ℝ) ≤ x
          · left
            refine ⟨hw'F₁, hw'_le_x, ?_⟩
            intro v hvF₁ hvx
            exact hw_max v hvF₁ (le_trans hvx hzRU.2.1)
          · exfalso
            push Not at hw'_le_x
            have hw_ge_z : (z : ℝ) ≤ (w' : ℝ) :=
              hzRU.2.2 w' (hsub _ hw'F₁) hw'_le_x.le
            have : (w' : ℝ) = (z : ℝ) := le_antisymm hwz hw_ge_z
            exact hz_ne_w' this.symm
        · right
          obtain ⟨_, hzw, hw_min⟩ := hwRU
          have hxz := hzRU.2.1
          refine ⟨hw'F₁, le_trans hxz hzw, ?_⟩
          intro v hvF₁ hxv
          have hzv : (z : ℝ) ≤ (v : ℝ) := hzRU.2.2 v (hsub _ hvF₁) hxv
          exact hw_min v hvF₁ hzv
    · -- Parity: IsOdd F₁ w' is intrinsic to (F₁, w'), no transfer needed!
      intro _
      exact hw_odd_imp hz_ne_w'

/-- **rnd-RTO-RTZ** (Fig. 9), positive case `0 < x`. The general theorem (over
all `x ∈ ℝ`) follows by `RoundsRTO.neg`-style symmetry plus the trivial `x = 0`
case (deferred).

Uses Lemma 5.3 (`RoundsRTO.ne_of_precisionAtMost`) to rule out the case where
RTO in `F₂` lands on an `F₁`-representable value when `x ∉ F₁`. The hypothesis
`hzgt` provides the F₂-rounding precision at `z` (the rounded value), needed
for the new format-parameterized `IsOdd`. -/
theorem rndRTO_RTZ_pos {F₁ F₂ : AbstractFormat} {w : ℕ}
    (hsub : F₁ ⊆ F₂)
    (hp_F₁ : F₁.p = (w : ℕ∞))
    {x : ℝ} (hx_pos : 0 < x)
    {z w' : Dyadic}
    (hz : RoundsRTO F₂ x z)
    (hw : RoundsRTZ F₁ (z : ℝ) w')
    (hzgt : x ≠ (z : ℝ) → (w : ℤ) < numDigits F₂.p F₂.exp (z : ℝ)) :
    RoundsRTZ F₁ x w' := by
  have h0_F₂ : (0 : Dyadic) ∈ F₂ := F₂.zero_mem
  obtain ⟨hzF₂, hz_adj, hz_odd_imp⟩ := hz
  obtain ⟨hw'F₁, hw'_bnd_z, hw'_sign_z, hw'_max⟩ := hw
  have hx_abs : |x| = x := abs_of_pos hx_pos
  -- z ≥ 0
  have hz_nn : 0 ≤ (z : ℝ) := by
    rcases hz_adj with hRD | hRU
    · obtain ⟨_, _, hz_max⟩ := hRD
      have h := hz_max 0 h0_F₂ hx_pos.le
      simpa using h
    · obtain ⟨_, hxz, _⟩ := hRU
      linarith
  have hz_abs : |(z : ℝ)| = (z : ℝ) := abs_of_nonneg hz_nn
  rw [hz_abs] at hw'_bnd_z
  -- w' ≥ 0
  have hw'_nn : 0 ≤ (w' : ℝ) := by
    rcases lt_or_eq_of_le hz_nn with hzpos | hzeq
    · nlinarith [hw'_sign_z]
    · have h1 : |(w' : ℝ)| ≤ 0 := hzeq.symm ▸ hw'_bnd_z
      have hw'0 : (w' : ℝ) = 0 := abs_nonpos_iff.mp h1
      linarith
  have hw'_abs : |(w' : ℝ)| = (w' : ℝ) := abs_of_nonneg hw'_nn
  -- w' ≤ x (key step using Lemma 5.3 in the RoundsUp case)
  have hw'_le_x : (w' : ℝ) ≤ x := by
    rcases hz_adj with hRD | hRU
    · -- RoundsDown z ≤ x: w' ≤ z ≤ x
      obtain ⟨_, hzx_le, _⟩ := hRD
      have : (w' : ℝ) ≤ (z : ℝ) := by rw [← hw'_abs]; exact hw'_bnd_z
      linarith
    · -- RoundsUp z ≥ x: by contradiction, suppose w' > x
      by_contra h_w_gt
      push Not at h_w_gt
      have hz_min := hRU.2.2
      have hw'F₂ : w' ∈ F₂ := hsub _ hw'F₁
      have hw'_ge_z : (z : ℝ) ≤ (w' : ℝ) := hz_min w' hw'F₂ h_w_gt.le
      have hw'_le_z : (w' : ℝ) ≤ (z : ℝ) := by rw [← hw'_abs]; exact hw'_bnd_z
      have hw'_eq_z : (w' : ℝ) = (z : ℝ) := le_antisymm hw'_le_z hw'_ge_z
      have hxne : x ≠ (z : ℝ) := by
        intro hxz_eq
        rw [← hxz_eq] at hw'_eq_z
        linarith
      have hw'_prec : Dyadic.precisionAtMost (w : ℕ∞) w' := by
        have ⟨hyP, _, _⟩ := hw'F₁
        rwa [hp_F₁] at hyP
      have hz_full : RoundsRTO F₂ x z := ⟨hzF₂, Or.inr hRU, hz_odd_imp⟩
      have hgt : (w : ℤ) < numDigits F₂.p F₂.exp (z : ℝ) := hzgt hxne
      have h_ne := RoundsRTO.ne_of_precisionAtMost (w := w)
                     hz_full hxne hgt hw'_prec
      exact h_ne hw'_eq_z.symm
  refine ⟨hw'F₁, ?_, ?_, ?_⟩
  · -- |w'| ≤ |x|
    rw [hw'_abs, hx_abs]; exact hw'_le_x
  · -- w' * x ≥ 0
    exact mul_nonneg hw'_nn hx_pos.le
  · -- maximality
    intro v hvF₁ hv_bnd_x hv_sign_x
    rw [hx_abs] at hv_bnd_x
    have hv_nn : 0 ≤ (v : ℝ) := by nlinarith [hv_sign_x]
    have hv_abs : |(v : ℝ)| = (v : ℝ) := abs_of_nonneg hv_nn
    -- v ≤ z (by RoundsDown of z's max-in-F₂, or by v ≤ x ≤ z in RoundsUp)
    have hv_le_z : (v : ℝ) ≤ (z : ℝ) := by
      rcases hz_adj with hRD | hRU
      · obtain ⟨_, _, hz_F₂_max⟩ := hRD
        have hvF₂ : v ∈ F₂ := hsub _ hvF₁
        have h1 : (v : ℝ) ≤ x := by rw [← hv_abs]; exact hv_bnd_x
        exact hz_F₂_max v hvF₂ h1
      · obtain ⟨_, hxz, _⟩ := hRU
        have h1 : (v : ℝ) ≤ x := by rw [← hv_abs]; exact hv_bnd_x
        linarith
    have hv_bnd_z : |(v : ℝ)| ≤ |(z : ℝ)| := by rw [hv_abs, hz_abs]; exact hv_le_z
    have hv_z_sign : 0 ≤ (v : ℝ) * (z : ℝ) := mul_nonneg hv_nn hz_nn
    exact hw'_max v hvF₁ hv_bnd_z hv_z_sign

/-- **rnd-RTO-RTZ** (Fig. 9), general version over all `x ∈ ℝ`. Combines the
positive case (`rndRTO_RTZ_pos`), the negative case (via `RoundsRTO.neg` and
`RoundsRTZ.neg`), and the trivial `x = 0` case (vacuous: `hzgt` at `x = 0`
combined with `IsOdd F₂ z` gives a contradiction since `IsOdd` requires
`numDigits F₂ z ≥ 1`, but `z` would be 0 if `x = 0` — actually for `x = 0`
the case `x ≠ z` may or may not hold; the result holds regardless). -/
theorem rndRTO_RTZ {F₁ F₂ : AbstractFormat} {w : ℕ}
    (hsub : F₁ ⊆ F₂)
    (hp_F₁ : F₁.p = (w : ℕ∞))
    {x : ℝ}
    {z w' : Dyadic}
    (hz : RoundsRTO F₂ x z)
    (hw : RoundsRTZ F₁ (z : ℝ) w')
    (hzgt : x ≠ (z : ℝ) → (w : ℤ) < numDigits F₂.p F₂.exp (z : ℝ)) :
    RoundsRTZ F₁ x w' := by
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · -- x < 0: negate, apply _pos, negate back
    have hx_pos' : 0 < (-x) := by linarith
    have hz' : RoundsRTO F₂ (-x) (-z) := RoundsRTO.neg hz
    have hw' : RoundsRTZ F₁ ((-z : Dyadic) : ℝ) (-w') := by
      have h := RoundsRTZ.neg hw
      have hcoe : ((-z : Dyadic) : ℝ) = -(z : ℝ) := by push_cast; rfl
      rw [hcoe]; exact h
    have hzgt' : -x ≠ ((-z : Dyadic) : ℝ) →
        (w : ℤ) < numDigits F₂.p F₂.exp ((-z : Dyadic) : ℝ) := by
      intro hne
      have hxne : x ≠ (z : ℝ) := by
        intro heq; apply hne; rw [heq]; push_cast; rfl
      have h_nd : numDigits F₂.p F₂.exp ((-z : Dyadic) : ℝ) =
          numDigits F₂.p F₂.exp (z : ℝ) := by
        change numDigits F₂.p F₂.exp (-(z : ℝ)) = _
        exact numDigits_neg F₂.p F₂.exp (z : ℝ)
      rw [h_nd]; exact hzgt hxne
    have h_result := rndRTO_RTZ_pos hsub hp_F₁ hx_pos' hz' hw' hzgt'
    have hfinal := RoundsRTZ.neg h_result
    rwa [neg_neg, neg_neg] at hfinal
  · -- x = 0: 0 ∈ F₂ pins z = 0 via the RoundsDown/RoundsUp adjacency,
    -- and then 0 ∈ F₁ similarly pins w' = 0.
    subst hx_zero
    have h0_F₂ : (0 : Dyadic) ∈ F₂ := F₂.zero_mem
    obtain ⟨hzF₂, hz_adj, _⟩ := hz
    have hz_zero : z = 0 := by
      rcases hz_adj with ⟨_, hz_le, hz_max⟩ | ⟨_, hz_ge, hz_min⟩
      · -- z ≤ 0 and z is max in F₂ ≤ 0; since 0 ∈ F₂ and 0 ≤ 0, z ≥ 0
        have h1 : (0 : ℝ) ≤ (z : ℝ) := hz_max 0 h0_F₂ (le_refl _)
        have h2 : (z : ℝ) ≤ 0 := hz_le
        have : (z : ℝ) = 0 := le_antisymm h2 h1
        exact Subtype.ext this
      · -- z ≥ 0 and z is min in F₂ ≥ 0; similar
        have h1 : (z : ℝ) ≤ 0 := hz_min 0 h0_F₂ (le_refl _)
        have h2 : (0 : ℝ) ≤ (z : ℝ) := hz_ge
        have : (z : ℝ) = 0 := le_antisymm h1 h2
        exact Subtype.ext this
    -- z = 0 and RoundsRTZ F₁ 0 w' forces w' = 0
    rw [hz_zero] at hw
    obtain ⟨hw'F₁, hw'_bnd, _, _⟩ := hw
    have hw'_zero : (w' : ℝ) = 0 := by
      have h0eq : ((0 : Dyadic) : ℝ) = 0 := rfl
      change |(w' : ℝ)| ≤ |((0 : Dyadic) : ℝ)| at hw'_bnd
      rw [h0eq, abs_zero] at hw'_bnd
      exact abs_nonpos_iff.mp hw'_bnd
    refine ⟨hw'F₁, ?_, ?_, ?_⟩
    · change |(w' : ℝ)| ≤ |((0 : Dyadic) : ℝ)|
      rw [hw'_zero]; simp
    · change (w' : ℝ) * ((0 : Dyadic) : ℝ) ≥ 0
      rw [hw'_zero]; simp
    · intro v _ hv_bnd _
      change |(v : ℝ)| ≤ |((0 : Dyadic) : ℝ)| at hv_bnd
      rw [hw'_zero]
      exact hv_bnd
  · -- x > 0
    exact rndRTO_RTZ_pos hsub hp_F₁ hx_pos hz hw hzgt

/-- **rnd-RTO-RAZ** (Fig. 9), positive case `0 < x`. Symmetric to `rndRTO_RTZ_pos`
but for round-away-from-zero instead of round-toward-zero. The key Lemma 5.3
application happens in the *RoundsDown* case of `z` (rather than RoundsUp). -/
theorem rndRTO_RAZ_pos {F₁ F₂ : AbstractFormat} {w : ℕ}
    (hsub : F₁ ⊆ F₂)
    (hp_F₁ : F₁.p = (w : ℕ∞))
    {x : ℝ} (hx_pos : 0 < x)
    {z w' : Dyadic}
    (hz : RoundsRTO F₂ x z)
    (hw : RoundsRAZ F₁ (z : ℝ) w')
    (hzgt : x ≠ (z : ℝ) → (w : ℤ) < numDigits F₂.p F₂.exp (z : ℝ)) :
    RoundsRAZ F₁ x w' := by
  have h0_F₂ : (0 : Dyadic) ∈ F₂ := F₂.zero_mem
  obtain ⟨hzF₂, hz_adj, hz_odd_imp⟩ := hz
  obtain ⟨hw'F₁, hw'_bnd_z, hw'_sign_z, hw'_min⟩ := hw
  have hx_abs : |x| = x := abs_of_pos hx_pos
  -- z ≥ 0
  have hz_nn : 0 ≤ (z : ℝ) := by
    rcases hz_adj with hRD | hRU
    · obtain ⟨_, _, hz_max⟩ := hRD
      have h := hz_max 0 h0_F₂ hx_pos.le
      simpa using h
    · obtain ⟨_, hxz, _⟩ := hRU
      linarith
  have hz_abs : |(z : ℝ)| = (z : ℝ) := abs_of_nonneg hz_nn
  rw [hz_abs] at hw'_bnd_z
  -- z > 0 (RTO of positive x cannot be 0: |c| ≥ 2^(w-1) ≥ 1 forces c ≠ 0)
  have hz_pos : 0 < (z : ℝ) := by
    rcases eq_or_ne ((z : ℝ)) x with hzx | hzx
    · rw [hzx]; exact hx_pos
    · have hxne : x ≠ (z : ℝ) := fun h => hzx h.symm
      have hodd : IsOdd F₂ z := hz_odd_imp hxne
      have hz_ne : z ≠ 0 := hodd.ne_zero
      have : (z : ℝ) ≠ 0 := fun h => hz_ne (Subtype.ext (by rw [h]; rfl))
      exact lt_of_le_of_ne hz_nn (Ne.symm this)
  -- w' ≥ z > 0 (so w' > 0)
  have hw'_pos : 0 < (w' : ℝ) := by
    -- |w'| ≥ z > 0 (from hw'_bnd_z : z ≤ |w'|).
    -- w' * z ≥ 0 with z > 0 → w' ≥ 0.
    -- |w'| ≥ z and w' ≥ 0 → w' = |w'| ≥ z > 0
    have h1 : (z : ℝ) ≤ |(w' : ℝ)| := hw'_bnd_z
    have hw'_nn : 0 ≤ (w' : ℝ) := by nlinarith [hw'_sign_z]
    have hw'_abs : |(w' : ℝ)| = (w' : ℝ) := abs_of_nonneg hw'_nn
    rw [hw'_abs] at h1
    linarith
  have hw'_nn : 0 ≤ (w' : ℝ) := le_of_lt hw'_pos
  have hw'_abs : |(w' : ℝ)| = (w' : ℝ) := abs_of_nonneg hw'_nn
  -- |w'| ≥ |x| (key step: in the RoundsDown case, use Lemma 5.3 to rule out w' < x → w' = z ∈ F₁)
  have hx_le_w' : x ≤ (w' : ℝ) := by
    rcases hz_adj with hRD | hRU
    · -- RoundsDown z ≤ x: by contradiction, suppose w' < x
      by_contra h_w_lt
      push Not at h_w_lt
      -- w' < x. w' ∈ F₁ ⊆ F₂. By RoundsDown max of z: w' ≤ z.
      have hz_max := hRD.2.2
      have hw'F₂ : w' ∈ F₂ := hsub _ hw'F₁
      have hw'_le_z : (w' : ℝ) ≤ (z : ℝ) := hz_max w' hw'F₂ h_w_lt.le
      have hz_le_w' : (z : ℝ) ≤ (w' : ℝ) := by
        have := hw'_bnd_z; rw [hw'_abs] at this; exact this
      have hw'_eq_z : (w' : ℝ) = (z : ℝ) := le_antisymm hw'_le_z hz_le_w'
      have hxne : x ≠ (z : ℝ) := by
        intro hxz_eq
        rw [← hxz_eq] at hw'_eq_z
        linarith
      have hw'_prec : Dyadic.precisionAtMost (w : ℕ∞) w' := by
        have ⟨hyP, _, _⟩ := hw'F₁
        rwa [hp_F₁] at hyP
      have hz_full : RoundsRTO F₂ x z := ⟨hzF₂, Or.inl hRD, hz_odd_imp⟩
      have hgt : (w : ℤ) < numDigits F₂.p F₂.exp (z : ℝ) := hzgt hxne
      have h_ne := RoundsRTO.ne_of_precisionAtMost (w := w)
                     hz_full hxne hgt hw'_prec
      exact h_ne hw'_eq_z.symm
    · -- RoundsUp z ≥ x: z ≤ w' (from RAZ), so w' ≥ z ≥ x
      have hxz := hRU.2.1
      have hz_le_w' : (z : ℝ) ≤ (w' : ℝ) := by
        have := hw'_bnd_z; rw [hw'_abs] at this; exact this
      linarith
  refine ⟨hw'F₁, ?_, ?_, ?_⟩
  · -- |x| ≤ |w'|
    rw [hx_abs, hw'_abs]; exact hx_le_w'
  · -- w' * x ≥ 0
    exact mul_nonneg hw'_nn hx_pos.le
  · -- minimality
    intro v hvF₁ hv_bnd_x hv_sign_x
    rw [hx_abs] at hv_bnd_x
    have hv_nn : 0 ≤ (v : ℝ) := by nlinarith [hv_sign_x]
    have hv_abs : |(v : ℝ)| = (v : ℝ) := abs_of_nonneg hv_nn
    have hx_le_v : x ≤ (v : ℝ) := by rw [← hv_abs]; exact hv_bnd_x
    -- Show v ≥ z, then apply hw'_min
    have hz_le_v : (z : ℝ) ≤ (v : ℝ) := by
      rcases hz_adj with hRD | hRU
      · have hzx := hRD.2.1
        linarith
      · -- RoundsUp z is min in F₂ ≥ x; v ∈ F₁ ⊆ F₂, v ≥ x → v ≥ z
        have hz_min := hRU.2.2
        have hvF₂ : v ∈ F₂ := hsub _ hvF₁
        exact hz_min v hvF₂ hx_le_v
    have hv_bnd_z : |(z : ℝ)| ≤ |(v : ℝ)| := by rw [hz_abs, hv_abs]; exact hz_le_v
    have hv_z_sign : 0 ≤ (v : ℝ) * (z : ℝ) := mul_nonneg hv_nn hz_nn
    exact hw'_min v hvF₁ hv_bnd_z hv_z_sign

/-- **rnd-RTO-RAZ** (Fig. 9), general version over all `x ∈ ℝ`. -/
theorem rndRTO_RAZ {F₁ F₂ : AbstractFormat} {w : ℕ}
    (hsub : F₁ ⊆ F₂)
    (hp_F₁ : F₁.p = (w : ℕ∞))
    {x : ℝ}
    {z w' : Dyadic}
    (hz : RoundsRTO F₂ x z)
    (hw : RoundsRAZ F₁ (z : ℝ) w')
    (hzgt : x ≠ (z : ℝ) → (w : ℤ) < numDigits F₂.p F₂.exp (z : ℝ)) :
    RoundsRAZ F₁ x w' := by
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · -- x < 0: negate, apply _pos, negate back
    have hx_pos' : 0 < (-x) := by linarith
    have hz' : RoundsRTO F₂ (-x) (-z) := RoundsRTO.neg hz
    have hw' : RoundsRAZ F₁ ((-z : Dyadic) : ℝ) (-w') := by
      have h := RoundsRAZ.neg hw
      have hcoe : ((-z : Dyadic) : ℝ) = -(z : ℝ) := by push_cast; rfl
      rw [hcoe]; exact h
    have hzgt' : -x ≠ ((-z : Dyadic) : ℝ) →
        (w : ℤ) < numDigits F₂.p F₂.exp ((-z : Dyadic) : ℝ) := by
      intro hne
      have hxne : x ≠ (z : ℝ) := by
        intro heq; apply hne; rw [heq]; push_cast; rfl
      have h_nd : numDigits F₂.p F₂.exp ((-z : Dyadic) : ℝ) =
          numDigits F₂.p F₂.exp (z : ℝ) := by
        change numDigits F₂.p F₂.exp (-(z : ℝ)) = _
        exact numDigits_neg F₂.p F₂.exp (z : ℝ)
      rw [h_nd]; exact hzgt hxne
    have h_result := rndRTO_RAZ_pos hsub hp_F₁ hx_pos' hz' hw' hzgt'
    have hfinal := RoundsRAZ.neg h_result
    rwa [neg_neg, neg_neg] at hfinal
  · -- x = 0: pin z = 0 = w'
    subst hx_zero
    have h0_F₂ : (0 : Dyadic) ∈ F₂ := F₂.zero_mem
    obtain ⟨hzF₂, hz_adj, _⟩ := hz
    have hz_zero : z = 0 := by
      rcases hz_adj with ⟨_, hz_le, hz_max⟩ | ⟨_, hz_ge, hz_min⟩
      · have h1 : (0 : ℝ) ≤ (z : ℝ) := hz_max 0 h0_F₂ (le_refl _)
        have : (z : ℝ) = 0 := le_antisymm hz_le h1
        exact Subtype.ext this
      · have h1 : (z : ℝ) ≤ 0 := hz_min 0 h0_F₂ (le_refl _)
        have : (z : ℝ) = 0 := le_antisymm h1 hz_ge
        exact Subtype.ext this
    rw [hz_zero] at hw
    obtain ⟨hw'F₁, _, _, hw'_min⟩ := hw
    -- RAZ at 0: w' is min-|·| in F₁. Since 0 ∈ F₁, w' = 0.
    have h0_F₁ : (0 : Dyadic) ∈ F₁ := F₁.zero_mem
    have h_min := hw'_min 0 h0_F₁ (le_refl _) (by simp)
    have hw'_zero : (w' : ℝ) = 0 := by
      change |(w' : ℝ)| ≤ |((0 : Dyadic) : ℝ)| at h_min
      have h0eq : ((0 : Dyadic) : ℝ) = 0 := rfl
      rw [h0eq, abs_zero] at h_min
      exact abs_nonpos_iff.mp h_min
    refine ⟨hw'F₁, ?_, ?_, ?_⟩
    · simp [hw'_zero]
    · simp [hw'_zero]
    · intro v _ _ _
      simp [hw'_zero, abs_nonneg]
  · -- x > 0
    exact rndRTO_RAZ_pos hsub hp_F₁ hx_pos hz hw hzgt

/-- **rnd-RTO-RNE** (Fig. 9), structural form: assumes the F₂-to-F₁ transfer
of adjacency, closeness, and tie-break has been done externally.

The structural transfers (`h_adj_transfer`, `h_close_transfer`,
`h_tie_transfer`) capture the content of Lemma 5.3 plus an F₂-adjacency
analysis specific to RNE. Proving them from `hz` and `hw` directly is
substantial future work; this theorem packages the remaining bookkeeping. -/
theorem rndRTO_RNE_via_transfers {F₁ : AbstractFormat}
    {x : ℝ} {w' : Dyadic}
    (hw'F₁ : w' ∈ F₁)
    (h_adj_transfer : RoundsDown F₁ x w' ∨ RoundsUp F₁ x w')
    (h_close_transfer : ∀ z' : Dyadic, z' ∈ F₁ →
      (RoundsDown F₁ x z' ∨ RoundsUp F₁ x z') →
      |x - (w' : ℝ)| ≤ |x - (z' : ℝ)|)
    (h_tie_transfer : (∃ z' : Dyadic, z' ∈ F₁ ∧
        (RoundsDown F₁ x z' ∨ RoundsUp F₁ x z') ∧
        z' ≠ w' ∧ |x - (w' : ℝ)| = |x - (z' : ℝ)|) →
      IsEven F₁ w') :
    RoundsRNE F₁ x w' :=
  ⟨hw'F₁, h_adj_transfer, h_close_transfer, h_tie_transfer⟩

/-- Helper for tie-break: from `|x - w'| = |x - z'|` with `w' ≠ z'`, derive
`x = (w' + z') / 2`. -/
private theorem RoundsRNE.midpoint_of_tie {x : ℝ} {w' z' : Dyadic}
    (h_ne : z' ≠ w') (h_tie : |x - (w' : ℝ)| = |x - (z' : ℝ)|) :
    x = ((w' : ℝ) + (z' : ℝ)) / 2 := by
  rcases abs_eq_abs.mp h_tie with h1 | h1
  · -- x - w' = x - z' ⇒ w' = z', contradicting h_ne
    have : (w' : ℝ) = (z' : ℝ) := by linarith
    exact absurd (Subtype.ext this).symm h_ne
  · -- x - w' = -(x - z') ⇒ 2x = w' + z'
    linarith

/-- **rnd-RTO-RNE** wrapper: derives the adjacency transfer fully (same
case-split as `rndRTO_RTO`), and takes the closeness and tie-break transfers
as hypotheses (these require F₂-adjacency analysis specific to RNE).

The adjacency transfer uses Lemma 5.3 to show `z ∉ F₁`, then case-analyzes
the four direction combinations. The closeness and tie-break hypotheses
should follow when `k ≥ 2` and the midpoint of `F₁`-adjacents is in `F₂` —
proving this is the next step. -/
theorem rndRTO_RNE {F₁ F₂ : AbstractFormat} {w : ℕ}
    (hsub : F₁ ⊆ F₂)
    (hp_F₁ : F₁.p = (w : ℕ∞))
    {x : ℝ}
    {z w' : Dyadic}
    (hz : RoundsRTO F₂ x z)
    (hw : RoundsRNE F₁ (z : ℝ) w')
    (hzgt : x ≠ (z : ℝ) → (w : ℤ) < numDigits F₂.p F₂.exp (z : ℝ))
    -- Closeness transfer (provable when k ≥ 2 with F₂-adjacency analysis)
    (h_close : ∀ z' : Dyadic, z' ∈ F₁ →
      (RoundsDown F₁ x z' ∨ RoundsUp F₁ x z') →
      |x - (w' : ℝ)| ≤ |x - (z' : ℝ)|)
    -- "No tie at x unless z = x" (provable when k ≥ 2 with midpoint ∈ F₂)
    (h_no_tie : (z : ℝ) ≠ x →
      ∀ z' : Dyadic, z' ∈ F₁ →
        (RoundsDown F₁ x z' ∨ RoundsUp F₁ x z') →
        z' ≠ w' → |x - (w' : ℝ)| ≠ |x - (z' : ℝ)|) :
    RoundsRNE F₁ x w' := by
  rcases eq_or_ne ((z : ℝ)) x with hzx | hzx
  · -- z = x: hw is essentially the goal (inline `rndRTO_RNE_of_eq`)
    obtain ⟨hw'F₁, hw_adj, hw_close, hw_tie⟩ := hw
    rw [hzx] at hw_adj hw_close hw_tie
    exact ⟨hw'F₁, hw_adj, hw_close, hw_tie⟩
  · -- z ≠ x: use Lemma 5.3 to derive adjacency, h_close + h_no_tie for the rest
    have hxne : x ≠ (z : ℝ) := fun h => hzx h.symm
    obtain ⟨hzF₂, hz_adj, hz_odd_imp⟩ := hz
    obtain ⟨hw'F₁, hw_adj, _, _⟩ := hw
    -- z ∉ F₁ via Lemma 5.3
    have hgt : (w : ℤ) < numDigits F₂.p F₂.exp (z : ℝ) := hzgt hxne
    have hz_not_F₁ : z ∉ F₁ := by
      intro hzF₁
      have hz_prec : Dyadic.precisionAtMost (w : ℕ∞) z := by
        have ⟨hzP, _, _⟩ := hzF₁
        rwa [hp_F₁] at hzP
      exact (RoundsRTO.ne_of_precisionAtMost (w := w)
              ⟨hzF₂, hz_adj, hz_odd_imp⟩ hxne hgt hz_prec) rfl
    have hz_ne_w' : (z : ℝ) ≠ (w' : ℝ) := by
      intro h_eq
      apply hz_not_F₁
      rw [show z = w' from Subtype.ext h_eq]
      exact hw'F₁
    -- Adjacency: copy of rndRTO_RTO's case analysis
    have h_adj_x : RoundsDown F₁ x w' ∨ RoundsUp F₁ x w' := by
      rcases hz_adj with hzRD | hzRU
      · rcases hw_adj with hwRD | hwRU
        · left
          obtain ⟨_, hwz, hw_max⟩ := hwRD
          have hzx_le := hzRD.2.1
          refine ⟨hw'F₁, le_trans hwz hzx_le, ?_⟩
          intro v hvF₁ hvx
          exact hw_max v hvF₁ (hzRD.2.2 v (hsub _ hvF₁) hvx)
        · obtain ⟨_, hzw, hw_min⟩ := hwRU
          by_cases hw'_le_x : (w' : ℝ) ≤ x
          · exfalso
            have hw_le_z : (w' : ℝ) ≤ (z : ℝ) := hzRD.2.2 w' (hsub _ hw'F₁) hw'_le_x
            exact hz_ne_w' (le_antisymm hw_le_z hzw).symm
          · push Not at hw'_le_x
            right
            refine ⟨hw'F₁, hw'_le_x.le, ?_⟩
            intro v hvF₁ hxv
            exact hw_min v hvF₁ (le_trans hzRD.2.1 hxv)
      · rcases hw_adj with hwRD | hwRU
        · obtain ⟨_, hwz, hw_max⟩ := hwRD
          by_cases hw'_le_x : (w' : ℝ) ≤ x
          · left
            refine ⟨hw'F₁, hw'_le_x, ?_⟩
            intro v hvF₁ hvx
            exact hw_max v hvF₁ (le_trans hvx hzRU.2.1)
          · exfalso
            push Not at hw'_le_x
            have hw_ge_z : (z : ℝ) ≤ (w' : ℝ) :=
              hzRU.2.2 w' (hsub _ hw'F₁) hw'_le_x.le
            exact hz_ne_w' (le_antisymm hwz hw_ge_z).symm
        · right
          obtain ⟨_, hzw, hw_min⟩ := hwRU
          have hxz := hzRU.2.1
          refine ⟨hw'F₁, le_trans hxz hzw, ?_⟩
          intro v hvF₁ hxv
          exact hw_min v hvF₁ (hzRU.2.2 v (hsub _ hvF₁) hxv)
    refine ⟨hw'F₁, h_adj_x, h_close, ?_⟩
    rintro ⟨z', hz'F₁, hz'_adj_x, hz'_ne_w', hz'_eq_dist⟩
    exact absurd hz'_eq_dist (h_no_tie hzx z' hz'F₁ hz'_adj_x hz'_ne_w')

/-- **rnd-RTO-RNE** with `h_mid_in_F₂`: derives `h_no_tie` from the structural
assumption that midpoints of `F₁`-pairs are in `F₂`. The closeness transfer
`h_close` is still a hypothesis. -/
theorem rndRTO_RNE_with_mid {F₁ F₂ : AbstractFormat} {w : ℕ}
    (hsub : F₁ ⊆ F₂)
    (hp_F₁ : F₁.p = (w : ℕ∞))
    {x : ℝ}
    {z w' : Dyadic}
    (hz : RoundsRTO F₂ x z)
    (hw : RoundsRNE F₁ (z : ℝ) w')
    (hzgt : x ≠ (z : ℝ) → (w : ℤ) < numDigits F₂.p F₂.exp (z : ℝ))
    (h_close : ∀ z' : Dyadic, z' ∈ F₁ →
      (RoundsDown F₁ x z' ∨ RoundsUp F₁ x z') →
      |x - (w' : ℝ)| ≤ |x - (z' : ℝ)|)
    -- Midpoints of `F₁`-pairs lie in `F₂` (provable when `k ≥ 2` and the
    -- containment relation provides the precision and quantum slack)
    (h_mid_in_F₂ : ∀ y₁ y₂ : Dyadic, y₁ ∈ F₁ → y₂ ∈ F₁ →
      ∃ m : Dyadic, m ∈ F₂ ∧ (m : ℝ) = ((y₁ : ℝ) + (y₂ : ℝ)) / 2) :
    RoundsRNE F₁ x w' := by
  apply rndRTO_RNE hsub hp_F₁ hz hw hzgt h_close
  -- Derive `h_no_tie` from `h_mid_in_F₂`: a tie at x means x = midpoint = some m ∈ F₂,
  -- which by `RoundsRTO.unique_of_mem` forces z = m, contradicting z ≠ x.
  intro hzx_ne z' hz'F₁ _ hz'_ne_w' hz'_eq_dist
  obtain ⟨hw'F₁, _, _, _⟩ := hw
  have hx_mid : x = ((w' : ℝ) + (z' : ℝ)) / 2 :=
    RoundsRNE.midpoint_of_tie hz'_ne_w' hz'_eq_dist
  obtain ⟨m, hmF₂, hm_eq⟩ := h_mid_in_F₂ w' z' hw'F₁ hz'F₁
  have hm_x : (m : ℝ) = x := by rw [hm_eq, ← hx_mid]
  -- RoundsRTO F₂ x z forces z = m via unique_of_mem (after rewriting x = m)
  have hz_eq : z = m := by
    have hz' : RoundsRTO F₂ ((m : ℝ)) z := by rw [hm_x]; exact hz
    exact RoundsRTO.unique_of_mem hmF₂ hz'
  -- (z : ℝ) = (m : ℝ) = x, contradicting hzx_ne
  apply hzx_ne
  rw [hz_eq]; exact hm_x

end AbstractFormat

end Mpfx
