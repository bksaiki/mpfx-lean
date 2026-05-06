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
    obtain ⟨w_val, hwx, hw_pos, hodd⟩ := hodd_imp hxne'
    refine ⟨w_val, ?_, hw_pos, ?_⟩
    · rw [numDigits_neg]; exact hwx
    · exact (Dyadic.isOddAtP_neg _ _).mpr hodd

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

/-- **rnd-RTO-RTO** (Fig. 9), general case `x ∈ ℝ`. Uses Lemma 5.3 corollary
plus an additional `h_prec` hypothesis: the rounding precision in `F₁` is the
same at `z`'s magnitude as at `x`'s magnitude. This holds whenever the
`F₁`-adjacents of `x` are in the same magnitude bin (do not cross a
power-of-two boundary), which is the typical case. -/
theorem rndRTO_RTO {F₁ F₂ : AbstractFormat} {w k : ℕ}
    (hsub : F₁ ⊆ F₂)
    (hp_F₁ : F₁.p = (w : ℕ∞))
    (hk : 1 ≤ k)
    {x : ℝ}
    (hwk : numDigits F₂.p F₂.exp x = ((w + k : ℕ) : ℤ))
    {z w' : Dyadic}
    (hz : RoundsRTO F₂ x z)
    (hw : RoundsRTO F₁ (z : ℝ) w')
    (h_prec : numDigits F₁.p F₁.exp (z : ℝ) = numDigits F₁.p F₁.exp x) :
    RoundsRTO F₁ x w' := by
  obtain ⟨hzF₂, hz_adj, hz_odd_imp⟩ := hz
  obtain ⟨hw'F₁, hw_adj, hw_odd_imp⟩ := hw
  rcases eq_or_ne ((z : ℝ)) x with hzx | hzx
  · -- z = x: hw is essentially the goal
    rw [hzx] at hw_adj hw_odd_imp
    refine ⟨hw'F₁, hw_adj, ?_⟩
    intro hxne
    exact hw_odd_imp hxne
  · -- z ≠ x: use Lemma 5.3
    have hxne : x ≠ (z : ℝ) := fun h => hzx h.symm
    have hz_not_F₁ : z ∉ F₁ := by
      intro hzF₁
      have hz_prec : Dyadic.precisionAtMost (w : ℕ∞) z := by
        have ⟨hzP, _, _⟩ := hzF₁
        rwa [hp_F₁] at hzP
      exact (RoundsRTO.ne_of_precisionAtMost (w := w) (k := k) hk
              ⟨hzF₂, hz_adj, hz_odd_imp⟩ hxne hwk hz_prec) rfl
    have hz_ne_w' : (z : ℝ) ≠ (w' : ℝ) := by
      intro h_eq
      apply hz_not_F₁
      rw [show z = w' from Subtype.ext h_eq]
      exact hw'F₁
    obtain ⟨p_z, hp_z_eq, hp_z_pos, hodd_z⟩ := hw_odd_imp hz_ne_w'
    refine ⟨hw'F₁, ?_, ?_⟩
    · -- Adjacency: 4 cases on (hz_adj, hw_adj)
      rcases hz_adj with hzRD | hzRU
      · rcases hw_adj with hwRD | hwRU
        · -- z RoundsDown, w' RoundsDown: w' ≤ z ≤ x ⇒ RoundsDown F₁ x w'
          left
          obtain ⟨_, hwz, hw_max⟩ := hwRD
          have hzx_le := hzRD.2.1
          refine ⟨hw'F₁, le_trans hwz hzx_le, ?_⟩
          intro v hvF₁ hvx
          have hv_le_z : (v : ℝ) ≤ (z : ℝ) := hzRD.2.2 v (hsub _ hvF₁) hvx
          exact hw_max v hvF₁ hv_le_z
        · -- z RoundsDown, w' RoundsUp: z ≤ w', z ≤ x. By contradiction, w' ≤ x ⇒ w' = z.
          obtain ⟨_, hzw, hw_min⟩ := hwRU
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
        · -- z RoundsUp, w' RoundsDown: w' ≤ z, x ≤ z. By contradiction, w' > x ⇒ w' = z.
          obtain ⟨_, hwz, hw_max⟩ := hwRD
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
        · -- z RoundsUp, w' RoundsUp: x ≤ z ≤ w' ⇒ RoundsUp F₁ x w'
          right
          obtain ⟨_, hzw, hw_min⟩ := hwRU
          have hxz := hzRU.2.1
          refine ⟨hw'F₁, le_trans hxz hzw, ?_⟩
          intro v hvF₁ hxv
          have hzv : (z : ℝ) ≤ (v : ℝ) := hzRU.2.2 v (hsub _ hvF₁) hxv
          exact hw_min v hvF₁ hzv
    · -- Parity: numDigits F₁ x = p_z (via h_prec) and IsOddAtP p_z w' (from hw)
      intro _
      exact ⟨p_z, h_prec ▸ hp_z_eq, hp_z_pos, hodd_z⟩

/-- **rnd-RTO-RTZ** (Fig. 9), positive case `0 < x`. The general theorem (over
all `x ∈ ℝ`) follows by `RoundsRTO.neg`-style symmetry plus the trivial `x = 0`
case (deferred).

Uses Lemma 5.3 (`RoundsRTO.ne_of_precisionAtMost`) to rule out the case where
RTO in `F₂` lands on an `F₁`-representable value when `x ∉ F₁`. Requires
`F₁.p = w`, `numDigits F₂.p F₂.exp x = w + k`, `k ≥ 1`, and `0 ∈ F₁`. -/
theorem rndRTO_RTZ_pos {F₁ F₂ : AbstractFormat} {w k : ℕ}
    (hsub : F₁ ⊆ F₂)
    (hp_F₁ : F₁.p = (w : ℕ∞))
    (hk : 1 ≤ k)
    {x : ℝ} (hx_pos : 0 < x)
    (hwk : numDigits F₂.p F₂.exp x = ((w + k : ℕ) : ℤ))
    {z w' : Dyadic}
    (hz : RoundsRTO F₂ x z)
    (hw : RoundsRTZ F₁ (z : ℝ) w') :
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
      -- Reconstruct hz from the RoundsUp witness hRU
      have hz_full : RoundsRTO F₂ x z := ⟨hzF₂, Or.inr hRU, hz_odd_imp⟩
      have h_ne := RoundsRTO.ne_of_precisionAtMost (w := w) (k := k) hk
                     hz_full hxne hwk hw'_prec
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
`RoundsRTZ.neg`), and the trivial `x = 0` case (which is vacuous: the precision
hypothesis `hwk` with `hk : 1 ≤ k` is contradictory at `x = 0`). -/
theorem rndRTO_RTZ {F₁ F₂ : AbstractFormat} {w k : ℕ}
    (hsub : F₁ ⊆ F₂)
    (hp_F₁ : F₁.p = (w : ℕ∞))
    (hk : 1 ≤ k)
    {x : ℝ}
    (hwk : numDigits F₂.p F₂.exp x = ((w + k : ℕ) : ℤ))
    {z w' : Dyadic}
    (hz : RoundsRTO F₂ x z)
    (hw : RoundsRTZ F₁ (z : ℝ) w') :
    RoundsRTZ F₁ x w' := by
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · -- x < 0: negate, apply _pos, negate back
    have hx_pos' : 0 < (-x) := by linarith
    have hwk' : numDigits F₂.p F₂.exp (-x) = ((w + k : ℕ) : ℤ) := by
      rw [numDigits_neg]; exact hwk
    have hz' : RoundsRTO F₂ (-x) (-z) := RoundsRTO.neg hz
    have hw' : RoundsRTZ F₁ ((-z : Dyadic) : ℝ) (-w') := by
      have h := RoundsRTZ.neg hw
      have hcoe : ((-z : Dyadic) : ℝ) = -(z : ℝ) := by push_cast; rfl
      rw [hcoe]; exact h
    have h_result := rndRTO_RTZ_pos hsub hp_F₁ hk hx_pos' hwk' hz' hw'
    have hfinal := RoundsRTZ.neg h_result
    rwa [neg_neg, neg_neg] at hfinal
  · -- x = 0: hwk + hk gives contradiction
    exfalso
    subst hx_zero
    have h0 : numDigits F₂.p F₂.exp (0 : ℝ) = 0 := by simp [numDigits]
    rw [h0] at hwk
    have : (w + k : ℕ) = 0 := by exact_mod_cast hwk.symm
    omega
  · -- x > 0
    exact rndRTO_RTZ_pos hsub hp_F₁ hk hx_pos hwk hz hw

/-- **rnd-RTO-RAZ** (Fig. 9), positive case `0 < x`. Symmetric to `rndRTO_RTZ_pos`
but for round-away-from-zero instead of round-toward-zero. The key Lemma 5.3
application happens in the *RoundsDown* case of `z` (rather than RoundsUp). -/
theorem rndRTO_RAZ_pos {F₁ F₂ : AbstractFormat} {w k : ℕ}
    (hsub : F₁ ⊆ F₂)
    (hp_F₁ : F₁.p = (w : ℕ∞))
    (hk : 1 ≤ k)
    {x : ℝ} (hx_pos : 0 < x)
    (hwk : numDigits F₂.p F₂.exp x = ((w + k : ℕ) : ℤ))
    {z w' : Dyadic}
    (hz : RoundsRTO F₂ x z)
    (hw : RoundsRAZ F₁ (z : ℝ) w') :
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
      obtain ⟨w_val, _, _, hodd⟩ := hz_odd_imp hxne
      obtain ⟨c, e, ⟨hzeq, hc_low, _⟩, _⟩ := hodd
      have hc_ne : c ≠ 0 := by
        intro hc0
        rw [hc0, abs_zero] at hc_low
        have : (1 : ℤ) ≤ (2 : ℤ) ^ (w_val - 1) := one_le_pow₀ (by norm_num)
        linarith
      have hz_ne : (z : ℝ) ≠ 0 := by
        intro hz0
        rw [hz0] at hzeq
        have h2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
        have hc_zero_real : (c : ℝ) = 0 := by
          rcases mul_eq_zero.mp hzeq.symm with h | h
          · exact h
          · linarith
        exact hc_ne (by exact_mod_cast hc_zero_real)
      exact lt_of_le_of_ne hz_nn (Ne.symm hz_ne)
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
      have h_ne := RoundsRTO.ne_of_precisionAtMost (w := w) (k := k) hk
                     hz_full hxne hwk hw'_prec
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
theorem rndRTO_RAZ {F₁ F₂ : AbstractFormat} {w k : ℕ}
    (hsub : F₁ ⊆ F₂)
    (hp_F₁ : F₁.p = (w : ℕ∞))
    (hk : 1 ≤ k)
    {x : ℝ}
    (hwk : numDigits F₂.p F₂.exp x = ((w + k : ℕ) : ℤ))
    {z w' : Dyadic}
    (hz : RoundsRTO F₂ x z)
    (hw : RoundsRAZ F₁ (z : ℝ) w') :
    RoundsRAZ F₁ x w' := by
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · -- x < 0: negate, apply _pos, negate back
    have hx_pos' : 0 < (-x) := by linarith
    have hwk' : numDigits F₂.p F₂.exp (-x) = ((w + k : ℕ) : ℤ) := by
      rw [numDigits_neg]; exact hwk
    have hz' : RoundsRTO F₂ (-x) (-z) := RoundsRTO.neg hz
    have hw' : RoundsRAZ F₁ ((-z : Dyadic) : ℝ) (-w') := by
      have h := RoundsRAZ.neg hw
      have hcoe : ((-z : Dyadic) : ℝ) = -(z : ℝ) := by push_cast; rfl
      rw [hcoe]; exact h
    have h_result := rndRTO_RAZ_pos hsub hp_F₁ hk hx_pos' hwk' hz' hw'
    have hfinal := RoundsRAZ.neg h_result
    rwa [neg_neg, neg_neg] at hfinal
  · -- x = 0: hwk + hk gives contradiction
    exfalso
    subst hx_zero
    have h0 : numDigits F₂.p F₂.exp (0 : ℝ) = 0 := by simp [numDigits]
    rw [h0] at hwk
    have : (w + k : ℕ) = 0 := by exact_mod_cast hwk.symm
    omega
  · -- x > 0
    exact rndRTO_RAZ_pos hsub hp_F₁ hk hx_pos hwk hz hw

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
      ∃ p : ℕ, numDigits F₁.p F₁.exp x = (p : ℤ) ∧ 1 ≤ p ∧
        Dyadic.IsEvenAtP p w') :
    RoundsRNE F₁ x w' :=
  ⟨hw'F₁, h_adj_transfer, h_close_transfer, h_tie_transfer⟩

/-- **rnd-RTO-RNE** (Fig. 9), trivial case `(z : ℝ) = x`.

Includes the case `x ∈ F₂` (where RTO returns `x` itself) and the case where
`x` is itself the midpoint of two `F₁`-adjacents (representable in `F₂` since
midpoints are at precision `w + 1 ≤ F₂.p`). The full theorem (for `z ≠ x`)
requires proving that `x` and `z` agree on which `F₁`-adjacent is closer
(equivalently, which side of the midpoint they fall on), which is established
by Lemma 5.3 + a case analysis on the F₂-adjacency structure. -/
theorem rndRTO_RNE_of_eq {F₁ : AbstractFormat}
    {x : ℝ} {z w' : Dyadic}
    (hzx : (z : ℝ) = x)
    (hw : RoundsRNE F₁ (z : ℝ) w') :
    RoundsRNE F₁ x w' := by
  obtain ⟨hw'F₁, hw_adj, hw_close, hw_tie⟩ := hw
  rw [hzx] at hw_adj hw_close hw_tie
  exact ⟨hw'F₁, hw_adj, hw_close, hw_tie⟩

end AbstractFormat

end Mpfx
