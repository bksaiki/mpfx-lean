import Mpfx.Digits
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
    (hz : Rounds F₂ .ToZero x z) (hw : Rounds F₁ .ToZero (z : ℝ) w) :
    Rounds F₁ .ToZero x w := by
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

/-- **rnd-RAZ-RAZ** (Fig. 9), case `0 < x`. The general theorem follows by
symmetry (`neg_mem`) and the trivial `x = 0` case. -/
theorem rndRAZ_RAZ_pos {F₁ F₂ : AbstractFormat} (hsub : F₁ ⊆ F₂)
    {x : ℝ} (hx : 0 < x) {z w : Dyadic}
    (hz : Rounds F₂ .AwayZero x z) (hw : Rounds F₁ .AwayZero (z : ℝ) w) :
    Rounds F₁ .AwayZero x w := by
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
positive case, negative case (via `Rounds.neg`), and the `x = 0` case
(uses `neg_mem` to handle elements of `F₁` whose sign opposes `z`). -/
theorem rndRAZ_RAZ {F₁ F₂ : AbstractFormat} (hsub : F₁ ⊆ F₂)
    {x : ℝ} {z w : Dyadic}
    (hz : Rounds F₂ .AwayZero x z) (hw : Rounds F₁ .AwayZero (z : ℝ) w) :
    Rounds F₁ .AwayZero x w := by
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · -- x < 0: flip via Rounds.neg, apply positive case, flip back
    have hz' : Rounds F₂ .AwayZero (-x) (-z) := Rounds.neg hz trivial
    have hw' : Rounds F₁ .AwayZero ((-z : Dyadic) : ℝ) (-w) := by
      have := Rounds.neg hw trivial
      have hcoe : ((-z : Dyadic) : ℝ) = -(z : ℝ) := by push_cast; rfl
      rw [hcoe]; exact this
    have hresult := rndRAZ_RAZ_pos hsub (neg_pos.mpr hx_neg) hz' hw'
    have : Rounds F₁ .AwayZero (-(-x)) (-(-w)) := Rounds.neg hresult trivial
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

/-- **rnd-RTP-RTP** (round towards +∞ chained). Reduces to `rndRAZ_RAZ_pos`
when `x > 0` and to `rndRTZ_RTZ` when `x ≤ 0`, via the sign-bridge lemmas. -/
theorem rndRTP_RTP {F₁ F₂ : AbstractFormat} (hsub : F₁ ⊆ F₂)
    {x : ℝ} {z w : Dyadic}
    (hz : Rounds F₂ .ToPositive x z) (hw : Rounds F₁ .ToPositive (z : ℝ) w) :
    Rounds F₁ .ToPositive x w := by
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · -- x < 0: bridge to RTZ.
    have hx_le : x ≤ 0 := le_of_lt hx_neg
    have hz_le_0 : (z : ℝ) ≤ 0 := hz.2.2 0 F₂.zero_mem hx_le
    have hz_RTZ : Rounds F₂ .ToZero x z := (Rounds.toPositive_iff_toZero_of_nonpos hx_le).mp hz
    have hw_RTZ : Rounds F₁ .ToZero (z : ℝ) w :=
      (Rounds.toPositive_iff_toZero_of_nonpos hz_le_0).mp hw
    have hresult : Rounds F₁ .ToZero x w := rndRTZ_RTZ hsub hz_RTZ hw_RTZ
    exact (Rounds.toPositive_iff_toZero_of_nonpos hx_le).mpr hresult
  · -- x = 0: bridge to RTZ.
    have hx_le : x ≤ 0 := le_of_eq hx_zero
    have hz_le_0 : (z : ℝ) ≤ 0 := hz.2.2 0 F₂.zero_mem hx_le
    have hz_RTZ : Rounds F₂ .ToZero x z := (Rounds.toPositive_iff_toZero_of_nonpos hx_le).mp hz
    have hw_RTZ : Rounds F₁ .ToZero (z : ℝ) w :=
      (Rounds.toPositive_iff_toZero_of_nonpos hz_le_0).mp hw
    have hresult : Rounds F₁ .ToZero x w := rndRTZ_RTZ hsub hz_RTZ hw_RTZ
    exact (Rounds.toPositive_iff_toZero_of_nonpos hx_le).mpr hresult
  · -- x > 0: bridge to RAZ, apply rndRAZ_RAZ_pos.
    have hx_nn : 0 ≤ x := le_of_lt hx_pos
    have hz_nn : 0 ≤ (z : ℝ) := le_trans hx_nn hz.2.1
    have hz_RAZ : Rounds F₂ .AwayZero x z := (Rounds.toPositive_iff_awayZero_of_nn hx_nn).mp hz
    have hw_RAZ : Rounds F₁ .AwayZero (z : ℝ) w :=
      (Rounds.toPositive_iff_awayZero_of_nn hz_nn).mp hw
    have hresult : Rounds F₁ .AwayZero x w := rndRAZ_RAZ_pos hsub hx_pos hz_RAZ hw_RAZ
    exact (Rounds.toPositive_iff_awayZero_of_nn hx_nn).mpr hresult

/-- **rnd-RTN-RTN** (round towards −∞ chained). Reduces to `rndRTZ_RTZ` when
`x ≥ 0` and to `rndRAZ_RAZ` when `x < 0`, via the sign-bridge lemmas. -/
theorem rndRTN_RTN {F₁ F₂ : AbstractFormat} (hsub : F₁ ⊆ F₂)
    {x : ℝ} {z w : Dyadic}
    (hz : Rounds F₂ .ToNegative x z) (hw : Rounds F₁ .ToNegative (z : ℝ) w) :
    Rounds F₁ .ToNegative x w := by
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · -- x < 0: bridge to RAZ.
    have hx_le : x ≤ 0 := le_of_lt hx_neg
    have hz_le_0 : (z : ℝ) ≤ 0 := le_trans hz.2.1 hx_le
    have hz_RAZ : Rounds F₂ .AwayZero x z := (Rounds.toNegative_iff_awayZero_of_nonpos hx_le).mp hz
    have hw_RAZ : Rounds F₁ .AwayZero (z : ℝ) w :=
      (Rounds.toNegative_iff_awayZero_of_nonpos hz_le_0).mp hw
    have hresult : Rounds F₁ .AwayZero x w := rndRAZ_RAZ hsub hz_RAZ hw_RAZ
    exact (Rounds.toNegative_iff_awayZero_of_nonpos hx_le).mpr hresult
  · -- x = 0: bridge to RTZ.
    have hx_nn : 0 ≤ x := le_of_eq hx_zero.symm
    have hz_nn : 0 ≤ (z : ℝ) := hz.2.2 0 F₂.zero_mem hx_nn
    have hz_RTZ : Rounds F₂ .ToZero x z := (Rounds.toNegative_iff_toZero_of_nn hx_nn).mp hz
    have hw_RTZ : Rounds F₁ .ToZero (z : ℝ) w := (Rounds.toNegative_iff_toZero_of_nn hz_nn).mp hw
    have hresult : Rounds F₁ .ToZero x w := rndRTZ_RTZ hsub hz_RTZ hw_RTZ
    exact (Rounds.toNegative_iff_toZero_of_nn hx_nn).mpr hresult
  · -- x > 0: bridge to RTZ.
    have hx_nn : 0 ≤ x := le_of_lt hx_pos
    have hz_nn : 0 ≤ (z : ℝ) := hz.2.2 0 F₂.zero_mem hx_nn
    have hz_RTZ : Rounds F₂ .ToZero x z := (Rounds.toNegative_iff_toZero_of_nn hx_nn).mp hz
    have hw_RTZ : Rounds F₁ .ToZero (z : ℝ) w := (Rounds.toNegative_iff_toZero_of_nn hz_nn).mp hw
    have hresult : Rounds F₁ .ToZero x w := rndRTZ_RTZ hsub hz_RTZ hw_RTZ
    exact (Rounds.toNegative_iff_toZero_of_nn hx_nn).mpr hresult

/-- **rnd-RTO-RTO** (Fig. 9), general case `x ∈ ℝ`.

Restricted to `F₂.p ≥ 2`. -/
theorem rndRTO_RTO {F₁ F₂ : AbstractFormat}
    (hsub : F₁ ⊆ F₂)
    (hp_F₂ : 2 ≤ F₂.p)
    {x : ℝ}
    {z w' : Dyadic}
    (hz : Rounds F₂ .ToOdd x z)
    (hw : Rounds F₁ .ToOdd (z : ℝ) w') :
    Rounds F₁ .ToOdd x w' := by
  have hz_adj : Rounds F₂ .ToNegative x z ∨ Rounds F₂ .ToPositive x z := hz.2.1
  have hw'F₁ : w' ∈ F₁ := hw.1
  have hw_adj : Rounds F₁ .ToNegative (z : ℝ) w' ∨ Rounds F₁ .ToPositive (z : ℝ) w' := hw.2.1
  have hw_odd_imp : (z : ℝ) ≠ (w' : ℝ) → IsOdd F₁ w' := hw.2.2
  rcases eq_or_ne ((z : ℝ)) x with hzx | hzx
  · -- z = x: hw is essentially the goal
    rw [hzx] at hw_adj hw_odd_imp
    refine ⟨hw'F₁, hw_adj, ?_⟩
    intro hxne
    exact hw_odd_imp hxne
  · -- z ≠ x: split on z = w' vs z ≠ w' (decidable equality on Dyadic).
    have hxne : x ≠ (z : ℝ) := fun h => hzx h.symm
    rcases eq_or_ne z w' with hzw | hzw
    · -- z = w': w' is x's F₁-rounding directly via hz's adjacency.
      have hzF₁ : z ∈ F₁ := hzw ▸ hw'F₁
      have hw'_eq : w' = z := hzw.symm
      have hw'_eq_real : (w' : ℝ) = (z : ℝ) := by rw [hw'_eq]
      refine ⟨hw'F₁, ?_, ?_⟩
      · -- Adjacency: z is x's F₁-adjacent (because z ∈ F₁ ⊆ F₂ and z is x's F₂-adjacent)
        rw [hw'_eq]
        rcases hz_adj with hRD | hRU
        · left
          obtain ⟨_, hzx_le, hz_max⟩ := hRD
          refine ⟨hzF₁, hzx_le, ?_⟩
          intro v hvF₁ hvx
          exact hz_max v (hsub _ hvF₁) hvx
        · right
          obtain ⟨_, hxz, hz_min⟩ := hRU
          refine ⟨hzF₁, hxz, ?_⟩
          intro v hvF₁ hxv
          exact hz_min v (hsub _ hvF₁) hxv
      · -- Parity: IsOdd F₁ z from IsOdd F₂ z, via the precision-equality.
        intro _
        have h_iod_F₂ : IsOdd F₂ z := hz.2.2 hxne
        rw [hw'_eq]
        have h_eq : numDigits F₁.p F₁.exp ((z : Dyadic) : ℝ)
            = numDigits F₂.p F₂.exp ((z : Dyadic) : ℝ) :=
          numDigits_eq_of_subset_of_isOdd hsub hp_F₂ hzF₁ h_iod_F₂
        exact IsOdd.transfer_of_numDigits_eq hsub hp_F₂ hzF₁ h_iod_F₂ h_eq
    · -- z ≠ w': standard 4-way adjacency case split.
      have hz_ne_w' : (z : ℝ) ≠ (w' : ℝ) := fun h_eq => hzw (Subtype.ext h_eq)
      refine ⟨hw'F₁, ?_, ?_⟩
      · rcases hz_adj with hzRD | hzRU
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
      · -- Parity: IsOdd F₁ w' from `hw`'s parity clause (z ≠ w')
        intro _
        exact hw_odd_imp hz_ne_w'

/-- A `Dyadic` not representable in 1 bit cannot live in a format with
`F.p = 1`. Combined with `F.p_pos`, having a precision-2 witness in `F`
forces `F.p ≥ 2`. -/
private lemma two_le_p_of_precision_two_witness {F : AbstractFormat} {v : Dyadic}
    (hvF : v ∈ F) (hv_not_p1 : ¬ Dyadic.precisionAtMost (1 : ℕ∞) v) :
    2 ≤ F.p := by
  by_contra h_p_lt
  push Not at h_p_lt
  have h_F_p_eq_1 : F.p = (1 : ℕ∞) := by
    rcases hpf : F.p with _ | n
    · exfalso; rw [hpf] at h_p_lt; exact not_top_lt h_p_lt
    · have hp_pos := F.p_pos
      rw [hpf] at hp_pos h_p_lt
      have hn_ge : 1 ≤ n := WithTop.coe_le_coe.mp hp_pos
      have hn_lt : n < 2 := WithTop.coe_lt_coe.mp h_p_lt
      have hn_eq : n = 1 := by omega
      rw [hn_eq]; rfl
  have hv_p_F : Dyadic.precisionAtMost F.p v := hvF.1
  rw [h_F_p_eq_1] at hv_p_F
  exact hv_not_p1 hv_p_F

/-- From the paper-aligned containment
`(F₁.extend 1).withBound F₁.boundAfterNext ⊆ F₂`, either `F₂.p ≥ 2` (the
auxiliary needed for Lemma 5.3 / `notMem_of_extend_subset`) or `F₁` contains
only `0`. The proof either constructs a precision-2 witness `v = 3·2^k` lying
in `(F₁.extend 1).withBound F₁.boundAfterNext` (which forces `F₂.p ≥ 2`), or
shows `F₁` is trivial. The witness exists exactly when `F₁` contains some
nonzero element. -/
private theorem hp_F₂_or_F₁_trivial {F₁ F₂ : AbstractFormat}
    (hsub : ((F₁.extend 1).withBound F₁.boundAfterNext F₁.boundAfterNext_nn) ⊆ F₂) :
    2 ≤ F₂.p ∨ ∀ d : Dyadic, d ∈ F₁ → (d : ℝ) = 0 := by
  by_contra h
  push Not at h
  obtain ⟨h_p_lt, ⟨d, hd_mem, hd_ne⟩⟩ := h
  -- F₁⁺.p = F₁.p + 1 ≥ 2 since F₁.p ≥ 1.
  have h_F₁ext_p_ge_2 : (2 : ℕ∞) ≤ F₁.p + 1 :=
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ F₁.p + 1 := add_le_add F₁.p_pos le_rfl
  -- Reduce to producing a precision-2 witness in F₁⁺.withBound.
  suffices h_witness : ∃ v : Dyadic,
      v ∈ ((F₁.extend 1).withBound F₁.boundAfterNext F₁.boundAfterNext_nn) ∧
      ¬ Dyadic.precisionAtMost (1 : ℕ∞) v by
    obtain ⟨v, hv_mem, hv_not_p1⟩ := h_witness
    exact absurd (two_le_p_of_precision_two_witness (hsub v hv_mem) hv_not_p1)
      (not_le.mpr h_p_lt)
  -- Build a witness `Dyadic.ofIntZpow 3 k` for an appropriate `k`.
  -- Reusable builder: from `quantumOK` and `boundOK` for v, package full membership.
  have h_mk_member : ∀ k : ℤ,
      Dyadic.quantumAtLeast (F₁.exp.map (· - (1 : ℤ))) (Dyadic.ofIntZpow 3 k) →
      AbstractFormat.boundOK F₁.boundAfterNext (Dyadic.ofIntZpow 3 k) →
      Dyadic.ofIntZpow 3 k ∈
        ((F₁.extend 1).withBound F₁.boundAfterNext F₁.boundAfterNext_nn) := by
    intro k hq hb
    refine ⟨?_, ?_, ?_⟩
    · -- precisionAtMost (F₁.p + 1) (ofIntZpow 3 k)
      change Dyadic.precisionAtMost _ _
      exact Dyadic.precisionAtMost_mono h_F₁ext_p_ge_2
        (Dyadic.precisionAtMost_two_three_zpow k)
    · -- quantumAtLeast — `withBound` preserves `exp = (extend 1).exp = F.exp.map (· - 1)`
      change Dyadic.quantumAtLeast _ _
      exact hq
    · -- boundOK — `withBound`'s b = F₁.boundAfterNext.
      change AbstractFormat.boundOK F₁.boundAfterNext _
      exact hb
  rcases hF_exp : F₁.exp with _ | e
  · -- F₁.exp = ⊥. F₁⁺.exp = ⊥ ⇒ quantumAtLeast trivial.
    have h_q_triv : ∀ k : ℤ, Dyadic.quantumAtLeast (F₁.exp.map (· - (1 : ℤ)))
        (Dyadic.ofIntZpow 3 k) := by
      intro k; rw [hF_exp]; exact trivial
    rcases hF_b : F₁.b with _ | b
    · -- F₁.b = ⊤. Witness 3·2^0 = 3.
      refine ⟨Dyadic.ofIntZpow 3 0, h_mk_member 0 (h_q_triv 0) ?_,
        Dyadic.not_precisionAtMost_one_three_zpow 0⟩
      have h_top : F₁.boundAfterNext = ⊤ := by
        unfold AbstractFormat.boundAfterNext; rw [hF_b]
      rw [h_top]; trivial
    · -- F₁.b = (b : Dyadic). F.exp = ⊥ ⇒ next b = b + 1. Witness 3·2^(-2) = 3/4 ≤ 1 ≤ b + 1.
      refine ⟨Dyadic.ofIntZpow 3 (-2), h_mk_member (-2) (h_q_triv (-2)) ?_,
        Dyadic.not_precisionAtMost_one_three_zpow (-2)⟩
      have h_bAfter : F₁.boundAfterNext = ((F₁.next b : Dyadic) : WithTop Dyadic) := by
        unfold AbstractFormat.boundAfterNext; rw [hF_b]
      rw [h_bAfter]
      change |((Dyadic.ofIntZpow 3 (-2) : Dyadic) : ℝ)| ≤ ((F₁.next b : Dyadic) : ℝ)
      have h_next_eq : F₁.next b = b + 1 := by unfold AbstractFormat.next; rw [hF_exp]
      rw [h_next_eq]
      rw [Dyadic.coe_ofIntZpow]
      have hb_nn : 0 ≤ ((b : Dyadic) : ℝ) := F₁.b_nn_of_coe hF_b
      push_cast
      have h_v_eq : (3 : ℝ) * (2 : ℝ) ^ (-2 : ℤ) = 3/4 := by norm_num
      rw [h_v_eq]
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 3/4)]
      linarith
  · -- F₁.exp = (e : ℤ). Use `d ≠ 0` to derive `|d| ≥ 2^e`.
    have h_q_d : Dyadic.quantumAtLeast (F₁.exp) d := hd_mem.2.1
    rw [hF_exp] at h_q_d
    have hd_abs_ge : (2 : ℝ)^e ≤ |(d : ℝ)| :=
      Dyadic.abs_ge_two_zpow_of_quantum h_q_d hd_ne
    have h_q_v : ∀ k : ℤ, k ≥ e - 1 →
        Dyadic.quantumAtLeast (F₁.exp.map (· - (1 : ℤ))) (Dyadic.ofIntZpow 3 k) := by
      intro k hk
      rw [hF_exp]
      change Dyadic.quantumAtLeast (((e - 1 : ℤ) : WithBot ℤ)) _
      rw [Dyadic.quantumAtLeast_coe]
      refine ⟨3 * 2 ^ (k - (e - 1)).toNat, ?_⟩
      rw [Dyadic.coe_ofIntZpow]
      have h_split := two_zpow_split_toNat hk
      push_cast
      rw [h_split]
      ring
    rcases hF_b : F₁.b with _ | b
    · -- F₁.b = ⊤. Witness 3·2^(e-1).
      refine ⟨Dyadic.ofIntZpow 3 (e - 1), h_mk_member (e - 1) (h_q_v (e - 1) (by omega)) ?_,
        Dyadic.not_precisionAtMost_one_three_zpow (e - 1)⟩
      have h_top : F₁.boundAfterNext = ⊤ := by
        unfold AbstractFormat.boundAfterNext; rw [hF_b]
      rw [h_top]; trivial
    · -- F₁.b = (b : Dyadic). |d| ≤ b. With |d| ≥ 2^e: b ≥ 2^e.
      have hd_le_b : |((d : Dyadic) : ℝ)| ≤ ((b : Dyadic) : ℝ) := by
        have hb_OK : AbstractFormat.boundOK F₁.b d := hd_mem.2.2
        rw [hF_b] at hb_OK
        exact hb_OK
      have hb_ge : (2 : ℝ)^e ≤ ((b : Dyadic) : ℝ) := le_trans hd_abs_ge hd_le_b
      have h2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
      have hb_pos : 0 < ((b : Dyadic) : ℝ) := lt_of_lt_of_le h2e_pos hb_ge
      refine ⟨Dyadic.ofIntZpow 3 (e - 1), h_mk_member (e - 1) (h_q_v (e - 1) (by omega)) ?_,
        Dyadic.not_precisionAtMost_one_three_zpow (e - 1)⟩
      have h_bAfter : F₁.boundAfterNext = ((F₁.next b : Dyadic) : WithTop Dyadic) := by
        unfold AbstractFormat.boundAfterNext; rw [hF_b]
      rw [h_bAfter]
      change |((Dyadic.ofIntZpow 3 (e - 1) : Dyadic) : ℝ)| ≤ ((F₁.next b : Dyadic) : ℝ)
      -- Now show `|3·2^(e-1)| = 1.5·2^e ≤ F₁.next b ≥ b + 2^e ≥ 2^(e+1) = 2·2^e ≥ 1.5·2^e`.
      -- The witness magnitude is 1.5·2^e. F₁.next b ≥ b + 2^e ≥ 2·2^e ≥ 1.5·2^e.
      have h_v_eq : ((Dyadic.ofIntZpow 3 (e - 1) : Dyadic) : ℝ) = (3 : ℝ) * (2 : ℝ)^(e - 1) := by
        rw [Dyadic.coe_ofIntZpow]; push_cast; ring
      have h_v_pos : (0 : ℝ) ≤ (3 : ℝ) * (2 : ℝ)^(e - 1) := by positivity
      have h_v_split : (3 : ℝ) * (2 : ℝ)^(e - 1) = (2 : ℝ)^e + (2 : ℝ)^(e - 1) := by
        rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]; field_simp; ring
      have h_e1_le_e : (2 : ℝ)^(e - 1) ≤ (2 : ℝ)^e :=
        zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
      rcases hF_p : F₁.p with _ | p
      · -- F₁.p = ⊤. F₁.next b = b + 2^e.
        have h_next_eq : F₁.next b = b + Dyadic.ofIntZpow 1 e :=
          AbstractFormat.next_eq_p_top F₁ hF_exp hF_p b
        rw [h_next_eq, h_v_eq]
        push_cast
        rw [abs_of_nonneg h_v_pos, h_v_split]
        rw [Dyadic.coe_ofIntZpow]; push_cast
        linarith
      · -- F₁.p = (p : ℕ). Step ≥ 2^e.
        have h_next_eq : F₁.next b = b + Dyadic.ofIntZpow 1
            (max e (Int.log 2 ((b : Dyadic) : ℝ) - (p : ℤ) + 1)) :=
          AbstractFormat.next_eq_finite_pos F₁ hF_exp hF_p hb_pos
        rw [h_next_eq, h_v_eq]
        push_cast
        rw [abs_of_nonneg h_v_pos, h_v_split]
        rw [Dyadic.coe_ofIntZpow]; push_cast
        have h_step_ge_e : e ≤ max e (Int.log 2 ((b : Dyadic) : ℝ) - (p : ℤ) + 1) :=
          le_max_left _ _
        have h_step_pow : (2 : ℝ)^e ≤
            (2 : ℝ)^(max e (Int.log 2 ((b : Dyadic) : ℝ) - (p : ℤ) + 1)) :=
          zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h_step_ge_e
        linarith

/-- If `F₁` is trivial (contains only `0`) and `w' ∈ F₁` then `Rounds F₁ .ToZero x w'`
holds for any real `x`, since `w' = 0` is the unique element. -/
private theorem Rounds.toZero_of_trivial {F₁ : AbstractFormat}
    (hF₁_triv : ∀ d : Dyadic, d ∈ F₁ → (d : ℝ) = 0)
    {x : ℝ} {w' : Dyadic} (hw : w' ∈ F₁) :
    Rounds F₁ .ToZero x w' := by
  have hw'_zero : (w' : ℝ) = 0 := hF₁_triv w' hw
  refine ⟨hw, ?_, ?_, ?_⟩
  · rw [hw'_zero, abs_zero]; exact abs_nonneg _
  · rw [hw'_zero, zero_mul]
  · intro v hvF₁ _ _
    have hv_zero : (v : ℝ) = 0 := hF₁_triv v hvF₁
    rw [hv_zero, hw'_zero]

/-- If `F₁` is trivial, the chained RAZ rounding forces `x = 0` (so the
conclusion `Rounds F₁ .AwayZero x w'` reduces to the trivial RAZ at zero). The
forcing comes from RTO's parity clause: with `z = 0` (the only F₁ image
under RAZ), `x ≠ 0` would require `IsOdd F₂ 0`, which is false. -/
private theorem Rounds.awayZero_of_trivial {F₁ F₂ : AbstractFormat}
    (hF₁_triv : ∀ d : Dyadic, d ∈ F₁ → (d : ℝ) = 0)
    {x : ℝ} {z w' : Dyadic}
    (hz : Rounds F₂ .ToOdd x z) (hw : Rounds F₁ .AwayZero (z : ℝ) w') :
    Rounds F₁ .AwayZero x w' := by
  have hw'F₁ : w' ∈ F₁ := hw.1
  have hw'_zero : (w' : ℝ) = 0 := hF₁_triv w' hw'F₁
  have hzw : |(z : ℝ)| ≤ |(w' : ℝ)| := hw.2.1
  rw [hw'_zero, abs_zero] at hzw
  have hz_zero_real : (z : ℝ) = 0 := abs_nonpos_iff.mp hzw
  have hz_zero : z = 0 := Subtype.ext (by rw [hz_zero_real]; rfl)
  have hx_zero : x = 0 := by
    obtain ⟨_, _, hz_odd_imp⟩ := hz
    by_contra hxne
    have hxne_z : x ≠ (z : ℝ) := by rw [hz_zero_real]; exact hxne
    have h_iod : IsOdd F₂ z := hz_odd_imp hxne_z
    rw [hz_zero] at h_iod
    exact h_iod.ne_zero rfl
  refine ⟨hw'F₁, ?_, ?_, ?_⟩
  · rw [hx_zero, hw'_zero]
  · rw [hx_zero, hw'_zero, mul_zero]
  · intro v hvF₁ _ _
    rw [hF₁_triv v hvF₁, hw'_zero]

/-- RN analog of `hp_F₂_or_F₁_trivial` (for round-to-nearest, used by
`rndRTO_RN`): from the paper-aligned containment
`((F₁.extend 2).withBound (F₁.extend 1).boundAfterNext _) ⊆ F₂`,
either `2 ≤ F₂.p` or `F₁` contains only `0`.

The same precision-2 witness `v = 3·2^k` works because the RN format only
has *looser* precision and quantum constraints than RTZ's `F₁.extend 1`
shape (`F₁.p + 2 ≥ F₁.p + 1`, `F₁.exp - 2 ≤ F₁.exp - 1`). The bound
`(F₁.extend 1).boundAfterNext = (F₁.extend 1).next F₁.b` is large enough:
its step is `≥ 2^(F₁.exp - 1)`, so when F₁ has a nonzero element
(`F₁.b ≥ 2^F₁.exp`), the bound is `≥ 1.5·2^F₁.exp = |v|`. -/
private theorem hp_F₂_or_F₁_trivial_RN {F₁ F₂ : AbstractFormat}
    (hsub : ((F₁.extend 2).withBound (F₁.extend 1).boundAfterNext
              (F₁.extend 1).boundAfterNext_nn) ⊆ F₂) :
    2 ≤ F₂.p ∨ ∀ d : Dyadic, d ∈ F₁ → (d : ℝ) = 0 := by
  by_contra h
  push Not at h
  obtain ⟨h_p_lt, ⟨d, hd_mem, hd_ne⟩⟩ := h
  -- F₁⁺².p = F₁.p + 2 ≥ 3 ≥ 2.
  have h_F₁ext2_p_ge_2 : (2 : ℕ∞) ≤ F₁.p + 2 :=
    calc (2 : ℕ∞) ≤ 1 + 2 := by norm_num
      _ ≤ F₁.p + 2 := add_le_add F₁.p_pos le_rfl
  suffices h_witness : ∃ v : Dyadic,
      v ∈ ((F₁.extend 2).withBound (F₁.extend 1).boundAfterNext
            (F₁.extend 1).boundAfterNext_nn) ∧
      ¬ Dyadic.precisionAtMost (1 : ℕ∞) v by
    obtain ⟨v, hv_mem, hv_not_p1⟩ := h_witness
    exact absurd (two_le_p_of_precision_two_witness (hsub v hv_mem) hv_not_p1)
      (not_le.mpr h_p_lt)
  -- Builder: package full membership for `Dyadic.ofIntZpow 3 k`.
  have h_mk_member : ∀ k : ℤ,
      Dyadic.quantumAtLeast (F₁.exp.map (· - (2 : ℤ))) (Dyadic.ofIntZpow 3 k) →
      AbstractFormat.boundOK (F₁.extend 1).boundAfterNext (Dyadic.ofIntZpow 3 k) →
      Dyadic.ofIntZpow 3 k ∈
        ((F₁.extend 2).withBound (F₁.extend 1).boundAfterNext
          (F₁.extend 1).boundAfterNext_nn) := by
    intro k hq hb
    refine ⟨?_, ?_, ?_⟩
    · change Dyadic.precisionAtMost _ _
      exact Dyadic.precisionAtMost_mono h_F₁ext2_p_ge_2
        (Dyadic.precisionAtMost_two_three_zpow k)
    · change Dyadic.quantumAtLeast _ _; exact hq
    · change AbstractFormat.boundOK (F₁.extend 1).boundAfterNext _; exact hb
  rcases hF_exp : F₁.exp with _ | e
  · -- F₁.exp = ⊥. F₁⁺².exp = ⊥ ⇒ quantumAtLeast trivial.
    have h_q_triv : ∀ k : ℤ, Dyadic.quantumAtLeast (F₁.exp.map (· - (2 : ℤ)))
        (Dyadic.ofIntZpow 3 k) := by
      intro k; rw [hF_exp]; exact trivial
    rcases hF_b : F₁.b with _ | b
    · -- F₁.b = ⊤. (F₁.extend 1).b = ⊤ ⇒ boundAfterNext = ⊤. Witness 3.
      refine ⟨Dyadic.ofIntZpow 3 0, h_mk_member 0 (h_q_triv 0) ?_,
        Dyadic.not_precisionAtMost_one_three_zpow 0⟩
      have h_top : (F₁.extend 1).boundAfterNext = ⊤ := by
        unfold AbstractFormat.boundAfterNext
        have : (F₁.extend 1).b = F₁.b := rfl
        rw [this, hF_b]
      rw [h_top]; trivial
    · -- F₁.b = (b : Dyadic). (F₁.extend 1).next b = b + 1 (since F₁⁺.exp = ⊥).
      -- Witness 3·2^(-2) = 3/4 ≤ 1 ≤ b + 1.
      refine ⟨Dyadic.ofIntZpow 3 (-2), h_mk_member (-2) (h_q_triv (-2)) ?_,
        Dyadic.not_precisionAtMost_one_three_zpow (-2)⟩
      have h_bAfter : (F₁.extend 1).boundAfterNext =
          (((F₁.extend 1).next b : Dyadic) : WithTop Dyadic) := by
        unfold AbstractFormat.boundAfterNext
        have : (F₁.extend 1).b = F₁.b := rfl
        rw [this, hF_b]
      rw [h_bAfter]
      change |((Dyadic.ofIntZpow 3 (-2) : Dyadic) : ℝ)|
        ≤ (((F₁.extend 1).next b : Dyadic) : ℝ)
      have h_F₁ext_exp : (F₁.extend 1).exp = ⊥ := by
        change F₁.exp.map (· - (1 : ℤ)) = ⊥
        rw [hF_exp]; rfl
      have h_next_eq : (F₁.extend 1).next b = b + 1 := by
        unfold AbstractFormat.next; rw [h_F₁ext_exp]
      rw [h_next_eq]
      rw [Dyadic.coe_ofIntZpow]
      have hb_nn : 0 ≤ ((b : Dyadic) : ℝ) := F₁.b_nn_of_coe hF_b
      push_cast
      have h_v_eq : (3 : ℝ) * (2 : ℝ) ^ (-2 : ℤ) = 3/4 := by norm_num
      rw [h_v_eq]
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 3/4)]
      linarith
  · -- F₁.exp = (e : ℤ). Use d ≠ 0 ⇒ |d| ≥ 2^e ⇒ b ≥ 2^e.
    have h_q_d : Dyadic.quantumAtLeast (F₁.exp) d := hd_mem.2.1
    rw [hF_exp] at h_q_d
    have hd_abs_ge : (2 : ℝ)^e ≤ |(d : ℝ)| :=
      Dyadic.abs_ge_two_zpow_of_quantum h_q_d hd_ne
    have h_q_v : ∀ k : ℤ, k ≥ e - 2 →
        Dyadic.quantumAtLeast (F₁.exp.map (· - (2 : ℤ))) (Dyadic.ofIntZpow 3 k) := by
      intro k hk
      rw [hF_exp]
      change Dyadic.quantumAtLeast (((e - 2 : ℤ) : WithBot ℤ)) _
      rw [Dyadic.quantumAtLeast_coe]
      refine ⟨3 * 2 ^ (k - (e - 2)).toNat, ?_⟩
      rw [Dyadic.coe_ofIntZpow]
      have h_split := two_zpow_split_toNat hk
      push_cast; rw [h_split]; ring
    rcases hF_b : F₁.b with _ | b
    · -- F₁.b = ⊤. Witness 3·2^(e-1).
      refine ⟨Dyadic.ofIntZpow 3 (e - 1), h_mk_member (e - 1) (h_q_v (e - 1) (by omega)) ?_,
        Dyadic.not_precisionAtMost_one_three_zpow (e - 1)⟩
      have h_top : (F₁.extend 1).boundAfterNext = ⊤ := by
        unfold AbstractFormat.boundAfterNext
        have : (F₁.extend 1).b = F₁.b := rfl
        rw [this, hF_b]
      rw [h_top]; trivial
    · -- F₁.b = (b : Dyadic). |d| ≤ b + nontriv ⇒ b ≥ 2^e.
      have hd_le_b : |((d : Dyadic) : ℝ)| ≤ ((b : Dyadic) : ℝ) := by
        have hb_OK : AbstractFormat.boundOK F₁.b d := hd_mem.2.2
        rw [hF_b] at hb_OK; exact hb_OK
      have hb_ge : (2 : ℝ)^e ≤ ((b : Dyadic) : ℝ) := le_trans hd_abs_ge hd_le_b
      have h2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
      have hb_pos : 0 < ((b : Dyadic) : ℝ) := lt_of_lt_of_le h2e_pos hb_ge
      refine ⟨Dyadic.ofIntZpow 3 (e - 1), h_mk_member (e - 1) (h_q_v (e - 1) (by omega)) ?_,
        Dyadic.not_precisionAtMost_one_three_zpow (e - 1)⟩
      have h_bAfter : (F₁.extend 1).boundAfterNext =
          (((F₁.extend 1).next b : Dyadic) : WithTop Dyadic) := by
        unfold AbstractFormat.boundAfterNext
        have : (F₁.extend 1).b = F₁.b := rfl
        rw [this, hF_b]
      rw [h_bAfter]
      change |((Dyadic.ofIntZpow 3 (e - 1) : Dyadic) : ℝ)|
        ≤ (((F₁.extend 1).next b : Dyadic) : ℝ)
      have h_F₁ext_exp : (F₁.extend 1).exp = ((e - 1 : ℤ) : WithBot ℤ) := by
        change F₁.exp.map (· - (1 : ℤ)) = _
        rw [hF_exp]; rfl
      have h_v_eq : ((Dyadic.ofIntZpow 3 (e - 1) : Dyadic) : ℝ)
          = (3 : ℝ) * (2 : ℝ)^(e - 1) := by
        rw [Dyadic.coe_ofIntZpow]; push_cast; ring
      have h_v_pos : (0 : ℝ) ≤ (3 : ℝ) * (2 : ℝ)^(e - 1) := by positivity
      have h_v_split : (3 : ℝ) * (2 : ℝ)^(e - 1) = (2 : ℝ)^e + (2 : ℝ)^(e - 1) := by
        rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]; field_simp; ring
      have h_e1_le_e : (2 : ℝ)^(e - 1) ≤ (2 : ℝ)^e :=
        zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
      rcases hF_p : F₁.p with _ | p
      · -- F₁.p = ⊤. F₁⁺.p = ⊤ + 1 = ⊤. F₁⁺.next b = b + 2^(e-1) (since F₁⁺.exp = e-1).
        have h_F₁ext_p : (F₁.extend 1).p = ⊤ := by
          change F₁.p + 1 = ⊤
          rw [hF_p]; rfl
        have h_next_eq : (F₁.extend 1).next b = b + Dyadic.ofIntZpow 1 (e - 1) :=
          AbstractFormat.next_eq_p_top (F₁.extend 1) h_F₁ext_exp h_F₁ext_p b
        rw [h_next_eq, h_v_eq]; push_cast
        rw [abs_of_nonneg h_v_pos, h_v_split]
        rw [Dyadic.coe_ofIntZpow]; push_cast
        linarith
      · -- F₁.p = (p : ℕ). F₁⁺.p = p + 1.
        have h_F₁ext_p : (F₁.extend 1).p = (((p + 1 : ℕ) : ℕ∞)) := by
          change F₁.p + 1 = _
          rw [hF_p]; push_cast; rfl
        have h_next_eq : (F₁.extend 1).next b = b + Dyadic.ofIntZpow 1
            (max (e - 1) (Int.log 2 ((b : Dyadic) : ℝ) - ((p + 1 : ℕ) : ℤ) + 1)) :=
          AbstractFormat.next_eq_finite_pos (F₁.extend 1) h_F₁ext_exp h_F₁ext_p hb_pos
        rw [h_next_eq, h_v_eq]; push_cast
        rw [abs_of_nonneg h_v_pos, h_v_split]
        rw [Dyadic.coe_ofIntZpow]; push_cast
        rw [one_mul]
        set k_step := max (e - 1) (Int.log 2 ((b : Dyadic) : ℝ) - ((p : ℤ) + 1) + 1)
            with h_kstep_def
        have h_step_ge : (e - 1) ≤ k_step := le_max_left _ _
        have h_step_pow : (2 : ℝ)^(e - 1) ≤ (2 : ℝ)^k_step :=
          zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h_step_ge
        linarith

/-- If `F₁` is trivial (contains only `0`) then `Rounds F₁ (.Nearest tb) x w'`
holds for any real `x` and tie-break `tb`, whenever `w' ∈ F₁`. With
`F₁ = {0}`, the closeness and tie-break conditions are vacuous (every F₁
element equals `w' = 0`); the adjacency condition is satisfied by the
round-down branch (when `x ≥ 0`) or the round-up branch (when `x < 0`). -/
private theorem Rounds.nearest_of_trivial {F₁ : AbstractFormat}
    (hF₁_triv : ∀ d : Dyadic, d ∈ F₁ → (d : ℝ) = 0)
    {tb : TieBreak}
    {x : ℝ} {w' : Dyadic} (hw : w' ∈ F₁) :
    Rounds F₁ (.Nearest tb) x w' := by
  have hw'_zero : (w' : ℝ) = 0 := hF₁_triv w' hw
  -- Every F₁ element equals w' (since both are 0).
  have h_eq_w' : ∀ z : Dyadic, z ∈ F₁ → z = w' := fun z hzF₁ =>
    Subtype.ext (by rw [hF₁_triv z hzF₁, hw'_zero])
  -- Shared adjacency proof.
  have h_adj : IsFaithfulRound F₁ x w' := by
    rcases lt_or_ge x 0 with hx_neg | hx_nn
    · right
      refine ⟨hw, by rw [hw'_zero]; linarith, ?_⟩
      intro v hvF₁ _
      rw [hF₁_triv v hvF₁, hw'_zero]
    · left
      refine ⟨hw, by rw [hw'_zero]; exact hx_nn, ?_⟩
      intro v hvF₁ _
      rw [hF₁_triv v hvF₁, hw'_zero]
  -- Shared closeness proof.
  have h_close : ∀ z : Dyadic, z ∈ F₁ → IsFaithfulRound F₁ x z →
      |x - (w' : ℝ)| ≤ |x - (z : ℝ)| := by
    intro z hzF₁ _
    rw [hF₁_triv z hzF₁, hw'_zero]
  -- Dispatch on tb only for the tie-break clause shape.
  cases tb with
  | ToEven =>
    refine ⟨hw, h_adj, h_close, ?_⟩
    rintro ⟨z, hzF₁, _, hz_ne_w', _⟩
    exact (hz_ne_w' (h_eq_w' z hzF₁)).elim
  | AwayZero =>
    refine ⟨hw, h_adj, h_close, ?_⟩
    intro z hzF₁ _ hz_ne_w' _
    exact (hz_ne_w' (h_eq_w' z hzF₁)).elim

/-- Given the paper-aligned containment, derive the weaker
`F₁.extend 1 ⊆ F₂` form (used by the `_pos` private theorems). The bound
`F₁.boundAfterNext` is at least as large as `F₁.b`, so any `y ∈ F₁.extend 1`
also satisfies the relaxed bound. -/
private theorem extend_one_subset_of_paper_subset {F₁ F₂ : AbstractFormat}
    (hsub : ((F₁.extend 1).withBound F₁.boundAfterNext F₁.boundAfterNext_nn) ⊆ F₂) :
    F₁.extend 1 ⊆ F₂ := by
  intro y hy
  apply hsub
  obtain ⟨hp_y, hq_y, hb_y⟩ := hy
  refine ⟨hp_y, hq_y, ?_⟩
  change AbstractFormat.boundOK F₁.boundAfterNext y
  cases hF_b : F₁.b with
  | top =>
    have h_top : F₁.boundAfterNext = ⊤ := by
      unfold AbstractFormat.boundAfterNext; rw [hF_b]
    rw [h_top]; trivial
  | coe b =>
    have h_after : F₁.boundAfterNext = ((F₁.next b : Dyadic) : WithTop Dyadic) := by
      unfold AbstractFormat.boundAfterNext; rw [hF_b]
    rw [h_after]
    change |((y : Dyadic) : ℝ)| ≤ ((F₁.next b : Dyadic) : ℝ)
    change AbstractFormat.boundOK F₁.b y at hb_y
    rw [hF_b] at hb_y
    have h_y_le_b : |((y : Dyadic) : ℝ)| ≤ ((b : Dyadic) : ℝ) := hb_y
    have hb_nn : 0 ≤ ((b : Dyadic) : ℝ) := F₁.b_nn_of_coe hF_b
    linarith [AbstractFormat.self_le_next F₁ b hb_nn]

/-- RN analog of `extend_one_subset_of_paper_subset` (for round-to-nearest,
used by `rndRTO_RN`): from the paper-aligned containment
`((F₁.extend 2).withBound (F₁.extend 1).boundAfterNext _) ⊆ F₂`,
derive the weaker `F₁.extend 2 ⊆ F₂` form. -/
private theorem extend_two_subset_of_paper_RN_subset {F₁ F₂ : AbstractFormat}
    (hsub : ((F₁.extend 2).withBound (F₁.extend 1).boundAfterNext
              (F₁.extend 1).boundAfterNext_nn) ⊆ F₂) :
    F₁.extend 2 ⊆ F₂ := by
  intro y hy
  apply hsub
  obtain ⟨hp_y, hq_y, hb_y⟩ := hy
  refine ⟨hp_y, hq_y, ?_⟩
  change AbstractFormat.boundOK (F₁.extend 1).boundAfterNext y
  cases hF_b : F₁.b with
  | top =>
    have h_top : (F₁.extend 1).boundAfterNext = ⊤ := by
      unfold AbstractFormat.boundAfterNext
      have : (F₁.extend 1).b = F₁.b := rfl
      rw [this, hF_b]
    rw [h_top]; trivial
  | coe b =>
    have h_after : (F₁.extend 1).boundAfterNext =
        (((F₁.extend 1).next b : Dyadic) : WithTop Dyadic) := by
      unfold AbstractFormat.boundAfterNext
      have : (F₁.extend 1).b = F₁.b := rfl
      rw [this, hF_b]
    rw [h_after]
    change |((y : Dyadic) : ℝ)| ≤ (((F₁.extend 1).next b : Dyadic) : ℝ)
    -- y ∈ F₁.extend 2 has |y| ≤ F₁.b = b.
    change AbstractFormat.boundOK (F₁.extend 2).b y at hb_y
    have hF₁_ext2_b : (F₁.extend 2).b = F₁.b := rfl
    rw [hF₁_ext2_b, hF_b] at hb_y
    have h_y_le_b : |((y : Dyadic) : ℝ)| ≤ ((b : Dyadic) : ℝ) := hb_y
    have hb_nn : 0 ≤ ((b : Dyadic) : ℝ) := F₁.b_nn_of_coe hF_b
    linarith [AbstractFormat.self_le_next (F₁.extend 1) b hb_nn]

/-- `(F.extend 1).extend 1 ⊆ F.extend 2` via precision/quantum equivalence. -/
private theorem extend_one_extend_one_subset_extend_two (F : AbstractFormat) :
    (F.extend 1).extend 1 ⊆ F.extend 2 := by
  intro y hy
  obtain ⟨hp, hq, hb⟩ := hy
  refine ⟨?_, ?_, hb⟩
  · -- precisionAtMost (F.extend 2).p = (F.p + 2) y from precisionAtMost ((F.p + 1) + 1) y.
    change Dyadic.precisionAtMost (F.p + 2) y
    change Dyadic.precisionAtMost (F.p + 1 + 1) y at hp
    have h_eq : F.p + 1 + 1 = F.p + 2 := by
      cases F.p with
      | top => simp
      | coe n =>
        change (((n + 1 + 1 : ℕ)) : ℕ∞) = (((n + 2 : ℕ)) : ℕ∞)
        push_cast; ring
    rw [h_eq] at hp; exact hp
  · -- quantumAtLeast (F.extend 2).exp = (F.exp.map (· - 2)) y.
    change Dyadic.quantumAtLeast (F.exp.map (· - (2 : ℤ))) y
    change Dyadic.quantumAtLeast ((F.exp.map (· - (1 : ℤ))).map (· - (1 : ℤ))) y at hq
    have h_eq : (F.exp.map (· - (1 : ℤ))).map (· - (1 : ℤ)) = F.exp.map (· - (2 : ℤ)) := by
      cases F.exp with
      | bot => rfl
      | coe e =>
        change ((((e - 1 : ℤ)) - 1 : ℤ) : WithBot ℤ) = (((e - 2 : ℤ)) : WithBot ℤ)
        congr 1; ring
    rw [h_eq] at hq; exact hq

/-- Midpoint of F-adjacent F₁-elements lies in F₁.extend 1. Dispatches on
both F₁.p and F₁.exp shapes. -/
private theorem midpoint_in_F₁_extend_one_of_F_adjacent {F₁ : AbstractFormat}
    {y₁ y₂ : Dyadic} (hy₁F : y₁ ∈ F₁) (hy₂F : y₂ ∈ F₁)
    (h_lt : ((y₁ : Dyadic) : ℝ) < ((y₂ : Dyadic) : ℝ))
    (h_adj : ∀ y : Dyadic, y ∈ F₁ → ((y₁ : Dyadic) : ℝ) < ((y : Dyadic) : ℝ) →
              ((y₂ : Dyadic) : ℝ) ≤ ((y : Dyadic) : ℝ)) :
    Dyadic.midpoint y₁ y₂ ∈ F₁.extend 1 := by
  rcases hp : F₁.p with _ | p
  · -- F₁.p = ⊤: not_degenerate forces F₁.exp ≠ ⊥.
    have hexp_ne_bot : F₁.exp ≠ ⊥ := by
      rcases F₁.not_degenerate with ⟨hpne, _⟩ | hexpne
      · exact absurd hp hpne
      · exact hexpne
    rcases hF_exp : F₁.exp with _ | exp
    · exact absurd hF_exp hexp_ne_bot
    · exact AbstractFormat.midpoint_mem_extend_one_of_p_top F₁ hp hF_exp hy₁F hy₂F
  · have hp_ge_1 : 1 ≤ p := by
      have hpp := F₁.p_pos
      rw [hp] at hpp
      exact WithTop.coe_le_coe.mp hpp
    rcases hF_exp : F₁.exp with _ | exp
    · -- F₁.exp = ⊥, F₁.p finite.
      exact AbstractFormat.midpoint_mem_extend_one_of_F_adjacent_exp_bot
        F₁ hp hF_exp hp_ge_1 hy₁F hy₂F h_lt h_adj
    · -- Both finite.
      exact AbstractFormat.midpoint_mem_extend_one_of_F_adjacent
        F₁ hp hF_exp hp_ge_1 hy₁F hy₂F h_lt h_adj

/-- F-adjacency of (w', z') in F₁: no F₁ element strictly between. Derived
from `RoundDown w'` ∨ `RoundUp w'` + `RoundDown z'` ∨ `RoundUp z'` for `x`,
when `w' < z'` (or symmetric). For w' < z', x ∈ (w', z') and any F₁-y with
w' < y must be ≥ z' (else contradicts the round-down/up structure). -/
private theorem F_adjacent_of_RN_round_pair {F₁ : AbstractFormat}
    {x : ℝ} {w' z' : Dyadic}
    (hw'_adj : Rounds F₁ .ToNegative x w' ∨ Rounds F₁ .ToPositive x w')
    (hz'_adj : Rounds F₁ .ToNegative x z' ∨ Rounds F₁ .ToPositive x z')
    (hw'_lt_x : ((w' : Dyadic) : ℝ) ≤ x) (hx_lt_z' : x ≤ ((z' : Dyadic) : ℝ)) :
    ∀ y : Dyadic, y ∈ F₁ → ((w' : Dyadic) : ℝ) < ((y : Dyadic) : ℝ) →
      ((z' : Dyadic) : ℝ) ≤ ((y : Dyadic) : ℝ) := by
  intro y hyF₁ h_w_lt_y
  by_cases h_y_le_x : ((y : Dyadic) : ℝ) ≤ x
  · -- y ≤ x. By RoundDown w' (or via RoundUp w' contradicting w' ≤ x), y ≤ w'.
    exfalso
    rcases hw'_adj with hwRD | hwRU
    · obtain ⟨_, _, hw_max⟩ := hwRD
      have h_y_le_w' : ((y : Dyadic) : ℝ) ≤ (w' : ℝ) := hw_max y hyF₁ h_y_le_x
      linarith
    · obtain ⟨_, hxw, _⟩ := hwRU
      -- RoundUp w': x ≤ w'. But h_lt: w' < z' and hx_lt_z'. So w' < z' and x ≤ w'.
      -- Combined with hw'_lt_x (w' ≤ x): w' = x. With x ≤ w' and w' ≤ x.
      -- y ≤ x = w'. Combined w' < y: contradiction.
      have hxw' : x = (w' : ℝ) := le_antisymm hxw hw'_lt_x
      rw [← hxw'] at h_w_lt_y
      linarith
  · push Not at h_y_le_x
    -- y > x. By RoundUp z' (or RoundDown z' contradicting), z' ≤ y.
    rcases hz'_adj with hzRD | hzRU
    · obtain ⟨_, hzx_le, _⟩ := hzRD
      -- RoundDown z': z' ≤ x. With hx_lt_z': x ≤ z'. So z' ≤ x ≤ z' ⟹ z' = x.
      have hxz' : x = (z' : ℝ) := le_antisymm hx_lt_z' hzx_le
      linarith
    · obtain ⟨_, _, hz_min⟩ := hzRU
      have h_z'_le_y : (z' : ℝ) ≤ ((y : Dyadic) : ℝ) := hz_min y hyF₁ (le_of_lt h_y_le_x)
      exact h_z'_le_y

/-- F-adjacent midpoint membership in F₂. Combines `midpoint_in_F₁_extend_one`
with the chain `F₁.extend 1 ⊆ F₁.extend 2 ⊆ F₂` (where the last step uses
the paper-aligned RNE containment). -/
private theorem midpoint_F₁_in_F₂_of_F_adjacent {F₁ F₂ : AbstractFormat}
    (hsub : ((F₁.extend 2).withBound (F₁.extend 1).boundAfterNext
              (F₁.extend 1).boundAfterNext_nn) ⊆ F₂)
    {y₁ y₂ : Dyadic} (hy₁F : y₁ ∈ F₁) (hy₂F : y₂ ∈ F₁)
    (h_lt : ((y₁ : Dyadic) : ℝ) < ((y₂ : Dyadic) : ℝ))
    (h_adj : ∀ y : Dyadic, y ∈ F₁ → ((y₁ : Dyadic) : ℝ) < ((y : Dyadic) : ℝ) →
              ((y₂ : Dyadic) : ℝ) ≤ ((y : Dyadic) : ℝ)) :
    Dyadic.midpoint y₁ y₂ ∈ F₂ := by
  have h_mid_ext_one := midpoint_in_F₁_extend_one_of_F_adjacent
    hy₁F hy₂F h_lt h_adj
  have h_in_ext_2 : Dyadic.midpoint y₁ y₂ ∈ F₁.extend 2 := by
    obtain ⟨hp, hq, hb⟩ := h_mid_ext_one
    refine ⟨?_, ?_, hb⟩
    · have h_p_le : F₁.p + 1 ≤ F₁.p + 2 := by
        cases F₁.p with
        | top => simp
        | coe n =>
          change ((n + 1 : ℕ) : ℕ∞) ≤ ((n + 2 : ℕ) : ℕ∞)
          exact_mod_cast (by omega : n + 1 ≤ n + 2)
      change Dyadic.precisionAtMost _ _
      exact Dyadic.precisionAtMost_mono h_p_le hp
    · change Dyadic.quantumAtLeast _ _
      have h_exp_ge : (F₁.exp.map (· - (2 : ℤ))) ≤ (F₁.exp.map (· - (1 : ℤ))) := by
        cases F₁.exp with
        | bot => simp
        | coe e =>
          change ((e - 2 : ℤ) : WithBot ℤ) ≤ ((e - 1 : ℤ) : WithBot ℤ)
          exact WithBot.coe_le_coe.mpr (by linarith)
      exact Dyadic.quantumAtLeast_anti h_exp_ge hq
  exact extend_two_subset_of_paper_RN_subset hsub _ h_in_ext_2

/-- **rnd-RTO-RTZ** (Fig. 9), paper-aligned form, positive case `0 < x`. -/
private theorem rndRTO_RTZ_pos {F₁ F₂ : AbstractFormat}
    (hsub : F₁.extend 1 ⊆ F₂)
    (hp_F₂ : 2 ≤ F₂.p)
    {x : ℝ} (hx_pos : 0 < x)
    {z w' : Dyadic}
    (hz : Rounds F₂ .ToOdd x z)
    (hw : Rounds F₁ .ToZero (z : ℝ) w') :
    Rounds F₁ .ToZero x w' := by
  have hF₁_sub_ext : F₁ ⊆ F₁.extend 1 := self_subset_extend F₁ 1
  have hsub' : F₁ ⊆ F₂ := fun y hy => hsub _ (hF₁_sub_ext _ hy)
  -- Body: copied from `rndRTO_RTZ_pos`, but replace the
  -- `notMem_of_lower_numDigits` step with `notMem_of_extend_subset`.
  have hz_nn : 0 ≤ (z : ℝ) := Rounds.toOdd_nonneg_of_nn hx_pos.le hz
  obtain ⟨hzF₂, hz_adj, hz_odd_imp⟩ := hz
  obtain ⟨hw'F₁, hw'_bnd_z, hw'_sign_z, hw'_max⟩ := hw
  have hx_abs : |x| = x := abs_of_pos hx_pos
  have hz_abs : |(z : ℝ)| = (z : ℝ) := abs_of_nonneg hz_nn
  rw [hz_abs] at hw'_bnd_z
  have hw'_nn : 0 ≤ (w' : ℝ) := by
    rcases lt_or_eq_of_le hz_nn with hzpos | hzeq
    · nlinarith [hw'_sign_z]
    · have h1 : |(w' : ℝ)| ≤ 0 := hzeq.symm ▸ hw'_bnd_z
      have hw'0 : (w' : ℝ) = 0 := abs_nonpos_iff.mp h1
      linarith
  have hw'_abs : |(w' : ℝ)| = (w' : ℝ) := abs_of_nonneg hw'_nn
  have hw'_le_x : (w' : ℝ) ≤ x := by
    rcases hz_adj with hRD | hRU
    · obtain ⟨_, hzx_le, _⟩ := hRD
      have : (w' : ℝ) ≤ (z : ℝ) := by rw [← hw'_abs]; exact hw'_bnd_z
      linarith
    · by_contra h_w_gt
      push Not at h_w_gt
      have hz_min := hRU.2.2
      have hw'F₂ : w' ∈ F₂ := hsub' _ hw'F₁
      have hw'_ge_z : (z : ℝ) ≤ (w' : ℝ) := hz_min w' hw'F₂ h_w_gt.le
      have hw'_le_z : (w' : ℝ) ≤ (z : ℝ) := by rw [← hw'_abs]; exact hw'_bnd_z
      have hw'_eq_z : (w' : ℝ) = (z : ℝ) := le_antisymm hw'_le_z hw'_ge_z
      have hxne : x ≠ (z : ℝ) := by
        intro hxz_eq
        rw [← hxz_eq] at hw'_eq_z
        linarith
      have hz_full : Rounds F₂ .ToOdd x z := ⟨hzF₂, Or.inr hRU, hz_odd_imp⟩
      have hzF₁ : z ∈ F₁ := by
        rw [show z = w' from Subtype.ext hw'_eq_z.symm]; exact hw'F₁
      exact (Rounds.toOdd_notMem_of_extend_subset hsub hp_F₂ hz_full hxne) hzF₁
  refine ⟨hw'F₁, ?_, ?_, ?_⟩
  · rw [hw'_abs, hx_abs]; exact hw'_le_x
  · exact mul_nonneg hw'_nn hx_pos.le
  · intro v hvF₁ hv_bnd_x hv_sign_x
    rw [hx_abs] at hv_bnd_x
    have hv_nn : 0 ≤ (v : ℝ) := by nlinarith [hv_sign_x]
    have hv_abs : |(v : ℝ)| = (v : ℝ) := abs_of_nonneg hv_nn
    have hv_le_z : (v : ℝ) ≤ (z : ℝ) := by
      rcases hz_adj with hRD | hRU
      · obtain ⟨_, _, hz_F₂_max⟩ := hRD
        have hvF₂ : v ∈ F₂ := hsub' _ hvF₁
        have h1 : (v : ℝ) ≤ x := by rw [← hv_abs]; exact hv_bnd_x
        exact hz_F₂_max v hvF₂ h1
      · obtain ⟨_, hxz, _⟩ := hRU
        have h1 : (v : ℝ) ≤ x := by rw [← hv_abs]; exact hv_bnd_x
        linarith
    have hv_bnd_z : |(v : ℝ)| ≤ |(z : ℝ)| := by rw [hv_abs, hz_abs]; exact hv_le_z
    have hv_z_sign : 0 ≤ (v : ℝ) * (z : ℝ) := mul_nonneg hv_nn hz_nn
    exact hw'_max v hvF₁ hv_bnd_z hv_z_sign

/-- **rnd-RTO-RTZ** (Fig. 9), paper-aligned form. The hypothesis
`hsub` encodes the paper's full containment
`A(p₁ + 1, exp₁ − 1, next_{p₁,exp₁}(b₁)) ⊆ A(p₂, exp₂, b₂)`,
where the `next` bound forces F₂'s grid to extend strictly past `b₁` (this
rules out the degenerate `F₂.p = 1` configurations that fail the theorem
under a weaker `F₁.extend 1 ⊆ F₂` containment).

The auxiliary `2 ≤ F₂.p` needed for `notMem_of_extend_subset` is derived
internally via `hp_F₂_or_F₁_trivial`: either the precision-2 witness
`3·2^k` (for an appropriate `k`) lies in `(F₁.extend 1).withBound F₁.boundAfterNext`
forcing `F₂.p ≥ 2`, or `F₁` is trivial in which case the conclusion holds
directly via `Rounds.toZero_of_trivial`. -/
theorem rndRTO_RTZ {F₁ F₂ : AbstractFormat}
    (hsub : ((F₁.extend 1).withBound F₁.boundAfterNext F₁.boundAfterNext_nn) ⊆ F₂)
    {x : ℝ}
    {z w' : Dyadic}
    (hz : Rounds F₂ .ToOdd x z)
    (hw : Rounds F₁ .ToZero (z : ℝ) w') :
    Rounds F₁ .ToZero x w' := by
  rcases hp_F₂_or_F₁_trivial hsub with hp_F₂ | hF₁_triv
  swap
  · -- F₁ trivial: conclusion holds directly from `w' ∈ F₁`.
    exact Rounds.toZero_of_trivial hF₁_triv hw.1
  -- Derive the weaker `F₁.extend 1 ⊆ F₂` form for the existing proof body.
  have hsub_old : F₁.extend 1 ⊆ F₂ := extend_one_subset_of_paper_subset hsub
  have hF₁_sub_ext : F₁ ⊆ F₁.extend 1 := self_subset_extend F₁ 1
  have hsub' : F₁ ⊆ F₂ := fun y hy => hsub_old _ (hF₁_sub_ext _ hy)
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · -- x < 0: negate, apply _pos', negate back.
    have hx_pos' : 0 < (-x) := by linarith
    have hz' : Rounds F₂ .ToOdd (-x) (-z) := Rounds.neg hz trivial
    have hw' : Rounds F₁ .ToZero ((-z : Dyadic) : ℝ) (-w') := by
      have h := Rounds.neg hw trivial
      have hcoe : ((-z : Dyadic) : ℝ) = -(z : ℝ) := by push_cast; rfl
      rw [hcoe]; exact h
    have h_result := rndRTO_RTZ_pos hsub_old hp_F₂ hx_pos' hz' hw'
    have hfinal : Rounds F₁ .ToZero (-(-x)) (-(-w')) := Rounds.neg h_result trivial
    rwa [neg_neg, neg_neg] at hfinal
  · -- x = 0: forces z = 0 and w' = 0.
    subst hx_zero
    have hz_zero : z = 0 := Rounds.toOdd_eq_zero_of_zero hz
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
    exact rndRTO_RTZ_pos hsub_old hp_F₂ hx_pos hz hw

/-- **rnd-RTO-RAZ** (Fig. 9), paper-aligned form, positive case `0 < x`.
Symmetric to `rndRTO_RTZ_pos` but for round-away-from-zero. The key Lemma 5.3
application happens in the *ToNegative* (RTN) case of `z` rather than ToPositive (RTP). -/
private theorem rndRTO_RAZ_pos {F₁ F₂ : AbstractFormat}
    (hsub : F₁.extend 1 ⊆ F₂)
    (hp_F₂ : 2 ≤ F₂.p)
    {x : ℝ} (hx_pos : 0 < x)
    {z w' : Dyadic}
    (hz : Rounds F₂ .ToOdd x z)
    (hw : Rounds F₁ .AwayZero (z : ℝ) w') :
    Rounds F₁ .AwayZero x w' := by
  have hF₁_sub_ext : F₁ ⊆ F₁.extend 1 := self_subset_extend F₁ 1
  have hsub' : F₁ ⊆ F₂ := fun y hy => hsub _ (hF₁_sub_ext _ hy)
  have hz_nn : 0 ≤ (z : ℝ) := Rounds.toOdd_nonneg_of_nn hx_pos.le hz
  obtain ⟨hzF₂, hz_adj, hz_odd_imp⟩ := hz
  obtain ⟨hw'F₁, hw'_bnd_z, hw'_sign_z, hw'_min⟩ := hw
  have hx_abs : |x| = x := abs_of_pos hx_pos
  have hz_abs : |(z : ℝ)| = (z : ℝ) := abs_of_nonneg hz_nn
  rw [hz_abs] at hw'_bnd_z
  -- z > 0 (RTO of positive x cannot be 0)
  have hz_pos : 0 < (z : ℝ) := by
    rcases eq_or_ne ((z : ℝ)) x with hzx | hzx
    · rw [hzx]; exact hx_pos
    · have hxne : x ≠ (z : ℝ) := fun h => hzx h.symm
      have hodd : IsOdd F₂ z := hz_odd_imp hxne
      have hz_ne : z ≠ 0 := hodd.ne_zero
      have : (z : ℝ) ≠ 0 := fun h => hz_ne (Subtype.ext (by rw [h]; rfl))
      exact lt_of_le_of_ne hz_nn (Ne.symm this)
  -- w' ≥ z > 0
  have hw'_pos : 0 < (w' : ℝ) := by
    have h1 : (z : ℝ) ≤ |(w' : ℝ)| := hw'_bnd_z
    have hw'_nn : 0 ≤ (w' : ℝ) := by nlinarith [hw'_sign_z]
    have hw'_abs : |(w' : ℝ)| = (w' : ℝ) := abs_of_nonneg hw'_nn
    rw [hw'_abs] at h1
    linarith
  have hw'_nn : 0 ≤ (w' : ℝ) := le_of_lt hw'_pos
  have hw'_abs : |(w' : ℝ)| = (w' : ℝ) := abs_of_nonneg hw'_nn
  -- |w'| ≥ |x| via the contradiction in the ToNegative (RTN) branch using
  -- `notMem_of_extend_subset` instead of going through `hgt`.
  have hx_le_w' : x ≤ (w' : ℝ) := by
    rcases hz_adj with hRD | hRU
    · by_contra h_w_lt
      push Not at h_w_lt
      have hz_max := hRD.2.2
      have hw'F₂ : w' ∈ F₂ := hsub' _ hw'F₁
      have hw'_le_z : (w' : ℝ) ≤ (z : ℝ) := hz_max w' hw'F₂ h_w_lt.le
      have hz_le_w' : (z : ℝ) ≤ (w' : ℝ) := by
        have := hw'_bnd_z; rw [hw'_abs] at this; exact this
      have hw'_eq_z : (w' : ℝ) = (z : ℝ) := le_antisymm hw'_le_z hz_le_w'
      have hxne : x ≠ (z : ℝ) := by
        intro hxz_eq
        rw [← hxz_eq] at hw'_eq_z
        linarith
      have hz_full : Rounds F₂ .ToOdd x z := ⟨hzF₂, Or.inl hRD, hz_odd_imp⟩
      have hzF₁ : z ∈ F₁ := by
        rw [show z = w' from Subtype.ext hw'_eq_z.symm]; exact hw'F₁
      exact (Rounds.toOdd_notMem_of_extend_subset hsub hp_F₂ hz_full hxne) hzF₁
    · have hxz := hRU.2.1
      have hz_le_w' : (z : ℝ) ≤ (w' : ℝ) := by
        have := hw'_bnd_z; rw [hw'_abs] at this; exact this
      linarith
  refine ⟨hw'F₁, ?_, ?_, ?_⟩
  · rw [hx_abs, hw'_abs]; exact hx_le_w'
  · exact mul_nonneg hw'_nn hx_pos.le
  · intro v hvF₁ hv_bnd_x hv_sign_x
    rw [hx_abs] at hv_bnd_x
    have hv_nn : 0 ≤ (v : ℝ) := by nlinarith [hv_sign_x]
    have hv_abs : |(v : ℝ)| = (v : ℝ) := abs_of_nonneg hv_nn
    have hx_le_v : x ≤ (v : ℝ) := by rw [← hv_abs]; exact hv_bnd_x
    have hz_le_v : (z : ℝ) ≤ (v : ℝ) := by
      rcases hz_adj with hRD | hRU
      · have hzx := hRD.2.1
        linarith
      · have hz_min := hRU.2.2
        have hvF₂ : v ∈ F₂ := hsub' _ hvF₁
        exact hz_min v hvF₂ hx_le_v
    have hv_bnd_z : |(z : ℝ)| ≤ |(v : ℝ)| := by rw [hz_abs, hv_abs]; exact hz_le_v
    have hv_z_sign : 0 ≤ (v : ℝ) * (z : ℝ) := mul_nonneg hv_nn hz_nn
    exact hw'_min v hvF₁ hv_bnd_z hv_z_sign

/-- **rnd-RTO-RAZ** (Fig. 9), paper-aligned form. The hypothesis `hsub`
encodes the same paper containment used by `rndRTO_RTZ`
(`A(p₁ + 1, exp₁ − 1, next_{p₁,exp₁}(b₁)) ⊆ A(p₂, exp₂, b₂)`); for RAZ the
paper actually uses just `b₁` rather than `next(b₁)`, but accepting the
stronger paper-RTZ form costs nothing and keeps the signature uniform.
The auxiliary `2 ≤ F₂.p` is derived internally via `hp_F₂_or_F₁_trivial`. -/
theorem rndRTO_RAZ {F₁ F₂ : AbstractFormat}
    (hsub : ((F₁.extend 1).withBound F₁.boundAfterNext F₁.boundAfterNext_nn) ⊆ F₂)
    {x : ℝ}
    {z w' : Dyadic}
    (hz : Rounds F₂ .ToOdd x z)
    (hw : Rounds F₁ .AwayZero (z : ℝ) w') :
    Rounds F₁ .AwayZero x w' := by
  rcases hp_F₂_or_F₁_trivial hsub with hp_F₂ | hF₁_triv
  swap
  · -- F₁ trivial: x = 0 is forced and conclusion is Rounds F₁ .AwayZero 0 0.
    exact Rounds.awayZero_of_trivial hF₁_triv hz hw
  -- Derive the weaker `F₁.extend 1 ⊆ F₂` form for the existing _pos body.
  have hsub_old : F₁.extend 1 ⊆ F₂ := extend_one_subset_of_paper_subset hsub
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · -- x < 0: negate, apply _pos, negate back
    have hx_pos' : 0 < (-x) := by linarith
    have hz' : Rounds F₂ .ToOdd (-x) (-z) := Rounds.neg hz trivial
    have hw' : Rounds F₁ .AwayZero ((-z : Dyadic) : ℝ) (-w') := by
      have h := Rounds.neg hw trivial
      have hcoe : ((-z : Dyadic) : ℝ) = -(z : ℝ) := by push_cast; rfl
      rw [hcoe]; exact h
    have h_result := rndRTO_RAZ_pos hsub_old hp_F₂ hx_pos' hz' hw'
    have hfinal : Rounds F₁ .AwayZero (-(-x)) (-(-w')) := Rounds.neg h_result trivial
    rwa [neg_neg, neg_neg] at hfinal
  · -- x = 0: pin z = 0 = w'
    subst hx_zero
    have hz_zero : z = 0 := Rounds.toOdd_eq_zero_of_zero hz
    rw [hz_zero] at hw
    obtain ⟨hw'F₁, _, _, hw'_min⟩ := hw
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
    exact rndRTO_RAZ_pos hsub_old hp_F₂ hx_pos hz hw

/-- **rnd-RTO-RTP** (round-to-odd then round-to-+∞). Reduces to `rndRTO_RAZ`
when `x ≥ 0` and to `rndRTO_RTZ` when `x ≤ 0`, via the sign-bridge lemmas. -/
theorem rndRTO_RTP {F₁ F₂ : AbstractFormat}
    (hsub : ((F₁.extend 1).withBound F₁.boundAfterNext F₁.boundAfterNext_nn) ⊆ F₂)
    {x : ℝ} {z w : Dyadic}
    (hz : Rounds F₂ .ToOdd x z) (hw : Rounds F₁ .ToPositive (z : ℝ) w) :
    Rounds F₁ .ToPositive x w := by
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · have hx_le : x ≤ 0 := le_of_lt hx_neg
    have hz_le_0 : (z : ℝ) ≤ 0 := Rounds.toOdd_nonpos_of_nonpos hx_le hz
    have hw_RTZ : Rounds F₁ .ToZero (z : ℝ) w :=
      (Rounds.toPositive_iff_toZero_of_nonpos hz_le_0).mp hw
    have hresult : Rounds F₁ .ToZero x w := rndRTO_RTZ hsub hz hw_RTZ
    exact (Rounds.toPositive_iff_toZero_of_nonpos hx_le).mpr hresult
  · have hx_le : x ≤ 0 := le_of_eq hx_zero
    have hz_le_0 : (z : ℝ) ≤ 0 := Rounds.toOdd_nonpos_of_nonpos hx_le hz
    have hw_RTZ : Rounds F₁ .ToZero (z : ℝ) w :=
      (Rounds.toPositive_iff_toZero_of_nonpos hz_le_0).mp hw
    have hresult : Rounds F₁ .ToZero x w := rndRTO_RTZ hsub hz hw_RTZ
    exact (Rounds.toPositive_iff_toZero_of_nonpos hx_le).mpr hresult
  · have hx_nn : 0 ≤ x := le_of_lt hx_pos
    have hz_nn : 0 ≤ (z : ℝ) := Rounds.toOdd_nonneg_of_nn hx_pos.le hz
    have hw_RAZ : Rounds F₁ .AwayZero (z : ℝ) w :=
      (Rounds.toPositive_iff_awayZero_of_nn hz_nn).mp hw
    have hresult : Rounds F₁ .AwayZero x w := rndRTO_RAZ hsub hz hw_RAZ
    exact (Rounds.toPositive_iff_awayZero_of_nn hx_nn).mpr hresult

/-- **rnd-RTO-RTN** (round-to-odd then round-to-−∞). Reduces to `rndRTO_RTZ`
when `x ≥ 0` and to `rndRTO_RAZ` when `x ≤ 0`, via the sign-bridge lemmas. -/
theorem rndRTO_RTN {F₁ F₂ : AbstractFormat}
    (hsub : ((F₁.extend 1).withBound F₁.boundAfterNext F₁.boundAfterNext_nn) ⊆ F₂)
    {x : ℝ} {z w : Dyadic}
    (hz : Rounds F₂ .ToOdd x z) (hw : Rounds F₁ .ToNegative (z : ℝ) w) :
    Rounds F₁ .ToNegative x w := by
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · have hx_le : x ≤ 0 := le_of_lt hx_neg
    have hz_le_0 : (z : ℝ) ≤ 0 := Rounds.toOdd_nonpos_of_nonpos hx_le hz
    have hw_RAZ : Rounds F₁ .AwayZero (z : ℝ) w :=
      (Rounds.toNegative_iff_awayZero_of_nonpos hz_le_0).mp hw
    have hresult : Rounds F₁ .AwayZero x w := rndRTO_RAZ hsub hz hw_RAZ
    exact (Rounds.toNegative_iff_awayZero_of_nonpos hx_le).mpr hresult
  · have hx_nn : 0 ≤ x := le_of_eq hx_zero.symm
    have hz_nn : 0 ≤ (z : ℝ) := Rounds.toOdd_nonneg_of_nn hx_nn hz
    have hw_RTZ : Rounds F₁ .ToZero (z : ℝ) w := (Rounds.toNegative_iff_toZero_of_nn hz_nn).mp hw
    have hresult : Rounds F₁ .ToZero x w := rndRTO_RTZ hsub hz hw_RTZ
    exact (Rounds.toNegative_iff_toZero_of_nn hx_nn).mpr hresult
  · have hx_nn : 0 ≤ x := le_of_lt hx_pos
    have hz_nn : 0 ≤ (z : ℝ) := Rounds.toOdd_nonneg_of_nn hx_pos.le hz
    have hw_RTZ : Rounds F₁ .ToZero (z : ℝ) w := (Rounds.toNegative_iff_toZero_of_nn hz_nn).mp hw
    have hresult : Rounds F₁ .ToZero x w := rndRTO_RTZ hsub hz hw_RTZ
    exact (Rounds.toNegative_iff_toZero_of_nn hx_nn).mpr hresult

/-- Helper for tie-break: from `|x - w'| = |x - z'|` with `w' ≠ z'`, derive
`x = (w' + z') / 2`. -/
private theorem Rounds.nearest_midpoint_of_tie {x : ℝ} {w' z' : Dyadic}
    (h_ne : z' ≠ w') (h_tie : |x - (w' : ℝ)| = |x - (z' : ℝ)|) :
    x = ((w' : ℝ) + (z' : ℝ)) / 2 := by
  rcases abs_eq_abs.mp h_tie with h1 | h1
  · -- x - w' = x - z' ⇒ w' = z', contradicting h_ne
    have : (w' : ℝ) = (z' : ℝ) := by linarith
    exact absurd (Subtype.ext this).symm h_ne
  · -- x - w' = -(x - z') ⇒ 2x = w' + z'
    linarith

/-- The closeness transfer step for `rndRTO_RN`: given that `z = RTO F₂ x`
sits outside `F₁.extend 1` (Lemma 5.3) and `w' = RN F₁ z`, every F₁-adjacent
`z'` to `x` satisfies `|x - w'| ≤ |x - z'|`. The argument uses the midpoint
`m = (w' + z') / 2` (in F₂ via `midpoint_F₁_in_F₂_of_F_adjacent`, in
`F₁.extend 1` via `midpoint_in_F₁_extend_one_of_F_adjacent`), shows
`z ≠ m`, and concludes `x` lies on `w'`'s side of `m`. -/
private lemma rndRTO_RN_close_transfer {F₁ F₂ : AbstractFormat}
    (hsub_paper : ((F₁.extend 2).withBound (F₁.extend 1).boundAfterNext
                    (F₁.extend 1).boundAfterNext_nn) ⊆ F₂)
    (hsub' : F₁ ⊆ F₂)
    (hF₁_sub_ext1 : F₁ ⊆ F₁.extend 1)
    {x : ℝ} {z w' : Dyadic}
    (hz_adj : Rounds F₂ .ToNegative x z ∨ Rounds F₂ .ToPositive x z)
    (hw'F₁ : w' ∈ F₁)
    (h_adj_x : Rounds F₁ .ToNegative x w' ∨ Rounds F₁ .ToPositive x w')
    (hw_close_inner : ∀ z' : Dyadic, z' ∈ F₁ →
        (Rounds F₁ .ToNegative ((z : Dyadic) : ℝ) z'
          ∨ Rounds F₁ .ToPositive ((z : Dyadic) : ℝ) z') →
        |((z : Dyadic) : ℝ) - ((w' : Dyadic) : ℝ)| ≤
            |((z : Dyadic) : ℝ) - ((z' : Dyadic) : ℝ)|)
    (hz_not_F₁_ext1 : z ∉ F₁.extend 1) :
    ∀ z' : Dyadic, z' ∈ F₁ →
      (Rounds F₁ .ToNegative x z' ∨ Rounds F₁ .ToPositive x z') →
      |x - ((w' : Dyadic) : ℝ)| ≤ |x - ((z' : Dyadic) : ℝ)| := by
  intro z' hz'F₁ hz'_adj
  by_cases h_eq : ((z' : Dyadic) : ℝ) = ((w' : Dyadic) : ℝ)
  · rw [h_eq]
  · have h_w_ne_z' : ((w' : Dyadic) : ℝ) ≠ ((z' : Dyadic) : ℝ) := fun h => h_eq h.symm
    have h_z_ne_w'_real : ((z : Dyadic) : ℝ) ≠ ((w' : Dyadic) : ℝ) := by
      intro h
      apply hz_not_F₁_ext1
      have hzw : z = w' := Subtype.ext h
      rw [hzw]; exact hF₁_sub_ext1 _ hw'F₁
    have h_z_ne_z'_real : ((z : Dyadic) : ℝ) ≠ ((z' : Dyadic) : ℝ) := by
      intro h
      apply hz_not_F₁_ext1
      have hzz' : z = z' := Subtype.ext h
      rw [hzz']; exact hF₁_sub_ext1 _ hz'F₁
    have hw'F₂ : w' ∈ F₂ := hsub' _ hw'F₁
    have hz'F₂ : z' ∈ F₂ := hsub' _ hz'F₁
    rcases lt_or_gt_of_ne h_w_ne_z' with h_w_lt_z | h_z_lt_w
    · have hwRD : Rounds F₁ .ToNegative x w' := by
        rcases h_adj_x with hwRD | hwRU
        · exact hwRD
        · exfalso
          rcases hz'_adj with hzRD | hzRU
          · linarith [hwRU.2.1, hzRD.2.1]
          · have h1 : ((w' : Dyadic) : ℝ) ≤ ((z' : Dyadic) : ℝ) :=
              hwRU.2.2 z' hz'F₁ hzRU.2.1
            have h2 : ((z' : Dyadic) : ℝ) ≤ ((w' : Dyadic) : ℝ) :=
              hzRU.2.2 w' hw'F₁ hwRU.2.1
            exact h_w_ne_z' (le_antisymm h1 h2)
      have hzRU : Rounds F₁ .ToPositive x z' := by
        rcases hz'_adj with hzRD | hzRU
        · exfalso
          have h1 : ((w' : Dyadic) : ℝ) ≤ ((z' : Dyadic) : ℝ) :=
            hzRD.2.2 w' hw'F₁ hwRD.2.1
          have h2 : ((z' : Dyadic) : ℝ) ≤ ((w' : Dyadic) : ℝ) :=
            hwRD.2.2 z' hz'F₁ hzRD.2.1
          exact h_w_ne_z' (le_antisymm h1 h2)
        · exact hzRU
      have h_w_le_x : ((w' : Dyadic) : ℝ) ≤ x := hwRD.2.1
      have h_x_le_z : x ≤ ((z' : Dyadic) : ℝ) := hzRU.2.1
      have h_F_adj : ∀ y : Dyadic, y ∈ F₁ →
          ((w' : Dyadic) : ℝ) < ((y : Dyadic) : ℝ) →
          ((z' : Dyadic) : ℝ) ≤ ((y : Dyadic) : ℝ) :=
        F_adjacent_of_RN_round_pair (Or.inl hwRD) (Or.inr hzRU) h_w_le_x h_x_le_z
      have h_mid_F₂ : Dyadic.midpoint w' z' ∈ F₂ :=
        midpoint_F₁_in_F₂_of_F_adjacent hsub_paper hw'F₁ hz'F₁
          h_w_lt_z h_F_adj
      have h_mid_F₁_ext1 : Dyadic.midpoint w' z' ∈ F₁.extend 1 :=
        midpoint_in_F₁_extend_one_of_F_adjacent hw'F₁ hz'F₁
          h_w_lt_z h_F_adj
      have h_mid_real : ((Dyadic.midpoint w' z' : Dyadic) : ℝ) =
          (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2 := Dyadic.coe_midpoint w' z'
      have h_z_ne_m : ((z : Dyadic) : ℝ) ≠ ((Dyadic.midpoint w' z' : Dyadic) : ℝ) := by
        intro h_eq_m
        apply hz_not_F₁_ext1
        have : z = Dyadic.midpoint w' z' := Subtype.ext h_eq_m
        rw [this]; exact h_mid_F₁_ext1
      have h_w_le_z_F : ((w' : Dyadic) : ℝ) ≤ ((z : Dyadic) : ℝ) := by
        rcases hz_adj with hzRD' | hzRU'
        · exact hzRD'.2.2 w' hw'F₂ h_w_le_x
        · linarith [hzRU'.2.1]
      have h_z_le_z'_F : ((z : Dyadic) : ℝ) ≤ ((z' : Dyadic) : ℝ) := by
        rcases hz_adj with hzRD' | hzRU'
        · linarith [hzRD'.2.1]
        · exact hzRU'.2.2 z' hz'F₂ h_x_le_z
      have h_w_lt_z_F : ((w' : Dyadic) : ℝ) < ((z : Dyadic) : ℝ) :=
        lt_of_le_of_ne h_w_le_z_F (Ne.symm h_z_ne_w'_real)
      have h_z_lt_z' : ((z : Dyadic) : ℝ) < ((z' : Dyadic) : ℝ) :=
        lt_of_le_of_ne h_z_le_z'_F h_z_ne_z'_real
      have hz_RU_z' : Rounds F₁ .ToPositive z z' := by
        refine ⟨hz'F₁, le_of_lt h_z_lt_z', ?_⟩
        intro y hyF₁ h_z_le_y
        have h_w_lt_y : ((w' : Dyadic) : ℝ) < ((y : Dyadic) : ℝ) := by linarith
        exact h_F_adj y hyF₁ h_w_lt_y
      have h_z_close : |((z : Dyadic) : ℝ) - ((w' : Dyadic) : ℝ)|
          ≤ |((z : Dyadic) : ℝ) - ((z' : Dyadic) : ℝ)| :=
        hw_close_inner z' hz'F₁ (Or.inr hz_RU_z')
      have h_z_w_pos : 0 < ((z : Dyadic) : ℝ) - ((w' : Dyadic) : ℝ) := by linarith
      have h_z_z_neg : ((z : Dyadic) : ℝ) - ((z' : Dyadic) : ℝ) < 0 := by linarith
      rw [abs_of_pos h_z_w_pos, abs_of_neg h_z_z_neg] at h_z_close
      have h_z_le_m : ((z : Dyadic) : ℝ)
          ≤ (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2 := by linarith
      have h_z_lt_m : ((z : Dyadic) : ℝ)
          < (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2 := by
        have : ((z : Dyadic) : ℝ) ≠ (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2 := by
          rw [← h_mid_real]; exact h_z_ne_m
        exact lt_of_le_of_ne h_z_le_m this
      have h_x_le_m : x ≤ (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2 := by
        rcases hz_adj with hzRD' | hzRU'
        · by_contra h_x_gt
          push Not at h_x_gt
          have h_m_le_x : (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2 ≤ x :=
            le_of_lt h_x_gt
          have h_m_le_x' : ((Dyadic.midpoint w' z' : Dyadic) : ℝ) ≤ x := by
            rw [h_mid_real]; exact h_m_le_x
          have h_m_le_z : ((Dyadic.midpoint w' z' : Dyadic) : ℝ) ≤ ((z : Dyadic) : ℝ) :=
            hzRD'.2.2 (Dyadic.midpoint w' z') h_mid_F₂ h_m_le_x'
          rw [h_mid_real] at h_m_le_z
          linarith
        · linarith [hzRU'.2.1]
      have h_x_w_pos : 0 ≤ x - ((w' : Dyadic) : ℝ) := by linarith
      have h_x_z_nonpos : x - ((z' : Dyadic) : ℝ) ≤ 0 := by linarith
      rw [abs_of_nonneg h_x_w_pos, abs_of_nonpos h_x_z_nonpos]
      linarith
    · have hwRU : Rounds F₁ .ToPositive x w' := by
        rcases h_adj_x with hwRD | hwRU
        · exfalso
          rcases hz'_adj with hzRD | hzRU
          · have h1 : ((w' : Dyadic) : ℝ) ≤ ((z' : Dyadic) : ℝ) :=
              hzRD.2.2 w' hw'F₁ hwRD.2.1
            have h2 : ((z' : Dyadic) : ℝ) ≤ ((w' : Dyadic) : ℝ) :=
              hwRD.2.2 z' hz'F₁ hzRD.2.1
            exact h_w_ne_z' (le_antisymm h1 h2)
          · linarith [hwRD.2.1, hzRU.2.1]
        · exact hwRU
      have hzRD : Rounds F₁ .ToNegative x z' := by
        rcases hz'_adj with hzRD | hzRU
        · exact hzRD
        · exfalso
          have h1 : ((w' : Dyadic) : ℝ) ≤ ((z' : Dyadic) : ℝ) :=
            hwRU.2.2 z' hz'F₁ hzRU.2.1
          have h2 : ((z' : Dyadic) : ℝ) ≤ ((w' : Dyadic) : ℝ) :=
            hzRU.2.2 w' hw'F₁ hwRU.2.1
          exact h_w_ne_z' (le_antisymm h1 h2)
      have h_x_le_w : x ≤ ((w' : Dyadic) : ℝ) := hwRU.2.1
      have h_z_le_x : ((z' : Dyadic) : ℝ) ≤ x := hzRD.2.1
      have h_F_adj : ∀ y : Dyadic, y ∈ F₁ →
          ((z' : Dyadic) : ℝ) < ((y : Dyadic) : ℝ) →
          ((w' : Dyadic) : ℝ) ≤ ((y : Dyadic) : ℝ) :=
        F_adjacent_of_RN_round_pair (Or.inl hzRD) (Or.inr hwRU) h_z_le_x h_x_le_w
      have h_mid_F₂_swap : Dyadic.midpoint z' w' ∈ F₂ :=
        midpoint_F₁_in_F₂_of_F_adjacent hsub_paper hz'F₁ hw'F₁
          h_z_lt_w h_F_adj
      have h_mid_F₁_ext1_swap : Dyadic.midpoint z' w' ∈ F₁.extend 1 :=
        midpoint_in_F₁_extend_one_of_F_adjacent hz'F₁ hw'F₁
          h_z_lt_w h_F_adj
      have h_mid_swap_eq : Dyadic.midpoint z' w' = Dyadic.midpoint w' z' :=
        Dyadic.midpoint_comm z' w'
      have h_mid_F₂ : Dyadic.midpoint w' z' ∈ F₂ := h_mid_swap_eq ▸ h_mid_F₂_swap
      have h_mid_F₁_ext1 : Dyadic.midpoint w' z' ∈ F₁.extend 1 :=
        h_mid_swap_eq ▸ h_mid_F₁_ext1_swap
      have h_mid_real : ((Dyadic.midpoint w' z' : Dyadic) : ℝ) =
          (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2 := Dyadic.coe_midpoint w' z'
      have h_z_ne_m : ((z : Dyadic) : ℝ) ≠ ((Dyadic.midpoint w' z' : Dyadic) : ℝ) := by
        intro h_eq_m
        apply hz_not_F₁_ext1
        have : z = Dyadic.midpoint w' z' := Subtype.ext h_eq_m
        rw [this]; exact h_mid_F₁_ext1
      have h_z_le_w_F : ((z : Dyadic) : ℝ) ≤ ((w' : Dyadic) : ℝ) := by
        rcases hz_adj with hzRD' | hzRU'
        · linarith [hzRD'.2.1]
        · exact hzRU'.2.2 w' hw'F₂ h_x_le_w
      have h_z'_le_z_F : ((z' : Dyadic) : ℝ) ≤ ((z : Dyadic) : ℝ) := by
        rcases hz_adj with hzRD' | hzRU'
        · exact hzRD'.2.2 z' hz'F₂ h_z_le_x
        · linarith [hzRU'.2.1]
      have h_z_lt_w_F : ((z : Dyadic) : ℝ) < ((w' : Dyadic) : ℝ) :=
        lt_of_le_of_ne h_z_le_w_F h_z_ne_w'_real
      have h_z'_lt_z : ((z' : Dyadic) : ℝ) < ((z : Dyadic) : ℝ) :=
        lt_of_le_of_ne h_z'_le_z_F (Ne.symm h_z_ne_z'_real)
      have hz_RD_z' : Rounds F₁ .ToNegative z z' := by
        refine ⟨hz'F₁, le_of_lt h_z'_lt_z, ?_⟩
        intro y hyF₁ h_y_le_z
        by_contra h_lt
        push Not at h_lt
        have h_w_le_y := h_F_adj y hyF₁ h_lt
        linarith
      have h_z_close : |((z : Dyadic) : ℝ) - ((w' : Dyadic) : ℝ)|
          ≤ |((z : Dyadic) : ℝ) - ((z' : Dyadic) : ℝ)| :=
        hw_close_inner z' hz'F₁ (Or.inl hz_RD_z')
      have h_z_w_neg : ((z : Dyadic) : ℝ) - ((w' : Dyadic) : ℝ) < 0 := by linarith
      have h_z_z_pos : 0 < ((z : Dyadic) : ℝ) - ((z' : Dyadic) : ℝ) := by linarith
      rw [abs_of_neg h_z_w_neg, abs_of_pos h_z_z_pos] at h_z_close
      have h_m_le_z : (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2
          ≤ ((z : Dyadic) : ℝ) := by linarith
      have h_m_lt_z : (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2
          < ((z : Dyadic) : ℝ) := by
        have : (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2 ≠ ((z : Dyadic) : ℝ) := by
          intro h_eq2
          rw [← h_mid_real] at h_eq2
          exact h_z_ne_m h_eq2.symm
        exact lt_of_le_of_ne h_m_le_z this
      have h_m_le_x : (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2 ≤ x := by
        rcases hz_adj with hzRD' | hzRU'
        · linarith [hzRD'.2.1]
        · by_contra h_x_lt
          push Not at h_x_lt
          have h_x_le_m : x ≤ (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2 :=
            le_of_lt h_x_lt
          have h_x_le_m' : x ≤ ((Dyadic.midpoint w' z' : Dyadic) : ℝ) := by
            rw [h_mid_real]; exact h_x_le_m
          have h_z_le_m : ((z : Dyadic) : ℝ) ≤ ((Dyadic.midpoint w' z' : Dyadic) : ℝ) :=
            hzRU'.2.2 (Dyadic.midpoint w' z') h_mid_F₂ h_x_le_m'
          rw [h_mid_real] at h_z_le_m
          linarith
      have h_x_w_neg : x - ((w' : Dyadic) : ℝ) ≤ 0 := by linarith
      have h_x_z_pos : 0 ≤ x - ((z' : Dyadic) : ℝ) := by linarith
      rw [abs_of_nonpos h_x_w_neg, abs_of_nonneg h_x_z_pos]
      linarith

/-- The "no-tie" derivation used by the nearest-rounding branch of `rndRTO_RN`. Given
that `z = RTO F₂ x` is unrepresentable in `F₁` (`hxne` + the implicit
`z ∉ F₁` chain) and that `z'` is supposedly tied with `w'` for `x`'s
nearest-rounding in `F₁`, derive `False` via the midpoint-uniqueness
argument: the tie equation forces `x = midpoint(w', z')`, F-adjacency makes
that midpoint lie in `F₂` (via `midpoint_F₁_in_F₂_of_F_adjacent`), and
`Rounds.toOdd_unique_of_mem` then forces `z = midpoint`, so `x = z`,
contradicting `hxne`. Both RNE (with even tie-break) and RNA (with
larger-magnitude tie-break) discharge their tie-break clauses vacuously
through this lemma. -/
private lemma rndRTO_no_tie_contradiction {F₁ F₂ : AbstractFormat}
    (hsub_paper : ((F₁.extend 2).withBound (F₁.extend 1).boundAfterNext
                    (F₁.extend 1).boundAfterNext_nn) ⊆ F₂)
    {x : ℝ} {z w' z' : Dyadic}
    (hz : Rounds F₂ .ToOdd x z) (hxne : x ≠ (z : ℝ))
    (hw'F₁ : w' ∈ F₁) (hz'F₁ : z' ∈ F₁)
    (h_adj_x : Rounds F₁ .ToNegative x w' ∨ Rounds F₁ .ToPositive x w')
    (hz'_adj : Rounds F₁ .ToNegative x z' ∨ Rounds F₁ .ToPositive x z')
    (hz'_ne_w' : z' ≠ w')
    (hz'_eq_dist : |x - ((w' : Dyadic) : ℝ)| = |x - ((z' : Dyadic) : ℝ)|) :
    False := by
  have hx_mid : x = ((w' : ℝ) + (z' : ℝ)) / 2 :=
    Rounds.nearest_midpoint_of_tie hz'_ne_w' hz'_eq_dist
  have hw'_ne_z'_real : ((w' : Dyadic) : ℝ) ≠ ((z' : Dyadic) : ℝ) := by
    intro heq
    apply hz'_ne_w'
    exact Subtype.ext heq.symm
  -- F-adjacency: between w' and z' (in either order), no F₁ element strictly between.
  have h_F_adj_pair : ∀ (a b : Dyadic), a ∈ F₁ → b ∈ F₁ →
      ((a : ℝ) = (w' : ℝ) ∧ (b : ℝ) = (z' : ℝ)) ∨
        ((a : ℝ) = (z' : ℝ) ∧ (b : ℝ) = (w' : ℝ)) →
      ((a : Dyadic) : ℝ) < ((b : Dyadic) : ℝ) →
      ∀ y : Dyadic, y ∈ F₁ → ((a : Dyadic) : ℝ) < ((y : Dyadic) : ℝ) →
        ((b : Dyadic) : ℝ) ≤ ((y : Dyadic) : ℝ) := by
    intro a b haF₁ hbF₁ h_ab_eq h_ab_lt y hyF₁ h_a_lt_y
    have hx_mid' : x = ((a : ℝ) + (b : ℝ)) / 2 := by
      rcases h_ab_eq with ⟨ha_eq, hb_eq⟩ | ⟨ha_eq, hb_eq⟩
      · rw [ha_eq, hb_eq]; exact hx_mid
      · rw [ha_eq, hb_eq, hx_mid]; ring
    have h_a_lt_x : (a : ℝ) < x := by rw [hx_mid']; linarith
    have h_x_lt_b : x < (b : ℝ) := by rw [hx_mid']; linarith
    by_cases h_y_le_x : ((y : Dyadic) : ℝ) ≤ x
    · exfalso
      rcases h_ab_eq with ⟨ha_eq, _⟩ | ⟨ha_eq, _⟩
      · rcases h_adj_x with hwRD | hwRU
        · obtain ⟨_, _, hw_max⟩ := hwRD
          have h_y_le_w' : ((y : Dyadic) : ℝ) ≤ (w' : ℝ) := hw_max y hyF₁ h_y_le_x
          rw [ha_eq] at h_a_lt_y
          linarith
        · obtain ⟨_, hxw, _⟩ := hwRU
          rw [ha_eq] at h_a_lt_x
          linarith
      · rcases hz'_adj with hzRD | hzRU
        · obtain ⟨_, _, hz_max⟩ := hzRD
          have h_y_le_z' : ((y : Dyadic) : ℝ) ≤ (z' : ℝ) := hz_max y hyF₁ h_y_le_x
          rw [ha_eq] at h_a_lt_y
          linarith
        · obtain ⟨_, hxz, _⟩ := hzRU
          rw [ha_eq] at h_a_lt_x
          linarith
    · push Not at h_y_le_x
      rcases h_ab_eq with ⟨_, hb_eq⟩ | ⟨_, hb_eq⟩
      · rcases hz'_adj with hzRD | hzRU
        · obtain ⟨_, hzx_le, _⟩ := hzRD
          rw [hb_eq] at h_x_lt_b
          linarith
        · obtain ⟨_, _, hz_min⟩ := hzRU
          have h_z'_le_y : (z' : ℝ) ≤ ((y : Dyadic) : ℝ) := hz_min y hyF₁ (le_of_lt h_y_le_x)
          rw [hb_eq]; exact h_z'_le_y
      · rcases h_adj_x with hwRD | hwRU
        · obtain ⟨_, hwx_le, _⟩ := hwRD
          rw [hb_eq] at h_x_lt_b
          linarith
        · obtain ⟨_, _, hw_min⟩ := hwRU
          have h_w'_le_y : (w' : ℝ) ≤ ((y : Dyadic) : ℝ) := hw_min y hyF₁ (le_of_lt h_y_le_x)
          rw [hb_eq]; exact h_w'_le_y
  have h_mid_F₂ : Dyadic.midpoint w' z' ∈ F₂ := by
    rcases lt_or_gt_of_ne hw'_ne_z'_real with h_w_lt_z | h_z_lt_w
    · have h_adj_pair := h_F_adj_pair w' z' hw'F₁ hz'F₁
        (Or.inl ⟨rfl, rfl⟩) h_w_lt_z
      exact midpoint_F₁_in_F₂_of_F_adjacent hsub_paper hw'F₁ hz'F₁
        h_w_lt_z h_adj_pair
    · have h_mid_swap : Dyadic.midpoint w' z' = Dyadic.midpoint z' w' :=
        Dyadic.midpoint_comm w' z'
      rw [h_mid_swap]
      have h_adj_pair := h_F_adj_pair z' w' hz'F₁ hw'F₁
        (Or.inr ⟨rfl, rfl⟩) h_z_lt_w
      exact midpoint_F₁_in_F₂_of_F_adjacent hsub_paper hz'F₁ hw'F₁
        h_z_lt_w h_adj_pair
  set m := Dyadic.midpoint w' z' with hm_def
  have hm_eq : ((m : Dyadic) : ℝ) = ((w' : ℝ) + (z' : ℝ)) / 2 := by
    rw [hm_def, Dyadic.coe_midpoint]
  have hm_x : (m : ℝ) = x := by rw [hm_eq, ← hx_mid]
  have hz_eq : z = m := by
    have hz' : Rounds F₂ .ToOdd ((m : ℝ)) z := by rw [hm_x]; exact hz
    exact Rounds.toOdd_unique_of_mem h_mid_F₂ hz'
  exact hxne (by rw [hz_eq]; exact hm_x.symm)

/-- Shared core for the nearest-rounding branch of `rndRTO_RN`. Given the
paper-aligned RNE containment plus extracted hypotheses from the inner
nearest-rounding, produces the three facts needed by either tie-break:
adjacency transfer (`h_adj_x`), closeness transfer (`h_close`), and an
absence-of-tie property (`h_no_tie`). The two `tb` branches of `rndRTO_RN`
differ only in how they consume `h_no_tie` (∃→IsEven for `.ToEven`,
∀→|·|-bound for `.AwayZero`). -/
private theorem rndRTO_nearest_facts {F₁ F₂ : AbstractFormat}
    (hsub_paper : ((F₁.extend 2).withBound (F₁.extend 1).boundAfterNext
                    (F₁.extend 1).boundAfterNext_nn) ⊆ F₂)
    (hp_F₂_two : 2 ≤ F₂.p)
    {x : ℝ} {z w' : Dyadic}
    (hz : Rounds F₂ .ToOdd x z) (hxne : x ≠ (z : ℝ))
    (hw'F₁ : w' ∈ F₁)
    (hw_adj : Rounds F₁ .ToNegative ((z : Dyadic) : ℝ) w'
              ∨ Rounds F₁ .ToPositive ((z : Dyadic) : ℝ) w')
    (hw_close_inner : ∀ z' : Dyadic, z' ∈ F₁ →
        (Rounds F₁ .ToNegative ((z : Dyadic) : ℝ) z'
          ∨ Rounds F₁ .ToPositive ((z : Dyadic) : ℝ) z') →
        |((z : Dyadic) : ℝ) - ((w' : Dyadic) : ℝ)| ≤
            |((z : Dyadic) : ℝ) - ((z' : Dyadic) : ℝ)|) :
    (Rounds F₁ .ToNegative x w' ∨ Rounds F₁ .ToPositive x w') ∧
    (∀ z' : Dyadic, z' ∈ F₁ →
        (Rounds F₁ .ToNegative x z' ∨ Rounds F₁ .ToPositive x z') →
        |x - ((w' : Dyadic) : ℝ)| ≤ |x - ((z' : Dyadic) : ℝ)|) ∧
    (∀ z' : Dyadic, z' ∈ F₁ →
        (Rounds F₁ .ToNegative x z' ∨ Rounds F₁ .ToPositive x z') →
        z' ≠ w' →
        |x - ((w' : Dyadic) : ℝ)| = |x - ((z' : Dyadic) : ℝ)| → False) := by
  have hsub : F₁.extend 2 ⊆ F₂ := extend_two_subset_of_paper_RN_subset hsub_paper
  have hF₁_sub_ext1 : F₁ ⊆ F₁.extend 1 := self_subset_extend F₁ 1
  have h_ext1_sub_ext2 : F₁.extend 1 ⊆ F₁.extend 2 := extend_mono F₁ (by omega : 1 ≤ 2)
  have hsub_ext1 : F₁.extend 1 ⊆ F₂ := fun y hy => hsub _ (h_ext1_sub_ext2 _ hy)
  have hsub' : F₁ ⊆ F₂ := fun y hy => hsub_ext1 _ (hF₁_sub_ext1 _ hy)
  have hz_not_F₁ : z ∉ F₁ :=
    Rounds.toOdd_notMem_of_extend_subset hsub_ext1 hp_F₂_two hz hxne
  have hz_adj : Rounds F₂ .ToNegative x z ∨ Rounds F₂ .ToPositive x z := hz.2.1
  have hz_ne_w' : (z : ℝ) ≠ (w' : ℝ) := by
    intro h_eq
    apply hz_not_F₁
    rw [show z = w' from Subtype.ext h_eq]
    exact hw'F₁
  -- Adjacency transfer (4-way case split).
  have h_adj_x : Rounds F₁ .ToNegative x w' ∨ Rounds F₁ .ToPositive x w' := by
    rcases hz_adj with hzRD | hzRU
    · rcases hw_adj with hwRD | hwRU
      · left
        obtain ⟨_, hwz, hw_max⟩ := hwRD
        have hzx_le := hzRD.2.1
        refine ⟨hw'F₁, le_trans hwz hzx_le, ?_⟩
        intro v hvF₁ hvx
        exact hw_max v hvF₁ (hzRD.2.2 v (hsub' _ hvF₁) hvx)
      · obtain ⟨_, hzw, hw_min⟩ := hwRU
        by_cases hw'_le_x : (w' : ℝ) ≤ x
        · exfalso
          have hw_le_z : (w' : ℝ) ≤ (z : ℝ) := hzRD.2.2 w' (hsub' _ hw'F₁) hw'_le_x
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
            hzRU.2.2 w' (hsub' _ hw'F₁) hw'_le_x.le
          exact hz_ne_w' (le_antisymm hwz hw_ge_z).symm
      · right
        obtain ⟨_, hzw, hw_min⟩ := hwRU
        have hxz := hzRU.2.1
        refine ⟨hw'F₁, le_trans hxz hzw, ?_⟩
        intro v hvF₁ hxv
        exact hw_min v hvF₁ (hzRU.2.2 v (hsub' _ hvF₁) hxv)
  have hsub_double : (F₁.extend 1).extend 1 ⊆ F₂ := fun y hy =>
    extend_two_subset_of_paper_RN_subset hsub_paper y
      (extend_one_extend_one_subset_extend_two F₁ y hy)
  have hz_not_F₁_ext1 : z ∉ F₁.extend 1 :=
    Rounds.toOdd_notMem_of_extend_subset hsub_double hp_F₂_two hz hxne
  have h_close := rndRTO_RN_close_transfer hsub_paper hsub' hF₁_sub_ext1
    hz_adj hw'F₁ h_adj_x hw_close_inner hz_not_F₁_ext1
  refine ⟨h_adj_x, h_close, ?_⟩
  intro z' hz'F₁ hz'_adj hz'_ne_w' hz'_eq_dist
  exact rndRTO_no_tie_contradiction hsub_paper hz hxne hw'F₁ hz'F₁
    h_adj_x hz'_adj hz'_ne_w' hz'_eq_dist

/-- **rnd-RTO-RN** (Fig. 9), paper-aligned form for round-to-odd followed by
round-to-nearest, parameterized by the nearest-rounding tie-break `tb`.
Covers both RNE (`tb = .ToEven`) and RNA (`tb = .AwayZero`) in a single
theorem: the hypothesis `hsub` encodes the paper's
`A(p₁ + 2, exp₁ − 2, next_{p₁+1, exp₁-1}(b₁)) ⊆ A(p₂, exp₂, b₂)` containment
— uniform with the `rndRTO_RTZ` and `rndRTO_RAZ` signatures.

Proof structure:
* `hp_F₂_or_F₁_trivial_RN` discharges either `F₂.p ≥ 2` or trivial F₁.
* x = z case: direct transport of `hw`.
* x ≠ z case: extract the three shared facts (adjacency-transfer, closeness,
  no-tie) from `rndRTO_nearest_facts`, then dispatch on `tb` to consume the
  appropriate tie-break clause (∃→IsEven for RNE; ∀→|·|-bound for RNA).
  Both tie-break clauses are discharged *vacuously* because
  `rndRTO_nearest_facts` proves no tie can exist (any tied `z' ≠ w'` would
  force `x = midpoint(w', z') = z`, contradicting `z ∉ F₁`). -/
theorem rndRTO_RN {F₁ F₂ : AbstractFormat}
    (hsub : ((F₁.extend 2).withBound (F₁.extend 1).boundAfterNext
              (F₁.extend 1).boundAfterNext_nn) ⊆ F₂)
    {tb : TieBreak}
    {x : ℝ}
    {z w' : Dyadic}
    (hz : Rounds F₂ .ToOdd x z)
    (hw : Rounds F₁ (.Nearest tb) (z : ℝ) w') :
    Rounds F₁ (.Nearest tb) x w' := by
  rcases hp_F₂_or_F₁_trivial_RN hsub with hp_F₂_two | hF₁_triv
  swap
  · -- F₁ trivial: handled uniformly for any tb.
    exact Rounds.nearest_of_trivial hF₁_triv hw.1
  rcases eq_or_ne ((z : ℝ)) x with hzx | hzx
  · -- x = z: hw already has the right shape after rewriting.
    rw [hzx] at hw; exact hw
  have hxne : x ≠ (z : ℝ) := fun h => hzx h.symm
  -- Non-trivial case: destructure hw (requires cases tb), then assemble.
  cases tb with
  | ToEven =>
    obtain ⟨hw'F₁, hw_adj, hw_close_inner, _⟩ := hw
    obtain ⟨h_adj_x, h_close, h_no_tie⟩ :=
      rndRTO_nearest_facts hsub hp_F₂_two hz hxne hw'F₁ hw_adj hw_close_inner
    refine ⟨hw'F₁, h_adj_x, h_close, ?_⟩
    rintro ⟨z', hz'F₁, hz'_adj, hz'_ne_w', hz'_eq_dist⟩
    exact (h_no_tie z' hz'F₁ hz'_adj hz'_ne_w' hz'_eq_dist).elim
  | AwayZero =>
    obtain ⟨hw'F₁, hw_adj, hw_close_inner, _⟩ := hw
    obtain ⟨h_adj_x, h_close, h_no_tie⟩ :=
      rndRTO_nearest_facts hsub hp_F₂_two hz hxne hw'F₁ hw_adj hw_close_inner
    refine ⟨hw'F₁, h_adj_x, h_close, ?_⟩
    intro z' hz'F₁ hz'_adj hz'_ne_w' hz'_eq_dist
    exact (h_no_tie z' hz'F₁ hz'_adj hz'_ne_w' hz'_eq_dist).elim


/-! ## Counterexample: RN-RN double rounding can be incorrect

The seven rules in §5.2 are exhaustive — an obvious reviewer question is
"why not RNE-RNE, RNA-RNA, RTZ-RAZ, …?" For each omitted pair the answer
is the same: even when `F₁ ⊆ F₂`, there is a real `x` whose chained
two-step rounding disagrees with the direct rounding in `F₁`, and the
failure persists no matter how much we enlarge `F₂`. We formalize the
classical RNE-RNE counterexample.

### Setup

* `F₁ = 𝒜(p, e, ⊤)` with `p ≥ 2`, `e : ℤ`.
* `y_lo = 3·2^e` (odd in F₁ at numDigits 2), `y_hi = 4·2^e = 2^(e+2)`
  (even in F₁).
* `m = 7·2^(e-1)` — the midpoint of the F₁-adjacent pair `(y_lo, y_hi)`,
  living in `F₁.extend 1`.

`RNE_{F₁}(m) = y_hi` (ties broken to the even neighbor). For a witness
`x` strictly between F₂'s predecessor of `m` and `m`,
`RN_{F₂}(x) = m`, so the chain returns `y_hi` — but `x < m` is closer to
`y_lo` in F₁, so `RN_{F₁}(x)` directly returns `y_lo`. -/

private def F₁_g (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ) : AbstractFormat where
  p := (p : ℕ∞)
  exp := ((e : ℤ) : WithBot ℤ)
  b := ⊤
  p_pos := by
    have : (1 : ℕ) ≤ p := by omega
    exact_mod_cast this
  not_degenerate := Or.inr WithBot.coe_ne_bot
  b_nn := le_top

private noncomputable def y_lo_g (e : ℤ) : Dyadic := Dyadic.ofIntZpow 3 e
private noncomputable def y_hi_g (e : ℤ) : Dyadic := Dyadic.ofIntZpow 1 (e + 2)

private theorem coe_y_lo_g (e : ℤ) : ((y_lo_g e : Dyadic) : ℝ) = 3 * (2 : ℝ)^e := by
  change ((Dyadic.ofIntZpow 3 e : Dyadic) : ℝ) = _
  rw [Dyadic.coe_ofIntZpow]; push_cast; ring

private theorem coe_y_hi_g (e : ℤ) :
    ((y_hi_g e : Dyadic) : ℝ) = (2 : ℝ)^(e + 2) := by
  change ((Dyadic.ofIntZpow 1 (e + 2) : Dyadic) : ℝ) = _
  rw [Dyadic.coe_ofIntZpow]; push_cast; ring

private theorem y_lo_mem_F₁_g (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ) :
    y_lo_g e ∈ F₁_g p hp_ge_2 e := by
  refine ⟨?_, ?_, trivial⟩
  · -- precisionAtMost p: take (c=3, k=e). |3| < 2^p since p ≥ 2.
    change Dyadic.precisionAtMost ((p : ℕ) : ℕ∞) (y_lo_g e)
    refine ⟨3, e, ?_, ?_⟩
    · rw [coe_y_lo_g]; push_cast; ring
    · have h_pow : (4 : ℤ) ≤ (2 : ℤ)^p :=
        calc (4 : ℤ) = (2 : ℤ)^2 := by norm_num
          _ ≤ (2 : ℤ)^p := pow_le_pow_right₀ (by norm_num) hp_ge_2
      have h_abs : |(3 : ℤ)| = 3 := by decide
      omega
  · -- quantumAtLeast e: take c=3 (i.e., 3·2^e = 3·2^e).
    change Dyadic.quantumAtLeast (((e : ℤ)) : WithBot ℤ) (y_lo_g e)
    rw [Dyadic.quantumAtLeast_coe]
    refine ⟨3, ?_⟩
    rw [coe_y_lo_g]; push_cast; ring

private theorem F₁_g_quantum (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ)
    {z : Dyadic} (hz : z ∈ F₁_g p hp_ge_2 e) :
    ∃ c : ℤ, (z : ℝ) = (c : ℝ) * (2 : ℝ)^e := hz.2.1

private noncomputable def m_g (e : ℤ) : Dyadic := Dyadic.ofIntZpow 7 (e - 1)

private theorem coe_m_g (e : ℤ) : ((m_g e : Dyadic) : ℝ) = 7 * (2 : ℝ)^(e - 1) := by
  change ((Dyadic.ofIntZpow 7 (e - 1) : Dyadic) : ℝ) = _
  rw [Dyadic.coe_ofIntZpow]; push_cast; ring

private theorem y_hi_mem_F₁_g (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ) :
    y_hi_g e ∈ F₁_g p hp_ge_2 e := by
  refine ⟨?_, ?_, trivial⟩
  · change Dyadic.precisionAtMost ((p : ℕ) : ℕ∞) (y_hi_g e)
    refine ⟨1, e + 2, ?_, ?_⟩
    · rw [coe_y_hi_g]; push_cast; ring
    · have h_pow : (2 : ℤ) ≤ (2 : ℤ)^p :=
        calc (2 : ℤ) = (2 : ℤ)^1 := by norm_num
          _ ≤ (2 : ℤ)^p := pow_le_pow_right₀ (by norm_num) (by omega : 1 ≤ p)
      have h_abs : |(1 : ℤ)| = 1 := by decide
      omega
  · change Dyadic.quantumAtLeast (((e : ℤ)) : WithBot ℤ) (y_hi_g e)
    rw [Dyadic.quantumAtLeast_coe]
    refine ⟨4, ?_⟩
    rw [coe_y_hi_g]
    -- 2^(e+2) = 4 * 2^e.
    rw [show (e + 2 : ℤ) = e + 2 from rfl,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have : (2 : ℝ)^(2 : ℤ) = 4 := by norm_num
    rw [this]; push_cast; ring

/-- `IsEven F₁ (4·2^e)` for any `p ≥ 2`. At numDigits = min p 3, the canonical
significand of `4·2^e` is even: `2 = 1·2^(e+1)` when `numDigits = 2` (p = 2),
or `4 = 1·2^e` when `numDigits = 3` (p ≥ 3). -/
private theorem isEven_F₁_g_y_hi (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ) :
    IsEven (F₁_g p hp_ge_2 e) (y_hi_g e) := by
  have h_coe : ((y_hi_g e : Dyadic) : ℝ) = (2 : ℝ)^(e + 2) := coe_y_hi_g e
  have h_2_pos : (0 : ℝ) < (2 : ℝ)^(e + 2) := zpow_pos (by norm_num) _
  have h_y_ne_real : ((y_hi_g e : Dyadic) : ℝ) ≠ 0 := by
    rw [h_coe]; exact ne_of_gt h_2_pos
  have h_log : Int.log 2 |((y_hi_g e : Dyadic) : ℝ)| = e + 2 := by
    rw [h_coe, abs_of_pos h_2_pos]
    rw [show (2 : ℝ)^(e + 2) = ((2 : ℕ) : ℝ)^(e + 2) by push_cast; rfl]
    exact Int.log_zpow (R := ℝ) (by omega : 1 < 2) (e + 2)
  -- Compute numDigits = min p 3.
  have h_nd : numDigits (F₁_g p hp_ge_2 e).p (F₁_g p hp_ge_2 e).exp
        ((y_hi_g e : Dyadic) : ℝ) = min ((p : ℕ) : ℤ) 3 := by
    unfold numDigits
    rw [if_neg h_y_ne_real]
    change (min ((p : ℕ) : ℤ) (Int.log 2 |((y_hi_g e : Dyadic) : ℝ)| - (e : ℤ) + 1)) = _
    rw [h_log]
    congr 1; ring
  -- F₁_g.p ≠ 1 since p ≥ 2.
  have h_p_ne_1 : (F₁_g p hp_ge_2 e).p ≠ (1 : ℕ∞) := by
    intro h
    have : (((p : ℕ) : ℕ∞)) = (1 : ℕ∞) := h
    have : p = 1 := by exact_mod_cast this
    omega
  right
  -- Case split on whether numDigits is 2 (p = 2) or 3 (p ≥ 3).
  rcases (lt_or_ge p 3) with hp_lt | hp_ge
  · -- p = 2 (since 2 ≤ p < 3).
    have hp_eq : p = 2 := by omega
    -- numDigits = min 2 3 = 2.
    have h_nd_toNat : (numDigits (F₁_g p hp_ge_2 e).p (F₁_g p hp_ge_2 e).exp
          ((y_hi_g e : Dyadic) : ℝ)).toNat = 2 := by
      rw [h_nd, hp_eq]
      have : min ((2 : ℕ) : ℤ) 3 = 2 := by decide
      rw [this]; rfl
    refine ⟨2, e + 1, ⟨?_, ?_, ?_⟩, ?_⟩
    · -- 4·2^e = 2·2^(e+1)
      rw [h_coe]
      rw [show (e + 2 : ℤ) = (e + 1) + 1 from by ring,
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      have : (2 : ℝ)^(1 : ℤ) = 2 := by norm_num
      rw [this]; push_cast; ring
    · -- 2^(n-1) ≤ |2|. n = 2, so 2^1 = 2 ≤ 2.
      rw [h_nd_toNat]; decide
    · -- |2| < 2^n. 2^2 = 4 > 2.
      rw [h_nd_toNat]; decide
    · rw [if_neg h_p_ne_1]; decide
  · -- p ≥ 3.
    have h_nd_toNat : (numDigits (F₁_g p hp_ge_2 e).p (F₁_g p hp_ge_2 e).exp
          ((y_hi_g e : Dyadic) : ℝ)).toNat = 3 := by
      rw [h_nd]
      have h_min : min ((p : ℕ) : ℤ) 3 = 3 := by
        have : ((p : ℕ) : ℤ) ≥ 3 := by exact_mod_cast hp_ge
        omega
      rw [h_min]; rfl
    refine ⟨4, e, ⟨?_, ?_, ?_⟩, ?_⟩
    · -- 4·2^e = 4·2^e
      rw [h_coe]
      rw [show (e + 2 : ℤ) = e + 2 from rfl,
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      have : (2 : ℝ)^(2 : ℤ) = 4 := by norm_num
      rw [this]; push_cast; ring
    · rw [h_nd_toNat]; decide
    · rw [h_nd_toNat]; decide
    · rw [if_neg h_p_ne_1]; decide

/-- F₁-faithful values of `m`: enumeration to `{y_lo, y_hi}`. -/
private theorem F₁_faithful_m_eq_g (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ)
    {z : Dyadic} (hf : IsFaithfulRound (F₁_g p hp_ge_2 e) ((m_g e : Dyadic) : ℝ) z) :
    (z : ℝ) = ((y_lo_g e : Dyadic) : ℝ) ∨ (z : ℝ) = ((y_hi_g e : Dyadic) : ℝ) := by
  have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
  have h_m_eq : ((m_g e : Dyadic) : ℝ) = (7 / 2) * (2 : ℝ)^e := by
    rw [coe_m_g]
    rw [show (e - 1 : ℤ) = e + (-1 : ℤ) by ring,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have : (2 : ℝ)^(-1 : ℤ) = 1/2 := by
      rw [show ((-1 : ℤ)) = -(1 : ℤ) by ring, zpow_neg]; norm_num
    rw [this]; ring
  rcases hf with ⟨hzF, hle, hmax⟩ | ⟨hzF, hge, hmin⟩
  · -- RoundDown: z ≤ m.
    left
    obtain ⟨c, hc⟩ := F₁_g_quantum p hp_ge_2 e hzF
    rw [hc, h_m_eq] at hle
    -- c·2^e ≤ (7/2)·2^e ⇒ c ≤ 3.
    have hc_r_le : (c : ℝ) ≤ 7/2 := le_of_mul_le_mul_right hle h_2e_pos
    have hc_lt : (c : ℝ) < 4 := by linarith
    have hc_int_lt : c < 4 := by exact_mod_cast hc_lt
    have hc_int_le : c ≤ 3 := by omega
    -- y_lo = 3·2^e ≤ m, so by max, z ≥ y_lo.
    have h_y_lo_le : ((y_lo_g e : Dyadic) : ℝ) ≤ ((m_g e : Dyadic) : ℝ) := by
      rw [coe_y_lo_g, h_m_eq]
      have : (3 : ℝ) ≤ 7/2 := by norm_num
      nlinarith
    have h_ge_y_lo := hmax (y_lo_g e) (y_lo_mem_F₁_g p hp_ge_2 e) h_y_lo_le
    rw [coe_y_lo_g, hc] at h_ge_y_lo
    have hc_r_ge : (3 : ℝ) ≤ (c : ℝ) := by
      exact le_of_mul_le_mul_right h_ge_y_lo h_2e_pos
    have hc_int_ge : 3 ≤ c := by exact_mod_cast hc_r_ge
    have hc_eq : c = 3 := by omega
    rw [hc, coe_y_lo_g, hc_eq]; push_cast; ring
  · -- RoundUp: z ≥ m.
    right
    obtain ⟨c, hc⟩ := F₁_g_quantum p hp_ge_2 e hzF
    rw [hc, h_m_eq] at hge
    have hc_r_ge : (7 / 2 : ℝ) ≤ (c : ℝ) := le_of_mul_le_mul_right hge h_2e_pos
    have hc_gt : (3 : ℝ) < (c : ℝ) := by linarith
    have hc_int_gt : 3 < c := by exact_mod_cast hc_gt
    have hc_int_ge : 4 ≤ c := by omega
    -- y_hi = 4·2^e ≥ m, so by min, z ≤ y_hi.
    have h_y_hi_ge : ((m_g e : Dyadic) : ℝ) ≤ ((y_hi_g e : Dyadic) : ℝ) := by
      rw [coe_y_hi_g, h_m_eq]
      have h_split : (2 : ℝ)^(e + 2) = 4 * (2 : ℝ)^e := by
        rw [show (e + 2 : ℤ) = e + 2 from rfl,
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        have : (2 : ℝ)^(2 : ℤ) = 4 := by norm_num
        rw [this]; ring
      rw [h_split]
      have : (7/2 : ℝ) ≤ 4 := by norm_num
      nlinarith
    have h_le_y_hi := hmin (y_hi_g e) (y_hi_mem_F₁_g p hp_ge_2 e) h_y_hi_ge
    rw [coe_y_hi_g, hc] at h_le_y_hi
    have h_split : (2 : ℝ)^(e + 2) = 4 * (2 : ℝ)^e := by
      rw [show (e + 2 : ℤ) = e + 2 from rfl,
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      have : (2 : ℝ)^(2 : ℤ) = 4 := by norm_num
      rw [this]; ring
    rw [h_split] at h_le_y_hi
    have hc_r_le : (c : ℝ) ≤ 4 := le_of_mul_le_mul_right h_le_y_hi h_2e_pos
    have hc_int_le : c ≤ 4 := by exact_mod_cast hc_r_le
    have hc_eq : c = 4 := by omega
    rw [hc, coe_y_hi_g, hc_eq, h_split]; push_cast; ring

/-- Inner step: `Rounds F₁ RNE m y_hi` — at the F₁-midpoint `m`, RNE breaks
the tie between `y_lo = 3·2^e` and `y_hi = 4·2^e` toward the even neighbor. -/
private theorem rounds_F₁_g_RNE_m_y_hi (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ) :
    Rounds (F₁_g p hp_ge_2 e) (.Nearest .ToEven)
      ((m_g e : Dyadic) : ℝ) (y_hi_g e) := by
  have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
  have h_m_eq : ((m_g e : Dyadic) : ℝ) = (7 / 2) * (2 : ℝ)^e := by
    rw [coe_m_g, show (e - 1 : ℤ) = e + (-1 : ℤ) by ring,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have : (2 : ℝ)^(-1 : ℤ) = 1/2 := by
      rw [show ((-1 : ℤ)) = -(1 : ℤ) by ring, zpow_neg]; norm_num
    rw [this]; ring
  have h_y_hi_eq : ((y_hi_g e : Dyadic) : ℝ) = 4 * (2 : ℝ)^e := by
    rw [coe_y_hi_g, show (e + 2 : ℤ) = e + 2 from rfl,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have : (2 : ℝ)^(2 : ℤ) = 4 := by norm_num
    rw [this]; ring
  refine ⟨y_hi_mem_F₁_g p hp_ge_2 e, ?_, ?_, ?_⟩
  · right
    refine ⟨y_hi_mem_F₁_g p hp_ge_2 e, ?_, ?_⟩
    · rw [h_m_eq, h_y_hi_eq]; nlinarith
    · intro z hz hge
      obtain ⟨c, hc⟩ := F₁_g_quantum p hp_ge_2 e hz
      rw [hc, h_m_eq] at hge
      rw [h_y_hi_eq, hc]
      have hc_r_ge : (7/2 : ℝ) ≤ (c : ℝ) := le_of_mul_le_mul_right hge h_2e_pos
      have hc_r_3lt : (3 : ℝ) < (c : ℝ) := by linarith
      have hc_int_3lt : 3 < c := by exact_mod_cast hc_r_3lt
      have hc_int_ge : 4 ≤ c := by omega
      have hc_r_ge_4 : (4 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc_int_ge
      nlinarith
  · intro z hz hf
    rcases F₁_faithful_m_eq_g p hp_ge_2 e hf with hz_lo | hz_hi
    · rw [hz_lo, coe_y_lo_g, h_m_eq, h_y_hi_eq]
      have hL : |(7/2 : ℝ) * (2 : ℝ)^e - 4 * (2 : ℝ)^e| = (1/2) * (2 : ℝ)^e := by
        rw [show (7/2 : ℝ) * (2 : ℝ)^e - 4 * (2 : ℝ)^e
            = -((1/2) * (2 : ℝ)^e) by ring, abs_neg, abs_of_pos]
        nlinarith
      have hR : |(7/2 : ℝ) * (2 : ℝ)^e - 3 * (2 : ℝ)^e| = (1/2) * (2 : ℝ)^e := by
        rw [show (7/2 : ℝ) * (2 : ℝ)^e - 3 * (2 : ℝ)^e
            = (1/2) * (2 : ℝ)^e by ring, abs_of_pos]
        nlinarith
      rw [hL, hR]
    · rw [hz_hi]
  · rintro ⟨_, _, _, _, _⟩
    exact isEven_F₁_g_y_hi p hp_ge_2 e

/-! ### Predecessor-extraction lemma for the witness construction -/

/-- For our specific midpoint `m = 7·2^(e-1)`, F₂'s grid representation
`(c, k)` always has `c ≥ 2` and `Int.log 2 c = Int.log 2 (c-1)` (since
`c = 7·2^j` for some `j ≥ 0` and `7·2^j - 1 ≥ 4·2^j` keeps it in the same
magnitude class). This is the pre-requisite for invoking
`prev_F_adjacent_of_log_eq`. -/
private theorem m_g_grid_log_invariant {q₂ : ℕ} {f₂ : ℤ} {k c : ℤ} {e : ℤ}
    (hq₂ : 4 ≤ q₂) (hf₂_le : f₂ ≤ e - 2)
    (hk_max : k = max f₂ (Int.log 2 ((c : ℝ) * (2 : ℝ) ^ k) - (q₂ : ℤ) + 1))
    (hm_eq : (7 : ℝ) * (2 : ℝ) ^ (e - 1) = (c : ℝ) * (2 : ℝ) ^ k) :
    2 ≤ c ∧ Int.log 2 (((c - 1 : ℤ) : ℝ) * (2 : ℝ)^k) =
            Int.log 2 ((c : ℝ) * (2 : ℝ)^k) := by
  have h_2_pos : (0 : ℝ) < (2 : ℝ)^(e-1) := zpow_pos (by norm_num) _
  have hm_pos : (0 : ℝ) < (7 : ℝ) * (2 : ℝ)^(e - 1) := by nlinarith
  have h_log_m : Int.log 2 ((7 : ℝ) * (2 : ℝ)^(e - 1)) = e + 1 := by
    apply le_antisymm
    · have hle : (7 : ℝ) * (2 : ℝ)^(e-1) < ((2 : ℕ) : ℝ)^(e + 2) := by
        rw [show ((2 : ℕ) : ℝ) = 2 from by push_cast; rfl,
            show e + 2 = (e - 1) + 3 by ring,
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        have : (2 : ℝ)^(3 : ℤ) = 8 := by norm_num
        rw [this]; nlinarith
      have h_lt := (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) hm_pos).mp hle
      omega
    · have hge : ((2 : ℕ) : ℝ)^(e + 1) ≤ (7 : ℝ) * (2 : ℝ)^(e-1) := by
        rw [show ((2 : ℕ) : ℝ) = 2 from by push_cast; rfl,
            show e + 1 = (e - 1) + 2 by ring,
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        have : (2 : ℝ)^(2 : ℤ) = 4 := by norm_num
        rw [this]; nlinarith
      exact (Int.zpow_le_iff_le_log (by norm_num : 1 < (2 : ℕ)) hm_pos).mp hge
  have h_log_cxk : Int.log 2 ((c : ℝ) * (2 : ℝ)^k) = e + 1 := by
    rw [← hm_eq]; exact h_log_m
  rw [h_log_cxk] at hk_max
  have hk_eq : k = max f₂ (e + 2 - q₂) := by
    convert hk_max using 2; ring
  have hk_le : k ≤ e - 2 := by
    rw [hk_eq]
    have h1 : f₂ ≤ e - 2 := hf₂_le
    have h2 : e + 2 - (q₂ : ℤ) ≤ e - 2 := by
      have : (4 : ℤ) ≤ (q₂ : ℤ) := by exact_mod_cast hq₂
      omega
    exact max_le h1 h2
  have h_2k_pos : (0 : ℝ) < (2 : ℝ)^k := zpow_pos (by norm_num) _
  have hc_real : (c : ℝ) = 7 * (2 : ℝ)^(e - 1 - k) := by
    have h_split : (2 : ℝ)^(e - 1) = (2 : ℝ)^(e - 1 - k) * (2 : ℝ)^k := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
    have h1 : (7 : ℝ) * ((2 : ℝ)^(e - 1 - k) * (2 : ℝ)^k) = (c : ℝ) * (2 : ℝ)^k := by
      rw [← h_split]; exact hm_eq
    have h2 : (7 : ℝ) * (2 : ℝ)^(e - 1 - k) * (2 : ℝ)^k = (c : ℝ) * (2 : ℝ)^k := by
      rw [mul_assoc]; exact h1
    exact (mul_right_cancel₀ (ne_of_gt h_2k_pos) h2).symm
  have h_exp_ge : 1 ≤ e - 1 - k := by omega
  have hc_ge_14 : (14 : ℝ) ≤ (c : ℝ) := by
    rw [hc_real]
    have : (2 : ℝ)^(e - 1 - k) ≥ (2 : ℝ)^(1 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h_exp_ge
    nlinarith
  have hc_int_ge : 14 ≤ c := by exact_mod_cast hc_ge_14
  refine ⟨by omega, ?_⟩
  rw [h_log_cxk]
  apply le_antisymm
  · have h_c1_pos : 0 < c - 1 := by omega
    have h_c1_real_pos : (0 : ℝ) < ((c - 1 : ℤ) : ℝ) := by exact_mod_cast h_c1_pos
    have h_prod_pos : (0 : ℝ) < ((c - 1 : ℤ) : ℝ) * (2 : ℝ)^k :=
      mul_pos h_c1_real_pos h_2k_pos
    have h_c1_lt_c : ((c - 1 : ℤ) : ℝ) < (c : ℝ) := by push_cast; linarith
    have h_prod_lt_m : ((c - 1 : ℤ) : ℝ) * (2 : ℝ)^k < (c : ℝ) * (2 : ℝ)^k := by
      nlinarith
    have h_prod_lt_2 : ((c - 1 : ℤ) : ℝ) * (2 : ℝ)^k < ((2 : ℕ) : ℝ)^(e + 2) := by
      rw [show ((2 : ℕ) : ℝ) = 2 from by push_cast; rfl]
      have h_c1_lt : ((c - 1 : ℤ) : ℝ) * (2 : ℝ)^k < (c : ℝ) * (2 : ℝ)^k := h_prod_lt_m
      have h_log_m_ub : (7 : ℝ) * (2 : ℝ)^(e - 1) < (2 : ℝ)^(e + 2) := by
        rw [show e + 2 = (e - 1) + 3 by ring,
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        have : (2 : ℝ)^(3 : ℤ) = 8 := by norm_num
        rw [this]; nlinarith
      have : (c : ℝ) * (2 : ℝ)^k < (2 : ℝ)^(e + 2) := by rw [← hm_eq]; exact h_log_m_ub
      linarith
    have h := (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) h_prod_pos).mp h_prod_lt_2
    omega
  · have h_c1_pos : 0 < c - 1 := by omega
    have h_prod_pos : (0 : ℝ) < ((c - 1 : ℤ) : ℝ) * (2 : ℝ)^k :=
      mul_pos (by exact_mod_cast h_c1_pos) h_2k_pos
    have h_c1_ge_13 : (13 : ℝ) ≤ ((c - 1 : ℤ) : ℝ) := by
      have : (13 : ℤ) ≤ c - 1 := by omega
      exact_mod_cast this
    have h_prod_ge : ((2 : ℕ) : ℝ)^(e + 1) ≤ ((c - 1 : ℤ) : ℝ) * (2 : ℝ)^k := by
      rw [show ((2 : ℕ) : ℝ) = 2 from by push_cast; rfl,
          show e + 1 = (e - 1 - k) + k + 2 by ring,
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      have h22 : (2 : ℝ)^(2 : ℤ) = 4 := by norm_num
      rw [h22]
      have h_2e1k_pos : (0 : ℝ) < (2 : ℝ)^(e - 1 - k) := zpow_pos (by norm_num) _
      have hc_real_alt : (c : ℝ) = 7 * (2 : ℝ)^(e - 1 - k) := hc_real
      have h_c1_real : ((c - 1 : ℤ) : ℝ) = (c : ℝ) - 1 := by push_cast; ring
      rw [h_c1_real, hc_real_alt]
      have h_2e1k_ge_2 : (2 : ℝ) ≤ (2 : ℝ)^(e - 1 - k) := by
        calc (2 : ℝ) = (2 : ℝ)^(1 : ℤ) := by norm_num
          _ ≤ (2 : ℝ)^(e - 1 - k) :=
              zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h_exp_ge
      nlinarith
    exact (Int.zpow_le_iff_le_log (by norm_num : 1 < (2 : ℕ)) h_prod_pos).mp h_prod_ge

/-- **Core RNE-RNE counterexample.** Takes F₂'s structural parameters
explicitly: precision `q₂ ≥ p + 2`, finite quantum `f₂ ≤ e − 2`, and
unbounded magnitude. Witness `x = (3m + pred_{F₂}(m)) / 4` where the F₂-
predecessor of `m` is extracted via `prev_F_adjacent_of_log_eq`. The
public-facing version is `no_rndRNE_RNE_general`, which takes only
`(F₁.extend 2) ⊆ F₂` plus the finiteness hypotheses and derives the
remaining bounds. -/
theorem no_rndRNE_RNE_arbitrary_F₂
    (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ)
    (F₂ : AbstractFormat)
    {q₂ : ℕ} (hF₂_p : F₂.p = (q₂ : ℕ∞)) (hq₂ : p + 2 ≤ q₂)
    {f₂ : ℤ} (hF₂_exp : F₂.exp = (f₂ : WithBot ℤ)) (hf₂ : f₂ ≤ e - 2)
    (hF₂_b : F₂.b = ⊤) :
    F₁_g p hp_ge_2 e ⊆ F₂ ∧
    ∃ (x : ℝ) (z w : Dyadic),
      Rounds F₂ (.Nearest .ToEven) x z ∧
      Rounds (F₁_g p hp_ge_2 e) (.Nearest .ToEven) (z : ℝ) w ∧
      ¬ Rounds (F₁_g p hp_ge_2 e) (.Nearest .ToEven) x w := by
  -- Hypotheses derived from F₂'s parameters.
  have hq₁_le_q₂ : (((p : ℕ) : ℕ∞)) ≤ F₂.p := by
    rw [hF₂_p]; exact_mod_cast (by omega : p ≤ q₂)
  have hf₂_le_e : F₂.exp ≤ (((e : ℤ)) : WithBot ℤ) := by
    rw [hF₂_exp]
    exact_mod_cast (by omega : f₂ ≤ e)
  have hb_le : (F₁_g p hp_ge_2 e).b ≤ F₂.b := by
    have h1 : (F₁_g p hp_ge_2 e).b = ⊤ := rfl
    rw [h1, hF₂_b]
  have h_F₁_sub : F₁_g p hp_ge_2 e ⊆ F₂ := containsPrec hq₁_le_q₂ hf₂_le_e hb_le
  refine ⟨h_F₁_sub, ?_⟩
  -- m, y_lo, y_hi, etc.
  set m : Dyadic := Dyadic.ofIntZpow 7 (e - 1) with hm_def
  set y_lo : Dyadic := y_lo_g e with hy_lo_def
  set y_hi : Dyadic := y_hi_g e with hy_hi_def
  have h_m_coe : (m : ℝ) = 7 * (2 : ℝ)^(e - 1) := by
    rw [hm_def, Dyadic.coe_ofIntZpow]; push_cast; ring
  have h_m_pos : 0 < (m : ℝ) := by
    rw [h_m_coe]
    have : (0 : ℝ) < (2 : ℝ)^(e - 1) := zpow_pos (by norm_num) _
    nlinarith
  -- m ∈ F₂.
  have h_m_mem_F₂ : m ∈ F₂ := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hF₂_p]
      refine ⟨7, e - 1, ?_, ?_⟩
      · rw [hm_def, Dyadic.coe_ofIntZpow]
      · have h_pow : (8 : ℤ) ≤ (2 : ℤ)^q₂ :=
          calc (8 : ℤ) = (2 : ℤ)^3 := by norm_num
            _ ≤ (2 : ℤ)^q₂ := pow_le_pow_right₀ (by norm_num) (by omega : 3 ≤ q₂)
        have h_abs : |(7 : ℤ)| = 7 := by decide
        omega
    · rw [hF₂_exp]
      rw [Dyadic.quantumAtLeast_coe]
      refine ⟨7 * (2 : ℤ)^(e - 1 - f₂).toNat, ?_⟩
      rw [hm_def, Dyadic.coe_ofIntZpow]
      have h_diff_nn : 0 ≤ e - 1 - f₂ := by omega
      have h_split : (2 : ℝ)^(e - 1) = (2 : ℝ)^((e - 1 - f₂).toNat : ℤ) * (2 : ℝ)^f₂ := by
        rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        congr 1; rw [Int.toNat_of_nonneg h_diff_nn]; ring
      rw [h_split, zpow_natCast]; push_cast; ring
    · rw [hF₂_b]; trivial
  -- Extract grid representation of m in F₂.
  obtain ⟨k, c, hk_ge_f₂, hc_lt_abs, hm_eq_F₂, hk_max⟩ :=
    exists_grid_rep F₂ hF₂_p hF₂_exp h_m_mem_F₂.1 h_m_mem_F₂.2.1 h_m_pos
  -- c > 0.
  have hc_pos : 0 < c := grid_rep_c_pos h_m_pos hm_eq_F₂
  have hc_lt_pos : c < (2 : ℤ)^q₂ := by
    have h_abs : |c| = c := abs_of_pos hc_pos
    rw [← h_abs]; exact hc_lt_abs
  -- m_g_grid_log_invariant: c ≥ 2 and log invariance.
  have hm_eq_simple : (7 : ℝ) * (2 : ℝ)^(e - 1) = (c : ℝ) * (2 : ℝ)^k := by
    rw [← h_m_coe]; exact hm_eq_F₂
  -- Convert hk_max from the `Int.log 2 m` form to the `Int.log 2 (c·2^k)` form.
  have hk_max' : k = max f₂ (Int.log 2 ((c : ℝ) * (2 : ℝ)^k) - (q₂ : ℤ) + 1) := by
    rw [← hm_eq_F₂]; exact hk_max
  obtain ⟨hc_ge_2, h_log_eq⟩ := m_g_grid_log_invariant
    (by omega : 4 ≤ q₂) hf₂ hk_max' hm_eq_simple
  -- Apply prev_F_adjacent_of_log_eq to extract pred.
  obtain ⟨h_pred_mem, h_pred_lt_m, h_pred_max⟩ :=
    prev_F_adjacent_of_log_eq F₂ hF₂_p hF₂_exp h_m_mem_F₂ h_m_pos
      hk_ge_f₂ hc_ge_2 hc_lt_pos hm_eq_F₂ hk_max' h_log_eq
  set pred : Dyadic := Dyadic.ofIntZpow (c - 1) k with h_pred_def
  -- Define x = (3m + pred)/4.
  set x_val : ℝ := (3 * (m : ℝ) + (pred : ℝ)) / 4 with hx_def
  -- Key inequalities about x.
  have h_pred_real : (pred : ℝ) = ((c - 1 : ℤ) : ℝ) * (2 : ℝ)^k := by
    rw [h_pred_def, Dyadic.coe_ofIntZpow]
  have h_m_real : (m : ℝ) = (c : ℝ) * (2 : ℝ)^k := hm_eq_F₂
  have h_m_minus_pred : (m : ℝ) - (pred : ℝ) = (2 : ℝ)^k := by
    rw [h_m_real, h_pred_real]; push_cast; ring
  have h_2k_pos : (0 : ℝ) < (2 : ℝ)^k := zpow_pos (by norm_num) _
  have h_pred_pos : (0 : ℝ) < (pred : ℝ) := by
    rw [h_pred_real]
    have h_c1_pos : (0 : ℝ) < ((c - 1 : ℤ) : ℝ) := by
      have : 0 < c - 1 := by omega
      exact_mod_cast this
    exact mul_pos h_c1_pos h_2k_pos
  have h_x_lt_m : x_val < (m : ℝ) := by
    rw [hx_def]; linarith
  have h_pred_lt_x : (pred : ℝ) < x_val := by
    rw [hx_def]; linarith
  have h_x_pos : 0 < x_val := by linarith
  -- x_val < y_hi/2 (where y_hi = 4·2^e = 2^(e+2)). Specifically x < m, m < y_hi.
  -- Coercions for y_lo and y_hi.
  have h_y_lo_coe : (y_lo : ℝ) = 3 * (2 : ℝ)^e := coe_y_lo_g e
  have h_y_hi_coe : (y_hi : ℝ) = (2 : ℝ)^(e + 2) := coe_y_hi_g e
  -- y_hi = m + Δ where Δ = 2^(e-1). y_lo = m - Δ.
  have h_2e1_pos : (0 : ℝ) < (2 : ℝ)^(e - 1) := zpow_pos (by norm_num) _
  have h_y_hi_eq : (y_hi : ℝ) = (m : ℝ) + (2 : ℝ)^(e - 1) := by
    rw [h_y_hi_coe, h_m_coe]
    rw [show e + 2 = (e - 1) + 3 by ring,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have : (2 : ℝ)^(3 : ℤ) = 8 := by norm_num
    rw [this]; ring
  have h_y_lo_eq : (y_lo : ℝ) = (m : ℝ) - (2 : ℝ)^(e - 1) := by
    rw [h_y_lo_coe, h_m_coe]
    have h_split : (2 : ℝ)^e = (2 : ℝ)^(e - 1) * (2 : ℝ)^(1 : ℤ) := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
    rw [h_split]
    have h_two : (2 : ℝ)^(1 : ℤ) = 2 := by norm_num
    rw [h_two]; ring
  -- k ≤ e - 2 (proven inside m_g_grid_log_invariant, but we need it again).
  have hk_le_e2 : k ≤ e - 2 := by
    have h_log_cxk : Int.log 2 ((c : ℝ) * (2 : ℝ)^k) = e + 1 := by
      have h_log_m : Int.log 2 ((m : ℝ)) = e + 1 := by
        rw [h_m_coe]
        rw [show (7 : ℝ) * (2 : ℝ)^(e - 1) = (7 : ℝ) * (2 : ℝ)^(e - 1) from rfl]
        apply le_antisymm
        · have hle : (7 : ℝ) * (2 : ℝ)^(e-1) < ((2 : ℕ) : ℝ)^(e + 2) := by
            rw [show ((2 : ℕ) : ℝ) = 2 from by push_cast; rfl,
                show e + 2 = (e - 1) + 3 by ring,
                zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
            have : (2 : ℝ)^(3 : ℤ) = 8 := by norm_num
            rw [this]; nlinarith
          have hm_pos' : (0 : ℝ) < (7 : ℝ) * (2 : ℝ)^(e - 1) := by nlinarith
          have h_log_lt : Int.log 2 ((7 : ℝ) * (2 : ℝ)^(e-1)) < e + 2 :=
            (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) hm_pos').mp hle
          omega
        · have hge : ((2 : ℕ) : ℝ)^(e + 1) ≤ (7 : ℝ) * (2 : ℝ)^(e-1) := by
            rw [show ((2 : ℕ) : ℝ) = 2 from by push_cast; rfl,
                show e + 1 = (e - 1) + 2 by ring,
                zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
            have : (2 : ℝ)^(2 : ℤ) = 4 := by norm_num
            rw [this]; nlinarith
          have hm_pos' : (0 : ℝ) < (7 : ℝ) * (2 : ℝ)^(e - 1) := by nlinarith
          exact (Int.zpow_le_iff_le_log (by norm_num : 1 < (2 : ℕ)) hm_pos').mp hge
      rw [h_m_real] at h_log_m
      exact h_log_m
    rw [h_log_cxk] at hk_max'
    have : k = max f₂ (e + 2 - q₂) := by
      convert hk_max' using 2; ring
    rw [this]
    have h2 : e + 2 - (q₂ : ℤ) ≤ e - 2 := by
      have : (4 : ℤ) ≤ (q₂ : ℤ) := by exact_mod_cast (show 4 ≤ q₂ by omega)
      omega
    exact max_le hf₂ h2
  -- m - pred = 2^k, and 2^k ≤ 2^(e-2).
  have h_2k_le : (2 : ℝ)^k ≤ (2 : ℝ)^(e - 2) :=
    zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk_le_e2
  have h_2e2_pos : (0 : ℝ) < (2 : ℝ)^(e - 2) := zpow_pos (by norm_num) _
  -- 2^k ≤ 2^(e-2) < 2^(e-1) < 2^(e+1).
  have h_2k_lt_2e1 : (2 : ℝ)^k < (2 : ℝ)^(e - 1) := by
    calc (2 : ℝ)^k ≤ (2 : ℝ)^(e - 2) := h_2k_le
      _ < (2 : ℝ)^(e - 1) := by
          have h : (e - 2 : ℤ) < e - 1 := by omega
          have : (2 : ℝ)^(e - 2) < (2 : ℝ)^(e - 1) :=
            zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) h
          exact this
  -- 4·x = 3m + pred = 3m + (m - 2^k) = 4m - 2^k.
  -- So x = m - 2^k/4 = m - 2^(k-2).
  -- y_lo ≤ x: m - Δ ≤ m - 2^k/4 iff 2^k/4 ≤ Δ = 2^(e-1) iff 2^k ≤ 2^(e+1). True.
  refine ⟨x_val, m, y_hi, ?_, ?_, ?_⟩
  · -- Rounds F₂ RNE x m.
    refine ⟨h_m_mem_F₂, ?_, ?_, ?_⟩
    · -- IsFaithfulRound: RoundUp.
      right
      refine ⟨h_m_mem_F₂, le_of_lt h_x_lt_m, ?_⟩
      intro z hzF₂ hx_le_z
      -- Need m ≤ z. If z < m, then z ≤ pred (by h_pred_max), but pred < x ≤ z, contra.
      by_contra h_z_lt_m
      push Not at h_z_lt_m
      have h_z_le_pred := h_pred_max z hzF₂ h_z_lt_m
      linarith
    · -- Closeness: ∀ z ∈ F₂ faithful for x, |x - m| ≤ |x - z|.
      intro z hzF₂ hf
      -- Faithful z: RoundDown (= pred) or RoundUp (= m).
      rcases hf with ⟨_, hz_le, hz_max⟩ | ⟨_, hx_le_z, hz_min⟩
      · -- RoundDown: z ≤ x. z ≤ x < m, so z < m, so z ≤ pred.
        have h_z_lt_m : (z : ℝ) < (m : ℝ) := lt_of_le_of_lt hz_le h_x_lt_m
        have h_z_le_pred := h_pred_max z hzF₂ h_z_lt_m
        -- z ≤ pred ⇒ |x - z| ≥ x - pred = 3·2^k/4 ≥ 2^k/4 = |x - m|.
        have h_xm : x_val - (m : ℝ) = -((2 : ℝ)^k / 4) := by
          rw [hx_def]; linarith
        have h_zx : (z : ℝ) ≤ (pred : ℝ) := by
          have hpred_ge_z : (pred : ℝ) ≥ (z : ℝ) := h_z_le_pred
          linarith
        have h_x_pred : x_val - (pred : ℝ) = 3 * (2 : ℝ)^k / 4 := by
          rw [hx_def]; linarith
        have hL : |x_val - (m : ℝ)| = (2 : ℝ)^k / 4 := by
          rw [h_xm, abs_neg, abs_of_pos]; linarith
        rw [hL]
        have h_x_minus_z_ge : (2 : ℝ)^k / 4 ≤ x_val - (z : ℝ) := by
          have : x_val - (pred : ℝ) ≤ x_val - (z : ℝ) := by linarith
          rw [h_x_pred] at this; linarith
        have h_abs : |x_val - (z : ℝ)| = x_val - (z : ℝ) := by
          rw [abs_of_nonneg]; linarith
        rw [h_abs]; exact h_x_minus_z_ge
      · -- RoundUp: x ≤ z ≤ m (by min property). Either z = m (trivial) or
        -- z < m forces z ≤ pred via F-adjacency, contradicting pred < x ≤ z.
        have h_z_le_m : (z : ℝ) ≤ (m : ℝ) :=
          hz_min m h_m_mem_F₂ (le_of_lt h_x_lt_m)
        -- Need 2^k/4 ≤ z - x, but z ≤ m gives z - x ≤ 2^k/4. So z = m.
        -- Hmm we'd need to verify z = m here.
        have h_z_eq_m : (z : ℝ) = (m : ℝ) := by
          -- If z < m: by adjacency, z ≤ pred. But z ≥ x > pred. Contra.
          by_contra h_z_ne_m
          have h_z_lt_m : (z : ℝ) < (m : ℝ) := lt_of_le_of_ne h_z_le_m h_z_ne_m
          have h_z_le_pred := h_pred_max z hzF₂ h_z_lt_m
          linarith
        rw [h_z_eq_m]
    · -- No-tie.
      rintro ⟨z, hzF₂, hf, hne, heq⟩
      -- z faithful, z ≠ m, equal distance. Then z = pred (the only other faithful).
      rcases hf with ⟨_, hz_le, hz_max⟩ | ⟨_, hx_le_z, hz_min⟩
      · -- RoundDown z ≤ pred ⇒ |x - z| ≥ 3·2^k/4 > 2^k/4 = |x - m|.
        exfalso
        have h_z_lt_m : (z : ℝ) < (m : ℝ) := lt_of_le_of_lt hz_le h_x_lt_m
        have h_z_le_pred := h_pred_max z hzF₂ h_z_lt_m
        have h_xm : x_val - (m : ℝ) = -((2 : ℝ)^k / 4) := by rw [hx_def]; linarith
        have hL : |x_val - (m : ℝ)| = (2 : ℝ)^k / 4 := by
          rw [h_xm, abs_neg, abs_of_pos]; linarith
        have h_xz_ge : x_val - (z : ℝ) ≥ x_val - (pred : ℝ) := by linarith
        have h_x_pred : x_val - (pred : ℝ) = 3 * (2 : ℝ)^k / 4 := by
          rw [hx_def]; linarith
        have h_abs_xz : |x_val - (z : ℝ)| = x_val - (z : ℝ) := by
          rw [abs_of_nonneg]; linarith
        rw [hL, h_abs_xz] at heq
        linarith
      · -- RoundUp: z ≥ x. We've shown z = m. But hne says z ≠ m. Contradiction.
        exfalso
        apply hne
        apply Subtype.ext
        have h_z_le_m : (z : ℝ) ≤ (m : ℝ) := hz_min m h_m_mem_F₂ (le_of_lt h_x_lt_m)
        by_contra h_z_ne_m
        have h_z_lt_m : (z : ℝ) < (m : ℝ) := lt_of_le_of_ne h_z_le_m h_z_ne_m
        have h_z_le_pred := h_pred_max z hzF₂ h_z_lt_m
        linarith
  · -- Rounds F₁ RNE m y_hi.
    exact rounds_F₁_g_RNE_m_y_hi p hp_ge_2 e
  · -- ¬ Rounds F₁ RNE x y_hi.
    intro hr
    obtain ⟨_, _, h_close, _⟩ := hr
    have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
    -- y_lo is a faithful F₁-RoundDown of x.
    have h_y_lo_faith : IsFaithfulRound (F₁_g p hp_ge_2 e) x_val y_lo := by
      left
      refine ⟨y_lo_mem_F₁_g p hp_ge_2 e, ?_, ?_⟩
      · -- y_lo ≤ x = m - 2^k/4. y_lo = m - 2^(e-1). Need 2^k/4 ≤ 2^(e-1).
        rw [h_y_lo_eq]
        have h_2k4_le : (2 : ℝ)^k / 4 ≤ (2 : ℝ)^(e - 1) :=
          le_of_lt (by linarith [h_2k_lt_2e1])
        have hx_eq : x_val = (m : ℝ) - (2 : ℝ)^k / 4 := by
          rw [hx_def]; linarith
        rw [hx_eq]; linarith
      · intro z hz hz_le
        obtain ⟨c', hc'⟩ := F₁_g_quantum p hp_ge_2 e hz
        have h_z_lt_m : (z : ℝ) < (m : ℝ) := lt_of_le_of_lt hz_le h_x_lt_m
        rw [hc', h_m_coe] at h_z_lt_m
        have h_7_2 : (7 : ℝ) * (2 : ℝ)^(e-1) = (7/2) * (2 : ℝ)^e := by
          rw [show (e-1 : ℤ) = e + (-1 : ℤ) from by ring,
              zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          have : (2 : ℝ)^(-1 : ℤ) = 1/2 := by
            rw [show ((-1 : ℤ)) = -(1 : ℤ) from by ring, zpow_neg]; norm_num
          rw [this]; ring
        rw [h_7_2] at h_z_lt_m
        have hc'_r_lt : (c' : ℝ) < 7/2 :=
          lt_of_mul_lt_mul_right h_z_lt_m h_2e_pos.le
        have hc'_lt_4 : (c' : ℝ) < 4 := by linarith
        have : c' < 4 := by exact_mod_cast hc'_lt_4
        have hc'_le_3 : c' ≤ 3 := by omega
        change (z : ℝ) ≤ (y_lo : ℝ)
        rw [hc', h_y_lo_coe]
        have : (c' : ℝ) ≤ 3 := by exact_mod_cast hc'_le_3
        nlinarith
    -- Apply closeness.
    have h_close_lo := h_close y_lo (y_lo_mem_F₁_g p hp_ge_2 e) h_y_lo_faith
    -- |x - y_hi| = 2^(e-1) + 2^k/4. |x - y_lo| = 2^(e-1) - 2^k/4.
    have hx_eq : x_val = (m : ℝ) - (2 : ℝ)^k / 4 := by
      rw [hx_def]; linarith
    have h_x_y_hi : x_val - (y_hi : ℝ) = -((2 : ℝ)^(e-1) + (2 : ℝ)^k/4) := by
      rw [h_y_hi_eq, hx_eq]; ring
    have h_x_y_lo : x_val - (y_lo : ℝ) = (2 : ℝ)^(e-1) - (2 : ℝ)^k/4 := by
      rw [h_y_lo_eq, hx_eq]; ring
    have h_2k4_pos : (0 : ℝ) < (2 : ℝ)^k / 4 := by linarith
    have h_2k4_lt : (2 : ℝ)^k / 4 < (2 : ℝ)^(e - 1) := by linarith [h_2k_lt_2e1]
    have hL : |x_val - (y_hi : ℝ)| = (2 : ℝ)^(e-1) + (2 : ℝ)^k/4 := by
      rw [h_x_y_hi, abs_neg, abs_of_pos]; linarith
    have hR : |x_val - (y_lo : ℝ)| = (2 : ℝ)^(e-1) - (2 : ℝ)^k/4 := by
      rw [h_x_y_lo, abs_of_pos]; linarith
    rw [hL, hR] at h_close_lo
    linarith

/-- **Convenience wrapper** with the minimal user-facing hypotheses: the
paper-style containment `(F₁.extend 2) ⊆ F₂` plus the structural finiteness
of `F₂.p` and `F₂.exp`. The precision/quantum bounds and the unboundedness of
`F₂.b` are derived internally and forwarded to `no_rndRNE_RNE_arbitrary_F₂`.

The two finiteness hypotheses are essential: the predecessor-extraction
machinery needs `exists_grid_rep`, which requires both `F.p` and `F.exp`
finite. (Containment alone does *not* force these — `F₂.p = ⊤` and
`F₂.exp = ⊥` are consistent with `F₁.extend 2 ⊆ F₂`.) -/
theorem no_rndRNE_RNE_general
    (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ)
    (F₂ : AbstractFormat)
    (hsub : (F₁_g p hp_ge_2 e).extend 2 ⊆ F₂)
    (hF₂_p_fin : F₂.p ≠ ⊤)
    (hF₂_exp_fin : F₂.exp ≠ ⊥) :
    ∃ (x : ℝ) (z w : Dyadic),
      Rounds F₂ (.Nearest .ToEven) x z ∧
      Rounds (F₁_g p hp_ge_2 e) (.Nearest .ToEven) (z : ℝ) w ∧
      ¬ Rounds (F₁_g p hp_ge_2 e) (.Nearest .ToEven) x w := by
  -- Extract finite q₂ and f₂.
  obtain ⟨q₂, hq₂_eq⟩ := WithTop.ne_top_iff_exists.mp hF₂_p_fin
  obtain ⟨f₂, hf₂_eq⟩ := WithBot.ne_bot_iff_exists.mp hF₂_exp_fin
  have hF₂_p : F₂.p = (q₂ : ℕ∞) := hq₂_eq.symm
  have hF₂_exp : F₂.exp = (f₂ : WithBot ℤ) := hf₂_eq.symm
  -- Derive F₂.b = ⊤ from arbitrarily large element.
  have hF₂_b : F₂.b = ⊤ := by
    by_contra h_b_ne
    obtain ⟨b, hb_eq⟩ := WithTop.ne_top_iff_exists.mp h_b_ne
    set N : ℤ := max (e - 2) (Int.log 2 ((b : Dyadic) : ℝ) + 1) with hN_def
    set y_huge : Dyadic := Dyadic.ofIntZpow 1 N with hy_huge_def
    have hN_ge : e - 2 ≤ N := le_max_left _ _
    have hy_huge_real : ((y_huge : Dyadic) : ℝ) = (2 : ℝ)^N := by
      rw [hy_huge_def, Dyadic.coe_ofIntZpow]; push_cast; ring
    have hy_huge_in_ext2 : y_huge ∈ (F₁_g p hp_ge_2 e).extend 2 := by
      refine ⟨?_, ?_, trivial⟩
      · change Dyadic.precisionAtMost ((((p : ℕ) : ℕ∞)) + (2 : ℕ)) y_huge
        have h_eq : ((((p : ℕ) : ℕ∞)) + (2 : ℕ)) = ((p + 2 : ℕ) : ℕ∞) := by
          push_cast; ring
        rw [h_eq]
        refine ⟨1, N, ?_, ?_⟩
        · rw [hy_huge_real]; push_cast; ring
        · have h_pow : (2 : ℤ) ≤ (2 : ℤ)^(p + 2) :=
            calc (2 : ℤ) = (2 : ℤ)^1 := by norm_num
              _ ≤ (2 : ℤ)^(p + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
          have h_abs : |(1 : ℤ)| = 1 := by decide
          omega
      · change Dyadic.quantumAtLeast (((e - 2 : ℤ)) : WithBot ℤ) y_huge
        rw [Dyadic.quantumAtLeast_coe]
        refine ⟨(2 : ℤ)^(N - (e - 2)).toNat, ?_⟩
        rw [hy_huge_real, two_zpow_split_toNat (show e - 2 ≤ N by omega)]
        push_cast; ring
    have hy_huge_in_F₂ : y_huge ∈ F₂ := hsub _ hy_huge_in_ext2
    have hb_ok : boundOK F₂.b y_huge := hy_huge_in_F₂.2.2
    rw [← hb_eq] at hb_ok
    change |((y_huge : Dyadic) : ℝ)| ≤ ((b : Dyadic) : ℝ) at hb_ok
    rw [hy_huge_real] at hb_ok
    have h_2N_pos : (0 : ℝ) < (2 : ℝ)^N := zpow_pos (by norm_num) _
    rw [abs_of_pos h_2N_pos] at hb_ok
    have hN_ge_log : Int.log 2 ((b : Dyadic) : ℝ) + 1 ≤ N := le_max_right _ _
    by_cases hb_pos : 0 < ((b : Dyadic) : ℝ)
    · have h_lt_log_succ :
          ((b : Dyadic) : ℝ) < (2 : ℝ)^(Int.log 2 ((b : Dyadic) : ℝ) + 1) := by
        have := Int.lt_zpow_succ_log_self (b := 2)
          (by norm_num : 1 < (2 : ℕ)) ((b : Dyadic) : ℝ)
        rw [show ((2 : ℕ) : ℝ) = 2 from by push_cast; rfl] at this
        exact this
      have h_2N_ge : (2 : ℝ)^(Int.log 2 ((b : Dyadic) : ℝ) + 1) ≤ (2 : ℝ)^N :=
        zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hN_ge_log
      linarith
    · push Not at hb_pos
      linarith
  -- Derive p + 2 ≤ q₂ and f₂ ≤ e - 2 from a "tight" element.
  have hq₂_hf₂ : p + 2 ≤ q₂ ∧ f₂ ≤ e - 2 := by
    set c_max : ℤ := (2 : ℤ)^(p + 2) - 1 with hc_max_def
    have hc_max_pos : 0 < c_max := by
      have h_pow_ge : (2 : ℤ) ≤ (2 : ℤ)^(p + 2) := by
        calc (2 : ℤ) = (2 : ℤ)^1 := by norm_num
          _ ≤ (2 : ℤ)^(p + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
      omega
    have hc_max_lt : c_max < (2 : ℤ)^(p + 2) := by omega
    have hc_max_odd : Odd c_max := by
      refine ⟨(2 : ℤ)^(p + 1) - 1, ?_⟩
      rw [hc_max_def, show p + 2 = (p + 1) + 1 from by omega, pow_succ]
      ring
    set y_max : Dyadic := Dyadic.ofIntZpow c_max (e - 2) with hy_max_def
    have hy_max_real : ((y_max : Dyadic) : ℝ) = (c_max : ℝ) * (2 : ℝ)^(e - 2) := by
      rw [hy_max_def, Dyadic.coe_ofIntZpow]
    have h_2e2_pos : (0 : ℝ) < (2 : ℝ)^(e - 2) := zpow_pos (by norm_num) _
    have hy_max_pos : 0 < ((y_max : Dyadic) : ℝ) := by
      rw [hy_max_real]
      have : (0 : ℝ) < (c_max : ℝ) := by exact_mod_cast hc_max_pos
      exact mul_pos this h_2e2_pos
    have hy_max_in_ext2 : y_max ∈ (F₁_g p hp_ge_2 e).extend 2 := by
      refine ⟨?_, ?_, trivial⟩
      · change Dyadic.precisionAtMost ((((p : ℕ) : ℕ∞)) + (2 : ℕ)) y_max
        have h_eq : ((((p : ℕ) : ℕ∞)) + (2 : ℕ)) = ((p + 2 : ℕ) : ℕ∞) := by
          push_cast; ring
        rw [h_eq]
        refine ⟨c_max, e - 2, hy_max_real, ?_⟩
        rw [abs_of_pos hc_max_pos]; exact hc_max_lt
      · change Dyadic.quantumAtLeast (((e - 2 : ℤ)) : WithBot ℤ) y_max
        rw [Dyadic.quantumAtLeast_coe]; refine ⟨c_max, hy_max_real⟩
    have hy_max_in_F₂ : y_max ∈ F₂ := hsub _ hy_max_in_ext2
    -- Apply exists_grid_rep at F₂.
    obtain ⟨k, c, hk_ge_f₂, hc_lt_abs, hy_eq, hk_max⟩ :=
      exists_grid_rep F₂ hF₂_p hF₂_exp hy_max_in_F₂.1 hy_max_in_F₂.2.1 hy_max_pos
    have h_eq_real : (c : ℝ) * (2 : ℝ)^k = (c_max : ℝ) * (2 : ℝ)^(e - 2) := by
      rw [← hy_max_real, ← hy_eq]
    -- k ≤ e - 2 from c integer + c_max odd.
    have hk_le : k ≤ e - 2 := by
      by_contra h_gt
      push Not at h_gt
      -- Extract n : ℕ with (n : ℤ) = k - (e - 2) and 1 ≤ n.
      set n : ℕ := (k - (e - 2)).toNat with hn_def
      have h_n_eq : (n : ℤ) = k - (e - 2) := Int.toNat_of_nonneg (by omega)
      have h_n_ge_1 : 1 ≤ n := by
        have : (1 : ℤ) ≤ (n : ℤ) := by rw [h_n_eq]; omega
        exact_mod_cast this
      have h_2e2_ne : (2 : ℝ)^(e - 2) ≠ 0 := ne_of_gt h_2e2_pos
      -- From c·2^k = c_max·2^(e-2), divide by 2^(e-2):
      have h_real_eq2 : (c : ℝ) * (2 : ℝ)^(n : ℤ) = (c_max : ℝ) := by
        have h_split : (2 : ℝ)^k = (2 : ℝ)^(n : ℤ) * (2 : ℝ)^(e - 2) := by
          rw [show (k : ℤ) = (n : ℤ) + (e - 2) from by linarith [h_n_eq],
              zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        rw [h_split, ← mul_assoc] at h_eq_real
        exact mul_right_cancel₀ h_2e2_ne h_eq_real
      -- (2 : ℝ)^(n : ℤ) = (2 : ℕ)^n in ℝ.
      rw [zpow_natCast] at h_real_eq2
      -- Cast to ℤ.
      have h_int_eq : c * (2 : ℤ)^n = c_max := by
        have h_cast : ((c * (2 : ℤ)^n : ℤ) : ℝ) = ((c_max : ℤ) : ℝ) := by
          push_cast; exact h_real_eq2
        exact_mod_cast h_cast
      -- c_max = c · 2^n with n ≥ 1 ⇒ c_max even.
      have h_even : Even c_max := by
        rw [← h_int_eq, show (n : ℕ) = (n - 1) + 1 from by omega, pow_succ]
        refine ⟨c * (2 : ℤ)^(n - 1), ?_⟩
        ring
      exact (Int.not_even_iff_odd.mpr hc_max_odd) h_even
    -- Compute log y_max = e + p - 1.
    have h_log_y_max : Int.log 2 ((y_max : Dyadic) : ℝ) = e + p - 1 := by
      rw [hy_max_real]
      apply le_antisymm
      · -- Upper bound: c_max · 2^(e-2) < 2^(e+p).
        have h_lt : (c_max : ℝ) * (2 : ℝ)^(e - 2) < ((2 : ℕ) : ℝ)^(e + p) := by
          rw [show ((2 : ℕ) : ℝ) = 2 from by push_cast; rfl,
              show e + p = (e - 2) + (p + 2) by ring,
              zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          have h_2p_pow : (2 : ℝ)^((p + 2 : ℕ) : ℤ) = ((2 : ℤ)^(p + 2) : ℝ) := by
            rw [zpow_natCast]; push_cast; ring
          rw [show ((p + 2 : ℤ)) = ((p + 2 : ℕ) : ℤ) from by push_cast; rfl, h_2p_pow]
          have hc_max_lt_r : (c_max : ℝ) < ((2 : ℤ)^(p + 2) : ℝ) := by
            exact_mod_cast hc_max_lt
          nlinarith
        have hy_pos' : (0 : ℝ) < (c_max : ℝ) * (2 : ℝ)^(e - 2) := by
          rw [← hy_max_real]; exact hy_max_pos
        have := (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) hy_pos').mp h_lt
        omega
      · -- Lower bound: 2^(e+p-1) ≤ c_max · 2^(e-2).
        have h_ge : ((2 : ℕ) : ℝ)^(e + p - 1) ≤ (c_max : ℝ) * (2 : ℝ)^(e - 2) := by
          rw [show ((2 : ℕ) : ℝ) = 2 from by push_cast; rfl,
              show e + p - 1 = (e - 2) + (p + 1) by ring,
              zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          have h_2p1_pow : (2 : ℝ)^((p + 1 : ℕ) : ℤ) = ((2 : ℤ)^(p + 1) : ℝ) := by
            rw [zpow_natCast]; push_cast; ring
          rw [show ((p + 1 : ℤ)) = ((p + 1 : ℕ) : ℤ) from by push_cast; rfl, h_2p1_pow]
          have hc_max_ge : ((2 : ℤ)^(p + 1) : ℝ) ≤ (c_max : ℝ) := by
            have h_int : (2 : ℤ)^(p + 1) ≤ c_max := by
              rw [hc_max_def]
              have h_two_pp2 : (2 : ℤ)^(p + 2) = 2 * (2 : ℤ)^(p + 1) := by
                rw [show p + 2 = (p + 1) + 1 from by omega, pow_succ]; ring
              omega
            exact_mod_cast h_int
          nlinarith
        have hy_pos' : (0 : ℝ) < (c_max : ℝ) * (2 : ℝ)^(e - 2) := by
          rw [← hy_max_real]; exact hy_max_pos
        exact (Int.zpow_le_iff_le_log (by norm_num : 1 < (2 : ℕ)) hy_pos').mp h_ge
    rw [h_log_y_max] at hk_max
    have hk_eq : k = max f₂ (e + p - q₂) := by convert hk_max using 2; ring
    rw [hk_eq] at hk_le
    refine ⟨?_, ?_⟩
    · -- p + 2 ≤ q₂
      have h_part : e + p - (q₂ : ℤ) ≤ e - 2 := le_trans (le_max_right _ _) hk_le
      have hq_int : (p + 2 : ℤ) ≤ (q₂ : ℤ) := by omega
      exact_mod_cast hq_int
    · exact le_trans (le_max_left _ _) hk_le
  obtain ⟨hq₂, hf₂⟩ := hq₂_hf₂
  exact (no_rndRNE_RNE_arbitrary_F₂ p hp_ge_2 e F₂ hF₂_p hq₂ hF₂_exp hf₂ hF₂_b).2

end AbstractFormat

end Mpfx
