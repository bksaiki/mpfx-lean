import Mpfx.Format.Containment

/-!
# Discreteness: canonical representation and midpoints

A positive `y ∈ F` is `c · 2^(canonicalExp y)` with `|c| < 2^p`
(`exists_canonical_rep`, via `FiniteFormat.exists_mul_zpow_canonicalExp`), and the
midpoint of adjacent values lies in `F.extend 1`
(`midpoint_in_F₁_extend_one_of_F_adjacent`), the structural prerequisite for
`roundsRTO_RN_finite`.
-/

namespace Mpfx

/-- If `y₁` and `y₂` both satisfy the magnitude bound `B`, so does their
midpoint (triangle inequality over `ℚ`). -/
private theorem boundOK_midpoint {B : Bound} {y₁ y₂ : Dyadic}
    (h₁ : Format.boundOK B y₁) (h₂ : Format.boundOK B y₂) :
    Format.boundOK B (Dyadic.midpoint y₁ y₂) := by
  cases B using Bound.recTopCoe with
  | top => trivial
  | coe B =>
    change |((Dyadic.midpoint y₁ y₂ : Dyadic) : ℚ)| ≤ ((B.val : Dyadic) : ℚ)
    change |((y₁ : Dyadic) : ℚ)| ≤ ((B.val : Dyadic) : ℚ) at h₁
    change |((y₂ : Dyadic) : ℚ)| ≤ ((B.val : Dyadic) : ℚ) at h₂
    rw [Dyadic.coe_rat_midpoint, abs_div, abs_of_pos (by norm_num : (0 : ℚ) < 2)]
    have h_tri : |((y₁ : Dyadic) : ℚ) + ((y₂ : Dyadic) : ℚ)|
        ≤ |((y₁ : Dyadic) : ℚ)| + |((y₂ : Dyadic) : ℚ)| := abs_add_le _ _
    linarith

/-- **Canonical representation.** A positive `y ∈ F` (precision `p`) is
`c · 2^(canonicalExp y)` with `|c| < 2^p` (Flocq `canonical_generic_format`). -/
theorem exists_canonical_rep (F : FiniteFormat) {p : ℕ}
    (hp : F.p = (p : Prec))
    {y : Dyadic} (hmem : y ∈ F) (hpos : 0 < (y : ℝ)) :
    ∃ c : ℤ, |c| < (2 : ℤ) ^ p ∧
      (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ (F.canonicalExp (y : ℝ)) := by
  obtain ⟨m, hm⟩ := F.exists_mul_zpow_canonicalExp (mem_unbounded_of_mem hmem)
  exact ⟨m, F.abs_lt_of_mul_zpow_canonicalExp hp hpos.ne' hm, hm⟩

/-- **Midpoint of adjacent positive values.** The next power of two above `y₁`
is at least `y₂`, so the midpoint stays in `y₁`'s binade and has `y₁`'s step
`2^c`. Both endpoints are multiples of `2^c`, so the midpoint is a multiple of
`2^(c−1)`, the step of `F.extend 1` there. -/
theorem midpoint_mem_extend_one_of_adjacent_pos (F : FiniteFormat)
    {y₁ y₂ : Dyadic} (hy₁F : y₁ ∈ F) (hy₂F : y₂ ∈ F)
    (h_pos : 0 < ((y₁ : Dyadic) : ℝ))
    (h_lt : ((y₁ : Dyadic) : ℝ) < ((y₂ : Dyadic) : ℝ))
    (h_adj : ∀ y : Dyadic, y ∈ F →
              ((y₁ : Dyadic) : ℝ) < ((y : Dyadic) : ℝ) →
              ((y₂ : Dyadic) : ℝ) ≤ ((y : Dyadic) : ℝ)) :
    Dyadic.midpoint y₁ y₂ ∈ F.extend 1 := by
  set m := Dyadic.midpoint y₁ y₂
  have hm : ((m : Dyadic) : ℝ) = (((y₁ : Dyadic) : ℝ) + ((y₂ : Dyadic) : ℝ)) / 2 :=
    Dyadic.coe_midpoint y₁ y₂
  set c := F.canonicalExp ((y₁ : Dyadic) : ℝ)
  set L := Int.log 2 ((y₁ : Dyadic) : ℝ)
  have hy₂_pos : 0 < ((y₂ : Dyadic) : ℝ) := h_pos.trans h_lt
  have hlo : (2 : ℝ) ^ L ≤ ((y₁ : Dyadic) : ℝ) := by
    have := Int.zpow_log_le_self (b := 2) (by norm_num) h_pos; exact_mod_cast this
  have hhi : ((y₁ : Dyadic) : ℝ) < (2 : ℝ) ^ (L + 1) := Int.lt_zpow_succ_log_self (by norm_num) _
  -- `y₂ ≤ 2^(L+1)`: that power of two is a value of `F` above `y₁`, or out of bound.
  have hy₂_le : ((y₂ : Dyadic) : ℝ) ≤ (2 : ℝ) ^ (L + 1) := by
    by_cases hb : Format.boundOK F.b (Dyadic.ofIntZpow 1 (L + 1))
    · have hexp : F.exp ≤ ((L + 1 : ℤ) : QExp) := by
        cases he : F.exp using QExp.recBotCoe with
        | bot => exact bot_le
        | coe e =>
          have := exp_le_log_of_mem F he (mem_unbounded_of_mem hy₁F) h_pos
          exact WithBot.coe_le_coe.mpr (by omega)
      have := h_adj _ (Format.ofIntZpow_mem (precisionAtMost_one_zpow F.pos _) hexp hb)
        (by rw [coe_real_ofIntZpow_one]; exact hhi)
      rwa [coe_real_ofIntZpow_one] at this
    · by_contra hgt
      push Not at hgt
      exact hb (boundOK_of_abs_le (by
        rw [coe_real_ofIntZpow_one, abs_of_pos (zpow_pos two_pos _), abs_of_pos hy₂_pos]
        exact hgt.le) hy₂F.2.2)
  have hm0 : 0 < ((m : Dyadic) : ℝ) := by rw [hm]; linarith
  have hcm : F.canonicalExp ((m : Dyadic) : ℝ) = c := by
    refine canonicalExp_eq_of_log_eq F hm0.ne' h_pos.ne' ?_
    rw [abs_of_pos hm0, abs_of_pos h_pos]
    exact log_eq_of_zpow_bounds hm0 (by rw [hm]; linarith) (by rw [hm]; linarith)
  obtain ⟨a, ha⟩ := F.exists_mul_zpow_canonicalExp (mem_unbounded_of_mem hy₁F)
  have hc₂ : c ≤ F.canonicalExp ((y₂ : Dyadic) : ℝ) :=
    F.canonicalExp_mono h_pos.ne' (by rw [abs_of_pos h_pos, abs_of_pos hy₂_pos]; exact h_lt.le)
  obtain ⟨b, hb⟩ : ∃ b : ℤ, ((y₂ : Dyadic) : ℝ) = b * (2 : ℝ) ^ c := by
    obtain ⟨b, hb⟩ := F.exists_mul_zpow_canonicalExp (mem_unbounded_of_mem hy₂F)
    exact ⟨_, hb.trans (two_zpow_shift b hc₂)⟩
  have ha' : ((y₁ : Dyadic) : ℝ) = a * (2 : ℝ) ^ c := ha
  refine mem_of_mem_unbounded_of_boundOK
    ((F.extend 1).mem_unbounded_of_mul_zpow_canonicalExp (m := a + b) ?_)
    (boundOK_midpoint hy₁F.2.2 hy₂F.2.2)
  rw [F.canonicalExp_extend 1 hm0.ne', hcm, hm, ha', hb, zpow_sub₀ two_ne_zero]
  push_cast; field_simp

/-- For `y ∈ F`, `midpoint(0, y) = y/2 ∈ F.extend 1`. -/
private theorem half_mem_extend_one (F : FiniteFormat)
    {y : Dyadic} (hyF : y ∈ F) :
    (Dyadic.midpoint 0 y : Dyadic) ∈ F.extend 1 := by
  obtain ⟨hp_y, hq_y, hb_y⟩ := hyF
  have h_mid_eq : ((Dyadic.midpoint 0 y : Dyadic) : ℝ) = ((y : Dyadic) : ℝ) / 2 := by
    rw [Dyadic.coe_midpoint]; push_cast; ring
  have h_mid_eq_rat : ((Dyadic.midpoint 0 y : Dyadic) : ℚ) = ((y : Dyadic) : ℚ) / 2 := by
    rw [Dyadic.coe_rat_midpoint]; push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · -- Halving keeps the significand, so the precision is unchanged.
    change Dyadic.precisionAtMost (F.p + ((1 : ℕ) : Prec)) _
    refine Dyadic.precisionAtMost_mono (le_add_right le_rfl) ?_
    cases hpF : F.p using ENat.recTopCoe with
    | top => trivial
    | coe p =>
      have hp_y' : Dyadic.precisionAtMost (p : Prec) y := hpF ▸ hp_y
      rw [Dyadic.precisionAtMost_coe] at hp_y' ⊢
      obtain ⟨c, e, hy_eq, hc_lt⟩ := hp_y'
      refine ⟨c, e - 1, ?_, hc_lt⟩
      rw [h_mid_eq_rat, hy_eq, zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0)]
      field_simp
  · show Dyadic.quantumAtLeast (F.extend 1).exp _
    have h_exp_eq : (F.extend 1).exp = F.exp.map (· - ((1 : ℕ) : ℤ)) := rfl
    rw [h_exp_eq]
    cases hF_exp : F.exp using QExp.recBotCoe with
    | bot => trivial
    | coe e =>
      rw [WithBot.map_coe]
      change Dyadic.quantumAtLeast (((e - (1 : ℕ)) : ℤ) : QExp) _
      rw [Dyadic.quantumAtLeast_coe]
      rw [hF_exp] at hq_y
      rw [Dyadic.quantumAtLeast_coe] at hq_y
      obtain ⟨c, hy_eq⟩ := hq_y
      refine ⟨c, ?_⟩
      rw [h_mid_eq_rat, hy_eq]
      have : ((1 : ℕ) : ℤ) = 1 := rfl
      rw [this, zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0)]
      field_simp
  · exact boundOK_midpoint (Format.boundOK_zero F.b) hb_y

/-- **Midpoint of adjacent values**, either sign, lies in `F.extend 1`: negative
pairs reflect to the positive case, and a pair at `0` is a halving. -/
theorem midpoint_in_F₁_extend_one_of_F_adjacent {F : FiniteFormat}
    {y₁ y₂ : Dyadic} (hy₁F : y₁ ∈ F) (hy₂F : y₂ ∈ F)
    (h_lt : ((y₁ : Dyadic) : ℝ) < ((y₂ : Dyadic) : ℝ))
    (h_adj : ∀ y : Dyadic, y ∈ F →
              ((y₁ : Dyadic) : ℝ) < ((y : Dyadic) : ℝ) →
              ((y₂ : Dyadic) : ℝ) ≤ ((y : Dyadic) : ℝ)) :
    Dyadic.midpoint y₁ y₂ ∈ F.extend 1 := by
  rcases lt_trichotomy ((y₁ : Dyadic) : ℝ) 0 with hy₁_neg | hy₁_zero | hy₁_pos
  · rcases lt_trichotomy ((y₂ : Dyadic) : ℝ) 0 with hy₂_neg | hy₂_zero | hy₂_pos
    · -- Both negative: apply the positive case to `(-y₂, -y₁)`.
      have h_neg_y₁_pos : 0 < ((-y₁ : Dyadic) : ℝ) := by push_cast; linarith
      have h_neg_y₂_pos : 0 < ((-y₂ : Dyadic) : ℝ) := by push_cast; linarith
      have h_lt' : ((-y₂ : Dyadic) : ℝ) < ((-y₁ : Dyadic) : ℝ) := by push_cast; linarith
      have h_adj' : ∀ y : Dyadic, y ∈ F →
          ((-y₂ : Dyadic) : ℝ) < ((y : Dyadic) : ℝ) →
          ((-y₁ : Dyadic) : ℝ) ≤ ((y : Dyadic) : ℝ) := by
        intro y hyF hyg
        by_contra h_lt_neg
        push Not at h_lt_neg
        have h_neg_yF : -y ∈ F := FiniteFormat.neg_mem hyF
        have h_y_gt_y₁ : ((y₁ : Dyadic) : ℝ) < ((-y : Dyadic) : ℝ) := by
          push_cast at h_lt_neg ⊢; linarith
        have h_y_le_y₂ := h_adj (-y) h_neg_yF h_y_gt_y₁
        push_cast at hyg h_y_le_y₂
        linarith
      have h_neg_in_extend := midpoint_mem_extend_one_of_adjacent_pos F
        (FiniteFormat.neg_mem hy₂F) (FiniteFormat.neg_mem hy₁F)
        h_neg_y₂_pos h_lt' h_adj'
      have h_mid_neg : Dyadic.midpoint (-y₂) (-y₁) = -(Dyadic.midpoint y₁ y₂) := by
        apply Dyadic.ext_real
        simp only [Dyadic.coe_midpoint, Dyadic.coe_real_neg]
        ring
      rw [h_mid_neg] at h_neg_in_extend
      have := FiniteFormat.neg_mem h_neg_in_extend
      rw [neg_neg] at this
      exact this
    · -- `y₂ = 0`: halve `-y₁`.
      have h_y₂_eq_0 : y₂ = 0 := Dyadic.ext_real (by rw [Dyadic.coe_real_zero]; exact hy₂_zero)
      rw [h_y₂_eq_0]
      have h_mid_eq : Dyadic.midpoint y₁ 0 = -(Dyadic.midpoint 0 (-y₁)) := by
        apply Dyadic.ext_real
        simp only [Dyadic.coe_midpoint, Dyadic.coe_real_neg]
        push_cast; ring
      rw [h_mid_eq]
      have h_neg_y₁F : -y₁ ∈ F := FiniteFormat.neg_mem hy₁F
      have h_half := half_mem_extend_one F h_neg_y₁F
      exact FiniteFormat.neg_mem h_half
    · -- `y₁ < 0 < y₂` contradicts adjacency, since `0 ∈ F`.
      exfalso
      have h_0_F : (0 : Dyadic) ∈ F := FiniteFormat.zero_mem F
      have h_0_gt : ((y₁ : Dyadic) : ℝ) < ((0 : Dyadic) : ℝ) := by
        rw [Dyadic.coe_real_zero]; exact hy₁_neg
      have h_y₂_le : ((y₂ : Dyadic) : ℝ) ≤ ((0 : Dyadic) : ℝ) := h_adj 0 h_0_F h_0_gt
      rw [Dyadic.coe_real_zero] at h_y₂_le
      linarith
  · have h_y₁_eq_0 : y₁ = 0 := Dyadic.ext_real (by rw [Dyadic.coe_real_zero]; exact hy₁_zero)
    rw [h_y₁_eq_0]
    exact half_mem_extend_one F hy₂F
  · exact midpoint_mem_extend_one_of_adjacent_pos F hy₁F hy₂F hy₁_pos h_lt h_adj

end Mpfx
