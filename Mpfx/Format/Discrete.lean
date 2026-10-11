import Mpfx.Format.Containment

/-!
# Discreteness: canonical representation and midpoints

A positive `y ∈ F` is `c · 2^(canonicalExp y)` with `|c| < 2^p`
(`exists_canonical_rep`, via `FiniteFormat.exists_mul_zpow_canonicalExp`), and the
midpoint of adjacent values lies in `F.extend 1`
(`midpoint_in_F₁_extend_one_of_F_adjacent`), the structural prerequisite for
`roundsRTO_RN_finite`. The closing facts place members on multiples of the
quantum (`quantum_floor_of_mem`/`quantum_ceil_of_mem`) and of the local binade
step (`binade_quantum`).

`canonicalExp` carries the spacing, so the format shapes need no separate
treatment.
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

/-- A positive `y` meeting `F`'s precision and quantum constraints is
`c · 2^(canonicalExp y)` with `|c| < 2^p`. `canonicalExp` absorbs the `max` with
`F.exp`, so this covers both exponent regimes
(Flocq `canonical_generic_format`). -/
theorem exists_canonical_rep_of_parts (F : FiniteFormat) {p : ℕ}
    (hp : F.p = (p : Prec))
    {y : Dyadic} (hp_y_full : Dyadic.precisionAtMost F.p y)
    (hq_y_full : Dyadic.quantumAtLeast F.exp y)
    (hy_pos : 0 < ((y : Dyadic) : ℝ)) :
    ∃ c : ℤ, |c| < (2 : ℤ) ^ p ∧
      ((y : Dyadic) : ℝ) =
        (c : ℝ) * (2 : ℝ) ^ (F.canonicalExp ((y : Dyadic) : ℝ)) := by
  have hy_ne : ((y : Dyadic) : ℝ) ≠ 0 := ne_of_gt hy_pos
  obtain ⟨m, hm⟩ := F.exists_mul_zpow_canonicalExp ⟨hp_y_full, hq_y_full, trivial⟩
  refine ⟨m, ?_, hm⟩
  set c := F.canonicalExp ((y : Dyadic) : ℝ)
  -- `|m|·2^c = |y| < 2^(⌊log₂|y|⌋ + 1) ≤ 2^(p + c)`.
  have hc := F.log_sub_p_le_canonicalExp hy_ne hp
  have hlt : |((y : Dyadic) : ℝ)| < (2 : ℝ) ^ (Int.log 2 |((y : Dyadic) : ℝ)| + 1) :=
    Int.lt_zpow_succ_log_self (by norm_num) _
  have h : |(m : ℝ)| * (2 : ℝ) ^ c < (2 : ℝ) ^ (p : ℤ) * (2 : ℝ) ^ c := by
    rw [← abs_mul_two_zpow, ← hm, ← zpow_add₀ two_ne_zero]
    exact hlt.trans_le (zpow_le_zpow_right₀ (by norm_num) (by omega))
  have h' := lt_of_mul_lt_mul_right h (zpow_pos two_pos c).le
  rw [zpow_natCast] at h'
  exact_mod_cast h'

/-- **Canonical representation.** A positive `y ∈ F` (precision `p`) is
`c · 2^(canonicalExp y)` with `|c| < 2^p`. Unifies the `exp = ⊥` and finite-`exp`
grid lemmas (both have step `= canonicalExp`). -/
theorem exists_canonical_rep (F : FiniteFormat) {p : ℕ}
    (hp : F.p = (p : Prec))
    {y : Dyadic} (hmem : y ∈ F) (hpos : 0 < (y : ℝ)) :
    ∃ c : ℤ, |c| < (2 : ℤ) ^ p ∧
      (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ (F.canonicalExp (y : ℝ)) :=
  have ⟨hprec, hquant, _⟩ := hmem
  exists_canonical_rep_of_parts F hp hprec hquant hpos

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

/-- For `y ∈ F` (any F shape), `midpoint(0, y) = y/2 ∈ F.extend 1`.
Handles both `F.exp = ⊥` and `F.exp = (e : ℤ)` cases. -/
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
  · -- quantumAtLeast ((F.exp).map (· - 1)).
    show Dyadic.quantumAtLeast (F.extend 1).exp _
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
  · -- bound: |y/2| ≤ b (midpoint of 0 and y).
    exact boundOK_midpoint (Format.boundOK_zero F.b) hb_y

/-- Midpoint of F-adjacent values, either sign: negative pairs reflect to the
positive case, and a pair at `0` is a halving. -/
private theorem midpoint_mem_extend_one_of_adjacent (F : FiniteFormat)
    {y₁ y₂ : Dyadic} (hy₁F : y₁ ∈ F) (hy₂F : y₂ ∈ F)
    (h_lt : ((y₁ : Dyadic) : ℝ) < ((y₂ : Dyadic) : ℝ))
    (h_adj : ∀ y : Dyadic, y ∈ F →
              ((y₁ : Dyadic) : ℝ) < ((y : Dyadic) : ℝ) →
              ((y₂ : Dyadic) : ℝ) ≤ ((y : Dyadic) : ℝ)) :
    Dyadic.midpoint y₁ y₂ ∈ F.extend 1 := by
  rcases lt_trichotomy ((y₁ : Dyadic) : ℝ) 0 with hy₁_neg | hy₁_zero | hy₁_pos
  · -- y₁ < 0. Either y₂ < 0 or y₂ = 0 or y₂ > 0.
    rcases lt_trichotomy ((y₂ : Dyadic) : ℝ) 0 with hy₂_neg | hy₂_zero | hy₂_pos
    · -- Both negative. Apply positive case to (-y₂, -y₁).
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
    · -- y₂ = 0. midpoint(y₁, 0) = y₁/2. Apply half_mem_extend_one to -y₁.
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
    · -- y₁ < 0 < y₂: F-adjacency violated since 0 ∈ F.
      exfalso
      have h_0_F : (0 : Dyadic) ∈ F := FiniteFormat.zero_mem F
      have h_0_gt : ((y₁ : Dyadic) : ℝ) < ((0 : Dyadic) : ℝ) := by
        rw [Dyadic.coe_real_zero]; exact hy₁_neg
      have h_y₂_le : ((y₂ : Dyadic) : ℝ) ≤ ((0 : Dyadic) : ℝ) := h_adj 0 h_0_F h_0_gt
      rw [Dyadic.coe_real_zero] at h_y₂_le
      linarith
  · -- y₁ = 0. midpoint = y₂/2 = midpoint 0 y₂.
    have h_y₁_eq_0 : y₁ = 0 := Dyadic.ext_real (by rw [Dyadic.coe_real_zero]; exact hy₁_zero)
    rw [h_y₁_eq_0]
    exact half_mem_extend_one F hy₂F
  · -- y₁ > 0.
    exact midpoint_mem_extend_one_of_adjacent_pos F hy₁F hy₂F hy₁_pos h_lt h_adj

/-- F-adjacent midpoint membership in `F₁.extend 1`, any format shape. -/
theorem midpoint_in_F₁_extend_one_of_F_adjacent {F₁ : FiniteFormat}
    {y₁ y₂ : Dyadic} (hy₁F : y₁ ∈ F₁) (hy₂F : y₂ ∈ F₁)
    (h_lt : (y₁ : ℝ) < (y₂ : ℝ))
    (h_adj : ∀ y : Dyadic, y ∈ F₁ → (y₁ : ℝ) < (y : ℝ) → (y₂ : ℝ) ≤ (y : ℝ)) :
    Dyadic.midpoint y₁ y₂ ∈ F₁.extend 1 :=
  midpoint_mem_extend_one_of_adjacent F₁ hy₁F hy₂F h_lt h_adj

/-! ### Grid facts

Members of `F` are integer multiples of the quantum `2^exp` and, within a
binade, of the local step. -/

/-- **Grid floor.** Given `target = c_target · 2^f₂` on F₂'s grid, any
`z ∈ F₂` strictly below `target + 2^f₂` is at most `target`. -/
theorem quantum_floor_of_mem
    {F₂ : Format} {f₂ : ℤ} (hF₂_exp : F₂.exp = (f₂ : QExp))
    {target : ℝ} {c_target : ℤ}
    (h_target_eq : target = (c_target : ℝ) * (2 : ℝ) ^ f₂) :
    ∀ z ∈ F₂, ((z : Dyadic) : ℝ) < target + (2 : ℝ)^f₂ →
      ((z : Dyadic) : ℝ) ≤ target := by
  intro z hz hz_lt
  obtain ⟨_, hq, _⟩ := hz
  rw [hF₂_exp, Dyadic.quantumAtLeast_coe_real] at hq
  obtain ⟨c, hc⟩ := hq
  rw [hc, h_target_eq, show (c_target : ℝ) * (2 : ℝ)^f₂ + (2 : ℝ)^f₂
        = ((c_target + 1 : ℤ) : ℝ) * (2 : ℝ)^f₂ from by push_cast; ring] at hz_lt
  rw [hc, h_target_eq]
  exact int_mul_two_zpow_le_iff.mpr (by have := int_mul_two_zpow_lt_iff.mp hz_lt; omega)

/-- **Grid ceiling** (dual of `quantum_floor_of_mem`). Given
`target = c_target · 2^f₂` on F₂'s grid, any `z ∈ F₂` strictly above
`target − 2^f₂` is at least `target`. -/
theorem quantum_ceil_of_mem
    {F₂ : Format} {f₂ : ℤ} (hF₂_exp : F₂.exp = (f₂ : QExp))
    {target : ℝ} {c_target : ℤ}
    (h_target_eq : target = (c_target : ℝ) * (2 : ℝ) ^ f₂) :
    ∀ z ∈ F₂, target - (2 : ℝ)^f₂ < ((z : Dyadic) : ℝ) →
      target ≤ ((z : Dyadic) : ℝ) := by
  intro z hz hz_gt
  obtain ⟨_, hq, _⟩ := hz
  rw [hF₂_exp, Dyadic.quantumAtLeast_coe_real] at hq
  obtain ⟨c, hc⟩ := hq
  rw [hc, h_target_eq, show (c_target : ℝ) * (2 : ℝ)^f₂ - (2 : ℝ)^f₂
        = ((c_target - 1 : ℤ) : ℝ) * (2 : ℝ)^f₂ from by push_cast; ring] at hz_gt
  rw [hc, h_target_eq]
  exact int_mul_two_zpow_le_iff.mpr (by have := int_mul_two_zpow_lt_iff.mp hz_gt; omega)

/-- **Binade quantization.** In a format with finite precision `q₂`, every
element of the binade `[2^E, 2^(E+1))` is an integer multiple of the local
step `2^(E − q₂ + 1)`. -/
theorem binade_quantum {F₂ : FiniteFormat} {q₂ : ℕ}
    (hp : F₂.p = (q₂ : Prec)) {E : ℤ} {y : Dyadic}
    (hy : y ∈ F₂.toFormat)
    (h_lo : (2 : ℝ) ^ E ≤ ((y : Dyadic) : ℝ))
    (_h_hi : ((y : Dyadic) : ℝ) < (2 : ℝ) ^ (E + 1)) :
    ∃ c : ℤ, ((y : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ)^(E - q₂ + 1) := by
  have hprec : Dyadic.precisionAtMost F₂.p y := hy.1
  rw [hp, Dyadic.precisionAtMost_coe_real] at hprec
  obtain ⟨c, k, hck, hc_lt⟩ := hprec
  have h2E_pos : (0 : ℝ) < (2 : ℝ)^E := zpow_pos (by norm_num) _
  have h2k_pos : (0 : ℝ) < (2 : ℝ)^k := zpow_pos (by norm_num) _
  have hc_real_lt : (c : ℝ) < (2 : ℝ)^(q₂ : ℤ) := by
    have h1 : (c : ℝ) ≤ ((|c| : ℤ) : ℝ) := by
      rw [Int.cast_abs]; exact le_abs_self _
    have h2 : ((|c| : ℤ) : ℝ) < (((2 : ℤ)^q₂ : ℤ) : ℝ) := by
      exact_mod_cast hc_lt
    have h3 : (((2 : ℤ)^q₂ : ℤ) : ℝ) = (2 : ℝ)^(q₂ : ℤ) := by
      push_cast
      rw [← zpow_natCast (2 : ℝ) q₂]
    linarith
  have hk_ge : E - q₂ + 1 ≤ k := by
    by_contra h
    push Not at h
    have h_y_lt : ((y : Dyadic) : ℝ) < (2 : ℝ)^E := by
      rw [hck]
      calc (c : ℝ) * (2 : ℝ)^k
          < (2 : ℝ)^(q₂ : ℤ) * (2 : ℝ)^k := by nlinarith
        _ = (2 : ℝ)^((q₂ : ℤ) + k) := by
            rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        _ ≤ (2 : ℝ)^E := zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith
  refine ⟨c * 2^((k - (E - q₂ + 1)).toNat), ?_⟩
  rw [hck, two_zpow_split k (E - q₂ + 1) hk_ge]
  push_cast; ring

end Mpfx
