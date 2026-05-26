import Mpfx2.Containment

namespace Mpfx2

/-- `F.numDigits x ≤ 1` whenever `F.p = 1`. When the precision is a single
binary digit, the format rounds every value to `±2^e`, so its effective
digit count never exceeds one. -/
theorem FiniteFormat.numDigits_le_one_of_p_one {F : FiniteFormat}
    (hp1 : F.toFormat.p = ((1 : ℕ+) : WithTop ℕ+)) (x : ℝ) :
    F.numDigits x ≤ 1 := by
  unfold FiniteFormat.numDigits
  by_cases hx : x = 0
  · simp [hx]
  · simp only [hx, ↓reduceIte]
    -- `F.p = 1`, so only the `(p, ⊥)` and `(p, e')` branches apply.
    cases hexp : F.toFormat.exp with
    | bot =>
      rw [hp1]
      change ((1 : ℕ) : ℤ) ≤ 1
      norm_num
    | coe e' =>
      rw [hp1]
      change min ((1 : ℕ) : ℤ) (Int.log 2 |x| - e' + 1) ≤ 1
      exact min_le_left _ _

/-- **Lemma 5.3 corollary** (format-parameterized form): If `y` has precision
at most `w` and the rounding precision in `F` (= `numDigits F y`) strictly
exceeds `w`, then `y` cannot be `IsOdd F`. -/
theorem ParityFormat.precisionAtMost_not_IsOdd {F : ParityFormat} {w : ℕ+} {y : Dyadic}
    (hgt : ((w : ℕ) : ℤ) < F.toFiniteFormat.numDigits (y : ℝ))
    (hprec : Dyadic.precisionAtMost ((w : ℕ+) : WithTop ℕ+) y) :
    ¬ F.IsOdd y := by
  intro hodd
  obtain ⟨c₁, e₁, ⟨hy_eq₁, hlow, _hhigh⟩, hp_check⟩ := hodd
  set p_y : ℕ := (F.toFiniteFormat.numDigits (y : ℝ)).toNat with hp_y_def
  have h_nd_pos : 0 ≤ F.toFiniteFormat.numDigits (y : ℝ) := by
    have : (0 : ℤ) ≤ ((w : ℕ) : ℤ) := by positivity
    linarith
  have h_pyZ : (p_y : ℤ) = F.toFiniteFormat.numDigits (y : ℝ) := Int.toNat_of_nonneg h_nd_pos
  have hp_y_ge : p_y ≥ (w : ℕ) + 1 := by
    have : (p_y : ℤ) ≥ ((w : ℕ) : ℤ) + 1 := by rw [h_pyZ]; linarith
    exact_mod_cast this
  -- Show `F.p ≠ 1` (else `numDigits F y ≤ 1`, but `numDigits ≥ w + 1 ≥ 2`).
  have hFp_ne_1 : F.toFormat.p ≠ ((1 : ℕ+) : WithTop ℕ+) := by
    intro hFp1
    have h_le := F.toFiniteFormat.numDigits_le_one_of_p_one hFp1 (y : ℝ)
    have h1 : (p_y : ℤ) ≤ 1 := by rw [h_pyZ]; exact h_le
    have h2 : p_y ≤ 1 := by exact_mod_cast h1
    have hw_pos : 1 ≤ (w : ℕ) := w.pos
    omega
  rw [if_neg hFp_ne_1] at hp_check
  have hc₁_odd : Odd c₁ := hp_check
  set k : ℕ := p_y - (w : ℕ) with hk_def
  have hpyw : p_y = (w : ℕ) + k := by omega
  -- Unpack the precision witness for `y` (over ℚ).
  rw [Dyadic.precisionAtMost_coe] at hprec
  obtain ⟨c₂, e₂, hy_eq₂, hc₂_low⟩ := hprec
  have heq_rat : (c₁ : ℚ) * (2 : ℚ) ^ e₁ = (c₂ : ℚ) * (2 : ℚ) ^ e₂ := by
    rw [← hy_eq₁]; exact hy_eq₂
  have h2ne : (2 : ℚ) ≠ 0 := two_ne_zero
  have h2pos : (0 : ℚ) < 2 := by norm_num
  rcases lt_or_ge e₁ e₂ with he | he
  · -- `e₁ < e₂`: `c₁ = c₂ · 2^(e₂-e₁)` is even, contradicting `Odd c₁`.
    have h_nat : ((e₂ - e₁).toNat : ℤ) = e₂ - e₁ := Int.toNat_of_nonneg (by omega)
    have heq_int : c₁ = c₂ * 2 ^ (e₂ - e₁).toNat := by
      have h_rat : (c₁ : ℚ) = (c₂ : ℚ) * (2 : ℚ) ^ (e₂ - e₁).toNat := by
        rw [show ((2 : ℚ) ^ (e₂ - e₁).toNat : ℚ) = (2 : ℚ) ^ ((e₂ - e₁).toNat : ℤ) from
            (zpow_natCast _ _).symm, h_nat]
        have h_step : (c₂ : ℚ) * (2 : ℚ) ^ (e₂ - e₁) * (2 : ℚ) ^ e₁
            = (c₁ : ℚ) * (2 : ℚ) ^ e₁ := by
          rw [mul_assoc, ← zpow_add₀ h2ne, show e₂ - e₁ + e₁ = e₂ from by ring]
          exact heq_rat.symm
        have h2e₁_pos : (0 : ℚ) < (2 : ℚ) ^ e₁ := zpow_pos h2pos _
        exact (mul_right_cancel₀ (ne_of_gt h2e₁_pos) h_step).symm
      exact_mod_cast h_rat
    have h_even : Even c₁ := by
      rw [heq_int,
          show (e₂ - e₁).toNat = ((e₂ - e₁).toNat - 1) + 1 from by omega, pow_succ]
      exact ⟨c₂ * 2 ^ ((e₂ - e₁).toNat - 1), by ring⟩
    exact (Int.not_even_iff_odd.mpr hc₁_odd) h_even
  · -- `e₁ ≥ e₂`: `|c₂| = |c₁| · 2^(e₁-e₂) ≥ 2^(p_y-1) ≥ 2^w`, contradicting `|c₂| < 2^w`.
    have h_nat : ((e₁ - e₂).toNat : ℤ) = e₁ - e₂ := Int.toNat_of_nonneg (by omega)
    have heq_int : c₂ = c₁ * 2 ^ (e₁ - e₂).toNat := by
      have h_rat : (c₂ : ℚ) = (c₁ : ℚ) * (2 : ℚ) ^ (e₁ - e₂).toNat := by
        rw [show ((2 : ℚ) ^ (e₁ - e₂).toNat : ℚ) = (2 : ℚ) ^ ((e₁ - e₂).toNat : ℤ) from
            (zpow_natCast _ _).symm, h_nat]
        have h_step : (c₁ : ℚ) * (2 : ℚ) ^ (e₁ - e₂) * (2 : ℚ) ^ e₂
            = (c₂ : ℚ) * (2 : ℚ) ^ e₂ := by
          rw [mul_assoc, ← zpow_add₀ h2ne, show e₁ - e₂ + e₂ = e₁ from by ring]
          exact heq_rat
        have h2e₂_pos : (0 : ℚ) < (2 : ℚ) ^ e₂ := zpow_pos h2pos _
        exact (mul_right_cancel₀ (ne_of_gt h2e₂_pos) h_step).symm
      exact_mod_cast h_rat
    have h_abs : |c₂| = |c₁| * 2 ^ (e₁ - e₂).toNat := by
      rw [heq_int, abs_mul, abs_pow]; congr 1
    -- `2^(p_y - 1) ≤ |c₁|` (the low bound of `IsRepresentableAtP`).
    have hlow' : (2 : ℤ) ^ (p_y - 1) ≤ |c₁| := hlow
    have hpow_le : (2 : ℤ) ^ (w : ℕ) ≤ (2 : ℤ) ^ (p_y - 1) := by
      apply pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
      have hw_pos : 1 ≤ (w : ℕ) := w.pos
      omega
    have h2pow_pos : (0 : ℤ) < 2 ^ (e₁ - e₂).toNat := by positivity
    have h_one_le : (1 : ℤ) ≤ 2 ^ (e₁ - e₂).toNat := h2pow_pos
    have h_chain : (2 : ℤ) ^ (w : ℕ) ≤ |c₂| := by
      calc (2 : ℤ) ^ (w : ℕ)
          ≤ (2 : ℤ) ^ (p_y - 1) := hpow_le
        _ ≤ |c₁| := hlow'
        _ = |c₁| * 1 := (mul_one _).symm
        _ ≤ |c₁| * 2 ^ (e₁ - e₂).toNat :=
            mul_le_mul_of_nonneg_left h_one_le (abs_nonneg _)
        _ = |c₂| := h_abs.symm
    exact absurd (lt_of_le_of_lt h_chain hc₂_low) (lt_irrefl _)

end Mpfx2
