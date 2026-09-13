import Mathlib.Tactic
import Mathlib.Data.Int.Log

/-!
# Project-agnostic helpers

Pure-Mathlib lemmas that arise repeatedly in the formalization.
Nothing here mentions `Dyadic` or `Format`.
-/

namespace Mpfx

/-- `|c · 2^e| = |c| · 2^e` for `c : ℝ, e : ℤ`. -/
lemma abs_mul_two_zpow (c : ℝ) (e : ℤ) :
    |c * (2 : ℝ) ^ e| = |c| * (2 : ℝ) ^ e := by
  rw [abs_mul, abs_zpow, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- Split `2 ^ e₁ = 2 ^ (e₁ - e₂).toNat * 2 ^ e₂` when `e₂ ≤ e₁`. -/
lemma two_zpow_split_toNat {e₁ e₂ : ℤ} (h : e₂ ≤ e₁) :
    (2 : ℝ) ^ e₁ = (2 : ℝ) ^ (e₁ - e₂).toNat * (2 : ℝ) ^ e₂ := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hsub : ((e₁ - e₂).toNat : ℤ) = e₁ - e₂ := Int.toNat_of_nonneg (by omega)
  rw [show ((2 : ℝ) ^ (e₁ - e₂).toNat : ℝ) = (2 : ℝ) ^ ((e₁ - e₂).toNat : ℤ) from
      (zpow_natCast _ _).symm, ← zpow_add₀ h2, hsub]
  congr 1; ring

/-- `(2:ℝ)^(e - f) = ((2:ℤ)^(e - f).toNat : ℝ)` when `f ≤ e`. -/
lemma two_zpow_diff_eq (e f : ℤ) (h : f ≤ e) :
    (2 : ℝ) ^ (e - f) = ((2 : ℤ) ^ (e - f).toNat : ℝ) := by
  have hn_eq : ((e - f).toNat : ℤ) = e - f := Int.toNat_of_nonneg (by omega)
  rw [show (2 : ℝ) ^ (e - f) = (2 : ℝ) ^ (((e - f).toNat : ℤ) : ℤ) by rw [hn_eq],
      zpow_natCast]
  push_cast; ring

/-- `(2:ℝ)^e = ((2:ℤ)^n : ℝ) * (2:ℝ)^f` where `n = (e - f).toNat`, when `f ≤ e`. -/
lemma two_zpow_split (e f : ℤ) (h : f ≤ e) :
    (2 : ℝ) ^ e = ((2 : ℤ) ^ (e - f).toNat : ℝ) * (2 : ℝ) ^ f := by
  have h_split : (2 : ℝ) ^ e = (2 : ℝ) ^ (e - f) * (2 : ℝ) ^ f := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
  rw [h_split, two_zpow_diff_eq e f h]

/-- `2^f = 4 · 2^(f − 2)`. -/
lemma two_zpow_split_minus_two (f : ℤ) :
    (2 : ℝ) ^ f = 4 * (2 : ℝ) ^ (f - 2) := by
  have h_eq : (2 : ℝ) ^ f = (2 : ℝ) ^ (f - 2) * (2 : ℝ) ^ (2 : ℤ) := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
  rw [h_eq, show (2 : ℝ) ^ (2 : ℤ) = 4 by norm_num]; ring

/-- Re-base a canonical rep to a coarser exponent (ℝ): shift `(c:ℝ)·2^e` down to
quantum `k ≤ e`, folding the extra powers of two into an integer coefficient. -/
lemma two_zpow_shift_real (c : ℤ) {e k : ℤ} (h : k ≤ e) :
    (c : ℝ) * (2 : ℝ) ^ e = ((c * (2 : ℤ) ^ (e - k).toNat : ℤ) : ℝ) * (2 : ℝ) ^ k := by
  rw [two_zpow_split e k h]; push_cast; ring

/-- Re-base a canonical rep to a coarser exponent (ℚ), the ℚ twin of
`two_zpow_shift_real`. -/
lemma two_zpow_shift_rat (c : ℤ) {e k : ℤ} (h : k ≤ e) :
    (c : ℚ) * (2 : ℚ) ^ e = ((c * (2 : ℤ) ^ (e - k).toNat : ℤ) : ℚ) * (2 : ℚ) ^ k := by
  have hn : ((e - k).toNat : ℤ) = e - k := Int.toNat_of_nonneg (by omega)
  have hsplit : (2 : ℚ) ^ e = (2 : ℚ) ^ ((e - k).toNat : ℤ) * (2 : ℚ) ^ k := by
    rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), hn]; congr 1; ring
  rw [hsplit, zpow_natCast]; push_cast; ring

/-- Inverse of the shift (ℝ): if two canonical reps of the same real agree with
`e₁ ≤ e₂`, the finer coefficient is the coarser one scaled by `2^(e₂-e₁)`. -/
lemma coeff_eq_of_shift_real {c₁ c₂ e₁ e₂ : ℤ} (h : e₁ ≤ e₂)
    (heq : (c₁ : ℝ) * (2 : ℝ) ^ e₁ = (c₂ : ℝ) * (2 : ℝ) ^ e₂) :
    c₁ = c₂ * (2 : ℤ) ^ (e₂ - e₁).toNat := by
  rw [two_zpow_shift_real c₂ h] at heq
  have h2 : (0 : ℝ) < (2 : ℝ) ^ e₁ := zpow_pos (by norm_num) _
  exact_mod_cast mul_right_cancel₀ (ne_of_gt h2) heq

/-- Inverse of the shift (ℚ), the ℚ twin of `coeff_eq_of_shift_real`. -/
lemma coeff_eq_of_shift_rat {c₁ c₂ e₁ e₂ : ℤ} (h : e₁ ≤ e₂)
    (heq : (c₁ : ℚ) * (2 : ℚ) ^ e₁ = (c₂ : ℚ) * (2 : ℚ) ^ e₂) :
    c₁ = c₂ * (2 : ℤ) ^ (e₂ - e₁).toNat := by
  rw [two_zpow_shift_rat c₂ h] at heq
  have h2 : (0 : ℚ) < (2 : ℚ) ^ e₁ := zpow_pos (by norm_num) _
  exact_mod_cast mul_right_cancel₀ (ne_of_gt h2) heq

/-- If `z·x ≥ 0` and `0 < x`, then `0 ≤ z`. -/
lemma nonneg_of_mul_nonneg_pos {z x : ℝ} (h_sign : z * x ≥ 0) (hx : 0 < x) :
    0 ≤ z := by
  rcases le_or_gt 0 z with h | h
  · exact h
  · exfalso; nlinarith

/-- Extract one factor of `2` from `(2 : ℤ) ^ k` when `k ≥ 1`. -/
lemma Int.two_pow_succ_pred {k : ℕ} (hk : 1 ≤ k) :
    (2 : ℤ) ^ k = 2 * (2 : ℤ) ^ (k - 1) := by
  conv_lhs => rw [show k = (k - 1) + 1 from by omega]
  rw [pow_succ]; ring

/-- The absolute value of an odd integer is odd. -/
lemma Odd.abs {c : ℤ} (hodd : Odd c) : Odd |c| := by
  rcases hodd with ⟨k, hk⟩
  rcases lt_trichotomy c 0 with h | h | h
  · rw [abs_of_neg h]; exact ⟨-k - 1, by linarith⟩
  · simp [h] at hk; omega
  · rw [abs_of_pos h]; exact ⟨k, hk⟩


/-! ### Sign and power helpers (used by the double-rounding development) -/

/-- `|1| < 2^p` for any positive precision. -/
theorem abs_one_lt_two_pow {p : ℕ} (hp : 0 < p) : |(1 : ℤ)| < 2 ^ p := by
  have h2 : (2 : ℤ) ^ 1 ≤ (2 : ℤ) ^ p := pow_le_pow_right₀ (by norm_num) hp
  simp only [abs_one]
  omega

/-- Sign-transitivity through a nonzero pivot: if `y·x ≥ 0` and `z·x ≥ 0`,
and `x = 0` implies `y = 0`, then `y·z ≥ 0`. -/
theorem mul_nonneg_of_common_sign {x : ℝ} {y z : ℝ}
    (hyx : y * x ≥ 0) (hzx : z * x ≥ 0) (hy0 : x = 0 → y = 0) :
    y * z ≥ 0 := by
  rcases eq_or_ne x 0 with hx | hx
  · rw [hy0 hx, zero_mul]
  · have hx2 : 0 < x ^ 2 := by positivity
    nlinarith [mul_nonneg hyx hzx]


/-! ### Scaled-mantissa arithmetic

Floor/ceiling and `Int.log` facts about `x · 2^(-e)`. The format-dependent
companions are in `Mpfx/CanonicalExp.lean`. -/

/-- For `r` with `|r| < N`, the floor `⌊r⌋` has `|⌊r⌋| ≤ N`. The
asymmetry: negative floors can saturate (e.g. `⌊-1.5⌋ = -2` with
`|-1.5| < 2` but `|⌊-1.5⌋| = 2`). -/
theorem abs_floor_le_of_abs_lt {r : ℝ} {N : ℤ} (h : |r| < (N : ℝ)) :
    |⌊r⌋| ≤ N := by
  obtain ⟨h_neg, h_pos⟩ := abs_lt.mp h
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have h_lt : (-N - 1 : ℝ) < (⌊r⌋ : ℝ) := by
      have := Int.sub_one_lt_floor r
      linarith
    have : (-N - 1 : ℤ) < ⌊r⌋ := by exact_mod_cast h_lt
    omega
  · have h_lt : (⌊r⌋ : ℝ) < (N : ℝ) :=
      lt_of_le_of_lt (Int.floor_le r) h_pos
    exact_mod_cast h_lt.le

/-- Mirror of `abs_floor_le_of_abs_lt` for the ceiling: positive ceilings
can saturate (e.g. `⌈1.5⌉ = 2` with `|1.5| < 2` but `|⌈1.5⌉| = 2`). -/
theorem abs_ceil_le_of_abs_lt {r : ℝ} {N : ℤ} (h : |r| < (N : ℝ)) :
    |⌈r⌉| ≤ N := by
  obtain ⟨h_neg, h_pos⟩ := abs_lt.mp h
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have h_lt : (-N : ℝ) < (⌈r⌉ : ℝ) :=
      lt_of_lt_of_le h_neg (Int.le_ceil r)
    have : (-N : ℤ) < ⌈r⌉ := by exact_mod_cast h_lt
    omega
  · have h_lt : (⌈r⌉ : ℝ) < (N : ℝ) + 1 := by
      have := Int.ceil_lt_add_one r
      linarith
    have : (⌈r⌉ : ℤ) < N + 1 := by exact_mod_cast h_lt
    omega

/-- Binade lemma for directed-mode minimality: when `z = a · 2^e_a` has
`|a| < 2^p`, `e_a < e`, and `e = log|x|+1-p` (so `e` came from the precision
side of `canonicalExp`), then `|z| < 2^(log|x|)`. Combined with `|x| ≥
2^(log|x|)` this strictly bounds `|z|` below `|x|`. -/
theorem abs_lt_two_pow_log_of_precision {p : ℕ} {x : ℝ}
    {a e e_a : ℤ} (ha_bound : |a| < (2 : ℤ) ^ p)
    (h_ea_lt : e_a < e) (h_e_eq_log : e = Int.log 2 |x| + 1 - (p : ℤ)) :
    |(a : ℝ) * (2 : ℝ) ^ e_a| < (2 : ℝ) ^ (Int.log 2 |x|) := by
  have h_2ea_pos : (0 : ℝ) < (2 : ℝ) ^ e_a := zpow_pos (by norm_num) _
  have h_abs_bound : (|a| : ℝ) < (2 : ℝ) ^ p := by exact_mod_cast ha_bound
  rw [abs_mul, abs_of_pos h_2ea_pos]
  calc (|a| : ℝ) * (2 : ℝ) ^ e_a
      < (2 : ℝ) ^ p * (2 : ℝ) ^ e_a :=
        mul_lt_mul_of_pos_right h_abs_bound h_2ea_pos
    _ = (2 : ℝ) ^ ((p : ℤ) + e_a) := by
        rw [← zpow_natCast (2 : ℝ) p,
            ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    _ ≤ (2 : ℝ) ^ (Int.log 2 |x|) :=
        zpow_le_zpow_right₀ (by norm_num)
          (by linarith [h_ea_lt, h_e_eq_log])

/-- Apply the binade argument in `_toNegative`: if `z = a · 2^e_a ≤ x` is
in the binade-clipped regime, then `z ≤ ⌊x · 2^(-e)⌋ · 2^e`. -/
theorem binade_le_floor {p : ℕ} (hp : 0 < p) {x : ℝ} (hx : x ≠ 0)
    {a e e_a : ℤ} (ha_bound : |a| < (2 : ℤ) ^ p)
    (h_ea_lt : e_a < e) (h_e_eq_log : e = Int.log 2 |x| + 1 - (p : ℤ))
    (hz_le_x : (a : ℝ) * (2 : ℝ) ^ e_a ≤ x) :
    (a : ℝ) * (2 : ℝ) ^ e_a ≤ (⌊x * (2 : ℝ) ^ (-e)⌋ : ℝ) * (2 : ℝ) ^ e := by
  have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have h_2neg_pos : (0 : ℝ) < (2 : ℝ) ^ (-e) := zpow_pos (by norm_num) _
  have h_abs_z := abs_lt_two_pow_log_of_precision ha_bound h_ea_lt h_e_eq_log
  have h_x_ge : (2 : ℝ) ^ (Int.log 2 |x|) ≤ |x| :=
    Int.zpow_log_le_self (b := 2) (by norm_num : (1 : ℕ) < 2) (abs_pos.mpr hx)
  by_cases hx_nn : 0 ≤ x
  · -- x ≥ 0: y ≥ 2^log|x| > |z| ≥ z.
    -- c = ⌊x · 2^(-e)⌋ ≥ 2^(p-1).
    have h_x_scaled_ge : (2 : ℝ) ^ (p - 1 : ℤ) ≤ x * (2 : ℝ) ^ (-e) := by
      have h_2p_pos : (0 : ℝ) < (2 : ℝ) ^ ((p - 1 : ℤ)) := zpow_pos (by norm_num) _
      have h_2log_x : (2 : ℝ) ^ (Int.log 2 |x|) ≤ x := by
        have habs : |x| = x := abs_of_nonneg hx_nn
        linarith [h_x_ge, habs.symm.le]
      have h_exp_eq : Int.log 2 |x| - e = (p - 1 : ℤ) := by
        linarith [h_e_eq_log]
      calc (2 : ℝ) ^ (p - 1 : ℤ)
          = (2 : ℝ) ^ (Int.log 2 |x| - e) := by rw [h_exp_eq]
        _ = (2 : ℝ) ^ (Int.log 2 |x|) * (2 : ℝ) ^ (-e) := by
            rw [show (Int.log 2 |x| - e : ℤ) = (Int.log 2 |x|) + (-e) by ring,
                zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        _ ≤ x * (2 : ℝ) ^ (-e) :=
            mul_le_mul_of_nonneg_right h_2log_x h_2neg_pos.le
    have h_c_ge : (2 : ℤ) ^ (p - 1) ≤ ⌊x * (2 : ℝ) ^ (-e)⌋ := by
      apply Int.le_floor.mpr
      have h_cast : (((2 : ℤ) ^ (p - 1) : ℤ) : ℝ) =
          (2 : ℝ) ^ (p - 1 : ℤ) := by
        rw [show (p - 1 : ℤ) = ((p - 1 : ℕ) : ℤ) by omega,
            zpow_natCast]
        push_cast; rfl
      rw [h_cast]
      exact h_x_scaled_ge
    have h_y_ge : (2 : ℝ) ^ (Int.log 2 |x|) ≤
        (⌊x * (2 : ℝ) ^ (-e)⌋ : ℝ) * (2 : ℝ) ^ e := by
      have h_exp_eq : ((p - 1 : ℤ)) + e = Int.log 2 |x| := by
        linarith [h_e_eq_log]
      calc (2 : ℝ) ^ (Int.log 2 |x|)
          = (2 : ℝ) ^ (((p - 1 : ℤ)) + e) := by rw [h_exp_eq]
        _ = (2 : ℝ) ^ (p - 1 : ℤ) * (2 : ℝ) ^ e := by
            rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        _ ≤ (⌊x * (2 : ℝ) ^ (-e)⌋ : ℝ) * (2 : ℝ) ^ e := by
            apply mul_le_mul_of_nonneg_right _ h_2e_pos.le
            have : ((2 : ℤ) ^ (p - 1) : ℝ) ≤ (⌊x * (2 : ℝ) ^ (-e)⌋ : ℝ) := by
              exact_mod_cast h_c_ge
            have h_cast_eq : ((2 : ℤ) ^ (p - 1) : ℝ) =
                (2 : ℝ) ^ (p - 1 : ℤ) := by
              push_cast
              rw [show (p - 1 : ℤ) = ((p - 1 : ℕ) : ℤ) by
                    omega,
                  zpow_natCast]
            rw [← h_cast_eq]; exact this
    have h_z_lt : (a : ℝ) * (2 : ℝ) ^ e_a ≤ |(a : ℝ) * (2 : ℝ) ^ e_a| :=
      le_abs_self _
    linarith [h_abs_z, h_y_ge, h_z_lt]
  · -- x < 0: hypothesis z ≤ x forces |z| ≥ |x| ≥ 2^log|x|, contradicting |z| < 2^log|x|.
    push Not at hx_nn
    exfalso
    have h_z_neg : (a : ℝ) * (2 : ℝ) ^ e_a < 0 := lt_of_le_of_lt hz_le_x hx_nn
    have h_abs_z_ge : |x| ≤ |(a : ℝ) * (2 : ℝ) ^ e_a| := by
      rw [abs_of_neg hx_nn, abs_of_neg h_z_neg]; linarith
    have h_x_lt : |x| < (2 : ℝ) ^ (Int.log 2 |x|) := by
      have : |(a : ℝ) * (2 : ℝ) ^ e_a| < (2 : ℝ) ^ (Int.log 2 |x|) := h_abs_z
      linarith
    linarith [h_x_ge]

/-- The "rescale back" identity: `x · 2^(-e) · 2^e = x`. Used pervasively
to lift `c ≤ x · 2^(-e)` to `c · 2^e ≤ x` (and similar). -/
theorem mul_zpow_neg_self (x : ℝ) (e : ℤ) :
    x * (2 : ℝ) ^ (-e) * (2 : ℝ) ^ e = x := by
  rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
      neg_add_cancel, zpow_zero, mul_one]

/-- `|⌊x · 2^(-e)⌋ + 1| ≤ 2^p` when `|x · 2^(-e)| < 2^p` (the canonical bound
applied to the upper-grid mantissa). Used in parity-mode proofs where `dhi`'s
mantissa is `lo + 1`. -/
theorem abs_floor_add_one_le_of_abs_lt {r : ℝ} {p : ℕ}
    (h : |r| < (2 : ℝ) ^ p) :
    |⌊r⌋ + 1| ≤ (2 : ℤ) ^ p := by
  obtain ⟨h_neg_lt, h_lt⟩ := abs_lt.mp h
  have h_lo_upper : ⌊r⌋ ≤ (2 : ℤ) ^ p - 1 := by
    have h1 : (⌊r⌋ : ℝ) ≤ r := Int.floor_le _
    have h2 : (⌊r⌋ : ℝ) < (2 : ℝ) ^ p := lt_of_le_of_lt h1 h_lt
    have : (⌊r⌋ : ℤ) < ((2 : ℤ) ^ p : ℤ) := by exact_mod_cast h2
    omega
  have h_lo_lower : -((2 : ℤ) ^ p) ≤ ⌊r⌋ := by
    have h_floor_succ : r < (⌊r⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    have h_lo_lower_r : -((2 : ℝ) ^ p) < (⌊r⌋ : ℝ) + 1 := by linarith
    have : -((2 : ℤ) ^ p) < ⌊r⌋ + 1 := by exact_mod_cast h_lo_lower_r
    omega
  rw [abs_le]; exact ⟨by linarith, by linarith⟩

/-- `|k| < 2^p` (integers) ⟹ `log₂|k| + 1 ≤ p`. -/
theorem log_lt_p_of_abs_lt_two_pow {p : ℕ} (hp : 0 < p) {k : ℤ}
    (hk : |k| < (2 : ℤ) ^ p) :
    Int.log 2 (|k| : ℝ) + 1 ≤ (p : ℤ) := by
  by_cases hk0 : k = 0
  · rw [hk0]
    simp only [Int.cast_zero, abs_zero, Int.log_zero_right, zero_add, Nat.one_le_cast]
    exact_mod_cast hp
  · have h_abs_pos : (0 : ℝ) < (|k| : ℝ) := by
      have h1 : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
      have h2 : (1 : ℝ) ≤ (|k| : ℝ) := by exact_mod_cast h1
      linarith
    have h_abs_lt_zpow : (|k| : ℝ) < (2 : ℝ) ^ (p : ℤ) := by
      rw [zpow_natCast]
      have h1 : ((|k| : ℤ) : ℝ) < ((2 : ℤ) ^ p : ℝ) := by
        exact_mod_cast hk
      have h_cast : ((2 : ℤ) ^ p : ℝ) =
          (2 : ℝ) ^ p := by push_cast; rfl
      rw [h_cast] at h1; push_cast at h1; exact h1
    have h_log_lt : Int.log 2 (|k| : ℝ) < (p : ℤ) :=
      (Int.lt_zpow_iff_log_lt (by norm_num : 1 < 2) h_abs_pos).mp h_abs_lt_zpow
    linarith

/-- `Int.log 2 ((2 : ℝ) ^ k) = k` for integer `k`. -/
theorem log_two_zpow (k : ℤ) : Int.log 2 ((2 : ℝ) ^ k) = k := by
  simpa using Int.log_zpow (R := ℝ) (b := 2) (by norm_num) k

/-- `Int.log 2 ((2 : ℝ) ^ n) = n` for natural `n`. -/
theorem log_two_pow_nat (n : ℕ) : Int.log 2 ((2 : ℝ) ^ n) = (n : ℤ) := by
  rw [show ((2 : ℝ) ^ n) = ((2 : ℝ) ^ (n : ℤ)) from (zpow_natCast (2 : ℝ) n).symm]
  exact Int.log_zpow (by norm_num : 1 < 2) (n : ℤ)

/-- Cast `((2 : ℤ) ^ (p - 1) : ℝ) = (2 : ℝ) ^ (p - 1 : ℤ)`. -/
theorem cast_two_pow_pred {p : ℕ} (hp : 0 < p) :
    ((2 : ℤ) ^ (p - 1) : ℝ) = (2 : ℝ) ^ ((p : ℤ) - 1) := by
  rw [show ((p : ℤ) - 1 : ℤ) = ((p - 1 : ℕ) : ℤ) by omega, zpow_natCast]
  push_cast; rfl

/-- `2^(p-1) ≤ |k|` (integers) ⟹ `p - 1 ≤ log₂|↑k|`. -/
theorem log_ge_p_pred_of_two_pow_pred_le {p : ℕ} (hp : 0 < p) {k : ℤ}
    (hk : (2 : ℤ) ^ (p - 1) ≤ |k|) :
    (p : ℤ) - 1 ≤ Int.log 2 |(k : ℝ)| := by
  have h_2pm1_pos : (0 : ℝ) < ((2 : ℤ) ^ (p - 1) : ℝ) := by
    have : (0 : ℤ) < (2 : ℤ) ^ (p - 1) := by positivity
    exact_mod_cast this
  have h_le_real : ((2 : ℤ) ^ (p - 1) : ℝ) ≤ |(k : ℝ)| := by
    rw [show |(k : ℝ)| = ((|k| : ℤ) : ℝ) from by push_cast; rfl]
    exact_mod_cast hk
  have h_log_mono : Int.log 2 ((2 : ℤ) ^ (p - 1) : ℝ) ≤
      Int.log 2 |(k : ℝ)| :=
    Int.log_mono_right (by linarith) h_le_real
  have h_log_2pm1 : Int.log 2 ((2 : ℤ) ^ (p - 1) : ℝ) =
      ((p - 1 : ℕ) : ℤ) := by
    have h_cast : ((2 : ℤ) ^ (p - 1) : ℝ) =
        (2 : ℝ) ^ (p - 1 : ℕ) := by push_cast; rfl
    rw [h_cast, log_two_pow_nat]
  rw [h_log_2pm1] at h_log_mono
  have h_cast_eq : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
  linarith

/-- If `2^(p-1) ≤ |r|`, then `2^(p-1) ≤ |⌊r⌋|`. Sign-split argument. -/
theorem abs_floor_ge_two_pow_pred {p : ℕ} {r : ℝ}
    (h_r : ((2 : ℤ) ^ (p - 1) : ℝ) ≤ |r|) :
    (2 : ℤ) ^ (p - 1) ≤ |⌊r⌋| := by
  by_cases hr_nn : 0 ≤ r
  · have h_lo_nn : 0 ≤ ⌊r⌋ := Int.floor_nonneg.mpr hr_nn
    have h_r_ge : ((2 : ℤ) ^ (p - 1) : ℝ) ≤ r := by
      rw [show |r| = r from abs_of_nonneg hr_nn] at h_r
      exact h_r
    have h_floor_ge : (2 : ℤ) ^ (p - 1) ≤ ⌊r⌋ := by
      apply Int.le_floor.mpr
      have : (((2 : ℤ) ^ (p - 1) : ℤ) : ℝ) =
          ((2 : ℤ) ^ (p - 1) : ℝ) := by push_cast; rfl
      rw [this]; exact h_r_ge
    rw [abs_of_nonneg h_lo_nn]; exact h_floor_ge
  · have hr_neg : r < 0 := not_le.mp hr_nn
    have h_r_le : r ≤ -((2 : ℤ) ^ (p - 1) : ℝ) := by
      have h_abs_eq : |r| = -r := abs_of_neg hr_neg
      linarith
    have h_floor_le : (⌊r⌋ : ℝ) ≤ r := Int.floor_le _
    have h_lo_le_r : (⌊r⌋ : ℝ) ≤ -((2 : ℤ) ^ (p - 1) : ℝ) := by linarith
    have h_lo_le : ⌊r⌋ ≤ -((2 : ℤ) ^ (p - 1)) := by exact_mod_cast h_lo_le_r
    have h_lo_neg : ⌊r⌋ < 0 := by
      have hpos : (0 : ℤ) < (2 : ℤ) ^ (p - 1) := by positivity
      linarith
    rw [abs_of_neg h_lo_neg]; linarith

/-- For `x ≠ 0` and `e = log₂|x| + 1 - p`, we have `2^(p-1) ≤ |x · 2^(-e)|`. -/
theorem two_pow_pred_le_scaled {p : ℕ} (hp : 0 < p) {x : ℝ} (hx : x ≠ 0) {e : ℤ}
    (h_e_eq_log : e = Int.log 2 |x| + 1 - (p : ℤ)) :
    ((2 : ℤ) ^ (p - 1) : ℝ) ≤ |x * (2 : ℝ) ^ (-e)| := by
  rw [cast_two_pow_pred (p := p) hp]
  have h_x_ge : (2 : ℝ) ^ (Int.log 2 |x|) ≤ |x| :=
    Int.zpow_log_le_self (b := 2) (by norm_num : (1 : ℕ) < 2) (abs_pos.mpr hx)
  have h_2neg_pos : (0 : ℝ) < (2 : ℝ) ^ (-e) := zpow_pos (by norm_num) _
  have h_abs_s : |x * (2 : ℝ) ^ (-e)| = |x| * (2 : ℝ) ^ (-e) := by
    rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)]
  rw [h_abs_s]
  calc (2 : ℝ) ^ ((p : ℤ) - 1)
      = (2 : ℝ) ^ (Int.log 2 |x| + (-e)) := by
        congr 1; linarith [h_e_eq_log]
    _ = (2 : ℝ) ^ (Int.log 2 |x|) * (2 : ℝ) ^ (-e) := by
        rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    _ ≤ |x| * (2 : ℝ) ^ (-e) :=
        mul_le_mul_of_nonneg_right h_x_ge h_2neg_pos.le

end Mpfx
