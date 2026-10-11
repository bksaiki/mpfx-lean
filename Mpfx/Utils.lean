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
lemma two_zpow_split_toNat {K : Type*} [Field K] [CharZero K] {e₁ e₂ : ℤ} (h : e₂ ≤ e₁) :
    (2 : K) ^ e₁ = (2 : K) ^ (e₁ - e₂).toNat * (2 : K) ^ e₂ := by
  rw [← zpow_natCast, ← zpow_add₀ two_ne_zero, Int.toNat_of_nonneg (by omega)]
  congr 1; ring

/-- Read off `Int.log 2 x = k` from the binade bounds `2^k ≤ x < 2^(k+1)`. -/
theorem log_eq_of_zpow_bounds {x : ℝ} {k : ℤ} (hx : 0 < x)
    (hlo : (2 : ℝ) ^ k ≤ x) (hhi : x < (2 : ℝ) ^ (k + 1)) : Int.log 2 x = k := by
  have h1 : k ≤ Int.log 2 x :=
    (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hx).mp (by exact_mod_cast hlo)
  have h2 : Int.log 2 x < k + 1 :=
    (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hx).mp (by exact_mod_cast hhi)
  omega

/-- `Int.log 2 |k · 2^e'| = Int.log 2 |k| + e'` for nonzero integer `k`. -/
theorem log_abs_mul_zpow {k : ℤ} (hk_ne : k ≠ 0) (e' : ℤ) :
    Int.log 2 |(k : ℝ) * (2 : ℝ) ^ e'| = Int.log 2 (|k| : ℝ) + e' := by
  have h2e : (0 : ℝ) < (2 : ℝ) ^ e' := zpow_pos two_pos e'
  have hk : (0 : ℝ) < |(k : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hk_ne)
  rw [abs_mul, abs_of_pos h2e]
  refine log_eq_of_zpow_bounds (mul_pos hk h2e) ?_ ?_
  · rw [zpow_add₀ two_ne_zero]
    exact mul_le_mul_of_nonneg_right (Int.zpow_log_le_self (by norm_num) hk) h2e.le
  · rw [show Int.log 2 |(k : ℝ)| + e' + 1 = (Int.log 2 |(k : ℝ)| + 1) + e' by ring,
      zpow_add₀ two_ne_zero]
    exact mul_lt_mul_of_pos_right (Int.lt_zpow_succ_log_self (by norm_num) _) h2e

/-! ### Powers of two

Stated per exponent shape, so callers can rewrite without touching an exponent
bound by `set`. -/

/-- `2^(t+1) = 2 · 2^t`. -/
theorem two_zpow_succ (t : ℤ) : (2 : ℝ) ^ (t + 1) = 2 * (2 : ℝ) ^ t := by
  rw [zpow_add_one₀ (by norm_num)]; ring

/-- `2^a = 2 · 2^(a-1)`. -/
theorem two_zpow_dbl (a : ℤ) : (2 : ℝ) ^ a = 2 * (2 : ℝ) ^ (a - 1) := by
  rw [← two_zpow_succ, sub_add_cancel]

/-- `2^a / 2 = 2^(a-1)`. -/
theorem two_zpow_half (a : ℤ) : (2 : ℝ) ^ a / 2 = (2 : ℝ) ^ (a - 1) := by
  rw [two_zpow_dbl a]; ring

/-- Re-base a canonical rep to a coarser exponent: shift `c·2^e` down to quantum
`k ≤ e`, folding the extra powers of two into an integer coefficient. -/
lemma two_zpow_shift {K : Type*} [Field K] [CharZero K] (c : ℤ) {e k : ℤ} (h : k ≤ e) :
    (c : K) * (2 : K) ^ e = ((c * (2 : ℤ) ^ (e - k).toNat : ℤ) : K) * (2 : K) ^ k := by
  rw [two_zpow_split_toNat h]; push_cast; ring

/-- Inverse of the shift: if two canonical reps of the same value agree with
`e₁ ≤ e₂`, the finer coefficient is the coarser one scaled by `2^(e₂-e₁)`. -/
lemma coeff_eq_of_shift {K : Type*} [Field K] [CharZero K] {c₁ c₂ e₁ e₂ : ℤ} (h : e₁ ≤ e₂)
    (heq : (c₁ : K) * (2 : K) ^ e₁ = (c₂ : K) * (2 : K) ^ e₂) :
    c₁ = c₂ * (2 : ℤ) ^ (e₂ - e₁).toNat := by
  rw [two_zpow_shift c₂ h] at heq
  exact_mod_cast mul_right_cancel₀ (zpow_ne_zero _ two_ne_zero) heq

/-! ### Sign and power helpers -/

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
companions are in `Mpfx/Format/CanonicalExp.lean`. -/

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

/-- Integer multiples of `2^k` compare as their coefficients. -/
theorem int_mul_two_zpow_lt_iff {a b k : ℤ} :
    (a : ℝ) * (2 : ℝ) ^ k < (b : ℝ) * (2 : ℝ) ^ k ↔ a < b := by
  rw [mul_lt_mul_iff_of_pos_right (zpow_pos two_pos k)]; exact Int.cast_lt

theorem int_mul_two_zpow_le_iff {a b k : ℤ} :
    (a : ℝ) * (2 : ℝ) ^ k ≤ (b : ℝ) * (2 : ℝ) ^ k ↔ a ≤ b := by
  rw [mul_le_mul_iff_of_pos_right (zpow_pos two_pos k)]; exact Int.cast_le

/-- The "rescale back" identity: `x · 2^(-e) · 2^e = x`. -/
theorem mul_zpow_neg_self (x : ℝ) (e : ℤ) :
    x * (2 : ℝ) ^ (-e) * (2 : ℝ) ^ e = x := by
  rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
      neg_add_cancel, zpow_zero, mul_one]

/-- `|⌊r⌋ + 1| ≤ 2^p` when `|r| < 2^p`: the canonical bound for the ceiling
mantissa off the floor. -/
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

end Mpfx
