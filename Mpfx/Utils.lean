import Mathlib.Tactic

/-!
# Project-agnostic helpers

Pure-Mathlib lemmas that arise repeatedly in the formalization.
Nothing here mentions `Dyadic` or `Format`.
-/

namespace Mpfx

/-- `(2 : ℝ) ^ e` is positive — convenience wrapper around `zpow_pos`. -/
lemma two_zpow_pos (e : ℤ) : (0 : ℝ) < (2 : ℝ) ^ e :=
  zpow_pos (by norm_num) _

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

end Mpfx
