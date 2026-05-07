import Mathlib.Tactic

/-!
# Project-agnostic helpers

Pure-Mathlib lemmas that arise repeatedly across the formalization.
Nothing here mentions `Dyadic` or `AbstractFormat` — anything project-specific
belongs in the appropriate file.
-/

namespace Mpfx

/-- `(2 : ℝ) ^ e` is positive — convenience wrapper around `zpow_pos`. -/
lemma two_zpow_pos (e : ℤ) : (0 : ℝ) < (2 : ℝ) ^ e :=
  zpow_pos (by norm_num) _

/-- `|c · 2^e|` simplifies to `|c| · 2^e` (for `c : ℝ, e : ℤ`). -/
lemma abs_mul_two_zpow (c : ℝ) (e : ℤ) :
    |c * (2 : ℝ) ^ e| = |c| * (2 : ℝ) ^ e := by
  rw [abs_mul, abs_zpow, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- Extract one factor of `2` out of `(2 : ℤ) ^ k` when `k ≥ 1`. -/
lemma Int.two_pow_succ_pred {k : ℕ} (hk : 1 ≤ k) :
    (2 : ℤ) ^ k = 2 * (2 : ℤ) ^ (k - 1) := by
  have hk_eq : k = (k - 1) + 1 := by omega
  conv_lhs => rw [hk_eq]
  rw [pow_succ]; ring

/-- Split `2 ^ e₁` along a smaller exponent `e₂` using `toNat`. Shows up
whenever an integer-coefficient pair `(c, e₂)` is rebuilt from a finer-grained
`(c', e₁)`. -/
lemma two_zpow_split_toNat {e₁ e₂ : ℤ} (h : e₂ ≤ e₁) :
    (2 : ℝ) ^ e₁ = (2 : ℝ) ^ (e₁ - e₂).toNat * (2 : ℝ) ^ e₂ := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hsub : ((e₁ - e₂).toNat : ℤ) = e₁ - e₂ := Int.toNat_of_nonneg (by omega)
  rw [show ((2 : ℝ) ^ (e₁ - e₂).toNat : ℝ) = (2 : ℝ) ^ ((e₁ - e₂).toNat : ℤ) from
      (zpow_natCast _ _).symm, ← zpow_add₀ h2, hsub]
  congr 1; ring

/-- Odd integers have odd absolute value. -/
lemma Odd.abs_int {c : ℤ} (hodd : Odd c) : Odd |c| := by
  rcases hodd with ⟨k, hk⟩
  rcases lt_trichotomy c 0 with h | h | h
  · rw [abs_of_neg h]; exact ⟨-k - 1, by linarith⟩
  · simp [h] at hk; omega
  · rw [abs_of_pos h]; exact ⟨k, hk⟩

end Mpfx
