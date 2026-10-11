import Mpfx.Rounding.Defs
import Mpfx.Format.Parity

/-!
# Parity of adjacent values

For `x` strictly between its neighbouring values at the canonical exponent,
those neighbours have opposite parity (`neighbors_alternate`): by shrink
membership for `p ≠ 1`, and by counting exponents for `p = 1`.
-/

namespace Mpfx

/-- A nonzero neighbour of `x` at the canonical step is at least `2^⌊log₂|x|⌋`
in magnitude: inside `x`'s binade the floor and ceiling stay in it, and below
it any nonzero multiple of the step is at least the step. -/
private theorem two_zpow_log_le_neighbor {F : FiniteFormat} {x : ℝ} (hx : x ≠ 0)
    (hns : (⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ : ℝ) ≠ x * (2 : ℝ) ^ (-F.canonicalExp x))
    {m : ℤ} (hm : m = ⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ ∨
      m = ⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ + 1) (hm0 : m ≠ 0) :
    (2 : ℝ) ^ Int.log 2 |x| ≤ |(m : ℝ) * (2 : ℝ) ^ F.canonicalExp x| := by
  set e := F.canonicalExp x
  set s := x * (2 : ℝ) ^ (-e)
  set L := Int.log 2 |x|
  have h2e : (0 : ℝ) < 2 ^ e := zpow_pos two_pos e
  rw [abs_mul_two_zpow]
  rcases lt_or_ge L e with hLe | hLe
  · have : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm0
    calc (2 : ℝ) ^ L ≤ 2 ^ e := zpow_le_zpow_right₀ (by norm_num) hLe.le
      _ ≤ |(m : ℝ)| * 2 ^ e := le_mul_of_one_le_left h2e.le this
  -- `N = 2^(L - e)` is an integer with `N ≤ |s|`, so `N ≤ |m|`.
  set N : ℤ := 2 ^ (L - e).toNat with hN_def
  have hNpos : 0 < N := by positivity
  have hN : (N : ℝ) * 2 ^ e = 2 ^ L := by
    rw [two_zpow_split_toNat (K := ℝ) hLe, hN_def]; push_cast; ring
  have hNs : (N : ℝ) ≤ |s| := by
    rw [abs_mul_two_zpow, ← mul_le_mul_iff_of_pos_right h2e, hN, mul_assoc,
      ← zpow_add₀ two_ne_zero, neg_add_cancel, zpow_zero, mul_one]
    exact Int.zpow_log_le_self (by norm_num) (abs_pos.mpr hx)
  have hfl := Int.floor_le s
  have hlt : (⌊s⌋ : ℝ) < s := lt_of_le_of_ne hfl hns
  have hNm : N ≤ |m| := by
    rcases le_or_gt 0 s with hs | hs
    · rw [abs_of_nonneg hs] at hNs
      have : N ≤ ⌊s⌋ := Int.le_floor.mpr hNs
      rcases hm with rfl | rfl <;> rw [abs_of_nonneg (by omega)] <;> omega
    · rw [abs_of_neg hs] at hNs
      have : ⌊s⌋ < -N := by exact_mod_cast (show (⌊s⌋ : ℝ) < -N by linarith)
      rcases hm with rfl | rfl <;> rw [abs_of_neg (by omega)] <;> omega
  calc (2 : ℝ) ^ L = (N : ℝ) * 2 ^ e := hN.symm
    _ ≤ |(m : ℝ)| * 2 ^ e := mul_le_mul_of_nonneg_right (by exact_mod_cast hNm) h2e.le

/-- **Adjacent values alternate in parity.** For `dlo = ⌊s⌋·2^e` and
`dhi = (⌊s⌋+1)·2^e` at the canonical exponent, `dhi` is odd exactly when `dlo`
is not. Flocq `DN_UP_parity_generic_pos`. -/
theorem neighbors_alternate {F : FiniteFormat} (x : ℝ)
    (h : ¬ F.IsUndefined .toOdd)
    (h_lo_ne_s :
      (⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ : ℝ) ≠ x * (2 : ℝ) ^ (-F.canonicalExp x)) :
    F.IsOdd (Dyadic.ofIntZpow (⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ + 1) (F.canonicalExp x))
      ↔ ¬ F.IsOdd
        (Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ (F.canonicalExp x)) := by
  have hx_ne : x ≠ 0 := fun hx0 => h_lo_ne_s (by simp [hx0])
  set e := F.canonicalExp x
  set s := x * (2 : ℝ) ^ (-e)
  set k := ⌊s⌋
  -- Both neighbours have significand at most `2^p`.
  have hk : ∀ m, (m = k ∨ m = k + 1) → ∀ p : ℕ, F.p = p → |m| ≤ 2 ^ p := by
    intro m hm p hp
    have hs := floor_mantissa_lt (F := F) (x := x) hp
    rcases hm with rfl | rfl
    · exact abs_floor_le_of_abs_lt (N := 2 ^ p) (by push_cast; exact hs)
    · exact abs_floor_add_one_le_of_abs_lt hs
  by_cases hp1 : F.p = ((1 : ℕ) : Prec)
  swap
  · -- `p ≠ 1`: a neighbour is even iff it lies in the shrink iff its significand is.
    have hpar : ∀ m, (m = k ∨ m = k + 1) → (F.IsOdd (Dyadic.ofIntZpow m e) ↔ ¬ Even m) := by
      intro m hm
      have hC := FiniteFormat.ofIntZpow_mem_shrink_iff F hp1 (exp_le_canonicalExp_coe F x)
        (hk m hm) fun hm0 => by
          have hlog := two_zpow_log_le_neighbor hx_ne h_lo_ne_s hm hm0
          rw [← Dyadic.coe_ofIntZpow] at hlog
          have h2L' : (0 : ℝ) < 2 ^ Int.log 2 |x| := zpow_pos two_pos _
          have h2L : (2 : ℝ) ^ Int.log 2 |x| ≠ 0 := h2L'.ne'
          calc e = F.canonicalExp ((2 : ℝ) ^ Int.log 2 |x|) := canonicalExp_eq_of_log_eq F hx_ne
                h2L (by rw [abs_of_pos h2L', log_eq_of_zpow_bounds h2L' le_rfl
                  (zpow_lt_zpow_right₀ one_lt_two (lt_add_one _))])
            _ ≤ _ := F.canonicalExp_mono h2L (by rwa [abs_of_pos h2L'])
      have hmem : Dyadic.ofIntZpow m e ∈ F.unbounded :=
        ofIntZpow_mem_unbounded F (fun {e'} he' => F.exp_le_canonicalExp x he')
          (fun {p} hp => hk m hm p hp)
      exact (FiniteFormat.isOdd_iff_mem_shrink F hp1 _).trans
        ⟨fun h' => (not_congr hC).mp h'.2, fun h' => ⟨hmem, (not_congr hC).mpr h'⟩⟩
    rw [hpar k (Or.inl rfl), hpar (k + 1) (Or.inr rfl), Int.even_add_one, not_not]
  -- `p = 1`: the values are `0` and `±2^j`, and parity counts `j` from `exp`.
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : ℤ, F.exp = (e₀ : QExp) := by
    cases hexp : F.exp using QExp.recBotCoe with
    | bot => exact absurd ⟨hp1, hexp, Or.inl rfl⟩ h
    | coe e₀ => exact ⟨e₀, rfl⟩
  have he : e₀ ≤ e := F.exp_le_canonicalExp x he₀
  have hpow : ∀ σ j : ℤ, |σ| = 1 → e₀ ≤ j →
      (F.IsOdd (Dyadic.ofIntZpow σ j) ↔ Even (j - e₀)) := fun σ j hσ hj =>
    F.isOdd_ofIntZpow_of_p_one hp1 he₀ hσ hj
  have hdbl : ∀ σ : ℤ, Dyadic.ofIntZpow (2 * σ) e = Dyadic.ofIntZpow σ (e + 1) := fun σ =>
    Dyadic.ext_real (by
      simp only [Dyadic.coe_ofIntZpow]; rw [zpow_add_one₀ two_ne_zero]; push_cast; ring)
  have hzero : Dyadic.ofIntZpow 0 e = 0 := Dyadic.ext_real (by simp)
  -- A neighbour `0` puts `x` below `2^e`, so `e` is the quantum.
  have hsub : (k = 0 ∨ k = -1) → e = e₀ := by
    intro hk01
    have hfl : (k : ℝ) ≤ s := Int.floor_le s
    have hlt : s < k + 1 := Int.lt_floor_add_one s
    have hs_lt : |s| < 1 := by
      rcases hk01 with h0 | h0 <;> rw [h0] at hfl hlt <;> push_cast at hfl hlt
      · exact abs_lt.mpr ⟨by linarith, by linarith⟩
      · have : s ≠ -1 := fun hs => h_lo_ne_s (by rw [h0, hs]; push_cast; ring)
        exact abs_lt.mpr ⟨lt_of_le_of_ne hfl (Ne.symm this), by linarith⟩
    have hx_lt : |x| < 2 ^ e := by
      have h2e : (0 : ℝ) < 2 ^ e := zpow_pos two_pos e
      have : |s| * 2 ^ e = |x| := by
        rw [abs_mul_two_zpow, mul_assoc, ← zpow_add₀ two_ne_zero, neg_add_cancel, zpow_zero,
          mul_one]
      nlinarith
    have hL : Int.log 2 |x| < e := (Int.lt_zpow_iff_log_lt (by norm_num) (abs_pos.mpr hx_ne)).mp
      (by exact_mod_cast hx_lt)
    have := canonicalExp_expFinite hp1 he₀ hx_ne
    push_cast at this
    omega
  have hk_bnd := hk k (Or.inl rfl) 1 hp1
  have hk1_bnd := hk (k + 1) (Or.inr rfl) 1 hp1
  rw [abs_le] at hk_bnd hk1_bnd
  have hk_range : k = -2 ∨ k = -1 ∨ k = 0 ∨ k = 1 := by norm_num at hk_bnd hk1_bnd; omega
  rcases hk_range with hk' | hk' | hk' | hk' <;> rw [hk']
  · rw [show (-2 : ℤ) = 2 * -1 by norm_num, hdbl, show 2 * (-1 : ℤ) + 1 = -1 by norm_num,
      hpow (-1) (e + 1) (by norm_num) (by omega), hpow (-1) e (by norm_num) he,
      show e + 1 - e₀ = e - e₀ + 1 by ring, Int.even_add_one, not_not]
  · rw [show (-1 : ℤ) + 1 = 0 by norm_num, hzero, hpow (-1) e (by norm_num) he,
      hsub (Or.inr hk'), sub_self]
    exact iff_of_false (fun h' => h'.ne_zero rfl) (not_not.mpr Even.zero)
  · rw [zero_add, hzero, hpow 1 e (by norm_num) he, hsub (Or.inl hk'), sub_self]
    exact iff_of_true Even.zero (fun h' => h'.ne_zero rfl)
  · rw [show (1 : ℤ) + 1 = 2 * 1 by norm_num, hdbl, hpow 1 (e + 1) (by norm_num) (by omega),
      hpow 1 e (by norm_num) he, show e + 1 - e₀ = e - e₀ + 1 by ring, Int.even_add_one]

end Mpfx
