import Mpfx.Containment

/-!
# Grid representation theory

For a finite-precision format `F` with precision `p` and exponent floor `exp`,
a positive value `y ∈ F` admits a representation `y = c · 2^k` on the
`F`-grid, where `k = max(exp, ⌊log₂ y⌋ - p + 1)` is the grid step exponent at
`y` and `c` is a positive integer with `|c| < 2^p`. This is the structural
prerequisite for the `rndRTO_RN` analysis: the grid-representation lemmas
build up to the F-adjacency and midpoint-membership results used there.
-/

namespace Mpfx

/-- For a finite-precision finite-exp format `F` with `F.p = (p : ℕ+)`,
`F.exp = (exp : ℤ)`, and a positive value `y ∈ F`, there exist `k : ℤ` with
`k ≥ exp` and an integer `c` with `|c| < 2^p` such that `y = c·2^k`. The
exponent `k` is the F-grid step exponent at `y`: `max(exp, ⌊log₂ y⌋ - p + 1)`.

This is the key structural lemma underlying the F-adjacent midpoint analysis:
F-adjacent values at this `k` differ by exactly `2^k`. -/
theorem exists_grid_rep (F : FiniteFormat) {p : ℕ+} {exp : ℤ}
    (hp : F.p = ((p : ℕ+) : WithTop ℕ+)) (he : F.exp = (exp : WithBot ℤ))
    {y : Dyadic} (hp_y_full : Dyadic.precisionAtMost F.p y)
    (hq_y_full : Dyadic.quantumAtLeast F.exp y)
    (hy_pos : 0 < ((y : Dyadic) : ℝ)) :
    ∃ (k : ℤ) (c : ℤ),
      k ≥ exp ∧ |c| < (2 : ℤ)^(p : ℕ) ∧
      ((y : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ)^k ∧
      k = max exp (Int.log 2 ((y : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1) := by
  let k : ℤ := max exp (Int.log 2 ((y : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1)
  -- Get canonical (c_can, e_can) for y.
  have hy_ne : ((y : Dyadic) : ℝ) ≠ 0 := ne_of_gt hy_pos
  have hp_y : Dyadic.precisionAtMost ((p : ℕ+) : WithTop ℕ+) y := hp ▸ hp_y_full
  obtain ⟨c_can, e_can, hy_eq, h_odd, hc_can_lt⟩ :=
    Dyadic.exists_odd_canonical_of_precisionAtMost hp_y hy_ne
  -- Need e_can ≥ k. From canonical form constraints.
  have h_e_can_ge_exp : e_can ≥ exp := by
    have hq : Dyadic.quantumAtLeast F.exp y := hq_y_full
    rw [he, Dyadic.quantumAtLeast_coe_real] at hq
    obtain ⟨c', hc'_eq⟩ := hq
    -- y = c'·2^exp. Compare with canonical (c_can, e_can): c_can·2^e_can = c'·2^exp.
    -- If e_can < exp: by uniqueness, contradiction with c_can odd.
    by_contra h_lt
    push Not at h_lt
    have h_e_can_lt : e_can < exp := h_lt
    -- We have c_can·2^e_can = c'·2^exp with e_can < exp.
    have h_diff : c_can = c' * (2 : ℤ)^(exp - e_can).toNat := by
      have hd_pos : 0 < exp - e_can := by omega
      have hd_nn : 0 ≤ exp - e_can := le_of_lt hd_pos
      have : (c_can : ℝ) * (2 : ℝ)^e_can = (c' : ℝ) * (2 : ℝ)^exp := hy_eq.symm.trans hc'_eq
      have h_2_ne : (2 : ℝ) ≠ 0 := by norm_num
      have h_2e_can_ne : (2 : ℝ)^e_can ≠ 0 := zpow_ne_zero _ h_2_ne
      have h_eq2 : (c_can : ℝ) * (2 : ℝ)^e_can =
          ((c' : ℝ) * (2 : ℝ)^(exp - e_can)) * (2 : ℝ)^e_can := by
        have h_split :
            (c' : ℝ) * (2 : ℝ)^(exp - e_can) * (2 : ℝ)^e_can = (c' : ℝ) * (2 : ℝ)^exp := by
          rw [mul_assoc, ← zpow_add₀ h_2_ne]
          congr 2; omega
        rw [h_split]; exact this
      have h_c_eq : (c_can : ℝ) = (c' : ℝ) * (2 : ℝ)^(exp - e_can) :=
        mul_right_cancel₀ h_2e_can_ne h_eq2
      lift (exp - e_can) to ℕ using hd_nn with d hd
      rw [zpow_natCast] at h_c_eq
      have : ((c_can : ℝ)) = ((c' * (2 : ℤ)^d : ℤ) : ℝ) := by
        rw [h_c_eq]; push_cast; ring
      exact_mod_cast this
    have h_2_dvd_c_can : (2 : ℤ) ∣ c_can := by
      rw [h_diff]
      have hd_pos_nat : 0 < (exp - e_can).toNat := by
        have : 0 < exp - e_can := by omega
        omega
      exact dvd_mul_of_dvd_right (dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hd_pos_nat)) _
    exact (Int.not_even_iff_odd.mpr h_odd) (even_iff_two_dvd.mpr h_2_dvd_c_can)
  -- Now derive: e_can ≥ k. Need ⌊log₂ y⌋ - p + 1 ≤ e_can.
  have h_log_y : Int.log 2 ((y : Dyadic) : ℝ) ≤ e_can + ((p : ℕ) : ℤ) - 1 := by
    have h_c_can_ne : c_can ≠ 0 := by
      intro h
      rw [h] at hy_eq; push_cast at hy_eq
      rw [zero_mul] at hy_eq
      exact hy_ne hy_eq
    have h_c_can_pos_int : 0 < c_can := by
      rcases lt_trichotomy c_can 0 with hc | hc | hc
      · exfalso
        have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e_can := zpow_pos (by norm_num) _
        have h_neg : ((c_can : ℝ)) < 0 := by exact_mod_cast hc
        have : ((y : Dyadic) : ℝ) < 0 := by
          rw [hy_eq]; exact mul_neg_of_neg_of_pos h_neg h_2e_pos
        linarith
      · exfalso
        rw [hc] at hy_eq; push_cast at hy_eq
        rw [zero_mul] at hy_eq; linarith
      · exact hc
    have h_y_lt : ((y : Dyadic) : ℝ) < (2 : ℝ)^(e_can + ((p : ℕ) : ℤ)) := by
      have h_y_eq' : ((y : Dyadic) : ℝ) = (c_can : ℝ) * (2 : ℝ)^e_can := hy_eq
      rw [h_y_eq']
      have h_c_abs : (c_can : ℝ) < (2 : ℝ)^((p : ℕ) : ℤ) := by
        have h_c_abs_int : c_can < (2 : ℤ)^(p : ℕ) := by
          have habs : |c_can| = c_can := abs_of_pos h_c_can_pos_int
          rw [← habs]; exact hc_can_lt
        have : ((c_can : ℤ) : ℝ) < (((2 : ℤ)^(p : ℕ) : ℤ) : ℝ) := by exact_mod_cast h_c_abs_int
        rw [show (((2 : ℤ)^(p : ℕ) : ℤ) : ℝ) = (2 : ℝ)^((p : ℕ) : ℤ) from by push_cast; rfl] at this
        exact this
      have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e_can := zpow_pos (by norm_num) _
      calc (c_can : ℝ) * (2 : ℝ)^e_can
          < (2 : ℝ)^((p : ℕ) : ℤ) * (2 : ℝ)^e_can :=
              mul_lt_mul_of_pos_right h_c_abs h_2e_pos
        _ = (2 : ℝ)^(e_can + ((p : ℕ) : ℤ)) := by
              rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; ring_nf
    have h_y_lt' : ((y : Dyadic) : ℝ) < ((2 : ℕ) : ℝ)^(e_can + ((p : ℕ) : ℤ)) := by
      rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) from by push_cast; rfl]
      exact h_y_lt
    have h_log_lt : Int.log 2 ((y : Dyadic) : ℝ) < e_can + ((p : ℕ) : ℤ) :=
      (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) hy_pos).mp h_y_lt'
    omega
  -- k = max(exp, log_y - p + 1) ≤ e_can.
  have h_k_le_e_can : k ≤ e_can := by
    change max exp (Int.log 2 ((y : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1) ≤ e_can
    have h1 : exp ≤ e_can := h_e_can_ge_exp
    have h2 : Int.log 2 ((y : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1 ≤ e_can := by omega
    exact max_le h1 h2
  have h_k_ge_exp : k ≥ exp := le_max_left _ _
  -- Now y at quantum k: y = c_can · 2^(e_can - k) · 2^k = (c_can · 2^(e_can - k)) · 2^k.
  refine ⟨k, c_can * (2 : ℤ)^(e_can - k).toNat, h_k_ge_exp, ?_, ?_, rfl⟩
  · -- |d| < 2^p, where d = c_can · 2^(e_can - k).toNat.
    set d : ℤ := c_can * (2 : ℤ)^(e_can - k).toNat with hd_def
    have h_y_eq_d : ((y : Dyadic) : ℝ) = (d : ℝ) * (2 : ℝ)^k := by
      rw [hy_eq, hd_def]
      have h_diff_nn : 0 ≤ e_can - k := by omega
      have h_split :
          (c_can : ℝ) * (2 : ℝ)^e_can = (c_can : ℝ) * (2 : ℝ)^(e_can - k) * (2 : ℝ)^k := by
        rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        congr 2; omega
      rw [h_split]
      have h_eq_zpow : (2 : ℝ)^(e_can - k) = (2 : ℝ)^((e_can - k).toNat : ℤ) := by
        rw [Int.toNat_of_nonneg h_diff_nn]
      rw [h_eq_zpow, zpow_natCast]
      push_cast; ring
    have h_y_lt : ((y : Dyadic) : ℝ) < (2 : ℝ)^(k + ((p : ℕ) : ℤ)) := by
      have h_log_lt : Int.log 2 ((y : Dyadic) : ℝ) < k + ((p : ℕ) : ℤ) := by
        have hk_ge : Int.log 2 ((y : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1 ≤ k := le_max_right _ _
        omega
      have := (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) hy_pos).mpr h_log_lt
      exact_mod_cast this
    have h_2k_pos : (0 : ℝ) < (2 : ℝ)^k := zpow_pos (by norm_num) _
    have h_d_pos : 0 < d := by
      have h_d_real_pos : (0 : ℝ) < (d : ℝ) := by
        have : (d : ℝ) * (2 : ℝ)^k > 0 := h_y_eq_d ▸ hy_pos
        exact pos_of_mul_pos_left (by linarith [this, h_2k_pos]) (le_of_lt h_2k_pos)
      exact_mod_cast h_d_real_pos
    have h_d_real_lt : (d : ℝ) < (2 : ℝ)^((p : ℕ) : ℤ) := by
      have h_calc : (d : ℝ) * (2 : ℝ)^k < (2 : ℝ)^(k + ((p : ℕ) : ℤ)) := h_y_eq_d ▸ h_y_lt
      have h_kp_eq : (2 : ℝ)^(k + ((p : ℕ) : ℤ)) = (2 : ℝ)^((p : ℕ) : ℤ) * (2 : ℝ)^k := by
        rw [add_comm, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      rw [h_kp_eq] at h_calc
      exact lt_of_mul_lt_mul_right h_calc (le_of_lt h_2k_pos)
    have h_d_lt : d < (2 : ℤ)^(p : ℕ) := by
      have : ((d : ℤ) : ℝ) < (((2 : ℤ)^(p : ℕ) : ℤ) : ℝ) := by
        rw [show (((2 : ℤ)^(p : ℕ) : ℤ) : ℝ) = (2 : ℝ)^((p : ℕ) : ℤ) from by push_cast; rfl]
        exact h_d_real_lt
      exact_mod_cast this
    have h_abs : |d| = d := abs_of_pos h_d_pos
    rw [h_abs]
    exact h_d_lt
  · -- y = d · 2^k.
    rw [hy_eq]
    have h_diff_nn : 0 ≤ e_can - k := by omega
    have h_split :
        (c_can : ℝ) * (2 : ℝ)^e_can = (c_can : ℝ) * (2 : ℝ)^(e_can - k) * (2 : ℝ)^k := by
      rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 2; omega
    rw [h_split]
    have h_eq_zpow : (2 : ℝ)^(e_can - k) = (2 : ℝ)^((e_can - k).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg h_diff_nn]
    rw [h_eq_zpow, zpow_natCast]
    push_cast; ring

/-- For a representation `y = c·2^k` with `y > 0`, the integer `c > 0`. -/
theorem grid_rep_c_pos {y : Dyadic} (hy_pos : 0 < ((y : Dyadic) : ℝ))
    {k c : ℤ}
    (h : ((y : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ) ^ k) :
    0 < c := by
  have h_2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
  have h_c_real_pos : (0 : ℝ) < (c : ℝ) := by
    have : (c : ℝ) * (2 : ℝ) ^ k > 0 := h ▸ hy_pos
    exact pos_of_mul_pos_left (by linarith) (le_of_lt h_2k_pos)
  exact_mod_cast h_c_real_pos

/-- F-grid representation in the precision-only form: `k = ⌊log₂ y⌋ - p + 1`
(no `max` with `F.exp`). Useful when `F.exp = ⊥` (since the `k ≥ exp` clause
of `exists_grid_rep` is then vacuous). -/
theorem exists_grid_rep_exp_bot (F : FiniteFormat) {p : ℕ+}
    (hp : F.p = ((p : ℕ+) : WithTop ℕ+))
    {y : Dyadic} (hp_y_full : Dyadic.precisionAtMost F.p y)
    (hy_pos : 0 < ((y : Dyadic) : ℝ)) :
    ∃ (k : ℤ) (c : ℤ),
      |c| < (2 : ℤ) ^ (p : ℕ) ∧
      ((y : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ) ^ k ∧
      k = Int.log 2 ((y : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1 := by
  let k : ℤ := Int.log 2 ((y : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1
  have hy_ne : ((y : Dyadic) : ℝ) ≠ 0 := ne_of_gt hy_pos
  have hp_y : Dyadic.precisionAtMost ((p : ℕ+) : WithTop ℕ+) y := hp ▸ hp_y_full
  obtain ⟨c_can, e_can, hy_eq, h_odd, hc_can_lt⟩ :=
    Dyadic.exists_odd_canonical_of_precisionAtMost hp_y hy_ne
  have h_c_can_ne : c_can ≠ 0 := by
    intro h
    rw [h] at hy_eq; push_cast at hy_eq
    rw [zero_mul] at hy_eq
    exact hy_ne hy_eq
  have h_c_can_pos_int : 0 < c_can := by
    rcases lt_trichotomy c_can 0 with hc | hc | hc
    · exfalso
      have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e_can := zpow_pos (by norm_num) _
      have h_neg : ((c_can : ℝ)) < 0 := by exact_mod_cast hc
      have : ((y : Dyadic) : ℝ) < 0 := by
        rw [hy_eq]; exact mul_neg_of_neg_of_pos h_neg h_2e_pos
      linarith
    · exfalso; exact h_c_can_ne hc
    · exact hc
  have h_log_y : Int.log 2 ((y : Dyadic) : ℝ) ≤ e_can + ((p : ℕ) : ℤ) - 1 := by
    have h_y_lt : ((y : Dyadic) : ℝ) < (2 : ℝ) ^ (e_can + ((p : ℕ) : ℤ)) := by
      rw [hy_eq]
      have h_c_abs : (c_can : ℝ) < (2 : ℝ) ^ ((p : ℕ) : ℤ) := by
        have h_c_abs_int : c_can < (2 : ℤ) ^ (p : ℕ) := by
          have habs : |c_can| = c_can := abs_of_pos h_c_can_pos_int
          rw [← habs]; exact hc_can_lt
        have : ((c_can : ℤ) : ℝ) < (((2 : ℤ) ^ (p : ℕ) : ℤ) : ℝ) := by exact_mod_cast h_c_abs_int
        rw [show (((2 : ℤ) ^ (p : ℕ) : ℤ) : ℝ) = (2 : ℝ) ^ ((p : ℕ) : ℤ) from by
          push_cast; rfl] at this
        exact this
      have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e_can := zpow_pos (by norm_num) _
      calc (c_can : ℝ) * (2 : ℝ) ^ e_can
          < (2 : ℝ) ^ ((p : ℕ) : ℤ) * (2 : ℝ) ^ e_can :=
              mul_lt_mul_of_pos_right h_c_abs h_2e_pos
        _ = (2 : ℝ) ^ (e_can + ((p : ℕ) : ℤ)) := by
              rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; ring_nf
    have h_y_lt_nat : ((y : Dyadic) : ℝ) < ((2 : ℕ) : ℝ) ^ (e_can + ((p : ℕ) : ℤ)) := by
      rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) from by push_cast; rfl]
      exact h_y_lt
    have : Int.log 2 ((y : Dyadic) : ℝ) < e_can + ((p : ℕ) : ℤ) :=
      (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) hy_pos).mp h_y_lt_nat
    omega
  have h_k_le_e_can : k ≤ e_can := by
    change Int.log 2 ((y : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1 ≤ e_can
    omega
  refine ⟨k, c_can * (2 : ℤ) ^ (e_can - k).toNat, ?_, ?_, rfl⟩
  · set d : ℤ := c_can * (2 : ℤ) ^ (e_can - k).toNat with hd_def
    have h_y_eq_d : ((y : Dyadic) : ℝ) = (d : ℝ) * (2 : ℝ) ^ k := by
      rw [hy_eq, hd_def]
      have h_diff_nn : 0 ≤ e_can - k := by omega
      have h_split :
          (c_can : ℝ) * (2 : ℝ) ^ e_can
            = (c_can : ℝ) * (2 : ℝ) ^ (e_can - k) * (2 : ℝ) ^ k := by
        rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        congr 2; omega
      rw [h_split]
      have h_eq_zpow : (2 : ℝ) ^ (e_can - k) = (2 : ℝ) ^ ((e_can - k).toNat : ℤ) := by
        rw [Int.toNat_of_nonneg h_diff_nn]
      rw [h_eq_zpow, zpow_natCast]
      push_cast; ring
    have h_y_lt : ((y : Dyadic) : ℝ) < (2 : ℝ) ^ (k + ((p : ℕ) : ℤ)) := by
      have h_log_lt : Int.log 2 ((y : Dyadic) : ℝ) < k + ((p : ℕ) : ℤ) := by
        have hk_def : k = Int.log 2 ((y : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1 := rfl
        omega
      have := (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) hy_pos).mpr h_log_lt
      exact_mod_cast this
    have h_2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
    have h_d_pos : 0 < d := by
      have h_d_real_pos : (0 : ℝ) < (d : ℝ) := by
        have : (d : ℝ) * (2 : ℝ) ^ k > 0 := h_y_eq_d ▸ hy_pos
        exact pos_of_mul_pos_left (by linarith) (le_of_lt h_2k_pos)
      exact_mod_cast h_d_real_pos
    have h_d_real_lt : (d : ℝ) < (2 : ℝ) ^ ((p : ℕ) : ℤ) := by
      have h_calc : (d : ℝ) * (2 : ℝ) ^ k < (2 : ℝ) ^ (k + ((p : ℕ) : ℤ)) := h_y_eq_d ▸ h_y_lt
      have h_kp_eq : (2 : ℝ) ^ (k + ((p : ℕ) : ℤ)) = (2 : ℝ) ^ ((p : ℕ) : ℤ) * (2 : ℝ) ^ k := by
        rw [add_comm, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      rw [h_kp_eq] at h_calc
      exact lt_of_mul_lt_mul_right h_calc (le_of_lt h_2k_pos)
    have h_d_lt : d < (2 : ℤ) ^ (p : ℕ) := by
      have : ((d : ℤ) : ℝ) < (((2 : ℤ) ^ (p : ℕ) : ℤ) : ℝ) := by
        rw [show (((2 : ℤ) ^ (p : ℕ) : ℤ) : ℝ) = (2 : ℝ) ^ ((p : ℕ) : ℤ) from by push_cast; rfl]
        exact h_d_real_lt
      exact_mod_cast this
    have h_abs : |d| = d := abs_of_pos h_d_pos
    rw [h_abs]; exact h_d_lt
  · rw [hy_eq]
    have h_diff_nn : 0 ≤ e_can - k := by omega
    have h_split :
        (c_can : ℝ) * (2 : ℝ) ^ e_can
          = (c_can : ℝ) * (2 : ℝ) ^ (e_can - k) * (2 : ℝ) ^ k := by
      rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 2; omega
    rw [h_split]
    have h_eq_zpow : (2 : ℝ) ^ (e_can - k) = (2 : ℝ) ^ ((e_can - k).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg h_diff_nn]
    rw [h_eq_zpow, zpow_natCast]
    push_cast; ring

/-- No F element lies strictly in the open interval `(c·2^k, (c+1)·2^k)` when
`k = max(exp, ⌊log₂(c·2^k)⌋ - p + 1)` is the F-grid step exponent at `c·2^k`.
This is the key F-adjacency lemma: applying `exists_grid_rep` to a putative
`y ∈ F` strictly in the interval forces `y` to have grid-exp `k' = k`, making
`y/2^k` an integer strictly between `c` and `c+1`, a contradiction. -/
theorem no_F_element_in_step_interval (F : FiniteFormat) {p : ℕ+} {exp : ℤ}
    (hp : F.p = ((p : ℕ+) : WithTop ℕ+)) (he : F.exp = (exp : WithBot ℤ))
    {c : ℤ} (hc_pos : 0 < c) (hc_lt : c < (2 : ℤ) ^ (p : ℕ))
    {k : ℤ} (hk : k ≥ exp)
    (hk_max : k = max exp (Int.log 2 ((c : ℝ) * (2 : ℝ) ^ k) - ((p : ℕ) : ℤ) + 1))
    {y : Dyadic}
    (hp_y : Dyadic.precisionAtMost F.p y)
    (hq_y : Dyadic.quantumAtLeast F.exp y)
    (h_lb : ((c : ℝ)) * (2 : ℝ) ^ k < ((y : Dyadic) : ℝ))
    (h_ub : ((y : Dyadic) : ℝ) < (((c + 1 : ℤ) : ℝ)) * (2 : ℝ) ^ k) :
    False := by
  have h_2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
  have h_c_real_pos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc_pos
  have h_cxk_pos : (0 : ℝ) < (c : ℝ) * (2 : ℝ) ^ k := mul_pos h_c_real_pos h_2k_pos
  have hy_pos : 0 < ((y : Dyadic) : ℝ) := by linarith
  obtain ⟨k', c', hk'_ge, hc'_lt, hy_eq, hk'_max⟩ :=
    exists_grid_rep F hp he hp_y hq_y hy_pos
  -- Bound: log y ≤ k + p - 1.
  have h_y_lt_2pk : ((y : Dyadic) : ℝ) < (2 : ℝ) ^ (k + ((p : ℕ) : ℤ)) := by
    have h_c1_le : ((c + 1 : ℤ) : ℝ) ≤ (2 : ℝ) ^ ((p : ℕ) : ℤ) := by
      have h_int : c + 1 ≤ (2 : ℤ) ^ (p : ℕ) := by omega
      have h_cast : ((c + 1 : ℤ) : ℝ) ≤ (((2 : ℤ) ^ (p : ℕ) : ℤ) : ℝ) := by exact_mod_cast h_int
      rw [show (((2 : ℤ) ^ (p : ℕ) : ℤ) : ℝ) = (2 : ℝ) ^ ((p : ℕ) : ℤ) from by push_cast; rfl]
        at h_cast
      exact h_cast
    calc ((y : Dyadic) : ℝ)
        < ((c + 1 : ℤ) : ℝ) * (2 : ℝ) ^ k := h_ub
      _ ≤ (2 : ℝ) ^ ((p : ℕ) : ℤ) * (2 : ℝ) ^ k :=
            mul_le_mul_of_nonneg_right h_c1_le (le_of_lt h_2k_pos)
      _ = (2 : ℝ) ^ (k + ((p : ℕ) : ℤ)) := by
            rw [add_comm, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have h_log_y_le : Int.log 2 ((y : Dyadic) : ℝ) ≤ k + ((p : ℕ) : ℤ) - 1 := by
    have h_y_lt_nat : ((y : Dyadic) : ℝ) < ((2 : ℕ) : ℝ) ^ (k + ((p : ℕ) : ℤ)) := by
      rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) from by push_cast; rfl]
      exact h_y_lt_2pk
    have : Int.log 2 ((y : Dyadic) : ℝ) < k + ((p : ℕ) : ℤ) :=
      (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) hy_pos).mp h_y_lt_nat
    omega
  have h_k'_le_k : k' ≤ k := by
    rw [hk'_max]
    exact max_le hk (by omega)
  -- Lower bound: log y ≥ log(c·2^k) ≥ k.
  have h_2k_le_cxk : ((2 : ℕ) : ℝ) ^ k ≤ (c : ℝ) * (2 : ℝ) ^ k := by
    rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) from by push_cast; rfl]
    have h_c_ge_1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc_pos
    calc (2 : ℝ) ^ k = 1 * (2 : ℝ) ^ k := by ring
      _ ≤ (c : ℝ) * (2 : ℝ) ^ k :=
            mul_le_mul_of_nonneg_right h_c_ge_1 (le_of_lt h_2k_pos)
  have h_log_cxk_ge_k : k ≤ Int.log 2 ((c : ℝ) * (2 : ℝ) ^ k) :=
    (Int.zpow_le_iff_le_log (by norm_num : 1 < (2 : ℕ)) h_cxk_pos).mp h_2k_le_cxk
  have h_log_y_ge : Int.log 2 ((c : ℝ) * (2 : ℝ) ^ k) ≤ Int.log 2 ((y : Dyadic) : ℝ) :=
    Int.log_mono_right h_cxk_pos (le_of_lt h_lb)
  have h_k'_ge_k : k' ≥ k := by
    rw [hk'_max]
    rcases eq_or_lt_of_le hk with hke | hke
    · rw [← hke]; exact le_max_left _ _
    · -- k > exp. From hk_max, k = log(c·2^k) - p + 1.
      have h_hk_form : k = Int.log 2 ((c : ℝ) * (2 : ℝ) ^ k) - ((p : ℕ) : ℤ) + 1 := by
        by_cases h : exp ≤ Int.log 2 ((c : ℝ) * (2 : ℝ) ^ k) - ((p : ℕ) : ℤ) + 1
        · have h_max_eq : max exp (Int.log 2 ((c : ℝ) * (2 : ℝ) ^ k) - ((p : ℕ) : ℤ) + 1)
              = Int.log 2 ((c : ℝ) * (2 : ℝ) ^ k) - ((p : ℕ) : ℤ) + 1 := max_eq_right h
          rw [h_max_eq] at hk_max
          exact hk_max
        · push Not at h
          have h_max_eq : max exp (Int.log 2 ((c : ℝ) * (2 : ℝ) ^ k) - ((p : ℕ) : ℤ) + 1) = exp :=
            max_eq_left (le_of_lt h)
          rw [h_max_eq] at hk_max
          exact absurd hk_max.symm (ne_of_lt hke)
      -- log y ≥ log(c·2^k) = k + p - 1, so log y - p + 1 ≥ k.
      apply le_max_of_le_right
      omega
  have h_k'_eq : k' = k := le_antisymm h_k'_le_k h_k'_ge_k
  rw [h_k'_eq] at hy_eq
  -- y = c'·2^k. Combined with h_lb, h_ub: c < c' < c+1.
  have h_c'_gt_c : (c : ℝ) < (c' : ℝ) := by
    have : (c : ℝ) * (2 : ℝ) ^ k < (c' : ℝ) * (2 : ℝ) ^ k := hy_eq ▸ h_lb
    exact lt_of_mul_lt_mul_right this (le_of_lt h_2k_pos)
  have h_c'_lt_c1 : (c' : ℝ) < ((c + 1 : ℤ) : ℝ) := by
    have : (c' : ℝ) * (2 : ℝ) ^ k < ((c + 1 : ℤ) : ℝ) * (2 : ℝ) ^ k := hy_eq ▸ h_ub
    exact lt_of_mul_lt_mul_right this (le_of_lt h_2k_pos)
  have h_c'_int_gt : c < c' := by exact_mod_cast h_c'_gt_c
  have h_c'_int_lt : c' < c + 1 := by exact_mod_cast h_c'_lt_c1
  omega

/-- No F element lies strictly in `(c·2^k, (c+1)·2^k)` when `k` is the
precision-only step `log(c·2^k) - p + 1` (no `max` with `F.exp`). -/
private theorem no_F_element_in_step_interval_exp_bot (F : FiniteFormat) {p : ℕ+}
    (hp : F.p = ((p : ℕ+) : WithTop ℕ+))
    {c : ℤ} (hc_pos : 0 < c) (hc_lt : c < (2 : ℤ) ^ (p : ℕ))
    {k : ℤ}
    (hk_eq : k = Int.log 2 ((c : ℝ) * (2 : ℝ) ^ k) - ((p : ℕ) : ℤ) + 1)
    {y : Dyadic}
    (hp_y : Dyadic.precisionAtMost F.p y)
    (h_lb : ((c : ℝ)) * (2 : ℝ) ^ k < ((y : Dyadic) : ℝ))
    (h_ub : ((y : Dyadic) : ℝ) < (((c + 1 : ℤ) : ℝ)) * (2 : ℝ) ^ k) :
    False := by
  have h_2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
  have h_c_real_pos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc_pos
  have h_cxk_pos : (0 : ℝ) < (c : ℝ) * (2 : ℝ) ^ k := mul_pos h_c_real_pos h_2k_pos
  have hy_pos : 0 < ((y : Dyadic) : ℝ) := by linarith
  obtain ⟨k', c', hc'_lt, hy_eq, hk'_eq⟩ :=
    exists_grid_rep_exp_bot F hp hp_y hy_pos
  have h_y_lt_2pk : ((y : Dyadic) : ℝ) < (2 : ℝ) ^ (k + ((p : ℕ) : ℤ)) := by
    have h_c1_le : ((c + 1 : ℤ) : ℝ) ≤ (2 : ℝ) ^ ((p : ℕ) : ℤ) := by
      have h_int : c + 1 ≤ (2 : ℤ) ^ (p : ℕ) := by omega
      have h_cast : ((c + 1 : ℤ) : ℝ) ≤ (((2 : ℤ) ^ (p : ℕ) : ℤ) : ℝ) := by exact_mod_cast h_int
      rw [show (((2 : ℤ) ^ (p : ℕ) : ℤ) : ℝ) = (2 : ℝ) ^ ((p : ℕ) : ℤ) from by push_cast; rfl]
        at h_cast
      exact h_cast
    calc ((y : Dyadic) : ℝ)
        < ((c + 1 : ℤ) : ℝ) * (2 : ℝ) ^ k := h_ub
      _ ≤ (2 : ℝ) ^ ((p : ℕ) : ℤ) * (2 : ℝ) ^ k :=
            mul_le_mul_of_nonneg_right h_c1_le (le_of_lt h_2k_pos)
      _ = (2 : ℝ) ^ (k + ((p : ℕ) : ℤ)) := by
            rw [add_comm, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have h_log_y_le : Int.log 2 ((y : Dyadic) : ℝ) ≤ k + ((p : ℕ) : ℤ) - 1 := by
    have h_y_lt_nat : ((y : Dyadic) : ℝ) < ((2 : ℕ) : ℝ) ^ (k + ((p : ℕ) : ℤ)) := by
      rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) from by push_cast; rfl]
      exact h_y_lt_2pk
    have : Int.log 2 ((y : Dyadic) : ℝ) < k + ((p : ℕ) : ℤ) :=
      (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) hy_pos).mp h_y_lt_nat
    omega
  have h_2k_le_cxk : ((2 : ℕ) : ℝ) ^ k ≤ (c : ℝ) * (2 : ℝ) ^ k := by
    rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) from by push_cast; rfl]
    have h_c_ge_1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc_pos
    calc (2 : ℝ) ^ k = 1 * (2 : ℝ) ^ k := by ring
      _ ≤ (c : ℝ) * (2 : ℝ) ^ k :=
            mul_le_mul_of_nonneg_right h_c_ge_1 (le_of_lt h_2k_pos)
  have h_log_cxk_ge_k : k ≤ Int.log 2 ((c : ℝ) * (2 : ℝ) ^ k) :=
    (Int.zpow_le_iff_le_log (by norm_num : 1 < (2 : ℕ)) h_cxk_pos).mp h_2k_le_cxk
  have h_log_y_ge : Int.log 2 ((c : ℝ) * (2 : ℝ) ^ k) ≤ Int.log 2 ((y : Dyadic) : ℝ) :=
    Int.log_mono_right h_cxk_pos (le_of_lt h_lb)
  -- k' = log y - p + 1.
  -- We have log(c·2^k) ≤ log y ≤ k+p-1, and log(c·2^k) = k+p-1 (from hk_eq).
  -- So log y = k+p-1, k' = k.
  have h_log_cxk_eq : Int.log 2 ((c : ℝ) * (2 : ℝ) ^ k) = k + ((p : ℕ) : ℤ) - 1 := by
    omega
  have h_log_y_eq : Int.log 2 ((y : Dyadic) : ℝ) = k + ((p : ℕ) : ℤ) - 1 := by
    omega
  have h_k'_eq : k' = k := by
    rw [hk'_eq]; omega
  rw [h_k'_eq] at hy_eq
  have h_c'_gt_c : (c : ℝ) < (c' : ℝ) := by
    have : (c : ℝ) * (2 : ℝ) ^ k < (c' : ℝ) * (2 : ℝ) ^ k := hy_eq ▸ h_lb
    exact lt_of_mul_lt_mul_right this (le_of_lt h_2k_pos)
  have h_c'_lt_c1 : (c' : ℝ) < ((c + 1 : ℤ) : ℝ) := by
    have : (c' : ℝ) * (2 : ℝ) ^ k < ((c + 1 : ℤ) : ℝ) * (2 : ℝ) ^ k := hy_eq ▸ h_ub
    exact lt_of_mul_lt_mul_right this (le_of_lt h_2k_pos)
  have h_c'_int_gt : c < c' := by exact_mod_cast h_c'_gt_c
  have h_c'_int_lt : c' < c + 1 := by exact_mod_cast h_c'_lt_c1
  omega

/-- F-adjacent step form: F-adjacent positive `y₁ < y₂ ∈ F` have
`y₁ = c·2^k`, `y₂ = (c+1)·2^k` where `(c, k)` is `y₁`'s grid rep. The exponent
`k = max(exp, ⌊log₂ y₁⌋ - p + 1)` is the F-grid step exponent at `y₁`. -/
theorem F_adjacent_step_form (F : FiniteFormat) {p : ℕ+} {exp : ℤ}
    (hp : F.p = ((p : ℕ+) : WithTop ℕ+)) (he : F.exp = (exp : WithBot ℤ))
    {y₁ y₂ : Dyadic} (hy₁F : y₁ ∈ F) (hy₂F : y₂ ∈ F)
    (h_pos : 0 < ((y₁ : Dyadic) : ℝ))
    (h_lt : ((y₁ : Dyadic) : ℝ) < ((y₂ : Dyadic) : ℝ))
    (h_adj : ∀ y : Dyadic, y ∈ F →
              ((y₁ : Dyadic) : ℝ) < ((y : Dyadic) : ℝ) →
              ((y₂ : Dyadic) : ℝ) ≤ ((y : Dyadic) : ℝ)) :
    ∃ (k : ℤ) (c : ℤ),
      k ≥ exp ∧ 0 < c ∧ c < (2 : ℤ) ^ (p : ℕ) ∧
      ((y₁ : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ) ^ k ∧
      ((y₂ : Dyadic) : ℝ) = ((c + 1 : ℤ) : ℝ) * (2 : ℝ) ^ k := by
  obtain ⟨hp_y₁, hq_y₁, hb_y₁⟩ := hy₁F
  obtain ⟨hp_y₂, hq_y₂, hb_y₂⟩ := hy₂F
  obtain ⟨k, c, hk, hc_lt, hy₁_eq, hk_max⟩ :=
    exists_grid_rep F hp he hp_y₁ hq_y₁ h_pos
  have hc_pos : 0 < c := grid_rep_c_pos h_pos hy₁_eq
  have hc_lt_int : c < (2 : ℤ) ^ (p : ℕ) := by
    have habs : |c| = c := abs_of_pos hc_pos
    rw [← habs]; exact hc_lt
  refine ⟨k, c, hk, hc_pos, hc_lt_int, hy₁_eq, ?_⟩
  have h_2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
  have hk_max' : k = max exp (Int.log 2 ((c : ℝ) * (2 : ℝ) ^ k) - ((p : ℕ) : ℤ) + 1) := by
    have h_log_eq : Int.log 2 ((y₁ : Dyadic) : ℝ) = Int.log 2 ((c : ℝ) * (2 : ℝ) ^ k) := by
      rw [hy₁_eq]
    rw [← h_log_eq]; exact hk_max
  -- Step 1: (c+1)·2^k ≤ y₂.
  have h_y₂_ge : ((c + 1 : ℤ) : ℝ) * (2 : ℝ) ^ k ≤ ((y₂ : Dyadic) : ℝ) := by
    by_contra h_lt2
    push Not at h_lt2
    have h_y₁_lt' : (c : ℝ) * (2 : ℝ) ^ k < ((y₂ : Dyadic) : ℝ) := hy₁_eq ▸ h_lt
    exact no_F_element_in_step_interval F hp he hc_pos hc_lt_int hk hk_max'
      hp_y₂ hq_y₂ h_y₁_lt' h_lt2
  -- Step 2: construct z = (c+1)·2^k as a Dyadic in F.
  set z : Dyadic := Dyadic.ofIntZpow (c + 1) k with hz_def
  have hz_eq : ((z : Dyadic) : ℝ) = ((c + 1 : ℤ) : ℝ) * (2 : ℝ) ^ k := by
    change ((Dyadic.ofIntZpow (c + 1) k : Dyadic) : ℝ) = _
    rw [Dyadic.coe_ofIntZpow]
  have hz_p : Dyadic.precisionAtMost F.p z := by
    rw [hp]
    apply Dyadic.precisionAtMost_of_abs_le (c + 1) k (by rw [Dyadic.coe_rat_ofIntZpow])
    have h_c1_pos : 0 < c + 1 := by omega
    rw [abs_of_pos h_c1_pos]
    omega
  have hz_q : Dyadic.quantumAtLeast F.exp z := by
    rw [he]
    rw [Dyadic.quantumAtLeast_coe_real]
    refine ⟨(c + 1) * (2 : ℤ) ^ (k - exp).toNat, ?_⟩
    rw [hz_eq]
    have h_diff_nn : 0 ≤ k - exp := by omega
    have h_eq_zpow : (2 : ℝ) ^ k = (2 : ℝ) ^ ((k - exp).toNat : ℤ) * (2 : ℝ) ^ exp := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1
      rw [Int.toNat_of_nonneg h_diff_nn]; ring
    rw [h_eq_zpow, zpow_natCast]
    push_cast; ring
  have hz_b : Format.boundOK F.b z := by
    cases hF_b : F.b with
    | top => trivial
    | coe b =>
      change |((z : Dyadic) : ℚ)| ≤ ((b.val : Dyadic) : ℚ)
      change Format.boundOK F.b y₂ at hb_y₂
      rw [hF_b] at hb_y₂
      have hy₂_le_b : |((y₂ : Dyadic) : ℚ)| ≤ ((b.val : Dyadic) : ℚ) := hb_y₂
      have hz_pos : 0 < ((z : Dyadic) : ℝ) := by
        rw [hz_eq]
        have h_c1_pos : (0 : ℝ) < ((c + 1 : ℤ) : ℝ) := by
          have : 0 < c + 1 := by omega
          exact_mod_cast this
        exact mul_pos h_c1_pos h_2k_pos
      have hy₂_pos : 0 < ((y₂ : Dyadic) : ℝ) := lt_trans h_pos h_lt
      have hz_le_y₂_real : ((z : Dyadic) : ℝ) ≤ ((y₂ : Dyadic) : ℝ) := by
        rw [hz_eq]; exact h_y₂_ge
      -- Transfer ordering/positivity to ℚ.
      have hz_le_y₂_rat : ((z : Dyadic) : ℚ) ≤ ((y₂ : Dyadic) : ℚ) := by
        rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast] at hz_le_y₂_real
        exact_mod_cast hz_le_y₂_real
      have hz_pos_rat : 0 < ((z : Dyadic) : ℚ) := by
        rw [Dyadic.coe_real_eq_ratCast] at hz_pos
        exact_mod_cast hz_pos
      have hy₂_pos_rat : 0 < ((y₂ : Dyadic) : ℚ) := by
        rw [Dyadic.coe_real_eq_ratCast] at hy₂_pos
        exact_mod_cast hy₂_pos
      rw [abs_of_pos hz_pos_rat]
      rw [abs_of_pos hy₂_pos_rat] at hy₂_le_b
      linarith
  have hzF : z ∈ F := ⟨hz_p, hz_q, hz_b⟩
  -- Step 3: F-adjacency gives y₂ ≤ z = (c+1)·2^k.
  have h_z_gt_y₁ : ((y₁ : Dyadic) : ℝ) < ((z : Dyadic) : ℝ) := by
    rw [hy₁_eq, hz_eq]
    have : (c : ℝ) < ((c + 1 : ℤ) : ℝ) := by push_cast; linarith
    nlinarith
  have h_y₂_le_z : ((y₂ : Dyadic) : ℝ) ≤ ((z : Dyadic) : ℝ) :=
    h_adj z hzF h_z_gt_y₁
  rw [hz_eq] at h_y₂_le_z
  linarith

/-- F-adjacent step form for `F.exp = ⊥`: F-adjacent positive `y₁ < y₂ ∈ F`
have `y₁ = c·2^k`, `y₂ = (c+1)·2^k` where `(c, k)` is `y₁`'s grid rep
(`k = ⌊log₂ y₁⌋ - p + 1`). -/
theorem F_adjacent_step_form_exp_bot (F : FiniteFormat) {p : ℕ+}
    (hp : F.p = ((p : ℕ+) : WithTop ℕ+)) (he : F.exp = ⊥)
    {y₁ y₂ : Dyadic} (hy₁F : y₁ ∈ F) (hy₂F : y₂ ∈ F)
    (h_pos : 0 < ((y₁ : Dyadic) : ℝ))
    (h_lt : ((y₁ : Dyadic) : ℝ) < ((y₂ : Dyadic) : ℝ))
    (h_adj : ∀ y : Dyadic, y ∈ F →
              ((y₁ : Dyadic) : ℝ) < ((y : Dyadic) : ℝ) →
              ((y₂ : Dyadic) : ℝ) ≤ ((y : Dyadic) : ℝ)) :
    ∃ (k : ℤ) (c : ℤ),
      0 < c ∧ c < (2 : ℤ) ^ (p : ℕ) ∧
      ((y₁ : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ) ^ k ∧
      ((y₂ : Dyadic) : ℝ) = ((c + 1 : ℤ) : ℝ) * (2 : ℝ) ^ k := by
  obtain ⟨hp_y₁, hq_y₁, hb_y₁⟩ := hy₁F
  obtain ⟨hp_y₂, hq_y₂, hb_y₂⟩ := hy₂F
  obtain ⟨k, c, hc_lt, hy₁_eq, hk_eq⟩ :=
    exists_grid_rep_exp_bot F hp hp_y₁ h_pos
  have hc_pos : 0 < c := grid_rep_c_pos h_pos hy₁_eq
  have hc_lt_int : c < (2 : ℤ) ^ (p : ℕ) := by
    have habs : |c| = c := abs_of_pos hc_pos
    rw [← habs]; exact hc_lt
  refine ⟨k, c, hc_pos, hc_lt_int, hy₁_eq, ?_⟩
  have h_2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
  -- hk_eq has y₁ in it; convert to c·2^k.
  have hk_eq' : k = Int.log 2 ((c : ℝ) * (2 : ℝ) ^ k) - ((p : ℕ) : ℤ) + 1 := by
    have h_log_eq : Int.log 2 ((y₁ : Dyadic) : ℝ) = Int.log 2 ((c : ℝ) * (2 : ℝ) ^ k) := by
      rw [hy₁_eq]
    rw [← h_log_eq]; exact hk_eq
  have h_y₂_ge : ((c + 1 : ℤ) : ℝ) * (2 : ℝ) ^ k ≤ ((y₂ : Dyadic) : ℝ) := by
    by_contra h_lt2
    push Not at h_lt2
    have h_y₁_lt' : (c : ℝ) * (2 : ℝ) ^ k < ((y₂ : Dyadic) : ℝ) := hy₁_eq ▸ h_lt
    exact no_F_element_in_step_interval_exp_bot F hp hc_pos hc_lt_int hk_eq'
      hp_y₂ h_y₁_lt' h_lt2
  set z : Dyadic := Dyadic.ofIntZpow (c + 1) k with hz_def
  have hz_eq : ((z : Dyadic) : ℝ) = ((c + 1 : ℤ) : ℝ) * (2 : ℝ) ^ k := by
    change ((Dyadic.ofIntZpow (c + 1) k : Dyadic) : ℝ) = _
    rw [Dyadic.coe_ofIntZpow]
  have hz_p : Dyadic.precisionAtMost F.p z := by
    rw [hp]
    apply Dyadic.precisionAtMost_of_abs_le (c + 1) k (by rw [Dyadic.coe_rat_ofIntZpow])
    have h_c1_pos : 0 < c + 1 := by omega
    rw [abs_of_pos h_c1_pos]; omega
  have hz_q : Dyadic.quantumAtLeast F.exp z := by
    rw [he]; trivial
  have hz_b : Format.boundOK F.b z := by
    cases hF_b : F.b with
    | top => trivial
    | coe b =>
      change |((z : Dyadic) : ℚ)| ≤ ((b.val : Dyadic) : ℚ)
      change Format.boundOK F.b y₂ at hb_y₂
      rw [hF_b] at hb_y₂
      have hy₂_le_b : |((y₂ : Dyadic) : ℚ)| ≤ ((b.val : Dyadic) : ℚ) := hb_y₂
      have hz_pos : 0 < ((z : Dyadic) : ℝ) := by
        rw [hz_eq]
        have h_c1_pos : (0 : ℝ) < ((c + 1 : ℤ) : ℝ) := by
          have : 0 < c + 1 := by omega
          exact_mod_cast this
        exact mul_pos h_c1_pos h_2k_pos
      have hy₂_pos : 0 < ((y₂ : Dyadic) : ℝ) := lt_trans h_pos h_lt
      have hz_le_y₂_real : ((z : Dyadic) : ℝ) ≤ ((y₂ : Dyadic) : ℝ) := by
        rw [hz_eq]; exact h_y₂_ge
      have hz_le_y₂_rat : ((z : Dyadic) : ℚ) ≤ ((y₂ : Dyadic) : ℚ) := by
        rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast] at hz_le_y₂_real
        exact_mod_cast hz_le_y₂_real
      have hz_pos_rat : 0 < ((z : Dyadic) : ℚ) := by
        rw [Dyadic.coe_real_eq_ratCast] at hz_pos
        exact_mod_cast hz_pos
      have hy₂_pos_rat : 0 < ((y₂ : Dyadic) : ℚ) := by
        rw [Dyadic.coe_real_eq_ratCast] at hy₂_pos
        exact_mod_cast hy₂_pos
      rw [abs_of_pos hz_pos_rat]
      rw [abs_of_pos hy₂_pos_rat] at hy₂_le_b
      linarith
  have hzF : z ∈ F := ⟨hz_p, hz_q, hz_b⟩
  have h_z_gt_y₁ : ((y₁ : Dyadic) : ℝ) < ((z : Dyadic) : ℝ) := by
    rw [hy₁_eq, hz_eq]
    have : (c : ℝ) < ((c + 1 : ℤ) : ℝ) := by push_cast; linarith
    nlinarith
  have h_y₂_le_z : ((y₂ : Dyadic) : ℝ) ≤ ((z : Dyadic) : ℝ) :=
    h_adj z hzF h_z_gt_y₁
  rw [hz_eq] at h_y₂_le_z
  linarith

/-- **F-predecessor of `m`** for the finite-precision finite-exp case.

Given `m ∈ F` positive with grid representation `(c, k)` where `c ≥ 2` and
`(c-1)·2^k` lies in the same magnitude class as `m` (`Int.log 2` equal),
the predecessor `(c-1)·2^k` is in `F` and is F-adjacent to `m` (no F-element
strictly between).

Used to extract the F-predecessor of a midpoint at proof time when the exact
F-structure is hypothesized only as a containment. -/
theorem prev_F_adjacent_of_log_eq (F : FiniteFormat) {p : ℕ+} {exp : ℤ}
    (hp : F.p = ((p : ℕ+) : WithTop ℕ+)) (he : F.exp = (exp : WithBot ℤ))
    {m : Dyadic} (hmF : m ∈ F) (hm_pos : 0 < ((m : Dyadic) : ℝ))
    {k c : ℤ} (hk : k ≥ exp) (hc_ge_2 : 2 ≤ c) (hc_lt : c < (2 : ℤ) ^ (p : ℕ))
    (hm_eq : ((m : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ) ^ k)
    (hk_max : k = max exp (Int.log 2 ((c : ℝ) * (2 : ℝ) ^ k) - ((p : ℕ) : ℤ) + 1))
    (h_log_eq : Int.log 2 (((c - 1 : ℤ) : ℝ) * (2 : ℝ) ^ k) =
                Int.log 2 ((c : ℝ) * (2 : ℝ) ^ k)) :
    Dyadic.ofIntZpow (c - 1) k ∈ F ∧
    ((Dyadic.ofIntZpow (c - 1) k : Dyadic) : ℝ) < ((m : Dyadic) : ℝ) ∧
    ∀ z : Dyadic, z ∈ F → ((z : Dyadic) : ℝ) < ((m : Dyadic) : ℝ) →
      ((z : Dyadic) : ℝ) ≤ ((Dyadic.ofIntZpow (c - 1) k : Dyadic) : ℝ) := by
  have h_2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
  have hc_1_pos : 0 < c - 1 := by omega
  have hc_1_pos_real : (0 : ℝ) < ((c - 1 : ℤ) : ℝ) := by exact_mod_cast hc_1_pos
  have hc_1_lt : c - 1 < (2 : ℤ) ^ (p : ℕ) := by omega
  have h_prev_pos : 0 < ((Dyadic.ofIntZpow (c - 1) k : Dyadic) : ℝ) := by
    rw [Dyadic.coe_ofIntZpow]; exact mul_pos hc_1_pos_real h_2k_pos
  have h_prev_lt_m : ((Dyadic.ofIntZpow (c - 1) k : Dyadic) : ℝ) < ((m : Dyadic) : ℝ) := by
    rw [Dyadic.coe_ofIntZpow, hm_eq]
    have : ((c - 1 : ℤ) : ℝ) < (c : ℝ) := by push_cast; linarith
    nlinarith
  refine ⟨?_, h_prev_lt_m, ?_⟩
  · -- (c-1)·2^k ∈ F.
    refine ⟨?_, ?_, ?_⟩
    · -- precisionAtMost p
      rw [hp]
      apply Dyadic.precisionAtMost_of_abs_le (c - 1) k (by rw [Dyadic.coe_rat_ofIntZpow])
      have h_abs : |c - 1| = c - 1 := abs_of_pos hc_1_pos
      rw [h_abs]; omega
    · -- quantumAtLeast exp
      rw [he]
      rw [Dyadic.quantumAtLeast_coe_real]
      refine ⟨(c - 1) * (2 : ℤ) ^ (k - exp).toNat, ?_⟩
      rw [Dyadic.coe_ofIntZpow]
      have h_diff_nn : 0 ≤ k - exp := by omega
      have h_split : (2 : ℝ) ^ k = (2 : ℝ) ^ ((k - exp).toNat : ℤ) * (2 : ℝ) ^ exp := by
        rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        congr 1; rw [Int.toNat_of_nonneg h_diff_nn]; ring
      rw [h_split, zpow_natCast]; push_cast; ring
    · -- boundOK F.b: |prev| ≤ |m| ≤ b.
      have hb_m : Format.boundOK F.b m := hmF.2.2
      cases hF_b : F.b with
      | top => trivial
      | coe b =>
        rw [hF_b] at hb_m
        change |((m : Dyadic) : ℚ)| ≤ ((b.val : Dyadic) : ℚ) at hb_m
        have hm_pos_rat : 0 < ((m : Dyadic) : ℚ) := by
          rw [Dyadic.coe_real_eq_ratCast] at hm_pos
          exact_mod_cast hm_pos
        rw [abs_of_pos hm_pos_rat] at hb_m
        change |((Dyadic.ofIntZpow (c - 1) k : Dyadic) : ℚ)| ≤ ((b.val : Dyadic) : ℚ)
        have h_prev_pos_rat : 0 < ((Dyadic.ofIntZpow (c - 1) k : Dyadic) : ℚ) := by
          rw [Dyadic.coe_real_eq_ratCast] at h_prev_pos
          exact_mod_cast h_prev_pos
        rw [abs_of_pos h_prev_pos_rat]
        have h_prev_lt_m_rat :
            ((Dyadic.ofIntZpow (c - 1) k : Dyadic) : ℚ) < ((m : Dyadic) : ℚ) := by
          rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast] at h_prev_lt_m
          exact_mod_cast h_prev_lt_m
        linarith
  · -- F-adjacency: no F-element z with prev < z < m.
    intro z hzF hz_lt
    by_contra h_gt
    push Not at h_gt
    rw [Dyadic.coe_ofIntZpow] at h_gt
    -- z lies in ((c-1)·2^k, c·2^k = m). Apply no_F_element_in_step_interval with c-1.
    have h_z_lt_c : ((z : Dyadic) : ℝ) < (((c - 1 : ℤ) + 1 : ℤ) : ℝ) * (2 : ℝ) ^ k := by
      have h_simp : ((c - 1 : ℤ) + 1 : ℤ) = c := by ring
      rw [h_simp, ← hm_eq]; exact hz_lt
    have hk_max_c1 : k = max exp
        (Int.log 2 (((c - 1 : ℤ) : ℝ) * (2 : ℝ) ^ k) - ((p : ℕ) : ℤ) + 1) := by
      rw [h_log_eq]; exact hk_max
    exact no_F_element_in_step_interval F hp he hc_1_pos hc_1_lt hk hk_max_c1
      hzF.1 hzF.2.1 h_gt h_z_lt_c

/-- The precision component of `F.extend 1` for `F.p = (p : ℕ+)`:
it is `(p + 1 : ℕ+)`. The `ℕ+` arithmetic `(p:ℕ+)+1 = (p+1:ℕ+)` is
definitional. -/
private theorem extend_one_p (F : FiniteFormat) {p : ℕ+}
    (hp : F.p = ((p : ℕ+) : WithTop ℕ+)) :
    (F.extend 1).p = (((p + 1 : ℕ+)) : WithTop ℕ+) := by
  change F.p.map (· + (1 : ℕ+)) = _
  rw [hp, WithTop.map_coe]

/-- `((p + 1 : ℕ+) : ℕ) = (p : ℕ) + 1`. -/
private theorem pnat_succ_natCast (p : ℕ+) : (((p + 1 : ℕ+)) : ℕ) = (p : ℕ) + 1 := by
  exact_mod_cast rfl

/-- Midpoint of F-adjacent values lies in `F.extend 1`. The midpoint computes
to `(2c+1)·2^(k-1)` where `(c, k)` is `y₁`'s grid rep and `y₂ = (c+1)·2^k`,
giving `|2c+1| < 2^(p+1)`, hence precision ≤ `p+1`. -/
theorem midpoint_mem_extend_one_of_F_adjacent_pos (F : FiniteFormat)
    {p : ℕ+} {exp : ℤ}
    (hp : F.p = ((p : ℕ+) : WithTop ℕ+)) (he : F.exp = (exp : WithBot ℤ))
    {y₁ y₂ : Dyadic} (hy₁F : y₁ ∈ F) (hy₂F : y₂ ∈ F)
    (h_pos : 0 < ((y₁ : Dyadic) : ℝ))
    (h_lt : ((y₁ : Dyadic) : ℝ) < ((y₂ : Dyadic) : ℝ))
    (h_adj : ∀ y : Dyadic, y ∈ F →
              ((y₁ : Dyadic) : ℝ) < ((y : Dyadic) : ℝ) →
              ((y₂ : Dyadic) : ℝ) ≤ ((y : Dyadic) : ℝ)) :
    Dyadic.midpoint y₁ y₂ ∈ F.extend 1 := by
  obtain ⟨k, c, hk_ge_exp, hc_pos, hc_lt, hy₁_eq, hy₂_eq⟩ :=
    F_adjacent_step_form F hp he hy₁F hy₂F h_pos h_lt h_adj
  have h_2_ne : (2 : ℝ) ≠ 0 := by norm_num
  have h_2q_ne : (2 : ℚ) ≠ 0 := by norm_num
  have h_2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
  -- ℝ-valued midpoint form.
  have h_mid_eq : ((Dyadic.midpoint y₁ y₂ : Dyadic) : ℝ)
      = ((2 * c + 1 : ℤ) : ℝ) * (2 : ℝ) ^ (k - 1) := by
    rw [Dyadic.coe_midpoint, hy₁_eq, hy₂_eq, zpow_sub₀ h_2_ne]
    push_cast; field_simp; ring
  -- ℚ-valued midpoint form (needed for `precisionAtMost_of_abs_le`).
  have hy₁_eq_rat : ((y₁ : Dyadic) : ℚ) = (c : ℚ) * (2 : ℚ) ^ k := by
    have h : (((y₁ : Dyadic) : ℚ) : ℝ) = (((c : ℚ) * (2 : ℚ) ^ k : ℚ) : ℝ) := by
      rw [← Dyadic.coe_real_eq_ratCast, hy₁_eq]; push_cast; ring
    exact_mod_cast h
  have hy₂_eq_rat : ((y₂ : Dyadic) : ℚ) = ((c + 1 : ℤ) : ℚ) * (2 : ℚ) ^ k := by
    have h : (((y₂ : Dyadic) : ℚ) : ℝ) = ((((c + 1 : ℤ) : ℚ) * (2 : ℚ) ^ k : ℚ) : ℝ) := by
      rw [← Dyadic.coe_real_eq_ratCast, hy₂_eq]; push_cast; ring
    exact_mod_cast h
  have h_mid_eq_rat : ((Dyadic.midpoint y₁ y₂ : Dyadic) : ℚ)
      = ((2 * c + 1 : ℤ) : ℚ) * (2 : ℚ) ^ (k - 1) := by
    rw [Dyadic.coe_rat_midpoint, hy₁_eq_rat, hy₂_eq_rat, zpow_sub₀ h_2q_ne]
    push_cast; field_simp; ring
  refine ⟨?_, ?_, ?_⟩
  · -- precisionAtMost (F.extend 1).p midpoint
    rw [extend_one_p F hp]
    apply Dyadic.precisionAtMost_of_abs_le (2 * c + 1) (k - 1) h_mid_eq_rat
    have h_c1_pos : 0 < 2 * c + 1 := by omega
    rw [abs_of_pos h_c1_pos, pnat_succ_natCast]
    have h_pow : (2 : ℤ) ^ ((p : ℕ) + 1) = 2 * (2 : ℤ) ^ (p : ℕ) := by
      rw [pow_succ]; ring
    omega
  · -- quantumAtLeast (F.exp - 1) midpoint
    show Dyadic.quantumAtLeast (F.extend 1).exp _
    have h_exp_extend : (F.extend 1).exp = (((exp - 1 : ℤ)) : WithBot ℤ) := by
      change F.exp.map (· - ((1 : ℕ+) : ℤ)) = _
      rw [he, WithBot.map_coe]
      have : ((1 : ℕ+) : ℤ) = 1 := rfl
      rw [this]
    rw [h_exp_extend, Dyadic.quantumAtLeast_coe_real]
    refine ⟨(2 * c + 1) * (2 : ℤ) ^ (k - 1 - (exp - 1)).toNat, ?_⟩
    rw [h_mid_eq]
    have h_diff_nn : 0 ≤ k - 1 - (exp - 1) := by omega
    have h_eq_zpow : (2 : ℝ) ^ (k - 1) =
        (2 : ℝ) ^ ((k - 1 - (exp - 1)).toNat : ℤ) * (2 : ℝ) ^ (exp - 1) := by
      rw [Int.toNat_of_nonneg h_diff_nn, ← zpow_add₀ h_2_ne]
      congr 1; omega
    rw [h_eq_zpow, zpow_natCast]; push_cast; ring
  · -- bound: |midpoint| ≤ b, computed over ℚ.
    show Format.boundOK (F.extend 1).b _
    have h_b : (F.extend 1).b = F.b := rfl
    rw [h_b]
    cases hF_b : F.b with
    | top => trivial
    | coe b =>
      change |((Dyadic.midpoint y₁ y₂ : Dyadic) : ℚ)| ≤ ((b.val : Dyadic) : ℚ)
      rw [Dyadic.coe_rat_midpoint]
      have hy₁_b : Format.boundOK F.b y₁ := hy₁F.2.2
      have hy₂_b : Format.boundOK F.b y₂ := hy₂F.2.2
      rw [hF_b] at hy₁_b hy₂_b
      have h1 : |((y₁ : Dyadic) : ℚ)| ≤ ((b.val : Dyadic) : ℚ) := hy₁_b
      have h2 : |((y₂ : Dyadic) : ℚ)| ≤ ((b.val : Dyadic) : ℚ) := hy₂_b
      have h_tri : |((y₁ : Dyadic) : ℚ) + ((y₂ : Dyadic) : ℚ)|
          ≤ |((y₁ : Dyadic) : ℚ)| + |((y₂ : Dyadic) : ℚ)| := abs_add_le _ _
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℚ) < 2)]
      linarith

/-- Midpoint lemma for F.exp = ⊥, positive case. Same as the finite-exp version
but quantum check is trivial. -/
theorem midpoint_mem_extend_one_of_F_adjacent_pos_exp_bot (F : FiniteFormat) {p : ℕ+}
    (hp : F.p = ((p : ℕ+) : WithTop ℕ+)) (he : F.exp = ⊥)
    {y₁ y₂ : Dyadic} (hy₁F : y₁ ∈ F) (hy₂F : y₂ ∈ F)
    (h_pos : 0 < ((y₁ : Dyadic) : ℝ))
    (h_lt : ((y₁ : Dyadic) : ℝ) < ((y₂ : Dyadic) : ℝ))
    (h_adj : ∀ y : Dyadic, y ∈ F →
              ((y₁ : Dyadic) : ℝ) < ((y : Dyadic) : ℝ) →
              ((y₂ : Dyadic) : ℝ) ≤ ((y : Dyadic) : ℝ)) :
    Dyadic.midpoint y₁ y₂ ∈ F.extend 1 := by
  obtain ⟨k, c, hc_pos, hc_lt, hy₁_eq, hy₂_eq⟩ :=
    F_adjacent_step_form_exp_bot F hp he hy₁F hy₂F h_pos h_lt h_adj
  have h_2_ne : (2 : ℝ) ≠ 0 := by norm_num
  have h_2q_ne : (2 : ℚ) ≠ 0 := by norm_num
  have h_2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
  have hy₁_eq_rat : ((y₁ : Dyadic) : ℚ) = (c : ℚ) * (2 : ℚ) ^ k := by
    have h : (((y₁ : Dyadic) : ℚ) : ℝ) = (((c : ℚ) * (2 : ℚ) ^ k : ℚ) : ℝ) := by
      rw [← Dyadic.coe_real_eq_ratCast, hy₁_eq]; push_cast; ring
    exact_mod_cast h
  have hy₂_eq_rat : ((y₂ : Dyadic) : ℚ) = ((c + 1 : ℤ) : ℚ) * (2 : ℚ) ^ k := by
    have h : (((y₂ : Dyadic) : ℚ) : ℝ) = ((((c + 1 : ℤ) : ℚ) * (2 : ℚ) ^ k : ℚ) : ℝ) := by
      rw [← Dyadic.coe_real_eq_ratCast, hy₂_eq]; push_cast; ring
    exact_mod_cast h
  have h_mid_eq_rat : ((Dyadic.midpoint y₁ y₂ : Dyadic) : ℚ)
      = ((2 * c + 1 : ℤ) : ℚ) * (2 : ℚ) ^ (k - 1) := by
    rw [Dyadic.coe_rat_midpoint, hy₁_eq_rat, hy₂_eq_rat, zpow_sub₀ h_2q_ne]
    push_cast; field_simp; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [extend_one_p F hp]
    apply Dyadic.precisionAtMost_of_abs_le (2 * c + 1) (k - 1) h_mid_eq_rat
    have h_c1_pos : 0 < 2 * c + 1 := by omega
    rw [abs_of_pos h_c1_pos, pnat_succ_natCast]
    have h_pow : (2 : ℤ) ^ ((p : ℕ) + 1) = 2 * (2 : ℤ) ^ (p : ℕ) := by
      rw [pow_succ]; ring
    omega
  · -- F.extend 1 .exp = ⊥ (since F.exp = ⊥). Quantum trivial.
    show Dyadic.quantumAtLeast (F.extend 1).exp _
    have h_exp_extend : (F.extend 1).exp = ⊥ := by
      change F.exp.map (· - ((1 : ℕ+) : ℤ)) = _
      rw [he]; rfl
    rw [h_exp_extend]; trivial
  · show Format.boundOK (F.extend 1).b _
    have h_b : (F.extend 1).b = F.b := rfl
    rw [h_b]
    cases hF_b : F.b with
    | top => trivial
    | coe b =>
      change |((Dyadic.midpoint y₁ y₂ : Dyadic) : ℚ)| ≤ ((b.val : Dyadic) : ℚ)
      rw [Dyadic.coe_rat_midpoint]
      have hy₁_b : Format.boundOK F.b y₁ := hy₁F.2.2
      have hy₂_b : Format.boundOK F.b y₂ := hy₂F.2.2
      rw [hF_b] at hy₁_b hy₂_b
      have h1 : |((y₁ : Dyadic) : ℚ)| ≤ ((b.val : Dyadic) : ℚ) := hy₁_b
      have h2 : |((y₂ : Dyadic) : ℚ)| ≤ ((b.val : Dyadic) : ℚ) := hy₂_b
      have h_tri : |((y₁ : Dyadic) : ℚ) + ((y₂ : Dyadic) : ℚ)|
          ≤ |((y₁ : Dyadic) : ℚ)| + |((y₂ : Dyadic) : ℚ)| := abs_add_le _ _
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℚ) < 2)]
      linarith

/-- For `y ∈ F` (any F shape), `midpoint(0, y) = y/2 ∈ F.extend 1`.
Handles both `F.exp = ⊥` and `F.exp = (e : ℤ)` cases. -/
theorem half_mem_extend_one (F : FiniteFormat) {p : ℕ+}
    (hp : F.p = ((p : ℕ+) : WithTop ℕ+))
    {y : Dyadic} (hyF : y ∈ F) :
    (Dyadic.midpoint 0 y : Dyadic) ∈ F.extend 1 := by
  obtain ⟨hp_y, hq_y, hb_y⟩ := hyF
  have h_mid_eq : ((Dyadic.midpoint 0 y : Dyadic) : ℝ) = ((y : Dyadic) : ℝ) / 2 := by
    rw [Dyadic.coe_midpoint]; push_cast; ring
  have h_mid_eq_rat : ((Dyadic.midpoint 0 y : Dyadic) : ℚ) = ((y : Dyadic) : ℚ) / 2 := by
    rw [Dyadic.coe_rat_midpoint]; push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · -- precisionAtMost (F.extend 1).p.
    show Dyadic.precisionAtMost (F.extend 1).p _
    have h_p_le : F.p ≤ (F.extend 1).p := by
      rw [hp, extend_one_p F hp]
      exact WithTop.coe_le_coe.mpr (by exact_mod_cast Nat.le_succ (p : ℕ))
    apply Dyadic.precisionAtMost_mono h_p_le
    rw [hp]
    rw [hp] at hp_y
    rw [Dyadic.precisionAtMost_coe] at hp_y ⊢
    obtain ⟨c, e, hy_eq, hc_lt⟩ := hp_y
    refine ⟨c, e - 1, ?_, hc_lt⟩
    rw [h_mid_eq_rat, hy_eq, zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0)]
    field_simp
  · -- quantumAtLeast ((F.exp).map (· - 1)).
    show Dyadic.quantumAtLeast (F.extend 1).exp _
    have h_exp_eq : (F.extend 1).exp = F.exp.map (· - ((1 : ℕ+) : ℤ)) := rfl
    rw [h_exp_eq]
    cases hF_exp : F.exp with
    | bot => trivial
    | coe e =>
      rw [WithBot.map_coe]
      change Dyadic.quantumAtLeast (((e - (1 : ℕ+)) : ℤ) : WithBot ℤ) _
      rw [Dyadic.quantumAtLeast_coe]
      rw [hF_exp] at hq_y
      rw [Dyadic.quantumAtLeast_coe] at hq_y
      obtain ⟨c, hy_eq⟩ := hq_y
      refine ⟨c, ?_⟩
      rw [h_mid_eq_rat, hy_eq]
      have : ((1 : ℕ+) : ℤ) = 1 := rfl
      rw [this, zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0)]
      field_simp
  · -- bound: |y/2| ≤ b.
    show Format.boundOK (F.extend 1).b _
    have h_b : (F.extend 1).b = F.b := rfl
    rw [h_b]
    cases hF_b : F.b with
    | top => trivial
    | coe b =>
      change |((Dyadic.midpoint 0 y : Dyadic) : ℚ)| ≤ ((b.val : Dyadic) : ℚ)
      rw [h_mid_eq_rat]
      have hb_y' : Format.boundOK F.b y := hb_y
      rw [hF_b] at hb_y'
      have h_b_nn : 0 ≤ ((b.val : Dyadic) : ℚ) := b.2
      have hy_le : |((y : Dyadic) : ℚ)| ≤ ((b.val : Dyadic) : ℚ) := hb_y'
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℚ) < 2)]
      linarith

/-- Midpoint of F-adjacent values (general — both signs handled).

For `y₁ < y₂` F-adjacent in `F`, `midpoint y₁ y₂ ∈ F.extend 1`. The proof
case-splits on the sign of `y₁`:
- `y₁ > 0`: positive case (`midpoint_mem_extend_one_of_F_adjacent_pos`).
- `y₁ = 0`: midpoint is `y₂/2`, handled by `half_mem_extend_one`.
- `y₁ < 0` and `y₂ ≤ 0`: negate, apply positive case to `(-y₂, -y₁)`, then negate back.
- `y₁ < 0 < y₂`: ruled out by F-adjacency since `0 ∈ F`. -/
theorem midpoint_mem_extend_one_of_F_adjacent (F : FiniteFormat) {p : ℕ+} {exp : ℤ}
    (hp : F.p = ((p : ℕ+) : WithTop ℕ+)) (he : F.exp = (exp : WithBot ℤ))
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
      have h_neg_in_extend := midpoint_mem_extend_one_of_F_adjacent_pos
        F hp he (FiniteFormat.neg_mem hy₂F) (FiniteFormat.neg_mem hy₁F)
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
      have h_half := half_mem_extend_one F hp h_neg_y₁F
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
    exact half_mem_extend_one F hp hy₂F
  · -- y₁ > 0.
    exact midpoint_mem_extend_one_of_F_adjacent_pos
      F hp he hy₁F hy₂F hy₁_pos h_lt h_adj

/-- General signed midpoint lemma for F.exp = ⊥, F.p finite. Same dispatch
structure as `midpoint_mem_extend_one_of_F_adjacent` but using the
`_exp_bot` positive case. -/
theorem midpoint_mem_extend_one_of_F_adjacent_exp_bot (F : FiniteFormat) {p : ℕ+}
    (hp : F.p = ((p : ℕ+) : WithTop ℕ+)) (he : F.exp = ⊥)
    {y₁ y₂ : Dyadic} (hy₁F : y₁ ∈ F) (hy₂F : y₂ ∈ F)
    (h_lt : ((y₁ : Dyadic) : ℝ) < ((y₂ : Dyadic) : ℝ))
    (h_adj : ∀ y : Dyadic, y ∈ F →
              ((y₁ : Dyadic) : ℝ) < ((y : Dyadic) : ℝ) →
              ((y₂ : Dyadic) : ℝ) ≤ ((y : Dyadic) : ℝ)) :
    Dyadic.midpoint y₁ y₂ ∈ F.extend 1 := by
  rcases lt_trichotomy ((y₁ : Dyadic) : ℝ) 0 with hy₁_neg | hy₁_zero | hy₁_pos
  · rcases lt_trichotomy ((y₂ : Dyadic) : ℝ) 0 with hy₂_neg | hy₂_zero | hy₂_pos
    · have h_neg_y₁_pos : 0 < ((-y₁ : Dyadic) : ℝ) := by push_cast; linarith
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
      have h_neg_in_extend := midpoint_mem_extend_one_of_F_adjacent_pos_exp_bot
        F hp he (FiniteFormat.neg_mem hy₂F) (FiniteFormat.neg_mem hy₁F)
        h_neg_y₂_pos h_lt' h_adj'
      have h_mid_neg : Dyadic.midpoint (-y₂) (-y₁) = -(Dyadic.midpoint y₁ y₂) := by
        apply Dyadic.ext_real
        simp only [Dyadic.coe_midpoint, Dyadic.coe_real_neg]
        ring
      rw [h_mid_neg] at h_neg_in_extend
      have := FiniteFormat.neg_mem h_neg_in_extend
      rw [neg_neg] at this
      exact this
    · have h_y₂_eq_0 : y₂ = 0 := Dyadic.ext_real (by rw [Dyadic.coe_real_zero]; exact hy₂_zero)
      rw [h_y₂_eq_0]
      have h_mid_eq : Dyadic.midpoint y₁ 0 = -(Dyadic.midpoint 0 (-y₁)) := by
        apply Dyadic.ext_real
        simp only [Dyadic.coe_midpoint, Dyadic.coe_real_neg]
        push_cast; ring
      rw [h_mid_eq]
      have h_neg_y₁F : -y₁ ∈ F := FiniteFormat.neg_mem hy₁F
      have h_half := half_mem_extend_one F hp h_neg_y₁F
      exact FiniteFormat.neg_mem h_half
    · exfalso
      have h_0_F : (0 : Dyadic) ∈ F := FiniteFormat.zero_mem F
      have h_0_gt : ((y₁ : Dyadic) : ℝ) < ((0 : Dyadic) : ℝ) := by
        rw [Dyadic.coe_real_zero]; exact hy₁_neg
      have h_y₂_le : ((y₂ : Dyadic) : ℝ) ≤ ((0 : Dyadic) : ℝ) := h_adj 0 h_0_F h_0_gt
      rw [Dyadic.coe_real_zero] at h_y₂_le
      linarith
  · have h_y₁_eq_0 : y₁ = 0 := Dyadic.ext_real (by rw [Dyadic.coe_real_zero]; exact hy₁_zero)
    rw [h_y₁_eq_0]
    exact half_mem_extend_one F hp hy₂F
  · exact midpoint_mem_extend_one_of_F_adjacent_pos_exp_bot
      F hp he hy₁F hy₂F hy₁_pos h_lt h_adj

/-- For `F.p = ⊤` and `F.exp` finite, midpoint of any two F-elements lies in
`F.extend 1`. F-adjacency isn't required since precision is unrestricted. -/
theorem midpoint_mem_extend_one_of_p_top (F : FiniteFormat) {exp : ℤ}
    (hp : F.p = ⊤) (he : F.exp = (exp : WithBot ℤ))
    {y₁ y₂ : Dyadic} (hy₁F : y₁ ∈ F) (hy₂F : y₂ ∈ F) :
    Dyadic.midpoint y₁ y₂ ∈ F.extend 1 := by
  obtain ⟨_, hq_y₁, hb_y₁⟩ := hy₁F
  obtain ⟨_, hq_y₂, hb_y₂⟩ := hy₂F
  refine ⟨?_, ?_, ?_⟩
  · -- precision: (F.extend 1).p = ⊤. Trivial.
    show Dyadic.precisionAtMost (F.extend 1).p _
    have h_p_top : (F.extend 1).p = ⊤ := by
      change F.p.map (· + (1 : ℕ+)) = _
      rw [hp]; rfl
    rw [h_p_top]; trivial
  · -- quantum: midpoint at quantum exp - 1.
    show Dyadic.quantumAtLeast (F.extend 1).exp _
    have h_exp_map : (F.extend 1).exp = ((exp - 1 : ℤ) : WithBot ℤ) := by
      change F.exp.map (· - ((1 : ℕ+) : ℤ)) = _
      rw [he, WithBot.map_coe]
      have : ((1 : ℕ+) : ℤ) = 1 := rfl
      rw [this]
    rw [h_exp_map, Dyadic.quantumAtLeast_coe]
    rw [he, Dyadic.quantumAtLeast_coe] at hq_y₁ hq_y₂
    obtain ⟨c₁, hc₁⟩ := hq_y₁
    obtain ⟨c₂, hc₂⟩ := hq_y₂
    refine ⟨c₁ + c₂, ?_⟩
    rw [Dyadic.coe_rat_midpoint, hc₁, hc₂]
    rw [zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0)]
    push_cast; field_simp
  · -- bound: |midpoint| ≤ b, over ℚ.
    show Format.boundOK (F.extend 1).b _
    have h_b : (F.extend 1).b = F.b := rfl
    rw [h_b]
    cases hF_b : F.b with
    | top => trivial
    | coe b =>
      change |((Dyadic.midpoint y₁ y₂ : Dyadic) : ℚ)| ≤ ((b.val : Dyadic) : ℚ)
      rw [Dyadic.coe_rat_midpoint]
      have hb_y₁' : Format.boundOK F.b y₁ := hb_y₁
      have hb_y₂' : Format.boundOK F.b y₂ := hb_y₂
      rw [hF_b] at hb_y₁' hb_y₂'
      have h1 : |((y₁ : Dyadic) : ℚ)| ≤ ((b.val : Dyadic) : ℚ) := hb_y₁'
      have h2 : |((y₂ : Dyadic) : ℚ)| ≤ ((b.val : Dyadic) : ℚ) := hb_y₂'
      have h_tri : |((y₁ : Dyadic) : ℚ) + ((y₂ : Dyadic) : ℚ)|
          ≤ |((y₁ : Dyadic) : ℚ)| + |((y₂ : Dyadic) : ℚ)| := abs_add_le _ _
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℚ) < 2)]
      linarith

end Mpfx
