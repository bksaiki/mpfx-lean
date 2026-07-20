import Mpfx.RoundOp.Defs
import Mpfx.RoundOp.Directed

/-!
# Constructive rounding: `toOdd` obligations

Soundness and uniqueness for the `toOdd` rounding mode.
-/

namespace Mpfx

attribute [local instance] Classical.propDecidable

/-- Shared `toOdd` parity dispatch. Runs the 6-leaf `(F.p, F.exp) × regime`
format case tree **once**, returning the parity-alternation iff
`IsOdd dhi ↔ ¬ IsOdd dlo` for the canonical neighbours
`dlo = lo·2^e`, `dhi = (lo+1)·2^e` (`e = canonicalExp x`, `lo = ⌊x·2^(-e)⌋`).
The soundness proof consumes the `.mpr` direction (given `¬ IsOdd dlo`, the
odd neighbour is `dhi`); the uniqueness proof consumes it via
`not_both_isOdd_of_alternating_iff`. Every leaf is a thin wrapper over the
shared `alternating_parity_*_iff` cores in `Format.lean` (saturation leaves
build the iff directly from `isOdd_iff_odd_at_canonical_mixed_subnormal` and
`not_isOdd_at_saturation_mixed_normal`); the only mode-specific inputs are
`x ≠ 0` and `(lo : ℝ) ≠ s`, whose differing derivations stay at the call
sites. -/
private theorem toOdd_neighbors_alternate {F : FiniteFormat} (x : ℝ)
    (h : ¬ F.IsUndefined .toOdd)
    (hx_ne : x ≠ 0)
    (h_lo_ne_s :
      (⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ : ℝ) ≠ x * (2 : ℝ) ^ (-F.canonicalExp x)) :
    (F.toParityFormatOfToOdd h).IsOdd
        (Dyadic.ofIntZpow (⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ + 1) (F.canonicalExp x))
      ↔ ¬ (F.toParityFormatOfToOdd h).IsOdd
        (Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ (F.canonicalExp x)) := by
  set e := F.canonicalExp x with h_e_def
  set s := x * (2 : ℝ) ^ (-e) with h_s_def
  set lo : ℤ := ⌊s⌋ with h_lo_def
  set dlo : Dyadic := Dyadic.ofIntZpow lo e with h_dlo_def
  set dhi : Dyadic := Dyadic.ofIntZpow (lo + 1) e with h_dhi_def
  set F'' := F.toParityFormatOfToOdd h with hF''_def
  have h_not_undef : ¬ (F.p = ⊤ ∧ F.exp = ⊥) :=
    fun ⟨hp, hexp⟩ => F.finite.elim (fun hh => hh hp) (fun hh => hh hexp)
  have h_floor_le_s : (lo : ℝ) ≤ s := Int.floor_le _
  have h_lo_bound : ∀ {p : ℕ+}, F.p = ((p : ℕ+) : WithTop ℕ+) →
      |lo| ≤ (2 : ℤ) ^ (p : ℕ) := fun hp => by
    apply abs_floor_le_of_abs_lt
    push_cast; exact floor_mantissa_lt hp
  have h_lop1_bound : ∀ {p : ℕ+}, F.p = ((p : ℕ+) : WithTop ℕ+) →
      |lo + 1| ≤ (2 : ℤ) ^ (p : ℕ) := fun hp =>
    abs_floor_add_one_le_of_abs_lt (floor_mantissa_lt hp)
  have h_dlo_real : (dlo : ℝ) = (lo : ℝ) * (2 : ℝ) ^ e :=
    Dyadic.coe_ofIntZpow _ _
  have h_dhi_real : (dhi : ℝ) = ((lo + 1 : ℤ) : ℝ) * (2 : ℝ) ^ e :=
    Dyadic.coe_ofIntZpow _ _
  cases hp_F : F.p with
  | top =>
    cases hexp_F : F.exp with
    | bot => exact absurd ⟨hp_F, hexp_F⟩ h_not_undef
    | coe e'' =>
      have h_e_eq : e = e'' := by
        change F.canonicalExp x = _
        unfold FiniteFormat.canonicalExp
        simp [hp_F, hexp_F]
      have h_dlo_at_e'' : dlo = Dyadic.ofIntZpow lo e'' := by rw [h_dlo_def, h_e_eq]
      have h_dhi_at_e'' : dhi = Dyadic.ofIntZpow (lo + 1) e'' := by rw [h_dhi_def, h_e_eq]
      rw [h_dhi_at_e'', h_dlo_at_e'']
      exact ParityFormat.alternating_parity_fixedpoint_iff hp_F hexp_F
  | coe p =>
    cases hexp_F : F.exp with
    | bot =>
      have hp_ne_1 : F.p ≠ ((1 : ℕ+) : WithTop ℕ+) := fun h_eq =>
        h ⟨h_eq, hexp_F, Or.inl rfl⟩
      have h_s_lt_p : |x * (2 : ℝ) ^ (-e)| < (2 : ℝ) ^ (p : ℕ) :=
        floor_mantissa_lt hp_F
      have h_lo_hi : |lo| ≤ (2 : ℤ) ^ (p : ℕ) := by
        apply abs_floor_le_of_abs_lt; push_cast; exact h_s_lt_p
      have h_lop1_hi : |lo + 1| ≤ (2 : ℤ) ^ (p : ℕ) :=
        abs_floor_add_one_le_of_abs_lt h_s_lt_p
      have h_e_eq_log : e = Int.log 2 |x| + 1 - (p : ℤ) := by
        change F.canonicalExp x = _
        unfold FiniteFormat.canonicalExp
        simp [hp_F, hexp_F, hx_ne]
      have h_s_lo_real : ((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) ≤
          |x * (2 : ℝ) ^ (-e)| :=
        two_pow_pred_le_scaled (p := p) hx_ne h_e_eq_log
      have h_lo_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo| :=
        abs_floor_ge_two_pow_pred (p := p) h_s_lo_real
      have h_lop1_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo + 1| := by
        by_cases hs_nn : 0 ≤ s
        · have h_lo_nn : 0 ≤ lo := Int.floor_nonneg.mpr hs_nn
          rw [abs_of_nonneg (by linarith : (0 : ℤ) ≤ lo + 1)]
          linarith [h_lo_lo, abs_of_nonneg h_lo_nn]
        · have hs_neg : s < 0 := not_le.mp hs_nn
          have h_floor_lt : (lo : ℝ) < s := lt_of_le_of_ne h_floor_le_s h_lo_ne_s
          have h_s_le_r : s ≤ -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) := by
            have h_abs_eq : |s| = -s := abs_of_neg hs_neg
            linarith [h_s_lo_real]
          have h_lo_lt_neg : (lo : ℝ) < -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) :=
            lt_of_lt_of_le h_floor_lt h_s_le_r
          have h_lo_lt_int : lo < -((2 : ℤ) ^ ((p : ℕ) - 1)) := by
            exact_mod_cast h_lo_lt_neg
          have h_lop1_le : lo + 1 ≤ -((2 : ℤ) ^ ((p : ℕ) - 1)) := by linarith
          have h_lop1_neg : lo + 1 < 0 := by
            have : (0 : ℤ) < (2 : ℤ) ^ ((p : ℕ) - 1) := by positivity
            linarith
          rw [abs_of_neg h_lop1_neg]; linarith
      rw [h_dhi_def, h_dlo_def]
      exact ParityFormat.alternating_parity_floating_iff hp_F hp_ne_1 hexp_F
        h_lo_lo h_lo_hi h_lop1_lo h_lop1_hi
    | coe e'' =>
      by_cases hp_eq_1 : p = (1 : ℕ+)
      · subst hp_eq_1
        have h_e_ge : e'' ≤ e := F.exp_le_canonicalExp x hexp_F
        have h_s_lt : |x * (2 : ℝ) ^ (-e)| < (2 : ℝ) ^ ((1 : ℕ+) : ℕ) :=
          floor_mantissa_lt hp_F
        have h_s_lt_2 : |x * (2 : ℝ) ^ (-e)| < ((2 : ℤ) : ℝ) := by
          have h_cast : ((2 : ℤ) : ℝ) = (2 : ℝ) ^ ((1 : ℕ+) : ℕ) := by
            change (2 : ℝ) = (2 : ℝ) ^ (1 : ℕ); ring
          rw [h_cast]; exact h_s_lt
        have h_lo_hi_int : |lo| ≤ 2 := abs_floor_le_of_abs_lt h_s_lt_2
        have h_lop1_hi_int : |lo + 1| ≤ 2 :=
          abs_floor_add_one_le_of_abs_lt (p := 1) h_s_lt
        by_cases h_regime : Int.log 2 |x| + 1 - ((1 : ℕ+) : ℤ) ≤ e''
        · have h_e_eq : e = e'' := by
            change F.canonicalExp x = e''
            unfold FiniteFormat.canonicalExp
            simp only [hp_F, hexp_F]
            rw [if_neg hx_ne]
            exact max_eq_right h_regime
          have h_dlo_at_e'' : dlo = Dyadic.ofIntZpow lo e'' := by rw [h_dlo_def, h_e_eq]
          have h_dhi_at_e'' : dhi = Dyadic.ofIntZpow (lo + 1) e'' := by
            rw [h_dhi_def, h_e_eq]
          rw [h_dhi_at_e'', h_dlo_at_e'']
          exact ParityFormat.alternating_parity_mixed_subnormal_p1_iff hp_F hexp_F
            h_lo_hi_int h_lop1_hi_int
        · push Not at h_regime
          have h_pcast : ((1 : ℕ+) : ℤ) = 1 := rfl
          have h_e_eq_log : e = Int.log 2 |x| := by
            change F.canonicalExp x = _
            unfold FiniteFormat.canonicalExp
            simp only [hp_F, hexp_F]
            rw [if_neg hx_ne]
            rw [show (((1 : ℕ+) : ℕ) : ℤ) = 1 from rfl]
            have h_max_eq : max (Int.log 2 |x| + 1 - 1) e'' =
                Int.log 2 |x| + 1 - 1 := by
              apply max_eq_left
              have := h_regime; rw [h_pcast] at this; linarith
            rw [h_max_eq]; ring
          have h_x_ge : (2 : ℝ) ^ (Int.log 2 |x|) ≤ |x| :=
            Int.zpow_log_le_self (b := 2) (by norm_num : (1 : ℕ) < 2)
              (abs_pos.mpr hx_ne)
          have h_abs_s : 1 ≤ |x * (2 : ℝ) ^ (-e)| := by
            have h_abs_eq : |x * (2 : ℝ) ^ (-e)| = |x| * (2 : ℝ) ^ (-e) := by
              rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)]
            rw [h_abs_eq, h_e_eq_log]
            have h_pow_eq : (2 : ℝ) ^ (Int.log 2 |x|) *
                (2 : ℝ) ^ (-Int.log 2 |x|) = 1 := by
              rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
                  add_neg_cancel, zpow_zero]
            have h_le := mul_le_mul_of_nonneg_right h_x_ge
              (zpow_pos (by norm_num : (0 : ℝ) < 2) (-Int.log 2 |x|)).le
            rw [h_pow_eq] at h_le
            exact h_le
          have h_lo_lo_int : 1 ≤ |lo| := by
            by_cases hs_nn : 0 ≤ x * (2 : ℝ) ^ (-e)
            · have h_s_ge : 1 ≤ x * (2 : ℝ) ^ (-e) := by
                have h_abs_eq : |x * (2 : ℝ) ^ (-e)| = x * (2 : ℝ) ^ (-e) :=
                  abs_of_nonneg hs_nn
                linarith [h_abs_s]
              have h_lo_ge_1 : 1 ≤ lo := by
                apply Int.le_floor.mpr; push_cast; exact h_s_ge
              rw [abs_of_nonneg (by linarith : (0 : ℤ) ≤ lo)]; exact h_lo_ge_1
            · push Not at hs_nn
              have h_s_le : x * (2 : ℝ) ^ (-e) ≤ -1 := by
                have h_abs_eq : |x * (2 : ℝ) ^ (-e)| =
                    -(x * (2 : ℝ) ^ (-e)) := abs_of_neg hs_nn
                linarith [h_abs_s]
              have h_floor_le : (lo : ℝ) ≤ x * (2 : ℝ) ^ (-e) :=
                Int.floor_le _
              have h_lo_le : (lo : ℝ) ≤ -1 := le_trans h_floor_le h_s_le
              have h_lo_le_int : lo ≤ -1 := by exact_mod_cast h_lo_le
              rw [abs_of_neg (by linarith : lo < 0)]; linarith
          have h_lo_ne_neg1 : lo ≠ -1 := by
            intro h_eq
            have h_lo_int : ⌊s⌋ = -1 := h_eq
            have h_floor_le_neg1 : (-1 : ℝ) ≤ s := by
              have h_fl := Int.floor_le s
              rw [h_lo_int] at h_fl; push_cast at h_fl; exact h_fl
            have h_lt_succ_zero : s < 0 := by
              have h_lt := Int.lt_floor_add_one s
              rw [h_lo_int] at h_lt; push_cast at h_lt; linarith
            have h_s_le_neg1 : s ≤ -1 := by
              have h_abs_eq : |s| = -s := abs_of_neg (by linarith : s < 0)
              have h_abs_ge : 1 ≤ |s| := h_abs_s
              linarith
            have h_s_eq : s = -1 := le_antisymm h_s_le_neg1 h_floor_le_neg1
            apply h_lo_ne_s
            rw [h_s_eq, h_eq]; push_cast; ring
          have h_lop1_lo_int : 1 ≤ |lo + 1| := by
            have h_lop1_ne : lo + 1 ≠ 0 := by
              intro h0; apply h_lo_ne_neg1; omega
            exact Int.one_le_abs h_lop1_ne
          rw [h_dhi_def, h_dlo_def]
          exact ParityFormat.alternating_parity_mixed_normal_p1_iff hp_F hexp_F
            h_e_ge h_lo_lo_int h_lo_hi_int h_lop1_lo_int h_lop1_hi_int
      · have hp_ne_1 : F.p ≠ ((1 : ℕ+) : WithTop ℕ+) := by
          rw [hp_F]; intro h_eq; apply hp_eq_1; exact_mod_cast h_eq
        by_cases h_regime : Int.log 2 |x| + 1 - ((p : ℕ+) : ℤ) ≤ e''
        · have h_e_eq : e = e'' := by
            change F.canonicalExp x = e''
            unfold FiniteFormat.canonicalExp
            simp only [hp_F, hexp_F]
            rw [if_neg hx_ne]
            exact max_eq_right h_regime
          have h_x_lt : |x| < (2 : ℝ) ^ (e'' + (p : ℤ)) := by
            have h_log_le : Int.log 2 |x| ≤ e'' + (p : ℤ) - 1 := by
              have h_pcast : ((p : ℕ+) : ℤ) = (p : ℤ) := rfl
              linarith
            have h_lt := Int.lt_zpow_succ_log_self
              (by norm_num : (1 : ℕ) < 2) |x|
            have : Int.log 2 |x| + 1 ≤ e'' + (p : ℤ) := by linarith
            exact lt_of_lt_of_le h_lt
              (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) this)
          have h_s_lt : |x * (2 : ℝ) ^ (-e)| < (2 : ℝ) ^ ((p : ℕ+) : ℕ) := by
            rw [h_e_eq]
            have h_abs : |x * (2 : ℝ) ^ (-e'')| = |x| * (2 : ℝ) ^ (-e'') := by
              rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)]
            rw [h_abs]
            have h_2neg_pos : (0 : ℝ) < (2 : ℝ) ^ (-e'') := zpow_pos (by norm_num) _
            have h_eq_split : (2 : ℝ) ^ (e'' + (p : ℤ)) =
                (2 : ℝ) ^ e'' * (2 : ℝ) ^ ((p : ℕ+) : ℕ) := by
              rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
              have h_pcast : ((p : ℕ+) : ℤ) = (((p : ℕ+) : ℕ) : ℤ) := rfl
              rw [h_pcast, zpow_natCast]
            have h_x2neg : |x| * (2 : ℝ) ^ (-e'') <
                (2 : ℝ) ^ (e'' + (p : ℤ)) * (2 : ℝ) ^ (-e'') :=
              mul_lt_mul_of_pos_right h_x_lt h_2neg_pos
            rw [h_eq_split] at h_x2neg
            have h_cancel : (2 : ℝ) ^ e'' * (2 : ℝ) ^ ((p : ℕ+) : ℕ) *
                (2 : ℝ) ^ (-e'') = (2 : ℝ) ^ ((p : ℕ+) : ℕ) := by
              rw [mul_right_comm, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
                  add_neg_cancel, zpow_zero, one_mul]
            rw [h_cancel] at h_x2neg
            exact h_x2neg
          have h_lo_le : |lo| ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by
            apply abs_floor_le_of_abs_lt; push_cast; exact h_s_lt
          have h_lop1_le : |lo + 1| ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) :=
            abs_floor_add_one_le_of_abs_lt h_s_lt
          have h_dlo_at_e'' : dlo = Dyadic.ofIntZpow lo e'' := by rw [h_dlo_def, h_e_eq]
          have h_dhi_at_e'' : dhi = Dyadic.ofIntZpow (lo + 1) e'' := by
            rw [h_dhi_def, h_e_eq]
          have h2p_nn : (0 : ℤ) ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by positivity
          rcases lt_or_eq_of_le h_lo_le with h_lo_lt | h_lo_sat
          · have h_log_lo' := log_lt_p_of_abs_lt_two_pow h_lo_lt
            rcases lt_or_eq_of_le h_lop1_le with h_lop1_lt | h_lop1_sat
            · have h_log_lop1_raw := log_lt_p_of_abs_lt_two_pow h_lop1_lt
              have h_log_lop1' : Int.log 2 |((lo : ℝ) + 1)| + 1 ≤
                  (((p : ℕ+) : ℕ) : ℤ) := by
                have h_eq : |((lo : ℝ) + 1)| = |((lo + 1 : ℤ) : ℝ)| := by
                  push_cast; rfl
                rw [h_eq]; exact h_log_lop1_raw
              rw [h_dhi_at_e'', h_dlo_at_e'']
              exact ParityFormat.alternating_parity_mixed_subnormal_pne1_iff hp_F
                hp_ne_1 hexp_F h_log_lo' h_log_lop1'
            · -- `|lo+1| = 2^p` saturated (dhi even/¬odd), `lo` odd (dlo odd).
              have h_even2p : Even ((2 : ℤ) ^ ((p : ℕ+) : ℕ)) := by
                refine ⟨(2 : ℤ) ^ (((p : ℕ+) : ℕ) - 1), ?_⟩
                have := Dyadic.two_pow_succ_pred (p : ℕ+).pos
                linarith
              have h_lo_ne : lo ≠ 0 := by
                intro h_zero
                rw [h_zero] at h_lop1_sat
                simp at h_lop1_sat
                have h2p_ge : (2 : ℤ) ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by
                  calc (2 : ℤ) = (2 : ℤ) ^ 1 := by ring
                    _ ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) :=
                        pow_le_pow_right₀ (by norm_num) (p : ℕ+).pos
                linarith
              have h_odd_dlo : F''.IsOdd (Dyadic.ofIntZpow lo e'') := by
                rw [ParityFormat.isOdd_iff_odd_at_canonical_mixed_subnormal
                  hp_F hp_ne_1 hexp_F h_lo_ne h_log_lo']
                rcases (abs_eq h2p_nn).mp h_lop1_sat with hpos | hneg
                · have h_lo_eq : lo = (2 : ℤ) ^ ((p : ℕ+) : ℕ) - 1 := by omega
                  rw [h_lo_eq]; obtain ⟨m, hm⟩ := h_even2p; exact ⟨m - 1, by linarith⟩
                · have h_lo_eq : lo = -((2 : ℤ) ^ ((p : ℕ+) : ℕ)) - 1 := by omega
                  rw [h_lo_eq]; obtain ⟨m, hm⟩ := h_even2p; exact ⟨-m - 1, by linarith⟩
              have h_dhi_real_e'' : (Dyadic.ofIntZpow (lo + 1) e'' : ℝ) =
                  ((lo + 1 : ℤ) : ℝ) * (2 : ℝ) ^ e'' := Dyadic.coe_ofIntZpow _ _
              have h_lop1_ne : lo + 1 ≠ 0 := by
                intro h_zero
                rw [h_zero] at h_lop1_sat
                simp at h_lop1_sat
                have : (0 : ℤ) < (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by positivity
                omega
              have h_dhi_ne : (Dyadic.ofIntZpow (lo + 1) e'' : ℝ) ≠ 0 := by
                rw [h_dhi_real_e'']
                exact mul_ne_zero (Int.cast_ne_zero.mpr h_lop1_ne)
                  (ne_of_gt (zpow_pos (by norm_num) _))
              have h_log_2p : Int.log 2 (|lo + 1| : ℝ) = (((p : ℕ+) : ℕ) : ℤ) := by
                have h_bridge : (|lo + 1| : ℝ) = ((|lo + 1| : ℤ) : ℝ) := by
                  push_cast; rfl
                rw [h_bridge, h_lop1_sat]
                have h_cast : (((2 : ℤ) ^ ((p : ℕ+) : ℕ) : ℤ) : ℝ) =
                    (2 : ℝ) ^ (((p : ℕ+) : ℕ) : ℤ) := by
                  rw [zpow_natCast]; push_cast; rfl
                rw [h_cast]
                exact Int.log_zpow (by norm_num : 1 < 2) _
              have h_log_dhi : Int.log 2 |(Dyadic.ofIntZpow (lo + 1) e'' : ℝ)| =
                  (((p : ℕ+) : ℕ) : ℤ) + e'' := by
                rw [h_dhi_real_e'', ParityFormat.log_abs_mul_zpow h_lop1_ne e'']
                have h_cast_eq : |((lo + 1 : ℤ) : ℝ)| = (|lo + 1| : ℝ) := by
                  push_cast; rfl
                rw [h_cast_eq, h_log_2p]
              have h_log_y_ge : (((p : ℕ+) : ℕ) : ℤ) ≤
                  Int.log 2 |(Dyadic.ofIntZpow (lo + 1) e'' : ℝ)| - e'' + 1 := by
                rw [h_log_dhi]; linarith
              have h_not_odd_dhi : ¬ F''.IsOdd (Dyadic.ofIntZpow (lo + 1) e'') :=
                ParityFormat.not_isOdd_at_saturation_mixed_normal hp_F hp_ne_1 hexp_F
                  h_dhi_ne h_log_y_ge h_dhi_real_e'' h_lop1_sat
              rw [h_dhi_at_e'', h_dlo_at_e'']
              exact ⟨fun ho => absurd ho h_not_odd_dhi, fun hn => absurd h_odd_dlo hn⟩
          · -- `|lo| = 2^p` saturated (dlo even/¬odd), `lo+1` odd (dhi odd).
            have h_even2p : Even ((2 : ℤ) ^ ((p : ℕ+) : ℕ)) := by
              refine ⟨(2 : ℤ) ^ (((p : ℕ+) : ℕ) - 1), ?_⟩
              have := Dyadic.two_pow_succ_pred (p : ℕ+).pos
              linarith
            have h_lo_neg : lo = -((2 : ℤ) ^ ((p : ℕ+) : ℕ)) := by
              rcases (abs_eq h2p_nn).mp h_lo_sat with hpos | hneg
              · exfalso
                rw [hpos] at h_lop1_le
                have h_abs : |(2 : ℤ) ^ ((p : ℕ+) : ℕ) + 1| =
                    (2 : ℤ) ^ ((p : ℕ+) : ℕ) + 1 := by
                  apply abs_of_pos; positivity
                linarith
              · exact hneg
            have h_lop1_lt : |lo + 1| < (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by
              rw [h_lo_neg]
              have h_pos_inner : (0 : ℤ) < (2 : ℤ) ^ ((p : ℕ+) : ℕ) - 1 := by
                have h2le : (2 : ℤ) ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by
                  calc (2 : ℤ) = (2 : ℤ) ^ 1 := by ring
                    _ ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) :=
                        pow_le_pow_right₀ (by norm_num) (p : ℕ+).pos
                linarith
              have h_rw : -((2 : ℤ) ^ ((p : ℕ+) : ℕ)) + 1 =
                  -((2 : ℤ) ^ ((p : ℕ+) : ℕ) - 1) := by ring
              rw [h_rw, abs_neg, abs_of_pos h_pos_inner]; linarith
            have h_log_lop1' := log_lt_p_of_abs_lt_two_pow h_lop1_lt
            have h_lop1_ne : lo + 1 ≠ 0 := by
              rw [h_lo_neg]
              have : (2 : ℤ) ^ ((p : ℕ+) : ℕ) ≥ 2 := by
                calc (2 : ℤ) ^ ((p : ℕ+) : ℕ) ≥ (2 : ℤ) ^ 1 :=
                    pow_le_pow_right₀ (by norm_num) (p : ℕ+).pos
                  _ = 2 := by ring
              omega
            have h_odd_dhi : F''.IsOdd (Dyadic.ofIntZpow (lo + 1) e'') := by
              rw [ParityFormat.isOdd_iff_odd_at_canonical_mixed_subnormal
                hp_F hp_ne_1 hexp_F h_lop1_ne h_log_lop1']
              rw [h_lo_neg]; obtain ⟨m, hm⟩ := h_even2p; exact ⟨-m, by linarith⟩
            have h_dlo_real_e'' : (Dyadic.ofIntZpow lo e'' : ℝ) =
                (lo : ℝ) * (2 : ℝ) ^ e'' := Dyadic.coe_ofIntZpow _ _
            have h_lo_ne : lo ≠ 0 := by
              rw [h_lo_neg]
              have : (2 : ℤ) ^ ((p : ℕ+) : ℕ) ≥ 2 := by
                calc (2 : ℤ) ^ ((p : ℕ+) : ℕ) ≥ (2 : ℤ) ^ 1 :=
                    pow_le_pow_right₀ (by norm_num) (p : ℕ+).pos
                  _ = 2 := by ring
              omega
            have h_dlo_ne : (Dyadic.ofIntZpow lo e'' : ℝ) ≠ 0 := by
              rw [h_dlo_real_e'']
              exact mul_ne_zero (Int.cast_ne_zero.mpr h_lo_ne)
                (ne_of_gt (zpow_pos (by norm_num) _))
            have h_log_2p : Int.log 2 (|lo| : ℝ) = (((p : ℕ+) : ℕ) : ℤ) := by
              have h_bridge : (|lo| : ℝ) = ((|lo| : ℤ) : ℝ) := by push_cast; rfl
              rw [h_bridge, h_lo_sat]
              have h_cast : (((2 : ℤ) ^ ((p : ℕ+) : ℕ) : ℤ) : ℝ) =
                  (2 : ℝ) ^ (((p : ℕ+) : ℕ) : ℤ) := by
                rw [zpow_natCast]; push_cast; rfl
              rw [h_cast]
              exact Int.log_zpow (by norm_num : 1 < 2) _
            have h_log_dlo : Int.log 2 |(Dyadic.ofIntZpow lo e'' : ℝ)| =
                (((p : ℕ+) : ℕ) : ℤ) + e'' := by
              rw [h_dlo_real_e'', ParityFormat.log_abs_mul_zpow h_lo_ne e'']
              have h_cast_eq : |(lo : ℝ)| = (|lo| : ℝ) := by rfl
              rw [h_cast_eq, h_log_2p]
            have h_log_y_ge : (((p : ℕ+) : ℕ) : ℤ) ≤
                Int.log 2 |(Dyadic.ofIntZpow lo e'' : ℝ)| - e'' + 1 := by
              rw [h_log_dlo]; linarith
            have h_not_odd_dlo : ¬ F''.IsOdd (Dyadic.ofIntZpow lo e'') :=
              ParityFormat.not_isOdd_at_saturation_mixed_normal hp_F hp_ne_1 hexp_F
                h_dlo_ne h_log_y_ge h_dlo_real_e'' h_lo_sat
            rw [h_dhi_at_e'', h_dlo_at_e'']
            exact ⟨fun _ => h_not_odd_dlo, fun _ => h_odd_dhi⟩
        · push Not at h_regime
          have h_e_eq_log : e = Int.log 2 |x| + 1 - ((p : ℕ+) : ℤ) := by
            change F.canonicalExp x = _
            unfold FiniteFormat.canonicalExp
            simp only [hp_F, hexp_F]
            rw [if_neg hx_ne]
            exact max_eq_left (le_of_lt h_regime)
          have h_s_lo_real : ((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) ≤
              |x * (2 : ℝ) ^ (-e)| :=
            two_pow_pred_le_scaled (p := p) hx_ne h_e_eq_log
          have h_lo_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo| :=
            abs_floor_ge_two_pow_pred (p := p) h_s_lo_real
          have h_lop1_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo + 1| := by
            by_cases hs_nn : 0 ≤ s
            · have h_lo_nn : 0 ≤ lo := Int.floor_nonneg.mpr hs_nn
              rw [abs_of_nonneg (by linarith : (0 : ℤ) ≤ lo + 1)]
              linarith [h_lo_lo, abs_of_nonneg h_lo_nn]
            · have hs_neg : s < 0 := not_le.mp hs_nn
              have h_floor_lt : (lo : ℝ) < s :=
                lt_of_le_of_ne h_floor_le_s h_lo_ne_s
              have h_s_le_r : s ≤ -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) := by
                have h_abs_eq : |s| = -s := abs_of_neg hs_neg
                linarith [h_s_lo_real]
              have h_lo_lt_neg : (lo : ℝ) < -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) :=
                lt_of_lt_of_le h_floor_lt h_s_le_r
              have h_lo_lt_int : lo < -((2 : ℤ) ^ ((p : ℕ) - 1)) := by
                exact_mod_cast h_lo_lt_neg
              have h_lop1_le_int : lo + 1 ≤ -((2 : ℤ) ^ ((p : ℕ) - 1)) := by
                linarith
              have h_lop1_neg : lo + 1 < 0 := by
                have : (0 : ℤ) < (2 : ℤ) ^ ((p : ℕ) - 1) := by positivity
                linarith
              rw [abs_of_neg h_lop1_neg]; linarith
          have h_lo_hi : |lo| ≤ (2 : ℤ) ^ ((p : ℕ) : ℕ) := h_lo_bound hp_F
          have h_lop1_hi : |lo + 1| ≤ (2 : ℤ) ^ ((p : ℕ) : ℕ) :=
            h_lop1_bound hp_F
          have h_lo_ne : lo ≠ 0 := by
            intro h_lo_zero
            rw [h_lo_zero] at h_lo_lo
            simp at h_lo_lo
            have : (0 : ℤ) < (2 : ℤ) ^ ((p : ℕ) - 1) := by positivity
            omega
          have h_lop1_ne : lo + 1 ≠ 0 := by
            intro h_lop1_zero
            rw [h_lop1_zero] at h_lop1_lo
            simp at h_lop1_lo
            have : (0 : ℤ) < (2 : ℤ) ^ ((p : ℕ) - 1) := by positivity
            omega
          have h_dlo_ne : (dlo : ℝ) ≠ 0 := by
            rw [h_dlo_real]
            exact mul_ne_zero (Int.cast_ne_zero.mpr h_lo_ne)
              (ne_of_gt (zpow_pos (by norm_num) _))
          have h_dhi_ne : (dhi : ℝ) ≠ 0 := by
            rw [h_dhi_real]
            exact mul_ne_zero (Int.cast_ne_zero.mpr h_lop1_ne)
              (ne_of_gt (zpow_pos (by norm_num) _))
          have h_log_dlo : Int.log 2 |(dlo : ℝ)| =
              Int.log 2 |(lo : ℝ)| + e := by
            rw [h_dlo_real]
            exact ParityFormat.log_abs_mul_zpow h_lo_ne e
          have h_log_dhi : Int.log 2 |(dhi : ℝ)| =
              Int.log 2 |((lo + 1 : ℤ) : ℝ)| + e := by
            rw [h_dhi_real]
            exact ParityFormat.log_abs_mul_zpow h_lop1_ne e
          have h_log_lo_lb := log_ge_p_pred_of_two_pow_pred_le
            (k := lo) h_lo_lo
          have h_log_lop1_lb := log_ge_p_pred_of_two_pow_pred_le
            (k := lo + 1) h_lop1_lo
          have h_log_lo : ((p : ℕ) : ℤ) ≤ Int.log 2 |(dlo : ℝ)| - e'' + 1 := by
            rw [h_log_dlo, h_e_eq_log]
            have : Int.log 2 |x| - e'' ≥ ((p : ℕ) : ℤ) := by linarith
            linarith [h_log_lo_lb]
          have h_log_hi : ((p : ℕ) : ℤ) ≤ Int.log 2 |(dhi : ℝ)| - e'' + 1 := by
            rw [h_log_dhi, h_e_eq_log]
            have : Int.log 2 |x| - e'' ≥ ((p : ℕ) : ℤ) := by linarith
            linarith [h_log_lop1_lb]
          exact ParityFormat.alternating_parity_mixed_normal_pne1_iff hp_F hp_ne_1
            hexp_F h_dlo_ne h_dhi_ne h_log_lo h_log_hi h_dlo_real h_dhi_real
            h_lo_lo h_lo_hi h_lop1_lo h_lop1_hi

/-- `Dyadic.ofIntZpow k e` is in `F.unbounded` provided `e ≥ F.exp` and (when
`F.p` is finite) `|k| ≤ 2^p`. The mantissa-bound boundary case `|k| = 2^p`
is handled by `precisionAtMost_of_abs_le`. -/
theorem rndUnbounded_satisfies_toOdd (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .toOdd) :
    RoundsFinite F.unbounded .toOdd x (rndUnbounded F .toOdd x h) := by
  have h_unb : ¬ F.unbounded.IsUndefined .toOdd := h
  set F'' := F.toParityFormatOfToOdd h with hF''_def
  set F' := F.unbounded.toParityFormatOfToOdd h_unb with hF'_def
  have h_F'_eq : F'.toFormat = F.unbounded.toFormat := rfl
  -- IsOdd-bridge: same predicate value for F and F.unbounded
  -- since both ParityFormats share `p` and `exp` definitionally.
  have h_isOdd_bridge : ∀ (y : Dyadic), F''.IsOdd y ↔ F'.IsOdd y := fun y => Iff.rfl
  have h_rnd_eq : rndUnbounded F .toOdd x h =
      rndParity F'' .toOdd x (F.canonicalExp x) := by
    unfold rndUnbounded
    rw [dif_pos rfl]
  rw [h_rnd_eq]
  set e := F.canonicalExp x with h_e_def
  set s := x * (2 : ℝ) ^ (-e)
  set lo : ℤ := ⌊s⌋ with h_lo_def
  set dlo : Dyadic := Dyadic.ofIntZpow lo e with h_dlo_def
  set dhi : Dyadic := Dyadic.ofIntZpow (lo + 1) e with h_dhi_def
  have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  -- Mantissa bounds for dlo, dhi membership.
  have h_lo_bound : ∀ {p : ℕ+}, F.p = ((p : ℕ+) : WithTop ℕ+) →
      |lo| ≤ (2 : ℤ) ^ (p : ℕ) := fun hp => by
    apply abs_floor_le_of_abs_lt
    push_cast; exact floor_mantissa_lt hp
  have h_lop1_bound : ∀ {p : ℕ+}, F.p = ((p : ℕ+) : WithTop ℕ+) →
      |lo + 1| ≤ (2 : ℤ) ^ (p : ℕ) := fun hp =>
    abs_floor_add_one_le_of_abs_lt (floor_mantissa_lt hp)
  have h_exp_le : ∀ {e' : ℤ}, F.exp = (e' : WithBot ℤ) → e' ≤ e :=
    fun hexp => F.exp_le_canonicalExp x hexp
  have h_dlo_mem : dlo ∈ F.unbounded :=
    ofIntZpow_mem_unbounded F h_exp_le h_lo_bound
  have h_dhi_mem : dhi ∈ F.unbounded :=
    ofIntZpow_mem_unbounded F h_exp_le h_lop1_bound
  have h_dlo_real : (dlo : ℝ) = (lo : ℝ) * (2 : ℝ) ^ e :=
    Dyadic.coe_ofIntZpow _ _
  have h_dhi_real : (dhi : ℝ) = ((lo + 1 : ℤ) : ℝ) * (2 : ℝ) ^ e :=
    Dyadic.coe_ofIntZpow _ _
  have h_floor_le_s : (lo : ℝ) ≤ s := Int.floor_le _
  have h_s_lt_succ : s < (lo : ℝ) + 1 := Int.lt_floor_add_one _
  have h_s_unscale : s * (2 : ℝ) ^ e = x := mul_zpow_neg_self x e
  have h_dlo_le_x : (dlo : ℝ) ≤ x := by
    rw [h_dlo_real, ← h_s_unscale]
    exact mul_le_mul_of_nonneg_right h_floor_le_s h_2e_pos.le
  have h_x_le_dhi : x ≤ (dhi : ℝ) := by
    rw [h_dhi_real, ← h_s_unscale]
    apply mul_le_mul_of_nonneg_right _ h_2e_pos.le
    push_cast; linarith
  -- Faithfulness witnesses.
  have h_dlo_round_down : ∀ z : Dyadic, z ∈ F.unbounded → (z : ℝ) ≤ x →
      (z : ℝ) ≤ (dlo : ℝ) := by
    intro z hz hz_le_x
    obtain ⟨hz_prec, hz_quant, _⟩ := hz
    rw [h_dlo_real]
    exact floor_minimality F x hz_prec hz_quant hz_le_x
  have h_dhi_round_up : (lo : ℝ) ≠ s →
      ∀ z : Dyadic, z ∈ F.unbounded → x ≤ (z : ℝ) → (dhi : ℝ) ≤ (z : ℝ) := by
    intro hs_ne z hz hx_le_z
    obtain ⟨hz_prec, hz_quant, _⟩ := hz
    rw [h_dhi_real]
    have h_ceil_eq : (⌈s⌉ : ℤ) = lo + 1 := by
      have h_lo_lt_s : (lo : ℝ) < s := lt_of_le_of_ne h_floor_le_s hs_ne
      have h_ceil_le : ⌈s⌉ ≤ lo + 1 :=
        Int.ceil_le.mpr (by push_cast; linarith)
      have h_ceil_ge : lo + 1 ≤ ⌈s⌉ := by
        have h_lt_ceil : (lo : ℝ) < (⌈s⌉ : ℝ) :=
          lt_of_lt_of_le h_lo_lt_s (Int.le_ceil _)
        have : lo < ⌈s⌉ := by exact_mod_cast h_lt_ceil
        omega
      omega
    have hh := ceil_minimality F x hz_prec hz_quant hx_le_z
    have h_subst : ((lo + 1 : ℤ) : ℝ) = ((⌈s⌉ : ℤ) : ℝ) := by exact_mod_cast h_ceil_eq.symm
    rw [h_subst]
    convert hh using 2
  -- Main case analysis. Goal: RoundsFinite ... (if ... then ... else ...).
  by_cases hs : (lo : ℝ) = s
  · -- Exact: y = dlo, x = dlo. Parity vacuous.
    rw [show rndParity F'' .toOdd x e =
        if (lo : ℝ) = s then dlo else if F''.IsOdd dlo then dlo else dhi from rfl,
        if_pos hs]
    refine ⟨h_dlo_mem, ?_, ?_⟩
    · left; exact ⟨h_dlo_mem, h_dlo_le_x, h_dlo_round_down⟩
    · intro hne
      exfalso
      apply hne
      rw [h_dlo_real]
      -- x = lo · 2^e: from (lo : ℝ) = s = x · 2^(-e).
      have h_x_eq : x = s * (2 : ℝ) ^ e := by
        change x = x * (2 : ℝ) ^ (-e) * (2 : ℝ) ^ e
        rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
            neg_add_cancel, zpow_zero, mul_one]
      rw [h_x_eq, ← hs]
  · by_cases hodd : F''.IsOdd dlo
    · -- y = dlo, IsOdd dlo holds.
      rw [show rndParity F'' .toOdd x e =
          if (lo : ℝ) = s then dlo else if F''.IsOdd dlo then dlo else dhi from rfl,
          if_neg hs, if_pos hodd]
      refine ⟨h_dlo_mem, ?_, ?_⟩
      · left; exact ⟨h_dlo_mem, h_dlo_le_x, h_dlo_round_down⟩
      · intro _
        exact ⟨F', h_F'_eq, (h_isOdd_bridge dlo).mp hodd⟩
    · -- y = dhi, need IsOdd dhi (alternating parity).
      rw [show rndParity F'' .toOdd x e =
          if (lo : ℝ) = s then dlo else if F''.IsOdd dlo then dlo else dhi from rfl,
          if_neg hs, if_neg hodd]
      refine ⟨h_dhi_mem, ?_, ?_⟩
      · right; exact ⟨h_dhi_mem, h_x_le_dhi, h_dhi_round_up hs⟩
      · intro _
        refine ⟨F', h_F'_eq, ?_⟩
        rw [← h_isOdd_bridge dhi]
        have hx : x ≠ 0 := by
          intro h_x0
          apply hs
          subst h_x0
          have hs0 : s = 0 := by change (0 : ℝ) * (2 : ℝ) ^ (-e) = 0; ring
          rw [hs0]
          simp [h_lo_def, hs0]
        exact (toOdd_neighbors_alternate x h hx hs).mpr hodd


theorem rndUnbounded_unique_toOdd (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .toOdd) {y : Dyadic}
    (hy : RoundsFinite F.unbounded .toOdd x y) :
    y = rndUnbounded F .toOdd x h := by
  set y' := rndUnbounded F .toOdd x h
  have hy' : RoundsFinite F.unbounded .toOdd x y' :=
    rndUnbounded_satisfies_toOdd F x h
  obtain ⟨hy_mem, hy_faith, hy_par⟩ := hy
  obtain ⟨hy'_mem, hy'_faith, hy'_par⟩ := hy'
  apply Dyadic.ext_real
  -- Mixed-case helper: given `y` is RoundDown, `y'` is RoundUp, show `y = y'`.
  -- This is the asymmetric case; the symmetric one is identical with `y` and
  -- `y'` swapped.
  have h_mixed_eq : ∀ {y y' : Dyadic},
      y ∈ F.unbounded → y' ∈ F.unbounded →
      (y : ℝ) ≤ x → (∀ z : Dyadic, z ∈ F.unbounded → (z : ℝ) ≤ x →
        (z : ℝ) ≤ (y : ℝ)) →
      x ≤ (y' : ℝ) → (∀ z : Dyadic, z ∈ F.unbounded → x ≤ (z : ℝ) →
        (y' : ℝ) ≤ (z : ℝ)) →
      (x ≠ (y : ℝ) → ∃ F' : ParityFormat, F'.toFormat = F.unbounded.toFormat ∧ F'.IsOdd y) →
      (x ≠ (y' : ℝ) → ∃ F' : ParityFormat, F'.toFormat = F.unbounded.toFormat ∧ F'.IsOdd y') →
      (y : ℝ) = (y' : ℝ) := by
    intro y y' hy_mem hy'_mem hy_le hy_max hy'_ge hy'_min hy_par hy'_par
    by_cases h_yx : (y : ℝ) = x
    · -- y = x: y' ≤ y by min property applied to y.
      have : (y' : ℝ) ≤ (y : ℝ) := hy'_min y hy_mem (by linarith [h_yx])
      linarith
    by_cases h_y'x : (y' : ℝ) = x
    · -- y' = x: y ≥ y' by max property applied to y'.
      have : (y' : ℝ) ≤ (y : ℝ) := hy_max y' hy'_mem (by linarith [h_y'x])
      linarith
    exfalso
    have hy_lt : (y : ℝ) < x := lt_of_le_of_ne hy_le h_yx
    have hx_lt : x < (y' : ℝ) := lt_of_le_of_ne hy'_ge (Ne.symm h_y'x)
    have h_xne_y : x ≠ (y : ℝ) := fun h_eq => h_yx h_eq.symm
    have h_xne_y' : x ≠ (y' : ℝ) := fun h_eq => h_y'x h_eq.symm
    obtain ⟨F_y, hF_y_eq, hF_y_odd⟩ := hy_par h_xne_y
    obtain ⟨F_y', hF_y'_eq, hF_y'_odd⟩ := hy'_par h_xne_y'
    set e := F.canonicalExp x with h_e_def
    set lo := ⌊x * (2 : ℝ) ^ (-e)⌋ with h_lo_def
    set dlo : Dyadic := Dyadic.ofIntZpow lo e with h_dlo_def
    set dhi : Dyadic := Dyadic.ofIntZpow (lo + 1) e with h_dhi_def
    have h_not_neg : ¬ F.IsUndefined .toNegative := fun ⟨_, _, hrm⟩ => by simp at hrm
    have h_not_pos : ¬ F.IsUndefined .toPositive := fun ⟨_, _, hrm⟩ => by simp at hrm
    -- y = dlo via uniqueness of RoundDown.
    have h_dlo_RD : RoundsFinite F.unbounded .toNegative x dlo := by
      have h_eq : rndUnbounded F .toNegative x h_not_neg = dlo := by
        unfold rndUnbounded
        rw [dif_neg (by decide : (RoundingMode.toNegative : RoundingMode) ≠ .toOdd)]
        rw [dif_neg (by decide :
          (RoundingMode.toNegative : RoundingMode) ≠ .nearest .toEven)]
        rfl
      rw [← h_eq]
      exact rndUnbounded_satisfies_toNegative F x h_not_neg
    obtain ⟨h_dlo_mem, h_dlo_le_x, h_dlo_max⟩ := h_dlo_RD
    have h_y_eq_dlo_r : (y : ℝ) = (dlo : ℝ) :=
      le_antisymm (h_dlo_max y hy_mem hy_le) (hy_max dlo h_dlo_mem h_dlo_le_x)
    -- x is strictly between dlo and dhi (not at lo · 2^e).
    have h_x_not_at_lo : x ≠ ((lo : ℝ) * (2 : ℝ) ^ e) := by
      intro hx_eq
      have h_y_eq_x : (y : ℝ) = x := by
        rw [h_y_eq_dlo_r, h_dlo_def, Dyadic.coe_ofIntZpow]
        exact hx_eq.symm
      exact h_yx h_y_eq_x
    have h_ceil_eq : ⌈x * (2 : ℝ) ^ (-e)⌉ = lo + 1 := by
      have h_floor_le : (lo : ℝ) ≤ x * (2 : ℝ) ^ (-e) := Int.floor_le _
      have h_floor_lt : (lo : ℝ) < x * (2 : ℝ) ^ (-e) := by
        rcases lt_or_eq_of_le h_floor_le with h_lt | h_eq
        · exact h_lt
        · exfalso
          apply h_x_not_at_lo
          have := mul_zpow_neg_self x e
          have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
          have hh : (lo : ℝ) * (2 : ℝ) ^ e = x := by
            calc (lo : ℝ) * (2 : ℝ) ^ e = (x * (2 : ℝ) ^ (-e)) * (2 : ℝ) ^ e := by
                  rw [← h_eq]
              _ = x := mul_zpow_neg_self x e
          linarith
      have h_lt_succ : x * (2 : ℝ) ^ (-e) < (lo : ℝ) + 1 :=
        Int.lt_floor_add_one _
      apply le_antisymm
      · exact Int.ceil_le.mpr (by push_cast; linarith)
      · have : lo < ⌈x * (2 : ℝ) ^ (-e)⌉ := by
          have h_lt_ceil := lt_of_lt_of_le h_floor_lt (Int.le_ceil _)
          exact_mod_cast h_lt_ceil
        omega
    have h_dhi_RU : RoundsFinite F.unbounded .toPositive x dhi := by
      have h_eq : rndUnbounded F .toPositive x h_not_pos = dhi := by
        unfold rndUnbounded
        rw [dif_neg (by decide : (RoundingMode.toPositive : RoundingMode) ≠ .toOdd)]
        rw [dif_neg (by decide :
          (RoundingMode.toPositive : RoundingMode) ≠ .nearest .toEven)]
        change Dyadic.ofIntZpow (rndInt .toPositive x e) e = dhi
        rw [show rndInt .toPositive x e = lo + 1 from h_ceil_eq]
      rw [← h_eq]
      exact rndUnbounded_satisfies_toPositive F x h_not_pos
    obtain ⟨h_dhi_mem, h_x_le_dhi, h_dhi_min⟩ := h_dhi_RU
    have h_y'_eq_dhi_r : (y' : ℝ) = (dhi : ℝ) :=
      le_antisymm (hy'_min dhi h_dhi_mem h_x_le_dhi)
        (h_dhi_min y' hy'_mem hy'_ge)
    have h_y_eq_dlo : y = dlo := Dyadic.ext_real h_y_eq_dlo_r
    have h_y'_eq_dhi : y' = dhi := Dyadic.ext_real h_y'_eq_dhi_r
    -- Transfer IsOdd of both neighbours into the shared ParityFormat, then
    -- consume the single parity-alternation dispatch.
    have h_unb : ¬ F.unbounded.IsUndefined .toOdd := h
    set F'' := F.unbounded.toParityFormatOfToOdd h_unb with hF''_def
    have hF''_eq : F''.toFormat = F.unbounded.toFormat := rfl
    have hF_y_eq_F'' : F_y.toFormat = F''.toFormat := by rw [hF_y_eq, hF''_eq]
    have hF_y'_eq_F'' : F_y'.toFormat = F''.toFormat := by rw [hF_y'_eq, hF''_eq]
    have h_F''_isOdd_dlo : F''.IsOdd dlo :=
      (ParityFormat.IsOdd_iff_of_toFormat_eq hF_y_eq_F'' dlo).mp
        (h_y_eq_dlo ▸ hF_y_odd)
    have h_F''_isOdd_dhi : F''.IsOdd dhi :=
      (ParityFormat.IsOdd_iff_of_toFormat_eq hF_y'_eq_F'' dhi).mp
        (h_y'_eq_dhi ▸ hF_y'_odd)
    have hx_ne : x ≠ 0 := by
      intro hx0
      subst hx0
      have h_zero_mem : (0 : Dyadic) ∈ F.unbounded := FiniteFormat.zero_mem F.unbounded
      have h_zero_le_y : ((0 : Dyadic) : ℝ) ≤ (y : ℝ) :=
        hy_max 0 h_zero_mem (by rw [Dyadic.coe_real_zero])
      rw [Dyadic.coe_real_zero] at h_zero_le_y
      linarith
    have h_lo_ne_s : (lo : ℝ) ≠ x * (2 : ℝ) ^ (-e) := by
      intro h_eq
      apply h_x_not_at_lo
      rw [← mul_zpow_neg_self x e, ← h_eq]
    exact ParityFormat.not_both_isOdd_of_alternating_iff
      (toOdd_neighbors_alternate x h hx_ne h_lo_ne_s)
      ⟨h_F''_isOdd_dlo, h_F''_isOdd_dhi⟩
  rcases hy_faith with ⟨_, hy_le, hy_max⟩ | ⟨_, hy_ge, hy_min⟩
  · rcases hy'_faith with ⟨_, hy'_le, hy'_max⟩ | ⟨_, hy'_ge, hy'_min⟩
    · -- Both RoundDown.
      exact le_antisymm (hy'_max y hy_mem hy_le) (hy_max y' hy'_mem hy'_le)
    · exact h_mixed_eq hy_mem hy'_mem hy_le hy_max hy'_ge hy'_min hy_par hy'_par
  · rcases hy'_faith with ⟨_, hy'_le, hy'_max⟩ | ⟨_, hy'_ge, hy'_min⟩
    · -- Mixed (y RoundUp, y' RoundDown): apply helper with swap.
      exact (h_mixed_eq hy'_mem hy_mem hy'_le hy'_max hy_ge hy_min hy'_par hy_par).symm
    · -- Both RoundUp.
      exact le_antisymm (hy_min y' hy'_mem hy'_ge) (hy'_min y hy_mem hy_ge)


end Mpfx
