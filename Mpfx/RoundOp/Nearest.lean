import Mpfx.RoundOp.Defs

/-!
# Constructive rounding: `nearest` obligations

Soundness and uniqueness for the `nearest tb` rounding modes.
-/

namespace Mpfx

attribute [local instance] Classical.propDecidable

/-- Shared `nearest .toEven` tie-break dispatch. Runs the 6-leaf
`(F.p, F.exp) × regime` format case tree **once**, returning both the
parity-alternation iff `IsOdd dhi ↔ ¬ IsOdd dlo` (consumed by the
uniqueness proof) and the `IsEven` alternation `¬ IsEven dlo → IsEven dhi`
(consumed by the soundness proof). Both projections are thin wrappers over
the shared `alternating_parity_*_iff` cores in `Format.lean`; the only
tie-specific inputs are `x ≠ 0` and `(lo : ℝ) ≠ s`, whose differing
derivations stay at the call sites. -/
private theorem nearest_toEven_neighbors_alternate {F : FiniteFormat} (x : ℝ)
    (h : ¬ F.IsUndefined (.nearest .toEven))
    (hx_ne : x ≠ 0)
    (h_lo_ne_s :
      (⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ : ℝ) ≠ x * (2 : ℝ) ^ (-F.canonicalExp x)) :
    ((F.toParityFormatOfNearestEven h).IsOdd
        (Dyadic.ofIntZpow (⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ + 1) (F.canonicalExp x))
      ↔ ¬ (F.toParityFormatOfNearestEven h).IsOdd
        (Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ (F.canonicalExp x)))
    ∧ (¬ (F.toParityFormatOfNearestEven h).IsEven
        (Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ (F.canonicalExp x))
      → (F.toParityFormatOfNearestEven h).IsEven
        (Dyadic.ofIntZpow (⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ + 1) (F.canonicalExp x))) := by
  set e := F.canonicalExp x with h_e_def
  set s := x * (2 : ℝ) ^ (-e) with h_s_def
  set lo : ℤ := ⌊s⌋ with h_lo_def
  set dlo : Dyadic := Dyadic.ofIntZpow lo e with h_dlo_def
  set dhi : Dyadic := Dyadic.ofIntZpow (lo + 1) e with h_dhi_def
  set F'' := F.toParityFormatOfNearestEven h with hF''_def
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
      exact ⟨ParityFormat.alternating_parity_fixedpoint_iff hp_F hexp_F,
             ParityFormat.alternating_isEven_fixedpoint hp_F hexp_F⟩
  | coe p =>
    cases hexp_F : F.exp with
    | bot =>
      have hp_ne_1 : F.p ≠ ((1 : ℕ+) : WithTop ℕ+) := fun h_eq =>
        h ⟨h_eq, hexp_F, Or.inr rfl⟩
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
      exact ⟨ParityFormat.alternating_parity_floating_iff hp_F hp_ne_1 hexp_F
               h_lo_lo h_lo_hi h_lop1_lo h_lop1_hi,
             ParityFormat.alternating_isEven_floating hp_F hp_ne_1 hexp_F
               h_lo_lo h_lo_hi h_lop1_lo h_lop1_hi⟩
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
          exact ⟨ParityFormat.alternating_parity_mixed_subnormal_p1_iff hp_F hexp_F
                   h_lo_hi_int h_lop1_hi_int,
                 ParityFormat.alternating_isEven_mixed_subnormal_p1 hp_F hexp_F
                   h_lo_hi_int h_lop1_hi_int⟩
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
          exact ⟨ParityFormat.alternating_parity_mixed_normal_p1_iff hp_F hexp_F
                   h_e_ge h_lo_lo_int h_lo_hi_int h_lop1_lo_int h_lop1_hi_int,
                 ParityFormat.alternating_isEven_mixed_normal_p1 hp_F hexp_F
                   h_e_ge h_lo_lo_int h_lo_hi_int h_lop1_lo_int h_lop1_hi_int⟩
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
              exact ⟨ParityFormat.alternating_parity_mixed_subnormal_pne1_iff hp_F
                       hp_ne_1 hexp_F h_log_lo' h_log_lop1',
                     ParityFormat.alternating_isEven_mixed_subnormal_pne1 hp_F
                       hp_ne_1 hexp_F h_log_lo' h_log_lop1'⟩
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
              have h_even_dhi : F''.IsEven (Dyadic.ofIntZpow (lo + 1) e'') :=
                ParityFormat.isEven_at_saturation_mixed_normal hp_F hp_ne_1 hexp_F
                  h_dhi_ne h_log_y_ge h_dhi_real_e'' h_lop1_sat
              rw [h_dhi_at_e'', h_dlo_at_e'']
              exact ⟨⟨fun ho => absurd ho h_not_odd_dhi, fun hn => absurd h_odd_dlo hn⟩,
                     fun _ => h_even_dhi⟩
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
            have h_even_dlo : F''.IsEven (Dyadic.ofIntZpow lo e'') :=
              ParityFormat.isEven_at_saturation_mixed_normal hp_F hp_ne_1 hexp_F
                h_dlo_ne h_log_y_ge h_dlo_real_e'' h_lo_sat
            rw [h_dhi_at_e'', h_dlo_at_e'']
            exact ⟨⟨fun _ => h_not_odd_dlo, fun _ => h_odd_dhi⟩,
                   fun hn => absurd h_even_dlo hn⟩
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
          exact ⟨ParityFormat.alternating_parity_mixed_normal_pne1_iff hp_F hp_ne_1
                   hexp_F h_dlo_ne h_dhi_ne h_log_lo h_log_hi h_dlo_real h_dhi_real
                   h_lo_lo h_lo_hi h_lop1_lo h_lop1_hi,
                 ParityFormat.alternating_isEven_mixed_normal_pne1 hp_F hp_ne_1
                   hexp_F h_dlo_ne h_dhi_ne h_log_lo h_log_hi h_dlo_real h_dhi_real
                   h_lo_lo h_lo_hi h_lop1_lo h_lop1_hi⟩

/-- Shared `nearest` neighbour setup, consumed by both the soundness and
uniqueness proofs. Given the canonical scaling data
`e = canonicalExp x`, `s = x·2^(-e)`, `lo = ⌊s⌋` and the two neighbours
`dlo = lo·2^e`, `dhi = (lo+1)·2^e`, it packages: positivity of `2^e`,
membership of both neighbours, their real values, the floor sandwich,
the unscaling identity, the enclosure `dlo ≤ x ≤ dhi`, the two rounding
directions (`round-down`/`round-up`) and the faithful-round dichotomy
(any faithful round of `x` is `dlo` or `dhi`). The caller establishes the
`set` variables and passes the defining equations. -/
private theorem nearest_neighbors_setup (F : FiniteFormat) (x : ℝ)
    {e : ℤ} (h_e_def : e = F.canonicalExp x)
    {s : ℝ} (h_s_def : s = x * (2 : ℝ) ^ (-e))
    {lo : ℤ} (h_lo_def : lo = ⌊s⌋)
    {dlo dhi : Dyadic}
    (h_dlo_def : dlo = Dyadic.ofIntZpow lo e)
    (h_dhi_def : dhi = Dyadic.ofIntZpow (lo + 1) e) :
    (0 : ℝ) < (2 : ℝ) ^ e
    ∧ dlo ∈ F.unbounded ∧ dhi ∈ F.unbounded
    ∧ (dlo : ℝ) = (lo : ℝ) * (2 : ℝ) ^ e
    ∧ (dhi : ℝ) = ((lo + 1 : ℤ) : ℝ) * (2 : ℝ) ^ e
    ∧ (lo : ℝ) ≤ s ∧ s < (lo : ℝ) + 1 ∧ s * (2 : ℝ) ^ e = x
    ∧ (dlo : ℝ) ≤ x ∧ x ≤ (dhi : ℝ)
    ∧ (∀ z : Dyadic, z ∈ F.unbounded → (z : ℝ) ≤ x → (z : ℝ) ≤ (dlo : ℝ))
    ∧ ((lo : ℝ) ≠ s →
        ∀ z : Dyadic, z ∈ F.unbounded → x ≤ (z : ℝ) → (dhi : ℝ) ≤ (z : ℝ))
    ∧ (∀ y : Dyadic, IsFaithfulRound F.unbounded x y → y = dlo ∨ y = dhi) := by
  subst h_dhi_def h_dlo_def h_lo_def h_s_def h_e_def
  set e := F.canonicalExp x
  set s := x * (2 : ℝ) ^ (-e)
  set lo : ℤ := ⌊s⌋
  set dlo : Dyadic := Dyadic.ofIntZpow lo e
  set dhi : Dyadic := Dyadic.ofIntZpow (lo + 1) e
  have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
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
  have h_faithful_eq : ∀ y : Dyadic, IsFaithfulRound F.unbounded x y →
      y = dlo ∨ y = dhi := by
    intro y hf
    rcases hf with ⟨hy_mem, hy_le, hy_max⟩ | ⟨hy_mem, hy_ge, hy_min⟩
    · left
      apply Dyadic.ext_real
      exact le_antisymm (h_dlo_round_down y hy_mem hy_le)
        (hy_max dlo h_dlo_mem h_dlo_le_x)
    · by_cases hs_eq : (lo : ℝ) = s
      · left; apply Dyadic.ext_real
        have hx_eq_dlo : x = (dlo : ℝ) := by
          rw [h_dlo_real]
          have h_x_eq : x = s * (2 : ℝ) ^ e := by
            change x = x * (2 : ℝ) ^ (-e) * (2 : ℝ) ^ e
            rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
                neg_add_cancel, zpow_zero, mul_one]
          rw [h_x_eq, ← hs_eq]
        have h_y_le_dlo : (y : ℝ) ≤ (dlo : ℝ) :=
          hy_min dlo h_dlo_mem (le_of_eq hx_eq_dlo)
        have h_y_ge_dlo : (dlo : ℝ) ≤ (y : ℝ) := hx_eq_dlo ▸ hy_ge
        exact le_antisymm h_y_le_dlo h_y_ge_dlo
      · right; apply Dyadic.ext_real
        exact le_antisymm (hy_min dhi h_dhi_mem h_x_le_dhi)
          (h_dhi_round_up hs_eq y hy_mem hy_ge)
  exact ⟨h_2e_pos, h_dlo_mem, h_dhi_mem, h_dlo_real, h_dhi_real, h_floor_le_s,
         h_s_lt_succ, h_s_unscale, h_dlo_le_x, h_x_le_dhi, h_dlo_round_down,
         h_dhi_round_up, h_faithful_eq⟩

theorem rndUnbounded_satisfies_nearest (F : FiniteFormat) (tb : TieBreak) (x : ℝ)
    (h : ¬ F.IsUndefined (.nearest tb)) :
    RoundsFinite F.unbounded (.nearest tb) x (rndUnbounded F (.nearest tb) x h) := by
  -- Setup mirrors `rndUnbounded_satisfies_toOdd`.
  set e := F.canonicalExp x with h_e_def
  set s := x * (2 : ℝ) ^ (-e) with h_s_def
  set lo : ℤ := ⌊s⌋ with h_lo_def
  set dlo : Dyadic := Dyadic.ofIntZpow lo e with h_dlo_def
  set dhi : Dyadic := Dyadic.ofIntZpow (lo + 1) e with h_dhi_def
  obtain ⟨h_2e_pos, h_dlo_mem, h_dhi_mem, h_dlo_real, h_dhi_real, h_floor_le_s,
      h_s_lt_succ, h_s_unscale, h_dlo_le_x, h_x_le_dhi, h_dlo_round_down,
      h_dhi_round_up, h_faithful_eq⟩ :=
    nearest_neighbors_setup F x h_e_def h_s_def h_lo_def h_dlo_def h_dhi_def
  -- Distances |x - dlo| = δ · 2^e and |x - dhi| = (1 - δ) · 2^e.
  set δ := s - (lo : ℝ) with h_δ_def
  have h_δ_nn : 0 ≤ δ := by change 0 ≤ s - (lo : ℝ); linarith
  have h_δ_lt : δ < 1 := by change s - (lo : ℝ) < 1; linarith
  have h_x_minus_dlo : x - (dlo : ℝ) = δ * (2 : ℝ) ^ e := by
    rw [h_dlo_real, ← h_s_unscale]
    rw [h_δ_def]; ring
  have h_dhi_minus_x : (dhi : ℝ) - x = (1 - δ) * (2 : ℝ) ^ e := by
    rw [h_dhi_real, ← h_s_unscale]
    push_cast
    change ((lo : ℝ) + 1) * (2 : ℝ) ^ e - s * (2 : ℝ) ^ e = (1 - δ) * (2 : ℝ) ^ e
    rw [h_δ_def]; ring
  have h_abs_x_minus_dlo : |x - (dlo : ℝ)| = δ * (2 : ℝ) ^ e := by
    rw [h_x_minus_dlo]
    rw [abs_mul, abs_of_pos h_2e_pos, abs_of_nonneg h_δ_nn]
  have h_abs_x_minus_dhi : |x - (dhi : ℝ)| = (1 - δ) * (2 : ℝ) ^ e := by
    rw [show x - (dhi : ℝ) = -((dhi : ℝ) - x) by ring, abs_neg, h_dhi_minus_x]
    rw [abs_mul, abs_of_pos h_2e_pos, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - δ)]
  -- Distance min reduces to δ vs 1 - δ, i.e., δ vs 1/2.
  have h_dlo_closer : δ < 1/2 → |x - (dlo : ℝ)| < |x - (dhi : ℝ)| := by
    intro h_δ_lt_half
    rw [h_abs_x_minus_dlo, h_abs_x_minus_dhi]
    have : δ < 1 - δ := by linarith
    exact mul_lt_mul_of_pos_right this h_2e_pos
  have h_dhi_closer : 1/2 < δ → |x - (dhi : ℝ)| < |x - (dlo : ℝ)| := by
    intro h_δ_gt_half
    rw [h_abs_x_minus_dlo, h_abs_x_minus_dhi]
    have : 1 - δ < δ := by linarith
    exact mul_lt_mul_of_pos_right this h_2e_pos
  have h_dist_eq : δ = 1/2 → |x - (dlo : ℝ)| = |x - (dhi : ℝ)| := by
    intro h_δ_half
    rw [h_abs_x_minus_dlo, h_abs_x_minus_dhi]
    congr 1; linarith
  -- Now split on tb.
  cases tb with
  | awayZero =>
    -- rndUnbounded F (.nearest .awayZero) x h = Dyadic.ofIntZpow (rndInt ...) e.
    have h_rnd_eq : rndUnbounded F (.nearest .awayZero) x h =
        Dyadic.ofIntZpow (rndInt (.nearest .awayZero) x e) e := by
      unfold rndUnbounded
      rw [dif_neg (by decide : (RoundingMode.nearest .awayZero) ≠ .toOdd)]
      rw [dif_neg (by decide :
        (RoundingMode.nearest .awayZero) ≠ .nearest .toEven)]
    rw [h_rnd_eq]
    -- Establish rndInt's value depending on δ.
    have h_rndInt_eq : rndInt (.nearest .awayZero) x e =
        (if δ < 1/2 then lo
         else if 1/2 < δ then lo + 1
         else if 0 ≤ x then lo + 1 else lo) := by
      change (if s - (lo : ℝ) < 1/2 then lo
              else if 1/2 < s - (lo : ℝ) then lo + 1
              else if 0 ≤ x then lo + 1 else lo) =
             if δ < 1/2 then lo
             else if 1/2 < δ then lo + 1
             else if 0 ≤ x then lo + 1 else lo
      rw [h_δ_def]
    rw [h_rndInt_eq]
    by_cases h_lt_half : δ < 1/2
    · -- y = dlo.
      rw [if_pos h_lt_half]
      refine ⟨h_dlo_mem, ?_, ?_, ?_⟩
      · left; exact ⟨h_dlo_mem, h_dlo_le_x, h_dlo_round_down⟩
      · intro z hz_mem hz_faith
        rcases h_faithful_eq z hz_faith with h_eq | h_eq
        · rw [h_eq]
        · rw [h_eq]; exact le_of_lt (h_dlo_closer h_lt_half)
      · intro z hz_mem hz_faith hz_ne hz_dist
        rcases h_faithful_eq z hz_faith with h_eq | h_eq
        · rw [h_eq]
        · exfalso
          rw [h_eq] at hz_dist
          have := h_dlo_closer h_lt_half
          linarith
    · rw [if_neg h_lt_half]
      by_cases h_gt_half : 1/2 < δ
      · -- y = dhi.
        rw [if_pos h_gt_half]
        have h_lo_ne_s : (lo : ℝ) ≠ s := by
          intro h_eq
          have : δ = 0 := by rw [h_δ_def]; linarith
          linarith
        refine ⟨h_dhi_mem, ?_, ?_, ?_⟩
        · right; exact ⟨h_dhi_mem, h_x_le_dhi, h_dhi_round_up h_lo_ne_s⟩
        · intro z hz_mem hz_faith
          rcases h_faithful_eq z hz_faith with h_eq | h_eq
          · rw [h_eq]; exact le_of_lt (h_dhi_closer h_gt_half)
          · rw [h_eq]
        · intro z hz_mem hz_faith hz_ne hz_dist
          rcases h_faithful_eq z hz_faith with h_eq | h_eq
          · exfalso
            rw [h_eq] at hz_dist
            have := h_dhi_closer h_gt_half
            linarith
          · rw [h_eq]
      · -- Tie: δ = 1/2.
        rw [if_neg h_gt_half]
        have h_δ_eq : δ = 1/2 := by
          push Not at h_lt_half h_gt_half
          linarith
        have h_dist_eq' : |x - (dlo : ℝ)| = |x - (dhi : ℝ)| := h_dist_eq h_δ_eq
        have h_lo_ne_s : (lo : ℝ) ≠ s := by
          intro h_eq
          have : δ = 0 := by rw [h_δ_def]; linarith
          linarith
        by_cases hx_nn : 0 ≤ x
        · rw [if_pos hx_nn]
          refine ⟨h_dhi_mem, ?_, ?_, ?_⟩
          · right; exact ⟨h_dhi_mem, h_x_le_dhi, h_dhi_round_up h_lo_ne_s⟩
          · intro z hz_mem hz_faith
            rcases h_faithful_eq z hz_faith with h_eq | h_eq
            · rw [h_eq, h_dist_eq']
            · rw [h_eq]
          · -- Tie rule: |z| ≤ |dhi|. In tie case, z = dlo or dhi. Show |dlo| ≤ |dhi|.
            intro z hz_mem hz_faith hz_ne hz_dist
            rcases h_faithful_eq z hz_faith with h_eq | h_eq
            · -- z = dlo. Show |dlo| ≤ |dhi|.
              rw [h_eq]
              -- x ≥ 0, dlo ≤ x ≤ dhi. So 0 ≤ x ≤ dhi means dhi ≥ 0.
              -- |dhi| = dhi. dlo ≤ dhi. If dlo ≥ 0, |dlo| = dlo ≤ dhi = |dhi|.
              -- If dlo < 0, |dlo| = -dlo. dlo ≤ x with |x - dlo| = |x - dhi| = (1/2)·2^e.
              -- dhi - x = (1/2)·2^e = x - dlo. dhi = 2x - dlo. |dhi| = 2x - dlo (since dhi ≥ 0).
              -- |dlo| = -dlo. |dlo| ≤ |dhi| iff -dlo ≤ 2x - dlo iff 0 ≤ 2x iff x ≥ 0. ✓
              have h_dhi_nn : (0 : ℝ) ≤ (dhi : ℝ) := le_trans hx_nn h_x_le_dhi
              rw [abs_of_nonneg h_dhi_nn]
              by_cases hdlo_nn : (0 : ℝ) ≤ (dlo : ℝ)
              · rw [abs_of_nonneg hdlo_nn]
                linarith [h_x_minus_dlo, h_dhi_minus_x, h_δ_eq]
              · push Not at hdlo_nn
                rw [abs_of_neg hdlo_nn]
                have h1 : x - (dlo : ℝ) = (1/2) * (2 : ℝ) ^ e := by
                  rw [h_x_minus_dlo, h_δ_eq]
                have h2 : (dhi : ℝ) - x = (1/2) * (2 : ℝ) ^ e := by
                  rw [h_dhi_minus_x, h_δ_eq]; ring
                linarith
            · rw [h_eq]
        · push Not at hx_nn
          rw [if_neg (by linarith : ¬ 0 ≤ x)]
          refine ⟨h_dlo_mem, ?_, ?_, ?_⟩
          · left; exact ⟨h_dlo_mem, h_dlo_le_x, h_dlo_round_down⟩
          · intro z hz_mem hz_faith
            rcases h_faithful_eq z hz_faith with h_eq | h_eq
            · rw [h_eq]
            · rw [h_eq, ← h_dist_eq']
          · -- Tie rule: x < 0, |z| ≤ |dlo|.
            intro z hz_mem hz_faith hz_ne hz_dist
            rcases h_faithful_eq z hz_faith with h_eq | h_eq
            · rw [h_eq]
            · -- z = dhi. dlo ≤ x < 0. |dlo| = -dlo, |dhi| = ?
              -- dhi - x = (1/2)·2^e = x - dlo. dhi = 2x - dlo.
              -- If dhi ≥ 0: |dhi| = 2x - dlo. |dlo| = -dlo.
              --   |dhi| ≤ |dlo| iff 2x - dlo ≤ -dlo iff 2x ≤ 0 iff x ≤ 0. ✓
              -- If dhi < 0: |dhi| = -dhi = -(2x - dlo) = dlo - 2x. |dlo| = -dlo.
              --   |dhi| ≤ |dlo| iff dlo - 2x ≤ -dlo iff 2dlo ≤ 2x iff dlo ≤ x. ✓
              rw [h_eq]
              have h_dlo_neg : (dlo : ℝ) < 0 := lt_of_le_of_lt h_dlo_le_x hx_nn
              rw [abs_of_neg h_dlo_neg]
              have h1 : x - (dlo : ℝ) = (1/2) * (2 : ℝ) ^ e := by
                rw [h_x_minus_dlo, h_δ_eq]
              have h2 : (dhi : ℝ) - x = (1/2) * (2 : ℝ) ^ e := by
                rw [h_dhi_minus_x, h_δ_eq]; ring
              by_cases hdhi_nn : (0 : ℝ) ≤ (dhi : ℝ)
              · rw [abs_of_nonneg hdhi_nn]
                linarith
              · push Not at hdhi_nn
                rw [abs_of_neg hdhi_nn]
                linarith
  | toEven =>
    have h_unb : ¬ F.unbounded.IsUndefined (.nearest .toEven) := h
    set F'' := F.toParityFormatOfNearestEven h with hF''_def
    set F' := F.unbounded.toParityFormatOfNearestEven h_unb with hF'_def
    have h_F'_eq : F'.toFormat = F.unbounded.toFormat := rfl
    -- Bridge: F'' and F' agree on IsEven (same p, exp).
    have h_isEven_bridge : ∀ (y : Dyadic), F''.IsEven y ↔ F'.IsEven y :=
      fun y => Iff.rfl
    have h_rnd_eq : rndUnbounded F (.nearest .toEven) x h =
        rndParity F'' (.nearest .toEven) x e := by
      unfold rndUnbounded
      rw [dif_neg (by decide : (RoundingMode.nearest .toEven) ≠ .toOdd)]
      rw [dif_pos rfl]
    rw [h_rnd_eq]
    -- rndParity for .nearest .toEven uses δ.
    have h_rndParity_eq : rndParity F'' (.nearest .toEven) x e =
        if δ < 1/2 then dlo
        else if 1/2 < δ then dhi
        else if F''.IsEven dlo then dlo else dhi := by
      change (if s - (lo : ℝ) < 1/2 then dlo
              else if 1/2 < s - (lo : ℝ) then dhi
              else if F''.IsEven dlo then dlo else dhi) =
           if δ < 1/2 then dlo
           else if 1/2 < δ then dhi
           else if F''.IsEven dlo then dlo else dhi
      rw [h_δ_def]
    rw [h_rndParity_eq]
    by_cases h_lt_half : δ < 1/2
    · rw [if_pos h_lt_half]
      refine ⟨h_dlo_mem, ?_, ?_, ?_⟩
      · left; exact ⟨h_dlo_mem, h_dlo_le_x, h_dlo_round_down⟩
      · intro z hz_mem hz_faith
        rcases h_faithful_eq z hz_faith with h_eq | h_eq
        · rw [h_eq]
        · rw [h_eq]; exact le_of_lt (h_dlo_closer h_lt_half)
      · -- No tie: no z ≠ dlo equidistant with dlo.
        rintro ⟨z, hz_mem, hz_faith, hz_ne, hz_dist⟩
        exfalso
        rcases h_faithful_eq z hz_faith with h_eq | h_eq
        · exact hz_ne h_eq
        · rw [h_eq] at hz_dist
          have := h_dlo_closer h_lt_half
          linarith
    · rw [if_neg h_lt_half]
      by_cases h_gt_half : 1/2 < δ
      · rw [if_pos h_gt_half]
        have h_lo_ne_s : (lo : ℝ) ≠ s := by
          intro h_eq
          have : δ = 0 := by rw [h_δ_def]; linarith
          linarith
        refine ⟨h_dhi_mem, ?_, ?_, ?_⟩
        · right; exact ⟨h_dhi_mem, h_x_le_dhi, h_dhi_round_up h_lo_ne_s⟩
        · intro z hz_mem hz_faith
          rcases h_faithful_eq z hz_faith with h_eq | h_eq
          · rw [h_eq]; exact le_of_lt (h_dhi_closer h_gt_half)
          · rw [h_eq]
        · rintro ⟨z, hz_mem, hz_faith, hz_ne, hz_dist⟩
          exfalso
          rcases h_faithful_eq z hz_faith with h_eq | h_eq
          · rw [h_eq] at hz_dist
            have := h_dhi_closer h_gt_half
            linarith
          · exact hz_ne h_eq
      · rw [if_neg h_gt_half]
        have h_δ_eq : δ = 1/2 := by
          push Not at h_lt_half h_gt_half; linarith
        have h_dist_eq' : |x - (dlo : ℝ)| = |x - (dhi : ℝ)| := h_dist_eq h_δ_eq
        have h_lo_ne_s : (lo : ℝ) ≠ s := by
          intro h_eq
          have : δ = 0 := by rw [h_δ_def]; linarith
          linarith
        by_cases h_even_dlo : F''.IsEven dlo
        · rw [if_pos h_even_dlo]
          refine ⟨h_dlo_mem, ?_, ?_, ?_⟩
          · left; exact ⟨h_dlo_mem, h_dlo_le_x, h_dlo_round_down⟩
          · intro z hz_mem hz_faith
            rcases h_faithful_eq z hz_faith with h_eq | h_eq
            · rw [h_eq]
            · rw [h_eq, h_dist_eq']
          · intro _
            refine ⟨F', h_F'_eq, (h_isEven_bridge dlo).mp h_even_dlo⟩
        · rw [if_neg h_even_dlo]
          refine ⟨h_dhi_mem, ?_, ?_, ?_⟩
          · right; exact ⟨h_dhi_mem, h_x_le_dhi, h_dhi_round_up h_lo_ne_s⟩
          · intro z hz_mem hz_faith
            rcases h_faithful_eq z hz_faith with h_eq | h_eq
            · rw [h_eq, ← h_dist_eq']
            · rw [h_eq]
          · intro _
            refine ⟨F', h_F'_eq, ?_⟩
            rw [← h_isEven_bridge dhi]
            -- Alternation from the shared `nearest .toEven` dispatch lemma.
            have hx_ne : x ≠ 0 := by
              intro hx0
              subst hx0
              have h_s_zero : s = 0 := by change (0 : ℝ) * (2 : ℝ) ^ (-e) = 0; ring
              have h_δ_zero_lo : δ = -lo := by
                change s - (lo : ℝ) = -lo
                rw [h_s_zero]; ring
              rw [h_δ_zero_lo] at h_δ_eq
              have h_2lo_neg1 : 2 * lo = -1 := by
                have h_real : (2 * lo : ℝ) = -1 := by linarith
                exact_mod_cast h_real
              omega
            exact (nearest_toEven_neighbors_alternate x h hx_ne h_lo_ne_s).2 h_even_dlo


theorem rndUnbounded_unique_nearest (F : FiniteFormat) (tb : TieBreak) (x : ℝ)
    (h : ¬ F.IsUndefined (.nearest tb)) {y : Dyadic}
    (hy : RoundsFinite F.unbounded (.nearest tb) x y) :
    y = rndUnbounded F (.nearest tb) x h := by
  set y' := rndUnbounded F (.nearest tb) x h with hy'_def
  have hy' : RoundsFinite F.unbounded (.nearest tb) x y' :=
    rndUnbounded_satisfies_nearest F tb x h
  -- Both y, y' satisfy the same spec. They're equidistant, and the tie-break
  -- uniquely determines them.
  cases tb with
  | awayZero =>
    obtain ⟨hy_mem, hy_faith, hy_min, hy_tie⟩ := hy
    obtain ⟨hy'_mem, hy'_faith, hy'_min, hy'_tie⟩ := hy'
    have h_dist_eq : |x - (y : ℝ)| = |x - (y' : ℝ)| :=
      le_antisymm (hy_min y' hy'_mem hy'_faith) (hy'_min y hy_mem hy_faith)
    by_cases h_yy : y = y'
    · exact h_yy
    · apply Dyadic.ext_real
      have h_y_le_y' : |(y : ℝ)| ≤ |(y' : ℝ)| :=
        hy'_tie y hy_mem hy_faith h_yy h_dist_eq.symm
      have h_y'_le_y : |(y' : ℝ)| ≤ |(y : ℝ)| :=
        hy_tie y' hy'_mem hy'_faith (Ne.symm h_yy) h_dist_eq
      -- |y| = |y'| and dist eq give y² = y'² and 2x(y - y') = 0. y ≠ y' ⟹ x = 0.
      have h_abs_eq : |(y : ℝ)| = |(y' : ℝ)| := le_antisymm h_y_le_y' h_y'_le_y
      have h_sq : (y : ℝ) ^ 2 = (y' : ℝ) ^ 2 := by
        have h1 : |(y : ℝ)| ^ 2 = |(y' : ℝ)| ^ 2 := by rw [h_abs_eq]
        rw [sq_abs, sq_abs] at h1
        exact h1
      have h_x_zero : x = 0 := by
        have h_dist_sq : (x - (y : ℝ)) ^ 2 = (x - (y' : ℝ)) ^ 2 := by
          have h1 : |x - (y : ℝ)| ^ 2 = |x - (y' : ℝ)| ^ 2 := by rw [h_dist_eq]
          rw [sq_abs, sq_abs] at h1
          exact h1
        have h_expand : 2 * x * ((y : ℝ) - (y' : ℝ)) = 0 := by
          have : (x - (y : ℝ)) ^ 2 - (x - (y' : ℝ)) ^ 2 = 0 := by linarith
          have : 2 * x * ((y' : ℝ) - (y : ℝ)) + ((y : ℝ)^2 - (y' : ℝ)^2) = 0 := by
            ring_nf; ring_nf at this; linarith
          linarith [h_sq]
        have h_y_ne_y' : (y : ℝ) ≠ (y' : ℝ) := fun heq =>
          h_yy (Dyadic.ext_real heq)
        have h_diff_ne : (y : ℝ) - (y' : ℝ) ≠ 0 := sub_ne_zero.mpr h_y_ne_y'
        have h_2x : 2 * x = 0 := by
          by_contra h2x
          have : 2 * x * ((y : ℝ) - (y' : ℝ)) ≠ 0 := mul_ne_zero h2x h_diff_ne
          exact this h_expand
        linarith
      -- At x = 0, faithful round of 0 must be 0 (since 0 ∈ F). So y = y' = 0.
      have h_zero_mem : (0 : Dyadic) ∈ F.unbounded := FiniteFormat.zero_mem F.unbounded
      have h_y_eq_zero : (y : ℝ) = 0 := by
        rcases hy_faith with ⟨_, hy_le, hy_max⟩ | ⟨_, hy_ge, hy_min'⟩
        · -- y ≤ x = 0 and 0 ∈ F means y is max F-elt ≤ 0, hence y = 0.
          rw [h_x_zero] at hy_le
          have h_zero_le_y : ((0 : Dyadic) : ℝ) ≤ (y : ℝ) := by
            have := hy_max 0 h_zero_mem (by rw [h_x_zero]; simp)
            simpa using this
          rw [Dyadic.coe_real_zero] at h_zero_le_y
          linarith
        · rw [h_x_zero] at hy_ge
          have h_y_le_zero : (y : ℝ) ≤ ((0 : Dyadic) : ℝ) := by
            have := hy_min' 0 h_zero_mem (by rw [h_x_zero]; simp)
            simpa using this
          rw [Dyadic.coe_real_zero] at h_y_le_zero
          linarith
      have h_y'_eq_zero : (y' : ℝ) = 0 := by
        rcases hy'_faith with ⟨_, hy'_le, hy'_max⟩ | ⟨_, hy'_ge, hy'_min'⟩
        · rw [h_x_zero] at hy'_le
          have h_zero_le_y' : ((0 : Dyadic) : ℝ) ≤ (y' : ℝ) := by
            have := hy'_max 0 h_zero_mem (by rw [h_x_zero]; simp)
            simpa using this
          rw [Dyadic.coe_real_zero] at h_zero_le_y'
          linarith
        · rw [h_x_zero] at hy'_ge
          have h_y'_le_zero : (y' : ℝ) ≤ ((0 : Dyadic) : ℝ) := by
            have := hy'_min' 0 h_zero_mem (by rw [h_x_zero]; simp)
            simpa using this
          rw [Dyadic.coe_real_zero] at h_y'_le_zero
          linarith
      rw [h_y_eq_zero, h_y'_eq_zero]
  | toEven =>
    obtain ⟨hy_mem, hy_faith, hy_min, hy_tie⟩ := hy
    obtain ⟨hy'_mem, hy'_faith, hy'_min, hy'_tie⟩ := hy'
    have h_dist_eq : |x - (y : ℝ)| = |x - (y' : ℝ)| :=
      le_antisymm (hy_min y' hy'_mem hy'_faith) (hy'_min y hy_mem hy_faith)
    by_cases h_yy : y = y'
    · exact h_yy
    · -- Tie case: both y and y' must be IsEven (per tie-break). Among {dlo, dhi},
      -- at most one is IsEven. So y = y' — contradiction with h_yy unless
      -- y = y' = unique even.
      -- But here we have y ≠ y'. Derive that both are IsEven and arrive at
      -- contradiction via parity dichotomy + alternating.
      exfalso
      have h_F_y_even : ∃ F' : ParityFormat, F'.toFormat = F.unbounded.toFormat ∧ F'.IsEven y :=
        hy_tie ⟨y', hy'_mem, hy'_faith, fun heq => h_yy heq.symm, h_dist_eq⟩
      have h_F_y'_even : ∃ F' : ParityFormat, F'.toFormat = F.unbounded.toFormat ∧ F'.IsEven y' :=
        hy'_tie ⟨y, hy_mem, hy_faith, h_yy, h_dist_eq.symm⟩
      obtain ⟨F_y, hF_y_eq, hF_y_even⟩ := h_F_y_even
      obtain ⟨F_y', hF_y'_eq, hF_y'_even⟩ := h_F_y'_even
      -- Bridge via IsEven_iff_of_toFormat_eq to a common ParityFormat F''.
      have h_unb : ¬ F.unbounded.IsUndefined (.nearest .toEven) := h
      set F'' := F.unbounded.toParityFormatOfNearestEven h_unb with hF''_def
      have hF''_eq : F''.toFormat = F.unbounded.toFormat := rfl
      have hF_y_eq_F'' : F_y.toFormat = F''.toFormat := by rw [hF_y_eq, hF''_eq]
      have hF_y'_eq_F'' : F_y'.toFormat = F''.toFormat := by rw [hF_y'_eq, hF''_eq]
      have hF''_even_y : F''.IsEven y :=
        ((ParityFormat.IsEven_iff_of_toFormat_eq hF_y_eq_F'' y).mp hF_y_even)
      have hF''_even_y' : F''.IsEven y' :=
        ((ParityFormat.IsEven_iff_of_toFormat_eq hF_y'_eq_F'' y').mp hF_y'_even)
      -- Neighbour setup shared with the soundness proof.
      set e := F.canonicalExp x with h_e_def
      set s := x * (2 : ℝ) ^ (-e) with h_s_def
      set lo : ℤ := ⌊s⌋ with h_lo_def
      set dlo : Dyadic := Dyadic.ofIntZpow lo e with h_dlo_def
      set dhi : Dyadic := Dyadic.ofIntZpow (lo + 1) e with h_dhi_def
      obtain ⟨-, h_dlo_mem, -, h_dlo_real, -, -, -, h_s_unscale, h_dlo_le_x, -,
          h_dlo_round_down, -, h_faithful_eq⟩ :=
        nearest_neighbors_setup F x h_e_def h_s_def h_lo_def h_dlo_def h_dhi_def
      -- y, y' ∈ {dlo, dhi}.
      have h_both_even : F''.IsEven dlo ∧ F''.IsEven dhi := by
        rcases h_faithful_eq y hy_faith with h_y_dlo | h_y_dhi
        · rcases h_faithful_eq y' hy'_faith with h_y'_dlo | h_y'_dhi
          · exact absurd (h_y_dlo.trans h_y'_dlo.symm) h_yy
          · refine ⟨?_, ?_⟩
            · rw [h_y_dlo] at hF''_even_y; exact hF''_even_y
            · rw [h_y'_dhi] at hF''_even_y'; exact hF''_even_y'
        · rcases h_faithful_eq y' hy'_faith with h_y'_dlo | h_y'_dhi
          · refine ⟨?_, ?_⟩
            · rw [h_y'_dlo] at hF''_even_y'; exact hF''_even_y'
            · rw [h_y_dhi] at hF''_even_y; exact hF''_even_y
          · exact absurd (h_y_dhi.trans h_y'_dhi.symm) h_yy
      obtain ⟨h_F''_even_dlo, h_F''_even_dhi⟩ := h_both_even
      -- Both `dlo` and `dhi` are `IsEven`, but the shared dispatch lemma forces
      -- the neighbours to alternate: `¬ IsOdd dlo → IsOdd dhi`, contradicting
      -- `IsEven dhi`.
      have hx_ne : x ≠ 0 := by
        intro hx0
        subst hx0
        have h_zero_mem : (0 : Dyadic) ∈ F.unbounded := FiniteFormat.zero_mem F.unbounded
        have h_y_eq_z : (y : ℝ) = 0 := by
          rcases hy_faith with ⟨_, hy_le, hy_max⟩ | ⟨_, hy_ge, hy_min'⟩
          · have h_zero_le_y : ((0 : Dyadic) : ℝ) ≤ (y : ℝ) := by
              have := hy_max 0 h_zero_mem (by simp); simpa using this
            rw [Dyadic.coe_real_zero] at h_zero_le_y; linarith
          · have h_y_le_z : (y : ℝ) ≤ ((0 : Dyadic) : ℝ) := by
              have := hy_min' 0 h_zero_mem (by simp); simpa using this
            rw [Dyadic.coe_real_zero] at h_y_le_z; linarith
        have h_y'_eq_z : (y' : ℝ) = 0 := by
          rcases hy'_faith with ⟨_, hy'_le, hy'_max⟩ | ⟨_, hy'_ge, hy'_min'⟩
          · have h_zero_le_y' : ((0 : Dyadic) : ℝ) ≤ (y' : ℝ) := by
              have := hy'_max 0 h_zero_mem (by simp); simpa using this
            rw [Dyadic.coe_real_zero] at h_zero_le_y'; linarith
          · have h_y'_le_z : (y' : ℝ) ≤ ((0 : Dyadic) : ℝ) := by
              have := hy'_min' 0 h_zero_mem (by simp); simpa using this
            rw [Dyadic.coe_real_zero] at h_y'_le_z; linarith
        exact h_yy (Dyadic.ext_real (h_y_eq_z.trans h_y'_eq_z.symm))
      have h_lo_ne_s : (lo : ℝ) ≠ s := by
        intro h_eq
        have h_x_eq_dlo : x = (dlo : ℝ) := by
          rw [h_dlo_real]
          have : x = s * (2 : ℝ) ^ e := h_s_unscale.symm
          rw [this, ← h_eq]
        have h_y_eq_dlo' : (y : ℝ) = (dlo : ℝ) := by
          rcases hy_faith with ⟨_, hy_le, hy_max⟩ | ⟨_, hy_ge, hy_min'⟩
          · exact le_antisymm (h_dlo_round_down y hy_mem hy_le)
              (hy_max dlo h_dlo_mem h_dlo_le_x)
          · exact le_antisymm (hy_min' dlo h_dlo_mem (le_of_eq h_x_eq_dlo))
              (h_x_eq_dlo ▸ hy_ge)
        have h_y'_eq_dlo' : (y' : ℝ) = (dlo : ℝ) := by
          rcases hy'_faith with ⟨_, hy'_le, hy'_max⟩ | ⟨_, hy'_ge, hy'_min'⟩
          · exact le_antisymm (h_dlo_round_down y' hy'_mem hy'_le)
              (hy'_max dlo h_dlo_mem h_dlo_le_x)
          · exact le_antisymm (hy'_min' dlo h_dlo_mem (le_of_eq h_x_eq_dlo))
              (h_x_eq_dlo ▸ hy'_ge)
        exact h_yy (Dyadic.ext_real (h_y_eq_dlo'.trans h_y'_eq_dlo'.symm))
      have h_not_isOdd_dlo : ¬ F''.IsOdd dlo := fun h_odd =>
        ParityFormat.not_isEven_and_isOdd h_F''_even_dlo h_odd
      have h_isOdd_dhi : F''.IsOdd dhi :=
        (nearest_toEven_neighbors_alternate x h hx_ne h_lo_ne_s).1.mpr h_not_isOdd_dlo
      exact ParityFormat.not_isEven_and_isOdd h_F''_even_dhi h_isOdd_dhi


end Mpfx
