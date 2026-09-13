import Mpfx.Rounding
import Mpfx.CanonicalExp

/-!
# Parity of adjacent grid points

For `x` strictly between its neighbouring grid points at the canonical exponent,
those neighbours have opposite parity. `neighbors_alternate` proves it once; the
`toOdd` and `nearest .toEven` forms are projections.
-/

namespace Mpfx

/-- At step `2 ^ cexp x`, the two neighbours of `x` alternate: the upper one is
odd exactly when the lower one is not, and evenness alternates with it. -/
private abbrev Alternate (F : FiniteFormat) (h : ¬ F.IsUndefined .toOdd) (x : ℝ) : Prop :=
  ((F.toParityFormatOfToOdd h).IsOdd
      (Dyadic.ofIntZpow (⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ + 1) (F.canonicalExp x))
    ↔ ¬ (F.toParityFormatOfToOdd h).IsOdd
      (Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ (F.canonicalExp x)))
  ∧ (¬ (F.toParityFormatOfToOdd h).IsEven
      (Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ (F.canonicalExp x))
    → (F.toParityFormatOfToOdd h).IsEven
      (Dyadic.ofIntZpow (⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ + 1) (F.canonicalExp x)))

/-- Precision `p ≠ 1`, minimum quantum `e''`, `x` **normal**
(`e'' < ⌊log₂|x|⌋ + 1 − p`): both neighbours carry a full `p`-bit significand. -/
private theorem alternate_normal_pne1 {F : FiniteFormat} (h : ¬ F.IsUndefined .toOdd)
    {x : ℝ} {p : ℕ} {e'' : ℤ} (hp_F : F.p = (p : Prec))
    (hexp_F : F.exp = (e'' : QExp)) (hp_ne_1 : F.p ≠ ((1 : ℕ) : Prec))
    (hx_ne : x ≠ 0) (h_regime : e'' < Int.log 2 |x| + 1 - (p : ℤ))
    (h_lo_ne_s : (⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ : ℝ)
      ≠ x * (2 : ℝ) ^ (-F.canonicalExp x)) :
    Alternate F h x := by
  unfold Alternate
  set e := F.canonicalExp x with h_e_def
  set s := x * (2 : ℝ) ^ (-e) with h_s_def
  set lo : ℤ := ⌊s⌋ with h_lo_def
  set dlo : Dyadic := Dyadic.ofIntZpow lo e with h_dlo_def
  set dhi : Dyadic := Dyadic.ofIntZpow (lo + 1) e with h_dhi_def
  set F'' := F.toParityFormatOfToOdd h with hF''_def
  have h_floor_le_s : (lo : ℝ) ≤ s := Int.floor_le _
  have h_lo_bound : ∀ {q : ℕ}, F.p = (q : Prec) → |lo| ≤ (2 : ℤ) ^ q := fun hq => by
    apply abs_floor_le_of_abs_lt
    push_cast; exact floor_mantissa_lt hq
  have h_lop1_bound : ∀ {q : ℕ}, F.p = (q : Prec) → |lo + 1| ≤ (2 : ℤ) ^ q := fun hq =>
    abs_floor_add_one_le_of_abs_lt (floor_mantissa_lt hq)
  have h_dlo_real : (dlo : ℝ) = (lo : ℝ) * (2 : ℝ) ^ e := Dyadic.coe_ofIntZpow _ _
  have h_dhi_real : (dhi : ℝ) = ((lo + 1 : ℤ) : ℝ) * (2 : ℝ) ^ e := Dyadic.coe_ofIntZpow _ _
  have h_e_eq_log : e = Int.log 2 |x| + 1 - (p : ℤ) :=
    canonicalExp_closed hp_F hx_ne (by rw [hexp_F]; exact_mod_cast h_regime.le)
  have h_s_lo_real : ((2 : ℤ) ^ (p - 1) : ℝ) ≤
      |x * (2 : ℝ) ^ (-e)| :=
    two_pow_pred_le_scaled (p := p) (F.p_pos hp_F) hx_ne h_e_eq_log
  have h_lo_lo : (2 : ℤ) ^ (p - 1) ≤ |lo| :=
    abs_floor_ge_two_pow_pred (p := p) h_s_lo_real
  have h_lop1_lo : (2 : ℤ) ^ (p - 1) ≤ |lo + 1| :=
    abs_floor_add_one_ge_two_pow_pred (p := p) h_s_lo_real h_lo_ne_s
  have h_lo_hi : |lo| ≤ (2 : ℤ) ^ p := h_lo_bound hp_F
  have h_lop1_hi : |lo + 1| ≤ (2 : ℤ) ^ p :=
    h_lop1_bound hp_F
  have h_lo_ne : lo ≠ 0 := by
    intro h_lo_zero
    rw [h_lo_zero] at h_lo_lo
    simp at h_lo_lo
    have : (0 : ℤ) < (2 : ℤ) ^ (p - 1) := by positivity
    omega
  have h_lop1_ne : lo + 1 ≠ 0 := by
    intro h_lop1_zero
    rw [h_lop1_zero] at h_lop1_lo
    simp at h_lop1_lo
    have : (0 : ℤ) < (2 : ℤ) ^ (p - 1) := by positivity
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
  have h_log_lo_lb := log_ge_p_pred_of_two_pow_pred_le (F.p_pos hp_F)
    (k := lo) h_lo_lo
  have h_log_lop1_lb := log_ge_p_pred_of_two_pow_pred_le (F.p_pos hp_F)
    (k := lo + 1) h_lop1_lo
  have h_log_lo : (p : ℤ) ≤ Int.log 2 |(dlo : ℝ)| - e'' + 1 := by
    rw [h_log_dlo, h_e_eq_log]
    have : Int.log 2 |x| - e'' ≥ (p : ℤ) := by linarith
    linarith [h_log_lo_lb]
  have h_log_hi : (p : ℤ) ≤ Int.log 2 |(dhi : ℝ)| - e'' + 1 := by
    rw [h_log_dhi, h_e_eq_log]
    have : Int.log 2 |x| - e'' ≥ (p : ℤ) := by linarith
    linarith [h_log_lop1_lb]
  exact ⟨ParityFormat.alternating_parity_mixed_normal_pne1_iff hp_F hp_ne_1
           hexp_F h_dlo_ne h_dhi_ne h_log_lo h_log_hi h_dlo_real h_dhi_real
           h_lo_lo h_lo_hi h_lop1_lo h_lop1_hi,
         ParityFormat.alternating_isEven_mixed_normal_pne1 hp_F hp_ne_1
           hexp_F h_dlo_ne h_dhi_ne h_log_lo h_log_hi h_dlo_real h_dhi_real
           h_lo_lo h_lo_hi h_lop1_lo h_lop1_hi⟩

/-- Precision `p ≠ 1`, minimum quantum `e''`, `x` **subnormal**
(`⌊log₂|x|⌋ + 1 − p ≤ e''`), so the step is `2 ^ e''` and the coefficients are
bounded by `2 ^ p`. Splits three ways on whether either coefficient saturates
that bound: at saturation the neighbour is a pure power of two, whose parity is
read off directly rather than from the `alternating_*` family. -/
private theorem alternate_subnormal_pne1 {F : FiniteFormat} (h : ¬ F.IsUndefined .toOdd)
    {x : ℝ} {p : ℕ} {e'' : ℤ} (hp_F : F.p = (p : Prec))
    (hexp_F : F.exp = (e'' : QExp)) (hp_ne_1 : F.p ≠ ((1 : ℕ) : Prec))
    (hx_ne : x ≠ 0) (h_regime : Int.log 2 |x| + 1 - (p : ℤ) ≤ e'') :
    Alternate F h x := by
  unfold Alternate
  set e := F.canonicalExp x with h_e_def
  set s := x * (2 : ℝ) ^ (-e) with h_s_def
  set lo : ℤ := ⌊s⌋ with h_lo_def
  set dlo : Dyadic := Dyadic.ofIntZpow lo e with h_dlo_def
  set dhi : Dyadic := Dyadic.ofIntZpow (lo + 1) e with h_dhi_def
  set F'' := F.toParityFormatOfToOdd h with hF''_def
  have h_e_eq : e = e'' := canonicalExp_subnormal hp_F hexp_F hx_ne h_regime
  have h_x_lt : |x| < (2 : ℝ) ^ (e'' + (p : ℤ)) := by
    have h_log_le : Int.log 2 |x| ≤ e'' + (p : ℤ) - 1 := by
      linarith
    have h_lt := Int.lt_zpow_succ_log_self
      (by norm_num : (1 : ℕ) < 2) |x|
    have : Int.log 2 |x| + 1 ≤ e'' + (p : ℤ) := by linarith
    exact lt_of_lt_of_le h_lt
      (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) this)
  have h_s_lt : |x * (2 : ℝ) ^ (-e)| < (2 : ℝ) ^ p := by
    rw [h_e_eq]
    have h_abs : |x * (2 : ℝ) ^ (-e'')| = |x| * (2 : ℝ) ^ (-e'') := by
      rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)]
    rw [h_abs]
    have h_2neg_pos : (0 : ℝ) < (2 : ℝ) ^ (-e'') := zpow_pos (by norm_num) _
    have h_eq_split : (2 : ℝ) ^ (e'' + (p : ℤ)) =
        (2 : ℝ) ^ e'' * (2 : ℝ) ^ p := by
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      rw [zpow_natCast]
    have h_x2neg : |x| * (2 : ℝ) ^ (-e'') <
        (2 : ℝ) ^ (e'' + (p : ℤ)) * (2 : ℝ) ^ (-e'') :=
      mul_lt_mul_of_pos_right h_x_lt h_2neg_pos
    rw [h_eq_split] at h_x2neg
    have h_cancel : (2 : ℝ) ^ e'' * (2 : ℝ) ^ p *
        (2 : ℝ) ^ (-e'') = (2 : ℝ) ^ p := by
      rw [mul_right_comm, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
          add_neg_cancel, zpow_zero, one_mul]
    rw [h_cancel] at h_x2neg
    exact h_x2neg
  have h_lo_le : |lo| ≤ (2 : ℤ) ^ p := by
    apply abs_floor_le_of_abs_lt; push_cast; exact h_s_lt
  have h_lop1_le : |lo + 1| ≤ (2 : ℤ) ^ p :=
    abs_floor_add_one_le_of_abs_lt h_s_lt
  have h_dlo_at_e'' : dlo = Dyadic.ofIntZpow lo e'' := by rw [h_dlo_def, h_e_eq]
  have h_dhi_at_e'' : dhi = Dyadic.ofIntZpow (lo + 1) e'' := by
    rw [h_dhi_def, h_e_eq]
  have h2p_nn : (0 : ℤ) ≤ (2 : ℤ) ^ p := by positivity
  rcases lt_or_eq_of_le h_lo_le with h_lo_lt | h_lo_sat
  · have h_log_lo' := log_lt_p_of_abs_lt_two_pow (F.p_pos hp_F) h_lo_lt
    rcases lt_or_eq_of_le h_lop1_le with h_lop1_lt | h_lop1_sat
    · have h_log_lop1_raw := log_lt_p_of_abs_lt_two_pow (F.p_pos hp_F) h_lop1_lt
      have h_log_lop1' : Int.log 2 |((lo : ℝ) + 1)| + 1 ≤
          (p : ℤ) := by
        have h_eq : |((lo : ℝ) + 1)| = |((lo + 1 : ℤ) : ℝ)| := by
          push_cast; rfl
        rw [h_eq]; exact h_log_lop1_raw
      rw [h_dhi_at_e'', h_dlo_at_e'']
      exact ⟨ParityFormat.alternating_parity_mixed_subnormal_pne1_iff hp_F
               hp_ne_1 hexp_F h_log_lo' h_log_lop1',
             ParityFormat.alternating_isEven_mixed_subnormal_pne1 hp_F
               hp_ne_1 hexp_F h_log_lo' h_log_lop1'⟩
    · -- `|lo+1| = 2^p` saturated (dhi even/¬odd), `lo` odd (dlo odd).
      have h_even2p : Even ((2 : ℤ) ^ p) := by
        refine ⟨(2 : ℤ) ^ (p - 1), ?_⟩
        have := Dyadic.two_pow_succ_pred (F.p_pos hp_F)
        linarith
      have h_lo_ne : lo ≠ 0 := by
        intro h_zero
        rw [h_zero] at h_lop1_sat
        simp at h_lop1_sat
        have h2p_ge : (2 : ℤ) ≤ (2 : ℤ) ^ p := by
          calc (2 : ℤ) = (2 : ℤ) ^ 1 := by ring
            _ ≤ (2 : ℤ) ^ p :=
                pow_le_pow_right₀ (by norm_num) (F.p_pos hp_F)
        linarith
      have h_odd_dlo : F''.IsOdd (Dyadic.ofIntZpow lo e'') := by
        rw [ParityFormat.isOdd_iff_odd_at_canonical_mixed_subnormal
          hp_F hp_ne_1 hexp_F h_lo_ne h_log_lo']
        rcases (abs_eq h2p_nn).mp h_lop1_sat with hpos | hneg
        · have h_lo_eq : lo = (2 : ℤ) ^ p - 1 := by omega
          rw [h_lo_eq]; obtain ⟨m, hm⟩ := h_even2p; exact ⟨m - 1, by linarith⟩
        · have h_lo_eq : lo = -((2 : ℤ) ^ p) - 1 := by omega
          rw [h_lo_eq]; obtain ⟨m, hm⟩ := h_even2p; exact ⟨-m - 1, by linarith⟩
      have h_dhi_real_e'' : (Dyadic.ofIntZpow (lo + 1) e'' : ℝ) =
          ((lo + 1 : ℤ) : ℝ) * (2 : ℝ) ^ e'' := Dyadic.coe_ofIntZpow _ _
      have h_lop1_ne : lo + 1 ≠ 0 := by
        intro h_zero
        rw [h_zero] at h_lop1_sat
        simp at h_lop1_sat
        have : (0 : ℤ) < (2 : ℤ) ^ p := by positivity
        omega
      have h_dhi_ne : (Dyadic.ofIntZpow (lo + 1) e'' : ℝ) ≠ 0 := by
        rw [h_dhi_real_e'']
        exact mul_ne_zero (Int.cast_ne_zero.mpr h_lop1_ne)
          (ne_of_gt (zpow_pos (by norm_num) _))
      have h_log_2p : Int.log 2 (|lo + 1| : ℝ) = (p : ℤ) := by
        have h_bridge : (|lo + 1| : ℝ) = ((|lo + 1| : ℤ) : ℝ) := by
          push_cast; rfl
        rw [h_bridge, h_lop1_sat]
        have h_cast : (((2 : ℤ) ^ p : ℤ) : ℝ) =
            (2 : ℝ) ^ (p : ℤ) := by
          rw [zpow_natCast]; push_cast; rfl
        rw [h_cast]
        exact Int.log_zpow (by norm_num : 1 < 2) _
      have h_log_dhi : Int.log 2 |(Dyadic.ofIntZpow (lo + 1) e'' : ℝ)| =
          (p : ℤ) + e'' := by
        rw [h_dhi_real_e'', ParityFormat.log_abs_mul_zpow h_lop1_ne e'']
        have h_cast_eq : |((lo + 1 : ℤ) : ℝ)| = (|lo + 1| : ℝ) := by
          push_cast; rfl
        rw [h_cast_eq, h_log_2p]
      have h_log_y_ge : (p : ℤ) ≤
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
    have h_even2p : Even ((2 : ℤ) ^ p) := by
      refine ⟨(2 : ℤ) ^ (p - 1), ?_⟩
      have := Dyadic.two_pow_succ_pred (F.p_pos hp_F)
      linarith
    have h_lo_neg : lo = -((2 : ℤ) ^ p) := by
      rcases (abs_eq h2p_nn).mp h_lo_sat with hpos | hneg
      · exfalso
        rw [hpos] at h_lop1_le
        have h_abs : |(2 : ℤ) ^ p + 1| =
            (2 : ℤ) ^ p + 1 := by
          apply abs_of_pos; positivity
        linarith
      · exact hneg
    have h_lop1_lt : |lo + 1| < (2 : ℤ) ^ p := by
      rw [h_lo_neg]
      have h_pos_inner : (0 : ℤ) < (2 : ℤ) ^ p - 1 := by
        have h2le : (2 : ℤ) ≤ (2 : ℤ) ^ p := by
          calc (2 : ℤ) = (2 : ℤ) ^ 1 := by ring
            _ ≤ (2 : ℤ) ^ p :=
                pow_le_pow_right₀ (by norm_num) (F.p_pos hp_F)
        linarith
      have h_rw : -((2 : ℤ) ^ p) + 1 =
          -((2 : ℤ) ^ p - 1) := by ring
      rw [h_rw, abs_neg, abs_of_pos h_pos_inner]; linarith
    have h_log_lop1' := log_lt_p_of_abs_lt_two_pow (F.p_pos hp_F) h_lop1_lt
    have h_lop1_ne : lo + 1 ≠ 0 := by
      rw [h_lo_neg]
      have : (2 : ℤ) ^ p ≥ 2 := by
        calc (2 : ℤ) ^ p ≥ (2 : ℤ) ^ 1 :=
            pow_le_pow_right₀ (by norm_num) (F.p_pos hp_F)
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
      have : (2 : ℤ) ^ p ≥ 2 := by
        calc (2 : ℤ) ^ p ≥ (2 : ℤ) ^ 1 :=
            pow_le_pow_right₀ (by norm_num) (F.p_pos hp_F)
          _ = 2 := by ring
      omega
    have h_dlo_ne : (Dyadic.ofIntZpow lo e'' : ℝ) ≠ 0 := by
      rw [h_dlo_real_e'']
      exact mul_ne_zero (Int.cast_ne_zero.mpr h_lo_ne)
        (ne_of_gt (zpow_pos (by norm_num) _))
    have h_log_2p : Int.log 2 (|lo| : ℝ) = (p : ℤ) := by
      have h_bridge : (|lo| : ℝ) = ((|lo| : ℤ) : ℝ) := by push_cast; rfl
      rw [h_bridge, h_lo_sat]
      have h_cast : (((2 : ℤ) ^ p : ℤ) : ℝ) =
          (2 : ℝ) ^ (p : ℤ) := by
        rw [zpow_natCast]; push_cast; rfl
      rw [h_cast]
      exact Int.log_zpow (by norm_num : 1 < 2) _
    have h_log_dlo : Int.log 2 |(Dyadic.ofIntZpow lo e'' : ℝ)| =
        (p : ℤ) + e'' := by
      rw [h_dlo_real_e'', ParityFormat.log_abs_mul_zpow h_lo_ne e'']
      have h_cast_eq : |(lo : ℝ)| = (|lo| : ℝ) := by rfl
      rw [h_cast_eq, h_log_2p]
    have h_log_y_ge : (p : ℤ) ≤
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

/-- With a one-bit significand both neighbours' coefficients are at most `2` in
magnitude, so parity has to be read off the exponent. -/
private theorem abs_le_two_of_p_one {F : FiniteFormat}
    (hp_F : F.p = ((1 : ℕ) : Prec)) (x : ℝ) :
    |⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋| ≤ 2
      ∧ |⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ + 1| ≤ 2 := by
  have h_s_lt : |x * (2 : ℝ) ^ (-F.canonicalExp x)| < (2 : ℝ) ^ (1 : ℕ) :=
    floor_mantissa_lt hp_F
  have h_s_lt_2 : |x * (2 : ℝ) ^ (-F.canonicalExp x)| < ((2 : ℤ) : ℝ) := by
    rw [show ((2 : ℤ) : ℝ) = (2 : ℝ) ^ (1 : ℕ) by norm_num]; exact h_s_lt
  exact ⟨abs_floor_le_of_abs_lt h_s_lt_2,
    abs_floor_add_one_le_of_abs_lt (p := 1) h_s_lt⟩

/-- Precision `1`, minimum quantum `e''`, `x` **normal**. With a one-bit
significand the coefficients are `±1` or `±2`, so parity is read off the
exponent rather than the significand. -/
private theorem alternate_normal_p1 {F : FiniteFormat} (h : ¬ F.IsUndefined .toOdd)
    {x : ℝ} {e'' : ℤ} (hp_F : F.p = ((1 : ℕ) : Prec))
    (hexp_F : F.exp = (e'' : QExp)) (hx_ne : x ≠ 0)
    (h_regime : e'' < Int.log 2 |x| + 1 - ((1 : ℕ) : ℤ))
    (h_lo_ne_s : (⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ : ℝ)
      ≠ x * (2 : ℝ) ^ (-F.canonicalExp x)) :
    Alternate F h x := by
  unfold Alternate
  obtain ⟨h_lo_hi_int, h_lop1_hi_int⟩ := abs_le_two_of_p_one hp_F x
  set e := F.canonicalExp x with h_e_def
  set s := x * (2 : ℝ) ^ (-e) with h_s_def
  set lo : ℤ := ⌊s⌋ with h_lo_def
  set dlo : Dyadic := Dyadic.ofIntZpow lo e with h_dlo_def
  set dhi : Dyadic := Dyadic.ofIntZpow (lo + 1) e with h_dhi_def
  set F'' := F.toParityFormatOfToOdd h with hF''_def
  have h_e_ge : e'' ≤ e := F.exp_le_canonicalExp x hexp_F
  have h_e_eq_log : e = Int.log 2 |x| := by
    change F.canonicalExp x = _
    unfold FiniteFormat.canonicalExp
    simp only [hp_F, hexp_F]
    rw [if_neg hx_ne, Nat.cast_one]
    have h_max_eq : max (Int.log 2 |x| + 1 - 1) e'' =
        Int.log 2 |x| + 1 - 1 := by
      apply max_eq_left
      have := h_regime; rw [Nat.cast_one] at this; linarith
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

/-- Precision `1`, minimum quantum `e''`, `x` **subnormal**: the step is `2 ^ e''`
and the coefficients are `±1`, `±2`. -/
private theorem alternate_subnormal_p1 {F : FiniteFormat} (h : ¬ F.IsUndefined .toOdd)
    {x : ℝ} {e'' : ℤ} (hp_F : F.p = ((1 : ℕ) : Prec))
    (hexp_F : F.exp = (e'' : QExp)) (hx_ne : x ≠ 0)
    (h_regime : Int.log 2 |x| + 1 - ((1 : ℕ) : ℤ) ≤ e'') :
    Alternate F h x := by
  unfold Alternate
  obtain ⟨h_lo_hi_int, h_lop1_hi_int⟩ := abs_le_two_of_p_one hp_F x
  set e := F.canonicalExp x with h_e_def
  set s := x * (2 : ℝ) ^ (-e) with h_s_def
  set lo : ℤ := ⌊s⌋ with h_lo_def
  set dlo : Dyadic := Dyadic.ofIntZpow lo e with h_dlo_def
  set dhi : Dyadic := Dyadic.ofIntZpow (lo + 1) e with h_dhi_def
  set F'' := F.toParityFormatOfToOdd h with hF''_def
  have h_e_eq : e = e'' := canonicalExp_subnormal hp_F hexp_F hx_ne h_regime
  have h_dlo_at_e'' : dlo = Dyadic.ofIntZpow lo e'' := by rw [h_dlo_def, h_e_eq]
  have h_dhi_at_e'' : dhi = Dyadic.ofIntZpow (lo + 1) e'' := by
    rw [h_dhi_def, h_e_eq]
  rw [h_dhi_at_e'', h_dlo_at_e'']
  exact ⟨ParityFormat.alternating_parity_mixed_subnormal_p1_iff hp_F hexp_F
           h_lo_hi_int h_lop1_hi_int,
         ParityFormat.alternating_isEven_mixed_subnormal_p1 hp_F hexp_F
           h_lo_hi_int h_lop1_hi_int⟩

/-- No minimum quantum (`exp = ⊥`) and precision `p ≠ 1`: every value is normal,
so both coefficients fill the `p`-bit range `[2^(p−1), 2^p]`. -/
private theorem alternate_expBot {F : FiniteFormat} (h : ¬ F.IsUndefined .toOdd)
    {x : ℝ} {p : ℕ} (hp_F : F.p = (p : Prec)) (hexp_F : F.exp = ⊥) (hx_ne : x ≠ 0)
    (h_lo_ne_s : (⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ : ℝ)
      ≠ x * (2 : ℝ) ^ (-F.canonicalExp x)) :
    Alternate F h x := by
  unfold Alternate
  set e := F.canonicalExp x with h_e_def
  set s := x * (2 : ℝ) ^ (-e) with h_s_def
  set lo : ℤ := ⌊s⌋ with h_lo_def
  set dlo : Dyadic := Dyadic.ofIntZpow lo e with h_dlo_def
  set dhi : Dyadic := Dyadic.ofIntZpow (lo + 1) e with h_dhi_def
  set F'' := F.toParityFormatOfToOdd h with hF''_def
  have h_floor_le_s : (lo : ℝ) ≤ s := Int.floor_le _
  have hp_ne_1 : F.p ≠ ((1 : ℕ) : Prec) := fun h_eq =>
    h ⟨h_eq, hexp_F, Or.inl rfl⟩
  have h_s_lt_p : |x * (2 : ℝ) ^ (-e)| < (2 : ℝ) ^ p :=
    floor_mantissa_lt hp_F
  have h_lo_hi : |lo| ≤ (2 : ℤ) ^ p := by
    apply abs_floor_le_of_abs_lt; push_cast; exact h_s_lt_p
  have h_lop1_hi : |lo + 1| ≤ (2 : ℤ) ^ p :=
    abs_floor_add_one_le_of_abs_lt h_s_lt_p
  have h_e_eq_log : e = Int.log 2 |x| + 1 - (p : ℤ) :=
    canonicalExp_closed hp_F hx_ne (by rw [hexp_F]; exact bot_le)
  have h_s_lo_real : ((2 : ℤ) ^ (p - 1) : ℝ) ≤
      |x * (2 : ℝ) ^ (-e)| :=
    two_pow_pred_le_scaled (p := p) (F.p_pos hp_F) hx_ne h_e_eq_log
  have h_lo_lo : (2 : ℤ) ^ (p - 1) ≤ |lo| :=
    abs_floor_ge_two_pow_pred (p := p) h_s_lo_real
  have h_lop1_lo : (2 : ℤ) ^ (p - 1) ≤ |lo + 1| :=
    abs_floor_add_one_ge_two_pow_pred (p := p) h_s_lo_real h_lo_ne_s
  rw [h_dhi_def, h_dlo_def]
  exact ⟨ParityFormat.alternating_parity_floating_iff hp_F hp_ne_1 hexp_F
           h_lo_lo h_lo_hi h_lop1_lo h_lop1_hi,
         ParityFormat.alternating_isEven_floating hp_F hp_ne_1 hexp_F
           h_lo_lo h_lo_hi h_lop1_lo h_lop1_hi⟩

/-- Unrestricted precision and minimum quantum `e''` — a fixed-point format. The
step is `2 ^ e''` everywhere, so the coefficients are consecutive integers. -/
private theorem alternate_fixedPoint {F : FiniteFormat} (h : ¬ F.IsUndefined .toOdd)
    {x : ℝ} {e'' : ℤ} (hp_F : F.p = ⊤) (hexp_F : F.exp = (e'' : QExp)) :
    Alternate F h x := by
  unfold Alternate
  set e := F.canonicalExp x with h_e_def
  set lo : ℤ := ⌊x * (2 : ℝ) ^ (-e)⌋ with h_lo_def
  set dlo : Dyadic := Dyadic.ofIntZpow lo e with h_dlo_def
  set dhi : Dyadic := Dyadic.ofIntZpow (lo + 1) e with h_dhi_def
  have h_e_eq : e = e'' := canonicalExp_pTop hp_F hexp_F x
  rw [show dhi = Dyadic.ofIntZpow (lo + 1) e'' by rw [h_dhi_def, h_e_eq],
    show dlo = Dyadic.ofIntZpow lo e'' by rw [h_dlo_def, h_e_eq]]
  exact ⟨ParityFormat.alternating_parity_fixedpoint_iff hp_F hexp_F,
         ParityFormat.alternating_isEven_fixedpoint hp_F hexp_F⟩

/-- **Adjacent grid points alternate in parity.** For `dlo = ⌊s⌋·2^e` and
`dhi = (⌊s⌋+1)·2^e` at the canonical exponent, `dhi` is odd exactly when `dlo`
is not, and evenness alternates with it. Flocq `DN_UP_parity_generic_pos`.

The six cases of `(F.p, F.exp) × regime`, each discharged by the leaf lemma
above of the same name. -/
theorem neighbors_alternate {F : FiniteFormat} (x : ℝ)
    (h : ¬ F.IsUndefined .toOdd)
    (hx_ne : x ≠ 0)
    (h_lo_ne_s :
      (⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ : ℝ) ≠ x * (2 : ℝ) ^ (-F.canonicalExp x)) :
    ((F.toParityFormatOfToOdd h).IsOdd
        (Dyadic.ofIntZpow (⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ + 1) (F.canonicalExp x))
      ↔ ¬ (F.toParityFormatOfToOdd h).IsOdd
        (Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ (F.canonicalExp x)))
    ∧ (¬ (F.toParityFormatOfToOdd h).IsEven
        (Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ (F.canonicalExp x))
      → (F.toParityFormatOfToOdd h).IsEven
        (Dyadic.ofIntZpow (⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ + 1) (F.canonicalExp x))) := by
  cases hp_F : F.p using ENat.recTopCoe with
  | top =>
    cases hexp_F : F.exp using QExp.recBotCoe with
    | bot => exact absurd hp_F (F.finite.elim id (fun hh => absurd hexp_F hh))
    | coe e'' => exact alternate_fixedPoint h hp_F hexp_F
  | coe p =>
    cases hexp_F : F.exp using QExp.recBotCoe with
    | bot => exact alternate_expBot h hp_F hexp_F hx_ne h_lo_ne_s
    | coe e'' =>
      by_cases hp_eq_1 : p = (1 : ℕ)
      · subst hp_eq_1
        by_cases h_regime : Int.log 2 |x| + 1 - ((1 : ℕ) : ℤ) ≤ e''
        · exact alternate_subnormal_p1 h hp_F hexp_F hx_ne h_regime
        · exact alternate_normal_p1 h hp_F hexp_F hx_ne (by omega) h_lo_ne_s
      · have hp_ne_1 : F.p ≠ ((1 : ℕ) : Prec) := by
          rw [hp_F]; intro h_eq; apply hp_eq_1; exact_mod_cast h_eq
        by_cases h_regime : Int.log 2 |x| + 1 - (p : ℤ) ≤ e''
        · exact alternate_subnormal_pne1 h hp_F hexp_F hp_ne_1 hx_ne h_regime
        · exact alternate_normal_pne1 h hp_F hexp_F hp_ne_1 hx_ne (by omega) h_lo_ne_s

/-- The `IsOdd` half. -/
theorem toOdd_neighbors_alternate {F : FiniteFormat} (x : ℝ)
    (h : ¬ F.IsUndefined .toOdd)
    (hx_ne : x ≠ 0)
    (h_lo_ne_s :
      (⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ : ℝ) ≠ x * (2 : ℝ) ^ (-F.canonicalExp x)) :
    (F.toParityFormatOfToOdd h).IsOdd
        (Dyadic.ofIntZpow (⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ + 1) (F.canonicalExp x))
      ↔ ¬ (F.toParityFormatOfToOdd h).IsOdd
        (Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ (F.canonicalExp x)) :=
  (neighbors_alternate x h hx_ne h_lo_ne_s).1

/-- Same dispatch: the two parity-format promotions differ only in their proof
term, hence are the same value. -/
theorem nearest_toEven_neighbors_alternate {F : FiniteFormat} (x : ℝ)
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
        (Dyadic.ofIntZpow (⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ + 1) (F.canonicalExp x))) :=
  neighbors_alternate x (fun ⟨h1, h2, _⟩ => h ⟨h1, h2, Or.inr rfl⟩) hx_ne h_lo_ne_s

end Mpfx
