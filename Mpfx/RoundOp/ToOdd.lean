import Mpfx.RoundOp.Defs
import Mpfx.RoundOp.Directed

/-!
# Constructive rounding: `toOdd` obligations

Soundness and uniqueness for the `toOdd` rounding mode.
-/

namespace Mpfx

attribute [local instance] Classical.propDecidable

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
        cases hp_F : F.p with
        | top =>
          cases hexp_F : F.exp with
          | bot =>
            exfalso
            rcases F.finite with hf | hf
            · exact hf hp_F
            · exact hf hexp_F
          | coe e' =>
            -- F.p = ⊤, F.exp = (e' : ℤ). canonicalExp x = e'.
            have h_e_eq : e = e' := by
              change F.canonicalExp x = _
              unfold FiniteFormat.canonicalExp
              simp [hp_F, hexp_F]
            -- Apply alternating_parity_fixedpoint to F''. Then transfer to F'.
            have h_dlo_def_e' : dlo = Dyadic.ofIntZpow lo e' := by
              rw [h_dlo_def, h_e_eq]
            have h_dhi_def_e' : dhi = Dyadic.ofIntZpow (lo + 1) e' := by
              rw [h_dhi_def, h_e_eq]
            rw [h_dhi_def_e']
            have h_F''_top : F''.p = ⊤ := hp_F
            have h_F''_exp : F''.exp = (e' : WithBot ℤ) := hexp_F
            have h_F''_odd_dhi : F''.IsOdd (Dyadic.ofIntZpow (lo + 1) e') := by
              apply ParityFormat.alternating_parity_fixedpoint h_F''_top h_F''_exp
              rw [← h_dlo_def_e']; exact hodd
            -- Bridge to F'.
            -- Bridge F'' to F'. Both ParityFormats have toFormat with
            -- same (p, exp) — F.unbounded inherits these from F.
            exact (show F''.IsOdd (Dyadic.ofIntZpow (lo + 1) e') =
              F'.IsOdd (Dyadic.ofIntZpow (lo + 1) e') from rfl).mp h_F''_odd_dhi
        | coe p =>
          cases hexp_F : F.exp with
          | bot =>
            have hp_eq : F''.p = ((p : ℕ+) : WithTop ℕ+) := hp_F
            have hexp_eq : F''.exp = ⊥ := hexp_F
            have hp_ne_1 : F''.p ≠ ((1 : ℕ+) : WithTop ℕ+) := by
              change F.p ≠ ((1 : ℕ+) : WithTop ℕ+)
              intro h_eq
              apply h
              exact ⟨h_eq, hexp_F, Or.inl rfl⟩
            have h_e_eq_log : e = Int.log 2 |x| + 1 - (p : ℤ) := by
              change F.canonicalExp x = _
              unfold FiniteFormat.canonicalExp
              simp [hp_F, hexp_F, hx]
            have h_s_lo_real : ((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) ≤ |s| :=
              two_pow_pred_le_scaled (p := p) hx h_e_eq_log
            -- |lo| ≥ 2^(p-1).
            have h_lo_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo| :=
              abs_floor_ge_two_pow_pred (p := p) h_s_lo_real
            -- |lo + 1| ≥ 2^(p-1) (non-exact case).
            have h_lop1_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo + 1| := by
              by_cases hs_nn : 0 ≤ s
              · have h_lo_nn : 0 ≤ lo := Int.floor_nonneg.mpr hs_nn
                rw [abs_of_nonneg (by linarith : (0 : ℤ) ≤ lo + 1)]
                linarith [h_lo_lo, abs_of_nonneg h_lo_nn]
              · have hs_neg : s < 0 := not_le.mp hs_nn
                have h_lo_le_r : (lo : ℝ) ≤ -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) := by
                  have h_s_le_r : s ≤ -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) := by
                    have h_abs_eq : |s| = -s := abs_of_neg hs_neg
                    linarith [h_s_lo_real]
                  have h_floor_le : (lo : ℝ) ≤ s := Int.floor_le _
                  linarith
                have h_lo_le : lo ≤ -((2 : ℤ) ^ ((p : ℕ) - 1)) := by
                  exact_mod_cast h_lo_le_r
                have h_lo_ne : lo ≠ -((2 : ℤ) ^ ((p : ℕ) - 1)) := by
                  intro h_lo_eq
                  apply hs
                  have h_floor_le : (lo : ℝ) ≤ s := Int.floor_le _
                  have h_s_le_lo : s ≤ -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) := by
                    have h_abs_eq : |s| = -s := abs_of_neg hs_neg
                    linarith [h_s_lo_real]
                  have h_lo_r : (lo : ℝ) = -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) := by
                    exact_mod_cast h_lo_eq
                  linarith
                have h_lo_lt : lo < -((2 : ℤ) ^ ((p : ℕ) - 1)) :=
                  lt_of_le_of_ne h_lo_le h_lo_ne
                have h_lop1_le : lo + 1 ≤ -((2 : ℤ) ^ ((p : ℕ) - 1)) := by linarith
                have hp_ge_2 : 2 ≤ (p : ℕ) := by
                  by_contra h_neg
                  push Not at h_neg
                  have hp_pos : 1 ≤ (p : ℕ) := p.pos
                  have hp_one : (p : ℕ) = 1 := by omega
                  have hp_subt : p = 1 := Subtype.ext hp_one
                  apply hp_ne_1
                  change F.p = _
                  rw [hp_F, hp_subt]
                have h_2p1_ge_2 : 2 ≤ (2 : ℤ) ^ ((p : ℕ) - 1) := by
                  calc (2 : ℤ) = (2 : ℤ) ^ 1 := by ring
                    _ ≤ (2 : ℤ) ^ ((p : ℕ) - 1) :=
                        pow_le_pow_right₀ (by norm_num) (by omega)
                have h_lop1_neg : lo + 1 < 0 := by linarith
                rw [abs_of_neg h_lop1_neg]; linarith
            exact ParityFormat.alternating_parity_floating hp_eq hp_ne_1 hexp_eq
              h_lo_lo (h_lo_bound hp_F) h_lop1_lo (h_lop1_bound hp_F) hodd
          | coe e' =>
            -- F.p = (p:ℕ+), F.exp = (e':ℤ). Mixed case.
            by_cases hp_eq_1 : p = (1 : ℕ+)
            · -- p = 1: exponent-index parity branch.
              subst hp_eq_1
              have hp_eq : F''.p = ((1 : ℕ+) : WithTop ℕ+) := hp_F
              have hexp_eq : F''.exp = (e' : WithBot ℤ) := hexp_F
              have h_e_ge : e' ≤ e := F.exp_le_canonicalExp x hexp_F
              have h_s_lt : |x * (2 : ℝ) ^ (-e)| < (2 : ℝ) ^ ((1 : ℕ+) : ℕ) :=
                floor_mantissa_lt hp_F
              have h_s_lt_2 : |x * (2 : ℝ) ^ (-e)| < ((2 : ℤ) : ℝ) := by
                have h_cast : ((2 : ℤ) : ℝ) = (2 : ℝ) ^ ((1 : ℕ+) : ℕ) := by
                  change (2 : ℝ) = (2 : ℝ) ^ (1 : ℕ); ring
                rw [h_cast]; exact h_s_lt
              have h_lo_hi_int : |lo| ≤ 2 := abs_floor_le_of_abs_lt h_s_lt_2
              have h_lop1_hi_int : |lo + 1| ≤ 2 := by
                have := abs_floor_add_one_le_of_abs_lt (p := 1) h_s_lt
                exact this
              -- Show dlo, dhi at canonical e.
              have h_dlo_at : dlo = Dyadic.ofIntZpow lo e := h_dlo_def
              have h_dhi_at : dhi = Dyadic.ofIntZpow (lo + 1) e := h_dhi_def
              by_cases h_regime : Int.log 2 |x| + 1 - ((1 : ℕ+) : ℤ) ≤ e'
              · -- Subnormal: e = e'.
                have h_e_eq : e = e' := by
                  change F.canonicalExp x = e'
                  unfold FiniteFormat.canonicalExp
                  simp only [hp_F, hexp_F]
                  rw [if_neg hx]
                  exact max_eq_right h_regime
                rw [h_dlo_at, h_e_eq] at hodd
                rw [h_dhi_at, h_e_eq]
                exact ParityFormat.alternating_parity_mixed_subnormal_p1
                  hp_eq hexp_eq h_lo_hi_int h_lop1_hi_int hodd
              · -- Normal: e = log|x|+1-1 = log|x|. Need |lo|, |lo+1| ≥ 1.
                push Not at h_regime
                have h_pcast : ((1 : ℕ+) : ℤ) = 1 := rfl
                have h_e_eq_log : e = Int.log 2 |x| := by
                  change F.canonicalExp x = _
                  unfold FiniteFormat.canonicalExp
                  simp only [hp_F, hexp_F]
                  rw [if_neg hx]
                  rw [show (((1 : ℕ+) : ℕ) : ℤ) = 1 from rfl]
                  have h_max_eq : max (Int.log 2 |x| + 1 - 1) e' =
                      Int.log 2 |x| + 1 - 1 := by
                    apply max_eq_left
                    have := h_regime; rw [h_pcast] at this; linarith
                  rw [h_max_eq]; ring
                -- |s| ≥ 1 from |x| ≥ 2^(log|x|) = 2^e.
                have h_x_ge : (2 : ℝ) ^ (Int.log 2 |x|) ≤ |x| :=
                  Int.zpow_log_le_self (b := 2) (by norm_num : (1 : ℕ) < 2)
                    (abs_pos.mpr hx)
                have h_2neg_pos : (0 : ℝ) < (2 : ℝ) ^ (-e) :=
                  zpow_pos (by norm_num) _
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
                -- |lo| ≥ 1.
                have h_lo_lo_int : 1 ≤ |lo| := by
                  by_cases hs_nn : 0 ≤ x * (2 : ℝ) ^ (-e)
                  · have h_s_ge : 1 ≤ x * (2 : ℝ) ^ (-e) := by
                      have h_abs_eq : |x * (2 : ℝ) ^ (-e)| = x * (2 : ℝ) ^ (-e) :=
                        abs_of_nonneg hs_nn
                      linarith [h_abs_s]
                    have h_lo_ge_1 : 1 ≤ lo := by
                      apply Int.le_floor.mpr
                      push_cast; exact h_s_ge
                    have h_lo_nn : 0 ≤ lo := by linarith
                    rw [abs_of_nonneg h_lo_nn]; exact h_lo_ge_1
                  · push Not at hs_nn
                    have h_s_le : x * (2 : ℝ) ^ (-e) ≤ -1 := by
                      have h_abs_eq : |x * (2 : ℝ) ^ (-e)| =
                          -(x * (2 : ℝ) ^ (-e)) := abs_of_neg hs_nn
                      linarith [h_abs_s]
                    have h_floor_le : (lo : ℝ) ≤ x * (2 : ℝ) ^ (-e) :=
                      Int.floor_le _
                    have h_lo_le : (lo : ℝ) ≤ -1 := le_trans h_floor_le h_s_le
                    have h_lo_le_int : lo ≤ -1 := by exact_mod_cast h_lo_le
                    have h_lo_neg : lo < 0 := by linarith
                    rw [abs_of_neg h_lo_neg]; linarith
                -- |lo+1| ≥ 1: lo ≠ -1.
                -- lo = -1 ⟹ s = -1 (boundary) since lo = ⌊s⌋ and |s| ≥ 1 in normal.
                --   x · 2^(-e) = -1, so x = -2^e = -2^(log|x|). Then dlo = x.
                --   Contradicts hs.
                have h_lo_ne_neg1 : lo ≠ -1 := by
                  intro h_eq
                  have h_lo_int : ⌊s⌋ = -1 := h_eq
                  have h_floor_le : (-1 : ℝ) ≤ s := by
                    have h_fl := Int.floor_le s
                    rw [h_lo_int] at h_fl; push_cast at h_fl; exact h_fl
                  have h_lt_succ : s < 0 := by
                    have h_lt := Int.lt_floor_add_one s
                    rw [h_lo_int] at h_lt; push_cast at h_lt; linarith
                  have h_s_le_neg1 : s ≤ -1 := by
                    have h_abs_eq : |s| = -s := abs_of_neg (by linarith : s < 0)
                    have h_abs_ge : 1 ≤ |s| := h_abs_s
                    linarith
                  have h_s_eq : s = -1 := le_antisymm h_s_le_neg1 h_floor_le
                  apply hs
                  rw [h_s_eq]
                  show (lo : ℝ) = -1
                  rw [h_eq]; push_cast; ring
                -- |lo+1| ≥ 1: from lo ∈ {-1 excluded, other values}.
                have h_lop1_lo_int : 1 ≤ |lo + 1| := by
                  have h_lop1_ne : lo + 1 ≠ 0 := by
                    intro h0; apply h_lo_ne_neg1; omega
                  exact Int.one_le_abs h_lop1_ne
                rw [h_dlo_at] at hodd
                rw [h_dhi_at]
                exact ParityFormat.alternating_parity_mixed_normal_p1
                  hp_eq hexp_eq h_e_ge h_lo_lo_int h_lo_hi_int
                  h_lop1_lo_int h_lop1_hi_int hodd
            · -- p ≠ 1.
              have hp_eq : F''.p = ((p : ℕ+) : WithTop ℕ+) := hp_F
              have hexp_eq : F''.exp = (e' : WithBot ℤ) := hexp_F
              have hp_ne_1 : F''.p ≠ ((1 : ℕ+) : WithTop ℕ+) := by
                change F.p ≠ _
                rw [hp_F]
                intro h
                apply hp_eq_1
                exact_mod_cast h
              by_cases h_regime : Int.log 2 |x| + 1 - ((p : ℕ+) : ℤ) ≤ e'
              · -- Subnormal regime: e = e'.
                have h_e_eq : e = e' := by
                  change F.canonicalExp x = e'
                  unfold FiniteFormat.canonicalExp
                  simp only [hp_F, hexp_F]
                  rw [if_neg hx]
                  exact max_eq_right h_regime
                -- |x| < 2^(e' + p) from h_regime.
                have h_x_lt : |x| < (2 : ℝ) ^ (e' + (p : ℤ)) := by
                  have h_log_le : Int.log 2 |x| ≤ e' + (p : ℤ) - 1 := by
                    have : Int.log 2 |x| + 1 - ((p : ℕ+) : ℤ) ≤ e' := h_regime
                    have h_pcast : ((p : ℕ+) : ℤ) = (p : ℤ) := rfl
                    linarith
                  have h_lt := Int.lt_zpow_succ_log_self
                    (by norm_num : (1 : ℕ) < 2) |x|
                  have : Int.log 2 |x| + 1 ≤ e' + (p : ℤ) := by linarith
                  exact lt_of_lt_of_le h_lt
                    (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) this)
                -- |s| = |x| * 2^(-e') < 2^p strict.
                have h_s_lt : |x * (2 : ℝ) ^ (-e)| < (2 : ℝ) ^ ((p : ℕ+) : ℕ) := by
                  rw [h_e_eq]
                  have h_abs : |x * (2 : ℝ) ^ (-e')| = |x| * (2 : ℝ) ^ (-e') := by
                    rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)]
                  rw [h_abs]
                  have h_2neg_pos : (0 : ℝ) < (2 : ℝ) ^ (-e') := zpow_pos (by norm_num) _
                  have h_eq_split : (2 : ℝ) ^ (e' + (p : ℤ)) =
                      (2 : ℝ) ^ e' * (2 : ℝ) ^ ((p : ℕ+) : ℕ) := by
                    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
                    have h_pcast : ((p : ℕ+) : ℤ) = (((p : ℕ+) : ℕ) : ℤ) := rfl
                    rw [h_pcast, zpow_natCast]
                  have h_x2neg : |x| * (2 : ℝ) ^ (-e') <
                      (2 : ℝ) ^ (e' + (p : ℤ)) * (2 : ℝ) ^ (-e') :=
                    mul_lt_mul_of_pos_right h_x_lt h_2neg_pos
                  rw [h_eq_split] at h_x2neg
                  have h_cancel : (2 : ℝ) ^ e' * (2 : ℝ) ^ ((p : ℕ+) : ℕ) *
                      (2 : ℝ) ^ (-e') = (2 : ℝ) ^ ((p : ℕ+) : ℕ) := by
                    rw [mul_right_comm, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
                        add_neg_cancel, zpow_zero, one_mul]
                  rw [h_cancel] at h_x2neg
                  exact h_x2neg
                -- |lo| ≤ 2^p, |lo+1| ≤ 2^p.
                have h_lo_le : |lo| ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by
                  apply abs_floor_le_of_abs_lt
                  push_cast; exact h_s_lt
                have h_lop1_le : |lo + 1| ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) :=
                  abs_floor_add_one_le_of_abs_lt h_s_lt
                    -- Case split: |lo| < 2^p (non-saturation) or |lo| = 2^p.
                rcases lt_or_eq_of_le h_lo_le with h_lo_lt | h_lo_sat
                · -- Non-saturation: also |lo+1| ≤ 2^p but may saturate.
                  rcases lt_or_eq_of_le h_lop1_le with h_lop1_lt | h_lop1_sat
                  · -- Both strict. Apply lemma.
                    have h_log_lo' := log_lt_p_of_abs_lt_two_pow h_lo_lt
                    have h_log_lop1_raw := log_lt_p_of_abs_lt_two_pow h_lop1_lt
                    -- Bridge for lo+1: lemma's `|lo + 1| : ℝ` elaborates as
                    -- `|↑lo + 1|`, but helper gives `|↑(lo + 1)|`.
                    have h_log_lop1' : Int.log 2 |((lo : ℝ) + 1)| + 1 ≤
                        (((p : ℕ+) : ℕ) : ℤ) := by
                      have h_eq : |((lo : ℝ) + 1)| = |((lo + 1 : ℤ) : ℝ)| := by
                        push_cast; rfl
                      rw [h_eq]; exact h_log_lop1_raw
                    have h_dlo_at_e' : dlo = Dyadic.ofIntZpow lo e' := by
                      rw [h_dlo_def, h_e_eq]
                    have h_dhi_at_e' : dhi = Dyadic.ofIntZpow (lo + 1) e' := by
                      rw [h_dhi_def, h_e_eq]
                    rw [h_dhi_at_e']
                    apply ParityFormat.alternating_parity_mixed_subnormal_pne1
                      hp_eq hp_ne_1 hexp_eq h_log_lo' h_log_lop1'
                    rw [← h_dlo_at_e']; exact hodd
                  · -- |lo+1| = 2^p saturation. Must be lo+1 = 2^p (positive
                    -- sat); lo+1 = -2^p would force |lo| = 2^p+1 > 2^p.
                    exfalso
                    have h2p_nn : (0 : ℤ) ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by positivity
                    have h_pos_lop1 : lo + 1 = (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by
                      rcases (abs_eq h2p_nn).mp h_lop1_sat with h | h
                      · exact h
                      · -- lo + 1 = -2^p ⟹ lo = -2^p - 1 ⟹ |lo| ≥ 2^p + 1.
                        exfalso
                        have h_lo_eq : lo = -((2 : ℤ) ^ ((p : ℕ+) : ℕ)) - 1 := by omega
                        have h_abs_lo : |lo| = (2 : ℤ) ^ ((p : ℕ+) : ℕ) + 1 := by
                          rw [h_lo_eq]
                          rw [show -((2 : ℤ) ^ ((p : ℕ+) : ℕ)) - 1 =
                              -((2 : ℤ) ^ ((p : ℕ+) : ℕ) + 1) by ring]
                          rw [abs_neg]
                          exact abs_of_nonneg (by linarith)
                        linarith [h_lo_lt, h_abs_lo]
                    -- lo = 2^p - 1, dlo = (2^p - 1) · 2^e' is Odd.
                    have h_lo_eq : lo = (2 : ℤ) ^ ((p : ℕ+) : ℕ) - 1 := by omega
                    -- Show F''.IsOdd dlo via mixed_subnormal characterization.
                    -- |lo| = 2^p - 1 < 2^p (since 2^p > 0).
                    have h_lo_pos : (0 : ℤ) < (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by positivity
                    have h_abs_lo_eq : |lo| = (2 : ℤ) ^ ((p : ℕ+) : ℕ) - 1 := by
                      rw [h_lo_eq]; exact abs_of_nonneg (by linarith)
                    have h_lo_ne : lo ≠ 0 := by
                      rw [h_lo_eq]
                      have : (2 : ℤ) ^ ((p : ℕ+) : ℕ) > 1 := by
                        calc (2 : ℤ) ^ ((p : ℕ+) : ℕ) ≥ 2 := by
                              calc (2 : ℤ) ^ ((p : ℕ+) : ℕ) ≥ (2 : ℤ) ^ 1 :=
                                  pow_le_pow_right₀ (by norm_num) (p : ℕ+).pos
                                _ = 2 := by ring
                          _ > 1 := by norm_num
                      omega
                    have h_log_lo' := log_lt_p_of_abs_lt_two_pow
                      (k := lo) (by rw [h_abs_lo_eq]; linarith)
                    have h_dlo_at_e' : dlo = Dyadic.ofIntZpow lo e' := by
                      rw [h_dlo_def, h_e_eq]
                    apply hodd
                    rw [h_dlo_at_e']
                    rw [ParityFormat.isOdd_iff_odd_at_canonical_mixed_subnormal
                        hp_eq hp_ne_1 hexp_eq h_lo_ne h_log_lo']
                    -- Show Odd lo = Odd (2^p - 1).
                    rw [h_lo_eq]
                    have h2p_even : Even ((2 : ℤ) ^ ((p : ℕ+) : ℕ)) := by
                      refine ⟨(2 : ℤ) ^ (((p : ℕ+) : ℕ) - 1), ?_⟩
                      have := Dyadic.two_pow_succ_pred (p : ℕ+).pos
                      linarith
                    have h_neg_odd : Odd ((2 : ℤ) ^ ((p : ℕ+) : ℕ) - 1) := by
                      rcases h2p_even with ⟨m, hm⟩
                      refine ⟨m - 1, ?_⟩
                      linarith
                    exact h_neg_odd
                · -- |lo| = 2^p saturation. Must be lo = -2^p (since lo ≤ s < 2^p).
                  have h2p_nn : (0 : ℤ) ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by positivity
                  have h2p_pos : (0 : ℤ) < (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by positivity
                  -- lo ≤ s < 2^p (real), so lo < 2^p as integers.
                  have h_lo_lt_2p : lo < (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by
                    have h_floor_le : (lo : ℝ) ≤ s := Int.floor_le _
                    have h_s_lt' : s < (2 : ℝ) ^ ((p : ℕ+) : ℕ) := by
                      have := h_s_lt; rw [abs_lt] at this; exact this.2
                    have h_cast : ((2 : ℤ) ^ ((p : ℕ+) : ℕ) : ℝ) =
                        (2 : ℝ) ^ ((p : ℕ+) : ℕ) := by push_cast; rfl
                    have h_lo_lt_r : (lo : ℝ) < ((2 : ℤ) ^ ((p : ℕ+) : ℕ) : ℝ) := by
                      rw [h_cast]; linarith
                    exact_mod_cast h_lo_lt_r
                  have h_lo_neg : lo = -((2 : ℤ) ^ ((p : ℕ+) : ℕ)) := by
                    rcases (abs_eq h2p_nn).mp h_lo_sat with h | h
                    · omega
                    · exact h
                  -- lo + 1 = -2^p + 1, |lo+1| = 2^p - 1 < 2^p.
                  have h_lop1_ne : lo + 1 ≠ 0 := by
                    rw [h_lo_neg]
                    have h_2_le : 2 ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by
                      calc (2 : ℤ) = (2 : ℤ) ^ 1 := by ring
                        _ ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) :=
                            pow_le_pow_right₀ (by norm_num) (p : ℕ+).pos
                    omega
                  have h_abs_lop1 : |lo + 1| = (2 : ℤ) ^ ((p : ℕ+) : ℕ) - 1 := by
                    rw [h_lo_neg]
                    rw [show -((2 : ℤ) ^ ((p : ℕ+) : ℕ)) + 1 =
                          -((2 : ℤ) ^ ((p : ℕ+) : ℕ) - 1) by ring]
                    rw [abs_neg]
                    have h_pos : 0 ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) - 1 := by
                      have : (1 : ℤ) ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) := one_le_pow₀ (by norm_num)
                      linarith
                    exact abs_of_nonneg h_pos
                  have h_log_lop1' := log_lt_p_of_abs_lt_two_pow
                    (k := lo + 1) (by rw [h_abs_lop1]; linarith)
                  have h_dhi_at_e' : dhi = Dyadic.ofIntZpow (lo + 1) e' := by
                    rw [h_dhi_def, h_e_eq]
                  rw [h_dhi_at_e']
                  rw [ParityFormat.isOdd_iff_odd_at_canonical_mixed_subnormal
                      hp_eq hp_ne_1 hexp_eq h_lop1_ne h_log_lop1']
                  -- Show Odd (lo + 1) = Odd (-2^p + 1).
                  rw [h_lo_neg]
                  have h2p_even : Even ((2 : ℤ) ^ ((p : ℕ+) : ℕ)) := by
                    refine ⟨(2 : ℤ) ^ (((p : ℕ+) : ℕ) - 1), ?_⟩
                    have := Dyadic.two_pow_succ_pred (p : ℕ+).pos
                    linarith
                  have h_neg_2p_even : Even (-((2 : ℤ) ^ ((p : ℕ+) : ℕ))) := h2p_even.neg
                  exact h_neg_2p_even.add_one
              · -- Normal regime: e = log|x|+1-p.
                push Not at h_regime
                have h_e_eq_log : e = Int.log 2 |x| + 1 - ((p : ℕ+) : ℤ) := by
                  change F.canonicalExp x = _
                  unfold FiniteFormat.canonicalExp
                  simp only [hp_F, hexp_F]
                  rw [if_neg hx]
                  exact max_eq_left (le_of_lt h_regime)
                have h_s_lo_real : ((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) ≤
                    |x * (2 : ℝ) ^ (-e)| :=
                  two_pow_pred_le_scaled (p := p) hx h_e_eq_log
                have h_lo_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo| :=
                  abs_floor_ge_two_pow_pred (p := p) h_s_lo_real
                -- |lo + 1| ≥ 2^(p-1) (non-exact case).
                have h_lop1_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo + 1| := by
                  by_cases hs_nn : 0 ≤ s
                  · have h_lo_nn : 0 ≤ lo := Int.floor_nonneg.mpr hs_nn
                    rw [abs_of_nonneg (by linarith : (0 : ℤ) ≤ lo + 1)]
                    linarith [h_lo_lo, abs_of_nonneg h_lo_nn]
                  · have hs_neg : s < 0 := not_le.mp hs_nn
                    have h_lo_le_r : (lo : ℝ) ≤ -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) := by
                      have h_s_le_r : s ≤ -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) := by
                        have h_abs_eq : |s| = -s := abs_of_neg hs_neg
                        linarith [h_s_lo_real]
                      have h_floor_le : (lo : ℝ) ≤ s := Int.floor_le _
                      linarith
                    have h_lo_le : lo ≤ -((2 : ℤ) ^ ((p : ℕ) - 1)) := by
                      exact_mod_cast h_lo_le_r
                    have h_lo_ne : lo ≠ -((2 : ℤ) ^ ((p : ℕ) - 1)) := by
                      intro h_lo_eq
                      apply hs
                      have h_floor_le : (lo : ℝ) ≤ s := Int.floor_le _
                      have h_s_le_lo : s ≤ -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) := by
                        have h_abs_eq : |s| = -s := abs_of_neg hs_neg
                        linarith [h_s_lo_real]
                      have h_lo_r : (lo : ℝ) = -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) := by
                        exact_mod_cast h_lo_eq
                      linarith
                    have h_lo_lt : lo < -((2 : ℤ) ^ ((p : ℕ) - 1)) :=
                      lt_of_le_of_ne h_lo_le h_lo_ne
                    have h_lop1_le : lo + 1 ≤ -((2 : ℤ) ^ ((p : ℕ) - 1)) := by linarith
                    have hp_ge_2 : 2 ≤ (p : ℕ) := by
                      by_contra h_neg
                      push Not at h_neg
                      have hp_pos : 1 ≤ (p : ℕ) := p.pos
                      have hp_one : (p : ℕ) = 1 := by omega
                      have hp_subt : p = 1 := Subtype.ext hp_one
                      exact hp_eq_1 hp_subt
                    have h_2p1_ge_2 : 2 ≤ (2 : ℤ) ^ ((p : ℕ) - 1) := by
                      calc (2 : ℤ) = (2 : ℤ) ^ 1 := by ring
                        _ ≤ (2 : ℤ) ^ ((p : ℕ) - 1) :=
                            pow_le_pow_right₀ (by norm_num) (by omega)
                    have h_lop1_neg : lo + 1 < 0 := by linarith
                    rw [abs_of_neg h_lop1_neg]; linarith
                -- |lo| ≤ 2^p, |lo+1| ≤ 2^p from h_lo_bound, h_lop1_bound.
                have h_lo_hi : |lo| ≤ (2 : ℤ) ^ ((p : ℕ) : ℕ) := h_lo_bound hp_F
                have h_lop1_hi : |lo + 1| ≤ (2 : ℤ) ^ ((p : ℕ) : ℕ) := h_lop1_bound hp_F
                -- Mixed-normal log bounds: p ≤ Int.log 2 |dlo| - e' + 1.
                -- |dlo| = |lo| · 2^e ≥ 2^(p-1) · 2^e = 2^(p-1+e) = 2^(log|x|).
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
                -- Helper: compute Int.log 2 (2^n : ℝ) = n for natural n.
                have h_log_lo_lb := log_ge_p_pred_of_two_pow_pred_le (k := lo) h_lo_lo
                have h_log_lop1_lb := log_ge_p_pred_of_two_pow_pred_le (k := lo + 1) h_lop1_lo
                -- Combine: log|dlo| = log|lo| + e ≥ (p-1) + (log|x|+1-p) = log|x|.
                have h_log_lo : ((p : ℕ) : ℤ) ≤
                    Int.log 2 |(dlo : ℝ)| - e' + 1 := by
                  rw [h_log_dlo, h_e_eq_log]
                  have : Int.log 2 |x| - e' ≥ ((p : ℕ) : ℤ) := by linarith
                  linarith [h_log_lo_lb]
                have h_log_hi : ((p : ℕ) : ℤ) ≤
                    Int.log 2 |(dhi : ℝ)| - e' + 1 := by
                  rw [h_log_dhi, h_e_eq_log]
                  have : Int.log 2 |x| - e' ≥ ((p : ℕ) : ℤ) := by linarith
                  linarith [h_log_lop1_lb]
                -- Apply alternating_parity_mixed_normal_pne1.
                apply ParityFormat.alternating_parity_mixed_normal_pne1
                  hp_eq hp_ne_1 hexp_eq h_dlo_ne h_dhi_ne h_log_lo h_log_hi
                  h_dlo_real h_dhi_real h_lo_lo h_lo_hi h_lop1_lo h_lop1_hi
                exact hodd


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
    -- Transfer IsOdd via the F_y → F'' bridge.
    cases hp_F : F.p with
    | top =>
      cases hexp_F : F.exp with
      | bot =>
        exfalso
        rcases F.finite with hf | hf
        · exact hf hp_F
        · exact hf hexp_F
      | coe e'' =>
        -- F.p = ⊤, F.exp = (e'' : ℤ). Apply not_both_isOdd_fixedpoint.
        have h_e_eq : e = e'' := by
          change F.canonicalExp x = _
          unfold FiniteFormat.canonicalExp
          simp [hp_F, hexp_F]
        have h_dlo_def_e'' : dlo = Dyadic.ofIntZpow lo e'' := by
          rw [h_dlo_def, h_e_eq]
        have h_dhi_def_e'' : dhi = Dyadic.ofIntZpow (lo + 1) e'' := by
          rw [h_dhi_def, h_e_eq]
        -- F_y, F_y' both have toFormat = F.unbounded, with .p = ⊤, .exp = e''.
        have h_unb : ¬ F.unbounded.IsUndefined .toOdd := h
        set F'' := F.unbounded.toParityFormatOfToOdd h_unb with hF''_def
        have hF_y_eq_F'' : F_y.toFormat = F''.toFormat := by
          rw [hF_y_eq]; rfl
        have hF_y'_eq_F'' : F_y'.toFormat = F''.toFormat := by
          rw [hF_y'_eq]; rfl
        have h_F''_top : F''.p = ⊤ := hp_F
        have h_F''_exp : F''.exp = (e'' : WithBot ℤ) := hexp_F
        have h_F''_odd_dlo : F''.IsOdd dlo :=
          ((ParityFormat.IsOdd_iff_of_toFormat_eq hF_y_eq_F'' dlo).mp
            (h_y_eq_dlo ▸ hF_y_odd))
        have h_F''_odd_dhi : F''.IsOdd dhi :=
          ((ParityFormat.IsOdd_iff_of_toFormat_eq hF_y'_eq_F'' dhi).mp
            (h_y'_eq_dhi ▸ hF_y'_odd))
        rw [h_dlo_def_e''] at h_F''_odd_dlo
        rw [h_dhi_def_e''] at h_F''_odd_dhi
        exact ParityFormat.not_both_isOdd_fixedpoint h_F''_top h_F''_exp
          ⟨h_F''_odd_dlo, h_F''_odd_dhi⟩
    | coe p =>
      cases hexp_F : F.exp with
      | bot =>
        have h_unb : ¬ F.unbounded.IsUndefined .toOdd := h
        set F'' := F.unbounded.toParityFormatOfToOdd h_unb with h_F''_def
        have hF''_eq : F''.toFormat = F.unbounded.toFormat := rfl
        have hF_y_eq_F'' : F_y.toFormat = F''.toFormat := by
          rw [hF_y_eq, hF''_eq]
        have hF_y'_eq_F'' : F_y'.toFormat = F''.toFormat := by
          rw [hF_y'_eq, hF''_eq]
        have h_F''_isOdd_dlo : F''.IsOdd dlo :=
          ((ParityFormat.IsOdd_iff_of_toFormat_eq hF_y_eq_F'' dlo).mp
            (h_y_eq_dlo ▸ hF_y_odd))
        have h_F''_isOdd_dhi : F''.IsOdd dhi :=
          ((ParityFormat.IsOdd_iff_of_toFormat_eq hF_y'_eq_F'' dhi).mp
            (h_y'_eq_dhi ▸ hF_y'_odd))
        have hp_eq : F''.p = ((p : ℕ+) : WithTop ℕ+) := hp_F
        have hexp_eq : F''.exp = ⊥ := hexp_F
        have hp_ne_1 : F''.p ≠ ((1 : ℕ+) : WithTop ℕ+) := by
          change F.p ≠ ((1 : ℕ+) : WithTop ℕ+)
          intro h_eq
          exact h ⟨h_eq, hexp_F, Or.inl rfl⟩
        have h_s_lt_p : |x * (2 : ℝ) ^ (-e)| < (2 : ℝ) ^ (p : ℕ) :=
          floor_mantissa_lt hp_F
        have h_lo_hi : |lo| ≤ (2 : ℤ) ^ (p : ℕ) := by
          apply abs_floor_le_of_abs_lt
          push_cast; exact h_s_lt_p
        have h_lop1_hi : |lo + 1| ≤ (2 : ℤ) ^ (p : ℕ) :=
          abs_floor_add_one_le_of_abs_lt h_s_lt_p
        -- Derive x ≠ 0 from strict y < x (impossible if x = 0 since RoundDown
        -- of 0 in F.unbounded must be 0).
        have hx_ne : x ≠ 0 := by
          intro hx0
          subst hx0
          -- y is RoundDown of 0; 0 ∈ F.unbounded so y ≥ 0. Combined with y ≤ 0:
          -- y = 0. But hy_lt : y < 0. Contradiction.
          have h_zero_mem : (0 : Dyadic) ∈ F.unbounded := FiniteFormat.zero_mem F.unbounded
          have h_zero_le_y : ((0 : Dyadic) : ℝ) ≤ (y : ℝ) :=
            hy_max 0 h_zero_mem (by rw [Dyadic.coe_real_zero])
          rw [Dyadic.coe_real_zero] at h_zero_le_y
          linarith
        -- e = log|x|+1-p from canonicalExp formula (F.exp = ⊥, x ≠ 0).
        have h_e_eq_log : e = Int.log 2 |x| + 1 - (p : ℤ) := by
          change F.canonicalExp x = _
          unfold FiniteFormat.canonicalExp
          simp [hp_F, hexp_F, hx_ne]
        have h_2neg_pos : (0 : ℝ) < (2 : ℝ) ^ (-e) := zpow_pos (by norm_num) _
        have h_s_lo_real : ((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) ≤
            |x * (2 : ℝ) ^ (-e)| :=
          two_pow_pred_le_scaled (p := p) hx_ne h_e_eq_log
        have h_lo_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo| :=
          abs_floor_ge_two_pow_pred (p := p) h_s_lo_real
        have h_lop1_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo + 1| := by
          by_cases hx_nn : 0 ≤ x
          · -- x ≥ 0: lo ≥ 2^(p-1) ⟹ lo+1 ≥ 2^(p-1) + 1.
            have h_lo_nn : 0 ≤ lo := by
              have h_s_ge_r : ((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) ≤ x * (2 : ℝ) ^ (-e) := by
                have hs_nn : 0 ≤ x * (2 : ℝ) ^ (-e) :=
                  mul_nonneg hx_nn h_2neg_pos.le
                have h_abs_eq : |x * (2 : ℝ) ^ (-e)| = x * (2 : ℝ) ^ (-e) :=
                  abs_of_nonneg hs_nn
                linarith [h_s_lo_real]
              exact Int.floor_nonneg.mpr (le_trans (by positivity) h_s_ge_r)
            rw [abs_of_nonneg (by linarith : (0 : ℤ) ≤ lo + 1)]
            have h_lo_ge : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ lo := by
              rw [← abs_of_nonneg h_lo_nn]; exact h_lo_lo
            linarith
          · -- x < 0: strict case gives lo < x · 2^(-e) ≤ -2^(p-1),
            -- so lo ≤ -2^(p-1) - 1 ⟹ lo+1 ≤ -2^(p-1).
            push Not at hx_nn
            have hs_neg : x * (2 : ℝ) ^ (-e) < 0 :=
              mul_neg_of_neg_of_pos hx_nn h_2neg_pos
            -- Use h_floor_lt from earlier: lo < x · 2^(-e) (strict from non-exact).
            -- Wait we need h_floor_lt. It was inside the ceil_eq proof. Let me re-derive.
            have h_floor_lt : (lo : ℝ) < x * (2 : ℝ) ^ (-e) := by
              -- From y < x and y = dlo = lo · 2^e:
              have h_y_real : (y : ℝ) = (lo : ℝ) * (2 : ℝ) ^ e := by
                rw [h_y_eq_dlo_r, h_dlo_def, Dyadic.coe_ofIntZpow]
              have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
              have h_lo_e_lt_x : (lo : ℝ) * (2 : ℝ) ^ e < x := by linarith [hy_lt, h_y_real]
              have := mul_lt_mul_of_pos_right h_lo_e_lt_x h_2neg_pos
              rw [show (lo : ℝ) * (2 : ℝ) ^ e * (2 : ℝ) ^ (-e) = (lo : ℝ) by
                rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
                    add_neg_cancel, zpow_zero, mul_one]] at this
              exact this
            have h_s_le_r : x * (2 : ℝ) ^ (-e) ≤ -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) := by
              have h_abs_eq : |x * (2 : ℝ) ^ (-e)| = -(x * (2 : ℝ) ^ (-e)) :=
                abs_of_neg hs_neg
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
        -- Apply not_both_isOdd_floating.
        exact ParityFormat.not_both_isOdd_floating hp_eq hp_ne_1 hexp_eq
          h_lo_lo h_lo_hi h_lop1_lo h_lop1_hi ⟨h_F''_isOdd_dlo, h_F''_isOdd_dhi⟩
      | coe e'' =>
        -- F.p = (p : ℕ+), F.exp = (e'' : ℤ). Mixed case.
        have h_unb : ¬ F.unbounded.IsUndefined .toOdd := h
        set F'' := F.unbounded.toParityFormatOfToOdd h_unb with hF''_def
        have hF''_eq : F''.toFormat = F.unbounded.toFormat := rfl
        have hF_y_eq_F'' : F_y.toFormat = F''.toFormat := by rw [hF_y_eq, hF''_eq]
        have hF_y'_eq_F'' : F_y'.toFormat = F''.toFormat := by rw [hF_y'_eq, hF''_eq]
        have h_F''_isOdd_dlo : F''.IsOdd dlo :=
          ((ParityFormat.IsOdd_iff_of_toFormat_eq hF_y_eq_F'' dlo).mp
            (h_y_eq_dlo ▸ hF_y_odd))
        have h_F''_isOdd_dhi : F''.IsOdd dhi :=
          ((ParityFormat.IsOdd_iff_of_toFormat_eq hF_y'_eq_F'' dhi).mp
            (h_y'_eq_dhi ▸ hF_y'_odd))
        have hp_eq : F''.p = ((p : ℕ+) : WithTop ℕ+) := hp_F
        have hexp_eq : F''.exp = (e'' : WithBot ℤ) := hexp_F
        by_cases hp_eq_1 : p = (1 : ℕ+)
        · -- p = 1: exponent-index parity branch.
          subst hp_eq_1
          have hp_eq_1' : F''.p = ((1 : ℕ+) : WithTop ℕ+) := hp_F
          have hexp_eq_1 : F''.exp = (e'' : WithBot ℤ) := hexp_F
          have hx_ne : x ≠ 0 := by
            intro hx0
            subst hx0
            have h_zero_mem : (0 : Dyadic) ∈ F.unbounded :=
              FiniteFormat.zero_mem F.unbounded
            have h_zero_le_y : ((0 : Dyadic) : ℝ) ≤ (y : ℝ) :=
              hy_max 0 h_zero_mem (by rw [Dyadic.coe_real_zero])
            rw [Dyadic.coe_real_zero] at h_zero_le_y
            linarith
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
          have h_dlo_at : dlo = Dyadic.ofIntZpow lo e := h_dlo_def
          have h_dhi_at : dhi = Dyadic.ofIntZpow (lo + 1) e := h_dhi_def
          by_cases h_regime : Int.log 2 |x| + 1 - ((1 : ℕ+) : ℤ) ≤ e''
          · -- Subnormal: e = e''.
            have h_e_eq : e = e'' := by
              change F.canonicalExp x = e''
              unfold FiniteFormat.canonicalExp
              simp only [hp_F, hexp_F]
              rw [if_neg hx_ne]
              exact max_eq_right h_regime
            rw [h_dlo_at, h_e_eq] at h_F''_isOdd_dlo
            rw [h_dhi_at, h_e_eq] at h_F''_isOdd_dhi
            exact ParityFormat.not_both_isOdd_mixed_subnormal_p1
              hp_eq_1' hexp_eq_1 h_lo_hi_int h_lop1_hi_int
              ⟨h_F''_isOdd_dlo, h_F''_isOdd_dhi⟩
          · -- Normal: e = log|x|. Need |lo|, |lo+1| ≥ 1.
            push Not at h_regime
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
            have h_2neg_pos : (0 : ℝ) < (2 : ℝ) ^ (-e) :=
              zpow_pos (by norm_num) _
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
            -- lo ≠ -1 (in unique, via h_y_eq_dlo_r and hy_lt to exclude).
            have h_lo_ne_neg1 : lo ≠ -1 := by
              intro h_eq
              set s := x * (2 : ℝ) ^ (-e)
              have h_lo_int : ⌊s⌋ = -1 := h_eq
              have h_floor_le : (-1 : ℝ) ≤ s := by
                have h_fl := Int.floor_le s
                rw [h_lo_int] at h_fl; push_cast at h_fl; exact h_fl
              have h_lt_succ : s < 0 := by
                have h_lt := Int.lt_floor_add_one s
                rw [h_lo_int] at h_lt; push_cast at h_lt; linarith
              have h_s_le_neg1 : s ≤ -1 := by
                have h_abs_eq : |s| = -s := abs_of_neg (by linarith : s < 0)
                have h_abs_ge : 1 ≤ |s| := h_abs_s
                linarith
              have h_s_eq : s = -1 := le_antisymm h_s_le_neg1 h_floor_le
              have h_x_eq : x = (-1 : ℝ) * (2 : ℝ) ^ e := by
                have h_s_eq' : x * (2 : ℝ) ^ (-e) = -1 := h_s_eq
                have h_mul_inv : (2 : ℝ) ^ (-e) * (2 : ℝ) ^ e = 1 := by
                  rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
                  rw [neg_add_cancel, zpow_zero]
                calc x = x * 1 := by ring
                  _ = x * ((2 : ℝ) ^ (-e) * (2 : ℝ) ^ e) := by rw [h_mul_inv]
                  _ = (x * (2 : ℝ) ^ (-e)) * (2 : ℝ) ^ e := by ring
                  _ = (-1 : ℝ) * (2 : ℝ) ^ e := by rw [h_s_eq']
              have h_y_real : (y : ℝ) = (lo : ℝ) * (2 : ℝ) ^ e := by
                rw [h_y_eq_dlo_r, h_dlo_def, Dyadic.coe_ofIntZpow]
              rw [h_eq] at h_y_real
              push_cast at h_y_real
              have h_yx_eq : (y : ℝ) = x := by rw [h_y_real, h_x_eq]
              linarith [hy_lt]
            have h_lop1_lo_int : 1 ≤ |lo + 1| := by
              have h_lop1_ne : lo + 1 ≠ 0 := by
                intro h0; apply h_lo_ne_neg1; omega
              exact Int.one_le_abs h_lop1_ne
            rw [h_dlo_at] at h_F''_isOdd_dlo
            rw [h_dhi_at] at h_F''_isOdd_dhi
            exact ParityFormat.not_both_isOdd_mixed_normal_p1
              hp_eq_1' hexp_eq_1 h_e_ge h_lo_lo_int h_lo_hi_int
              h_lop1_lo_int h_lop1_hi_int
              ⟨h_F''_isOdd_dlo, h_F''_isOdd_dhi⟩
        · have hp_ne_1 : F''.p ≠ ((1 : ℕ+) : WithTop ℕ+) := by
            change F.p ≠ _
            rw [hp_F]
            intro h_eq
            apply hp_eq_1
            exact_mod_cast h_eq
          -- Derive x ≠ 0.
          have hx_ne : x ≠ 0 := by
            intro hx0
            subst hx0
            have h_zero_mem : (0 : Dyadic) ∈ F.unbounded := FiniteFormat.zero_mem F.unbounded
            have h_zero_le_y : ((0 : Dyadic) : ℝ) ≤ (y : ℝ) :=
              hy_max 0 h_zero_mem (by rw [Dyadic.coe_real_zero])
            rw [Dyadic.coe_real_zero] at h_zero_le_y
            linarith
          by_cases h_regime : Int.log 2 |x| + 1 - ((p : ℕ+) : ℤ) ≤ e''
          · -- Subnormal: e = e''.
            have h_e_eq : e = e'' := by
              change F.canonicalExp x = e''
              unfold FiniteFormat.canonicalExp
              simp only [hp_F, hexp_F]
              rw [if_neg hx_ne]
              exact max_eq_right h_regime
            -- |x| < 2^(e'' + p) from h_regime.
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
              apply abs_floor_le_of_abs_lt
              push_cast; exact h_s_lt
            have h_lop1_le : |lo + 1| ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) :=
              abs_floor_add_one_le_of_abs_lt h_s_lt
            -- Helper: |k| ≤ 2^p ⟹ log|k| + 1 ≤ p (when |k| < 2^p strict — saturation
            -- excluded for h_F''_isOdd_* by separate argument).
            -- Apply not_both_isOdd_mixed_subnormal_pne1 after establishing log bounds.
            -- Handle saturation by showing IsOdd doesn't hold.
            have h_dlo_at_e'' : dlo = Dyadic.ofIntZpow lo e'' := by
              rw [h_dlo_def, h_e_eq]
            have h_dhi_at_e'' : dhi = Dyadic.ofIntZpow (lo + 1) e'' := by
              rw [h_dhi_def, h_e_eq]
            -- Case-split on |lo| vs |lo+1| saturation.
            rcases lt_or_eq_of_le h_lo_le with h_lo_lt | h_lo_sat
            · rcases lt_or_eq_of_le h_lop1_le with h_lop1_lt | h_lop1_sat
              · -- Both non-saturated. Apply not_both_isOdd_mixed_subnormal_pne1.
                have h_log_lo := log_lt_p_of_abs_lt_two_pow h_lo_lt
                have h_log_lop1_raw := log_lt_p_of_abs_lt_two_pow h_lop1_lt
                have h_log_lop1 : Int.log 2 |((lo : ℝ) + 1)| + 1 ≤
                    (((p : ℕ+) : ℕ) : ℤ) := by
                  have h_eq : |((lo : ℝ) + 1)| = |((lo + 1 : ℤ) : ℝ)| := by
                    push_cast; rfl
                  rw [h_eq]; exact h_log_lop1_raw
                rw [h_dlo_at_e''] at h_F''_isOdd_dlo
                rw [h_dhi_at_e''] at h_F''_isOdd_dhi
                exact ParityFormat.not_both_isOdd_mixed_subnormal_pne1
                  hp_eq hp_ne_1 hexp_eq h_log_lo h_log_lop1
                  ⟨h_F''_isOdd_dlo, h_F''_isOdd_dhi⟩
              · -- |lo+1| saturation: |lo+1| = 2^p. F''.IsOdd dhi fails.
                rw [h_dhi_at_e''] at h_F''_isOdd_dhi
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
                  rw [h_dhi_real_e'']
                  rw [ParityFormat.log_abs_mul_zpow h_lop1_ne e'']
                  have h_cast_eq : |((lo + 1 : ℤ) : ℝ)| = (|lo + 1| : ℝ) := by
                    push_cast; rfl
                  rw [h_cast_eq, h_log_2p]
                have h_log_y_ge : (((p : ℕ+) : ℕ) : ℤ) ≤
                    Int.log 2 |(Dyadic.ofIntZpow (lo + 1) e'' : ℝ)| - e'' + 1 := by
                  rw [h_log_dhi]; linarith
                exact (ParityFormat.not_isOdd_at_saturation_mixed_normal hp_eq
                  hp_ne_1 hexp_eq h_dhi_ne h_log_y_ge h_dhi_real_e'' h_lop1_sat)
                  h_F''_isOdd_dhi
            · -- |lo| saturation: |lo| = 2^p. F''.IsOdd dlo fails.
              rw [h_dlo_at_e''] at h_F''_isOdd_dlo
              have h_dlo_real_e'' : (Dyadic.ofIntZpow lo e'' : ℝ) =
                  (lo : ℝ) * (2 : ℝ) ^ e'' := Dyadic.coe_ofIntZpow _ _
              have h_lo_ne : lo ≠ 0 := by
                intro h_zero
                rw [h_zero] at h_lo_sat
                simp at h_lo_sat
                have : (0 : ℤ) < (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by positivity
                omega
              have h_dlo_ne : (Dyadic.ofIntZpow lo e'' : ℝ) ≠ 0 := by
                rw [h_dlo_real_e'']
                exact mul_ne_zero (Int.cast_ne_zero.mpr h_lo_ne)
                  (ne_of_gt (zpow_pos (by norm_num) _))
              have h_log_2p : Int.log 2 (|lo| : ℝ) = (((p : ℕ+) : ℕ) : ℤ) := by
                have h_bridge : (|lo| : ℝ) = ((|lo| : ℤ) : ℝ) := by
                  push_cast; rfl
                rw [h_bridge, h_lo_sat]
                have h_cast : (((2 : ℤ) ^ ((p : ℕ+) : ℕ) : ℤ) : ℝ) =
                    (2 : ℝ) ^ (((p : ℕ+) : ℕ) : ℤ) := by
                  rw [zpow_natCast]; push_cast; rfl
                rw [h_cast]
                exact Int.log_zpow (by norm_num : 1 < 2) _
              have h_log_dlo : Int.log 2 |(Dyadic.ofIntZpow lo e'' : ℝ)| =
                  (((p : ℕ+) : ℕ) : ℤ) + e'' := by
                rw [h_dlo_real_e'']
                rw [ParityFormat.log_abs_mul_zpow h_lo_ne e'']
                have h_cast_eq : |(lo : ℝ)| = (|lo| : ℝ) := by rfl
                rw [h_cast_eq, h_log_2p]
              have h_log_y_ge : (((p : ℕ+) : ℕ) : ℤ) ≤
                  Int.log 2 |(Dyadic.ofIntZpow lo e'' : ℝ)| - e'' + 1 := by
                rw [h_log_dlo]; linarith
              exact (ParityFormat.not_isOdd_at_saturation_mixed_normal hp_eq
                hp_ne_1 hexp_eq h_dlo_ne h_log_y_ge h_dlo_real_e'' h_lo_sat)
                h_F''_isOdd_dlo
          · -- Normal regime: e = log|x|+1-p.
            push Not at h_regime
            have h_dlo_real : (dlo : ℝ) = (lo : ℝ) * (2 : ℝ) ^ e :=
              Dyadic.coe_ofIntZpow _ _
            have h_dhi_real : (dhi : ℝ) = ((lo + 1 : ℤ) : ℝ) * (2 : ℝ) ^ e :=
              Dyadic.coe_ofIntZpow _ _
            have h_e_eq_log : e = Int.log 2 |x| + 1 - ((p : ℕ+) : ℤ) := by
              change F.canonicalExp x = _
              unfold FiniteFormat.canonicalExp
              simp only [hp_F, hexp_F]
              rw [if_neg hx_ne]
              exact max_eq_left (le_of_lt h_regime)
            have h_2neg_pos : (0 : ℝ) < (2 : ℝ) ^ (-e) := zpow_pos (by norm_num) _
            have h_s_lo_real : ((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) ≤
                |x * (2 : ℝ) ^ (-e)| :=
              two_pow_pred_le_scaled (p := p) hx_ne h_e_eq_log
            have h_lo_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo| :=
              abs_floor_ge_two_pow_pred (p := p) h_s_lo_real
            -- Derive lo+1 lower bound. Use h_floor_lt from y < x.
            have h_lop1_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo + 1| := by
              by_cases hx_nn : 0 ≤ x
              · have h_lo_nn : 0 ≤ lo := by
                  have h_s_ge_r : ((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) ≤ x * (2 : ℝ) ^ (-e) := by
                    have hs_nn : 0 ≤ x * (2 : ℝ) ^ (-e) :=
                      mul_nonneg hx_nn h_2neg_pos.le
                    have h_abs_eq : |x * (2 : ℝ) ^ (-e)| = x * (2 : ℝ) ^ (-e) :=
                      abs_of_nonneg hs_nn
                    linarith [h_s_lo_real]
                  exact Int.floor_nonneg.mpr (le_trans (by positivity) h_s_ge_r)
                rw [abs_of_nonneg (by linarith : (0 : ℤ) ≤ lo + 1)]
                have h_lo_ge : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ lo := by
                  rw [← abs_of_nonneg h_lo_nn]; exact h_lo_lo
                linarith
              · push Not at hx_nn
                have hs_neg : x * (2 : ℝ) ^ (-e) < 0 :=
                  mul_neg_of_neg_of_pos hx_nn h_2neg_pos
                have h_floor_lt : (lo : ℝ) < x * (2 : ℝ) ^ (-e) := by
                  have h_y_real : (y : ℝ) = (lo : ℝ) * (2 : ℝ) ^ e := by
                    rw [h_y_eq_dlo_r, h_dlo_def, Dyadic.coe_ofIntZpow]
                  have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
                  have h_lo_e_lt_x : (lo : ℝ) * (2 : ℝ) ^ e < x := by
                    linarith [hy_lt, h_y_real]
                  have := mul_lt_mul_of_pos_right h_lo_e_lt_x h_2neg_pos
                  rw [show (lo : ℝ) * (2 : ℝ) ^ e * (2 : ℝ) ^ (-e) = (lo : ℝ) by
                    rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
                        add_neg_cancel, zpow_zero, mul_one]] at this
                  exact this
                have h_s_le_r : x * (2 : ℝ) ^ (-e) ≤ -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) := by
                  have h_abs_eq : |x * (2 : ℝ) ^ (-e)| = -(x * (2 : ℝ) ^ (-e)) :=
                    abs_of_neg hs_neg
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
            -- |lo|, |lo+1| ≤ 2^p (via h_s_lt_p analog).
            have h_s_lt_p : |x * (2 : ℝ) ^ (-e)| < (2 : ℝ) ^ ((p : ℕ+) : ℕ) :=
              floor_mantissa_lt hp_F
            have h_lo_hi : |lo| ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by
              apply abs_floor_le_of_abs_lt
              push_cast; exact h_s_lt_p
            have h_lop1_hi : |lo + 1| ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) :=
              abs_floor_add_one_le_of_abs_lt h_s_lt_p
            -- Derive log bounds and apply not_both_isOdd_mixed_normal_pne1.
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
            have h_log_2pow_nat := log_two_pow_nat
            have h_log_lo_lb := log_ge_p_pred_of_two_pow_pred_le (k := lo) h_lo_lo
            have h_log_lop1_lb := log_ge_p_pred_of_two_pow_pred_le (k := lo + 1) h_lop1_lo
            have h_log_lo : ((p : ℕ) : ℤ) ≤ Int.log 2 |(dlo : ℝ)| - e'' + 1 := by
              rw [h_log_dlo, h_e_eq_log]
              have : Int.log 2 |x| - e'' ≥ ((p : ℕ) : ℤ) := by linarith
              linarith [h_log_lo_lb]
            have h_log_hi : ((p : ℕ) : ℤ) ≤ Int.log 2 |(dhi : ℝ)| - e'' + 1 := by
              rw [h_log_dhi, h_e_eq_log]
              have : Int.log 2 |x| - e'' ≥ ((p : ℕ) : ℤ) := by linarith
              linarith [h_log_lop1_lb]
            -- Apply not_both_isOdd_mixed_normal_pne1.
            exact ParityFormat.not_both_isOdd_mixed_normal_pne1
              hp_eq hp_ne_1 hexp_eq h_dlo_ne h_dhi_ne h_log_lo h_log_hi
              h_dlo_real h_dhi_real h_lo_lo h_lo_hi h_lop1_lo h_lop1_hi
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
