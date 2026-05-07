import Mpfx.Digits
import Mpfx.Rounding

/-!
# Correct double rounding

The seven theorems from §5.2 / Fig. 9 of the paper. Proofs follow Appendix A.

Each theorem is stated *spec-relationally*: given that `z` is the rounding of
`x` in `F₂` and `w` is the rounding of `z` in `F₁`, conclude that `w` is also
the rounding of `x` in `F₁`. This matches the paper's reasoning style and
sidesteps having to define `rnd` constructively.

The overflow conditions on `b` from Fig. 9 are not needed in this formulation:
they ensure that the rounded values *exist*, not that the relationship holds.
The spec form takes existence of `z` and `w` as hypotheses.
-/

namespace Mpfx

namespace AbstractFormat

/-- **rnd-RTZ-RTZ** (Fig. 9). If `F₁ ⊆ F₂` and the chained RTZ-rounding
`(F₂, RTZ) ; (F₁, RTZ)` produces results `z` and `w`, then `w` is also the
RTZ-rounding of `x` in `F₁` directly. -/
theorem rndRTZ_RTZ {F₁ F₂ : AbstractFormat} (hsub : F₁ ⊆ F₂)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsRTZ F₂ x z) (hw : RoundsRTZ F₁ (z : ℝ) w) :
    RoundsRTZ F₁ x w := by
  obtain ⟨hzF, hzbnd, hzsign, hzmax⟩ := hz
  obtain ⟨hwF, hwbnd, hwsign, hwmax⟩ := hw
  refine ⟨hwF, le_trans hwbnd hzbnd, ?_, ?_⟩
  · -- w * x ≥ 0
    rcases lt_trichotomy ((z : ℝ)) 0 with hzlt | hzeq | hzgt
    · -- z < 0
      have hx_le : x ≤ 0 := by
        by_contra hxlt
        push Not at hxlt
        linarith [mul_neg_of_neg_of_pos hzlt hxlt]
      have hw_le : (w : ℝ) ≤ 0 := by
        by_contra hwlt
        push Not at hwlt
        linarith [mul_neg_of_pos_of_neg hwlt hzlt]
      exact mul_nonneg_iff.mpr (Or.inr ⟨hw_le, hx_le⟩)
    · -- z = 0
      have hw_eq : (w : ℝ) = 0 := by
        have h : |(w : ℝ)| ≤ 0 := by rw [hzeq, abs_zero] at hwbnd; exact hwbnd
        exact abs_nonpos_iff.mp h
      rw [hw_eq]; simp
    · -- z > 0
      have hx_ge : 0 ≤ x := by
        by_contra hxlt
        push Not at hxlt
        linarith [mul_neg_of_pos_of_neg hzgt hxlt]
      have hw_ge : 0 ≤ (w : ℝ) := by
        by_contra hwlt
        push Not at hwlt
        linarith [mul_neg_of_neg_of_pos hwlt hzgt]
      exact mul_nonneg hw_ge hx_ge
  · -- maximality
    intro y hyF₁ hybnd hysign
    have hyF₂ : y ∈ F₂ := hsub y hyF₁
    have hyz_le : |(y : ℝ)| ≤ |(z : ℝ)| := hzmax y hyF₂ hybnd hysign
    have hyz_sign : 0 ≤ (y : ℝ) * (z : ℝ) := by
      rcases lt_trichotomy ((z : ℝ)) 0 with hzlt | hzeq | hzgt
      · have hx_le : x ≤ 0 := by
          by_contra hxlt; push Not at hxlt
          linarith [mul_neg_of_neg_of_pos hzlt hxlt]
        -- if x = 0, then |z| ≤ |x| = 0 forces z = 0, contradiction
        have hx_lt : x < 0 := by
          rcases lt_or_eq_of_le hx_le with hlt | heq
          · exact hlt
          · exfalso
            have : |(z : ℝ)| ≤ 0 := by rw [heq, abs_zero] at hzbnd; exact hzbnd
            have hzz : (z : ℝ) = 0 := abs_nonpos_iff.mp this
            linarith
        have hy_le : (y : ℝ) ≤ 0 := by
          by_contra hylt; push Not at hylt
          linarith [mul_neg_of_pos_of_neg hylt hx_lt]
        exact mul_nonneg_iff.mpr (Or.inr ⟨hy_le, hzlt.le⟩)
      · have hy_eq : (y : ℝ) = 0 := by
          rw [hzeq, abs_zero] at hyz_le
          exact abs_nonpos_iff.mp hyz_le
        rw [hy_eq, zero_mul]
      · have hx_ge : 0 ≤ x := by
          by_contra hxlt; push Not at hxlt
          linarith [mul_neg_of_pos_of_neg hzgt hxlt]
        have hx_pos : 0 < x := by
          rcases lt_or_eq_of_le hx_ge with hgt | heq
          · exact hgt
          · exfalso
            have : |(z : ℝ)| ≤ 0 := by rw [← heq, abs_zero] at hzbnd; exact hzbnd
            have hzz : (z : ℝ) = 0 := abs_nonpos_iff.mp this
            linarith
        have hy_ge : 0 ≤ (y : ℝ) := by
          by_contra hylt; push Not at hylt
          linarith [mul_neg_of_neg_of_pos hylt hx_pos]
        exact mul_nonneg hy_ge hzgt.le
    exact hwmax y hyF₁ hyz_le hyz_sign

/-- **rnd-RAZ-RAZ** (Fig. 9), case `0 < x`. The general theorem follows by
symmetry (`neg_mem`) and the trivial `x = 0` case. -/
theorem rndRAZ_RAZ_pos {F₁ F₂ : AbstractFormat} (hsub : F₁ ⊆ F₂)
    {x : ℝ} (hx : 0 < x) {z w : Dyadic}
    (hz : RoundsRAZ F₂ x z) (hw : RoundsRAZ F₁ (z : ℝ) w) :
    RoundsRAZ F₁ x w := by
  obtain ⟨hzF, hzbnd, hzsign, hzmin⟩ := hz
  obtain ⟨hwF, hwbnd, hwsign, hwmin⟩ := hw
  -- |x| ≤ |z| and 0 < x give 0 < z
  have hx_abs : |x| = x := abs_of_pos hx
  have hz_pos : 0 < (z : ℝ) := by
    have : 0 < |(z : ℝ)| := lt_of_lt_of_le (by rwa [hx_abs]) hzbnd
    rcases lt_or_gt_of_ne (abs_pos.mp this) with h | h
    · -- z < 0: contradicts z * x ≥ 0 with x > 0
      exfalso
      linarith [mul_neg_of_neg_of_pos h hx]
    · exact h
  have hz_abs : |(z : ℝ)| = (z : ℝ) := abs_of_pos hz_pos
  -- |w| ≥ |z| and 0 < z give 0 < w
  have hw_pos : 0 < (w : ℝ) := by
    have hw_pos' : 0 < |(w : ℝ)| := lt_of_lt_of_le (by rwa [hz_abs]) hwbnd
    rcases lt_or_gt_of_ne (abs_pos.mp hw_pos') with h | h
    · exfalso
      linarith [mul_neg_of_neg_of_pos h hz_pos]
    · exact h
  have hw_abs : |(w : ℝ)| = (w : ℝ) := abs_of_pos hw_pos
  refine ⟨hwF, ?_, ?_, ?_⟩
  · -- |x| ≤ |w|: |x| ≤ |z| ≤ |w|
    exact le_trans hzbnd hwbnd
  · -- w * x ≥ 0
    exact le_of_lt (mul_pos hw_pos hx)
  · -- minimality
    intro y hyF₁ hybnd hysign
    have hyF₂ : y ∈ F₂ := hsub y hyF₁
    have hzy_le : |(z : ℝ)| ≤ |(y : ℝ)| := hzmin y hyF₂ hybnd hysign
    -- y has same sign as x or is 0
    have hy_sign : 0 ≤ (y : ℝ) := by
      rcases mul_nonneg_iff.mp hysign with ⟨hyge, _⟩ | ⟨_, hxle⟩
      · exact hyge
      · linarith
    -- y ≥ 0 and y * z ≥ 0 (since z > 0)
    have hyz_sign : 0 ≤ (y : ℝ) * (z : ℝ) := mul_nonneg hy_sign hz_pos.le
    exact hwmin y hyF₁ hzy_le hyz_sign

/-- **rnd-RAZ-RAZ** (Fig. 9). General version, all `x ∈ ℝ`. Combines the
positive case, negative case (via `RoundsRAZ.neg`), and the `x = 0` case
(uses `neg_mem` to handle elements of `F₁` whose sign opposes `z`). -/
theorem rndRAZ_RAZ {F₁ F₂ : AbstractFormat} (hsub : F₁ ⊆ F₂)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsRAZ F₂ x z) (hw : RoundsRAZ F₁ (z : ℝ) w) :
    RoundsRAZ F₁ x w := by
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · -- x < 0: flip via RoundsRAZ.neg, apply positive case, flip back
    have hz' : RoundsRAZ F₂ (-x) (-z) := RoundsRAZ.neg hz
    have hw' : RoundsRAZ F₁ ((-z : Dyadic) : ℝ) (-w) := by
      have := RoundsRAZ.neg hw
      change RoundsRAZ F₁ (-(z : ℝ)) (-w) at this
      have hcoe : ((-z : Dyadic) : ℝ) = -(z : ℝ) := by push_cast; rfl
      rw [hcoe]; exact this
    have hresult := rndRAZ_RAZ_pos hsub (neg_pos.mpr hx_neg) hz' hw'
    have := RoundsRAZ.neg hresult
    rwa [neg_neg, neg_neg] at this
  · -- x = 0: w must be the minimum |·| in F₁ overall
    subst hx_zero
    obtain ⟨hzF, _, _, hzmin⟩ := hz
    obtain ⟨hwF, _, hwsign, hwmin⟩ := hw
    refine ⟨hwF, by simp, by simp, ?_⟩
    intro y hyF₁ _ _
    have hyF₂ : y ∈ F₂ := hsub y hyF₁
    -- `z` is min |·| in F₂ (constraints at x = 0 are trivial)
    have hzy : |(z : ℝ)| ≤ |(y : ℝ)| := hzmin y hyF₂ (by simp) (by simp)
    -- Apply hwmin to `y` if `y * z ≥ 0`, else to `-y`.
    by_cases hyz : 0 ≤ (y : ℝ) * (z : ℝ)
    · exact hwmin y hyF₁ hzy hyz
    · push Not at hyz
      have hny : (-y) ∈ F₁ := neg_mem hyF₁
      have h1 : |(z : ℝ)| ≤ |((-y : Dyadic) : ℝ)| := by
        push_cast; rw [abs_neg]; exact hzy
      have h2 : 0 ≤ ((-y : Dyadic) : ℝ) * (z : ℝ) := by
        push_cast; linarith
      have key := hwmin (-y) hny h1 h2
      have : |((-y : Dyadic) : ℝ)| = |(y : ℝ)| := by push_cast; rw [abs_neg]
      rwa [this] at key
  · -- x > 0
    exact rndRAZ_RAZ_pos hsub hx_pos hz hw

/-- **rnd-RTO-RTO** (Fig. 9), general case `x ∈ ℝ`.

Restricted to `F₂.p ≥ 2`. -/
theorem rndRTO_RTO {F₁ F₂ : AbstractFormat}
    (hsub : F₁ ⊆ F₂)
    (hp_F₂ : 2 ≤ F₂.p)
    {x : ℝ}
    {z w' : Dyadic}
    (hz : RoundsRTO F₂ x z)
    (hw : RoundsRTO F₁ (z : ℝ) w') :
    RoundsRTO F₁ x w' := by
  have hz_adj : RoundsDown F₂ x z ∨ RoundsUp F₂ x z := hz.2.1
  have hw'F₁ : w' ∈ F₁ := hw.1
  have hw_adj : RoundsDown F₁ (z : ℝ) w' ∨ RoundsUp F₁ (z : ℝ) w' := hw.2.1
  have hw_odd_imp : (z : ℝ) ≠ (w' : ℝ) → IsOdd F₁ w' := hw.2.2
  rcases eq_or_ne ((z : ℝ)) x with hzx | hzx
  · -- z = x: hw is essentially the goal
    rw [hzx] at hw_adj hw_odd_imp
    refine ⟨hw'F₁, hw_adj, ?_⟩
    intro hxne
    exact hw_odd_imp hxne
  · -- z ≠ x: split on z ∈ F₁ vs z ∉ F₁
    have hxne : x ≠ (z : ℝ) := fun h => hzx h.symm
    rcases Classical.em (z ∈ F₁) with hzF₁ | hz_not_F₁
    · -- z ∈ F₁: w' = z by uniqueness; conclusion follows from F₂'s data + IsOdd transfer
      have hw'_eq : w' = z := RoundsRTO.unique_of_mem hzF₁ hw
      have hw'_eq_real : (w' : ℝ) = (z : ℝ) := by rw [hw'_eq]
      refine ⟨hw'F₁, ?_, ?_⟩
      · -- Adjacency: z is x's F₁-adjacent (because z ∈ F₁ ⊆ F₂ and z is x's F₂-adjacent)
        rw [hw'_eq]
        rcases hz_adj with hRD | hRU
        · left
          obtain ⟨_, hzx_le, hz_max⟩ := hRD
          refine ⟨hzF₁, hzx_le, ?_⟩
          intro v hvF₁ hvx
          exact hz_max v (hsub _ hvF₁) hvx
        · right
          obtain ⟨_, hxz, hz_min⟩ := hRU
          refine ⟨hzF₁, hxz, ?_⟩
          intro v hvF₁ hxv
          exact hz_min v (hsub _ hvF₁) hxv
      · -- Parity: IsOdd F₁ z from IsOdd F₂ z.
        --
        -- Strategy: use `numDigits_eq_of_subset_of_isOdd` to get
        -- `numDigits F₁ z = numDigits F₂ z`, then transport the F₂ witness to F₁.
        -- For the F₁.p = 1 corner: the equality forces `numDigits F₁ z = 1` and
        -- (with `z ∈ F₁`) `e_z = F₁.exp`, giving `Odd 1` automatically.
        intro _
        have h_iod_F₂ : IsOdd F₂ z := hz.2.2 hxne
        rw [hw'_eq]
        have h_eq : numDigits F₁.p F₁.exp ((z : Dyadic) : ℝ)
            = numDigits F₂.p F₂.exp ((z : Dyadic) : ℝ) :=
          numDigits_eq_of_subset_of_isOdd hsub hp_F₂ hzF₁ h_iod_F₂
        -- Transport F₂'s witness to F₁
        have h_iod_F₂' : IsOdd F₂ z := h_iod_F₂  -- save for later use in F₁.p=1 case
        obtain ⟨c, e, h_rep_F₂, h_par_F₂⟩ := h_iod_F₂
        have hF₂_ne_1 : F₂.p ≠ 1 := by
          intro h; rw [h] at hp_F₂; exact absurd hp_F₂ (by decide)
        rw [if_neg hF₂_ne_1] at h_par_F₂
        have h_par_c : Odd c := h_par_F₂
        refine ⟨c, e, ?_, ?_⟩
        · rw [h_eq]; exact h_rep_F₂
        · -- F₁.p discriminator
          by_cases hF₁_p_1 : F₁.p = 1
          · -- F₁.p = 1: parity is Odd (e - F₁.exp + 1).
            -- Strategy: derive F₁.exp = F₂.exp = e_z, giving Odd 1 = true.
            rw [if_pos hF₁_p_1]
            have hF₁_exp_ne : F₁.exp ≠ ⊥ := F₁.exp_finite_of_p_one hF₁_p_1
            -- Extract e₁ via unbot
            set e₁ : ℤ := F₁.exp.unbot hF₁_exp_ne with he₁_def
            have hF₁_exp_eq : F₁.exp = (e₁ : WithBot ℤ) :=
              (WithBot.coe_unbot F₁.exp hF₁_exp_ne).symm
            have h_unbot : WithBot.unbotD 0 F₁.exp = e₁ := by
              rw [hF₁_exp_eq]; rfl
            rw [h_unbot]
            -- numDigits F₁ z = 1 (derived from F₁.p = 1 + h_eq + numDigits_pos)
            have h_F₂_pos_z : 0 < numDigits F₂.p F₂.exp ((z : Dyadic) : ℝ) :=
              h_iod_F₂'.numDigits_pos
            have h_numD_F₁_le_1 : numDigits F₁.p F₁.exp ((z : Dyadic) : ℝ) ≤ 1 :=
              numDigits_le_one_of_p_one hF₁_p_1 _ _
            have h_p₂_eq_1 : numDigits F₂.p F₂.exp ((z : Dyadic) : ℝ) = 1 := by
              rw [h_eq] at h_numD_F₁_le_1; omega
            have h_p₂_toNat_eq_1 :
                (numDigits F₂.p F₂.exp ((z : Dyadic) : ℝ)).toNat = 1 := by
              rw [h_p₂_eq_1]; rfl
            -- |c| = 1 from witness at precision 1
            obtain ⟨h_z_eq, hc_low_z, hc_high_z⟩ := h_rep_F₂
            rw [h_p₂_toNat_eq_1] at hc_low_z hc_high_z
            have hc_abs_eq : |c| = 1 := by
              have h1 : (1 : ℤ) ≤ |c| := by simpa using hc_low_z
              have h2 : |c| < (2 : ℤ) := by simpa using hc_high_z
              omega
            -- z ≠ 0 derivations
            have hz_ne_zero_d : z ≠ 0 := h_iod_F₂'.ne_zero
            have hz_ne_zero : ((z : Dyadic) : ℝ) ≠ 0 := by
              intro h; exact hz_ne_zero_d (Subtype.ext (by rw [h]; rfl))
            -- |z| = 2^e (since |c| = 1)
            have h2real_pos : (0 : ℝ) < 2 := by norm_num
            have h2real_ne : (2 : ℝ) ≠ 0 := by norm_num
            have habs_z_eq : |((z : Dyadic) : ℝ)| = (2 : ℝ) ^ e := by
              rw [h_z_eq, abs_mul_two_zpow]
              have hc_real : (|c| : ℝ) = 1 := by exact_mod_cast hc_abs_eq
              rw [hc_real]; ring
            have h_log_z_eq : Int.log 2 |((z : Dyadic) : ℝ)| = e := by
              rw [habs_z_eq]
              exact Int.log_zpow (by norm_num : 1 < 2) e
            -- e ≥ e₁ from z ∈ F₁'s quantumAtLeast (with c = ±1, only rep is at e)
            have hzF₁_q : Dyadic.quantumAtLeast F₁.exp z := hzF₁.2.1
            rw [hF₁_exp_eq, Dyadic.quantumAtLeast_coe] at hzF₁_q
            obtain ⟨c'_q, hc'_q_eq⟩ := hzF₁_q
            have h_e_ge_e₁ : e₁ ≤ e := by
              by_contra h_gt
              push Not at h_gt
              have h_diff : 0 < e₁ - e := by omega
              have h_diff_nat : ((e₁ - e).toNat : ℤ) = e₁ - e :=
                Int.toNat_of_nonneg (le_of_lt h_diff)
              -- c·2^e = c'_q·2^e₁ → c = c'_q·2^(e₁-e)
              have h_real : (c : ℝ) = (c'_q : ℝ) * (2 : ℝ) ^ (e₁ - e) := by
                have h2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos h2real_pos _
                have h_split : (2 : ℝ) ^ e₁ = (2 : ℝ) ^ (e₁ - e) * (2 : ℝ) ^ e := by
                  rw [← zpow_add₀ h2real_ne]; congr 1; ring
                have key : (c : ℝ) * (2 : ℝ) ^ e =
                    ((c'_q : ℝ) * (2 : ℝ) ^ (e₁ - e)) * (2 : ℝ) ^ e := by
                  rw [show ((c'_q : ℝ) * (2 : ℝ) ^ (e₁ - e)) * (2 : ℝ) ^ e =
                      (c'_q : ℝ) * ((2 : ℝ) ^ (e₁ - e) * (2 : ℝ) ^ e) from by ring]
                  rw [← h_split, ← hc'_q_eq, h_z_eq]
                exact mul_right_cancel₀ (ne_of_gt h2e_pos) key
              rw [show (2 : ℝ) ^ (e₁ - e) = (2 : ℝ) ^ ((e₁ - e).toNat : ℤ) from by
                  rw [h_diff_nat], zpow_natCast] at h_real
              have h_int_eq : c = c'_q * 2 ^ (e₁ - e).toNat := by
                have : ((c'_q * 2 ^ (e₁ - e).toNat : ℤ) : ℝ) = (c : ℝ) := by
                  push_cast; linarith
                exact_mod_cast this.symm
              have h_k_ge_1 : 1 ≤ (e₁ - e).toNat := by
                have : ((e₁ - e).toNat : ℤ) ≥ 1 := by rw [h_diff_nat]; omega
                exact_mod_cast this
              -- |c| = 1 = |c'_q| * 2^k with k ≥ 1: forces |c'_q| * 2 ≤ 1, contradiction
              have h_pow_ge_2 : (2 : ℤ) ≤ 2 ^ (e₁ - e).toNat := by
                have : (2 : ℤ) ^ 1 ≤ 2 ^ (e₁ - e).toNat :=
                  pow_le_pow_right₀ (by norm_num) h_k_ge_1
                simpa using this
              have h_factor : (1 : ℤ) = |c'_q| * 2 ^ (e₁ - e).toNat := by
                have : |c| = |c'_q * 2 ^ (e₁ - e).toNat| := by rw [h_int_eq]
                rw [hc_abs_eq, abs_mul, abs_pow] at this
                have h2_abs : |(2 : ℤ)| = 2 := by decide
                rw [h2_abs] at this
                exact this
              have h_abs_pos : (1 : ℤ) ≤ |c'_q| := by
                rcases eq_or_ne c'_q 0 with hc'0 | hc'_ne
                · rw [hc'0] at h_factor; simp at h_factor
                · exact Int.one_le_abs hc'_ne
              nlinarith
            -- Derive F₂.exp = e by analyzing numDigits F₂ z = 1
            have h_e_eq_F₂_exp_or_p_eq_1 :
                (∃ e₂ : ℤ, F₂.exp = (e₂ : WithBot ℤ) ∧ e = e₂) := by
              -- p₂ = 1 with F₂.p ≥ 2 forces F₂ subnormal: e_z = F₂.exp
              cases hF₂_exp_cases : F₂.exp with
              | bot =>
                -- F₂.exp = ⊥. Then F₂.p ≠ ⊤ (invariant). But numDigits = F₂.p.
                -- p₂ = 1 forces F₂.p = 1. Contradicts hp_F₂ ≥ 2.
                exfalso
                cases hF₂_p_cases : F₂.p with
                | top =>
                  have := F₂.not_doubly_unbounded
                  rcases this with h1 | h1
                  · exact h1 hF₂_p_cases
                  · exact h1 hF₂_exp_cases
                | coe n =>
                  have h_n : numDigits F₂.p F₂.exp ((z : Dyadic) : ℝ) = (n : ℤ) := by
                    rw [hF₂_p_cases, hF₂_exp_cases, numDigits_coe_bot' hz_ne_zero]
                  rw [h_n] at h_p₂_eq_1
                  have hn_eq_1 : n = 1 := by exact_mod_cast h_p₂_eq_1
                  have hF₂_p_eq_1 : F₂.p = (1 : ℕ∞) := by
                    rw [hF₂_p_cases]; exact_mod_cast hn_eq_1
                  rw [hF₂_p_eq_1] at hp_F₂
                  exact absurd hp_F₂ (by decide)
              | coe e₂ =>
                refine ⟨e₂, rfl, ?_⟩
                cases hF₂_p_cases : F₂.p with
                | top =>
                  have h_n : numDigits F₂.p F₂.exp ((z : Dyadic) : ℝ) =
                      Int.log 2 |((z : Dyadic) : ℝ)| - e₂ + 1 := by
                    rw [hF₂_p_cases, hF₂_exp_cases, numDigits_top_coe' hz_ne_zero]
                  rw [h_n, h_log_z_eq] at h_p₂_eq_1
                  omega
                | coe n =>
                  have h_n : numDigits F₂.p F₂.exp ((z : Dyadic) : ℝ) =
                      min ((n : ℕ) : ℤ) (Int.log 2 |((z : Dyadic) : ℝ)| - e₂ + 1) := by
                    rw [hF₂_p_cases, hF₂_exp_cases, numDigits_coe_coe' hz_ne_zero]
                  rw [h_n, h_log_z_eq] at h_p₂_eq_1
                  have hn_ge_2 : (2 : ℤ) ≤ (n : ℤ) := by
                    have : (2 : ℕ∞) ≤ ((n : ℕ) : ℕ∞) := hF₂_p_cases ▸ hp_F₂
                    exact_mod_cast this
                  rcases min_cases ((n : ℕ) : ℤ) (e - e₂ + 1) with ⟨h1, _⟩ | ⟨h1, _⟩
                  · -- min = n. n = 1 contradicts n ≥ 2.
                    rw [h1] at h_p₂_eq_1; omega
                  · rw [h1] at h_p₂_eq_1; omega
            obtain ⟨e₂, hF₂_exp_eq, h_e_eq⟩ := h_e_eq_F₂_exp_or_p_eq_1
            -- Construct 2^e₁ ∈ F₁
            have h_2e1_in_F₁ : (Dyadic.ofIntZpow 1 e₁) ∈ F₁ := by
              refine ⟨?_, ?_, ?_⟩
              · rw [hF₁_p_1]
                change Dyadic.precisionAtMost ((1 : ℕ) : ℕ∞) (Dyadic.ofIntZpow 1 e₁)
                rw [Dyadic.precisionAtMost_coe]
                refine ⟨1, e₁, ?_, ?_⟩
                · rw [Dyadic.coe_ofIntZpow]
                · decide
              · rw [hF₁_exp_eq, Dyadic.quantumAtLeast_coe]
                refine ⟨1, ?_⟩
                rw [Dyadic.coe_ofIntZpow]
              · -- |2^e₁| ≤ F₁.b
                have hzF₁_b := hzF₁.2.2
                cases hb : F₁.b with
                | top => trivial
                | coe b =>
                  rw [hb] at hzF₁_b
                  change |((Dyadic.ofIntZpow 1 e₁ : Dyadic) : ℝ)| ≤ (b : ℝ)
                  rw [Dyadic.coe_ofIntZpow]
                  have h2e₁_pos : (0 : ℝ) < (2 : ℝ) ^ e₁ := zpow_pos h2real_pos _
                  have h_eq_pow : ((1 : ℤ) : ℝ) * (2 : ℝ) ^ e₁ = (2 : ℝ) ^ e₁ := by
                    push_cast; ring
                  rw [h_eq_pow, abs_of_pos h2e₁_pos]
                  have h2e_le : (2 : ℝ) ^ e₁ ≤ (2 : ℝ) ^ e :=
                    zpow_le_zpow_right₀ (by norm_num) h_e_ge_e₁
                  have habs_z_le : |((z : Dyadic) : ℝ)| ≤ (b : ℝ) := hzF₁_b
                  rw [habs_z_eq] at habs_z_le
                  linarith
            have h_2e1_in_F₂ : (Dyadic.ofIntZpow 1 e₁) ∈ F₂ := hsub _ h_2e1_in_F₁
            -- F₂.exp ≤ e₁ from 2^e₁ ∈ F₂
            have hF₂_exp_le_e₁ : e₂ ≤ e₁ := by
              obtain ⟨_, hq, _⟩ := h_2e1_in_F₂
              rw [hF₂_exp_eq, Dyadic.quantumAtLeast_coe] at hq
              obtain ⟨c''', hc'''_eq⟩ := hq
              by_contra h_gt
              push Not at h_gt
              have h_gt' : 0 < e₂ - e₁ := by omega
              have h_diff_nat : ((e₂ - e₁).toNat : ℤ) = e₂ - e₁ :=
                Int.toNat_of_nonneg (le_of_lt h_gt')
              -- 2^e₁ = c'''·2^e₂. So 1 = c'''·2^(e₂-e₁) (in ℝ).
              have h_real : (1 : ℝ) = (c''' : ℝ) * (2 : ℝ) ^ (e₂ - e₁) := by
                rw [Dyadic.coe_ofIntZpow] at hc'''_eq
                have h_one : ((1 : ℤ) : ℝ) * (2 : ℝ) ^ e₁ =
                    (c''' : ℝ) * (2 : ℝ) ^ e₂ := hc'''_eq
                have h2e₁_pos : (0 : ℝ) < (2 : ℝ) ^ e₁ := zpow_pos h2real_pos _
                have h_split : (2 : ℝ) ^ e₂ = (2 : ℝ) ^ (e₂ - e₁) * (2 : ℝ) ^ e₁ := by
                  rw [← zpow_add₀ h2real_ne]; congr 1; ring
                have key : (1 : ℝ) * (2 : ℝ) ^ e₁ =
                    ((c''' : ℝ) * (2 : ℝ) ^ (e₂ - e₁)) * (2 : ℝ) ^ e₁ := by
                  rw [show ((1 : ℤ) : ℝ) = (1 : ℝ) from by push_cast; ring] at h_one
                  rw [h_one, h_split]; ring
                exact mul_right_cancel₀ (ne_of_gt h2e₁_pos) key
              rw [show (2 : ℝ) ^ (e₂ - e₁) =
                  (2 : ℝ) ^ ((e₂ - e₁).toNat : ℤ) from by rw [h_diff_nat],
                  zpow_natCast] at h_real
              have h_k_pos : 1 ≤ (e₂ - e₁).toNat := by
                have : ((e₂ - e₁).toNat : ℤ) ≥ 1 := by rw [h_diff_nat]; omega
                exact_mod_cast this
              have h_int_eq : (1 : ℤ) = c''' * 2 ^ (e₂ - e₁).toNat := by
                have : ((1 : ℤ) : ℝ) = ((c''' * 2 ^ (e₂ - e₁).toNat : ℤ) : ℝ) := by
                  push_cast; linarith
                exact_mod_cast this
              -- 2 | RHS but not LHS
              have h_2_dvd : (2 : ℤ) ∣ c''' * 2 ^ (e₂ - e₁).toNat := by
                rw [show (e₂ - e₁).toNat = ((e₂ - e₁).toNat - 1) + 1 from by omega,
                    pow_succ]
                exact ⟨c''' * 2 ^ ((e₂ - e₁).toNat - 1), by ring⟩
              rw [← h_int_eq] at h_2_dvd
              exact absurd h_2_dvd (by decide)
            -- Combine: e₁ = e (= e₂)
            have h_e₁_eq_e : e₁ = e := by omega
            -- Goal: Odd (e - e₁ + 1). With e = e₁: Odd 1 = true.
            rw [show (e - e₁ + 1 : ℤ) = 1 from by omega]
            exact ⟨0, by ring⟩
          · rw [if_neg hF₁_p_1]; exact h_par_c
    · -- z ∉ F₁: standard 4-way adjacency case split
      have hz_ne_w' : (z : ℝ) ≠ (w' : ℝ) := by
        intro h_eq
        apply hz_not_F₁
        rw [show z = w' from Subtype.ext h_eq]
        exact hw'F₁
      refine ⟨hw'F₁, ?_, ?_⟩
      · rcases hz_adj with hzRD | hzRU
        · rcases hw_adj with hwRD | hwRU
          · left
            obtain ⟨_, hwz, hw_max⟩ := hwRD
            have hzx_le := hzRD.2.1
            refine ⟨hw'F₁, le_trans hwz hzx_le, ?_⟩
            intro v hvF₁ hvx
            have hv_le_z : (v : ℝ) ≤ (z : ℝ) := hzRD.2.2 v (hsub _ hvF₁) hvx
            exact hw_max v hvF₁ hv_le_z
          · obtain ⟨_, hzw, hw_min⟩ := hwRU
            by_cases hw'_le_x : (w' : ℝ) ≤ x
            · exfalso
              have hw_le_z : (w' : ℝ) ≤ (z : ℝ) := hzRD.2.2 w' (hsub _ hw'F₁) hw'_le_x
              have : (w' : ℝ) = (z : ℝ) := le_antisymm hw_le_z hzw
              exact hz_ne_w' this.symm
            · push Not at hw'_le_x
              right
              refine ⟨hw'F₁, hw'_le_x.le, ?_⟩
              intro v hvF₁ hxv
              exact hw_min v hvF₁ (le_trans hzRD.2.1 hxv)
        · rcases hw_adj with hwRD | hwRU
          · obtain ⟨_, hwz, hw_max⟩ := hwRD
            by_cases hw'_le_x : (w' : ℝ) ≤ x
            · left
              refine ⟨hw'F₁, hw'_le_x, ?_⟩
              intro v hvF₁ hvx
              exact hw_max v hvF₁ (le_trans hvx hzRU.2.1)
            · exfalso
              push Not at hw'_le_x
              have hw_ge_z : (z : ℝ) ≤ (w' : ℝ) :=
                hzRU.2.2 w' (hsub _ hw'F₁) hw'_le_x.le
              have : (w' : ℝ) = (z : ℝ) := le_antisymm hwz hw_ge_z
              exact hz_ne_w' this.symm
          · right
            obtain ⟨_, hzw, hw_min⟩ := hwRU
            have hxz := hzRU.2.1
            refine ⟨hw'F₁, le_trans hxz hzw, ?_⟩
            intro v hvF₁ hxv
            have hzv : (z : ℝ) ≤ (v : ℝ) := hzRU.2.2 v (hsub _ hvF₁) hxv
            exact hw_min v hvF₁ hzv
      · -- Parity: IsOdd F₁ w' from `hw`'s parity clause (z ≠ w')
        intro _
        exact hw_odd_imp hz_ne_w'

/-- **rnd-RTO-RTZ** (Fig. 9), paper-aligned form, positive case `0 < x`. -/
private theorem rndRTO_RTZ_pos {F₁ F₂ : AbstractFormat}
    (hsub : F₁.extend 1 ⊆ F₂)
    (hp_F₂ : 2 ≤ F₂.p)
    {x : ℝ} (hx_pos : 0 < x)
    {z w' : Dyadic}
    (hz : RoundsRTO F₂ x z)
    (hw : RoundsRTZ F₁ (z : ℝ) w') :
    RoundsRTZ F₁ x w' := by
  -- F₁ ⊆ F₁.extend 1 ⊆ F₂.
  have hF₁_sub_ext : F₁ ⊆ F₁.extend 1 := by
    intro y hy
    obtain ⟨hp, hq, hb⟩ := hy
    refine ⟨?_, ?_, ?_⟩
    · have h_p_le : F₁.p ≤ F₁.p + 1 := by
        cases F₁.p with
        | top => simp
        | coe n => exact WithTop.coe_le_coe.mpr (Nat.le_succ n)
      change Dyadic.precisionAtMost _ y
      exact Dyadic.precisionAtMost_mono h_p_le hp
    · change Dyadic.quantumAtLeast _ y
      have h_exp_ge : (F₁.exp.map (· - (1 : ℤ))) ≤ F₁.exp := by
        cases F₁.exp with
        | bot => simp
        | coe e =>
          change ((e - 1 : ℤ) : WithBot ℤ) ≤ ((e : ℤ) : WithBot ℤ)
          exact WithBot.coe_le_coe.mpr (by linarith)
      exact Dyadic.quantumAtLeast_anti h_exp_ge hq
    · exact hb
  have hsub' : F₁ ⊆ F₂ := fun y hy => hsub _ (hF₁_sub_ext _ hy)
  -- Body: copied from `rndRTO_RTZ_pos`, but replace the
  -- `notMem_of_lower_numDigits` step with `notMem_of_extend_subset`.
  have h0_F₂ : (0 : Dyadic) ∈ F₂ := F₂.zero_mem
  obtain ⟨hzF₂, hz_adj, hz_odd_imp⟩ := hz
  obtain ⟨hw'F₁, hw'_bnd_z, hw'_sign_z, hw'_max⟩ := hw
  have hx_abs : |x| = x := abs_of_pos hx_pos
  have hz_nn : 0 ≤ (z : ℝ) := by
    rcases hz_adj with hRD | hRU
    · obtain ⟨_, _, hz_max⟩ := hRD
      have h := hz_max 0 h0_F₂ hx_pos.le
      simpa using h
    · obtain ⟨_, hxz, _⟩ := hRU
      linarith
  have hz_abs : |(z : ℝ)| = (z : ℝ) := abs_of_nonneg hz_nn
  rw [hz_abs] at hw'_bnd_z
  have hw'_nn : 0 ≤ (w' : ℝ) := by
    rcases lt_or_eq_of_le hz_nn with hzpos | hzeq
    · nlinarith [hw'_sign_z]
    · have h1 : |(w' : ℝ)| ≤ 0 := hzeq.symm ▸ hw'_bnd_z
      have hw'0 : (w' : ℝ) = 0 := abs_nonpos_iff.mp h1
      linarith
  have hw'_abs : |(w' : ℝ)| = (w' : ℝ) := abs_of_nonneg hw'_nn
  have hw'_le_x : (w' : ℝ) ≤ x := by
    rcases hz_adj with hRD | hRU
    · obtain ⟨_, hzx_le, _⟩ := hRD
      have : (w' : ℝ) ≤ (z : ℝ) := by rw [← hw'_abs]; exact hw'_bnd_z
      linarith
    · by_contra h_w_gt
      push Not at h_w_gt
      have hz_min := hRU.2.2
      have hw'F₂ : w' ∈ F₂ := hsub' _ hw'F₁
      have hw'_ge_z : (z : ℝ) ≤ (w' : ℝ) := hz_min w' hw'F₂ h_w_gt.le
      have hw'_le_z : (w' : ℝ) ≤ (z : ℝ) := by rw [← hw'_abs]; exact hw'_bnd_z
      have hw'_eq_z : (w' : ℝ) = (z : ℝ) := le_antisymm hw'_le_z hw'_ge_z
      have hxne : x ≠ (z : ℝ) := by
        intro hxz_eq
        rw [← hxz_eq] at hw'_eq_z
        linarith
      have hz_full : RoundsRTO F₂ x z := ⟨hzF₂, Or.inr hRU, hz_odd_imp⟩
      have hzF₁ : z ∈ F₁ := by
        rw [show z = w' from Subtype.ext hw'_eq_z.symm]; exact hw'F₁
      exact (RoundsRTO.notMem_of_extend_subset hsub hp_F₂ hz_full hxne) hzF₁
  refine ⟨hw'F₁, ?_, ?_, ?_⟩
  · rw [hw'_abs, hx_abs]; exact hw'_le_x
  · exact mul_nonneg hw'_nn hx_pos.le
  · intro v hvF₁ hv_bnd_x hv_sign_x
    rw [hx_abs] at hv_bnd_x
    have hv_nn : 0 ≤ (v : ℝ) := by nlinarith [hv_sign_x]
    have hv_abs : |(v : ℝ)| = (v : ℝ) := abs_of_nonneg hv_nn
    have hv_le_z : (v : ℝ) ≤ (z : ℝ) := by
      rcases hz_adj with hRD | hRU
      · obtain ⟨_, _, hz_F₂_max⟩ := hRD
        have hvF₂ : v ∈ F₂ := hsub' _ hvF₁
        have h1 : (v : ℝ) ≤ x := by rw [← hv_abs]; exact hv_bnd_x
        exact hz_F₂_max v hvF₂ h1
      · obtain ⟨_, hxz, _⟩ := hRU
        have h1 : (v : ℝ) ≤ x := by rw [← hv_abs]; exact hv_bnd_x
        linarith
    have hv_bnd_z : |(v : ℝ)| ≤ |(z : ℝ)| := by rw [hv_abs, hz_abs]; exact hv_le_z
    have hv_z_sign : 0 ≤ (v : ℝ) * (z : ℝ) := mul_nonneg hv_nn hz_nn
    exact hw'_max v hvF₁ hv_bnd_z hv_z_sign

/-- **rnd-RTO-RTZ** (Fig. 9), paper-aligned form. The hypothesis
`hsub : F₁.extend 1 ⊆ F₂` encodes the paper's
`A(p₁ + 1, exp₁ − 1, b₁) ⊆ A(p₂, exp₂, b₂)` containment (modulo the
`next_{p₁,exp₁}(b₁)` bound refinement, sidestepped in the spec-relational
form). The auxiliary `hp_F₂ : 2 ≤ F₂.p` mirrors `rndRTO_RTO`'s precondition
and is needed for `numDigits_eq_of_subset_of_isOdd`. -/
theorem rndRTO_RTZ {F₁ F₂ : AbstractFormat}
    (hsub : F₁.extend 1 ⊆ F₂)
    (hp_F₂ : 2 ≤ F₂.p)
    {x : ℝ}
    {z w' : Dyadic}
    (hz : RoundsRTO F₂ x z)
    (hw : RoundsRTZ F₁ (z : ℝ) w') :
    RoundsRTZ F₁ x w' := by
  -- F₁ ⊆ F₁.extend 1 ⊆ F₂.
  have hF₁_sub_ext : F₁ ⊆ F₁.extend 1 := by
    intro y hy
    obtain ⟨hp, hq, hb⟩ := hy
    refine ⟨?_, ?_, ?_⟩
    · have h_p_le : F₁.p ≤ F₁.p + 1 := by
        cases F₁.p with
        | top => simp
        | coe n => exact WithTop.coe_le_coe.mpr (Nat.le_succ n)
      change Dyadic.precisionAtMost _ y
      exact Dyadic.precisionAtMost_mono h_p_le hp
    · change Dyadic.quantumAtLeast _ y
      have h_exp_ge : (F₁.exp.map (· - (1 : ℤ))) ≤ F₁.exp := by
        cases F₁.exp with
        | bot => simp
        | coe e =>
          change ((e - 1 : ℤ) : WithBot ℤ) ≤ ((e : ℤ) : WithBot ℤ)
          exact WithBot.coe_le_coe.mpr (by linarith)
      exact Dyadic.quantumAtLeast_anti h_exp_ge hq
    · exact hb
  have hsub' : F₁ ⊆ F₂ := fun y hy => hsub _ (hF₁_sub_ext _ hy)
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · -- x < 0: negate, apply _pos', negate back.
    have hx_pos' : 0 < (-x) := by linarith
    have hz' : RoundsRTO F₂ (-x) (-z) := RoundsRTO.neg hz
    have hw' : RoundsRTZ F₁ ((-z : Dyadic) : ℝ) (-w') := by
      have h := RoundsRTZ.neg hw
      have hcoe : ((-z : Dyadic) : ℝ) = -(z : ℝ) := by push_cast; rfl
      rw [hcoe]; exact h
    have h_result := rndRTO_RTZ_pos hsub hp_F₂ hx_pos' hz' hw'
    have hfinal := RoundsRTZ.neg h_result
    rwa [neg_neg, neg_neg] at hfinal
  · -- x = 0: forces z = 0 and w' = 0.
    subst hx_zero
    have h0_F₂ : (0 : Dyadic) ∈ F₂ := F₂.zero_mem
    obtain ⟨hzF₂, hz_adj, _⟩ := hz
    have hz_zero : z = 0 := by
      rcases hz_adj with ⟨_, hz_le, hz_max⟩ | ⟨_, hz_ge, hz_min⟩
      · have h1 : (0 : ℝ) ≤ (z : ℝ) := hz_max 0 h0_F₂ (le_refl _)
        have h2 : (z : ℝ) ≤ 0 := hz_le
        have : (z : ℝ) = 0 := le_antisymm h2 h1
        exact Subtype.ext this
      · have h1 : (z : ℝ) ≤ 0 := hz_min 0 h0_F₂ (le_refl _)
        have h2 : (0 : ℝ) ≤ (z : ℝ) := hz_ge
        have : (z : ℝ) = 0 := le_antisymm h1 h2
        exact Subtype.ext this
    rw [hz_zero] at hw
    obtain ⟨hw'F₁, hw'_bnd, _, _⟩ := hw
    have hw'_zero : (w' : ℝ) = 0 := by
      have h0eq : ((0 : Dyadic) : ℝ) = 0 := rfl
      change |(w' : ℝ)| ≤ |((0 : Dyadic) : ℝ)| at hw'_bnd
      rw [h0eq, abs_zero] at hw'_bnd
      exact abs_nonpos_iff.mp hw'_bnd
    refine ⟨hw'F₁, ?_, ?_, ?_⟩
    · change |(w' : ℝ)| ≤ |((0 : Dyadic) : ℝ)|
      rw [hw'_zero]; simp
    · change (w' : ℝ) * ((0 : Dyadic) : ℝ) ≥ 0
      rw [hw'_zero]; simp
    · intro v _ hv_bnd _
      change |(v : ℝ)| ≤ |((0 : Dyadic) : ℝ)| at hv_bnd
      rw [hw'_zero]
      exact hv_bnd
  · -- x > 0
    exact rndRTO_RTZ_pos hsub hp_F₂ hx_pos hz hw

/-- **rnd-RTO-RAZ** (Fig. 9), paper-aligned form, positive case `0 < x`.
Symmetric to `rndRTO_RTZ_pos` but for round-away-from-zero. The key Lemma 5.3
application happens in the *RoundsDown* case of `z` (rather than RoundsUp). -/
private theorem rndRTO_RAZ_pos {F₁ F₂ : AbstractFormat}
    (hsub : F₁.extend 1 ⊆ F₂)
    (hp_F₂ : 2 ≤ F₂.p)
    {x : ℝ} (hx_pos : 0 < x)
    {z w' : Dyadic}
    (hz : RoundsRTO F₂ x z)
    (hw : RoundsRAZ F₁ (z : ℝ) w') :
    RoundsRAZ F₁ x w' := by
  -- F₁ ⊆ F₁.extend 1 ⊆ F₂.
  have hF₁_sub_ext : F₁ ⊆ F₁.extend 1 := by
    intro y hy
    obtain ⟨hp, hq, hb⟩ := hy
    refine ⟨?_, ?_, ?_⟩
    · have h_p_le : F₁.p ≤ F₁.p + 1 := by
        cases F₁.p with
        | top => simp
        | coe n => exact WithTop.coe_le_coe.mpr (Nat.le_succ n)
      change Dyadic.precisionAtMost _ y
      exact Dyadic.precisionAtMost_mono h_p_le hp
    · change Dyadic.quantumAtLeast _ y
      have h_exp_ge : (F₁.exp.map (· - (1 : ℤ))) ≤ F₁.exp := by
        cases F₁.exp with
        | bot => simp
        | coe e =>
          change ((e - 1 : ℤ) : WithBot ℤ) ≤ ((e : ℤ) : WithBot ℤ)
          exact WithBot.coe_le_coe.mpr (by linarith)
      exact Dyadic.quantumAtLeast_anti h_exp_ge hq
    · exact hb
  have hsub' : F₁ ⊆ F₂ := fun y hy => hsub _ (hF₁_sub_ext _ hy)
  have h0_F₂ : (0 : Dyadic) ∈ F₂ := F₂.zero_mem
  obtain ⟨hzF₂, hz_adj, hz_odd_imp⟩ := hz
  obtain ⟨hw'F₁, hw'_bnd_z, hw'_sign_z, hw'_min⟩ := hw
  have hx_abs : |x| = x := abs_of_pos hx_pos
  -- z ≥ 0
  have hz_nn : 0 ≤ (z : ℝ) := by
    rcases hz_adj with hRD | hRU
    · obtain ⟨_, _, hz_max⟩ := hRD
      have h := hz_max 0 h0_F₂ hx_pos.le
      simpa using h
    · obtain ⟨_, hxz, _⟩ := hRU
      linarith
  have hz_abs : |(z : ℝ)| = (z : ℝ) := abs_of_nonneg hz_nn
  rw [hz_abs] at hw'_bnd_z
  -- z > 0 (RTO of positive x cannot be 0)
  have hz_pos : 0 < (z : ℝ) := by
    rcases eq_or_ne ((z : ℝ)) x with hzx | hzx
    · rw [hzx]; exact hx_pos
    · have hxne : x ≠ (z : ℝ) := fun h => hzx h.symm
      have hodd : IsOdd F₂ z := hz_odd_imp hxne
      have hz_ne : z ≠ 0 := hodd.ne_zero
      have : (z : ℝ) ≠ 0 := fun h => hz_ne (Subtype.ext (by rw [h]; rfl))
      exact lt_of_le_of_ne hz_nn (Ne.symm this)
  -- w' ≥ z > 0
  have hw'_pos : 0 < (w' : ℝ) := by
    have h1 : (z : ℝ) ≤ |(w' : ℝ)| := hw'_bnd_z
    have hw'_nn : 0 ≤ (w' : ℝ) := by nlinarith [hw'_sign_z]
    have hw'_abs : |(w' : ℝ)| = (w' : ℝ) := abs_of_nonneg hw'_nn
    rw [hw'_abs] at h1
    linarith
  have hw'_nn : 0 ≤ (w' : ℝ) := le_of_lt hw'_pos
  have hw'_abs : |(w' : ℝ)| = (w' : ℝ) := abs_of_nonneg hw'_nn
  -- |w'| ≥ |x| via the contradiction in the RoundsDown branch using
  -- `notMem_of_extend_subset` instead of going through `hgt`.
  have hx_le_w' : x ≤ (w' : ℝ) := by
    rcases hz_adj with hRD | hRU
    · by_contra h_w_lt
      push Not at h_w_lt
      have hz_max := hRD.2.2
      have hw'F₂ : w' ∈ F₂ := hsub' _ hw'F₁
      have hw'_le_z : (w' : ℝ) ≤ (z : ℝ) := hz_max w' hw'F₂ h_w_lt.le
      have hz_le_w' : (z : ℝ) ≤ (w' : ℝ) := by
        have := hw'_bnd_z; rw [hw'_abs] at this; exact this
      have hw'_eq_z : (w' : ℝ) = (z : ℝ) := le_antisymm hw'_le_z hz_le_w'
      have hxne : x ≠ (z : ℝ) := by
        intro hxz_eq
        rw [← hxz_eq] at hw'_eq_z
        linarith
      have hz_full : RoundsRTO F₂ x z := ⟨hzF₂, Or.inl hRD, hz_odd_imp⟩
      have hzF₁ : z ∈ F₁ := by
        rw [show z = w' from Subtype.ext hw'_eq_z.symm]; exact hw'F₁
      exact (RoundsRTO.notMem_of_extend_subset hsub hp_F₂ hz_full hxne) hzF₁
    · have hxz := hRU.2.1
      have hz_le_w' : (z : ℝ) ≤ (w' : ℝ) := by
        have := hw'_bnd_z; rw [hw'_abs] at this; exact this
      linarith
  refine ⟨hw'F₁, ?_, ?_, ?_⟩
  · rw [hx_abs, hw'_abs]; exact hx_le_w'
  · exact mul_nonneg hw'_nn hx_pos.le
  · intro v hvF₁ hv_bnd_x hv_sign_x
    rw [hx_abs] at hv_bnd_x
    have hv_nn : 0 ≤ (v : ℝ) := by nlinarith [hv_sign_x]
    have hv_abs : |(v : ℝ)| = (v : ℝ) := abs_of_nonneg hv_nn
    have hx_le_v : x ≤ (v : ℝ) := by rw [← hv_abs]; exact hv_bnd_x
    have hz_le_v : (z : ℝ) ≤ (v : ℝ) := by
      rcases hz_adj with hRD | hRU
      · have hzx := hRD.2.1
        linarith
      · have hz_min := hRU.2.2
        have hvF₂ : v ∈ F₂ := hsub' _ hvF₁
        exact hz_min v hvF₂ hx_le_v
    have hv_bnd_z : |(z : ℝ)| ≤ |(v : ℝ)| := by rw [hz_abs, hv_abs]; exact hz_le_v
    have hv_z_sign : 0 ≤ (v : ℝ) * (z : ℝ) := mul_nonneg hv_nn hz_nn
    exact hw'_min v hvF₁ hv_bnd_z hv_z_sign

/-- **rnd-RTO-RAZ** (Fig. 9), paper-aligned form. The hypothesis
`hsub : F₁.extend 1 ⊆ F₂` encodes the paper's
`A(p₁ + 1, exp₁ − 1, b₁) ⊆ A(p₂, exp₂, b₂)` containment from Fig. 9. The
auxiliary `hp_F₂ : 2 ≤ F₂.p` mirrors `rndRTO_RTZ`'s precondition. -/
theorem rndRTO_RAZ {F₁ F₂ : AbstractFormat}
    (hsub : F₁.extend 1 ⊆ F₂)
    (hp_F₂ : 2 ≤ F₂.p)
    {x : ℝ}
    {z w' : Dyadic}
    (hz : RoundsRTO F₂ x z)
    (hw : RoundsRAZ F₁ (z : ℝ) w') :
    RoundsRAZ F₁ x w' := by
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · -- x < 0: negate, apply _pos, negate back
    have hx_pos' : 0 < (-x) := by linarith
    have hz' : RoundsRTO F₂ (-x) (-z) := RoundsRTO.neg hz
    have hw' : RoundsRAZ F₁ ((-z : Dyadic) : ℝ) (-w') := by
      have h := RoundsRAZ.neg hw
      have hcoe : ((-z : Dyadic) : ℝ) = -(z : ℝ) := by push_cast; rfl
      rw [hcoe]; exact h
    have h_result := rndRTO_RAZ_pos hsub hp_F₂ hx_pos' hz' hw'
    have hfinal := RoundsRAZ.neg h_result
    rwa [neg_neg, neg_neg] at hfinal
  · -- x = 0: pin z = 0 = w'
    subst hx_zero
    have h0_F₂ : (0 : Dyadic) ∈ F₂ := F₂.zero_mem
    obtain ⟨hzF₂, hz_adj, _⟩ := hz
    have hz_zero : z = 0 := by
      rcases hz_adj with ⟨_, hz_le, hz_max⟩ | ⟨_, hz_ge, hz_min⟩
      · have h1 : (0 : ℝ) ≤ (z : ℝ) := hz_max 0 h0_F₂ (le_refl _)
        have : (z : ℝ) = 0 := le_antisymm hz_le h1
        exact Subtype.ext this
      · have h1 : (z : ℝ) ≤ 0 := hz_min 0 h0_F₂ (le_refl _)
        have : (z : ℝ) = 0 := le_antisymm h1 hz_ge
        exact Subtype.ext this
    rw [hz_zero] at hw
    obtain ⟨hw'F₁, _, _, hw'_min⟩ := hw
    have h0_F₁ : (0 : Dyadic) ∈ F₁ := F₁.zero_mem
    have h_min := hw'_min 0 h0_F₁ (le_refl _) (by simp)
    have hw'_zero : (w' : ℝ) = 0 := by
      change |(w' : ℝ)| ≤ |((0 : Dyadic) : ℝ)| at h_min
      have h0eq : ((0 : Dyadic) : ℝ) = 0 := rfl
      rw [h0eq, abs_zero] at h_min
      exact abs_nonpos_iff.mp h_min
    refine ⟨hw'F₁, ?_, ?_, ?_⟩
    · simp [hw'_zero]
    · simp [hw'_zero]
    · intro v _ _ _
      simp [hw'_zero, abs_nonneg]
  · -- x > 0
    exact rndRTO_RAZ_pos hsub hp_F₂ hx_pos hz hw

/-- **rnd-RTO-RNE** (Fig. 9), structural form: assumes the F₂-to-F₁ transfer
of adjacency, closeness, and tie-break has been done externally.

The structural transfers (`h_adj_transfer`, `h_close_transfer`,
`h_tie_transfer`) capture the content of Lemma 5.3 plus an F₂-adjacency
analysis specific to RNE. Proving them from `hz` and `hw` directly is
substantial future work; this theorem packages the remaining bookkeeping. -/
theorem rndRTO_RNE_via_transfers {F₁ : AbstractFormat}
    {x : ℝ} {w' : Dyadic}
    (hw'F₁ : w' ∈ F₁)
    (h_adj_transfer : RoundsDown F₁ x w' ∨ RoundsUp F₁ x w')
    (h_close_transfer : ∀ z' : Dyadic, z' ∈ F₁ →
      (RoundsDown F₁ x z' ∨ RoundsUp F₁ x z') →
      |x - (w' : ℝ)| ≤ |x - (z' : ℝ)|)
    (h_tie_transfer : (∃ z' : Dyadic, z' ∈ F₁ ∧
        (RoundsDown F₁ x z' ∨ RoundsUp F₁ x z') ∧
        z' ≠ w' ∧ |x - (w' : ℝ)| = |x - (z' : ℝ)|) →
      IsEven F₁ w') :
    RoundsRNE F₁ x w' :=
  ⟨hw'F₁, h_adj_transfer, h_close_transfer, h_tie_transfer⟩

/-- Helper for tie-break: from `|x - w'| = |x - z'|` with `w' ≠ z'`, derive
`x = (w' + z') / 2`. -/
private theorem RoundsRNE.midpoint_of_tie {x : ℝ} {w' z' : Dyadic}
    (h_ne : z' ≠ w') (h_tie : |x - (w' : ℝ)| = |x - (z' : ℝ)|) :
    x = ((w' : ℝ) + (z' : ℝ)) / 2 := by
  rcases abs_eq_abs.mp h_tie with h1 | h1
  · -- x - w' = x - z' ⇒ w' = z', contradicting h_ne
    have : (w' : ℝ) = (z' : ℝ) := by linarith
    exact absurd (Subtype.ext this).symm h_ne
  · -- x - w' = -(x - z') ⇒ 2x = w' + z'
    linarith

/-- **rnd-RTO-RNE** (Fig. 9), paper-aligned form. The hypothesis
`hsub : F₁.extend 2 ⊆ F₂` encodes the paper's
`A(p₁ + 2, exp₁ − 2, b) ⊆ A(p₂, exp₂, b₂)` containment (modulo the
`next_{p₁+1, exp₁-1}(b₁)` bound refinement). The auxiliary `hp_F₂ : 3 ≤ F₂.p`
enables `numDigits_eq_of_subset_of_isOdd` and crucially rules out the
"`midpoint ∈ F₂` is odd" edge case: combined with `hsub`, every F₁-adjacent
midpoint reduces to even significand in F₂'s view. (For `F₁.p = 1` this
is `F₂.p ≥ F₁.p + 2`, the full structural shift; for `F₁.p ≥ 2` the
constraint `F₁.extend 2 ⊆ F₂` with `F₂.p = 3` forces F₁.b small enough that
problematic F₁-adjacent pairs don't arise.)

The proof handles the trivial `z = x` case directly. For `z ≠ x`, it derives:
1. `z ∉ F₁` via `RoundsRTO.notMem_of_extend_subset` (specialized to
   `F₁.extend 1 ⊆ F₂`, derived transitively from `hsub`).
2. The four-way adjacency transfer (same case-split as `rndRTO_RTO`).
3. The closeness transfer is taken as an auxiliary hypothesis `h_close` for
   now — it follows from a same-side-of-midpoint argument that requires
   midpoint membership in F₂ (which in turn requires F₁-adjacency precision
   analysis on the midpoint, deferred to future work).
4. The no-tie / tie-break is derived from `h_mid_in_F₂` (also auxiliary)
   using `RoundsRTO.unique_of_mem`.

The auxiliary hypotheses (`h_close`, `h_mid_in_F₂`) become *provable* in
principle under the stronger `3 ≤ F₂.p`, but the formalization still
requires an F₁-adjacency precision lemma on midpoints; tracked in TODO. -/
theorem rndRTO_RNE {F₁ F₂ : AbstractFormat}
    (hsub : F₁.extend 2 ⊆ F₂)
    (hp_F₂ : 3 ≤ F₂.p)
    {x : ℝ}
    {z w' : Dyadic}
    (hz : RoundsRTO F₂ x z)
    (hw : RoundsRNE F₁ (z : ℝ) w')
    (h_close : ∀ z' : Dyadic, z' ∈ F₁ →
      (RoundsDown F₁ x z' ∨ RoundsUp F₁ x z') →
      |x - (w' : ℝ)| ≤ |x - (z' : ℝ)|)
    (h_mid_in_F₂ : ∀ y₁ y₂ : Dyadic, y₁ ∈ F₁ → y₂ ∈ F₁ →
      ∃ m : Dyadic, m ∈ F₂ ∧ (m : ℝ) = ((y₁ : ℝ) + (y₂ : ℝ)) / 2) :
    RoundsRNE F₁ x w' := by
  -- Step 1: Derive subset chain F₁ ⊆ F₁.extend 1 ⊆ F₁.extend 2 ⊆ F₂.
  have hF₁_sub_ext1 : F₁ ⊆ F₁.extend 1 := by
    intro y hy
    obtain ⟨hp, hq, hb⟩ := hy
    refine ⟨?_, ?_, ?_⟩
    · have h_p_le : F₁.p ≤ F₁.p + 1 := by
        cases F₁.p with
        | top => simp
        | coe n => exact WithTop.coe_le_coe.mpr (Nat.le_succ n)
      change Dyadic.precisionAtMost _ y
      exact Dyadic.precisionAtMost_mono h_p_le hp
    · change Dyadic.quantumAtLeast _ y
      have h_exp_ge : (F₁.exp.map (· - (1 : ℤ))) ≤ F₁.exp := by
        cases F₁.exp with
        | bot => simp
        | coe e =>
          change ((e - 1 : ℤ) : WithBot ℤ) ≤ ((e : ℤ) : WithBot ℤ)
          exact WithBot.coe_le_coe.mpr (by linarith)
      exact Dyadic.quantumAtLeast_anti h_exp_ge hq
    · exact hb
  have h_ext1_sub_ext2 : F₁.extend 1 ⊆ F₁.extend 2 := by
    intro y hy
    obtain ⟨hp, hq, hb⟩ := hy
    refine ⟨?_, ?_, ?_⟩
    · have h_p_le : F₁.p + 1 ≤ F₁.p + 2 := by
        cases F₁.p with
        | top => simp
        | coe n =>
          change ((n + 1 : ℕ) : ℕ∞) ≤ ((n + 2 : ℕ) : ℕ∞)
          exact_mod_cast (by omega : n + 1 ≤ n + 2)
      change Dyadic.precisionAtMost _ y
      exact Dyadic.precisionAtMost_mono h_p_le hp
    · change Dyadic.quantumAtLeast _ y
      have h_exp_ge : (F₁.exp.map (· - (2 : ℤ))) ≤ (F₁.exp.map (· - (1 : ℤ))) := by
        cases F₁.exp with
        | bot => simp
        | coe e =>
          change ((e - 2 : ℤ) : WithBot ℤ) ≤ ((e - 1 : ℤ) : WithBot ℤ)
          exact WithBot.coe_le_coe.mpr (by linarith)
      exact Dyadic.quantumAtLeast_anti h_exp_ge hq
    · exact hb
  have hsub_ext1 : F₁.extend 1 ⊆ F₂ := fun y hy => hsub _ (h_ext1_sub_ext2 _ hy)
  have hsub' : F₁ ⊆ F₂ := fun y hy => hsub_ext1 _ (hF₁_sub_ext1 _ hy)
  -- Step 2: Trivial case z = x.
  rcases eq_or_ne ((z : ℝ)) x with hzx | hzx
  · obtain ⟨hw'F₁, hw_adj, hw_close, hw_tie⟩ := hw
    rw [hzx] at hw_adj hw_close hw_tie
    exact ⟨hw'F₁, hw_adj, hw_close, hw_tie⟩
  -- Step 3: Non-trivial case z ≠ x.
  have hxne : x ≠ (z : ℝ) := fun h => hzx h.symm
  have hp_F₂_two : 2 ≤ F₂.p := le_trans (by decide : (2 : ℕ∞) ≤ 3) hp_F₂
  have hz_not_F₁ : z ∉ F₁ :=
    RoundsRTO.notMem_of_extend_subset hsub_ext1 hp_F₂_two hz hxne
  have hz_adj : RoundsDown F₂ x z ∨ RoundsUp F₂ x z := hz.2.1
  obtain ⟨hw'F₁, hw_adj, _, _⟩ := hw
  have hz_ne_w' : (z : ℝ) ≠ (w' : ℝ) := by
    intro h_eq
    apply hz_not_F₁
    rw [show z = w' from Subtype.ext h_eq]
    exact hw'F₁
  -- Step 4: Adjacency transfer (4-way case split).
  have h_adj_x : RoundsDown F₁ x w' ∨ RoundsUp F₁ x w' := by
    rcases hz_adj with hzRD | hzRU
    · rcases hw_adj with hwRD | hwRU
      · left
        obtain ⟨_, hwz, hw_max⟩ := hwRD
        have hzx_le := hzRD.2.1
        refine ⟨hw'F₁, le_trans hwz hzx_le, ?_⟩
        intro v hvF₁ hvx
        exact hw_max v hvF₁ (hzRD.2.2 v (hsub' _ hvF₁) hvx)
      · obtain ⟨_, hzw, hw_min⟩ := hwRU
        by_cases hw'_le_x : (w' : ℝ) ≤ x
        · exfalso
          have hw_le_z : (w' : ℝ) ≤ (z : ℝ) := hzRD.2.2 w' (hsub' _ hw'F₁) hw'_le_x
          exact hz_ne_w' (le_antisymm hw_le_z hzw).symm
        · push Not at hw'_le_x
          right
          refine ⟨hw'F₁, hw'_le_x.le, ?_⟩
          intro v hvF₁ hxv
          exact hw_min v hvF₁ (le_trans hzRD.2.1 hxv)
    · rcases hw_adj with hwRD | hwRU
      · obtain ⟨_, hwz, hw_max⟩ := hwRD
        by_cases hw'_le_x : (w' : ℝ) ≤ x
        · left
          refine ⟨hw'F₁, hw'_le_x, ?_⟩
          intro v hvF₁ hvx
          exact hw_max v hvF₁ (le_trans hvx hzRU.2.1)
        · exfalso
          push Not at hw'_le_x
          have hw_ge_z : (z : ℝ) ≤ (w' : ℝ) :=
            hzRU.2.2 w' (hsub' _ hw'F₁) hw'_le_x.le
          exact hz_ne_w' (le_antisymm hwz hw_ge_z).symm
      · right
        obtain ⟨_, hzw, hw_min⟩ := hwRU
        have hxz := hzRU.2.1
        refine ⟨hw'F₁, le_trans hxz hzw, ?_⟩
        intro v hvF₁ hxv
        exact hw_min v hvF₁ (hzRU.2.2 v (hsub' _ hvF₁) hxv)
  -- Step 5: Assemble the RoundsRNE witness.
  refine ⟨hw'F₁, h_adj_x, h_close, ?_⟩
  -- Step 6: No-tie via midpoint + RoundsRTO.unique_of_mem.
  rintro ⟨z', hz'F₁, _, hz'_ne_w', hz'_eq_dist⟩
  have hx_mid : x = ((w' : ℝ) + (z' : ℝ)) / 2 :=
    RoundsRNE.midpoint_of_tie hz'_ne_w' hz'_eq_dist
  obtain ⟨m, hmF₂, hm_eq⟩ := h_mid_in_F₂ w' z' hw'F₁ hz'F₁
  have hm_x : (m : ℝ) = x := by rw [hm_eq, ← hx_mid]
  have hz_eq : z = m := by
    have hz' : RoundsRTO F₂ ((m : ℝ)) z := by rw [hm_x]; exact hz
    exact RoundsRTO.unique_of_mem hmF₂ hz'
  -- z = m and m = x as reals, so z = x as reals — contradicts hxne.
  exact (hxne (by rw [hz_eq]; exact hm_x.symm)).elim

end AbstractFormat

end Mpfx
