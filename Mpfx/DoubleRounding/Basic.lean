import Mpfx.Format.Next
import Mpfx.Format.Digits
import Mpfx.Format.Discrete
import Mpfx.Rounding.Defs
import Mpfx.Rounding.Op

/-!
# Correct double rounding (§5.2)

The double-rounding rules in the `RoundsFinite` layer (`roundsRTZ_RTZ_finite`, …):
stated *spec-relationally* — given that `z` is the rounding of `x` in `F₂`
and `w` is the rounding of `z` in `F₁` (with `F₁ ⊆ F₂`), conclude that `w` is
also the rounding of `x` in `F₁` directly. Overflow bookkeeping is sidestepped
and the existence of `z`, `w` is taken as hypotheses. `roundsRTO_RN_finite` is in
`Mpfx.DoubleRounding.Nearest`; the overflow-aware total forms
(`roundsRTZ_RTZ_inBound`, …) are in `Mpfx.DoubleRounding.Total`.
-/


namespace Mpfx


/-- **Exact-intermediate collapse.** If the input `v` is already representable
in the wide format `F₂`, double rounding is trivially correct for *any* modes:
the intermediate rounding fixes `v` (`z = v` by `RoundsFinite.eq_of_mem`), so
the chained rounding of `v` is the direct one. This is the spec-relational
form of Flocq's `round_generic`-based collapse and the shared core of every
"exact intermediate" operation rule. -/
theorem rndExact {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode}
    {v : Dyadic} (hv : v ∈ F₂) {z w : Dyadic}
    (hz : RoundsFinite F₂ rm₂ (v : ℝ) z) (hw : RoundsFinite F₁ rm₁ (z : ℝ) w) :
    RoundsFinite F₁ rm₁ (v : ℝ) w := by
  rw [RoundsFinite.eq_of_mem hv hz] at hw
  exact hw

/-- **rnd-RTZ-RTZ**. Chained round-toward-zero collapses: if
`F₁ ⊆ F₂`, `z` is the RTZ-rounding of `x` in `F₂`, and `w` is the RTZ-rounding
of `z` in `F₁`, then `w` is the RTZ-rounding of `x` in `F₁`. -/
theorem roundsRTZ_RTZ_finite {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toZero x z) (hw : RoundsFinite F₁ .toZero (z : ℝ) w) :
    RoundsFinite F₁ .toZero x w := by
  obtain ⟨hzF, hzbnd, hzsign, hzmax⟩ := hz
  obtain ⟨hwF, hwbnd, hwsign, hwmax⟩ := hw
  refine ⟨hwF, le_trans hwbnd hzbnd, ?_, ?_⟩
  · -- w * x ≥ 0
    rcases lt_trichotomy (z : ℝ) 0 with hzlt | hzeq | hzgt
    · have hx_le : x ≤ 0 := by
        by_contra hxlt; push Not at hxlt
        linarith [mul_neg_of_neg_of_pos hzlt hxlt]
      have hw_le : (w : ℝ) ≤ 0 := by
        by_contra hwlt; push Not at hwlt
        linarith [mul_neg_of_pos_of_neg hwlt hzlt]
      exact mul_nonneg_iff.mpr (Or.inr ⟨hw_le, hx_le⟩)
    · have hw_eq : (w : ℝ) = 0 := by
        have h : |(w : ℝ)| ≤ 0 := by rw [hzeq, abs_zero] at hwbnd; exact hwbnd
        exact abs_nonpos_iff.mp h
      rw [hw_eq]; simp
    · have hx_ge : 0 ≤ x := by
        by_contra hxlt; push Not at hxlt
        linarith [mul_neg_of_pos_of_neg hzgt hxlt]
      have hw_ge : 0 ≤ (w : ℝ) := by
        by_contra hwlt; push Not at hwlt
        linarith [mul_neg_of_neg_of_pos hwlt hzgt]
      exact mul_nonneg hw_ge hx_ge
  · -- maximality
    intro y hyF₁ hybnd hysign
    have hyF₂ : y ∈ F₂ := hsub y hyF₁
    have hyz_le : |(y : ℝ)| ≤ |(z : ℝ)| := hzmax y hyF₂ hybnd hysign
    have hyz_sign : 0 ≤ (y : ℝ) * (z : ℝ) := by
      rcases lt_trichotomy (z : ℝ) 0 with hzlt | hzeq | hzgt
      · have hx_le : x ≤ 0 := by
          by_contra hxlt; push Not at hxlt
          linarith [mul_neg_of_neg_of_pos hzlt hxlt]
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

/-- **rnd-RAZ-RAZ**, case `0 < x`. The general theorem follows by
sign-symmetry and the `x = 0` case. -/
private theorem roundsRAZ_RAZ_finite_pos {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    {x : ℝ} (hx : 0 < x) {z w : Dyadic}
    (hz : RoundsFinite F₂ .awayZero x z) (hw : RoundsFinite F₁ .awayZero (z : ℝ) w) :
    RoundsFinite F₁ .awayZero x w := by
  obtain ⟨hzF, hzbnd, hzsign, hzmin⟩ := hz
  obtain ⟨hwF, hwbnd, hwsign, hwmin⟩ := hw
  have hx_abs : |x| = x := abs_of_pos hx
  have hz_pos : 0 < (z : ℝ) := by
    have : 0 < |(z : ℝ)| := lt_of_lt_of_le (by rwa [hx_abs]) hzbnd
    rcases lt_or_gt_of_ne (abs_pos.mp this) with h | h
    · exfalso; linarith [mul_neg_of_neg_of_pos h hx]
    · exact h
  have hz_abs : |(z : ℝ)| = (z : ℝ) := abs_of_pos hz_pos
  have hw_pos : 0 < (w : ℝ) := by
    have hw_pos' : 0 < |(w : ℝ)| := lt_of_lt_of_le (by rwa [hz_abs]) hwbnd
    rcases lt_or_gt_of_ne (abs_pos.mp hw_pos') with h | h
    · exfalso; linarith [mul_neg_of_neg_of_pos h hz_pos]
    · exact h
  refine ⟨hwF, ?_, ?_, ?_⟩
  · exact le_trans hzbnd hwbnd
  · exact le_of_lt (mul_pos hw_pos hx)
  · intro y hyF₁ hybnd hysign
    have hyF₂ : y ∈ F₂ := hsub y hyF₁
    have hzy_le : |(z : ℝ)| ≤ |(y : ℝ)| := hzmin y hyF₂ hybnd hysign
    have hy_sign : 0 ≤ (y : ℝ) := by
      rcases mul_nonneg_iff.mp hysign with ⟨hyge, _⟩ | ⟨_, hxle⟩
      · exact hyge
      · linarith
    have hyz_sign : 0 ≤ (y : ℝ) * (z : ℝ) := mul_nonneg hy_sign hz_pos.le
    exact hwmin y hyF₁ hzy_le hyz_sign

/-- **rnd-RAZ-RAZ**. General version. Combines the positive case,
the negative case (via `RoundsFinite.neg_awayZero`), and the `x = 0` case. -/
theorem roundsRAZ_RAZ_finite {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .awayZero x z) (hw : RoundsFinite F₁ .awayZero (z : ℝ) w) :
    RoundsFinite F₁ .awayZero x w := by
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · -- x < 0: flip via sign-symmetry, apply the positive case, flip back.
    have hz' : RoundsFinite F₂ .awayZero (-x) (-z) :=
      (RoundsFinite.neg_awayZero F₂ x z).mp hz
    have hw' : RoundsFinite F₁ .awayZero ((-z : Dyadic) : ℝ) (-w) := by
      rw [Dyadic.coe_real_neg]; exact (RoundsFinite.neg_awayZero F₁ (z : ℝ) w).mp hw
    have hresult := roundsRAZ_RAZ_finite_pos hsub (neg_pos.mpr hx_neg) hz' hw'
    have hflip := (RoundsFinite.neg_awayZero F₁ (-x) (-w)).mp hresult
    rwa [neg_neg, neg_neg] at hflip
  · -- x = 0
    subst hx_zero
    obtain ⟨hzF, _, _, hzmin⟩ := hz
    obtain ⟨hwF, _, hwsign, hwmin⟩ := hw
    refine ⟨hwF, by simp, by simp, ?_⟩
    intro y hyF₁ _ _
    have hyF₂ : y ∈ F₂ := hsub y hyF₁
    have hzy : |(z : ℝ)| ≤ |(y : ℝ)| := hzmin y hyF₂ (by simp) (by simp)
    by_cases hyz : 0 ≤ (y : ℝ) * (z : ℝ)
    · exact hwmin y hyF₁ hzy hyz
    · push Not at hyz
      have hny : (-y) ∈ F₁ := FiniteFormat.neg_mem hyF₁
      have h1 : |(z : ℝ)| ≤ |((-y : Dyadic) : ℝ)| := by
        rw [Dyadic.coe_real_neg, abs_neg]; exact hzy
      have h2 : 0 ≤ ((-y : Dyadic) : ℝ) * (z : ℝ) := by
        rw [Dyadic.coe_real_neg]; linarith
      have key := hwmin (-y) hny h1 h2
      rwa [Dyadic.coe_real_neg, abs_neg] at key
  · exact roundsRAZ_RAZ_finite_pos hsub hx_pos hz hw

/-- **rnd-RTO-RTO**, general case `x ∈ ℝ`.

Restricted to `F₂.p ≥ 2`. -/
theorem roundsRTO_RTO_finite {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {x : ℝ} {z w' : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toOdd (z : ℝ) w') :
    RoundsFinite F₁ .toOdd x w' := by
  obtain ⟨hzF₂, hz_faithful, hz_odd_imp⟩ := hz
  obtain ⟨hw'F₁, hw_faithful, hw_odd_imp⟩ := hw
  rcases eq_or_ne ((z : ℝ)) x with hzx | hzx
  · -- z = x: hw is essentially the goal.
    rw [hzx] at hw_faithful hw_odd_imp
    exact ⟨hw'F₁, hw_faithful, hw_odd_imp⟩
  · -- z ≠ x: split on z = w' vs z ≠ w'.
    have hxne : x ≠ (z : ℝ) := fun h => hzx h.symm
    rcases eq_or_ne z w' with hzw | hzw
    · -- z = w': w' is x's F₁-rounding directly via hz's faithfulness, and
      -- its F₁-oddness comes from F₂-oddness via RTO-padding transfer.
      subst hzw
      refine ⟨hw'F₁, ?_, ?_⟩
      · -- Faithfulness: z is x's F₁-faithful rounding because z ∈ F₁ ⊆ F₂
        -- and z is x's F₂-faithful rounding.
        rcases hz_faithful with hRD | hRU
        · left
          obtain ⟨_, hzx_le, hz_max⟩ := hRD
          refine ⟨hw'F₁, hzx_le, ?_⟩
          intro v hvF₁ hvx
          exact hz_max v (hsub _ hvF₁) hvx
        · right
          obtain ⟨_, hxz, hz_min⟩ := hRU
          refine ⟨hw'F₁, hxz, ?_⟩
          intro v hvF₁ hxv
          exact hz_min v (hsub _ hvF₁) hxv
      · -- Parity: produce a `ParityFormat` over `F₁.toFormat` and transfer
        -- F₂-oddness of z into F₁-oddness of z.
        intro _
        obtain ⟨F₂', hF₂'eq, hF₂'odd⟩ := hz_odd_imp hxne
        -- `¬ F₁.IsUndefined .toOdd`, so a `ParityFormat` over `F₁` exists.
        have h_not_undef : ¬ F₁.IsUndefined .toOdd := by
          rintro ⟨hp1, hexp_bot, _⟩
          have hz_ne : z ≠ 0 := hF₂'odd.ne_zero
          have hz_ne_real : (z : ℝ) ≠ 0 := by
            rw [← Dyadic.coe_real_zero]; exact fun h => hz_ne (Dyadic.coe_real_inj z 0 |>.mp h)
          -- `F₁.exp = ⊥` + subset forces `F₂.exp = ⊥`, hence `numDigits = p₂ ≥ 2`.
          have hF₂'_exp_bot : F₂'.exp = ⊥ := by
            have h := Format.exp_le_of_subset ⟨_, hw'F₁, hz_ne⟩ (hF₂'eq ▸ hsub)
            rw [hexp_bot] at h; exact le_bot_iff.mp h
          obtain ⟨p₂, hp₂⟩ : ∃ p₂ : ℕ, F₂'.p = (p₂ : Prec) := by
            cases hc : F₂'.p using ENat.recTopCoe with
            | top =>
              -- `(⊤, ⊥)` is excluded by `FiniteFormat.finite`.
              exact absurd (F₂'.finite) (by push Not; exact ⟨hc, hF₂'_exp_bot⟩)
            | coe p₂ => exact ⟨p₂, rfl⟩
          -- numDigits agreement.
          have h_eq : F₁.numDigits (z : ℝ) = F₂'.toFiniteFormat.numDigits (z : ℝ) :=
            numDigits_eq_of_subset_of_isOdd (hF₂'eq ▸ hsub) (hF₂'eq ▸ hp_F₂) hw'F₁ hF₂'odd
          have h_F₁_eq_1 : F₁.numDigits (z : ℝ) = 1 :=
            F₁.numDigits_coe_bot hz_ne_real hp1 hexp_bot
          have h_F₂_eq_p₂ : F₂'.toFiniteFormat.numDigits (z : ℝ) = (p₂ : ℤ) :=
            F₂'.toFiniteFormat.numDigits_coe_bot hz_ne_real hp₂ hF₂'_exp_bot
          have hp₂_ge_2 : (2 : ℤ) ≤ (p₂ : ℤ) := by
            have : ((2 : ℕ) : Prec) ≤ (p₂ : Prec) := hp₂ ▸ (hF₂'eq ▸ hp_F₂)
            have h2 : (2 : ℕ) ≤ p₂ := by exact_mod_cast this
            simpa using (by exact_mod_cast h2 : (2 : ℤ) ≤ (p₂ : ℤ))
          rw [h_F₁_eq_1, h_F₂_eq_p₂] at h_eq
          omega
        set F₁' := F₁.toParityFormatOfToOdd h_not_undef with hF₁'_def
        have hF₁'eq : F₁'.toFormat = F₁.toFormat := rfl
        have hF₁'odd : F₁'.IsOdd z := by
          have h_F₁'F₂' : F₁'.toFormat ⊆ F₂'.toFormat := by
            rw [hF₁'eq, hF₂'eq]; exact hsub
          have h_p_F₂' : ((2 : ℕ) : Prec) ≤ F₂'.p := by
            rw [hF₂'eq]; exact hp_F₂
          exact IsOdd.transfer_of_subset h_F₁'F₂' h_p_F₂' hw'F₁ hF₂'odd
        exact ⟨F₁', hF₁'eq, hF₁'odd⟩
    · -- z ≠ w': standard 4-way faithfulness case split.
      have hz_ne_w' : (z : ℝ) ≠ (w' : ℝ) := fun h_eq => hzw (Dyadic.coe_real_inj z w' |>.mp h_eq)
      refine ⟨hw'F₁, ?_, ?_⟩
      · rcases hz_faithful with hzRD | hzRU
        · rcases hw_faithful with hwRD | hwRU
          · left
            obtain ⟨_, hwz, hw_max⟩ := hwRD
            have hzx_le := hzRD.2.1
            refine ⟨hw'F₁, le_trans hwz hzx_le, ?_⟩
            intro v hvF₁ hvx
            have hv_le_z : (v : ℝ) ≤ (z : ℝ) := hzRD.2.2 v (hsub _ hvF₁) hvx
            exact hw_max v hvF₁ hv_le_z
          · obtain ⟨_, hzw_le, hw_min⟩ := hwRU
            by_cases hw'_le_x : (w' : ℝ) ≤ x
            · exfalso
              have hw_le_z : (w' : ℝ) ≤ (z : ℝ) := hzRD.2.2 w' (hsub _ hw'F₁) hw'_le_x
              have : (w' : ℝ) = (z : ℝ) := le_antisymm hw_le_z hzw_le
              exact hz_ne_w' this.symm
            · push Not at hw'_le_x
              right
              refine ⟨hw'F₁, hw'_le_x.le, ?_⟩
              intro v hvF₁ hxv
              exact hw_min v hvF₁ (le_trans hzRD.2.1 hxv)
        · rcases hw_faithful with hwRD | hwRU
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
            obtain ⟨_, hzw_le, hw_min⟩ := hwRU
            have hxz := hzRU.2.1
            refine ⟨hw'F₁, le_trans hxz hzw_le, ?_⟩
            intro v hvF₁ hxv
            have hzv : (z : ℝ) ≤ (v : ℝ) := hzRU.2.2 v (hsub _ hvF₁) hxv
            exact hw_min v hvF₁ hzv
      · -- Parity: from `hw`'s own parity clause (z ≠ w').
        intro _
        exact hw_odd_imp hz_ne_w'

/-! ## `rnd-RTO-RTZ`

Chain: an RTO rounding `z` of `x` in the wider `F₂`, then an RTZ rounding `w'`
of `z` in `F₁`, collapses to a single RTZ rounding of `x` in `F₁`. Uses the
simpler containment hypothesis `F₁.extend 1 ⊆ F₂` plus the explicit
precision bound `2 ≤ F₂.p`. -/

/-- The RTO-rounding of a non-negative `x` is non-negative (uses faithfulness:
either disjunct of `IsFaithfulRound` forces `0 ≤ z` when `0 ≤ x`). -/
private theorem toOdd_nonneg_of_nn {F : FiniteFormat} {x : ℝ} {z : Dyadic}
    (hx : 0 ≤ x) (h : RoundsFinite F .toOdd x z) : 0 ≤ (z : ℝ) := by
  obtain ⟨_, hfaithful, _⟩ := h
  rcases hfaithful with hRD | hRU
  · obtain ⟨_, _, hz_max⟩ := hRD
    have := hz_max 0 F.zero_mem (by rw [Dyadic.coe_real_zero]; exact hx)
    rwa [Dyadic.coe_real_zero] at this
  · linarith [hRU.2.1]

/-- **RTO-padding lemma, applied form.** If `z` is the RTO-rounding of `x` in `F₂`
(with `x ≠ z`, hence `z` is `F₂`-odd) and `F₁` assigns `z` strictly fewer
digits than `F₂`, then `z ∉ F₁`: an `F₁`-representable value would have
precision below the rounding precision, contradicting oddness via
`precisionAtMost_not_IsOdd`. -/
private theorem toOdd_notMem_of_lower_numDigits {F₁ F₂ : FiniteFormat}
    {z : Dyadic}
    {F₂' : ParityFormat} (hF₂'eq : F₂'.toFormat = F₂.toFormat) (hodd : F₂'.IsOdd z)
    (hlt : F₁.numDigits (z : ℝ) < F₂.numDigits (z : ℝ)) :
    z ∉ F₁ := by
  intro hzF₁
  -- `z ≠ 0` (so numDigits is positive), and `numDigits F₁ z ≥ 1`.
  have hz_ne_real : (z : ℝ) ≠ 0 := by
    intro h
    have hz_d : z = 0 := eq_zero_of_coe_real_zero h
    rw [hz_d] at hodd
    exact hodd.ne_zero rfl
  have h_F₁_ge_1 : 1 ≤ F₁.numDigits (z : ℝ) := F₁.numDigits_nonneg z hzF₁ hz_ne_real
  -- Package `z`'s `F₁`-precision as `precisionAtMost (numDigits F₁ z).toNat`.
  set n : ℕ := (F₁.numDigits (z : ℝ)).toNat with hn_def
  have hn_eq : (n : ℤ) = F₁.numDigits (z : ℝ) := Int.toNat_of_nonneg (by linarith)
  have hn_pos : 1 ≤ n := by
    have : (1 : ℤ) ≤ (n : ℤ) := by rw [hn_eq]; exact h_F₁_ge_1
    exact_mod_cast this
  obtain ⟨c, e, hz_rep_real, hc_bound⟩ :=
    F₁.mem_imp_precisionAtMost_numDigits hzF₁ hz_ne_real
  have h_prec : Dyadic.precisionAtMost (n : Prec) z := by
    rw [Dyadic.precisionAtMost_coe_real]
    exact ⟨c, e, hz_rep_real, hc_bound⟩
  -- `numDigits F₂' z = numDigits F₂ z` (same underlying format), and it exceeds `w`.
  have hF₂'_nd : F₂'.toFiniteFormat.numDigits (z : ℝ) = F₂.numDigits (z : ℝ) := by
    unfold FiniteFormat.numDigits
    rw [show F₂'.toFiniteFormat.toFormat = F₂'.toFormat from rfl, hF₂'eq]
  have hgt : (n : ℤ) < F₂'.toFiniteFormat.numDigits (z : ℝ) := by
    rw [hF₂'_nd, hn_eq]; exact hlt
  exact F₂'.precisionAtMost_not_IsOdd hn_pos hgt h_prec hodd

/-- **RTO-padding lemma, paper form (simpler hypothesis).** From `F₁.extend 1 ⊆ F₂`,
`2 ≤ F₂.p`, and an RTO rounding `z` of `x` in `F₂` with `x ≠ z`, conclude
`z ∉ F₁`.

Proof: `z ∈ F₁ ⟹ z ∈ F₁.extend 1`; then `numDigits_eq_of_subset_of_isOdd`
gives `numDigits (F₁.extend 1) z = numDigits F₂ z`, and `numDigits_extend`
gives the LHS `= numDigits F₁ z + 1`, so `numDigits F₁ z < numDigits F₂ z`,
contradicting `toOdd_notMem_of_lower_numDigits`. -/
theorem toOdd_notMem_of_extend_subset {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {x : ℝ} {z : Dyadic} (hz : RoundsFinite F₂ .toOdd x z)
    (hxne : x ≠ (z : ℝ)) :
    z ∉ F₁ := by
  intro hzF₁
  -- Extract `F₂`-oddness of `z` (as a `ParityFormat` witness over `F₂`).
  obtain ⟨_, _, hz_odd_imp⟩ := hz
  obtain ⟨F₂', hF₂'eq, hF₂'odd⟩ := hz_odd_imp hxne
  have hz_ne_real : (z : ℝ) ≠ 0 := by
    intro h
    have hz_d : z = 0 := eq_zero_of_coe_real_zero h
    rw [hz_d] at hF₂'odd
    exact hF₂'odd.ne_zero rfl
  -- `z ∈ F₁ ⟹ z ∈ F₁.extend 1`.
  have hzF₁_ext : z ∈ (F₁.extend 1) := Format.self_subset_extend F₁.toFormat 1 z hzF₁
  -- numDigits agreement at `F₁.extend 1`.
  have hsub' : (F₁.extend 1).toFormat ⊆ F₂'.toFormat := by rw [hF₂'eq]; exact hsub
  have hp_F₂' : ((2 : ℕ) : Prec) ≤ F₂'.p := by rw [hF₂'eq]; exact hp_F₂
  have h_eq : (F₁.extend 1).numDigits (z : ℝ) = F₂'.toFiniteFormat.numDigits (z : ℝ) :=
    numDigits_eq_of_subset_of_isOdd hsub' hp_F₂' hzF₁_ext hF₂'odd
  rw [F₁.numDigits_extend 1 hz_ne_real] at h_eq
  -- `numDigits F₂' z = numDigits F₂ z`.
  have hF₂'_nd : F₂'.toFiniteFormat.numDigits (z : ℝ) = F₂.numDigits (z : ℝ) := by
    unfold FiniteFormat.numDigits
    rw [show F₂'.toFiniteFormat.toFormat = F₂'.toFormat from rfl, hF₂'eq]
  rw [hF₂'_nd] at h_eq
  -- `numDigits F₁ z + 1 = numDigits F₂ z`, so the strict inequality holds.
  have hlt : F₁.numDigits (z : ℝ) < F₂.numDigits (z : ℝ) := by
    omega
  exact (toOdd_notMem_of_lower_numDigits hF₂'eq hF₂'odd hlt) hzF₁

/-- If `F₁` is trivial (contains only `0`) and `w' ∈ F₁`, then
`RoundsFinite F₁ .toZero x w'` holds for any real `x` (since `w' = 0`). -/
private theorem RoundsFinite.toZero_of_trivial {F₁ : FiniteFormat}
    (hF₁_triv : ∀ d : Dyadic, d ∈ F₁ → (d : ℝ) = 0)
    {x : ℝ} {w' : Dyadic} (hw : w' ∈ F₁) :
    RoundsFinite F₁ .toZero x w' := by
  have hw'_zero : (w' : ℝ) = 0 := hF₁_triv w' hw
  refine ⟨hw, ?_, ?_, ?_⟩
  · rw [hw'_zero, abs_zero]; exact abs_nonneg _
  · rw [hw'_zero, zero_mul]
  · intro v hvF₁ _ _
    have hv_zero : (v : ℝ) = 0 := hF₁_triv v hvF₁
    rw [hv_zero, hw'_zero]

/-- If `F₁` is trivial, the chained RAZ rounding forces `x = 0`, so the
conclusion `RoundsFinite F₁ .awayZero x w'` reduces to the trivial RAZ at zero.
The forcing comes from RTO's parity clause: with `z = 0` (the only F₁ image),
`x ≠ 0` would require `F₂`-oddness of `0`, which is impossible. -/
private theorem RoundsFinite.awayZero_of_trivial {F₁ F₂ : FiniteFormat}
    (hF₁_triv : ∀ d : Dyadic, d ∈ F₁ → (d : ℝ) = 0)
    {x : ℝ} {z w' : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .awayZero (z : ℝ) w') :
    RoundsFinite F₁ .awayZero x w' := by
  have hw'F₁ : w' ∈ F₁ := hw.1
  have hw'_zero : (w' : ℝ) = 0 := hF₁_triv w' hw'F₁
  -- awayZero clause: |(z:ℝ)| ≤ |(w':ℝ)| = 0, so z = 0.
  have hz_zero_real : (z : ℝ) = 0 := by
    have h0 : |(z : ℝ)| ≤ 0 := hw.2.1.trans (by rw [hw'_zero, abs_zero])
    exact abs_nonpos_iff.mp h0
  have hz_zero : z = 0 := eq_zero_of_coe_real_zero hz_zero_real
  have hx_zero : x = 0 := by
    obtain ⟨_, _, hz_odd_imp⟩ := hz
    by_contra hxne
    have hxne_z : x ≠ (z : ℝ) := by rw [hz_zero_real]; exact hxne
    obtain ⟨F', _, hodd⟩ := hz_odd_imp hxne_z
    rw [hz_zero] at hodd
    exact hodd.ne_zero rfl
  refine ⟨hw'F₁, ?_, ?_, ?_⟩
  · rw [hx_zero, hw'_zero]
  · rw [hx_zero, hw'_zero, mul_zero]
  · intro v hvF₁ _ _
    rw [hF₁_triv v hvF₁, hw'_zero]

/-- **rnd-RTO-RTZ**, positive case `0 < x`. -/
private theorem roundsRTO_RTZ_finite_pos {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {x : ℝ} (hx_pos : 0 < x) {z w' : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toZero (z : ℝ) w') :
    RoundsFinite F₁ .toZero x w' := by
  -- `F₁ ⊆ F₁.extend 1 ⊆ F₂`.
  have hsub' : F₁.toFormat ⊆ F₂.toFormat :=
      Format.subset_of_mem hsub.specials fun y hy =>
    hsub y (Format.self_subset_extend F₁.toFormat 1 y hy)
  have hz_nn : 0 ≤ (z : ℝ) := toOdd_nonneg_of_nn hx_pos.le hz
  obtain ⟨hzF₂, hz_adj, hz_odd_imp⟩ := hz
  obtain ⟨hw'F₁, hw'_bnd_z, hw'_sign_z, hw'_max⟩ := hw
  have hx_abs : |x| = x := abs_of_pos hx_pos
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
      have hz_full : RoundsFinite F₂ .toOdd x z := ⟨hzF₂, Or.inr hRU, hz_odd_imp⟩
      have hzF₁ : z ∈ F₁ := by
        rw [show z = w' from (Dyadic.coe_real_inj z w').mp hw'_eq_z.symm]
        exact hw'F₁
      exact (toOdd_notMem_of_extend_subset hsub hp_F₂ hz_full hxne) hzF₁
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

/-- **rnd-RTO-RTZ** under `F₁.extend 1 ⊆ F₂` and `2 ≤ F₂.p`, without the relaxed
bound. -/
theorem roundsRTO_RTZ_finite_of_extend {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {x : ℝ} {z w' : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toZero (z : ℝ) w') :
    RoundsFinite F₁ .toZero x w' := by
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · -- x < 0: negate, apply the positive case, negate back.
    have hx_pos' : 0 < (-x) := by linarith
    have hz' : RoundsFinite F₂ .toOdd (-x) (-z) :=
      (RoundsFinite.neg_toOdd F₂ x z).mp hz
    have hw' : RoundsFinite F₁ .toZero ((-z : Dyadic) : ℝ) (-w') := by
      rw [Dyadic.coe_real_neg]; exact (RoundsFinite.neg_toZero F₁ (z : ℝ) w').mp hw
    have h_result := roundsRTO_RTZ_finite_pos hsub hp_F₂ hx_pos' hz' hw'
    have hfinal := (RoundsFinite.neg_toZero F₁ (-x) (-w')).mp h_result
    rwa [neg_neg, neg_neg] at hfinal
  · -- x = 0: forces z = 0 and w' = 0.
    subst hx_zero
    have hz_zero : z = 0 := RoundsFinite.eq_zero_of_zero hz
    rw [hz_zero] at hw
    obtain ⟨hw'F₁, hw'_bnd, _, _⟩ := hw
    have hw'_zero : (w' : ℝ) = 0 := by
      rw [Dyadic.coe_real_zero, abs_zero] at hw'_bnd
      exact abs_nonpos_iff.mp hw'_bnd
    refine ⟨hw'F₁, ?_, ?_, ?_⟩
    · simp [hw'_zero]
    · simp [hw'_zero]
    · intro v _ hv_bnd _
      rw [hw'_zero, abs_zero]
      simpa using hv_bnd
  · exact roundsRTO_RTZ_finite_pos hsub hp_F₂ hx_pos hz hw

/-- **rnd-RTO-RTZ** under the relaxed containment; `2 ≤ F₂.p` follows unless `F₁`
is trivial. -/
theorem roundsRTO_RTZ_finite {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {x : ℝ} {z w' : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toZero (z : ℝ) w') :
    RoundsFinite F₁ .toZero x w' := by
  rcases two_le_p_or_trivial_of_extend_one_withBound_subset hsub with hp_F₂ | hF₁_triv
  · exact roundsRTO_RTZ_finite_of_extend (extend_one_subset_of_withBound_subset hsub) hp_F₂
      hz hw
  · -- trivial case: F₁ = {0}.
    exact RoundsFinite.toZero_of_trivial hF₁_triv hw.1

/-- **rnd-RTO-RAZ**, positive case `0 < x`. Symmetric to
`roundsRTO_RTZ_finite_pos` but for round-away-from-zero. The key RTO-padding application
(`toOdd_notMem_of_extend_subset`) happens in the ToNegative (RTN / round-down)
branch of `z` rather than the ToPositive (RTP) branch. -/
private theorem roundsRTO_RAZ_finite_pos {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {x : ℝ} (hx_pos : 0 < x) {z w' : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .awayZero (z : ℝ) w') :
    RoundsFinite F₁ .awayZero x w' := by
  -- `F₁ ⊆ F₁.extend 1 ⊆ F₂`.
  have hsub' : F₁.toFormat ⊆ F₂.toFormat :=
      Format.subset_of_mem hsub.specials fun y hy =>
    hsub y (Format.self_subset_extend F₁.toFormat 1 y hy)
  have hz_nn : 0 ≤ (z : ℝ) := toOdd_nonneg_of_nn hx_pos.le hz
  obtain ⟨hzF₂, hz_adj, hz_odd_imp⟩ := hz
  obtain ⟨hw'F₁, hw'_bnd_z, hw'_sign_z, hw'_min⟩ := hw
  have hx_abs : |x| = x := abs_of_pos hx_pos
  have hz_abs : |(z : ℝ)| = (z : ℝ) := abs_of_nonneg hz_nn
  rw [hz_abs] at hw'_bnd_z
  -- |w'| ≥ |x| via the contradiction in the ToNegative (RTN) branch using
  -- `toOdd_notMem_of_extend_subset`.
  have hw'_nn : 0 ≤ (w' : ℝ) := by
    rcases lt_or_eq_of_le hz_nn with hzpos | hzeq
    · nlinarith [hw'_sign_z]
    · -- z = 0, so |w'| ≥ 0 trivially; we still need a sign. From hw'_sign_z,
      -- w' * z ≥ 0 with z = 0 gives nothing, but |x| ≤ |w'| forces nothing either.
      -- Use the min clause: 0 ∈ F₁ with |z| = 0 ≤ |0| and 0 * z ≥ 0.
      have h0 : |(w' : ℝ)| ≤ |((0 : Dyadic) : ℝ)| :=
        hw'_min 0 F₁.zero_mem (by rw [Dyadic.coe_real_zero, abs_zero]; rw [← hzeq]; simp)
          (by rw [Dyadic.coe_real_zero]; ring_nf; rfl)
      rw [Dyadic.coe_real_zero, abs_zero] at h0
      have : (w' : ℝ) = 0 := abs_nonpos_iff.mp h0
      linarith
  have hw'_abs : |(w' : ℝ)| = (w' : ℝ) := abs_of_nonneg hw'_nn
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
      have hz_full : RoundsFinite F₂ .toOdd x z := ⟨hzF₂, Or.inl hRD, hz_odd_imp⟩
      have hzF₁ : z ∈ F₁ := by
        rw [show z = w' from (Dyadic.coe_real_inj z w').mp hw'_eq_z.symm]
        exact hw'F₁
      exact (toOdd_notMem_of_extend_subset hsub hp_F₂ hz_full hxne) hzF₁
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

/-- **rnd-RTO-RAZ** under `F₁.extend 1 ⊆ F₂` and `2 ≤ F₂.p`, without the relaxed
bound. -/
theorem roundsRTO_RAZ_finite_of_extend {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {x : ℝ} {z w' : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .awayZero (z : ℝ) w') :
    RoundsFinite F₁ .awayZero x w' := by
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · -- x < 0: negate, apply the positive case, negate back.
    have hx_pos' : 0 < (-x) := by linarith
    have hz' : RoundsFinite F₂ .toOdd (-x) (-z) :=
      (RoundsFinite.neg_toOdd F₂ x z).mp hz
    have hw' : RoundsFinite F₁ .awayZero ((-z : Dyadic) : ℝ) (-w') := by
      rw [Dyadic.coe_real_neg]; exact (RoundsFinite.neg_awayZero F₁ (z : ℝ) w').mp hw
    have h_result := roundsRTO_RAZ_finite_pos hsub hp_F₂ hx_pos' hz' hw'
    have hfinal := (RoundsFinite.neg_awayZero F₁ (-x) (-w')).mp h_result
    rwa [neg_neg, neg_neg] at hfinal
  · -- x = 0: forces z = 0 and w' = 0.
    subst hx_zero
    have hz_zero : z = 0 := RoundsFinite.eq_zero_of_zero hz
    rw [hz_zero] at hw
    obtain ⟨hw'F₁, _, _, hw'_min⟩ := hw
    have h_min := hw'_min 0 F₁.zero_mem (le_refl _) (by simp)
    have hw'_zero : (w' : ℝ) = 0 := by
      rw [Dyadic.coe_real_zero, abs_zero] at h_min
      exact abs_nonpos_iff.mp h_min
    refine ⟨hw'F₁, ?_, ?_, ?_⟩
    · simp [hw'_zero]
    · simp [hw'_zero]
    · intro v _ _ _
      simp [hw'_zero, abs_nonneg]
  · exact roundsRTO_RAZ_finite_pos hsub hp_F₂ hx_pos hz hw

/-- **rnd-RTO-RAZ** under the relaxed containment; `2 ≤ F₂.p` follows unless `F₁`
is trivial. -/
theorem roundsRTO_RAZ_finite {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {x : ℝ} {z w' : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .awayZero (z : ℝ) w') :
    RoundsFinite F₁ .awayZero x w' := by
  rcases two_le_p_or_trivial_of_extend_one_withBound_subset hsub with hp_F₂ | hF₁_triv
  · exact roundsRTO_RAZ_finite_of_extend (extend_one_subset_of_withBound_subset hsub) hp_F₂
      hz hw
  · -- trivial case: F₁ = {0}.
    exact RoundsFinite.awayZero_of_trivial hF₁_triv hz hw

/-- **rnd-RTP-RTP** (round toward `+∞`, chained). For `x > 0` it is RAZ→RAZ
(`roundsRAZ_RAZ_finite_pos`); for `x ≤ 0` it is RTZ→RTZ (`roundsRTZ_RTZ_finite`). The two regimes
are connected to RTP through the sign-bridge iff lemmas. Only needs `F₁ ⊆ F₂`. -/
theorem roundsRTP_RTP_finite {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toPositive x z) (hw : RoundsFinite F₁ .toPositive (z : ℝ) w) :
    RoundsFinite F₁ .toPositive x w := by
  by_cases hx_le : x ≤ 0
  · -- x ≤ 0: bridge to RTZ.
    have hz_le_0 : (z : ℝ) ≤ 0 := by
      have := hz.2.2 0 F₂.zero_mem (by rw [Dyadic.coe_real_zero]; exact hx_le)
      rwa [Dyadic.coe_real_zero] at this
    have hz_RTZ : RoundsFinite F₂ .toZero x z :=
      (RoundsFinite.toPositive_iff_toZero_of_nonpos F₂ hx_le z).mp hz
    have hw_RTZ : RoundsFinite F₁ .toZero (z : ℝ) w :=
      (RoundsFinite.toPositive_iff_toZero_of_nonpos F₁ hz_le_0 w).mp hw
    exact (RoundsFinite.toPositive_iff_toZero_of_nonpos F₁ hx_le w).mpr
      (roundsRTZ_RTZ_finite hsub hz_RTZ hw_RTZ)
  · -- x > 0: bridge to RAZ.
    have hx_pos : 0 < x := not_le.mp hx_le
    have hz_nn : 0 ≤ (z : ℝ) := le_trans hx_pos.le hz.2.1
    have hz_RAZ : RoundsFinite F₂ .awayZero x z :=
      (RoundsFinite.toPositive_iff_awayZero_of_nonneg F₂ hx_pos.le z).mp hz
    have hw_RAZ : RoundsFinite F₁ .awayZero (z : ℝ) w :=
      (RoundsFinite.toPositive_iff_awayZero_of_nonneg F₁ hz_nn w).mp hw
    exact (RoundsFinite.toPositive_iff_awayZero_of_nonneg F₁ hx_pos.le w).mpr
      (roundsRAZ_RAZ_finite_pos hsub hx_pos hz_RAZ hw_RAZ)

/-- **rnd-RTN-RTN** (round toward `−∞`, chained). For `x < 0` it is RAZ→RAZ
(`roundsRAZ_RAZ_finite`); for `x ≥ 0` it is RTZ→RTZ (`roundsRTZ_RTZ_finite`), connected to RTN via
the sign-bridge iff lemmas. Only needs `F₁ ⊆ F₂`. -/
theorem roundsRTN_RTN_finite {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toNegative x z) (hw : RoundsFinite F₁ .toNegative (z : ℝ) w) :
    RoundsFinite F₁ .toNegative x w := by
  by_cases hx_neg : x < 0
  · -- x < 0: bridge to RAZ.
    have hx_le : x ≤ 0 := hx_neg.le
    have hz_le_0 : (z : ℝ) ≤ 0 := le_trans hz.2.1 hx_le
    have hz_RAZ : RoundsFinite F₂ .awayZero x z :=
      (RoundsFinite.toNegative_iff_awayZero_of_nonpos F₂ hx_le z).mp hz
    have hw_RAZ : RoundsFinite F₁ .awayZero (z : ℝ) w :=
      (RoundsFinite.toNegative_iff_awayZero_of_nonpos F₁ hz_le_0 w).mp hw
    exact (RoundsFinite.toNegative_iff_awayZero_of_nonpos F₁ hx_le w).mpr
      (roundsRAZ_RAZ_finite hsub hz_RAZ hw_RAZ)
  · -- x ≥ 0: bridge to RTZ.
    have hx_nn : 0 ≤ x := not_lt.mp hx_neg
    have hz_nn : 0 ≤ (z : ℝ) := by
      have := hz.2.2 0 F₂.zero_mem (by rw [Dyadic.coe_real_zero]; exact hx_nn)
      rwa [Dyadic.coe_real_zero] at this
    have hz_RTZ : RoundsFinite F₂ .toZero x z :=
      (RoundsFinite.toNegative_iff_toZero_of_nonneg F₂ hx_nn z).mp hz
    have hw_RTZ : RoundsFinite F₁ .toZero (z : ℝ) w :=
      (RoundsFinite.toNegative_iff_toZero_of_nonneg F₁ hz_nn w).mp hw
    exact (RoundsFinite.toNegative_iff_toZero_of_nonneg F₁ hx_nn w).mpr
      (roundsRTZ_RTZ_finite hsub hz_RTZ hw_RTZ)

end Mpfx
