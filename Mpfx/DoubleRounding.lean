import Mpfx.Digits
import Mpfx.Grid
import Mpfx.Rounding
import Mpfx.RoundOp

/-!
# Correct double rounding (§5.2, Fig. 9)

The double-rounding rules, in two layers:

* **`RoundsFinite` layer** (`rndRTZ_RTZ`, …): stated *spec-relationally* —
  given that `z` is the rounding of `x` in `F₂` and `w` is the rounding of
  `z` in `F₁` (with `F₁ ⊆ F₂`), conclude that `w` is also the rounding of
  `x` in `F₁` directly. Stated over `RoundsFinite` (membership + mode
  condition, no separate bound check), the spec-relational analog of the
  paper's `rnd`-relation; overflow bookkeeping is sidestepped and the
  existence of `z`, `w` is taken as hypotheses.

* **`Rounds` layer** (`roundsRTZ_RTZ`, …, one per Fig. 9 rule): the full,
  overflow-aware form. Given finite results for both roundings of the chain,
  conclude that either rounding `x` directly in `F₁` *overflows*, or `w` is
  the (finite) direct rounding of `x` in `F₁`. The overflow disjunct is
  genuine: the containment hypotheses constrain only the *bounded* formats,
  so the unbounded `F₁`-grid may contain out-of-bound values closer to `x`
  than anything the chained rounding sees. The paper's side condition ("the
  rules hold whenever `rnd_{F₁}(x)` does not overflow") is exactly the right
  disjunct's guard, decided here by the total unbounded rounding
  `rndUnbounded` from `Mpfx/RoundOp`.
-/

namespace Mpfx

/-- **rnd-RTZ-RTZ** (Fig. 9). Chained round-toward-zero collapses: if
`F₁ ⊆ F₂`, `z` is the RTZ-rounding of `x` in `F₂`, and `w` is the RTZ-rounding
of `z` in `F₁`, then `w` is the RTZ-rounding of `x` in `F₁`. -/
theorem rndRTZ_RTZ {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
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

/-- **rnd-RAZ-RAZ** (Fig. 9), case `0 < x`. The general theorem follows by
sign-symmetry and the `x = 0` case. -/
theorem rndRAZ_RAZ_pos {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
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

/-- **rnd-RAZ-RAZ** (Fig. 9). General version. Combines the positive case,
the negative case (via `RoundsFinite.neg_awayZero`), and the `x = 0` case. -/
theorem rndRAZ_RAZ {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .awayZero x z) (hw : RoundsFinite F₁ .awayZero (z : ℝ) w) :
    RoundsFinite F₁ .awayZero x w := by
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · -- x < 0: flip via sign-symmetry, apply the positive case, flip back.
    have hz' : RoundsFinite F₂ .awayZero (-x) (-z) :=
      (RoundsFinite.neg_awayZero F₂ x z).mp hz
    have hw' : RoundsFinite F₁ .awayZero ((-z : Dyadic) : ℝ) (-w) := by
      rw [Dyadic.coe_real_neg]; exact (RoundsFinite.neg_awayZero F₁ (z : ℝ) w).mp hw
    have hresult := rndRAZ_RAZ_pos hsub (neg_pos.mpr hx_neg) hz' hw'
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
  · exact rndRAZ_RAZ_pos hsub hx_pos hz hw

-- `FiniteFormat.toParityFormatOfToOdd` (promotion of `F : FiniteFormat` to
-- `ParityFormat` from a `¬ IsUndefined .toOdd` witness) is provided by
-- `Mpfx/RoundOp/Defs.lean`.

/-- If `F₁ ⊆ F₂`, `F₁.exp = ⊥`, and `F₁` contains a nonzero element `z`, then
`F₂.exp = ⊥` as well: an `exp = ⊥` (unbounded-quantum) format embeds values of
arbitrarily small quantum, which a finite-`exp` `F₂` cannot represent. -/
private theorem exp_bot_of_subset {F₁ F₂ : FiniteFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat) (hexp₁ : F₁.exp = ⊥)
    {z : Dyadic} (hzF₁ : z ∈ F₁) (hz_ne : z ≠ 0) :
    F₂.exp = ⊥ := by
  by_contra hF₂_exp
  -- F₂.exp = (e' : ℤ).
  obtain ⟨e', he'⟩ : ∃ e' : ℤ, F₂.exp = (e' : WithBot ℤ) := by
    cases hc : F₂.exp with
    | bot => exact absurd hc hF₂_exp
    | coe e' => exact ⟨e', rfl⟩
  -- A bound `2^k ≤ |z|` on the witness magnitude (so it stays within F₁.b).
  have hz_ne_q : (z : ℚ) ≠ 0 := by
    intro h; exact hz_ne (Subtype.ext (by rw [h]; rfl))
  set k : ℤ := min (e' - 1) (Int.log 2 |(z : ℚ)|) with hk_def
  have hk_le_e' : k ≤ e' - 1 := min_le_left _ _
  have hk_le_log : k ≤ Int.log 2 |(z : ℚ)| := min_le_right _ _
  -- The witness `w = 2^k`.
  set w : Dyadic := Dyadic.ofIntZpow 1 k with hw_def
  have hw_q : (w : ℚ) = (2 : ℚ) ^ k := by
    rw [hw_def, Dyadic.coe_rat_ofIntZpow]; push_cast; ring
  have h2k_pos : (0 : ℚ) < (2 : ℚ) ^ k := zpow_pos (by norm_num) _
  -- `w ∈ F₁`.
  have hwF₁ : w ∈ F₁ := by
    refine ⟨?_, ?_, ?_⟩
    · -- precision: c = 1, |1| < 2^p₁.
      cases hp₁ : F₁.p with
      | top => exact trivial
      | coe p₁ =>
        rw [Dyadic.precisionAtMost_coe]
        refine ⟨1, k, by rw [hw_q]; push_cast; ring, ?_⟩
        have hp_pos : 1 ≤ (p₁ : ℕ) := p₁.pos
        have : (2 : ℤ) ^ 1 ≤ (2 : ℤ) ^ (p₁ : ℕ) :=
          pow_le_pow_right₀ (by norm_num) hp_pos
        simp only [abs_one]
        omega
    · rw [hexp₁]; exact trivial
    · -- bound: |w| = 2^k ≤ |z| ≤ F₁.b.
      have hzbnd : Format.boundOK F₁.b z := hzF₁.2.2
      have h2k_le_z : (2 : ℚ) ^ k ≤ |(z : ℚ)| := by
        have hlog_le : (2 : ℚ) ^ (Int.log 2 |(z : ℚ)|) ≤ |(z : ℚ)| :=
          Int.zpow_log_le_self (by norm_num) (abs_pos.mpr hz_ne_q)
        calc (2 : ℚ) ^ k ≤ (2 : ℚ) ^ (Int.log 2 |(z : ℚ)|) :=
              zpow_le_zpow_right₀ (by norm_num) hk_le_log
          _ ≤ |(z : ℚ)| := hlog_le
      have hzbnd' : Format.boundOK F₁.b z := hzbnd
      rcases hb : F₁.b with _ | b
      · trivial
      · rw [hb] at hzbnd'
        change |(w : ℚ)| ≤ ((b.val : Dyadic) : ℚ)
        simp only [Format.boundOK] at hzbnd'
        rw [hw_q, abs_of_pos h2k_pos]
        linarith
  -- But `w ∉ F₂`: quantum constraint fails since `k < e'`.
  have hwF₂ := hsub w hwF₁
  have hwq₂ : Dyadic.quantumAtLeast F₂.exp w := hwF₂.2.1
  rw [he', Dyadic.quantumAtLeast_coe] at hwq₂
  obtain ⟨c, hc⟩ := hwq₂
  rw [hw_q] at hc
  -- `2^k = c · 2^{e'}` ⇒ `c = 2^{k - e'}`, impossible for `k - e' < 0`.
  have h2e'_pos : (0 : ℚ) < (2 : ℚ) ^ e' := zpow_pos (by norm_num) _
  have hc_eq : (c : ℚ) = (2 : ℚ) ^ (k - e') := by
    rw [zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0)]
    rw [eq_div_iff (ne_of_gt h2e'_pos)]
    linarith [hc]
  have hk_lt_e' : k - e' < 0 := by omega
  have h_lt_one : (2 : ℚ) ^ (k - e') < 1 :=
    zpow_lt_one_of_neg₀ (a := (2 : ℚ)) (by norm_num) hk_lt_e'
  have h_pos : (0 : ℚ) < (2 : ℚ) ^ (k - e') := zpow_pos (by norm_num) _
  have hc_pos : (0 : ℚ) < (c : ℚ) := hc_eq ▸ h_pos
  have hc_lt1 : (c : ℚ) < 1 := hc_eq ▸ h_lt_one
  have hc_pos_int : (0 : ℤ) < c := by exact_mod_cast hc_pos
  have hc_lt1_int : c < 1 := by exact_mod_cast hc_lt1
  omega

/-- **rnd-RTO-RTO** (Fig. 9), general case `x ∈ ℝ`.

Restricted to `F₂.p ≥ 2`. -/
theorem rndRTO_RTO {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ+) : WithTop ℕ+) ≤ F₂.p)
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
      -- its F₁-oddness comes from F₂-oddness via Lemma 5.3 transfer.
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
          have hF₂'_exp_bot : F₂'.exp = ⊥ :=
            exp_bot_of_subset (hF₂'eq ▸ hsub) hexp_bot hw'F₁ hz_ne
          obtain ⟨p₂, hp₂⟩ : ∃ p₂ : ℕ+, F₂'.p = ((p₂ : ℕ+) : WithTop ℕ+) := by
            cases hc : F₂'.p with
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
            have : ((2 : ℕ+) : WithTop ℕ+) ≤ ((p₂ : ℕ+) : WithTop ℕ+) := hp₂ ▸ (hF₂'eq ▸ hp_F₂)
            have h2 : ((2 : ℕ+) : ℕ) ≤ ((p₂ : ℕ+) : ℕ) := by exact_mod_cast this
            simpa using (by exact_mod_cast h2 : (2 : ℤ) ≤ (p₂ : ℤ))
          rw [h_F₁_eq_1, h_F₂_eq_p₂] at h_eq
          omega
        set F₁' := F₁.toParityFormatOfToOdd h_not_undef with hF₁'_def
        have hF₁'eq : F₁'.toFormat = F₁.toFormat := rfl
        have hF₁'odd : F₁'.IsOdd z := by
          have h_iod_F₂' : F₂'.IsOdd z := hF₂'odd
          have h_F₁'F₂' : F₁'.toFormat ⊆ F₂'.toFormat := by
            rw [hF₁'eq, hF₂'eq]; exact hsub
          have h_p_F₂' : ((2 : ℕ+) : WithTop ℕ+) ≤ F₂'.p := by
            rw [hF₂'eq]; exact hp_F₂
          have hz_mem : z ∈ F₁'.toFiniteFormat := hw'F₁
          exact IsOdd.transfer_of_subset h_F₁'F₂' h_p_F₂' hz_mem h_iod_F₂'
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

/-! ## `rnd-RTO-RTZ` (Fig. 9)

Chain: an RTO rounding `z` of `x` in the wider `F₂`, then an RTZ rounding `w'`
of `z` in `F₁`, collapses to a single RTZ rounding of `x` in `F₁`. Uses the
simpler containment hypothesis `F₁.extend 1 ⊆ F₂` plus the explicit
precision bound `2 ≤ F₂.p`. -/

/-- The RTO-rounding of `0` in any (finite) format is `0` itself: the only
faithful rounding of `0` is `0`, since `0 ∈ F`. -/
private theorem toOdd_eq_zero_of_zero {F : FiniteFormat} {z : Dyadic}
    (h : RoundsFinite F .toOdd 0 z) : z = 0 := by
  obtain ⟨_, hfaithful, _⟩ := h
  have hz_eq : (z : ℝ) = 0 := by
    rcases hfaithful with hRD | hRU
    · obtain ⟨_, hz_le, hz_max⟩ := hRD
      have h0 : ((0 : Dyadic) : ℝ) ≤ (z : ℝ) := by
        have := hz_max 0 F.zero_mem (le_of_eq (by rw [Dyadic.coe_real_zero]))
        rwa [Dyadic.coe_real_zero] at this ⊢
      rw [Dyadic.coe_real_zero] at h0
      linarith
    · obtain ⟨_, hle, hz_min⟩ := hRU
      have h0 : (z : ℝ) ≤ ((0 : Dyadic) : ℝ) := by
        have := hz_min 0 F.zero_mem (le_of_eq (by rw [Dyadic.coe_real_zero]))
        rwa [Dyadic.coe_real_zero] at this ⊢
      rw [Dyadic.coe_real_zero] at h0
      linarith
  exact (Dyadic.coe_real_inj z 0).mp (by rw [hz_eq, Dyadic.coe_real_zero])

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

/-- **Lemma 5.3, applied form.** If `z` is the RTO-rounding of `x` in `F₂`
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
    have hz_d : z = 0 := (Dyadic.coe_real_inj z 0).mp (by rw [h, Dyadic.coe_real_zero])
    rw [hz_d] at hodd
    exact hodd.ne_zero rfl
  have h_F₁_ge_1 : 1 ≤ F₁.numDigits (z : ℝ) := F₁.numDigits_nonneg z hzF₁ hz_ne_real
  -- Package `z`'s `F₁`-precision as `precisionAtMost (numDigits F₁ z).toNat`.
  set n : ℕ := (F₁.numDigits (z : ℝ)).toNat with hn_def
  have hn_eq : (n : ℤ) = F₁.numDigits (z : ℝ) := Int.toNat_of_nonneg (by linarith)
  have hn_pos : 1 ≤ n := by
    have : (1 : ℤ) ≤ (n : ℤ) := by rw [hn_eq]; exact h_F₁_ge_1
    exact_mod_cast this
  set w : ℕ+ := ⟨n, hn_pos⟩ with hw_def
  have hw_val : ((w : ℕ+) : ℕ) = n := rfl
  obtain ⟨c, e, hz_rep_real, hc_bound⟩ :=
    F₁.mem_imp_precisionAtMost_numDigits hzF₁ hz_ne_real
  have hc_bound_w : |c| < (2 : ℤ) ^ ((w : ℕ+) : ℕ) := by rw [hw_val]; exact hc_bound
  have h_prec : Dyadic.precisionAtMost ((w : ℕ+) : WithTop ℕ+) z := by
    rw [Dyadic.precisionAtMost_coe_real]
    exact ⟨c, e, hz_rep_real, hc_bound_w⟩
  -- `numDigits F₂' z = numDigits F₂ z` (same underlying format), and it exceeds `w`.
  have hF₂'_nd : F₂'.toFiniteFormat.numDigits (z : ℝ) = F₂.numDigits (z : ℝ) := by
    unfold FiniteFormat.numDigits
    rw [show F₂'.toFiniteFormat.toFormat = F₂'.toFormat from rfl, hF₂'eq]
  have hgt : (((w : ℕ+) : ℕ) : ℤ) < F₂'.toFiniteFormat.numDigits (z : ℝ) := by
    rw [hF₂'_nd, hw_val, hn_eq]; exact hlt
  exact F₂'.precisionAtMost_not_IsOdd hgt h_prec hodd

/-- **Lemma 5.3, paper form (simpler hypothesis).** From `F₁.extend 1 ⊆ F₂`,
`2 ≤ F₂.p`, and an RTO rounding `z` of `x` in `F₂` with `x ≠ z`, conclude
`z ∉ F₁`.

Proof: `z ∈ F₁ ⟹ z ∈ F₁.extend 1`; then `numDigits_eq_of_subset_of_isOdd`
gives `numDigits (F₁.extend 1) z = numDigits F₂ z`, and `numDigits_extend`
gives the LHS `= numDigits F₁ z + 1`, so `numDigits F₁ z < numDigits F₂ z`,
contradicting `toOdd_notMem_of_lower_numDigits`. -/
private theorem toOdd_notMem_of_extend_subset {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ+) : WithTop ℕ+) ≤ F₂.p)
    {x : ℝ} {z : Dyadic} (hz : RoundsFinite F₂ .toOdd x z)
    (hxne : x ≠ (z : ℝ)) :
    z ∉ F₁ := by
  intro hzF₁
  -- Extract `F₂`-oddness of `z` (as a `ParityFormat` witness over `F₂`).
  obtain ⟨_, _, hz_odd_imp⟩ := hz
  obtain ⟨F₂', hF₂'eq, hF₂'odd⟩ := hz_odd_imp hxne
  have hz_ne_real : (z : ℝ) ≠ 0 := by
    intro h
    have hz_d : z = 0 := (Dyadic.coe_real_inj z 0).mp (by rw [h, Dyadic.coe_real_zero])
    rw [hz_d] at hF₂'odd
    exact hF₂'odd.ne_zero rfl
  -- `z ∈ F₁ ⟹ z ∈ F₁.extend 1`.
  have hzF₁_ext : z ∈ (F₁.extend 1) := Format.self_subset_extend F₁.toFormat 1 z hzF₁
  -- numDigits agreement at `F₁.extend 1`.
  have hsub' : (F₁.extend 1).toFormat ⊆ F₂'.toFormat := by rw [hF₂'eq]; exact hsub
  have hp_F₂' : ((2 : ℕ+) : WithTop ℕ+) ≤ F₂'.p := by rw [hF₂'eq]; exact hp_F₂
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
    have h1 : (1 : ℤ) ≤ ((1 : ℕ+) : ℤ) := by exact_mod_cast (1 : ℕ+).one_le
    omega
  exact (toOdd_notMem_of_lower_numDigits hF₂'eq hF₂'odd hlt) hzF₁

/-! ### Paper-form helpers (single bound-aware containment hypothesis)

The paper states `rnd-RTO-RTZ`/`rnd-RTO-RAZ` with a single containment
hypothesis `(F₁.extend 1).withBound F₁.boundAfterNext ⊆ F₂`, from which the
auxiliary `2 ≤ F₂.p` is *derived* (rather than assumed). These helpers bridge
the paper form to the `_pos` private bodies (which keep the simpler
`F₁.extend 1 ⊆ F₂` + `2 ≤ F₂.p` form). -/

/-- Given the paper-aligned containment
`(F₁.extend 1).withBound F₁.boundAfterNext ⊆ F₂`, derive the weaker
`F₁.extend 1 ⊆ F₂` form (used by the `_pos` private theorems). The bound
`F₁.boundAfterNext = next(F₁.b)` is at least as large as `F₁.b`, so any
`y ∈ F₁.extend 1` (whose bound is `F₁.b`) also satisfies the relaxed bound. -/
private theorem extend_one_subset_of_paper_subset {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat) :
    (F₁.extend 1).toFormat ⊆ F₂.toFormat := by
  intro y hy
  apply hsub
  obtain ⟨hp_y, hq_y, hb_y⟩ := hy
  refine ⟨hp_y, hq_y, ?_⟩
  -- goal: boundOK F₁.boundAfterNext y (withBound replaces only the bound).
  change Format.boundOK F₁.toFormat.boundAfterNext y
  cases hF_b : F₁.b with
  | top =>
    rw [Format.boundAfterNext_top hF_b]; trivial
  | coe b =>
    obtain ⟨h_nn, h_after⟩ := Format.boundAfterNext_coe hF_b
    rw [h_after]
    -- goal: |(y : ℚ)| ≤ ((F₁.next b.val : Dyadic) : ℚ).
    change |((y : Dyadic) : ℚ)| ≤ (((F₁.toFormat.next b.val : Dyadic)) : ℚ)
    -- y's own bound: |y| ≤ b.val (over ℚ), since (extend 1).b = F₁.b.
    change Format.boundOK (F₁.extend 1).b y at hb_y
    rw [show (F₁.extend 1).b = F₁.b from rfl, hF_b] at hb_y
    have h_y_le_b : |((y : Dyadic) : ℚ)| ≤ ((b.val : Dyadic) : ℚ) := hb_y
    -- b ≤ next(b) over ℝ; bridge to ℚ.
    have hb_nn : 0 ≤ ((b.val : Dyadic) : ℝ) := by
      rw [Dyadic.coe_real_eq_ratCast]; exact_mod_cast b.2
    have h_le_next : ((b.val : Dyadic) : ℝ) ≤ ((F₁.toFormat.next b.val : Dyadic) : ℝ) :=
      Format.self_le_next F₁.toFormat b.val hb_nn
    have h_le_next_q : ((b.val : Dyadic) : ℚ) ≤ ((F₁.toFormat.next b.val : Dyadic) : ℚ) := by
      rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast] at h_le_next
      exact_mod_cast h_le_next
    exact le_trans h_y_le_b h_le_next_q

/-- From the paper-aligned containment
`(F₁.extend 1).withBound F₁.boundAfterNext ⊆ F₂`, either `F₂.p ≥ 2` (the
auxiliary needed for Lemma 5.3) or `F₁` contains only `0`. The proof either
constructs a precision-2 witness `v = 3·2^k` lying in
`(F₁.extend 1).withBound F₁.boundAfterNext` (forcing `F₂.p ≥ 2` via
`two_le_p_of_precision_two_witness`), or shows `F₁` is trivial. The witness
exists exactly when `F₁` contains some nonzero element. -/
private theorem hp_F₂_or_F₁_trivial {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat) :
    ((2 : ℕ+) : WithTop ℕ+) ≤ F₂.p ∨ ∀ d : Dyadic, d ∈ F₁ → (d : ℝ) = 0 := by
  by_contra h
  push Not at h
  obtain ⟨h_p_lt, ⟨d, hd_mem, hd_ne⟩⟩ := h
  -- F₁⁺.p = F₁.p + 1 ≥ 2 since F₁.p ≥ 1 (ℕ+ values are ≥ 1).
  have h_F₁ext_p_ge_2 :
      ((2 : ℕ+) : WithTop ℕ+) ≤ (F₁.extend 1).p := by
    change ((2 : ℕ+) : WithTop ℕ+) ≤ F₁.p.map (· + (1 : ℕ+))
    cases hp : F₁.p with
    | top => simp
    | coe n =>
      rw [WithTop.map_coe]
      refine WithTop.coe_le_coe.mpr ?_
      have : (1 : ℕ) ≤ (n : ℕ) := n.one_le
      change (2 : ℕ+) ≤ n + 1
      have h2 : ((2 : ℕ+) : ℕ) ≤ ((n + 1 : ℕ+) : ℕ) := by push_cast; omega
      exact_mod_cast h2
  -- Reduce to producing a precision-2 witness.
  suffices h_witness : ∃ v : Dyadic,
      v ∈ ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ∧
      ¬ Dyadic.precisionAtMost ((1 : ℕ+) : WithTop ℕ+) v by
    obtain ⟨v, hv_mem, hv_not_p1⟩ := h_witness
    exact absurd (Format.two_le_p_of_precision_two_witness (hsub v hv_mem) hv_not_p1)
      (not_le.mpr h_p_lt)
  -- Reusable builder: from quantum + bound for v, package full membership.
  have h_mk_member : ∀ k : ℤ,
      Dyadic.quantumAtLeast (F₁.exp.map (· - (1 : ℤ))) (Dyadic.ofIntZpow 3 k) →
      Format.boundOK F₁.toFormat.boundAfterNext (Dyadic.ofIntZpow 3 k) →
      Dyadic.ofIntZpow 3 k ∈
        ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) := by
    intro k hq hb
    refine ⟨?_, ?_, ?_⟩
    · -- precisionAtMost (F₁.p + 1) (ofIntZpow 3 k)
      change Dyadic.precisionAtMost (F₁.extend 1).p _
      exact Dyadic.precisionAtMost_mono h_F₁ext_p_ge_2
        (Dyadic.precisionAtMost_two_three_zpow k)
    · -- quantumAtLeast — withBound preserves exp = (extend 1).exp = F₁.exp.map (· - 1).
      change Dyadic.quantumAtLeast (F₁.extend 1).exp _
      exact hq
    · -- boundOK — withBound's b = F₁.boundAfterNext.
      change Format.boundOK F₁.toFormat.boundAfterNext _
      exact hb
  rcases hF_exp : F₁.exp with _ | e
  · -- F₁.exp = ⊥. F₁⁺.exp = ⊥ ⇒ quantumAtLeast trivial.
    have h_q_triv : ∀ k : ℤ, Dyadic.quantumAtLeast (F₁.exp.map (· - (1 : ℤ)))
        (Dyadic.ofIntZpow 3 k) := by
      intro k; rw [hF_exp]; exact trivial
    rcases hF_b : F₁.b with _ | b
    · -- F₁.b = ⊤. Witness 3·2^0 = 3.
      refine ⟨Dyadic.ofIntZpow 3 0, h_mk_member 0 (h_q_triv 0) ?_,
        Dyadic.not_precisionAtMost_one_three_zpow 0⟩
      rw [Format.boundAfterNext_top hF_b]; trivial
    · -- F₁.b = (b : NonNegDyadic). F.exp = ⊥ ⇒ next b = b + 1. Witness 3·2^(-2) = 3/4 ≤ 1 ≤ b + 1.
      refine ⟨Dyadic.ofIntZpow 3 (-2), h_mk_member (-2) (h_q_triv (-2)) ?_,
        Dyadic.not_precisionAtMost_one_three_zpow (-2)⟩
      obtain ⟨_, h_bAfter⟩ := Format.boundAfterNext_coe hF_b
      rw [h_bAfter]
      change |((Dyadic.ofIntZpow 3 (-2) : Dyadic) : ℚ)| ≤ ((F₁.toFormat.next b.val : Dyadic) : ℚ)
      have h_next_eq : F₁.toFormat.next b.val = b.val + 1 := by
        unfold Format.next; rw [hF_exp]
      rw [h_next_eq]
      have hb_nn : (0 : ℚ) ≤ ((b.val : Dyadic) : ℚ) := b.2
      rw [Dyadic.coe_rat_ofIntZpow]
      push_cast
      have h_v_eq : (3 : ℚ) * (2 : ℚ) ^ (-2 : ℤ) = 3/4 := by norm_num
      rw [h_v_eq, abs_of_nonneg (by linarith : (0 : ℚ) ≤ 3/4)]
      linarith
  · -- F₁.exp = (e : ℤ). Use d ≠ 0 to derive |d| ≥ 2^e.
    have h_q_d : Dyadic.quantumAtLeast (F₁.exp) d := hd_mem.2.1
    rw [hF_exp] at h_q_d
    have hd_abs_ge : (2 : ℝ)^e ≤ |(d : ℝ)| :=
      Dyadic.abs_ge_two_zpow_of_quantum h_q_d hd_ne
    have h_q_v : ∀ k : ℤ, k ≥ e - 1 →
        Dyadic.quantumAtLeast (F₁.exp.map (· - (1 : ℤ))) (Dyadic.ofIntZpow 3 k) := by
      intro k hk
      rw [hF_exp]
      change Dyadic.quantumAtLeast (((e - 1 : ℤ) : WithBot ℤ)) _
      rw [Dyadic.quantumAtLeast_coe]
      refine ⟨3 * 2 ^ (k - (e - 1)).toNat, ?_⟩
      rw [Dyadic.coe_rat_ofIntZpow]
      -- ℚ split: 2^k = 2^(k-(e-1)).toNat * 2^(e-1).
      have h2 : (2 : ℚ) ≠ 0 := by norm_num
      have hsub : ((k - (e - 1)).toNat : ℤ) = k - (e - 1) := Int.toNat_of_nonneg (by omega)
      have h_split : (2 : ℚ) ^ k = (2 : ℚ) ^ (k - (e - 1)).toNat * (2 : ℚ) ^ (e - 1) := by
        rw [show ((2 : ℚ) ^ (k - (e - 1)).toNat : ℚ) = (2 : ℚ) ^ ((k - (e - 1)).toNat : ℤ) from
            (zpow_natCast _ _).symm, ← zpow_add₀ h2, hsub]
        congr 1; ring
      push_cast
      rw [h_split]
      ring
    rcases hF_b : F₁.b with _ | b
    · -- F₁.b = ⊤. Witness 3·2^(e-1).
      refine ⟨Dyadic.ofIntZpow 3 (e - 1), h_mk_member (e - 1) (h_q_v (e - 1) (by omega)) ?_,
        Dyadic.not_precisionAtMost_one_three_zpow (e - 1)⟩
      rw [Format.boundAfterNext_top hF_b]; trivial
    · -- F₁.b = (b : NonNegDyadic). |d| ≤ b. With |d| ≥ 2^e: b ≥ 2^e.
      have hd_le_b_q : |((d : Dyadic) : ℚ)| ≤ ((b.val : Dyadic) : ℚ) := by
        have hb_OK : Format.boundOK F₁.b d := hd_mem.2.2
        rw [hF_b] at hb_OK; exact hb_OK
      have hd_le_b : |((d : Dyadic) : ℝ)| ≤ ((b.val : Dyadic) : ℝ) := by
        rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast, ← Rat.cast_abs]
        exact_mod_cast hd_le_b_q
      have hb_ge : (2 : ℝ)^e ≤ ((b.val : Dyadic) : ℝ) := le_trans hd_abs_ge hd_le_b
      have h2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
      have hb_pos : 0 < ((b.val : Dyadic) : ℝ) := lt_of_lt_of_le h2e_pos hb_ge
      refine ⟨Dyadic.ofIntZpow 3 (e - 1), h_mk_member (e - 1) (h_q_v (e - 1) (by omega)) ?_,
        Dyadic.not_precisionAtMost_one_three_zpow (e - 1)⟩
      obtain ⟨_, h_bAfter⟩ := Format.boundAfterNext_coe hF_b
      rw [h_bAfter]
      change |((Dyadic.ofIntZpow 3 (e - 1) : Dyadic) : ℚ)| ≤ ((F₁.toFormat.next b.val : Dyadic) : ℚ)
      -- Prove the bound over ℝ, then cast to ℚ.
      suffices h_real : |((Dyadic.ofIntZpow 3 (e - 1) : Dyadic) : ℝ)|
          ≤ ((F₁.toFormat.next b.val : Dyadic) : ℝ) by
        rw [Dyadic.coe_real_eq_ratCast, ← Rat.cast_abs] at h_real
        rw [Dyadic.coe_real_eq_ratCast] at h_real
        exact_mod_cast h_real
      -- |3·2^(e-1)| = 1.5·2^e ≤ next(b) (≥ b + step ≥ 2·2^e ≥ 1.5·2^e).
      have h_v_eq : ((Dyadic.ofIntZpow 3 (e - 1) : Dyadic) : ℝ) = (3 : ℝ) * (2 : ℝ)^(e - 1) := by
        rw [Dyadic.coe_ofIntZpow]; push_cast; ring
      have h_v_pos : (0 : ℝ) ≤ (3 : ℝ) * (2 : ℝ)^(e - 1) := by positivity
      have h_v_split : (3 : ℝ) * (2 : ℝ)^(e - 1) = (2 : ℝ)^e + (2 : ℝ)^(e - 1) := by
        rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]; field_simp; ring
      have h_e1_le_e : (2 : ℝ)^(e - 1) ≤ (2 : ℝ)^e :=
        zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
      rcases hF_p : F₁.p with _ | p
      · -- F₁.p = ⊤. F₁.next b = b + 2^e.
        have h_next_eq : F₁.toFormat.next b.val = b.val + Dyadic.ofIntZpow 1 e :=
          Format.next_eq_p_top F₁.toFormat hF_exp hF_p b.val
        rw [h_next_eq, h_v_eq, abs_of_nonneg h_v_pos, h_v_split]
        push_cast
        rw [Dyadic.coe_ofIntZpow]; push_cast
        linarith
      · -- F₁.p = (p : ℕ+). Step ≥ 2^e.
        have h_next_eq : F₁.toFormat.next b.val = b.val + Dyadic.ofIntZpow 1
            (max e (Int.log 2 ((b.val : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1)) :=
          Format.next_eq_finite_pos F₁.toFormat hF_exp hF_p hb_pos
        rw [h_next_eq, h_v_eq, abs_of_nonneg h_v_pos, h_v_split]
        push_cast
        rw [Dyadic.coe_ofIntZpow]; push_cast
        have h_step_pow : (2 : ℝ)^e ≤
            (2 : ℝ)^(max e (Int.log 2 ((b.val : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1)) :=
          zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (le_max_left _ _)
        linarith

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
  have hz_zero : z = 0 := (Dyadic.coe_real_inj z 0).mp (by rw [hz_zero_real, Dyadic.coe_real_zero])
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

/-- **rnd-RTO-RTZ** (Fig. 9), positive case `0 < x`. -/
private theorem rndRTO_RTZ_pos {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ+) : WithTop ℕ+) ≤ F₂.p)
    {x : ℝ} (hx_pos : 0 < x) {z w' : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toZero (z : ℝ) w') :
    RoundsFinite F₁ .toZero x w' := by
  -- `F₁ ⊆ F₁.extend 1 ⊆ F₂`.
  have hsub' : F₁.toFormat ⊆ F₂.toFormat := fun y hy =>
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

/-- **rnd-RTO-RTZ** (Fig. 9), general case, **paper form**. An RTO rounding
`z` of `x` in `F₂` followed by an RTZ rounding `w'` of `z` in `F₁` collapses
to an RTZ rounding of `x` in `F₁`. Uses the single bound-aware containment
hypothesis `(F₁.extend 1).withBound F₁.boundAfterNext ⊆ F₂`; the auxiliary
`2 ≤ F₂.p` is *derived* (or `F₁` is trivial). -/
theorem rndRTO_RTZ {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {x : ℝ} {z w' : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toZero (z : ℝ) w') :
    RoundsFinite F₁ .toZero x w' := by
  rcases hp_F₂_or_F₁_trivial hsub with hp_F₂ | hF₁_triv
  · -- main case: 2 ≤ F₂.p. Recover the weaker subset and run the trichotomy.
    have hsub' := extend_one_subset_of_paper_subset hsub
    rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
    · -- x < 0: negate, apply the positive case, negate back.
      have hx_pos' : 0 < (-x) := by linarith
      have hz' : RoundsFinite F₂ .toOdd (-x) (-z) :=
        (RoundsFinite.neg_toOdd F₂ x z).mp hz
      have hw' : RoundsFinite F₁ .toZero ((-z : Dyadic) : ℝ) (-w') := by
        rw [Dyadic.coe_real_neg]; exact (RoundsFinite.neg_toZero F₁ (z : ℝ) w').mp hw
      have h_result := rndRTO_RTZ_pos hsub' hp_F₂ hx_pos' hz' hw'
      have hfinal := (RoundsFinite.neg_toZero F₁ (-x) (-w')).mp h_result
      rwa [neg_neg, neg_neg] at hfinal
    · -- x = 0: forces z = 0 and w' = 0.
      subst hx_zero
      have hz_zero : z = 0 := toOdd_eq_zero_of_zero hz
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
    · -- x > 0
      exact rndRTO_RTZ_pos hsub' hp_F₂ hx_pos hz hw
  · -- trivial case: F₁ = {0}.
    exact RoundsFinite.toZero_of_trivial hF₁_triv hw.1

/-- **rnd-RTO-RAZ** (Fig. 9), positive case `0 < x`. Symmetric to
`rndRTO_RTZ_pos` but for round-away-from-zero. The key Lemma 5.3 application
(`toOdd_notMem_of_extend_subset`) happens in the ToNegative (RTN / round-down)
branch of `z` rather than the ToPositive (RTP) branch. -/
private theorem rndRTO_RAZ_pos {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ+) : WithTop ℕ+) ≤ F₂.p)
    {x : ℝ} (hx_pos : 0 < x) {z w' : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .awayZero (z : ℝ) w') :
    RoundsFinite F₁ .awayZero x w' := by
  -- `F₁ ⊆ F₁.extend 1 ⊆ F₂`.
  have hsub' : F₁.toFormat ⊆ F₂.toFormat := fun y hy =>
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

/-- **rnd-RTO-RAZ** (Fig. 9), general case, **paper form**. An RTO rounding
`z` of `x` in `F₂` followed by an RAZ (away-from-zero) rounding `w'` of `z` in
`F₁` collapses to an RAZ rounding of `x` in `F₁`. Uses the single bound-aware
containment hypothesis `(F₁.extend 1).withBound F₁.boundAfterNext ⊆ F₂`; the
auxiliary `2 ≤ F₂.p` is *derived* (or `F₁` is trivial). -/
theorem rndRTO_RAZ {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {x : ℝ} {z w' : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .awayZero (z : ℝ) w') :
    RoundsFinite F₁ .awayZero x w' := by
  rcases hp_F₂_or_F₁_trivial hsub with hp_F₂ | hF₁_triv
  · -- main case: 2 ≤ F₂.p. Recover the weaker subset and run the trichotomy.
    have hsub' := extend_one_subset_of_paper_subset hsub
    rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
    · -- x < 0: negate, apply the positive case, negate back.
      have hx_pos' : 0 < (-x) := by linarith
      have hz' : RoundsFinite F₂ .toOdd (-x) (-z) :=
        (RoundsFinite.neg_toOdd F₂ x z).mp hz
      have hw' : RoundsFinite F₁ .awayZero ((-z : Dyadic) : ℝ) (-w') := by
        rw [Dyadic.coe_real_neg]; exact (RoundsFinite.neg_awayZero F₁ (z : ℝ) w').mp hw
      have h_result := rndRTO_RAZ_pos hsub' hp_F₂ hx_pos' hz' hw'
      have hfinal := (RoundsFinite.neg_awayZero F₁ (-x) (-w')).mp h_result
      rwa [neg_neg, neg_neg] at hfinal
    · -- x = 0: forces z = 0 and w' = 0.
      subst hx_zero
      have hz_zero : z = 0 := toOdd_eq_zero_of_zero hz
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
    · -- x > 0
      exact rndRTO_RAZ_pos hsub' hp_F₂ hx_pos hz hw
  · -- trivial case: F₁ = {0}.
    exact RoundsFinite.awayZero_of_trivial hF₁_triv hz hw

/-! ## Round-to-nearest helpers for `rndRTO_RN` (Stage A) -/

/-- Helper for tie-break: from `|x - w'| = |x - z'|` with `w' ≠ z'`, derive
`x = (w' + z') / 2`. -/
private theorem nearest_midpoint_of_tie {x : ℝ} {w' z' : Dyadic}
    (h_ne : z' ≠ w') (h_tie : |x - (w' : ℝ)| = |x - (z' : ℝ)|) :
    x = ((w' : ℝ) + (z' : ℝ)) / 2 := by
  rcases abs_eq_abs.mp h_tie with h1 | h1
  · -- x - w' = x - z' ⇒ w' = z', contradicting h_ne
    have hwz : (w' : ℝ) = (z' : ℝ) := by linarith
    exact absurd ((Dyadic.coe_real_inj w' z').mp hwz).symm h_ne
  · -- x - w' = -(x - z') ⇒ 2x = w' + z'
    linarith

/-- F-adjacency of `(w', z')` in `F₁`: no F₁ element strictly between. Derived
from `RTN w'` ∨ `RTP w'` and `RTN z'` ∨ `RTP z'` for `x`, when `w' ≤ x ≤ z'`:
any F₁-`y` with `w' < y` must be `≥ z'`. -/
private theorem F_adjacent_of_RN_round_pair {F₁ : FiniteFormat}
    {x : ℝ} {w' z' : Dyadic}
    (hw'_adj : RoundsFinite F₁ .toNegative x w' ∨ RoundsFinite F₁ .toPositive x w')
    (hz'_adj : RoundsFinite F₁ .toNegative x z' ∨ RoundsFinite F₁ .toPositive x z')
    (hw'_le_x : (w' : ℝ) ≤ x) (hx_le_z' : x ≤ (z' : ℝ)) :
    ∀ y : Dyadic, y ∈ F₁ → (w' : ℝ) < (y : ℝ) → (z' : ℝ) ≤ (y : ℝ) := by
  intro y hyF₁ h_w_lt_y
  by_cases h_y_le_x : (y : ℝ) ≤ x
  · -- y ≤ x. By RTN w' (or via RTP w' contradicting w' ≤ x), y ≤ w'.
    exfalso
    rcases hw'_adj with hwRD | hwRU
    · obtain ⟨_, _, hw_max⟩ := hwRD
      have h_y_le_w' : (y : ℝ) ≤ (w' : ℝ) := hw_max y hyF₁ h_y_le_x
      linarith
    · obtain ⟨_, hxw, _⟩ := hwRU
      have hxw' : x = (w' : ℝ) := le_antisymm hxw hw'_le_x
      rw [← hxw'] at h_w_lt_y
      linarith
  · push Not at h_y_le_x
    -- y > x. By RTP z' (or RTN z' contradicting), z' ≤ y.
    rcases hz'_adj with hzRD | hzRU
    · obtain ⟨_, hzx_le, _⟩ := hzRD
      have hxz' : x = (z' : ℝ) := le_antisymm hx_le_z' hzx_le
      linarith
    · obtain ⟨_, _, hz_min⟩ := hzRU
      exact hz_min y hyF₁ (le_of_lt h_y_le_x)

/-- F-adjacent midpoint membership in `F₁.extend 1`. Dispatches on `F₁`'s
precision/exponent shape, routing to the appropriate Grid lemma. -/
private theorem midpoint_in_F₁_extend_one_of_F_adjacent {F₁ : FiniteFormat}
    {y₁ y₂ : Dyadic} (hy₁F : y₁ ∈ F₁) (hy₂F : y₂ ∈ F₁)
    (h_lt : (y₁ : ℝ) < (y₂ : ℝ))
    (h_adj : ∀ y : Dyadic, y ∈ F₁ → (y₁ : ℝ) < (y : ℝ) → (y₂ : ℝ) ≤ (y : ℝ)) :
    Dyadic.midpoint y₁ y₂ ∈ F₁.extend 1 := by
  cases hp : F₁.p with
  | top =>
    cases he : F₁.exp with
    | bot =>
        exact absurd F₁.finite (by push Not; exact ⟨hp, he⟩)
    | coe e' => exact midpoint_mem_extend_one_of_p_top F₁ hp he hy₁F hy₂F
  | coe p' =>
    cases he : F₁.exp with
    | bot =>
        exact midpoint_mem_extend_one_of_F_adjacent_exp_bot
          F₁ hp he hy₁F hy₂F h_lt h_adj
    | coe e' =>
        exact midpoint_mem_extend_one_of_F_adjacent
          F₁ hp he hy₁F hy₂F h_lt h_adj

/-- F-adjacent midpoint membership in `F₂`. Gets `midpoint y₁ y₂ ∈ F₁.extend 1`
from the Grid lemmas (dispatching on `F₁`'s precision/exponent shape) and then
applies the subset hypothesis. -/
private theorem midpoint_F₁_in_F₂_of_F_adjacent {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat)
    {y₁ y₂ : Dyadic} (hy₁F : y₁ ∈ F₁) (hy₂F : y₂ ∈ F₁)
    (h_lt : (y₁ : ℝ) < (y₂ : ℝ))
    (h_adj : ∀ y : Dyadic, y ∈ F₁ → (y₁ : ℝ) < (y : ℝ) → (y₂ : ℝ) ≤ (y : ℝ)) :
    Dyadic.midpoint y₁ y₂ ∈ F₂ :=
  hsub _ (midpoint_in_F₁_extend_one_of_F_adjacent hy₁F hy₂F h_lt h_adj)

/-- RN analog of `extend_one_subset_of_paper_subset`: from the paper-aligned
containment `((F₁.extend 2).withBound (F₁.extend 1).boundAfterNext) ⊆ F₂`,
derive the weaker `F₁.extend 2 ⊆ F₂` form. -/
private theorem extend_two_subset_of_paper_RN_subset {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
              ⊆ F₂.toFormat) :
    (F₁.extend 2).toFormat ⊆ F₂.toFormat := by
  intro y hy
  apply hsub
  obtain ⟨hp_y, hq_y, hb_y⟩ := hy
  refine ⟨hp_y, hq_y, ?_⟩
  change Format.boundOK (F₁.extend 1).toFormat.boundAfterNext y
  cases hF_b : (F₁.extend 1).b with
  | top =>
    rw [Format.boundAfterNext_top hF_b]; trivial
  | coe b =>
    obtain ⟨h_nn, h_after⟩ := Format.boundAfterNext_coe hF_b
    rw [h_after]
    change |((y : Dyadic) : ℚ)| ≤ (((F₁.extend 1).toFormat.next b.val : Dyadic) : ℚ)
    -- y ∈ F₁.extend 2 has |y| ≤ (F₁.extend 2).b = F₁.b = (F₁.extend 1).b = b.
    change Format.boundOK (F₁.extend 2).b y at hb_y
    rw [show (F₁.extend 2).b = (F₁.extend 1).b from rfl, hF_b] at hb_y
    have h_y_le_b : |((y : Dyadic) : ℚ)| ≤ ((b.val : Dyadic) : ℚ) := hb_y
    have hb_nn : 0 ≤ ((b.val : Dyadic) : ℝ) := by
      rw [Dyadic.coe_real_eq_ratCast]; exact_mod_cast b.2
    have h_le_next : ((b.val : Dyadic) : ℝ)
        ≤ (((F₁.extend 1).toFormat.next b.val : Dyadic) : ℝ) :=
      Format.self_le_next (F₁.extend 1).toFormat b.val hb_nn
    have h_le_next_q : ((b.val : Dyadic) : ℚ)
        ≤ (((F₁.extend 1).toFormat.next b.val : Dyadic) : ℚ) := by
      rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast] at h_le_next
      exact_mod_cast h_le_next
    exact le_trans h_y_le_b h_le_next_q

/-- RN analog of `hp_F₂_or_F₁_trivial`. From the paper-aligned RN containment
`((F₁.extend 2).withBound (F₁.extend 1).boundAfterNext) ⊆ F₂`, either
`F₂.p ≥ 2` or `F₁` contains only `0`. Same precision-2 witness `3·2^k`; the
looser precision (`F₁.p + 2`) and quantum (`exp - 2`) only make the witness
easier to place, and the bound `(F₁.extend 1).boundAfterNext` is large enough. -/
private theorem hp_F₂_or_F₁_trivial_RN {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
              ⊆ F₂.toFormat) :
    ((2 : ℕ+) : WithTop ℕ+) ≤ F₂.p ∨ ∀ d : Dyadic, d ∈ F₁ → (d : ℝ) = 0 := by
  by_contra h
  push Not at h
  obtain ⟨h_p_lt, ⟨d, hd_mem, hd_ne⟩⟩ := h
  -- F₁⁺².p = F₁.p + 2 ≥ 2.
  have h_F₁ext2_p_ge_2 :
      ((2 : ℕ+) : WithTop ℕ+) ≤ (F₁.extend 2).p := by
    change ((2 : ℕ+) : WithTop ℕ+) ≤ F₁.p.map (· + (2 : ℕ+))
    cases hp : F₁.p with
    | top => simp
    | coe n =>
      rw [WithTop.map_coe]
      refine WithTop.coe_le_coe.mpr ?_
      change (2 : ℕ+) ≤ n + 2
      have h2 : ((2 : ℕ+) : ℕ) ≤ ((n + 2 : ℕ+) : ℕ) := by push_cast; try omega
      exact_mod_cast h2
  -- Reduce to producing a precision-2 witness.
  suffices h_witness : ∃ v : Dyadic,
      v ∈ ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext) ∧
      ¬ Dyadic.precisionAtMost ((1 : ℕ+) : WithTop ℕ+) v by
    obtain ⟨v, hv_mem, hv_not_p1⟩ := h_witness
    exact absurd (Format.two_le_p_of_precision_two_witness (hsub v hv_mem) hv_not_p1)
      (not_le.mpr h_p_lt)
  -- Reusable builder: from quantum + bound for v, package full membership.
  have h_mk_member : ∀ k : ℤ,
      Dyadic.quantumAtLeast (F₁.exp.map (· - (2 : ℤ))) (Dyadic.ofIntZpow 3 k) →
      Format.boundOK (F₁.extend 1).toFormat.boundAfterNext (Dyadic.ofIntZpow 3 k) →
      Dyadic.ofIntZpow 3 k ∈
        ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext) := by
    intro k hq hb
    refine ⟨?_, ?_, ?_⟩
    · change Dyadic.precisionAtMost (F₁.extend 2).p _
      exact Dyadic.precisionAtMost_mono h_F₁ext2_p_ge_2
        (Dyadic.precisionAtMost_two_three_zpow k)
    · change Dyadic.quantumAtLeast (F₁.extend 2).exp _
      exact hq
    · change Format.boundOK (F₁.extend 1).toFormat.boundAfterNext _
      exact hb
  rcases hF_exp : F₁.exp with _ | e
  · -- F₁.exp = ⊥. F₁⁺².exp = ⊥ ⇒ quantumAtLeast trivial.
    have h_q_triv : ∀ k : ℤ, Dyadic.quantumAtLeast (F₁.exp.map (· - (2 : ℤ)))
        (Dyadic.ofIntZpow 3 k) := by
      intro k; rw [hF_exp]; exact trivial
    rcases hF_b : (F₁.extend 1).b with _ | b
    · -- (F₁.extend 1).b = ⊤. Witness 3.
      refine ⟨Dyadic.ofIntZpow 3 0, h_mk_member 0 (h_q_triv 0) ?_,
        Dyadic.not_precisionAtMost_one_three_zpow 0⟩
      rw [Format.boundAfterNext_top hF_b]; trivial
    · -- (F₁.extend 1).b = (b : NonNegDyadic). (F₁.extend 1).exp = ⊥ ⇒ next b = b + 1.
      -- Witness 3·2^(-2) = 3/4 ≤ 1 ≤ b + 1.
      refine ⟨Dyadic.ofIntZpow 3 (-2), h_mk_member (-2) (h_q_triv (-2)) ?_,
        Dyadic.not_precisionAtMost_one_three_zpow (-2)⟩
      obtain ⟨_, h_bAfter⟩ := Format.boundAfterNext_coe hF_b
      rw [h_bAfter]
      change |((Dyadic.ofIntZpow 3 (-2) : Dyadic) : ℚ)|
        ≤ (((F₁.extend 1).toFormat.next b.val : Dyadic) : ℚ)
      have h_ext1_exp : (F₁.extend 1).exp = ⊥ := by
        change F₁.exp.map (· - ((1 : ℕ+) : ℤ)) = ⊥; rw [hF_exp]; rfl
      have h_next_eq : (F₁.extend 1).toFormat.next b.val = b.val + 1 := by
        unfold Format.next; rw [h_ext1_exp]
      rw [h_next_eq]
      have hb_nn : (0 : ℚ) ≤ ((b.val : Dyadic) : ℚ) := b.2
      rw [Dyadic.coe_rat_ofIntZpow]
      push_cast
      have h_v_eq : (3 : ℚ) * (2 : ℚ) ^ (-2 : ℤ) = 3/4 := by norm_num
      rw [h_v_eq, abs_of_nonneg (by linarith : (0 : ℚ) ≤ 3/4)]
      linarith
  · -- F₁.exp = (e : ℤ). Use d ≠ 0 to derive |d| ≥ 2^e.
    have h_q_d : Dyadic.quantumAtLeast (F₁.exp) d := hd_mem.2.1
    rw [hF_exp] at h_q_d
    have hd_abs_ge : (2 : ℝ)^e ≤ |(d : ℝ)| :=
      Dyadic.abs_ge_two_zpow_of_quantum h_q_d hd_ne
    have h_q_v : ∀ k : ℤ, k ≥ e - 2 →
        Dyadic.quantumAtLeast (F₁.exp.map (· - (2 : ℤ))) (Dyadic.ofIntZpow 3 k) := by
      intro k hk
      rw [hF_exp]
      change Dyadic.quantumAtLeast (((e - 2 : ℤ) : WithBot ℤ)) _
      rw [Dyadic.quantumAtLeast_coe]
      refine ⟨3 * 2 ^ (k - (e - 2)).toNat, ?_⟩
      rw [Dyadic.coe_rat_ofIntZpow]
      have h2 : (2 : ℚ) ≠ 0 := by norm_num
      have hsub' : ((k - (e - 2)).toNat : ℤ) = k - (e - 2) := Int.toNat_of_nonneg (by omega)
      have h_split : (2 : ℚ) ^ k = (2 : ℚ) ^ (k - (e - 2)).toNat * (2 : ℚ) ^ (e - 2) := by
        rw [show ((2 : ℚ) ^ (k - (e - 2)).toNat : ℚ) = (2 : ℚ) ^ ((k - (e - 2)).toNat : ℤ) from
            (zpow_natCast _ _).symm, ← zpow_add₀ h2, hsub']
        congr 1; ring
      push_cast
      rw [h_split]
      ring
    -- (F₁.extend 1).b = F₁.b (extend doesn't change b).
    have h_ext1_b : (F₁.extend 1).b = F₁.b := rfl
    rcases hF_b : F₁.b with _ | b
    · -- F₁.b = ⊤. Witness 3·2^(e-1).
      refine ⟨Dyadic.ofIntZpow 3 (e - 1), h_mk_member (e - 1) (h_q_v (e - 1) (by omega)) ?_,
        Dyadic.not_precisionAtMost_one_three_zpow (e - 1)⟩
      have h_b_top : (F₁.extend 1).b = ⊤ := by rw [h_ext1_b, hF_b]; rfl
      rw [Format.boundAfterNext_top h_b_top]; trivial
    · -- F₁.b = (b : NonNegDyadic). |d| ≤ b. With |d| ≥ 2^e: b ≥ 2^e.
      have hd_le_b_q : |((d : Dyadic) : ℚ)| ≤ ((b.val : Dyadic) : ℚ) := by
        have hb_OK : Format.boundOK F₁.b d := hd_mem.2.2
        rw [hF_b] at hb_OK; exact hb_OK
      have hd_le_b : |((d : Dyadic) : ℝ)| ≤ ((b.val : Dyadic) : ℝ) := by
        rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast, ← Rat.cast_abs]
        exact_mod_cast hd_le_b_q
      have hb_ge : (2 : ℝ)^e ≤ ((b.val : Dyadic) : ℝ) := le_trans hd_abs_ge hd_le_b
      have h2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
      have hb_pos : 0 < ((b.val : Dyadic) : ℝ) := lt_of_lt_of_le h2e_pos hb_ge
      have h_ext1_b_coe : (F₁.extend 1).b = (b : WithTop NonNegDyadic) := by
        rw [h_ext1_b, hF_b]; rfl
      refine ⟨Dyadic.ofIntZpow 3 (e - 1), h_mk_member (e - 1) (h_q_v (e - 1) (by omega)) ?_,
        Dyadic.not_precisionAtMost_one_three_zpow (e - 1)⟩
      obtain ⟨_, h_bAfter⟩ := Format.boundAfterNext_coe h_ext1_b_coe
      rw [h_bAfter]
      change |((Dyadic.ofIntZpow 3 (e - 1) : Dyadic) : ℚ)|
        ≤ (((F₁.extend 1).toFormat.next b.val : Dyadic) : ℚ)
      suffices h_real : |((Dyadic.ofIntZpow 3 (e - 1) : Dyadic) : ℝ)|
          ≤ (((F₁.extend 1).toFormat.next b.val : Dyadic) : ℝ) by
        rw [Dyadic.coe_real_eq_ratCast, ← Rat.cast_abs] at h_real
        rw [Dyadic.coe_real_eq_ratCast] at h_real
        exact_mod_cast h_real
      -- |3·2^(e-1)| = 1.5·2^e ≤ next(b) (≥ b + step ≥ 2·2^e ≥ 1.5·2^e).
      have h_v_eq : ((Dyadic.ofIntZpow 3 (e - 1) : Dyadic) : ℝ) = (3 : ℝ) * (2 : ℝ)^(e - 1) := by
        rw [Dyadic.coe_ofIntZpow]; push_cast; ring
      have h_v_pos : (0 : ℝ) ≤ (3 : ℝ) * (2 : ℝ)^(e - 1) := by positivity
      have h_v_split : (3 : ℝ) * (2 : ℝ)^(e - 1) = (2 : ℝ)^e + (2 : ℝ)^(e - 1) := by
        rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]; field_simp; ring
      have h_e1_le_e : (2 : ℝ)^(e - 1) ≤ (2 : ℝ)^e :=
        zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
      -- (F₁.extend 1).exp = e - 1, since F₁.exp = e.
      have h_ext1_exp : (F₁.extend 1).exp = ((e - 1 : ℤ) : WithBot ℤ) := by
        change F₁.exp.map (· - ((1 : ℕ+) : ℤ)) = _
        rw [hF_exp]; rfl
      rcases hF_p : F₁.p with _ | p
      · -- F₁.p = ⊤ ⇒ (F₁.extend 1).p = ⊤. next b = b + 2^(e-1).
        have h_ext1_p : (F₁.extend 1).p = ⊤ := by
          change F₁.p.map (· + (1 : ℕ+)) = _; rw [hF_p]; rfl
        have h_next_eq : (F₁.extend 1).toFormat.next b.val
            = b.val + Dyadic.ofIntZpow 1 (e - 1) :=
          Format.next_eq_p_top (F₁.extend 1).toFormat h_ext1_exp h_ext1_p b.val
        rw [h_next_eq, h_v_eq, abs_of_nonneg h_v_pos, h_v_split]
        push_cast
        rw [Dyadic.coe_ofIntZpow]; push_cast
        linarith
      · -- F₁.p = (p : ℕ+) ⇒ (F₁.extend 1).p = p + 1. Step ≥ 2^(e-1).
        have h_ext1_p : (F₁.extend 1).p = (((p + 1 : ℕ+)) : WithTop ℕ+) := by
          change F₁.p.map (· + (1 : ℕ+)) = _; rw [hF_p]; rfl
        have h_next_eq : (F₁.extend 1).toFormat.next b.val = b.val + Dyadic.ofIntZpow 1
            (max (e - 1) (Int.log 2 ((b.val : Dyadic) : ℝ) - (((p + 1 : ℕ+) : ℕ) : ℤ) + 1)) :=
          Format.next_eq_finite_pos (F₁.extend 1).toFormat h_ext1_exp h_ext1_p hb_pos
        rw [h_next_eq, h_v_eq, abs_of_nonneg h_v_pos, h_v_split]
        push_cast
        rw [Dyadic.coe_ofIntZpow]; push_cast
        rw [one_mul]
        have h_step_pow : (2 : ℝ)^(e - 1) ≤
            (2 : ℝ)^(max (e - 1) (Int.log 2 ((b.val : Dyadic) : ℝ)
              - (((p : ℕ) : ℤ) + 1) + 1)) :=
          zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (le_max_left _ _)
        linarith

/-- If `F₁` is trivial (contains only `0`) then `RoundsFinite F₁ (.nearest tb) x w'`
holds for any real `x` and tie-break `tb`, whenever `w' ∈ F₁` (so `w' = 0`).
The closeness and tie-break conditions are vacuous; faithfulness holds by the
round-down branch (`x ≥ 0`) or round-up branch (`x < 0`). -/
private theorem RoundsFinite.nearest_of_trivial {F₁ : FiniteFormat} {tb : TieBreak}
    (hF₁_triv : ∀ d : Dyadic, d ∈ F₁ → (d : ℝ) = 0)
    {x : ℝ} {w' : Dyadic} (hw : w' ∈ F₁) :
    RoundsFinite F₁ (.nearest tb) x w' := by
  have hw'_zero : (w' : ℝ) = 0 := hF₁_triv w' hw
  -- Every F₁ element equals w' (both are 0).
  have h_eq_w' : ∀ z : Dyadic, z ∈ F₁ → z = w' := fun z hzF₁ =>
    (Dyadic.coe_real_inj z w').mp (by rw [hF₁_triv z hzF₁, hw'_zero])
  -- Shared faithfulness.
  have h_adj : IsFaithfulRound F₁ x w' := by
    rcases lt_or_ge x 0 with hx_neg | hx_nn
    · right
      refine ⟨hw, by rw [hw'_zero]; linarith, ?_⟩
      intro v hvF₁ _
      rw [hF₁_triv v hvF₁, hw'_zero]
    · left
      refine ⟨hw, by rw [hw'_zero]; exact hx_nn, ?_⟩
      intro v hvF₁ _
      rw [hF₁_triv v hvF₁, hw'_zero]
  -- Shared closeness.
  have h_close : ∀ z : Dyadic, z ∈ F₁ → IsFaithfulRound F₁ x z →
      |x - (w' : ℝ)| ≤ |x - (z : ℝ)| := by
    intro z hzF₁ _
    rw [hF₁_triv z hzF₁, hw'_zero]
  -- Dispatch on tb only for the tie-break clause shape.
  cases tb with
  | toEven =>
    refine ⟨hw, h_adj, h_close, ?_⟩
    rintro ⟨z, hzF₁, _, hz_ne_w', _⟩
    exact (hz_ne_w' (h_eq_w' z hzF₁)).elim
  | awayZero =>
    refine ⟨hw, h_adj, h_close, ?_⟩
    intro z hzF₁ _ hz_ne_w' _
    exact (hz_ne_w' (h_eq_w' z hzF₁)).elim

/-! ## `rnd-RTO-RN` (Fig. 9) — round-to-odd then round-to-nearest -/

/-- The closeness transfer step for `rndRTO_RN`: given that `z = RTO F₂ x`
sits outside `F₁.extend 1` (Lemma 5.3) and `w' = RN F₁ z`, every F₁-adjacent
`z'` to `x` satisfies `|x - w'| ≤ |x - z'|`. The argument uses the midpoint
`m = (w' + z') / 2` (in F₂ via `midpoint_F₁_in_F₂_of_F_adjacent`, in
`F₁.extend 1` via `midpoint_in_F₁_extend_one_of_F_adjacent`), shows
`z ≠ m`, and concludes `x` lies on `w'`'s side of `m`. -/
private lemma rndRTO_RN_close_transfer {F₁ F₂ : FiniteFormat}
    (hsub_ext1 : (F₁.extend 1).toFormat ⊆ F₂.toFormat)
    (hsub' : F₁.toFormat ⊆ F₂.toFormat)
    (hF₁_sub_ext1 : F₁.toFormat ⊆ (F₁.extend 1).toFormat)
    {x : ℝ} {z w' : Dyadic}
    (hz_adj : RoundsFinite F₂ .toNegative x z ∨ RoundsFinite F₂ .toPositive x z)
    (hw'F₁ : w' ∈ F₁)
    (h_adj_x : RoundsFinite F₁ .toNegative x w' ∨ RoundsFinite F₁ .toPositive x w')
    (hw_close_inner : ∀ z' : Dyadic, z' ∈ F₁ →
        (RoundsFinite F₁ .toNegative ((z : Dyadic) : ℝ) z'
          ∨ RoundsFinite F₁ .toPositive ((z : Dyadic) : ℝ) z') →
        |((z : Dyadic) : ℝ) - ((w' : Dyadic) : ℝ)| ≤
            |((z : Dyadic) : ℝ) - ((z' : Dyadic) : ℝ)|)
    (hz_not_F₁_ext1 : z ∉ F₁.extend 1) :
    ∀ z' : Dyadic, z' ∈ F₁ →
      (RoundsFinite F₁ .toNegative x z' ∨ RoundsFinite F₁ .toPositive x z') →
      |x - ((w' : Dyadic) : ℝ)| ≤ |x - ((z' : Dyadic) : ℝ)| := by
  intro z' hz'F₁ hz'_adj
  by_cases h_eq : ((z' : Dyadic) : ℝ) = ((w' : Dyadic) : ℝ)
  · rw [h_eq]
  · have h_w_ne_z' : ((w' : Dyadic) : ℝ) ≠ ((z' : Dyadic) : ℝ) := fun h => h_eq h.symm
    have h_z_ne_w'_real : ((z : Dyadic) : ℝ) ≠ ((w' : Dyadic) : ℝ) := by
      intro h
      apply hz_not_F₁_ext1
      have hzw : z = w' := (Dyadic.coe_real_inj z w').mp h
      rw [hzw]; exact hF₁_sub_ext1 _ hw'F₁
    have h_z_ne_z'_real : ((z : Dyadic) : ℝ) ≠ ((z' : Dyadic) : ℝ) := by
      intro h
      apply hz_not_F₁_ext1
      have hzz' : z = z' := (Dyadic.coe_real_inj z z').mp h
      rw [hzz']; exact hF₁_sub_ext1 _ hz'F₁
    have hw'F₂ : w' ∈ F₂ := hsub' _ hw'F₁
    have hz'F₂ : z' ∈ F₂ := hsub' _ hz'F₁
    rcases lt_or_gt_of_ne h_w_ne_z' with h_w_lt_z | h_z_lt_w
    · have hwRD : RoundsFinite F₁ .toNegative x w' := by
        rcases h_adj_x with hwRD | hwRU
        · exact hwRD
        · exfalso
          rcases hz'_adj with hzRD | hzRU
          · linarith [hwRU.2.1, hzRD.2.1]
          · have h1 : ((w' : Dyadic) : ℝ) ≤ ((z' : Dyadic) : ℝ) :=
              hwRU.2.2 z' hz'F₁ hzRU.2.1
            have h2 : ((z' : Dyadic) : ℝ) ≤ ((w' : Dyadic) : ℝ) :=
              hzRU.2.2 w' hw'F₁ hwRU.2.1
            exact h_w_ne_z' (le_antisymm h1 h2)
      have hzRU : RoundsFinite F₁ .toPositive x z' := by
        rcases hz'_adj with hzRD | hzRU
        · exfalso
          have h1 : ((w' : Dyadic) : ℝ) ≤ ((z' : Dyadic) : ℝ) :=
            hzRD.2.2 w' hw'F₁ hwRD.2.1
          have h2 : ((z' : Dyadic) : ℝ) ≤ ((w' : Dyadic) : ℝ) :=
            hwRD.2.2 z' hz'F₁ hzRD.2.1
          exact h_w_ne_z' (le_antisymm h1 h2)
        · exact hzRU
      have h_w_le_x : ((w' : Dyadic) : ℝ) ≤ x := hwRD.2.1
      have h_x_le_z : x ≤ ((z' : Dyadic) : ℝ) := hzRU.2.1
      have h_F_adj : ∀ y : Dyadic, y ∈ F₁ →
          ((w' : Dyadic) : ℝ) < ((y : Dyadic) : ℝ) →
          ((z' : Dyadic) : ℝ) ≤ ((y : Dyadic) : ℝ) :=
        F_adjacent_of_RN_round_pair (Or.inl hwRD) (Or.inr hzRU) h_w_le_x h_x_le_z
      have h_mid_F₂ : Dyadic.midpoint w' z' ∈ F₂ :=
        midpoint_F₁_in_F₂_of_F_adjacent hsub_ext1 hw'F₁ hz'F₁
          h_w_lt_z h_F_adj
      have h_mid_F₁_ext1 : Dyadic.midpoint w' z' ∈ F₁.extend 1 :=
        midpoint_in_F₁_extend_one_of_F_adjacent hw'F₁ hz'F₁
          h_w_lt_z h_F_adj
      have h_mid_real : ((Dyadic.midpoint w' z' : Dyadic) : ℝ) =
          (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2 := Dyadic.coe_midpoint w' z'
      have h_z_ne_m : ((z : Dyadic) : ℝ) ≠ ((Dyadic.midpoint w' z' : Dyadic) : ℝ) := by
        intro h_eq_m
        apply hz_not_F₁_ext1
        have : z = Dyadic.midpoint w' z' := (Dyadic.coe_real_inj z _).mp h_eq_m
        rw [this]; exact h_mid_F₁_ext1
      have h_w_le_z_F : ((w' : Dyadic) : ℝ) ≤ ((z : Dyadic) : ℝ) := by
        rcases hz_adj with hzRD' | hzRU'
        · exact hzRD'.2.2 w' hw'F₂ h_w_le_x
        · linarith [hzRU'.2.1]
      have h_z_le_z'_F : ((z : Dyadic) : ℝ) ≤ ((z' : Dyadic) : ℝ) := by
        rcases hz_adj with hzRD' | hzRU'
        · linarith [hzRD'.2.1]
        · exact hzRU'.2.2 z' hz'F₂ h_x_le_z
      have h_w_lt_z_F : ((w' : Dyadic) : ℝ) < ((z : Dyadic) : ℝ) :=
        lt_of_le_of_ne h_w_le_z_F (Ne.symm h_z_ne_w'_real)
      have h_z_lt_z' : ((z : Dyadic) : ℝ) < ((z' : Dyadic) : ℝ) :=
        lt_of_le_of_ne h_z_le_z'_F h_z_ne_z'_real
      have hz_RU_z' : RoundsFinite F₁ .toPositive z z' := by
        refine ⟨hz'F₁, le_of_lt h_z_lt_z', ?_⟩
        intro y hyF₁ h_z_le_y
        have h_w_lt_y : ((w' : Dyadic) : ℝ) < ((y : Dyadic) : ℝ) := by linarith
        exact h_F_adj y hyF₁ h_w_lt_y
      have h_z_close : |((z : Dyadic) : ℝ) - ((w' : Dyadic) : ℝ)|
          ≤ |((z : Dyadic) : ℝ) - ((z' : Dyadic) : ℝ)| :=
        hw_close_inner z' hz'F₁ (Or.inr hz_RU_z')
      have h_z_w_pos : 0 < ((z : Dyadic) : ℝ) - ((w' : Dyadic) : ℝ) := by linarith
      have h_z_z_neg : ((z : Dyadic) : ℝ) - ((z' : Dyadic) : ℝ) < 0 := by linarith
      rw [abs_of_pos h_z_w_pos, abs_of_neg h_z_z_neg] at h_z_close
      have h_z_le_m : ((z : Dyadic) : ℝ)
          ≤ (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2 := by linarith
      have h_z_lt_m : ((z : Dyadic) : ℝ)
          < (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2 := by
        have : ((z : Dyadic) : ℝ) ≠ (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2 := by
          rw [← h_mid_real]; exact h_z_ne_m
        exact lt_of_le_of_ne h_z_le_m this
      have h_x_le_m : x ≤ (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2 := by
        rcases hz_adj with hzRD' | hzRU'
        · by_contra h_x_gt
          push Not at h_x_gt
          have h_m_le_x : (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2 ≤ x :=
            le_of_lt h_x_gt
          have h_m_le_x' : ((Dyadic.midpoint w' z' : Dyadic) : ℝ) ≤ x := by
            rw [h_mid_real]; exact h_m_le_x
          have h_m_le_z : ((Dyadic.midpoint w' z' : Dyadic) : ℝ) ≤ ((z : Dyadic) : ℝ) :=
            hzRD'.2.2 (Dyadic.midpoint w' z') h_mid_F₂ h_m_le_x'
          rw [h_mid_real] at h_m_le_z
          linarith
        · linarith [hzRU'.2.1]
      have h_x_w_pos : 0 ≤ x - ((w' : Dyadic) : ℝ) := by linarith
      have h_x_z_nonpos : x - ((z' : Dyadic) : ℝ) ≤ 0 := by linarith
      rw [abs_of_nonneg h_x_w_pos, abs_of_nonpos h_x_z_nonpos]
      linarith
    · have hwRU : RoundsFinite F₁ .toPositive x w' := by
        rcases h_adj_x with hwRD | hwRU
        · exfalso
          rcases hz'_adj with hzRD | hzRU
          · have h1 : ((w' : Dyadic) : ℝ) ≤ ((z' : Dyadic) : ℝ) :=
              hzRD.2.2 w' hw'F₁ hwRD.2.1
            have h2 : ((z' : Dyadic) : ℝ) ≤ ((w' : Dyadic) : ℝ) :=
              hwRD.2.2 z' hz'F₁ hzRD.2.1
            exact h_w_ne_z' (le_antisymm h1 h2)
          · linarith [hwRD.2.1, hzRU.2.1]
        · exact hwRU
      have hzRD : RoundsFinite F₁ .toNegative x z' := by
        rcases hz'_adj with hzRD | hzRU
        · exact hzRD
        · exfalso
          have h1 : ((w' : Dyadic) : ℝ) ≤ ((z' : Dyadic) : ℝ) :=
            hwRU.2.2 z' hz'F₁ hzRU.2.1
          have h2 : ((z' : Dyadic) : ℝ) ≤ ((w' : Dyadic) : ℝ) :=
            hzRU.2.2 w' hw'F₁ hwRU.2.1
          exact h_w_ne_z' (le_antisymm h1 h2)
      have h_x_le_w : x ≤ ((w' : Dyadic) : ℝ) := hwRU.2.1
      have h_z_le_x : ((z' : Dyadic) : ℝ) ≤ x := hzRD.2.1
      have h_F_adj : ∀ y : Dyadic, y ∈ F₁ →
          ((z' : Dyadic) : ℝ) < ((y : Dyadic) : ℝ) →
          ((w' : Dyadic) : ℝ) ≤ ((y : Dyadic) : ℝ) :=
        F_adjacent_of_RN_round_pair (Or.inl hzRD) (Or.inr hwRU) h_z_le_x h_x_le_w
      have h_mid_F₂_swap : Dyadic.midpoint z' w' ∈ F₂ :=
        midpoint_F₁_in_F₂_of_F_adjacent hsub_ext1 hz'F₁ hw'F₁
          h_z_lt_w h_F_adj
      have h_mid_F₁_ext1_swap : Dyadic.midpoint z' w' ∈ F₁.extend 1 :=
        midpoint_in_F₁_extend_one_of_F_adjacent hz'F₁ hw'F₁
          h_z_lt_w h_F_adj
      have h_mid_swap_eq : Dyadic.midpoint z' w' = Dyadic.midpoint w' z' :=
        Dyadic.midpoint_comm z' w'
      have h_mid_F₂ : Dyadic.midpoint w' z' ∈ F₂ := h_mid_swap_eq ▸ h_mid_F₂_swap
      have h_mid_F₁_ext1 : Dyadic.midpoint w' z' ∈ F₁.extend 1 :=
        h_mid_swap_eq ▸ h_mid_F₁_ext1_swap
      have h_mid_real : ((Dyadic.midpoint w' z' : Dyadic) : ℝ) =
          (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2 := Dyadic.coe_midpoint w' z'
      have h_z_ne_m : ((z : Dyadic) : ℝ) ≠ ((Dyadic.midpoint w' z' : Dyadic) : ℝ) := by
        intro h_eq_m
        apply hz_not_F₁_ext1
        have : z = Dyadic.midpoint w' z' := (Dyadic.coe_real_inj z _).mp h_eq_m
        rw [this]; exact h_mid_F₁_ext1
      have h_z_le_w_F : ((z : Dyadic) : ℝ) ≤ ((w' : Dyadic) : ℝ) := by
        rcases hz_adj with hzRD' | hzRU'
        · linarith [hzRD'.2.1]
        · exact hzRU'.2.2 w' hw'F₂ h_x_le_w
      have h_z'_le_z_F : ((z' : Dyadic) : ℝ) ≤ ((z : Dyadic) : ℝ) := by
        rcases hz_adj with hzRD' | hzRU'
        · exact hzRD'.2.2 z' hz'F₂ h_z_le_x
        · linarith [hzRU'.2.1]
      have h_z_lt_w_F : ((z : Dyadic) : ℝ) < ((w' : Dyadic) : ℝ) :=
        lt_of_le_of_ne h_z_le_w_F h_z_ne_w'_real
      have h_z'_lt_z : ((z' : Dyadic) : ℝ) < ((z : Dyadic) : ℝ) :=
        lt_of_le_of_ne h_z'_le_z_F (Ne.symm h_z_ne_z'_real)
      have hz_RD_z' : RoundsFinite F₁ .toNegative z z' := by
        refine ⟨hz'F₁, le_of_lt h_z'_lt_z, ?_⟩
        intro y hyF₁ h_y_le_z
        by_contra h_lt
        push Not at h_lt
        have h_w_le_y := h_F_adj y hyF₁ h_lt
        linarith
      have h_z_close : |((z : Dyadic) : ℝ) - ((w' : Dyadic) : ℝ)|
          ≤ |((z : Dyadic) : ℝ) - ((z' : Dyadic) : ℝ)| :=
        hw_close_inner z' hz'F₁ (Or.inl hz_RD_z')
      have h_z_w_neg : ((z : Dyadic) : ℝ) - ((w' : Dyadic) : ℝ) < 0 := by linarith
      have h_z_z_pos : 0 < ((z : Dyadic) : ℝ) - ((z' : Dyadic) : ℝ) := by linarith
      rw [abs_of_neg h_z_w_neg, abs_of_pos h_z_z_pos] at h_z_close
      have h_m_le_z : (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2
          ≤ ((z : Dyadic) : ℝ) := by linarith
      have h_m_lt_z : (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2
          < ((z : Dyadic) : ℝ) := by
        have : (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2 ≠ ((z : Dyadic) : ℝ) := by
          intro h_eq2
          rw [← h_mid_real] at h_eq2
          exact h_z_ne_m h_eq2.symm
        exact lt_of_le_of_ne h_m_le_z this
      have h_m_le_x : (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2 ≤ x := by
        rcases hz_adj with hzRD' | hzRU'
        · linarith [hzRD'.2.1]
        · by_contra h_x_lt
          push Not at h_x_lt
          have h_x_le_m : x ≤ (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2 :=
            le_of_lt h_x_lt
          have h_x_le_m' : x ≤ ((Dyadic.midpoint w' z' : Dyadic) : ℝ) := by
            rw [h_mid_real]; exact h_x_le_m
          have h_z_le_m : ((z : Dyadic) : ℝ) ≤ ((Dyadic.midpoint w' z' : Dyadic) : ℝ) :=
            hzRU'.2.2 (Dyadic.midpoint w' z') h_mid_F₂ h_x_le_m'
          rw [h_mid_real] at h_z_le_m
          linarith
      have h_x_w_neg : x - ((w' : Dyadic) : ℝ) ≤ 0 := by linarith
      have h_x_z_pos : 0 ≤ x - ((z' : Dyadic) : ℝ) := by linarith
      rw [abs_of_nonpos h_x_w_neg, abs_of_nonneg h_x_z_pos]
      linarith

/-- The "no-tie" derivation used by the nearest-rounding branch of `rndRTO_RN`.
Given that `z = RTO F₂ x` is unrepresentable in `F₁` and that `z'` is supposedly
tied with `w'` for `x`'s nearest-rounding in `F₁`, derive `False`: the tie
equation forces `x = midpoint(w', z')`, F-adjacency makes that midpoint lie in
`F₂`, and `RoundsFinite.toOdd_unique_of_mem` then forces `z = midpoint`, so
`x = z`, contradicting `hxne`. -/
private lemma rndRTO_no_tie_contradiction {F₁ F₂ : FiniteFormat}
    (hsub_ext1 : (F₁.extend 1).toFormat ⊆ F₂.toFormat)
    {x : ℝ} {z w' z' : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hxne : x ≠ (z : ℝ))
    (hw'F₁ : w' ∈ F₁) (hz'F₁ : z' ∈ F₁)
    (h_adj_x : RoundsFinite F₁ .toNegative x w' ∨ RoundsFinite F₁ .toPositive x w')
    (hz'_adj : RoundsFinite F₁ .toNegative x z' ∨ RoundsFinite F₁ .toPositive x z')
    (hz'_ne_w' : z' ≠ w')
    (hz'_eq_dist : |x - ((w' : Dyadic) : ℝ)| = |x - ((z' : Dyadic) : ℝ)|) :
    False := by
  have hx_mid : x = ((w' : ℝ) + (z' : ℝ)) / 2 :=
    nearest_midpoint_of_tie hz'_ne_w' hz'_eq_dist
  have hw'_ne_z'_real : ((w' : Dyadic) : ℝ) ≠ ((z' : Dyadic) : ℝ) := by
    intro heq
    apply hz'_ne_w'
    exact (Dyadic.coe_real_inj z' w').mp heq.symm
  -- F-adjacency: between w' and z' (in either order), no F₁ element strictly between.
  have h_F_adj_pair : ∀ (a b : Dyadic), a ∈ F₁ → b ∈ F₁ →
      ((a : ℝ) = (w' : ℝ) ∧ (b : ℝ) = (z' : ℝ)) ∨
        ((a : ℝ) = (z' : ℝ) ∧ (b : ℝ) = (w' : ℝ)) →
      ((a : Dyadic) : ℝ) < ((b : Dyadic) : ℝ) →
      ∀ y : Dyadic, y ∈ F₁ → ((a : Dyadic) : ℝ) < ((y : Dyadic) : ℝ) →
        ((b : Dyadic) : ℝ) ≤ ((y : Dyadic) : ℝ) := by
    intro a b haF₁ hbF₁ h_ab_eq h_ab_lt y hyF₁ h_a_lt_y
    have hx_mid' : x = ((a : ℝ) + (b : ℝ)) / 2 := by
      rcases h_ab_eq with ⟨ha_eq, hb_eq⟩ | ⟨ha_eq, hb_eq⟩
      · rw [ha_eq, hb_eq]; exact hx_mid
      · rw [ha_eq, hb_eq, hx_mid]; ring
    have h_a_lt_x : (a : ℝ) < x := by rw [hx_mid']; linarith
    have h_x_lt_b : x < (b : ℝ) := by rw [hx_mid']; linarith
    by_cases h_y_le_x : ((y : Dyadic) : ℝ) ≤ x
    · exfalso
      rcases h_ab_eq with ⟨ha_eq, _⟩ | ⟨ha_eq, _⟩
      · rcases h_adj_x with hwRD | hwRU
        · obtain ⟨_, _, hw_max⟩ := hwRD
          have h_y_le_w' : ((y : Dyadic) : ℝ) ≤ (w' : ℝ) := hw_max y hyF₁ h_y_le_x
          rw [ha_eq] at h_a_lt_y
          linarith
        · obtain ⟨_, hxw, _⟩ := hwRU
          rw [ha_eq] at h_a_lt_x
          linarith
      · rcases hz'_adj with hzRD | hzRU
        · obtain ⟨_, _, hz_max⟩ := hzRD
          have h_y_le_z' : ((y : Dyadic) : ℝ) ≤ (z' : ℝ) := hz_max y hyF₁ h_y_le_x
          rw [ha_eq] at h_a_lt_y
          linarith
        · obtain ⟨_, hxz, _⟩ := hzRU
          rw [ha_eq] at h_a_lt_x
          linarith
    · push Not at h_y_le_x
      rcases h_ab_eq with ⟨_, hb_eq⟩ | ⟨_, hb_eq⟩
      · rcases hz'_adj with hzRD | hzRU
        · obtain ⟨_, hzx_le, _⟩ := hzRD
          rw [hb_eq] at h_x_lt_b
          linarith
        · obtain ⟨_, _, hz_min⟩ := hzRU
          have h_z'_le_y : (z' : ℝ) ≤ ((y : Dyadic) : ℝ) := hz_min y hyF₁ (le_of_lt h_y_le_x)
          rw [hb_eq]; exact h_z'_le_y
      · rcases h_adj_x with hwRD | hwRU
        · obtain ⟨_, hwx_le, _⟩ := hwRD
          rw [hb_eq] at h_x_lt_b
          linarith
        · obtain ⟨_, _, hw_min⟩ := hwRU
          have h_w'_le_y : (w' : ℝ) ≤ ((y : Dyadic) : ℝ) := hw_min y hyF₁ (le_of_lt h_y_le_x)
          rw [hb_eq]; exact h_w'_le_y
  have h_mid_F₂ : Dyadic.midpoint w' z' ∈ F₂ := by
    rcases lt_or_gt_of_ne hw'_ne_z'_real with h_w_lt_z | h_z_lt_w
    · have h_adj_pair := h_F_adj_pair w' z' hw'F₁ hz'F₁
        (Or.inl ⟨rfl, rfl⟩) h_w_lt_z
      exact midpoint_F₁_in_F₂_of_F_adjacent hsub_ext1 hw'F₁ hz'F₁
        h_w_lt_z h_adj_pair
    · have h_mid_swap : Dyadic.midpoint w' z' = Dyadic.midpoint z' w' :=
        Dyadic.midpoint_comm w' z'
      rw [h_mid_swap]
      have h_adj_pair := h_F_adj_pair z' w' hz'F₁ hw'F₁
        (Or.inr ⟨rfl, rfl⟩) h_z_lt_w
      exact midpoint_F₁_in_F₂_of_F_adjacent hsub_ext1 hz'F₁ hw'F₁
        h_z_lt_w h_adj_pair
  set m := Dyadic.midpoint w' z' with hm_def
  have hm_eq : ((m : Dyadic) : ℝ) = ((w' : ℝ) + (z' : ℝ)) / 2 := by
    rw [hm_def, Dyadic.coe_midpoint]
  have hm_x : (m : ℝ) = x := by rw [hm_eq, ← hx_mid]
  have hz_eq : z = m := by
    have hz' : RoundsFinite F₂ .toOdd ((m : ℝ)) z := by rw [hm_x]; exact hz
    exact RoundsFinite.toOdd_unique_of_mem h_mid_F₂ hz'
  exact hxne (by rw [hz_eq]; exact hm_x.symm)

/-- Shared core for the nearest-rounding branch of `rndRTO_RN`. From the
derived subset facts plus extracted hypotheses from the inner nearest-rounding,
produces the three facts needed by either tie-break: adjacency transfer
(`h_adj_x`), closeness transfer (`h_close`), and an absence-of-tie property
(`h_no_tie`). The two `tb` branches of `rndRTO_RN` differ only in how they
consume `h_no_tie`. -/
private theorem rndRTO_nearest_facts {F₁ F₂ : FiniteFormat}
    (hsub2 : (F₁.extend 2).toFormat ⊆ F₂.toFormat)
    (hsub_ext1 : (F₁.extend 1).toFormat ⊆ F₂.toFormat)
    (hsub' : F₁.toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ+) : WithTop ℕ+) ≤ F₂.p)
    {x : ℝ} {z w' : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hxne : x ≠ (z : ℝ))
    (hw'F₁ : w' ∈ F₁)
    (hw_adj : RoundsFinite F₁ .toNegative ((z : Dyadic) : ℝ) w'
              ∨ RoundsFinite F₁ .toPositive ((z : Dyadic) : ℝ) w')
    (hw_close_inner : ∀ z' : Dyadic, z' ∈ F₁ →
        (RoundsFinite F₁ .toNegative ((z : Dyadic) : ℝ) z'
          ∨ RoundsFinite F₁ .toPositive ((z : Dyadic) : ℝ) z') →
        |((z : Dyadic) : ℝ) - ((w' : Dyadic) : ℝ)| ≤
            |((z : Dyadic) : ℝ) - ((z' : Dyadic) : ℝ)|) :
    (RoundsFinite F₁ .toNegative x w' ∨ RoundsFinite F₁ .toPositive x w') ∧
    (∀ z' : Dyadic, z' ∈ F₁ →
        (RoundsFinite F₁ .toNegative x z' ∨ RoundsFinite F₁ .toPositive x z') →
        |x - ((w' : Dyadic) : ℝ)| ≤ |x - ((z' : Dyadic) : ℝ)|) ∧
    (∀ z' : Dyadic, z' ∈ F₁ →
        (RoundsFinite F₁ .toNegative x z' ∨ RoundsFinite F₁ .toPositive x z') →
        z' ≠ w' →
        |x - ((w' : Dyadic) : ℝ)| = |x - ((z' : Dyadic) : ℝ)| → False) := by
  have hF₁_sub_ext1 : F₁.toFormat ⊆ (F₁.extend 1).toFormat :=
    Format.self_subset_extend F₁.toFormat 1
  have hz_not_F₁ : z ∉ F₁ :=
    toOdd_notMem_of_extend_subset hsub_ext1 hp_F₂ hz hxne
  have hz_adj : RoundsFinite F₂ .toNegative x z ∨ RoundsFinite F₂ .toPositive x z :=
    isFaithfulRound_iff_directed.mp hz.2.1
  have hz_ne_w' : (z : ℝ) ≠ (w' : ℝ) := by
    intro h_eq
    apply hz_not_F₁
    rw [show z = w' from (Dyadic.coe_real_inj z w').mp h_eq]
    exact hw'F₁
  -- Adjacency transfer (4-way case split).
  have h_adj_x : RoundsFinite F₁ .toNegative x w' ∨ RoundsFinite F₁ .toPositive x w' := by
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
  have hsub_double : ((F₁.extend 1).extend 1).toFormat ⊆ F₂.toFormat := fun y hy =>
    hsub2 y (Format.extend_one_extend_one_subset_extend_two F₁.toFormat y hy)
  have hz_not_F₁_ext1 : z ∉ F₁.extend 1 :=
    toOdd_notMem_of_extend_subset hsub_double hp_F₂ hz hxne
  have h_close := rndRTO_RN_close_transfer hsub_ext1 hsub' hF₁_sub_ext1
    hz_adj hw'F₁ h_adj_x hw_close_inner hz_not_F₁_ext1
  refine ⟨h_adj_x, h_close, ?_⟩
  intro z' hz'F₁ hz'_adj hz'_ne_w' hz'_eq_dist
  exact rndRTO_no_tie_contradiction hsub_ext1 hz hxne hw'F₁ hz'F₁
    h_adj_x hz'_adj hz'_ne_w' hz'_eq_dist

/-- **rnd-RTO-RN** (Fig. 9), paper-aligned form for round-to-odd followed by
round-to-nearest, parameterized by the nearest-rounding tie-break `tb`.
Covers both RNE (`tb = .toEven`) and RNA (`tb = .awayZero`) in a single
theorem: the hypothesis `hsub` encodes the paper's RN containment, uniform with
the `rndRTO_RTZ`/`rndRTO_RAZ` signatures. -/
theorem rndRTO_RN {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
              ⊆ F₂.toFormat)
    {tb : TieBreak} {x : ℝ} {z w' : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z)
    (hw : RoundsFinite F₁ (.nearest tb) (z : ℝ) w') :
    RoundsFinite F₁ (.nearest tb) x w' := by
  rcases hp_F₂_or_F₁_trivial_RN hsub with hp_F₂ | hF₁_triv
  swap
  · -- F₁ trivial: handled uniformly for any tb.
    exact RoundsFinite.nearest_of_trivial hF₁_triv hw.1
  -- main case: 2 ≤ F₂.p. Derive the weaker subset chain.
  have hsub2 : (F₁.extend 2).toFormat ⊆ F₂.toFormat :=
    extend_two_subset_of_paper_RN_subset hsub
  have h_ext1_sub_ext2 : (F₁.extend 1).toFormat ⊆ (F₁.extend 2).toFormat :=
    Format.extend_mono F₁.toFormat (by exact_mod_cast (by omega : (1 : ℕ) ≤ 2) : (1 : ℕ+) ≤ 2)
  have hsub_ext1 : (F₁.extend 1).toFormat ⊆ F₂.toFormat := fun y hy =>
    hsub2 _ (h_ext1_sub_ext2 _ hy)
  have hsub' : F₁.toFormat ⊆ F₂.toFormat := fun y hy =>
    hsub_ext1 _ (Format.self_subset_extend F₁.toFormat 1 _ hy)
  rcases eq_or_ne ((z : ℝ)) x with hzx | hzx
  · -- x = z: hw already has the right shape after rewriting.
    rw [hzx] at hw; exact hw
  have hxne : x ≠ (z : ℝ) := fun h => hzx h.symm
  -- Non-trivial case: destructure hw (requires cases tb), then assemble via
  -- rndRTO_nearest_facts. The IsFaithfulRound↔directed conversions sit at the
  -- nearest-spec boundary.
  cases tb with
  | toEven =>
    obtain ⟨hw'F₁, hw_faithful, hw_close, _⟩ := hw
    have hw_adj := isFaithfulRound_iff_directed.mp hw_faithful
    have hw_close_inner : ∀ z'' : Dyadic, z'' ∈ F₁ →
        (RoundsFinite F₁ .toNegative ((z : Dyadic) : ℝ) z''
          ∨ RoundsFinite F₁ .toPositive ((z : Dyadic) : ℝ) z'') →
        |((z : Dyadic) : ℝ) - ((w' : Dyadic) : ℝ)| ≤
            |((z : Dyadic) : ℝ) - ((z'' : Dyadic) : ℝ)| :=
      fun z'' h1 h2 => hw_close z'' h1 (isFaithfulRound_iff_directed.mpr h2)
    obtain ⟨h_adj_x, h_close, h_no_tie⟩ :=
      rndRTO_nearest_facts hsub2 hsub_ext1 hsub' hp_F₂ hz hxne hw'F₁ hw_adj hw_close_inner
    refine ⟨hw'F₁, isFaithfulRound_iff_directed.mpr h_adj_x,
      fun z' h1 h2 => h_close z' h1 (isFaithfulRound_iff_directed.mp h2), ?_⟩
    rintro ⟨z', hz'F₁, hz'_faithful, hz'_ne_w', hz'_eq_dist⟩
    exact (h_no_tie z' hz'F₁ (isFaithfulRound_iff_directed.mp hz'_faithful)
      hz'_ne_w' hz'_eq_dist).elim
  | awayZero =>
    obtain ⟨hw'F₁, hw_faithful, hw_close, _⟩ := hw
    have hw_adj := isFaithfulRound_iff_directed.mp hw_faithful
    have hw_close_inner : ∀ z'' : Dyadic, z'' ∈ F₁ →
        (RoundsFinite F₁ .toNegative ((z : Dyadic) : ℝ) z''
          ∨ RoundsFinite F₁ .toPositive ((z : Dyadic) : ℝ) z'') →
        |((z : Dyadic) : ℝ) - ((w' : Dyadic) : ℝ)| ≤
            |((z : Dyadic) : ℝ) - ((z'' : Dyadic) : ℝ)| :=
      fun z'' h1 h2 => hw_close z'' h1 (isFaithfulRound_iff_directed.mpr h2)
    obtain ⟨h_adj_x, h_close, h_no_tie⟩ :=
      rndRTO_nearest_facts hsub2 hsub_ext1 hsub' hp_F₂ hz hxne hw'F₁ hw_adj hw_close_inner
    refine ⟨hw'F₁, isFaithfulRound_iff_directed.mpr h_adj_x,
      fun z' h1 h2 => h_close z' h1 (isFaithfulRound_iff_directed.mp h2), ?_⟩
    intro z' hz'F₁ hz'_faithful hz'_ne_w' hz'_eq_dist
    exact (h_no_tie z' hz'F₁ (isFaithfulRound_iff_directed.mp hz'_faithful)
      hz'_ne_w' hz'_eq_dist).elim

/-- **rnd-RTP-RTP** (round toward `+∞`, chained). For `x > 0` it is RAZ→RAZ
(`rndRAZ_RAZ_pos`); for `x ≤ 0` it is RTZ→RTZ (`rndRTZ_RTZ`). The two regimes
are connected to RTP through the sign-bridge iff lemmas. Only needs `F₁ ⊆ F₂`. -/
theorem rndRTP_RTP {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
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
      (rndRTZ_RTZ hsub hz_RTZ hw_RTZ)
  · -- x > 0: bridge to RAZ.
    have hx_pos : 0 < x := not_le.mp hx_le
    have hz_nn : 0 ≤ (z : ℝ) := le_trans hx_pos.le hz.2.1
    have hz_RAZ : RoundsFinite F₂ .awayZero x z :=
      (RoundsFinite.toPositive_iff_awayZero_of_nonneg F₂ hx_pos.le z).mp hz
    have hw_RAZ : RoundsFinite F₁ .awayZero (z : ℝ) w :=
      (RoundsFinite.toPositive_iff_awayZero_of_nonneg F₁ hz_nn w).mp hw
    exact (RoundsFinite.toPositive_iff_awayZero_of_nonneg F₁ hx_pos.le w).mpr
      (rndRAZ_RAZ_pos hsub hx_pos hz_RAZ hw_RAZ)

/-- **rnd-RTN-RTN** (round toward `−∞`, chained). For `x < 0` it is RAZ→RAZ
(`rndRAZ_RAZ`); for `x ≥ 0` it is RTZ→RTZ (`rndRTZ_RTZ`), connected to RTN via
the sign-bridge iff lemmas. Only needs `F₁ ⊆ F₂`. -/
theorem rndRTN_RTN {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
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
      (rndRAZ_RAZ hsub hz_RAZ hw_RAZ)
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
      (rndRTZ_RTZ hsub hz_RTZ hw_RTZ)

/-! # `Rounds`-level double rounding (overflow-aware)

The six Fig. 9 rules over the full `Rounds` relation. Shared infrastructure:
membership bridges across `FiniteFormat.unbounded`, per-mode *restrict*
(`unbounded spec + in-bound ⟹ bounded spec`) and *lift* (`bounded spec +
in-bound unbounded rounding ⟹ unbounded spec`) lemmas, and parity-witness
transport between formats agreeing on `(p, exp)`. -/

/-! ## Membership bridges across `FiniteFormat.unbounded` -/

/-- Bounded membership weakens to unbounded membership (drop the bound check). -/
private theorem mem_unbounded_of_mem {F : FiniteFormat} {d : Dyadic}
    (h : d ∈ F) : d ∈ F.unbounded :=
  ⟨h.1, h.2.1, trivial⟩

/-- Unbounded membership plus an explicit bound check gives bounded membership. -/
private theorem mem_of_mem_unbounded_of_boundOK {F : FiniteFormat} {d : Dyadic}
    (h : d ∈ F.unbounded) (hb : Format.boundOK F.b d) : d ∈ F :=
  ⟨h.1, h.2.1, hb⟩

/-! ## Restrict / lift for `.toZero` -/

/-- **Restrict** (`.toZero`): an in-bound unbounded rounding is also the
bounded rounding (competitors only shrink). -/
private theorem RoundsFinite.toZero_restrict {F : FiniteFormat} {x : ℝ}
    {y : Dyadic} (h : RoundsFinite F.unbounded .toZero x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F .toZero x y := by
  obtain ⟨hmem, hbnd, hsign, hmax⟩ := h
  exact ⟨mem_of_mem_unbounded_of_boundOK hmem hb, hbnd, hsign,
    fun v hv => hmax v (mem_unbounded_of_mem hv)⟩

/-- **Lift** (`.toZero`): if `w` is the bounded rounding of `x` and the
unbounded rounding `y` of `x` happens to be in-bound, then `w` is also the
unbounded rounding (any unbounded competitor is dominated by `y`, which is
itself a bounded competitor). -/
private theorem RoundsFinite.toZero_lift {F : FiniteFormat} {x : ℝ}
    {w y : Dyadic} (hw : RoundsFinite F .toZero x w)
    (hy : RoundsFinite F.unbounded .toZero x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F.unbounded .toZero x w := by
  obtain ⟨hwmem, hwbnd, hwsign, hwmax⟩ := hw
  obtain ⟨hymem, hybnd, hysign, hymax⟩ := hy
  refine ⟨mem_unbounded_of_mem hwmem, hwbnd, hwsign, ?_⟩
  intro v hv hvbnd hvsign
  have h1 : |(v : ℝ)| ≤ |(y : ℝ)| := hymax v hv hvbnd hvsign
  have h2 : |(y : ℝ)| ≤ |(w : ℝ)| :=
    hwmax y (mem_of_mem_unbounded_of_boundOK hymem hb) hybnd hysign
  exact le_trans h1 h2

/-! ## Restrict / lift for `.awayZero` -/

/-- **Restrict** (`.awayZero`): an in-bound unbounded rounding is also the
bounded rounding (competitors only shrink). -/
private theorem RoundsFinite.awayZero_restrict {F : FiniteFormat} {x : ℝ}
    {y : Dyadic} (h : RoundsFinite F.unbounded .awayZero x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F .awayZero x y := by
  obtain ⟨hmem, hbnd, hsign, hmin⟩ := h
  exact ⟨mem_of_mem_unbounded_of_boundOK hmem hb, hbnd, hsign,
    fun v hv => hmin v (mem_unbounded_of_mem hv)⟩

/-- **Lift** (`.awayZero`): if `w` is the bounded rounding of `x` and the
unbounded rounding `y` of `x` happens to be in-bound, then `w` is also the
unbounded rounding (any unbounded competitor dominates `y`, which is itself
a bounded competitor). -/
private theorem RoundsFinite.awayZero_lift {F : FiniteFormat} {x : ℝ}
    {w y : Dyadic} (hw : RoundsFinite F .awayZero x w)
    (hy : RoundsFinite F.unbounded .awayZero x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F.unbounded .awayZero x w := by
  obtain ⟨hwmem, hwbnd, hwsign, hwmin⟩ := hw
  obtain ⟨hymem, hybnd, hysign, hymin⟩ := hy
  refine ⟨mem_unbounded_of_mem hwmem, hwbnd, hwsign, ?_⟩
  intro v hv hvbnd hvsign
  have h1 : |(w : ℝ)| ≤ |(y : ℝ)| :=
    hwmin y (mem_of_mem_unbounded_of_boundOK hymem hb) hybnd hysign
  have h2 : |(y : ℝ)| ≤ |(v : ℝ)| := hymin v hv hvbnd hvsign
  exact le_trans h1 h2

/-! ## Parity transport across `unbounded`

`numDigits`, `IsOdd`, and `IsUndefined` only read `p` and `exp`, so parity
witnesses transport between formats that agree on `(p, exp)` — in particular
between `F` and `F.unbounded`. -/

/-- `numDigits` only reads `(p, exp)`. -/
private theorem numDigits_congr {F G : FiniteFormat} (hp : F.p = G.p)
    (he : F.exp = G.exp) (x : ℝ) : F.numDigits x = G.numDigits x := by
  unfold FiniteFormat.numDigits
  rw [hp, he]

/-- Transport a parity witness (`∃ F', F'.toFormat = _ ∧ F'.IsOdd y`) between
formats agreeing on `(p, exp)`. -/
private theorem parity_witness_congr {F G : FiniteFormat} (hp : F.p = G.p)
    (he : F.exp = G.exp) {y : Dyadic}
    (h : ∃ F' : ParityFormat, F'.toFormat = F.toFormat ∧ F'.IsOdd y) :
    ∃ F'' : ParityFormat, F''.toFormat = G.toFormat ∧ F''.IsOdd y := by
  obtain ⟨F', hFeq, hodd⟩ := h
  have hp' : F'.p = G.p := by rw [congrArg Format.p hFeq]; exact hp
  have he' : F'.exp = G.exp := by rw [congrArg Format.exp hFeq]; exact he
  refine ⟨⟨G, by rw [← hp', ← he']; exact F'.parity⟩, rfl, ?_⟩
  obtain ⟨c, e, hrep, hpar⟩ := hodd
  refine ⟨c, e, ?_, ?_⟩
  · change Dyadic.IsRepresentableAtP (G.numDigits (y : ℝ)).toNat c e y
    rwa [numDigits_congr (F := G) (G := F'.toFiniteFormat) hp'.symm he'.symm (y : ℝ)]
  · change if G.p = ((1 : ℕ+) : WithTop ℕ+) then
        Odd (e - WithBot.unbotD 0 G.exp + 1) else Odd c
    rw [← hp', ← he']
    exact hpar

/-! ## Faithful-round restrict / lift -/

/-- Directed modes are never undefined. -/
private theorem not_isUndefined_toNegative (F : FiniteFormat) :
    ¬ F.IsUndefined .toNegative := by
  rintro ⟨-, -, h | h⟩ <;> simp at h

private theorem not_isUndefined_toPositive (F : FiniteFormat) :
    ¬ F.IsUndefined .toPositive := by
  rintro ⟨-, -, h | h⟩ <;> simp at h

/-- A dyadic between two in-bound dyadics is in-bound. -/
private theorem boundOK_of_between {b : WithTop NonNegDyadic} {lo hi g : Dyadic}
    (hblo : Format.boundOK b lo) (hbhi : Format.boundOK b hi)
    (h1 : (lo : ℝ) ≤ (g : ℝ)) (h2 : (g : ℝ) ≤ (hi : ℝ)) :
    Format.boundOK b g := by
  cases b with
  | top => trivial
  | coe b =>
    have h1' : (lo : ℚ) ≤ (g : ℚ) := by
      rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast] at h1
      exact_mod_cast h1
    have h2' : (g : ℚ) ≤ (hi : ℚ) := by
      rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast] at h2
      exact_mod_cast h2
    have hblo' : |(lo : ℚ)| ≤ ((b.val : Dyadic) : ℚ) := hblo
    have hbhi' : |(hi : ℚ)| ≤ ((b.val : Dyadic) : ℚ) := hbhi
    change |(g : ℚ)| ≤ ((b.val : Dyadic) : ℚ)
    exact abs_le.mpr ⟨by linarith [(abs_le.mp hblo').1], by linarith [(abs_le.mp hbhi').2]⟩

/-- **Restrict** for `IsFaithfulRound`: a faithful rounding in `F.unbounded`
that lies in `F` is faithful in `F` (competitors only shrink). -/
private theorem IsFaithfulRound.restrict {F : FiniteFormat} {x : ℝ} {y : Dyadic}
    (h : IsFaithfulRound F.unbounded x y) (hb : Format.boundOK F.b y) :
    IsFaithfulRound F x y := by
  rcases h with ⟨hmem, hle, hmax⟩ | ⟨hmem, hge, hmin⟩
  · exact Or.inl ⟨mem_of_mem_unbounded_of_boundOK hmem hb, hle,
      fun v hv => hmax v (mem_unbounded_of_mem hv)⟩
  · exact Or.inr ⟨mem_of_mem_unbounded_of_boundOK hmem hb, hge,
      fun v hv => hmin v (mem_unbounded_of_mem hv)⟩

/-- **Lift** for `IsFaithfulRound`: a faithful rounding `w` of `x` in `F` is
faithful in `F.unbounded`, provided *some* in-bound `y` is faithful in
`F.unbounded` (no-overflow witness). Key step: the directed unbounded
rounding on `w`'s side is squeezed between `w` and `y` (or equals `y`), hence
in-bound, hence dominated by `w`'s maximality in `F`. -/
private theorem IsFaithfulRound.unbounded_lift {F : FiniteFormat} {x : ℝ}
    {w y : Dyadic} (hw : IsFaithfulRound F x w)
    (hy : IsFaithfulRound F.unbounded x y) (hb : Format.boundOK F.b y) :
    IsFaithfulRound F.unbounded x w := by
  rcases hw with ⟨hwmem, hw_le, hw_max⟩ | ⟨hwmem, hw_ge, hw_min⟩
  · -- RD side: w = max {v ∈ F : v ≤ x}. Show it is also the unbounded max.
    left
    refine ⟨mem_unbounded_of_mem hwmem, hw_le, ?_⟩
    intro c hc hc_le
    -- The unbounded RD rounding `g` of `x`.
    obtain ⟨hgmem, hg_le, hg_max⟩ :=
      rndUnbounded_satisfies F .toNegative x (not_isUndefined_toNegative F)
    set g := rndUnbounded F .toNegative x (not_isUndefined_toNegative F)
    have hc_g : (c : ℝ) ≤ (g : ℝ) := hg_max c hc hc_le
    have hw_g : (w : ℝ) ≤ (g : ℝ) := hg_max w (mem_unbounded_of_mem hwmem) hw_le
    -- `g` is in-bound: either `g = y` (y on the RD side) or `w ≤ g ≤ x ≤ y`.
    have hg_bnd : Format.boundOK F.b g := by
      rcases hy with ⟨hymem, hy_le, hy_max⟩ | ⟨hymem, hy_ge, _⟩
      · have h1 : (g : ℝ) ≤ (y : ℝ) := hy_max g hgmem hg_le
        exact boundOK_of_between hwmem.2.2 hb hw_g h1
      · exact boundOK_of_between hwmem.2.2 hb hw_g (le_trans hg_le hy_ge)
    -- So `g ∈ F`, hence `g ≤ w` by `w`'s maximality in `F`.
    have hg_w : (g : ℝ) ≤ (w : ℝ) :=
      hw_max g (mem_of_mem_unbounded_of_boundOK hgmem hg_bnd) hg_le
    exact le_trans hc_g hg_w
  · -- RU side: symmetric, with the unbounded RU rounding.
    right
    refine ⟨mem_unbounded_of_mem hwmem, hw_ge, ?_⟩
    intro c hc hc_ge
    obtain ⟨humem, hu_ge, hu_min⟩ :=
      rndUnbounded_satisfies F .toPositive x (not_isUndefined_toPositive F)
    set u := rndUnbounded F .toPositive x (not_isUndefined_toPositive F)
    have hu_c : (u : ℝ) ≤ (c : ℝ) := hu_min c hc hc_ge
    have hu_w : (u : ℝ) ≤ (w : ℝ) := hu_min w (mem_unbounded_of_mem hwmem) hw_ge
    have hu_bnd : Format.boundOK F.b u := by
      rcases hy with ⟨hymem, hy_le, _⟩ | ⟨hymem, hy_ge, hy_min⟩
      · exact boundOK_of_between hb hwmem.2.2 (le_trans hy_le hu_ge) hu_w
      · have h1 : (y : ℝ) ≤ (u : ℝ) := hy_min u humem hu_ge
        exact boundOK_of_between hb hwmem.2.2 h1 hu_w
    have hw_u : (w : ℝ) ≤ (u : ℝ) :=
      hw_min u (mem_of_mem_unbounded_of_boundOK humem hu_bnd) hu_ge
    exact le_trans hw_u hu_c

/-! ## Restrict / lift for `.toOdd` -/

/-- **Restrict** (`.toOdd`): an in-bound unbounded RTO rounding is also the
bounded RTO rounding. -/
private theorem RoundsFinite.toOdd_restrict {F : FiniteFormat} {x : ℝ}
    {y : Dyadic} (h : RoundsFinite F.unbounded .toOdd x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F .toOdd x y := by
  obtain ⟨hmem, hfaithful, hparity⟩ := h
  exact ⟨mem_of_mem_unbounded_of_boundOK hmem hb,
    IsFaithfulRound.restrict hfaithful hb,
    fun hne => parity_witness_congr (F := F.unbounded) (G := F) rfl rfl (hparity hne)⟩

/-- **Lift** (`.toOdd`): if `w` is the bounded RTO rounding of `x` and the
unbounded RTO rounding `y` of `x` happens to be in-bound, then `w` is also
the unbounded RTO rounding. -/
private theorem RoundsFinite.toOdd_lift {F : FiniteFormat} {x : ℝ}
    {w y : Dyadic} (hw : RoundsFinite F .toOdd x w)
    (hy : RoundsFinite F.unbounded .toOdd x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F.unbounded .toOdd x w := by
  obtain ⟨hwmem, hwfaithful, hwparity⟩ := hw
  exact ⟨mem_unbounded_of_mem hwmem,
    IsFaithfulRound.unbounded_lift hwfaithful hy.2.1 hb,
    fun hne => parity_witness_congr (F := F) (G := F.unbounded) rfl rfl (hwparity hne)⟩

/-- Transport an even-parity witness (`∃ F', F'.toFormat = _ ∧ F'.IsEven y`)
between formats agreeing on `(p, exp)`. -/
private theorem parity_witness_even_congr {F G : FiniteFormat} (hp : F.p = G.p)
    (he : F.exp = G.exp) {y : Dyadic}
    (h : ∃ F' : ParityFormat, F'.toFormat = F.toFormat ∧ F'.IsEven y) :
    ∃ F'' : ParityFormat, F''.toFormat = G.toFormat ∧ F''.IsEven y := by
  obtain ⟨F', hFeq, heven⟩ := h
  have hp' : F'.p = G.p := by rw [congrArg Format.p hFeq]; exact hp
  have he' : F'.exp = G.exp := by rw [congrArg Format.exp hFeq]; exact he
  refine ⟨⟨G, by rw [← hp', ← he']; exact F'.parity⟩, rfl, ?_⟩
  rcases heven with h0 | ⟨c, e, hrep, hpar⟩
  · exact Or.inl h0
  refine Or.inr ⟨c, e, ?_, ?_⟩
  · change Dyadic.IsRepresentableAtP (G.numDigits (y : ℝ)).toNat c e y
    rwa [numDigits_congr (F := G) (G := F'.toFiniteFormat) hp'.symm he'.symm (y : ℝ)]
  · change if G.p = ((1 : ℕ+) : WithTop ℕ+) then
        Even (e - WithBot.unbotD 0 G.exp + 1) else Even c
    rw [← hp', ← he']
    exact hpar

/-! ## Faithful-rounding uniqueness per side -/

/-- Two below-maximal (RD-side) faithful witnesses agree. -/
private theorem faithful_below_unique {G : FiniteFormat} {ξ : ℝ} {a b : Dyadic}
    (ha : a ∈ G ∧ (a : ℝ) ≤ ξ ∧ ∀ v : Dyadic, v ∈ G → (v : ℝ) ≤ ξ → (v : ℝ) ≤ (a : ℝ))
    (hb : b ∈ G ∧ (b : ℝ) ≤ ξ ∧ ∀ v : Dyadic, v ∈ G → (v : ℝ) ≤ ξ → (v : ℝ) ≤ (b : ℝ)) :
    a = b :=
  (Dyadic.coe_real_inj a b).mp
    (le_antisymm (hb.2.2 a ha.1 ha.2.1) (ha.2.2 b hb.1 hb.2.1))

/-- Two above-minimal (RU-side) faithful witnesses agree. -/
private theorem faithful_above_unique {G : FiniteFormat} {ξ : ℝ} {a b : Dyadic}
    (ha : a ∈ G ∧ ξ ≤ (a : ℝ) ∧ ∀ v : Dyadic, v ∈ G → ξ ≤ (v : ℝ) → (a : ℝ) ≤ (v : ℝ))
    (hb : b ∈ G ∧ ξ ≤ (b : ℝ) ∧ ∀ v : Dyadic, v ∈ G → ξ ≤ (v : ℝ) → (b : ℝ) ≤ (v : ℝ)) :
    a = b :=
  (Dyadic.coe_real_inj a b).mp
    (le_antisymm (ha.2.2 b hb.1 hb.2.1) (hb.2.2 a ha.1 ha.2.1))

/-- Three faithful witnesses with `c ∉ {w, y}` force `y = w` (there are at
most two distinct faithful values, one per side). -/
private theorem faithful_eq_of_third {F : FiniteFormat} {x : ℝ} {w y c : Dyadic}
    (hwf : IsFaithfulRound F.unbounded x w)
    (hyf : IsFaithfulRound F.unbounded x y)
    (hcf : IsFaithfulRound F.unbounded x c)
    (hc_ne_w : c ≠ w) (hc_ne_y : c ≠ y) : y = w := by
  rcases hwf with wRD | wRU
  · rcases hcf with cRD | cRU
    · exact absurd (faithful_below_unique cRD wRD) hc_ne_w
    · rcases hyf with yRD | yRU
      · exact faithful_below_unique yRD wRD
      · exact absurd (faithful_above_unique cRU yRU) hc_ne_y
  · rcases hcf with cRD | cRU
    · rcases hyf with yRD | yRU
      · exact absurd (faithful_below_unique cRD yRD) hc_ne_y
      · exact faithful_above_unique yRU wRU
    · exact absurd (faithful_above_unique cRU wRU) hc_ne_w

/-! ## Restrict / lift for `.nearest` -/

/-- A bounded-faithful competitor `c` is dominated by the unbounded nearest
rounding `y` in distance; and a *tie* upgrades `c` to an unbounded-faithful
witness (it must coincide with the directed unbounded rounding on its own
side). -/
private theorem nearest_close_upgrade {F : FiniteFormat} {x : ℝ} {y c : Dyadic}
    (hy_close : ∀ v : Dyadic, v ∈ F.unbounded → IsFaithfulRound F.unbounded x v →
      |x - (y : ℝ)| ≤ |x - (v : ℝ)|)
    (hc : c ∈ F) (hc_faithful : IsFaithfulRound F x c) :
    |x - (y : ℝ)| ≤ |x - (c : ℝ)| ∧
      (|x - (y : ℝ)| = |x - (c : ℝ)| → IsFaithfulRound F.unbounded x c) := by
  rcases hc_faithful with ⟨hc_mem, hc_le, hc_max⟩ | ⟨hc_mem, hc_ge, hc_min⟩
  · -- RD side: squeeze against the unbounded RD rounding `g`.
    obtain ⟨hg_mem, hg_le, hg_max⟩ :=
      rndUnbounded_satisfies F .toNegative x (not_isUndefined_toNegative F)
    set g := rndUnbounded F .toNegative x (not_isUndefined_toNegative F) with hg_def
    have hg_faithful : IsFaithfulRound F.unbounded x g := Or.inl ⟨hg_mem, hg_le, hg_max⟩
    have h1 : |x - (y : ℝ)| ≤ |x - (g : ℝ)| := hy_close g hg_mem hg_faithful
    have hcg : (c : ℝ) ≤ (g : ℝ) := hg_max c (mem_unbounded_of_mem hc) hc_le
    have h2 : |x - (g : ℝ)| ≤ |x - (c : ℝ)| := by
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
    refine ⟨le_trans h1 h2, fun heq => ?_⟩
    have h3 : |x - (g : ℝ)| = |x - (c : ℝ)| := le_antisymm h2 (heq ▸ h1)
    have hgc_eq : (g : ℝ) = (c : ℝ) := by
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h3
      linarith
    rw [(Dyadic.coe_real_inj g c).mp hgc_eq] at hg_faithful
    exact hg_faithful
  · -- RU side: squeeze against the unbounded RU rounding `u`.
    obtain ⟨hu_mem, hu_ge, hu_min⟩ :=
      rndUnbounded_satisfies F .toPositive x (not_isUndefined_toPositive F)
    set u := rndUnbounded F .toPositive x (not_isUndefined_toPositive F) with hu_def
    have hu_faithful : IsFaithfulRound F.unbounded x u := Or.inr ⟨hu_mem, hu_ge, hu_min⟩
    have h1 : |x - (y : ℝ)| ≤ |x - (u : ℝ)| := hy_close u hu_mem hu_faithful
    have huc : (u : ℝ) ≤ (c : ℝ) := hu_min c (mem_unbounded_of_mem hc) hc_ge
    have h2 : |x - (u : ℝ)| ≤ |x - (c : ℝ)| := by
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
    refine ⟨le_trans h1 h2, fun heq => ?_⟩
    have h3 : |x - (u : ℝ)| = |x - (c : ℝ)| := le_antisymm h2 (heq ▸ h1)
    have huc_eq : (u : ℝ) = (c : ℝ) := by
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at h3
      linarith
    rw [(Dyadic.coe_real_inj u c).mp huc_eq] at hu_faithful
    exact hu_faithful

/-- **Restrict** (`.nearest tb`): an in-bound unbounded RN rounding is also
the bounded RN rounding. -/
private theorem RoundsFinite.nearest_restrict {F : FiniteFormat} {tb : TieBreak}
    {x : ℝ} {y : Dyadic} (h : RoundsFinite F.unbounded (.nearest tb) x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F (.nearest tb) x y := by
  cases tb with
  | toEven =>
    obtain ⟨hmem, hfaithful, hclose, htie⟩ := h
    refine ⟨mem_of_mem_unbounded_of_boundOK hmem hb,
      IsFaithfulRound.restrict hfaithful hb, ?_, ?_⟩
    · intro c hcF hc_faithful
      exact (nearest_close_upgrade hclose hcF hc_faithful).1
    · rintro ⟨c, hcF, hc_faithful, hc_ne, hc_tie⟩
      have hc_up := (nearest_close_upgrade hclose hcF hc_faithful).2 hc_tie
      exact parity_witness_even_congr (F := F.unbounded) (G := F) rfl rfl
        (htie ⟨c, mem_unbounded_of_mem hcF, hc_up, hc_ne, hc_tie⟩)
  | awayZero =>
    obtain ⟨hmem, hfaithful, hclose, htie⟩ := h
    refine ⟨mem_of_mem_unbounded_of_boundOK hmem hb,
      IsFaithfulRound.restrict hfaithful hb, ?_, ?_⟩
    · intro c hcF hc_faithful
      exact (nearest_close_upgrade hclose hcF hc_faithful).1
    · intro c hcF hc_faithful hc_ne hc_tie
      have hc_up := (nearest_close_upgrade hclose hcF hc_faithful).2 hc_tie
      exact htie c (mem_unbounded_of_mem hcF) hc_up hc_ne hc_tie

/-- **Lift** (`.nearest tb`): if `w` is the bounded RN rounding of `x` and
the unbounded RN rounding `y` of `x` happens to be in-bound, then `w` is also
the unbounded RN rounding. -/
private theorem RoundsFinite.nearest_lift {F : FiniteFormat} {tb : TieBreak}
    {x : ℝ} {w y : Dyadic} (hw : RoundsFinite F (.nearest tb) x w)
    (hy : RoundsFinite F.unbounded (.nearest tb) x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F.unbounded (.nearest tb) x w := by
  cases tb with
  | toEven =>
    obtain ⟨hwmem, hwfaithful, hwclose, hwtie⟩ := hw
    obtain ⟨hymem, hyfaithful, hyclose, hytie⟩ := hy
    have hyF : y ∈ F := mem_of_mem_unbounded_of_boundOK hymem hb
    have hwy : |x - (w : ℝ)| ≤ |x - (y : ℝ)| :=
      hwclose y hyF (IsFaithfulRound.restrict hyfaithful hb)
    have hwf_u : IsFaithfulRound F.unbounded x w :=
      IsFaithfulRound.unbounded_lift hwfaithful hyfaithful hb
    refine ⟨mem_unbounded_of_mem hwmem, hwf_u, ?_, ?_⟩
    · intro c hc hc_faithful
      exact le_trans hwy (hyclose c hc hc_faithful)
    · rintro ⟨c, hc, hc_faithful, hc_ne, hc_tie⟩
      by_cases hcb : Format.boundOK F.b c
      · exact parity_witness_even_congr (F := F) (G := F.unbounded) rfl rfl
          (hwtie ⟨c, mem_of_mem_unbounded_of_boundOK hc hcb,
            IsFaithfulRound.restrict hc_faithful hcb, hc_ne, hc_tie⟩)
      · -- `c` out of bound forces `y = w`; fire `y`'s own tie clause.
        have hc_ne_y : c ≠ y := fun h => hcb (h ▸ hb)
        have hyw : y = w := faithful_eq_of_third hwf_u hyfaithful hc_faithful hc_ne hc_ne_y
        rw [← hyw] at hc_ne hc_tie ⊢
        exact hytie ⟨c, hc, hc_faithful, hc_ne, hc_tie⟩
  | awayZero =>
    obtain ⟨hwmem, hwfaithful, hwclose, hwtie⟩ := hw
    obtain ⟨hymem, hyfaithful, hyclose, hytie⟩ := hy
    have hyF : y ∈ F := mem_of_mem_unbounded_of_boundOK hymem hb
    have hwy : |x - (w : ℝ)| ≤ |x - (y : ℝ)| :=
      hwclose y hyF (IsFaithfulRound.restrict hyfaithful hb)
    have hwf_u : IsFaithfulRound F.unbounded x w :=
      IsFaithfulRound.unbounded_lift hwfaithful hyfaithful hb
    refine ⟨mem_unbounded_of_mem hwmem, hwf_u, ?_, ?_⟩
    · intro c hc hc_faithful
      exact le_trans hwy (hyclose c hc hc_faithful)
    · intro c hc hc_faithful hc_ne hc_tie
      by_cases hcb : Format.boundOK F.b c
      · exact hwtie c (mem_of_mem_unbounded_of_boundOK hc hcb)
          (IsFaithfulRound.restrict hc_faithful hcb) hc_ne hc_tie
      · have hc_ne_y : c ≠ y := fun h => hcb (h ▸ hb)
        have hyw : y = w := faithful_eq_of_third hwf_u hyfaithful hc_faithful hc_ne hc_ne_y
        rw [← hyw] at hc_ne hc_tie ⊢
        exact hytie c hc hc_faithful hc_ne hc_tie

/-! ## `Rounds`-level rnd-RTZ-RTZ -/

/-- **rnd-RTZ-RTZ** (Fig. 9), `Rounds` form. If `z` is the (finite) RTZ
rounding of `x` in `F₂` and `w` is the (finite) RTZ rounding of `z` in `F₁`,
then either rounding `x` directly in `F₁` overflows, or `w` is the (finite)
RTZ rounding of `x` in `F₁`. -/
private theorem roundsRTZ_RTZ_of_chain {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : Rounds F₂ .toZero x (.finite z))
    (hw : Rounds F₁ .toZero (z : ℝ) (.finite w)) :
    (∃ b, Rounds F₁ .toZero x (.overflow b)) ∨ Rounds F₁ .toZero x (.finite w) := by
  obtain ⟨h₂u, hz_fin, _⟩ := hz
  obtain ⟨h₁u, hw_fin, hw_bnd⟩ := hw
  -- The total unbounded rounding of `x` in `F₁` decides overflow.
  have hy := rndUnbounded_satisfies F₁ .toZero x h₁u
  set y := rndUnbounded F₁ .toZero x h₁u with hy_def
  by_cases hbOK : Format.boundOK F₁.b y
  · -- No overflow: compose the bounded roundings and lift back.
    right
    have hsub_u : F₁.toFormat ⊆ F₂.unbounded.toFormat := fun d hd =>
      mem_unbounded_of_mem (F := F₂) (hsub d hd)
    have hw_bdd : RoundsFinite F₁ .toZero (z : ℝ) w :=
      RoundsFinite.toZero_restrict hw_fin hw_bnd
    have hxw : RoundsFinite F₁ .toZero x w := rndRTZ_RTZ hsub_u hz_fin hw_bdd
    exact ⟨h₁u, RoundsFinite.toZero_lift hxw hy hbOK, hw_bnd⟩
  · -- Overflow: the unbounded rounding violates the bound.
    left
    exact ⟨decide ((0 : ℚ) < (y : ℚ)), h₁u, y, hy, hbOK, by simp⟩

/-! ## `Rounds`-level rnd-RAZ-RAZ -/

/-- **rnd-RAZ-RAZ** (Fig. 9), `Rounds` form. If `z` is the (finite) RAZ
rounding of `x` in `F₂` and `w` is the (finite) RAZ rounding of `z` in `F₁`,
then either rounding `x` directly in `F₁` overflows, or `w` is the (finite)
RAZ rounding of `x` in `F₁`. -/
private theorem roundsRAZ_RAZ_of_chain {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : Rounds F₂ .awayZero x (.finite z))
    (hw : Rounds F₁ .awayZero (z : ℝ) (.finite w)) :
    (∃ b, Rounds F₁ .awayZero x (.overflow b)) ∨ Rounds F₁ .awayZero x (.finite w) := by
  obtain ⟨h₂u, hz_fin, _⟩ := hz
  obtain ⟨h₁u, hw_fin, hw_bnd⟩ := hw
  -- The total unbounded rounding of `x` in `F₁` decides overflow.
  have hy := rndUnbounded_satisfies F₁ .awayZero x h₁u
  set y := rndUnbounded F₁ .awayZero x h₁u with hy_def
  by_cases hbOK : Format.boundOK F₁.b y
  · -- No overflow: compose the bounded roundings and lift back.
    right
    have hsub_u : F₁.toFormat ⊆ F₂.unbounded.toFormat := fun d hd =>
      mem_unbounded_of_mem (F := F₂) (hsub d hd)
    have hw_bdd : RoundsFinite F₁ .awayZero (z : ℝ) w :=
      RoundsFinite.awayZero_restrict hw_fin hw_bnd
    have hxw : RoundsFinite F₁ .awayZero x w := rndRAZ_RAZ hsub_u hz_fin hw_bdd
    exact ⟨h₁u, RoundsFinite.awayZero_lift hxw hy hbOK, hw_bnd⟩
  · -- Overflow: the unbounded rounding violates the bound.
    left
    exact ⟨decide ((0 : ℚ) < (y : ℚ)), h₁u, y, hy, hbOK, by simp⟩

/-! ## `Rounds`-level rnd-RTO-RTO -/

/-- **rnd-RTO-RTO** (Fig. 9), `Rounds` form. If `z` is the (finite) RTO
rounding of `x` in `F₂` and `w` is the (finite) RTO rounding of `z` in `F₁`,
then either rounding `x` directly in `F₁` overflows, or `w` is the (finite)
RTO rounding of `x` in `F₁`. Restricted to `F₂.p ≥ 2`. -/
private theorem roundsRTO_RTO_of_chain {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ+) : WithTop ℕ+) ≤ F₂.p)
    {x : ℝ} {z w : Dyadic}
    (hz : Rounds F₂ .toOdd x (.finite z))
    (hw : Rounds F₁ .toOdd (z : ℝ) (.finite w)) :
    (∃ b, Rounds F₁ .toOdd x (.overflow b)) ∨ Rounds F₁ .toOdd x (.finite w) := by
  obtain ⟨h₂u, hz_fin, _⟩ := hz
  obtain ⟨h₁u, hw_fin, hw_bnd⟩ := hw
  -- The total unbounded rounding of `x` in `F₁` decides overflow.
  have hy := rndUnbounded_satisfies F₁ .toOdd x h₁u
  set y := rndUnbounded F₁ .toOdd x h₁u with hy_def
  by_cases hbOK : Format.boundOK F₁.b y
  · -- No overflow: compose the bounded roundings and lift back.
    right
    have hsub_u : F₁.toFormat ⊆ F₂.unbounded.toFormat := fun d hd =>
      mem_unbounded_of_mem (F := F₂) (hsub d hd)
    have hw_bdd : RoundsFinite F₁ .toOdd (z : ℝ) w :=
      RoundsFinite.toOdd_restrict hw_fin hw_bnd
    have hxw : RoundsFinite F₁ .toOdd x w :=
      rndRTO_RTO hsub_u hp_F₂ hz_fin hw_bdd
    exact ⟨h₁u, RoundsFinite.toOdd_lift hxw hy hbOK, hw_bnd⟩
  · -- Overflow: the unbounded rounding violates the bound.
    left
    exact ⟨decide ((0 : ℚ) < (y : ℚ)), h₁u, y, hy, hbOK, by simp⟩

/-! ## `Rounds`-level rnd-RTO-RTZ -/

/-- **rnd-RTO-RTZ** (Fig. 9), `Rounds` form. If `z` is the (finite) RTO
rounding of `x` in `F₂` and `w` is the (finite) RTZ rounding of `z` in `F₁`,
then either rounding `x` directly in `F₁` overflows, or `w` is the (finite)
RTZ rounding of `x` in `F₁`. Uses the paper's bound-aware containment
`(F₁.extend 1).withBound F₁.boundAfterNext ⊆ F₂`. -/
private theorem roundsRTO_RTZ_of_chain {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : Rounds F₂ .toOdd x (.finite z))
    (hw : Rounds F₁ .toZero (z : ℝ) (.finite w)) :
    (∃ b, Rounds F₁ .toZero x (.overflow b)) ∨ Rounds F₁ .toZero x (.finite w) := by
  obtain ⟨h₂u, hz_fin, _⟩ := hz
  obtain ⟨h₁u, hw_fin, hw_bnd⟩ := hw
  -- The total unbounded rounding of `x` in `F₁` decides overflow.
  have hy := rndUnbounded_satisfies F₁ .toZero x h₁u
  set y := rndUnbounded F₁ .toZero x h₁u with hy_def
  by_cases hbOK : Format.boundOK F₁.b y
  · -- No overflow: compose the bounded roundings and lift back.
    right
    have hsub_u : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext)
        ⊆ F₂.unbounded.toFormat := fun d hd =>
      mem_unbounded_of_mem (F := F₂) (hsub d hd)
    have hw_bdd : RoundsFinite F₁ .toZero (z : ℝ) w :=
      RoundsFinite.toZero_restrict hw_fin hw_bnd
    have hxw : RoundsFinite F₁ .toZero x w := rndRTO_RTZ hsub_u hz_fin hw_bdd
    exact ⟨h₁u, RoundsFinite.toZero_lift hxw hy hbOK, hw_bnd⟩
  · -- Overflow: the unbounded rounding violates the bound.
    left
    exact ⟨decide ((0 : ℚ) < (y : ℚ)), h₁u, y, hy, hbOK, by simp⟩

/-! ## `Rounds`-level rnd-RTO-RAZ -/

/-- **rnd-RTO-RAZ** (Fig. 9), `Rounds` form. If `z` is the (finite) RTO
rounding of `x` in `F₂` and `w` is the (finite) RAZ rounding of `z` in `F₁`,
then either rounding `x` directly in `F₁` overflows, or `w` is the (finite)
RAZ rounding of `x` in `F₁`. Uses the paper's bound-aware containment
`(F₁.extend 1).withBound F₁.boundAfterNext ⊆ F₂`. -/
private theorem roundsRTO_RAZ_of_chain {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : Rounds F₂ .toOdd x (.finite z))
    (hw : Rounds F₁ .awayZero (z : ℝ) (.finite w)) :
    (∃ b, Rounds F₁ .awayZero x (.overflow b)) ∨ Rounds F₁ .awayZero x (.finite w) := by
  obtain ⟨h₂u, hz_fin, _⟩ := hz
  obtain ⟨h₁u, hw_fin, hw_bnd⟩ := hw
  -- The total unbounded rounding of `x` in `F₁` decides overflow.
  have hy := rndUnbounded_satisfies F₁ .awayZero x h₁u
  set y := rndUnbounded F₁ .awayZero x h₁u with hy_def
  by_cases hbOK : Format.boundOK F₁.b y
  · -- No overflow: compose the bounded roundings and lift back.
    right
    have hsub_u : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext)
        ⊆ F₂.unbounded.toFormat := fun d hd =>
      mem_unbounded_of_mem (F := F₂) (hsub d hd)
    have hw_bdd : RoundsFinite F₁ .awayZero (z : ℝ) w :=
      RoundsFinite.awayZero_restrict hw_fin hw_bnd
    have hxw : RoundsFinite F₁ .awayZero x w := rndRTO_RAZ hsub_u hz_fin hw_bdd
    exact ⟨h₁u, RoundsFinite.awayZero_lift hxw hy hbOK, hw_bnd⟩
  · -- Overflow: the unbounded rounding violates the bound.
    left
    exact ⟨decide ((0 : ℚ) < (y : ℚ)), h₁u, y, hy, hbOK, by simp⟩

/-! ## `Rounds`-level rnd-RTO-RN -/

/-- **rnd-RTO-RN** (Fig. 9), `Rounds` form, parameterized by the tie-break
`tb` (covers RNE and RNA). If `z` is the (finite) RTO rounding of `x` in `F₂`
and `w` is the (finite) RN rounding of `z` in `F₁`, then either rounding `x`
directly in `F₁` overflows, or `w` is the (finite) RN rounding of `x` in
`F₁`. Uses the paper's bound-aware containment
`(F₁.extend 2).withBound (F₁.extend 1).boundAfterNext ⊆ F₂`. -/
private theorem roundsRTO_RN_of_chain {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
              ⊆ F₂.toFormat)
    {tb : TieBreak} {x : ℝ} {z w : Dyadic}
    (hz : Rounds F₂ .toOdd x (.finite z))
    (hw : Rounds F₁ (.nearest tb) (z : ℝ) (.finite w)) :
    (∃ b, Rounds F₁ (.nearest tb) x (.overflow b)) ∨
      Rounds F₁ (.nearest tb) x (.finite w) := by
  obtain ⟨h₂u, hz_fin, _⟩ := hz
  obtain ⟨h₁u, hw_fin, hw_bnd⟩ := hw
  -- The total unbounded rounding of `x` in `F₁` decides overflow.
  have hy := rndUnbounded_satisfies F₁ (.nearest tb) x h₁u
  set y := rndUnbounded F₁ (.nearest tb) x h₁u with hy_def
  by_cases hbOK : Format.boundOK F₁.b y
  · -- No overflow: compose the bounded roundings and lift back.
    right
    have hsub_u : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
        ⊆ F₂.unbounded.toFormat := fun d hd =>
      mem_unbounded_of_mem (F := F₂) (hsub d hd)
    have hw_bdd : RoundsFinite F₁ (.nearest tb) (z : ℝ) w :=
      RoundsFinite.nearest_restrict hw_fin hw_bnd
    have hxw : RoundsFinite F₁ (.nearest tb) x w := rndRTO_RN hsub_u hz_fin hw_bdd
    exact ⟨h₁u, RoundsFinite.nearest_lift hxw hy hbOK, hw_bnd⟩
  · -- Overflow: the unbounded rounding violates the bound.
    left
    exact ⟨decide ((0 : ℚ) < (y : ℚ)), h₁u, y, hy, hbOK, by simp⟩

/-! # Total double rounding (overflow-aware, self-contained)

The final layer: no chain hypotheses at all. For each Fig. 9 rule, conclude
that either (i) rounding `x` directly in `F₁` overflows, or (ii) rounding
`x` in `F₂` does **not** overflow (finite `z`), the chained rounding is
finite (`w`), and double rounding holds. The paper's side condition ("the
rules hold whenever `rnd_{F₁}(x)` does not overflow") is the guard between
the two disjuncts; the paper's bound conditions (`next(b₁)` vs `b₁`) become
*proof obligations* for no-overflow propagation, which is also where the
`GridBound` regularity condition (implicit in the paper) enters. -/

/-- The format's magnitude bound is *regular*: whenever it is finite, the
bound itself lies on the format's grid and the format has a finite `exp`.
Implicit in the paper (where `b` is the largest finite value); needed for
no-overflow propagation — with an off-grid or `exp = ⊥` bound, `next(b₁)`
fails to dominate the format's overflow threshold and double rounding can
overflow in `F₂` without overflowing in `F₁`. -/
def FiniteFormat.GridBound (F : FiniteFormat) : Prop :=
  ∀ b : NonNegDyadic, F.b = (b : WithTop NonNegDyadic) → b.val ∈ F ∧ F.exp ≠ ⊥

/-! ## Helpers -/

private theorem not_isUndefined_toZero (F : FiniteFormat) :
    ¬ F.IsUndefined .toZero := by
  rintro ⟨-, -, h | h⟩ <;> simp at h

private theorem not_isUndefined_awayZero (F : FiniteFormat) :
    ¬ F.IsUndefined .awayZero := by
  rintro ⟨-, -, h | h⟩ <;> simp at h

/-- If `|g| ≤ |h|` (over ℝ) and `h` is in-bound, so is `g`. -/
private theorem boundOK_of_abs_le {b : WithTop NonNegDyadic} {g h : Dyadic}
    (hle : |(g : ℝ)| ≤ |(h : ℝ)|) (hb : Format.boundOK b h) :
    Format.boundOK b g := by
  cases b with
  | top => trivial
  | coe b =>
    have hle' : |(g : ℚ)| ≤ |(h : ℚ)| := by
      rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast,
        ← Rat.cast_abs, ← Rat.cast_abs] at hle
      exact_mod_cast hle
    have hb' : |(h : ℚ)| ≤ ((b.val : Dyadic) : ℚ) := hb
    change |(g : ℚ)| ≤ ((b.val : Dyadic) : ℚ)
    linarith

/-- Sign-transitivity through a nonzero pivot: if `y·x ≥ 0` and `z·x ≥ 0`,
and `x = 0` implies `y = 0`, then `y·z ≥ 0`. -/
private theorem mul_nonneg_of_common_sign {x : ℝ} {y z : ℝ}
    (hyx : y * x ≥ 0) (hzx : z * x ≥ 0) (hy0 : x = 0 → y = 0) :
    y * z ≥ 0 := by
  rcases eq_or_ne x 0 with hx | hx
  · rw [hy0 hx, zero_mul]
  · have hx2 : 0 < x ^ 2 := by positivity
    nlinarith [mul_nonneg hyx hzx]

/-- `2^k` (any `k`) has precision 1, hence fits any precision bound. -/
private theorem precisionAtMost_one_zpow {p : WithTop ℕ+} (k : ℤ) :
    Dyadic.precisionAtMost p (Dyadic.ofIntZpow 1 k) := by
  cases p with
  | top => trivial
  | coe p =>
    rw [Dyadic.precisionAtMost_coe]
    refine ⟨1, k, by rw [Dyadic.coe_rat_ofIntZpow], ?_⟩
    have hp1 : 1 ≤ (p : ℕ) := p.pos
    have h2 : (2 : ℤ) ^ 1 ≤ (2 : ℤ) ^ (p : ℕ) := pow_le_pow_right₀ (by norm_num) hp1
    simp only [abs_one]
    omega

/-- An odd-significand representation cannot sit below the quantum: if
`x = c·2^q` with `c` odd and `x` has quantum at least `e`, then `e ≤ q`. -/
private theorem quantum_le_of_odd_rep {e : ℤ} {x : Dyadic}
    (hq : Dyadic.quantumAtLeast ((e : ℤ) : WithBot ℤ) x) {c q : ℤ}
    (hodd : Odd c) (heq : ((x : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ) ^ q) :
    e ≤ q := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, ((x : Dyadic) : ℝ) = (m : ℝ) * (2 : ℝ) ^ e := by
    rw [← Dyadic.quantumAtLeast_coe_real]; exact hq
  by_contra hlt; push Not at hlt
  have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ q := zpow_pos (by norm_num) _
  have h1 : (c : ℝ) * (2 : ℝ) ^ q = (m : ℝ) * (2 : ℝ) ^ e := by rw [← heq, hm]
  have h2 : (m : ℝ) * (2 : ℝ) ^ (e - q) * (2 : ℝ) ^ q = (m : ℝ) * (2 : ℝ) ^ e := by
    rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), sub_add_cancel]
  have hce : (c : ℝ) = (m : ℝ) * (2 : ℝ) ^ (e - q) :=
    mul_right_cancel₀ (ne_of_gt h2q_pos) (h1.trans h2.symm)
  have hcast : ((m * 2 ^ (e - q).toNat : ℤ) : ℝ) = (m : ℝ) * (2 : ℝ) ^ (e - q) := by
    push_cast
    rw [← zpow_natCast (2 : ℝ) ((e - q).toNat), Int.toNat_of_nonneg (by omega)]
  have hc_int : c = m * 2 ^ (e - q).toNat := by
    exact_mod_cast hce.trans hcast.symm
  have h2dvd : (2 : ℤ) ∣ c := by
    rw [hc_int]
    exact dvd_mul_of_dvd_right (dvd_pow_self 2 (by omega)) m
  rcases hodd with ⟨t, ht⟩
  omega

/-- **Grid closure of `next`**: if `b ≥ 0` lies on the `(p, exp)` grid and
`exp` is finite, then `F.next b` lies on the grid as well. (The `exp = ⊥`
corner is genuinely false: there `next b = b + 1` under-approximates the grid
successor for large `b`.) -/
private theorem next_mem_unbounded {F : FiniteFormat} {e : ℤ}
    (he : F.exp = (e : WithBot ℤ)) {b : Dyadic}
    (hb_mem : b ∈ F.unbounded) :
    F.toFormat.next b ∈ F.unbounded := by
  obtain ⟨hb_p, hb_q, -⟩ := hb_mem
  have hb_q' : ∃ m : ℤ, ((b : Dyadic) : ℝ) = (m : ℝ) * (2 : ℝ) ^ e := by
    rw [← Dyadic.quantumAtLeast_coe_real, ← he]; exact hb_q
  obtain ⟨m, hm⟩ := hb_q'
  cases hF_p : F.p with
  | top =>
    -- `F.p = ⊤`: `next b = b + 2^e`, quantum is preserved by adding one step.
    have h_next : F.toFormat.next b = b + Dyadic.ofIntZpow 1 e :=
      Format.next_eq_p_top F.toFormat he hF_p b
    refine ⟨?_, ?_, trivial⟩
    · change Dyadic.precisionAtMost F.p _
      rw [hF_p]; trivial
    · change Dyadic.quantumAtLeast F.exp _
      rw [he, Dyadic.quantumAtLeast_coe_real]
      refine ⟨m + 1, ?_⟩
      have hstep : ((Dyadic.ofIntZpow 1 e : Dyadic) : ℝ) = (2 : ℝ) ^ e := by
        rw [Dyadic.coe_ofIntZpow]; push_cast; ring
      rw [h_next, Dyadic.coe_real_add, hstep, hm]
      push_cast; ring
  | coe p =>
    by_cases hb0 : ((b : Dyadic) : ℝ) ≤ 0
    · -- `b = 0`: `next b = 2^e`.
      have h_next : F.toFormat.next b = Dyadic.ofIntZpow 1 e := by
        have h_eq : F.toFormat.next b =
            if ((b : Dyadic) : ℝ) ≤ 0 then Dyadic.ofIntZpow 1 e
            else b + Dyadic.ofIntZpow 1
              (max e (Int.log 2 ((b : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1)) := by
          unfold Format.next; rw [he, hF_p]
        rw [h_eq, if_pos hb0]
      refine ⟨?_, ?_, trivial⟩
      · change Dyadic.precisionAtMost F.p _
        rw [hF_p, h_next]
        exact precisionAtMost_one_zpow e
      · change Dyadic.quantumAtLeast F.exp _
        rw [he, Dyadic.quantumAtLeast_coe_real]
        exact ⟨1, by rw [h_next, Dyadic.coe_ofIntZpow]⟩
    · -- `b > 0`: the main case.
      push Not at hb0
      have hb_ne : ((b : Dyadic) : ℝ) ≠ 0 := ne_of_gt hb0
      have hb_p' : Dyadic.precisionAtMost ((p : ℕ+) : WithTop ℕ+) b := by
        rw [← hF_p]; exact hb_p
      obtain ⟨c, q, hc_eq, hc_odd, hc_lt⟩ :=
        Dyadic.exists_odd_canonical_of_precisionAtMost hb_p' hb_ne
      have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ q := zpow_pos (by norm_num) _
      have hc_pos : 0 < c := by
        by_contra hc_np; push Not at hc_np
        have hcr : (c : ℝ) ≤ 0 := by exact_mod_cast hc_np
        nlinarith
      have hc1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc_pos
      -- `e ≤ q`: an odd significand cannot absorb a coarser quantum.
      have hqe : e ≤ q := quantum_le_of_odd_rep (he ▸ hb_q) hc_odd hc_eq
      -- log bounds: `q ≤ logB < q + p`.
      have h_lb : (2 : ℝ) ^ q ≤ ((b : Dyadic) : ℝ) := by rw [hc_eq]; nlinarith
      have hcp : (c : ℝ) < (2 : ℝ) ^ ((p : ℕ) : ℤ) := by
        rw [zpow_natCast]
        have h1 : (c : ℝ) < ((2 ^ (p : ℕ) : ℤ) : ℝ) := by
          exact_mod_cast lt_of_abs_lt hc_lt
        push_cast at h1; exact h1
      have h_ub : ((b : Dyadic) : ℝ) < (2 : ℝ) ^ (q + ((p : ℕ) : ℤ)) := by
        rw [hc_eq, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        calc (c : ℝ) * (2 : ℝ) ^ q < (2 : ℝ) ^ ((p : ℕ) : ℤ) * (2 : ℝ) ^ q := by nlinarith
          _ = (2 : ℝ) ^ q * (2 : ℝ) ^ ((p : ℕ) : ℤ) := by ring
      -- The computed form of `next` (introduced before folding `logB`, `s`).
      have h_next := Format.next_eq_finite_pos F.toFormat he hF_p hb0
      set logB := Int.log 2 ((b : Dyadic) : ℝ) with hlogB_def
      have hq_le_log : q ≤ logB :=
        (Int.zpow_le_iff_le_log (by norm_num) hb0).mp h_lb
      have hlog_lt : logB < q + ((p : ℕ) : ℤ) :=
        (Int.lt_zpow_iff_log_lt (by norm_num) hb0).mp h_ub
      -- step exponent `s`, with `e ≤ s ≤ q`.
      set s := max e (logB - ((p : ℕ) : ℤ) + 1) with hs_def
      have hs_le_q : s ≤ q := max_le hqe (by omega)
      have he_le_s : e ≤ s := le_max_left _ _
      have h2s_pos : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
      have h2q_split : (2 : ℝ) ^ q = (2 : ℝ) ^ ((q - s).toNat) * (2 : ℝ) ^ s :=
        two_zpow_split_toNat hs_le_q
      have h_val : ((F.toFormat.next b : Dyadic) : ℝ)
          = ((c * 2 ^ ((q - s).toNat) + 1 : ℤ) : ℝ) * (2 : ℝ) ^ s := by
        have hstep : ((Dyadic.ofIntZpow 1 s : Dyadic) : ℝ) = (2 : ℝ) ^ s := by
          rw [Dyadic.coe_ofIntZpow]; push_cast; ring
        rw [h_next, Dyadic.coe_real_add, hstep, hc_eq, h2q_split]
        push_cast; ring
      -- `c·2^(q−s) < 2^p`, hence the new significand is at most `2^p`.
      have hck_lt : c * 2 ^ ((q - s).toNat) < 2 ^ (p : ℕ) := by
        have hb_ub : ((b : Dyadic) : ℝ) < (2 : ℝ) ^ (logB + 1) :=
          Int.lt_zpow_succ_log_self (by norm_num) _
        have h3 : (c : ℝ) * (2 : ℝ) ^ ((q - s).toNat) * (2 : ℝ) ^ s
            < (2 : ℝ) ^ ((p : ℕ) : ℤ) * (2 : ℝ) ^ s := by
          have h4 : (c : ℝ) * (2 : ℝ) ^ ((q - s).toNat) * (2 : ℝ) ^ s
              = (c : ℝ) * (2 : ℝ) ^ q := by rw [h2q_split]; ring
          have h5 : (2 : ℝ) ^ (((p : ℕ) : ℤ) + s)
              = (2 : ℝ) ^ ((p : ℕ) : ℤ) * (2 : ℝ) ^ s := by
            rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          rw [h4, ← h5]
          calc (c : ℝ) * (2 : ℝ) ^ q = ((b : Dyadic) : ℝ) := hc_eq.symm
            _ < (2 : ℝ) ^ (logB + 1) := hb_ub
            _ ≤ (2 : ℝ) ^ (((p : ℕ) : ℤ) + s) :=
                zpow_le_zpow_right₀ (by norm_num) (by omega)
        have h6 : (c : ℝ) * (2 : ℝ) ^ ((q - s).toNat) < (2 : ℝ) ^ ((p : ℕ) : ℤ) :=
          lt_of_mul_lt_mul_right (by linarith [h3]) h2s_pos.le
        have h7 : (c : ℝ) * (2 : ℝ) ^ ((q - s).toNat) < (2 : ℝ) ^ (p : ℕ) := by
          rw [← zpow_natCast (2 : ℝ) (p : ℕ)]; exact h6
        exact_mod_cast h7
      have hc₁_pos : 0 < c * 2 ^ ((q - s).toNat) + 1 := by
        have h2k : (0 : ℤ) < 2 ^ ((q - s).toNat) := pow_pos (by norm_num) _
        have := mul_pos hc_pos h2k
        omega
      rcases lt_or_eq_of_le (Int.add_one_le_iff.mpr hck_lt) with hc₁_lt | hc₁_eq
      · -- Normal case: representation `(c·2^(q−s) + 1, s)`.
        refine ⟨?_, ?_, trivial⟩
        · change Dyadic.precisionAtMost F.p _
          rw [hF_p, Dyadic.precisionAtMost_coe_real]
          exact ⟨c * 2 ^ ((q - s).toNat) + 1, s, h_val, by rwa [abs_of_pos hc₁_pos]⟩
        · change Dyadic.quantumAtLeast F.exp _
          rw [he, Dyadic.quantumAtLeast_coe_real]
          refine ⟨(c * 2 ^ ((q - s).toNat) + 1) * 2 ^ ((s - e).toNat), ?_⟩
          rw [h_val, two_zpow_split_toNat he_le_s]
          push_cast; ring
      · -- Carry case: `next b = 2^(p + s)`, representation `(1, p + s)`.
        have h_val' : ((F.toFormat.next b : Dyadic) : ℝ)
            = (2 : ℝ) ^ (((p : ℕ) : ℤ) + s) := by
          rw [h_val, hc₁_eq, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
          push_cast; ring
        refine ⟨?_, ?_, trivial⟩
        · change Dyadic.precisionAtMost F.p _
          rw [hF_p, Dyadic.precisionAtMost_coe_real]
          refine ⟨1, ((p : ℕ) : ℤ) + s, by rw [h_val']; push_cast; ring, ?_⟩
          have hp1 : 1 ≤ (p : ℕ) := p.pos
          have h2 : (2 : ℤ) ^ 1 ≤ (2 : ℤ) ^ (p : ℕ) := pow_le_pow_right₀ (by norm_num) hp1
          simp only [abs_one]
          omega
        · change Dyadic.quantumAtLeast F.exp _
          rw [he, Dyadic.quantumAtLeast_coe_real]
          refine ⟨2 ^ ((((p : ℕ) : ℤ) + s - e).toNat), ?_⟩
          rw [h_val', two_zpow_split_toNat (show e ≤ ((p : ℕ) : ℤ) + s by omega)]
          push_cast; ring

/-- **Grid minimality of `next`**: for `b ≥ 0` on the grid and finite `exp`,
any grid point strictly above `b` is at least `F.next b` — i.e. the grid has
no point in `(b, next b)`. -/
private theorem next_min {F : FiniteFormat} {e : ℤ}
    (he : F.exp = (e : WithBot ℤ)) {b g : Dyadic}
    (hb_mem : b ∈ F.unbounded) (hg_mem : g ∈ F.unbounded)
    (hb_nn : 0 ≤ ((b : Dyadic) : ℝ))
    (hbg : ((b : Dyadic) : ℝ) < ((g : Dyadic) : ℝ)) :
    ((F.toFormat.next b : Dyadic) : ℝ) ≤ ((g : Dyadic) : ℝ) := by
  obtain ⟨hb_p, hb_q, -⟩ := hb_mem
  obtain ⟨hg_p, hg_q, -⟩ := hg_mem
  have h2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  cases hF_p : F.p with
  | top =>
    -- Both are multiples of `2^e`; a strict increase is at least one step.
    have h_next : F.toFormat.next b = b + Dyadic.ofIntZpow 1 e :=
      Format.next_eq_p_top F.toFormat he hF_p b
    obtain ⟨mb, hmb⟩ : ∃ m : ℤ, ((b : Dyadic) : ℝ) = (m : ℝ) * (2 : ℝ) ^ e := by
      rw [← Dyadic.quantumAtLeast_coe_real, ← he]; exact hb_q
    obtain ⟨mg, hmg⟩ : ∃ m : ℤ, ((g : Dyadic) : ℝ) = (m : ℝ) * (2 : ℝ) ^ e := by
      rw [← Dyadic.quantumAtLeast_coe_real, ← he]; exact hg_q
    have hm_lt : mb < mg := by
      have h1 : (mb : ℝ) < (mg : ℝ) := by
        rw [hmb, hmg] at hbg
        exact lt_of_mul_lt_mul_right hbg h2e_pos.le
      exact_mod_cast h1
    have hstep : ((Dyadic.ofIntZpow 1 e : Dyadic) : ℝ) = (2 : ℝ) ^ e := by
      rw [Dyadic.coe_ofIntZpow]; push_cast; ring
    rw [h_next, Dyadic.coe_real_add, hstep, hmb, hmg]
    have h1 : (mb : ℝ) + 1 ≤ (mg : ℝ) := by exact_mod_cast hm_lt
    nlinarith
  | coe p =>
    have hg_pos : 0 < ((g : Dyadic) : ℝ) := lt_of_le_of_lt hb_nn hbg
    have hg_ne : ((g : Dyadic) : ℝ) ≠ 0 := ne_of_gt hg_pos
    have hg_p' : Dyadic.precisionAtMost ((p : ℕ+) : WithTop ℕ+) g := by
      rw [← hF_p]; exact hg_p
    obtain ⟨cg, qg, hg_eq, hg_odd, hg_lt⟩ :=
      Dyadic.exists_odd_canonical_of_precisionAtMost hg_p' hg_ne
    have h2qg_pos : (0 : ℝ) < (2 : ℝ) ^ qg := zpow_pos (by norm_num) _
    have hcg_pos : 0 < cg := by
      by_contra h; push Not at h
      have : (cg : ℝ) ≤ 0 := by exact_mod_cast h
      nlinarith
    have hcg1 : (1 : ℝ) ≤ (cg : ℝ) := by exact_mod_cast hcg_pos
    have he_qg : e ≤ qg := quantum_le_of_odd_rep (he ▸ hg_q) hg_odd hg_eq
    by_cases hb0 : ((b : Dyadic) : ℝ) ≤ 0
    · -- `b = 0`: `next b = 2^e ≤ 2^qg ≤ g`.
      have h_next : F.toFormat.next b = Dyadic.ofIntZpow 1 e := by
        have h_eq : F.toFormat.next b =
            if ((b : Dyadic) : ℝ) ≤ 0 then Dyadic.ofIntZpow 1 e
            else b + Dyadic.ofIntZpow 1
              (max e (Int.log 2 ((b : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1)) := by
          unfold Format.next; rw [he, hF_p]
        rw [h_eq, if_pos hb0]
      rw [h_next, Dyadic.coe_ofIntZpow, hg_eq]
      have h1 : (2 : ℝ) ^ e ≤ (2 : ℝ) ^ qg :=
        zpow_le_zpow_right₀ (by norm_num) he_qg
      push_cast
      nlinarith
    · -- `b > 0`: both are multiples of the step `2^s`.
      push Not at hb0
      have hb_ne : ((b : Dyadic) : ℝ) ≠ 0 := ne_of_gt hb0
      have hb_p' : Dyadic.precisionAtMost ((p : ℕ+) : WithTop ℕ+) b := by
        rw [← hF_p]; exact hb_p
      obtain ⟨cb, qb, hb_eq, hb_odd, hb_lt⟩ :=
        Dyadic.exists_odd_canonical_of_precisionAtMost hb_p' hb_ne
      have h2qb_pos : (0 : ℝ) < (2 : ℝ) ^ qb := zpow_pos (by norm_num) _
      have hcb_pos : 0 < cb := by
        by_contra h; push Not at h
        have : (cb : ℝ) ≤ 0 := by exact_mod_cast h
        nlinarith
      have hcb1 : (1 : ℝ) ≤ (cb : ℝ) := by exact_mod_cast hcb_pos
      have he_qb : e ≤ qb := quantum_le_of_odd_rep (he ▸ hb_q) hb_odd hb_eq
      -- significand bounds, over ℝ
      have hcbp : (cb : ℝ) < (2 : ℝ) ^ ((p : ℕ) : ℤ) := by
        rw [zpow_natCast]
        have h1 : (cb : ℝ) < ((2 ^ (p : ℕ) : ℤ) : ℝ) := by
          exact_mod_cast lt_of_abs_lt hb_lt
        push_cast at h1; exact h1
      have hcgp : (cg : ℝ) < (2 : ℝ) ^ ((p : ℕ) : ℤ) := by
        rw [zpow_natCast]
        have h1 : (cg : ℝ) < ((2 ^ (p : ℕ) : ℤ) : ℝ) := by
          exact_mod_cast lt_of_abs_lt hg_lt
        push_cast at h1; exact h1
      -- log bounds for b
      have h_lb : (2 : ℝ) ^ qb ≤ ((b : Dyadic) : ℝ) := by rw [hb_eq]; nlinarith
      have h_ub : ((b : Dyadic) : ℝ) < (2 : ℝ) ^ (qb + ((p : ℕ) : ℤ)) := by
        rw [hb_eq, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        nlinarith
      have h_next := Format.next_eq_finite_pos F.toFormat he hF_p hb0
      set logB := Int.log 2 ((b : Dyadic) : ℝ) with hlogB_def
      have hqb_le_log : qb ≤ logB :=
        (Int.zpow_le_iff_le_log (by norm_num) hb0).mp h_lb
      have hlog_lt : logB < qb + ((p : ℕ) : ℤ) :=
        (Int.lt_zpow_iff_log_lt (by norm_num) hb0).mp h_ub
      set s := max e (logB - ((p : ℕ) : ℤ) + 1) with hs_def
      have hs_le_qb : s ≤ qb := max_le he_qb (by omega)
      -- `s ≤ qg`: from `2^logB ≤ b < g = cg·2^qg < 2^(qg+p)`.
      have hg_gt : (2 : ℝ) ^ logB < (2 : ℝ) ^ (qg + ((p : ℕ) : ℤ)) := by
        have h1 : (2 : ℝ) ^ logB ≤ ((b : Dyadic) : ℝ) :=
          Int.zpow_log_le_self (by norm_num) hb0
        have h2 : ((g : Dyadic) : ℝ) < (2 : ℝ) ^ (qg + ((p : ℕ) : ℤ)) := by
          rw [hg_eq, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          nlinarith
        linarith
      have hlog_qg : logB < qg + ((p : ℕ) : ℤ) := by
        by_contra h; push Not at h
        have := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h
        linarith
      have hs_le_qg : s ≤ qg := max_le he_qg (by omega)
      have h2s_pos : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
      -- both as multiples of `2^s`
      have hkb : ((b : Dyadic) : ℝ) = ((cb * 2 ^ ((qb - s).toNat) : ℤ) : ℝ) * (2 : ℝ) ^ s := by
        rw [hb_eq, two_zpow_split_toNat hs_le_qb]
        push_cast; ring
      have hkg : ((g : Dyadic) : ℝ) = ((cg * 2 ^ ((qg - s).toNat) : ℤ) : ℝ) * (2 : ℝ) ^ s := by
        rw [hg_eq, two_zpow_split_toNat hs_le_qg]
        push_cast; ring
      have hk_lt : cb * 2 ^ ((qb - s).toNat) < cg * 2 ^ ((qg - s).toNat) := by
        have h1 : ((cb * 2 ^ ((qb - s).toNat) : ℤ) : ℝ)
            < ((cg * 2 ^ ((qg - s).toNat) : ℤ) : ℝ) := by
          rw [hkb, hkg] at hbg
          exact lt_of_mul_lt_mul_right hbg h2s_pos.le
        exact_mod_cast h1
      have hstep : ((Dyadic.ofIntZpow 1 s : Dyadic) : ℝ) = (2 : ℝ) ^ s := by
        rw [Dyadic.coe_ofIntZpow]; push_cast; ring
      rw [h_next, Dyadic.coe_real_add, hstep, hkb, hkg]
      have h1 : ((cb * 2 ^ ((qb - s).toNat) : ℤ) : ℝ) + 1
          ≤ ((cg * 2 ^ ((qg - s).toNat) : ℤ) : ℝ) := by
        exact_mod_cast Int.add_one_le_iff.mpr hk_lt
      nlinarith

/-- `b < F.next b` for finite `exp` (any `p`), `b ≥ 0`. -/
private theorem lt_next' {F : Format} {e : ℤ} (he : F.exp = (e : WithBot ℤ))
    (b : Dyadic) (hb : 0 ≤ ((b : Dyadic) : ℝ)) :
    ((b : Dyadic) : ℝ) < ((F.next b : Dyadic) : ℝ) := by
  rcases hp : F.p with _ | p
  · exact Format.lt_next_of_p_top F he hp b
  · exact Format.lt_next_of_finite F he hp b hb

/-- If the *unbounded* `F₁` grid (bound `⊤`, here via
`withBound boundAfterNext` with `F₁.b = ⊤`) is contained in `F₂`, then `F₂`
cannot have a finite bound: the grid contains arbitrarily large powers of
two. -/
private theorem bound_top_of_withBound_top_subset {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound ⊤) ⊆ F₂.toFormat) : F₂.b = ⊤ := by
  by_contra h
  obtain ⟨b₂, hb₂⟩ : ∃ b₂ : NonNegDyadic, F₂.b = (b₂ : WithTop NonNegDyadic) := by
    cases hc : F₂.b with
    | top => exact absurd hc h
    | coe b₂ => exact ⟨b₂, rfl⟩
  set E := WithBot.unbotD 0 F₁.exp with hE_def
  set K := max E (Int.log 2 ((b₂.val : Dyadic) : ℚ) + 1) with hK_def
  set w := Dyadic.ofIntZpow 1 K with hw_def
  have hw_mem : w ∈ (F₁.toFormat.withBound ⊤) := by
    refine ⟨?_, ?_, ?_⟩
    · change Dyadic.precisionAtMost F₁.p w
      exact precisionAtMost_one_zpow K
    · change Dyadic.quantumAtLeast F₁.exp w
      cases hexp : F₁.exp with
      | bot => trivial
      | coe e =>
        rw [Dyadic.quantumAtLeast_coe]
        have hE : E = e := by rw [hE_def, hexp]; rfl
        have hKe : e ≤ K := by rw [← hE]; exact le_max_left _ _
        refine ⟨2 ^ (K - e).toNat, ?_⟩
        rw [hw_def, Dyadic.coe_rat_ofIntZpow]
        have hk : ((K - e).toNat : ℤ) = K - e := Int.toNat_of_nonneg (by omega)
        push_cast
        rw [← zpow_natCast (2 : ℚ) ((K - e).toNat), hk,
          ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), sub_add_cancel]
        ring
    · change Format.boundOK (⊤ : WithTop NonNegDyadic) w
      trivial
  have hb_w : Format.boundOK F₂.b w := (hsub w hw_mem).2.2
  rw [hb₂] at hb_w
  have hb_w' : |(w : ℚ)| ≤ ((b₂.val : Dyadic) : ℚ) := hb_w
  have h2K_pos : (0 : ℚ) < (2 : ℚ) ^ K := zpow_pos (by norm_num) _
  have hw_val : |(w : ℚ)| = (2 : ℚ) ^ K := by
    rw [hw_def, Dyadic.coe_rat_ofIntZpow]
    push_cast
    rw [one_mul, abs_of_pos h2K_pos]
  have hlt : ((b₂.val : Dyadic) : ℚ) < (2 : ℚ) ^ K :=
    lt_of_lt_of_le (Int.lt_zpow_succ_log_self (by norm_num) _)
      (zpow_le_zpow_right₀ (by norm_num) (le_max_right _ _))
  rw [hw_val] at hb_w'
  linarith

/-- Specialization: the paper containment with `F₁.b = ⊤` forces `F₂.b = ⊤`. -/
private theorem bound_top_of_paper_subset {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hb_top : F₁.b = ⊤) : F₂.b = ⊤ := by
  rw [Format.boundAfterNext_top hb_top] at hsub
  exact bound_top_of_withBound_top_subset hsub

/-! ## rnd-RTZ-RTZ, total form

Hypotheses **must change**: the paper containment
`F₁.withBound F₁.boundAfterNext ⊆ F₂` replaces plain `F₁ ⊆ F₂`, *and* the
bound `b₁` must be representable in `F₁` (with finite `exp` when `b₁` is
finite). Otherwise no-overflow propagation fails — e.g.
`F₁ = A(1, ⊥, 5)`, `F₂ = A(3, ⊥, 4)` satisfy the paper containment
(`A(1, ⊥, 6) ⊆ A(3, ⊥, 4)`), yet at `x = 5.2` the `F₁`-RTZ rounding is `4`
(no overflow) while the `F₂`-RTZ rounding is `5 > 4` (overflow). -/

/-- `next(b₁)` satisfies the relaxed bound `boundAfterNext`. -/
private theorem boundOK_boundAfterNext_next {F₁ : FiniteFormat} {b₁ : NonNegDyadic}
    (hF₁b : F₁.b = (b₁ : WithTop NonNegDyadic))
    (hN_nn : 0 ≤ ((F₁.toFormat.next b₁.val : Dyadic) : ℝ)) :
    Format.boundOK F₁.toFormat.boundAfterNext (F₁.toFormat.next b₁.val) := by
  obtain ⟨hnn, h_eq⟩ := Format.boundAfterNext_coe hF₁b
  rw [h_eq]
  have hN_nn_q : (0 : ℚ) ≤ ((F₁.toFormat.next b₁.val : Dyadic) : ℚ) := by
    rw [Dyadic.coe_real_eq_ratCast] at hN_nn
    exact_mod_cast hN_nn
  change |((F₁.toFormat.next b₁.val : Dyadic) : ℚ)|
    ≤ ((F₁.toFormat.next b₁.val : Dyadic) : ℚ)
  rw [abs_of_nonneg hN_nn_q]

/-- An in-bound RTZ rounding pins `x` strictly below `next(b₁)`: otherwise
`±next(b₁)` would compete and force `|y| > b₁`. -/
private theorem abs_lt_next_of_toZero_inbound {F₁ : FiniteFormat} {e₁ : ℤ}
    (he₁ : F₁.exp = (e₁ : WithBot ℤ)) {b₁ : NonNegDyadic}
    (hF₁b : F₁.b = (b₁ : WithTop NonNegDyadic)) (hb₁_mem : b₁.val ∈ F₁)
    {x : ℝ} {y : Dyadic}
    (hy : RoundsFinite F₁.unbounded .toZero x y) (hby : Format.boundOK F₁.b y) :
    |x| < ((F₁.toFormat.next b₁.val : Dyadic) : ℝ) := by
  set N := F₁.toFormat.next b₁.val with hN_def
  have hb₁_nn : 0 ≤ ((b₁.val : Dyadic) : ℝ) := by
    rw [Dyadic.coe_real_eq_ratCast]; exact_mod_cast b₁.2
  have hN_lt : ((b₁.val : Dyadic) : ℝ) < (N : ℝ) := lt_next' he₁ b₁.val hb₁_nn
  have hN_nn : 0 ≤ (N : ℝ) := le_trans hb₁_nn hN_lt.le
  have hN_mem : N ∈ F₁.unbounded :=
    next_mem_unbounded he₁ (mem_unbounded_of_mem hb₁_mem)
  by_contra hxN; push Not at hxN
  obtain ⟨-, -, -, hymax⟩ := hy
  have hy_le : |(y : ℝ)| ≤ ((b₁.val : Dyadic) : ℝ) := by
    have h := hby
    rw [hF₁b] at h
    rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast, ← Rat.cast_abs]
    exact_mod_cast h
  by_cases hx_sign : 0 ≤ x
  · have habs : |(N : ℝ)| ≤ |x| := by rwa [abs_of_nonneg hN_nn]
    have hN_y := hymax N hN_mem habs (mul_nonneg hN_nn hx_sign)
    rw [abs_of_nonneg hN_nn] at hN_y
    linarith
  · push Not at hx_sign
    have hnN_mem : (-N) ∈ F₁.unbounded := FiniteFormat.neg_mem hN_mem
    have habs : |((-N : Dyadic) : ℝ)| ≤ |x| := by
      rwa [Dyadic.coe_real_neg, abs_neg, abs_of_nonneg hN_nn]
    have hsign : ((-N : Dyadic) : ℝ) * x ≥ 0 := by
      rw [Dyadic.coe_real_neg]; nlinarith
    have hN_y := hymax (-N) hnN_mem habs hsign
    rw [Dyadic.coe_real_neg, abs_neg, abs_of_nonneg hN_nn] at hN_y
    linarith

/-- No-overflow propagation for RTZ-RTZ: if the unbounded RTZ rounding `y`
of `x` in `F₁` is in-bound, then the unbounded RTZ rounding `z` of `x` in
`F₂` is in-bound: `|x| < next(b₁)` by `abs_lt_next_of_toZero_inbound`, so
`|z| ≤ |x| < next(b₁) ≤ b₂` via the containment. -/
private theorem toZero_noOverflow_F₂ {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hreg : F₁.GridBound)
    {x : ℝ} {y z : Dyadic}
    (hy : RoundsFinite F₁.unbounded .toZero x y) (hby : Format.boundOK F₁.b y)
    (hz : RoundsFinite F₂.unbounded .toZero x z) :
    Format.boundOK F₂.b z := by
  rcases hF₁b : F₁.b with _ | b₁
  · -- `b₁ = ⊤` forces `b₂ = ⊤`.
    rw [bound_top_of_paper_subset hsub hF₁b]
    trivial
  · obtain ⟨hb₁_mem, hexp_ne⟩ := hreg b₁ hF₁b
    obtain ⟨e₁, he₁⟩ : ∃ e₁ : ℤ, F₁.exp = (e₁ : WithBot ℤ) := by
      cases hc : F₁.exp with
      | bot => exact absurd hc hexp_ne
      | coe e => exact ⟨e, rfl⟩
    set N := F₁.toFormat.next b₁.val with hN_def
    have hb₁_nn : 0 ≤ ((b₁.val : Dyadic) : ℝ) := by
      rw [Dyadic.coe_real_eq_ratCast]; exact_mod_cast b₁.2
    have hN_lt : ((b₁.val : Dyadic) : ℝ) < (N : ℝ) := lt_next' he₁ b₁.val hb₁_nn
    have hN_nn : 0 ≤ (N : ℝ) := le_trans hb₁_nn hN_lt.le
    have hN_mem : N ∈ F₁.unbounded :=
      next_mem_unbounded he₁ (mem_unbounded_of_mem hb₁_mem)
    have hxN : |x| < (N : ℝ) :=
      abs_lt_next_of_toZero_inbound he₁ hF₁b hb₁_mem hy hby
    -- `|z| ≤ |x| < N` and `N ∈ F₂`, so `z` is in-bound.
    have hN_F₂ : N ∈ F₂ := by
      apply hsub
      exact ⟨hN_mem.1, hN_mem.2.1, boundOK_boundAfterNext_next hF₁b hN_nn⟩
    have hzN : |(z : ℝ)| ≤ |(N : ℝ)| := by
      rw [abs_of_nonneg hN_nn]
      exact le_trans hz.2.1 hxN.le
    exact boundOK_of_abs_le hzN hN_F₂.2.2

/-- Chain no-overflow for RTZ-RTZ: the unbounded RTZ rounding `w` of `z` in
`F₁` is in-bound, given that the direct rounding `y` is (`w` competes
against `y` at `x`). -/
private theorem toZero_noOverflow_chain {F₁ F₂ : FiniteFormat} {x : ℝ}
    {y z w : Dyadic}
    (hy : RoundsFinite F₁.unbounded .toZero x y) (hby : Format.boundOK F₁.b y)
    (hz : RoundsFinite F₂.unbounded .toZero x z)
    (hw : RoundsFinite F₁.unbounded .toZero (z : ℝ) w) :
    Format.boundOK F₁.b w := by
  obtain ⟨hwmem, hwbnd, hwsign, -⟩ := hw
  obtain ⟨-, hzbnd, hzsign, -⟩ := hz
  have hwx_bnd : |(w : ℝ)| ≤ |x| := le_trans hwbnd hzbnd
  have hw0 : (z : ℝ) = 0 → (w : ℝ) = 0 := by
    intro h
    have h1 : |(w : ℝ)| ≤ 0 := by rw [← abs_zero, ← h]; exact hwbnd
    exact abs_nonpos_iff.mp h1
  have hwx_sign : (w : ℝ) * x ≥ 0 :=
    mul_nonneg_of_common_sign hwsign (by linarith [hzsign] : x * (z : ℝ) ≥ 0) hw0
  have hwy := hy.2.2.2 w hwmem hwx_bnd hwx_sign
  exact boundOK_of_abs_le hwy hby

/-- **rnd-RTZ-RTZ**, total form. Either rounding `x` directly in `F₁`
overflows, or rounding `x` in `F₂` does not overflow (finite `z`), the
chained rounding is finite (`w`), and double rounding holds.

Unlike the spec-relational form, this needs the paper's strengthened
containment `F₁.withBound F₁.boundAfterNext ⊆ F₂` **and** a representable
bound (`b₁ ∈ F₁`, finite `exp₁`) when `b₁` is finite. -/
theorem roundsRTZ_RTZ {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hreg : F₁.GridBound)
    (x : ℝ) :
    (∃ b, Rounds F₁ .toZero x (.overflow b)) ∨
    (∃ z w : Dyadic, Rounds F₂ .toZero x (.finite z) ∧
      Rounds F₁ .toZero (z : ℝ) (.finite w) ∧
      Rounds F₁ .toZero x (.finite w)) := by
  have h₁u := not_isUndefined_toZero F₁
  have h₂u := not_isUndefined_toZero F₂
  -- Plain containment, recovered from the paper form.
  have hsub' : F₁.toFormat ⊆ F₂.toFormat := by
    intro d hd
    apply hsub
    refine ⟨hd.1, hd.2.1, ?_⟩
    change Format.boundOK F₁.toFormat.boundAfterNext d
    rcases hF₁b : F₁.b with _ | b₁
    · rw [Format.boundAfterNext_top hF₁b]; trivial
    · obtain ⟨hnn, h_eq⟩ := Format.boundAfterNext_coe hF₁b
      rw [h_eq]
      have hd_b : Format.boundOK F₁.b d := hd.2.2
      rw [hF₁b] at hd_b
      have hd_b' : |(d : ℚ)| ≤ ((b₁.val : Dyadic) : ℚ) := hd_b
      have hb₁_nn : 0 ≤ ((b₁.val : Dyadic) : ℝ) := by
        rw [Dyadic.coe_real_eq_ratCast]; exact_mod_cast b₁.2
      have h_le : ((b₁.val : Dyadic) : ℚ) ≤ ((F₁.toFormat.next b₁.val : Dyadic) : ℚ) := by
        have h := Format.self_le_next F₁.toFormat b₁.val hb₁_nn
        rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast] at h
        exact_mod_cast h
      change |(d : ℚ)| ≤ ((F₁.toFormat.next b₁.val : Dyadic) : ℚ)
      linarith
  have hy := rndUnbounded_satisfies F₁ .toZero x h₁u
  set y := rndUnbounded F₁ .toZero x h₁u with hy_def
  by_cases hbOK : Format.boundOK F₁.b y
  · right
    -- F₂ does not overflow.
    have hz := rndUnbounded_satisfies F₂ .toZero x h₂u
    set z := rndUnbounded F₂ .toZero x h₂u with hz_def
    have hz_bnd : Format.boundOK F₂.b z := toZero_noOverflow_F₂ hsub hreg hy hbOK hz
    have hzR : Rounds F₂ .toZero x (.finite z) := ⟨h₂u, hz, hz_bnd⟩
    -- The chain does not overflow.
    have hw := rndUnbounded_satisfies F₁ .toZero (z : ℝ) h₁u
    set w := rndUnbounded F₁ .toZero (z : ℝ) h₁u with hw_def
    have hw_bnd : Format.boundOK F₁.b w := toZero_noOverflow_chain hy hbOK hz hw
    have hwR : Rounds F₁ .toZero (z : ℝ) (.finite w) := ⟨h₁u, hw, hw_bnd⟩
    -- Double rounding holds.
    rcases roundsRTZ_RTZ_of_chain hsub' hzR hwR with ⟨b, hovf⟩ | hfin
    · exfalso
      obtain ⟨-, y', hy', hbn', -⟩ := hovf
      rw [rndUnbounded_unique F₁ .toZero x h₁u hy'] at hbn'
      exact hbn' hbOK
    · exact ⟨z, w, hzR, hwR, hfin⟩
  · left
    exact ⟨decide ((0 : ℚ) < (y : ℚ)), h₁u, y, hy, hbOK, by simp⟩

/-- No-overflow propagation for RAZ: if the unbounded RAZ rounding `y` of `x`
in `F₁` is in-bound, then the unbounded RAZ rounding `z` of `x` in `F₂` is
in-bound (`y ∈ F₁ ⊆ F₂` competes, so `|z| ≤ |y|`). -/
private theorem awayZero_noOverflow_F₂ {F₁ F₂ : FiniteFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat) {x : ℝ} {y z : Dyadic}
    (hy : RoundsFinite F₁.unbounded .awayZero x y) (hby : Format.boundOK F₁.b y)
    (hz : RoundsFinite F₂.unbounded .awayZero x z) :
    Format.boundOK F₂.b z := by
  obtain ⟨hymem, hybnd, hysign, _⟩ := hy
  obtain ⟨_, _, _, hzmin⟩ := hz
  have hyF₂ : y ∈ F₂ := hsub y (mem_of_mem_unbounded_of_boundOK hymem hby)
  have hzy : |(z : ℝ)| ≤ |(y : ℝ)| :=
    hzmin y (mem_unbounded_of_mem hyF₂) hybnd hysign
  exact boundOK_of_abs_le hzy hyF₂.2.2

/-- Chain no-overflow for RAZ-RAZ: the unbounded RAZ rounding `w` of `z` in
`F₁` is in-bound, given that the direct rounding `y` is. -/
private theorem awayZero_noOverflow_chain {F₁ F₂ : FiniteFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat) {x : ℝ} {y z w : Dyadic}
    (hy : RoundsFinite F₁.unbounded .awayZero x y) (hby : Format.boundOK F₁.b y)
    (hz : RoundsFinite F₂.unbounded .awayZero x z)
    (hw : RoundsFinite F₁.unbounded .awayZero (z : ℝ) w) :
    Format.boundOK F₁.b w := by
  obtain ⟨hymem, hybnd, hysign, hymin⟩ := hy
  obtain ⟨_, hzbnd, hzsign, hzmin⟩ := hz
  obtain ⟨_, _, _, hwmin⟩ := hw
  -- `|z| ≤ |y|` since `y ∈ F₂.unbounded` competes for `z`.
  have hyF₂ : y ∈ F₂ := hsub y (mem_of_mem_unbounded_of_boundOK hymem hby)
  have hzy : |(z : ℝ)| ≤ |(y : ℝ)| :=
    hzmin y (mem_unbounded_of_mem hyF₂) hybnd hysign
  -- `y·z ≥ 0` (common sign through `x`; at `x = 0` minimality forces `y = 0`).
  have hy0 : x = 0 → (y : ℝ) = 0 := by
    intro hx
    have h0 := hymin 0 F₁.unbounded.toFormat.zero_mem
      (by rw [Dyadic.coe_real_zero, abs_zero, hx, abs_zero])
      (by rw [Dyadic.coe_real_zero, zero_mul])
    rw [Dyadic.coe_real_zero, abs_zero] at h0
    exact abs_nonpos_iff.mp h0
  have hyz : (y : ℝ) * (z : ℝ) ≥ 0 :=
    mul_nonneg_of_common_sign hysign hzsign hy0
  -- `y` competes for `w` at the point `z`.
  have hwy : |(w : ℝ)| ≤ |(y : ℝ)| := hwmin y hymem hzy hyz
  exact boundOK_of_abs_le hwy hby

/-- **rnd-RAZ-RAZ**, total form. Either rounding `x` directly in `F₁`
overflows, or rounding `x` in `F₂` does not overflow (finite `z`), the
chained rounding is finite (`w`), and double rounding holds. -/
theorem roundsRAZ_RAZ {F₁ F₂ : FiniteFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat) (x : ℝ) :
    (∃ b, Rounds F₁ .awayZero x (.overflow b)) ∨
    (∃ z w : Dyadic, Rounds F₂ .awayZero x (.finite z) ∧
      Rounds F₁ .awayZero (z : ℝ) (.finite w) ∧
      Rounds F₁ .awayZero x (.finite w)) := by
  have h₁u := not_isUndefined_awayZero F₁
  have h₂u := not_isUndefined_awayZero F₂
  have hy := rndUnbounded_satisfies F₁ .awayZero x h₁u
  set y := rndUnbounded F₁ .awayZero x h₁u with hy_def
  by_cases hbOK : Format.boundOK F₁.b y
  · right
    -- F₂ does not overflow.
    have hz := rndUnbounded_satisfies F₂ .awayZero x h₂u
    set z := rndUnbounded F₂ .awayZero x h₂u with hz_def
    have hz_bnd : Format.boundOK F₂.b z := awayZero_noOverflow_F₂ hsub hy hbOK hz
    have hzR : Rounds F₂ .awayZero x (.finite z) := ⟨h₂u, hz, hz_bnd⟩
    -- The chain does not overflow.
    have hw := rndUnbounded_satisfies F₁ .awayZero (z : ℝ) h₁u
    set w := rndUnbounded F₁ .awayZero (z : ℝ) h₁u with hw_def
    have hw_bnd : Format.boundOK F₁.b w :=
      awayZero_noOverflow_chain hsub hy hbOK hz hw
    have hwR : Rounds F₁ .awayZero (z : ℝ) (.finite w) := ⟨h₁u, hw, hw_bnd⟩
    -- Double rounding holds (overflow branch of the spec-relational theorem
    -- is refuted by uniqueness against the in-bound `y`).
    rcases roundsRAZ_RAZ_of_chain hsub hzR hwR with ⟨b, hovf⟩ | hfin
    · exfalso
      obtain ⟨_, y', hy', hbn', _⟩ := hovf
      rw [rndUnbounded_unique F₁ .awayZero x h₁u hy'] at hbn'
      exact hbn' hbOK
    · exact ⟨z, w, hzR, hwR, hfin⟩
  · left
    exact ⟨decide ((0 : ℚ) < (y : ℚ)), h₁u, y, hy, hbOK, by simp⟩

/-! ## rnd-RTO-RAZ, total form -/

/-- The relaxed bound `boundAfterNext` accepts anything the original bound
accepts (`b₁ ≤ next(b₁)`). -/
private theorem boundOK_boundAfterNext_of_boundOK {F₁ : FiniteFormat} {d : Dyadic}
    (hd_b : Format.boundOK F₁.b d) :
    Format.boundOK F₁.toFormat.boundAfterNext d := by
  cases hF_b : F₁.b with
  | top => rw [Format.boundAfterNext_top hF_b]; trivial
  | coe b =>
    obtain ⟨hnn, h_after⟩ := Format.boundAfterNext_coe hF_b
    rw [h_after]
    rw [hF_b] at hd_b
    have hd_b' : |(d : ℚ)| ≤ ((b.val : Dyadic) : ℚ) := hd_b
    have hb_nn : 0 ≤ ((b.val : Dyadic) : ℝ) := by
      rw [Dyadic.coe_real_eq_ratCast]; exact_mod_cast b.2
    have h_le : ((b.val : Dyadic) : ℚ) ≤ ((F₁.toFormat.next b.val : Dyadic) : ℚ) := by
      have h := Format.self_le_next F₁.toFormat b.val hb_nn
      rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast] at h
      exact_mod_cast h
    change |(d : ℚ)| ≤ ((F₁.toFormat.next b.val : Dyadic) : ℚ)
    linarith

/-- Membership transfer into the paper containment format: every `d ∈ F₁`
lies in `(F₁.extend 1).withBound F₁.boundAfterNext` (one more bit of
precision, bound relaxed from `b₁` to `next(b₁)`). -/
private theorem mem_paper_of_mem {F₁ : FiniteFormat} {d : Dyadic} (hd : d ∈ F₁) :
    d ∈ ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) := by
  have hd' : d ∈ (F₁.extend 1) := Format.self_subset_extend F₁.toFormat 1 d hd
  exact ⟨hd'.1, hd'.2.1, boundOK_boundAfterNext_of_boundOK hd.2.2⟩

/-- The RTO rounding `z` of `x` in `F₂` is dominated (in magnitude, with
matching sign) by any in-bound RAZ rounding `y` of `x` in `F₁`: the faithful
candidates of `z` are squeezed between `0` and `±y`, since `y ∈ F₂` competes
on `z`'s side. -/
private theorem toOdd_abs_le_of_awayZero {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {x : ℝ} {y z : Dyadic}
    (hy : RoundsFinite F₁.unbounded .awayZero x y) (hby : Format.boundOK F₁.b y)
    (hz : RoundsFinite F₂.unbounded .toOdd x z) :
    |(z : ℝ)| ≤ |(y : ℝ)| ∧ ((y : ℝ)) * ((z : ℝ)) ≥ 0 := by
  obtain ⟨hymem, hyabs, hysign, hymin⟩ := hy
  have hyF₂ : y ∈ F₂ :=
    hsub y (mem_paper_of_mem (mem_of_mem_unbounded_of_boundOK hymem hby))
  have hyF₂u : y ∈ F₂.unbounded := mem_unbounded_of_mem hyF₂
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · -- `x < 0`: `y ≤ x < 0`, both faithful candidates of `z` lie in `[y, 0]`.
    have hy_np : (y : ℝ) ≤ 0 := by nlinarith
    have hy_le_x : (y : ℝ) ≤ x := by
      have h := hyabs
      rw [abs_of_neg hx_neg, abs_of_nonpos hy_np] at h
      linarith
    obtain ⟨-, hfaithful, -⟩ := hz
    rcases hfaithful with ⟨-, hz_le, hz_max⟩ | ⟨-, hz_ge, hz_min⟩
    · have h1 : (y : ℝ) ≤ (z : ℝ) := hz_max y hyF₂u hy_le_x
      constructor
      · rw [abs_of_nonpos (by linarith), abs_of_nonpos hy_np]; linarith
      · nlinarith
    · have h1 : (z : ℝ) ≤ 0 := by
        have h := hz_min 0 F₂.unbounded.zero_mem
          (by rw [Dyadic.coe_real_zero]; linarith)
        rwa [Dyadic.coe_real_zero] at h
      constructor
      · rw [abs_of_nonpos h1, abs_of_nonpos hy_np]; linarith
      · nlinarith
  · -- `x = 0`: `z = 0`.
    have hz0 : z = 0 := toOdd_eq_zero_of_zero (hx_zero ▸ hz)
    rw [hz0]
    constructor
    · rw [Dyadic.coe_real_zero, abs_zero]; exact abs_nonneg _
    · rw [Dyadic.coe_real_zero, mul_zero]
  · -- `x > 0`: mirror image.
    have hy_nn : 0 ≤ (y : ℝ) := by nlinarith
    have hx_le_y : x ≤ (y : ℝ) := by
      have h := hyabs
      rw [abs_of_pos hx_pos, abs_of_nonneg hy_nn] at h
      linarith
    obtain ⟨-, hfaithful, -⟩ := hz
    rcases hfaithful with ⟨-, hz_le, hz_max⟩ | ⟨-, hz_ge, hz_min⟩
    · have h1 : 0 ≤ (z : ℝ) := by
        have h := hz_max 0 F₂.unbounded.zero_mem
          (by rw [Dyadic.coe_real_zero]; linarith)
        rwa [Dyadic.coe_real_zero] at h
      constructor
      · rw [abs_of_nonneg h1, abs_of_nonneg hy_nn]; linarith
      · nlinarith
    · have h1 : (z : ℝ) ≤ (y : ℝ) := hz_min y hyF₂u hx_le_y
      constructor
      · rw [abs_of_nonneg (by linarith), abs_of_nonneg hy_nn]; linarith
      · nlinarith

/-- **rnd-RTO-RAZ**, total form. Either rounding `x` directly in `F₁` (RAZ)
overflows, or the RTO rounding of `x` in `F₂` does not overflow (finite `z`),
the chained RAZ rounding is finite (`w`), and double rounding holds. Same
containment hypothesis as the spec-relational form; `F₂` must support RTO. -/
theorem roundsRTO_RAZ {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (h₂u : ¬ F₂.IsUndefined .toOdd) (x : ℝ) :
    (∃ b, Rounds F₁ .awayZero x (.overflow b)) ∨
    (∃ z w : Dyadic, Rounds F₂ .toOdd x (.finite z) ∧
      Rounds F₁ .awayZero (z : ℝ) (.finite w) ∧
      Rounds F₁ .awayZero x (.finite w)) := by
  have h₁u := not_isUndefined_awayZero F₁
  have hy := rndUnbounded_satisfies F₁ .awayZero x h₁u
  set y := rndUnbounded F₁ .awayZero x h₁u with hy_def
  by_cases hbOK : Format.boundOK F₁.b y
  · right
    -- F₂ does not overflow.
    have hz := rndUnbounded_satisfies F₂ .toOdd x h₂u
    set z := rndUnbounded F₂ .toOdd x h₂u with hz_def
    obtain ⟨hzy_abs, hzy_sign⟩ := toOdd_abs_le_of_awayZero hsub hy hbOK hz
    have hyF₂ : y ∈ F₂ :=
      hsub y (mem_paper_of_mem (mem_of_mem_unbounded_of_boundOK hy.1 hbOK))
    have hz_bnd : Format.boundOK F₂.b z := boundOK_of_abs_le hzy_abs hyF₂.2.2
    have hzR : Rounds F₂ .toOdd x (.finite z) := ⟨h₂u, hz, hz_bnd⟩
    -- The chain does not overflow: `y` competes for `w` at the point `z`.
    have hw := rndUnbounded_satisfies F₁ .awayZero (z : ℝ) h₁u
    set w := rndUnbounded F₁ .awayZero (z : ℝ) h₁u with hw_def
    have hw_bnd : Format.boundOK F₁.b w := by
      have h1 := hw.2.2.2 y hy.1 hzy_abs hzy_sign
      exact boundOK_of_abs_le h1 hbOK
    have hwR : Rounds F₁ .awayZero (z : ℝ) (.finite w) := ⟨h₁u, hw, hw_bnd⟩
    -- Double rounding holds.
    rcases roundsRTO_RAZ_of_chain hsub hzR hwR with ⟨b, hovf⟩ | hfin
    · exfalso
      obtain ⟨-, y', hy', hbn', -⟩ := hovf
      rw [rndUnbounded_unique F₁ .awayZero x h₁u hy'] at hbn'
      exact hbn' hbOK
    · exact ⟨z, w, hzR, hwR, hfin⟩
  · left
    exact ⟨decide ((0 : ℚ) < (y : ℚ)), h₁u, y, hy, hbOK, by simp⟩

/-! ## rnd-RTO-RTZ, total form -/

/-- `2 ≤ F.p` rules out `IsUndefined` (which requires `p = 1`). -/
private theorem not_isUndefined_of_two_le_p {F : FiniteFormat} {rm : RoundingMode}
    (hp : ((2 : ℕ+) : WithTop ℕ+) ≤ F.p) : ¬ F.IsUndefined rm := by
  rintro ⟨h1, -, -⟩
  rw [h1] at hp
  have h2 : (2 : ℕ+) ≤ (1 : ℕ+) := by exact_mod_cast hp
  have h3 : ((2 : ℕ+) : ℕ) ≤ ((1 : ℕ+) : ℕ) := h2
  simp at h3

/-- `F.withBound B`, packaged as a `FiniteFormat` (`p`/`exp` unchanged). -/
private def FiniteFormat.withBoundFF (F : FiniteFormat) (B : WithTop NonNegDyadic) :
    FiniteFormat :=
  ⟨F.toFormat.withBound B, F.finite⟩

/-- Unbounded grid membership plus the relaxed bound gives membership in the
paper containment format `(F₁.extend 1).withBound F₁.boundAfterNext`. -/
private theorem mem_paper_of_mem_unbounded {F₁ : FiniteFormat} {d : Dyadic}
    (hd : d ∈ F₁.unbounded)
    (hb : Format.boundOK F₁.toFormat.boundAfterNext d) :
    d ∈ ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) := by
  have hd' := Format.self_subset_extend F₁.toFormat.unbounded 1 d hd
  exact ⟨hd'.1, hd'.2.1, hb⟩

/-- The faithful candidates of any rounding of `x` in `F₂.unbounded` are
squeezed into `[-N, N]` once `|x| ≤ N` and `±N ∈ F₂.unbounded`. -/
private theorem abs_faithful_le_of_le {F₂ : FiniteFormat} {x : ℝ} {z N : Dyadic}
    (hN_mem : N ∈ F₂.unbounded) (hxN : |x| ≤ (N : ℝ))
    (hfaithful : IsFaithfulRound F₂.unbounded x z) :
    |(z : ℝ)| ≤ (N : ℝ) := by
  have hnN_mem : (-N) ∈ F₂.unbounded := FiniteFormat.neg_mem hN_mem
  rcases hfaithful with ⟨-, hz_le, hz_max⟩ | ⟨-, hz_ge, hz_min⟩
  · have h1 : ((-N : Dyadic) : ℝ) ≤ (z : ℝ) := by
      apply hz_max (-N) hnN_mem
      rw [Dyadic.coe_real_neg]
      have := abs_le.mp hxN
      linarith [this.1]
    rw [Dyadic.coe_real_neg] at h1
    have h2 := abs_le.mp hxN
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · have h1 : (z : ℝ) ≤ (N : ℝ) := by
      apply hz_min N hN_mem
      have := abs_le.mp hxN
      linarith [this.2]
    have h2 := abs_le.mp hxN
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Chain no-overflow for RTO-RTZ. If the chained RTZ rounding `w` of
`z = RTO_{F₂}(x)` escaped the bound, grid minimality would force
`|w| = |z| = next(b₁)`; but `z` is `F₂`-odd (Lemma 5.3 transfer through the
`extend 1` containment shows `z` cannot lie on the `F₁`-grid within the
relaxed bound), contradiction. -/
private theorem toOdd_toZero_noOverflow_chain {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hreg : F₁.GridBound) (hp_F₂ : ((2 : ℕ+) : WithTop ℕ+) ≤ F₂.p)
    {x : ℝ} {y z w : Dyadic}
    (hy : RoundsFinite F₁.unbounded .toZero x y) (hby : Format.boundOK F₁.b y)
    (hz : RoundsFinite F₂.unbounded .toOdd x z)
    (hw : RoundsFinite F₁.unbounded .toZero (z : ℝ) w) :
    Format.boundOK F₁.b w := by
  by_contra hbw
  -- The bound must be finite for the check to fail.
  obtain ⟨b₁, hF₁b⟩ : ∃ b₁ : NonNegDyadic, F₁.b = (b₁ : WithTop NonNegDyadic) := by
    cases hc : F₁.b with
    | top => rw [hc] at hbw; exact (hbw trivial).elim
    | coe b => exact ⟨b, rfl⟩
  obtain ⟨hb₁_mem, hexp_ne⟩ := hreg b₁ hF₁b
  obtain ⟨e₁, he₁⟩ : ∃ e₁ : ℤ, F₁.exp = (e₁ : WithBot ℤ) := by
    cases hc : F₁.exp with
    | bot => exact absurd hc hexp_ne
    | coe e => exact ⟨e, rfl⟩
  set N := F₁.toFormat.next b₁.val with hN_def
  have hb₁_nn : 0 ≤ ((b₁.val : Dyadic) : ℝ) := by
    rw [Dyadic.coe_real_eq_ratCast]; exact_mod_cast b₁.2
  have hN_lt : ((b₁.val : Dyadic) : ℝ) < (N : ℝ) := lt_next' he₁ b₁.val hb₁_nn
  have hN_nn : 0 ≤ (N : ℝ) := le_trans hb₁_nn hN_lt.le
  have hN_mem : N ∈ F₁.unbounded :=
    next_mem_unbounded he₁ (mem_unbounded_of_mem hb₁_mem)
  -- `|x| < N` (no direct overflow), hence `|z| ≤ N`.
  have hxN : |x| < (N : ℝ) :=
    abs_lt_next_of_toZero_inbound he₁ hF₁b hb₁_mem hy hby
  have hN_F₂u : N ∈ F₂.unbounded :=
    mem_unbounded_of_mem
      (hsub N (mem_paper_of_mem_unbounded hN_mem (boundOK_boundAfterNext_next hF₁b hN_nn)))
  have hz_abs : |(z : ℝ)| ≤ (N : ℝ) :=
    abs_faithful_le_of_le hN_F₂u hxN.le hz.2.1
  -- `b₁ < |w| ≤ |z| ≤ N`, and grid minimality pins `|w| = N`.
  have hbw' : ((b₁.val : Dyadic) : ℝ) < |(w : ℝ)| := by
    rw [hF₁b] at hbw
    have h1 : ¬ |(w : ℚ)| ≤ ((b₁.val : Dyadic) : ℚ) := hbw
    push Not at h1
    rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast, ← Rat.cast_abs]
    exact_mod_cast h1
  have hw_abs : |(w : ℝ)| ≤ |(z : ℝ)| := hw.2.1
  have hN_le_w : (N : ℝ) ≤ |(w : ℝ)| := by
    by_cases hw_sign : 0 ≤ (w : ℝ)
    · rw [abs_of_nonneg hw_sign] at hbw' ⊢
      exact next_min he₁ (mem_unbounded_of_mem hb₁_mem) hw.1 hb₁_nn hbw'
    · push Not at hw_sign
      rw [abs_of_neg hw_sign] at hbw' ⊢
      have h1 := next_min he₁ (mem_unbounded_of_mem hb₁_mem)
        (FiniteFormat.neg_mem hw.1) hb₁_nn (by rwa [Dyadic.coe_real_neg])
      rwa [Dyadic.coe_real_neg] at h1
  -- So `z = ±N`, and `z ≠ x`; `z` is the `F₂`-odd RTO result.
  have hzN : |(z : ℝ)| = (N : ℝ) := le_antisymm hz_abs (le_trans hN_le_w hw_abs)
  have hxz : x ≠ (z : ℝ) := by
    intro h
    rw [← h] at hzN
    linarith
  -- Lemma 5.3 transfer: `z` cannot lie on the `F₁` grid within the relaxed
  -- bound — but `±N` does.
  set F₁wB : FiniteFormat := FiniteFormat.withBoundFF F₁ F₁.toFormat.boundAfterNext
    with hF₁wB_def
  have hsub' : ((F₁wB.extend 1)).toFormat ⊆ F₂.unbounded.toFormat := fun d hd =>
    mem_unbounded_of_mem (F := F₂) (hsub d ⟨hd.1, hd.2.1, hd.2.2⟩)
  have h_notmem : z ∉ F₁wB :=
    toOdd_notMem_of_extend_subset hsub' hp_F₂ hz hxz
  have hN_wB : N ∈ F₁wB :=
    ⟨hN_mem.1, hN_mem.2.1, boundOK_boundAfterNext_next hF₁b hN_nn⟩
  rcases abs_eq hN_nn |>.mp hzN with hz_eq | hz_eq
  · exact h_notmem ((Dyadic.coe_real_inj z N).mp hz_eq ▸ hN_wB)
  · have h1 : z = -N := by
      apply (Dyadic.coe_real_inj z (-N)).mp
      rw [Dyadic.coe_real_neg]
      exact hz_eq
    exact h_notmem (h1 ▸ FiniteFormat.neg_mem hN_wB)

/-- **rnd-RTO-RTZ**, total form. Either rounding `x` directly in `F₁` (RTZ)
overflows, or the RTO rounding of `x` in `F₂` does not overflow (finite `z`),
the chained RTZ rounding is finite (`w`), and double rounding holds.

Beyond the spec-relational containment this needs `F₁.GridBound` and the
explicit `2 ≤ F₂.p` (for `p₂ = 1` the exponent-parity convention lets the
RTO result land on `next(b₁)`, overflowing the chain but not the direct
rounding). -/
theorem roundsRTO_RTZ {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hreg : F₁.GridBound) (hp_F₂ : ((2 : ℕ+) : WithTop ℕ+) ≤ F₂.p) (x : ℝ) :
    (∃ b, Rounds F₁ .toZero x (.overflow b)) ∨
    (∃ z w : Dyadic, Rounds F₂ .toOdd x (.finite z) ∧
      Rounds F₁ .toZero (z : ℝ) (.finite w) ∧
      Rounds F₁ .toZero x (.finite w)) := by
  have h₁u := not_isUndefined_toZero F₁
  have h₂u : ¬ F₂.IsUndefined .toOdd := not_isUndefined_of_two_le_p hp_F₂
  have hy := rndUnbounded_satisfies F₁ .toZero x h₁u
  set y := rndUnbounded F₁ .toZero x h₁u with hy_def
  by_cases hbOK : Format.boundOK F₁.b y
  · right
    have hz := rndUnbounded_satisfies F₂ .toOdd x h₂u
    set z := rndUnbounded F₂ .toOdd x h₂u with hz_def
    -- F₂ does not overflow.
    have hz_bnd : Format.boundOK F₂.b z := by
      rcases hF₁b : F₁.b with _ | b₁
      · -- `b₁ = ⊤` forces `b₂ = ⊤` (the containment swallows the whole grid).
        have h1 : ((F₁.extend 1).toFormat.withBound ⊤) ⊆ F₂.toFormat := by
          rw [← Format.boundAfterNext_top hF₁b]; exact hsub
        rw [bound_top_of_withBound_top_subset h1]
        trivial
      · obtain ⟨hb₁_mem, hexp_ne⟩ := hreg b₁ hF₁b
        obtain ⟨e₁, he₁⟩ : ∃ e₁ : ℤ, F₁.exp = (e₁ : WithBot ℤ) := by
          cases hc : F₁.exp with
          | bot => exact absurd hc hexp_ne
          | coe e => exact ⟨e, rfl⟩
        have hb₁_nn : 0 ≤ ((b₁.val : Dyadic) : ℝ) := by
          rw [Dyadic.coe_real_eq_ratCast]; exact_mod_cast b₁.2
        have hN_lt : ((b₁.val : Dyadic) : ℝ) < ((F₁.toFormat.next b₁.val : Dyadic) : ℝ) :=
          lt_next' he₁ b₁.val hb₁_nn
        have hN_nn : 0 ≤ ((F₁.toFormat.next b₁.val : Dyadic) : ℝ) :=
          le_trans hb₁_nn hN_lt.le
        have hN_mem : F₁.toFormat.next b₁.val ∈ F₁.unbounded :=
          next_mem_unbounded he₁ (mem_unbounded_of_mem hb₁_mem)
        have hN_F₂ : F₁.toFormat.next b₁.val ∈ F₂ :=
          hsub _ (mem_paper_of_mem_unbounded hN_mem
            (boundOK_boundAfterNext_next hF₁b hN_nn))
        have hxN : |x| < ((F₁.toFormat.next b₁.val : Dyadic) : ℝ) :=
          abs_lt_next_of_toZero_inbound he₁ hF₁b hb₁_mem hy hbOK
        have hz_abs : |(z : ℝ)| ≤ ((F₁.toFormat.next b₁.val : Dyadic) : ℝ) :=
          abs_faithful_le_of_le (mem_unbounded_of_mem hN_F₂) hxN.le hz.2.1
        exact boundOK_of_abs_le (by rwa [abs_of_nonneg hN_nn]) hN_F₂.2.2
    have hzR : Rounds F₂ .toOdd x (.finite z) := ⟨h₂u, hz, hz_bnd⟩
    -- The chain does not overflow.
    have hw := rndUnbounded_satisfies F₁ .toZero (z : ℝ) h₁u
    set w := rndUnbounded F₁ .toZero (z : ℝ) h₁u with hw_def
    have hw_bnd : Format.boundOK F₁.b w :=
      toOdd_toZero_noOverflow_chain hsub hreg hp_F₂ hy hbOK hz hw
    have hwR : Rounds F₁ .toZero (z : ℝ) (.finite w) := ⟨h₁u, hw, hw_bnd⟩
    -- Double rounding holds.
    rcases roundsRTO_RTZ_of_chain hsub hzR hwR with ⟨b, hovf⟩ | hfin
    · exfalso
      obtain ⟨-, y', hy', hbn', -⟩ := hovf
      rw [rndUnbounded_unique F₁ .toZero x h₁u hy'] at hbn'
      exact hbn' hbOK
    · exact ⟨z, w, hzR, hwR, hfin⟩
  · left
    exact ⟨decide ((0 : ℚ) < (y : ℚ)), h₁u, y, hy, hbOK, by simp⟩

/-! ## rnd-RTO-RTO, total form -/

/-- An in-bound RTO rounding pins `x` strictly below `next(b₁)`: otherwise
both faithful candidates lie beyond `±next(b₁)`, forcing `|y| > b₁`. -/
private theorem abs_lt_next_of_toOdd_inbound {F₁ : FiniteFormat} {e₁ : ℤ}
    (he₁ : F₁.exp = (e₁ : WithBot ℤ)) {b₁ : NonNegDyadic}
    (hF₁b : F₁.b = (b₁ : WithTop NonNegDyadic)) (hb₁_mem : b₁.val ∈ F₁)
    {x : ℝ} {y : Dyadic}
    (hy : RoundsFinite F₁.unbounded .toOdd x y) (hby : Format.boundOK F₁.b y) :
    |x| < ((F₁.toFormat.next b₁.val : Dyadic) : ℝ) := by
  set N := F₁.toFormat.next b₁.val with hN_def
  have hb₁_nn : 0 ≤ ((b₁.val : Dyadic) : ℝ) := by
    rw [Dyadic.coe_real_eq_ratCast]; exact_mod_cast b₁.2
  have hN_lt : ((b₁.val : Dyadic) : ℝ) < (N : ℝ) := lt_next' he₁ b₁.val hb₁_nn
  have hN_nn : 0 ≤ (N : ℝ) := le_trans hb₁_nn hN_lt.le
  have hN_mem : N ∈ F₁.unbounded :=
    next_mem_unbounded he₁ (mem_unbounded_of_mem hb₁_mem)
  by_contra hxN; push Not at hxN
  have hy_le : |(y : ℝ)| ≤ ((b₁.val : Dyadic) : ℝ) := by
    have h := hby
    rw [hF₁b] at h
    rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast, ← Rat.cast_abs]
    exact_mod_cast h
  obtain ⟨-, hfaithful, -⟩ := hy
  by_cases hx_sign : 0 ≤ x
  · -- `N ≤ x`: both faithful candidates are `≥ N`.
    have hN_le_x : (N : ℝ) ≤ x := by rwa [abs_of_nonneg hx_sign] at hxN
    rcases hfaithful with ⟨-, -, hy_max⟩ | ⟨-, hx_le_y, -⟩
    · have h1 := hy_max N hN_mem hN_le_x
      have h2 : (N : ℝ) ≤ |(y : ℝ)| := le_trans h1 (le_abs_self _)
      linarith
    · have h2 : (N : ℝ) ≤ |(y : ℝ)| :=
        le_trans (le_trans hN_le_x hx_le_y) (le_abs_self _)
      linarith
  · -- `x ≤ -N`: both faithful candidates are `≤ -N`.
    push Not at hx_sign
    have hx_le_nN : x ≤ -(N : ℝ) := by
      rw [abs_of_neg hx_sign] at hxN
      linarith
    have hnN_mem : (-N) ∈ F₁.unbounded := FiniteFormat.neg_mem hN_mem
    rcases hfaithful with ⟨-, hy_le_x, -⟩ | ⟨-, -, hy_min⟩
    · have h2 : (N : ℝ) ≤ |(y : ℝ)| := by
        rw [abs_of_nonpos (by linarith : (y : ℝ) ≤ 0)]
        linarith
      linarith
    · have h1 := hy_min (-N) hnN_mem (by rw [Dyadic.coe_real_neg]; linarith)
      rw [Dyadic.coe_real_neg] at h1
      have h2 : (N : ℝ) ≤ |(y : ℝ)| := by
        rw [abs_of_nonpos (by linarith : (y : ℝ) ≤ 0)]
        linarith
      linarith

/-- Chain no-overflow for RTO-RTO, via composition at the *intermediate*
format `G := F₁.withBound next(b₁)`: the chained rounding `w` is in-`G`
(its faithful candidates are squeezed into `[-N, N]`), so the
spec-relational composition at `(G, F₂.unbounded)` plus restrict/lift shows
`w` is *the* unbounded RTO rounding of `x` in `F₁` — which is in-bound by
hypothesis. -/
private theorem toOdd_toOdd_noOverflow_chain {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hreg : F₁.GridBound) (hp_F₂ : ((2 : ℕ+) : WithTop ℕ+) ≤ F₂.p)
    (h₁u : ¬ F₁.IsUndefined .toOdd)
    {x : ℝ} {y z w : Dyadic}
    (hy : RoundsFinite F₁.unbounded .toOdd x y) (hby : Format.boundOK F₁.b y)
    (hz : RoundsFinite F₂.unbounded .toOdd x z)
    (hw : RoundsFinite F₁.unbounded .toOdd (z : ℝ) w) :
    Format.boundOK F₁.b w := by
  rcases hF₁b : F₁.b with _ | b₁
  · trivial
  obtain ⟨hb₁_mem, hexp_ne⟩ := hreg b₁ hF₁b
  obtain ⟨e₁, he₁⟩ : ∃ e₁ : ℤ, F₁.exp = (e₁ : WithBot ℤ) := by
    cases hc : F₁.exp with
    | bot => exact absurd hc hexp_ne
    | coe e => exact ⟨e, rfl⟩
  set N := F₁.toFormat.next b₁.val with hN_def
  have hb₁_nn : 0 ≤ ((b₁.val : Dyadic) : ℝ) := by
    rw [Dyadic.coe_real_eq_ratCast]; exact_mod_cast b₁.2
  have hN_lt : ((b₁.val : Dyadic) : ℝ) < (N : ℝ) := lt_next' he₁ b₁.val hb₁_nn
  have hN_nn : 0 ≤ (N : ℝ) := le_trans hb₁_nn hN_lt.le
  have hN_mem : N ∈ F₁.unbounded :=
    next_mem_unbounded he₁ (mem_unbounded_of_mem hb₁_mem)
  -- `|x| < N` (no direct overflow), hence `|z| ≤ N`, hence `|w| ≤ N`.
  have hby' : Format.boundOK F₁.b y := hby
  rw [hF₁b] at hby'
  have hxN : |x| < (N : ℝ) :=
    abs_lt_next_of_toOdd_inbound he₁ hF₁b hb₁_mem hy hby
  have hN_F₂ : N ∈ F₂ :=
    hsub N ⟨hN_mem.1, hN_mem.2.1, boundOK_boundAfterNext_next hF₁b hN_nn⟩
  have hz_abs : |(z : ℝ)| ≤ (N : ℝ) :=
    abs_faithful_le_of_le (mem_unbounded_of_mem hN_F₂) hxN.le hz.2.1
  have hw_abs : |(w : ℝ)| ≤ (N : ℝ) :=
    abs_faithful_le_of_le hN_mem hz_abs hw.2.1
  -- `w` is in-`G` for the intermediate format `G := F₁.withBound next(b₁)`.
  set G : FiniteFormat := FiniteFormat.withBoundFF F₁ F₁.toFormat.boundAfterNext
    with hG_def
  have hG_bnd_w : Format.boundOK G.b w :=
    boundOK_of_abs_le (by rwa [abs_of_nonneg hN_nn])
      (boundOK_boundAfterNext_next hF₁b hN_nn)
  have hG_bnd_y : Format.boundOK G.b y :=
    boundOK_boundAfterNext_of_boundOK hby
  -- Restrict the chained rounding to `G`, compose at `(G, F₂.unbounded)`,
  -- and lift back: `w` is the unbounded RTO rounding of `x` in `F₁`.
  have hw_G : RoundsFinite G .toOdd (z : ℝ) w :=
    RoundsFinite.toOdd_restrict (F := G) hw hG_bnd_w
  have hsub_G : G.toFormat ⊆ F₂.unbounded.toFormat := fun d hd =>
    mem_unbounded_of_mem (F := F₂) (hsub d hd)
  have hxw_G : RoundsFinite G .toOdd x w := rndRTO_RTO hsub_G hp_F₂ hz hw_G
  have hxw : RoundsFinite F₁.unbounded .toOdd x w :=
    RoundsFinite.toOdd_lift (F := G) hxw_G hy hG_bnd_y
  -- Uniqueness against the in-bound direct rounding.
  have h_eq : w = y := by
    rw [rndUnbounded_unique F₁ .toOdd x h₁u hxw,
      rndUnbounded_unique F₁ .toOdd x h₁u hy]
  rw [h_eq]
  exact hby'

/-- **rnd-RTO-RTO**, total form (unified — no parity split on `b₁`; the
containment is the `rnd-RTO-RTO-O` one, which also covers even `b₁`).
Either rounding `x` directly in `F₁` (RTO) overflows, or the RTO rounding
of `x` in `F₂` does not overflow (finite `z`), the chained RTO rounding is
finite (`w`), and double rounding holds. -/
theorem roundsRTO_RTO {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hreg : F₁.GridBound) (hp_F₂ : ((2 : ℕ+) : WithTop ℕ+) ≤ F₂.p)
    (h₁u : ¬ F₁.IsUndefined .toOdd) (x : ℝ) :
    (∃ b, Rounds F₁ .toOdd x (.overflow b)) ∨
    (∃ z w : Dyadic, Rounds F₂ .toOdd x (.finite z) ∧
      Rounds F₁ .toOdd (z : ℝ) (.finite w) ∧
      Rounds F₁ .toOdd x (.finite w)) := by
  have h₂u : ¬ F₂.IsUndefined .toOdd := not_isUndefined_of_two_le_p hp_F₂
  have hy := rndUnbounded_satisfies F₁ .toOdd x h₁u
  set y := rndUnbounded F₁ .toOdd x h₁u with hy_def
  by_cases hbOK : Format.boundOK F₁.b y
  · right
    have hz := rndUnbounded_satisfies F₂ .toOdd x h₂u
    set z := rndUnbounded F₂ .toOdd x h₂u with hz_def
    -- F₂ does not overflow.
    have hz_bnd : Format.boundOK F₂.b z := by
      rcases hF₁b : F₁.b with _ | b₁
      · rw [bound_top_of_paper_subset hsub hF₁b]
        trivial
      · obtain ⟨hb₁_mem, hexp_ne⟩ := hreg b₁ hF₁b
        obtain ⟨e₁, he₁⟩ : ∃ e₁ : ℤ, F₁.exp = (e₁ : WithBot ℤ) := by
          cases hc : F₁.exp with
          | bot => exact absurd hc hexp_ne
          | coe e => exact ⟨e, rfl⟩
        have hb₁_nn : 0 ≤ ((b₁.val : Dyadic) : ℝ) := by
          rw [Dyadic.coe_real_eq_ratCast]; exact_mod_cast b₁.2
        have hN_lt : ((b₁.val : Dyadic) : ℝ)
            < ((F₁.toFormat.next b₁.val : Dyadic) : ℝ) := lt_next' he₁ b₁.val hb₁_nn
        have hN_nn : 0 ≤ ((F₁.toFormat.next b₁.val : Dyadic) : ℝ) :=
          le_trans hb₁_nn hN_lt.le
        have hN_mem : F₁.toFormat.next b₁.val ∈ F₁.unbounded :=
          next_mem_unbounded he₁ (mem_unbounded_of_mem hb₁_mem)
        have hN_F₂ : F₁.toFormat.next b₁.val ∈ F₂ :=
          hsub _ ⟨hN_mem.1, hN_mem.2.1, boundOK_boundAfterNext_next hF₁b hN_nn⟩
        have hxN : |x| < ((F₁.toFormat.next b₁.val : Dyadic) : ℝ) :=
          abs_lt_next_of_toOdd_inbound he₁ hF₁b hb₁_mem hy hbOK
        have hz_abs : |(z : ℝ)| ≤ ((F₁.toFormat.next b₁.val : Dyadic) : ℝ) :=
          abs_faithful_le_of_le (mem_unbounded_of_mem hN_F₂) hxN.le hz.2.1
        exact boundOK_of_abs_le (by rwa [abs_of_nonneg hN_nn]) hN_F₂.2.2
    have hzR : Rounds F₂ .toOdd x (.finite z) := ⟨h₂u, hz, hz_bnd⟩
    -- The chain does not overflow.
    have hw := rndUnbounded_satisfies F₁ .toOdd (z : ℝ) h₁u
    set w := rndUnbounded F₁ .toOdd (z : ℝ) h₁u with hw_def
    have hw_bnd : Format.boundOK F₁.b w :=
      toOdd_toOdd_noOverflow_chain hsub hreg hp_F₂ h₁u hy hbOK hz hw
    have hwR : Rounds F₁ .toOdd (z : ℝ) (.finite w) := ⟨h₁u, hw, hw_bnd⟩
    -- Double rounding holds.
    have hsub' : F₁.toFormat ⊆ F₂.toFormat := fun d hd =>
      hsub d ⟨hd.1, hd.2.1, boundOK_boundAfterNext_of_boundOK hd.2.2⟩
    rcases roundsRTO_RTO_of_chain hsub' hp_F₂ hzR hwR with ⟨b, hovf⟩ | hfin
    · exfalso
      obtain ⟨-, y', hy', hbn', -⟩ := hovf
      rw [rndUnbounded_unique F₁ .toOdd x h₁u hy'] at hbn'
      exact hbn' hbOK
    · exact ⟨z, w, hzR, hwR, hfin⟩
  · left
    exact ⟨decide ((0 : ℚ) < (y : ℚ)), h₁u, y, hy, hbOK, by simp⟩

/-! ## rnd-RTO-RN, total form -/

/-- The mode-independent components of a `.nearest` rounding spec:
membership, faithfulness, and the closest-distance clause. -/
private theorem nearest_components {F : FiniteFormat} {tb : TieBreak} {x : ℝ}
    {y : Dyadic} (h : RoundsFinite F (.nearest tb) x y) :
    y ∈ F ∧ IsFaithfulRound F x y ∧
      ∀ c : Dyadic, c ∈ F → IsFaithfulRound F x c →
        |x - (y : ℝ)| ≤ |x - (c : ℝ)| := by
  cases tb <;> exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- `next` on `F₁.extend 1` lands exactly on the midpoint of `b` and
`F₁.next b`: extending by one bit halves the grid step. -/
private theorem next_extend_midpoint {F₁ : FiniteFormat} {e₁ : ℤ}
    (he₁ : F₁.exp = (e₁ : WithBot ℤ)) {b : Dyadic}
    (hb_nn : 0 ≤ ((b : Dyadic) : ℝ)) :
    (((F₁.extend 1).toFormat.next b : Dyadic) : ℝ)
      = (((b : Dyadic) : ℝ) + ((F₁.toFormat.next b : Dyadic) : ℝ)) / 2 := by
  have he₁x : (F₁.extend 1).toFormat.exp = ((e₁ - 1 : ℤ) : WithBot ℤ) := by
    change F₁.exp.map (· - ((1 : ℕ+) : ℤ)) = _
    rw [he₁]
    rfl
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hstep : ∀ k : ℤ, ((Dyadic.ofIntZpow 1 k : Dyadic) : ℝ) = (2 : ℝ) ^ k := by
    intro k
    rw [Dyadic.coe_ofIntZpow]; push_cast; ring
  cases hp : F₁.p with
  | top =>
    have hpx : (F₁.extend 1).toFormat.p = ⊤ := by
      change F₁.p.map (· + (1 : ℕ+)) = ⊤
      rw [hp]
      rfl
    rw [Format.next_eq_p_top F₁.toFormat he₁ hp b,
      Format.next_eq_p_top (F₁.extend 1).toFormat he₁x hpx b,
      Dyadic.coe_real_add, Dyadic.coe_real_add, hstep, hstep,
      zpow_sub_one₀ h2]
    ring
  | coe p =>
    have hpx : (F₁.extend 1).toFormat.p = ((p + 1 : ℕ+) : WithTop ℕ+) := by
      change F₁.p.map (· + (1 : ℕ+)) = _
      rw [hp]
      rfl
    by_cases hb0 : ((b : Dyadic) : ℝ) ≤ 0
    · -- `b = 0`: both `next`s are pure powers of two.
      have h_next : F₁.toFormat.next b = Dyadic.ofIntZpow 1 e₁ := by
        have h_eq : F₁.toFormat.next b =
            if ((b : Dyadic) : ℝ) ≤ 0 then Dyadic.ofIntZpow 1 e₁
            else b + Dyadic.ofIntZpow 1
              (max e₁ (Int.log 2 ((b : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1)) := by
          unfold Format.next; rw [he₁, hp]
        rw [h_eq, if_pos hb0]
      have h_nextx : (F₁.extend 1).toFormat.next b = Dyadic.ofIntZpow 1 (e₁ - 1) := by
        have h_eq : (F₁.extend 1).toFormat.next b =
            if ((b : Dyadic) : ℝ) ≤ 0 then Dyadic.ofIntZpow 1 (e₁ - 1)
            else b + Dyadic.ofIntZpow 1
              (max (e₁ - 1)
                (Int.log 2 ((b : Dyadic) : ℝ) - (((p + 1 : ℕ+) : ℕ) : ℤ) + 1)) := by
          unfold Format.next; rw [he₁x, hpx]
        rw [h_eq, if_pos hb0]
      have hb_eq : ((b : Dyadic) : ℝ) = 0 := le_antisymm hb0 hb_nn
      rw [h_next, h_nextx, hstep, hstep, hb_eq, zpow_sub_one₀ h2]
      ring
    · -- `b > 0`: the step exponent drops by exactly one.
      push Not at hb0
      have h_next := Format.next_eq_finite_pos F₁.toFormat he₁ hp hb0
      have h_nextx := Format.next_eq_finite_pos (F₁.extend 1).toFormat he₁x hpx hb0
      have h_max : max (e₁ - 1)
            (Int.log 2 ((b : Dyadic) : ℝ) - (((p + 1 : ℕ+) : ℕ) : ℤ) + 1)
          = max e₁ (Int.log 2 ((b : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1) - 1 := by
        have hcast : (((p + 1 : ℕ+) : ℕ) : ℤ) = ((p : ℕ) : ℤ) + 1 := by
          push_cast; ring
        rw [hcast]
        omega
      rw [h_next, h_nextx, h_max, Dyadic.coe_real_add, Dyadic.coe_real_add,
        hstep, hstep, zpow_sub_one₀ h2]
      ring

/-- The midpoint `M = nextᵉ(b₁)` lies in the paper RN containment format
`(F₁.extend 2).withBound (F₁.extend 1).boundAfterNext`. -/
private theorem mid_mem_paperRN {F₁ : FiniteFormat} {e₁ : ℤ}
    (he₁ : F₁.exp = (e₁ : WithBot ℤ)) {b₁ : NonNegDyadic}
    (hF₁b : F₁.b = (b₁ : WithTop NonNegDyadic)) (hb₁_mem : b₁.val ∈ F₁) :
    (F₁.extend 1).toFormat.next b₁.val
      ∈ ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext) := by
  have he₁x : (F₁.extend 1).exp = ((e₁ - 1 : ℤ) : WithBot ℤ) := by
    change F₁.exp.map (· - ((1 : ℕ+) : ℤ)) = _
    rw [he₁]
    rfl
  have hb₁_memx : b₁.val ∈ (F₁.extend 1).unbounded := by
    have h := Format.self_subset_extend F₁.toFormat.unbounded 1 b₁.val
      (mem_unbounded_of_mem hb₁_mem)
    exact ⟨h.1, h.2.1, trivial⟩
  have hM_mem : (F₁.extend 1).toFormat.next b₁.val ∈ (F₁.extend 1).unbounded :=
    next_mem_unbounded he₁x hb₁_memx
  have hb₁_nn : 0 ≤ ((b₁.val : Dyadic) : ℝ) := by
    rw [Dyadic.coe_real_eq_ratCast]; exact_mod_cast b₁.2
  have hM_nn : 0 ≤ (((F₁.extend 1).toFormat.next b₁.val : Dyadic) : ℝ) :=
    le_trans hb₁_nn (lt_next' he₁x b₁.val hb₁_nn).le
  have hmono := Format.extend_mono F₁.toFormat.unbounded
    (by exact_mod_cast (by omega : (1 : ℕ) ≤ 2) : (1 : ℕ+) ≤ 2)
  have h2 := hmono _ hM_mem
  exact ⟨h2.1, h2.2.1,
    boundOK_boundAfterNext_next (F₁ := F₁.extend 1) hF₁b hM_nn⟩

/-- An in-bound RN rounding pins `|x|` to at most the midpoint
`M = nextᵉ(b₁)` of `b₁` and `next(b₁)`: beyond the midpoint, the
away-side candidate `±next(b₁)` is strictly closer than anything in-bound. -/
private theorem abs_le_mid_of_nearest_inbound {F₁ : FiniteFormat} {e₁ : ℤ}
    (he₁ : F₁.exp = (e₁ : WithBot ℤ)) {b₁ : NonNegDyadic}
    (hF₁b : F₁.b = (b₁ : WithTop NonNegDyadic)) (hb₁_mem : b₁.val ∈ F₁)
    {x : ℝ} {y : Dyadic}
    (hyfaithful : IsFaithfulRound F₁.unbounded x y)
    (hyclose : ∀ c : Dyadic, c ∈ F₁.unbounded → IsFaithfulRound F₁.unbounded x c →
      |x - (y : ℝ)| ≤ |x - (c : ℝ)|)
    (hby : Format.boundOK F₁.b y) :
    |x| ≤ (((F₁.extend 1).toFormat.next b₁.val : Dyadic) : ℝ) := by
  set N := F₁.toFormat.next b₁.val with hN_def
  set M := (F₁.extend 1).toFormat.next b₁.val with hM_def
  have hb₁_nn : 0 ≤ ((b₁.val : Dyadic) : ℝ) := by
    rw [Dyadic.coe_real_eq_ratCast]; exact_mod_cast b₁.2
  have hN_lt : ((b₁.val : Dyadic) : ℝ) < (N : ℝ) := lt_next' he₁ b₁.val hb₁_nn
  have hN_mem : N ∈ F₁.unbounded :=
    next_mem_unbounded he₁ (mem_unbounded_of_mem hb₁_mem)
  have hM_mid : (M : ℝ) = (((b₁.val : Dyadic) : ℝ) + (N : ℝ)) / 2 :=
    next_extend_midpoint he₁ hb₁_nn
  have hb₁_lt_M : ((b₁.val : Dyadic) : ℝ) < (M : ℝ) := by
    rw [hM_mid]; linarith
  have hy_le : |(y : ℝ)| ≤ ((b₁.val : Dyadic) : ℝ) := by
    have h := hby
    rw [hF₁b] at h
    rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast, ← Rat.cast_abs]
    exact_mod_cast h
  have hy_bounds := abs_le.mp hy_le
  by_contra hxM; push Not at hxM
  by_cases hx_sign : 0 ≤ x
  · -- `M < x`.
    have hM_lt_x : (M : ℝ) < x := by rwa [abs_of_nonneg hx_sign] at hxM
    by_cases hxN : x ≤ (N : ℝ)
    · -- `M < x ≤ N`: `N` is RU-faithful and strictly closer than `y`.
      have hN_faithful : IsFaithfulRound F₁.unbounded x N := by
        right
        refine ⟨hN_mem, hxN, ?_⟩
        intro v hv hxv
        have hv_gt : ((b₁.val : Dyadic) : ℝ) < (v : ℝ) := by linarith
        exact next_min he₁ (mem_unbounded_of_mem hb₁_mem) hv hb₁_nn hv_gt
      have h1 := hyclose N hN_mem hN_faithful
      have h2 : |x - (N : ℝ)| = (N : ℝ) - x := by
        rw [abs_of_nonpos (by linarith)]; ring
      have h3 : x - (y : ℝ) ≤ |x - (y : ℝ)| := le_abs_self _
      linarith
    · -- `N < x`: both faithful candidates exceed `N`, breaking the bound.
      push Not at hxN
      rcases hyfaithful with ⟨-, -, hy_max⟩ | ⟨-, hx_le_y, -⟩
      · have h1 := hy_max N hN_mem hxN.le
        linarith
      · linarith
  · -- Mirror: `x < -M`.
    push Not at hx_sign
    have hx_lt_nM : x < -(M : ℝ) := by
      rw [abs_of_neg hx_sign] at hxM
      linarith
    have hnN_mem : (-N) ∈ F₁.unbounded := FiniteFormat.neg_mem hN_mem
    by_cases hxN : -(N : ℝ) ≤ x
    · -- `-N ≤ x < -M`: `-N` is RD-faithful and strictly closer than `y`.
      have hnN_faithful : IsFaithfulRound F₁.unbounded x (-N) := by
        left
        refine ⟨hnN_mem, by rw [Dyadic.coe_real_neg]; exact hxN, ?_⟩
        intro v hv hvx
        rw [Dyadic.coe_real_neg]
        by_contra hvb; push Not at hvb
        have h1 : ((b₁.val : Dyadic) : ℝ) < ((-v : Dyadic) : ℝ) := by
          rw [Dyadic.coe_real_neg]
          linarith
        have h2 := next_min he₁ (mem_unbounded_of_mem hb₁_mem)
          (FiniteFormat.neg_mem hv) hb₁_nn h1
        rw [Dyadic.coe_real_neg] at h2
        linarith
      have h1 := hyclose (-N) hnN_mem hnN_faithful
      have h2 : |x - ((-N : Dyadic) : ℝ)| = x + (N : ℝ) := by
        rw [Dyadic.coe_real_neg, abs_of_nonneg (by linarith)]; ring
      have h3 : (y : ℝ) - x ≤ |x - (y : ℝ)| := by
        rw [abs_sub_comm]; exact le_abs_self _
      linarith
    · -- `x < -N`: both faithful candidates are below `-N`.
      push Not at hxN
      rcases hyfaithful with ⟨-, hy_le_x, -⟩ | ⟨-, -, hy_min⟩
      · linarith
      · have h1 := hy_min (-N) hnN_mem (by rw [Dyadic.coe_real_neg]; linarith)
        rw [Dyadic.coe_real_neg] at h1
        linarith

/-- Chain no-overflow for RTO-RN. With `|z| ≤ M` (midpoint), an out-of-bound
chained rounding would have to sit at `±next(b₁)`, strictly farther from `z`
than the in-bound side `±b₁` — except at `|z| = M` exactly, which Lemma 5.3
(through the `extend 2` containment) rules out. -/
private theorem toOdd_nearest_noOverflow_chain {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
      ⊆ F₂.toFormat)
    (hreg : F₁.GridBound) (hp_F₂ : ((2 : ℕ+) : WithTop ℕ+) ≤ F₂.p)
    {tb : TieBreak} (h₁u : ¬ F₁.IsUndefined (.nearest tb))
    {x : ℝ} {y z w : Dyadic}
    (hy : RoundsFinite F₁.unbounded (.nearest tb) x y)
    (hby : Format.boundOK F₁.b y)
    (hz : RoundsFinite F₂.unbounded .toOdd x z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb) (z : ℝ) w) :
    Format.boundOK F₁.b w := by
  -- `x = z` short-circuits through uniqueness.
  rcases eq_or_ne x ((z : Dyadic) : ℝ) with hxz | hxz
  · have hw' : RoundsFinite F₁.unbounded (.nearest tb) x w := hxz ▸ hw
    have h_eq : w = y := by
      rw [rndUnbounded_unique F₁ (.nearest tb) x h₁u hw',
        rndUnbounded_unique F₁ (.nearest tb) x h₁u hy]
    rw [h_eq]; exact hby
  rcases hF₁b : F₁.b with _ | b₁
  · trivial
  obtain ⟨hb₁_mem, hexp_ne⟩ := hreg b₁ hF₁b
  obtain ⟨e₁, he₁⟩ : ∃ e₁ : ℤ, F₁.exp = (e₁ : WithBot ℤ) := by
    cases hc : F₁.exp with
    | bot => exact absurd hc hexp_ne
    | coe e => exact ⟨e, rfl⟩
  obtain ⟨hymem, hyfaithful, hyclose⟩ := nearest_components hy
  obtain ⟨hwmem, hwfaithful, hwclose⟩ := nearest_components hw
  set N := F₁.toFormat.next b₁.val with hN_def
  set M := (F₁.extend 1).toFormat.next b₁.val with hM_def
  have hb₁_nn : 0 ≤ ((b₁.val : Dyadic) : ℝ) := by
    rw [Dyadic.coe_real_eq_ratCast]; exact_mod_cast b₁.2
  have hb₁_mem_u : b₁.val ∈ F₁.unbounded := mem_unbounded_of_mem hb₁_mem
  have hN_lt : ((b₁.val : Dyadic) : ℝ) < (N : ℝ) := lt_next' he₁ b₁.val hb₁_nn
  have hM_mid : (M : ℝ) = (((b₁.val : Dyadic) : ℝ) + (N : ℝ)) / 2 :=
    next_extend_midpoint he₁ hb₁_nn
  have hM_nn : 0 ≤ (M : ℝ) := by rw [hM_mid]; linarith
  have hby' : Format.boundOK ((b₁ : WithTop NonNegDyadic)) y := by
    rw [hF₁b] at hby; exact hby
  -- `|x| ≤ M`, hence `|z| ≤ M`.
  have hxM : |x| ≤ (M : ℝ) :=
    abs_le_mid_of_nearest_inbound he₁ hF₁b hb₁_mem hyfaithful hyclose
      (by rw [hF₁b]; exact hby')
  have hM_F₂ : M ∈ F₂ := hsub M (mid_mem_paperRN he₁ hF₁b hb₁_mem)
  have hzM : |(z : ℝ)| ≤ (M : ℝ) :=
    abs_faithful_le_of_le (mem_unbounded_of_mem hM_F₂) hxM hz.2.1
  -- If `|z| ≤ b₁`, the chained rounding is squeezed in-bound directly.
  by_cases hzb : |(z : ℝ)| ≤ ((b₁.val : Dyadic) : ℝ)
  · have hw_abs : |(w : ℝ)| ≤ ((b₁.val : Dyadic) : ℝ) :=
      abs_faithful_le_of_le hb₁_mem_u hzb hwfaithful
    have hb₁_ok : Format.boundOK ((b₁ : WithTop NonNegDyadic)) b₁.val := by
      change |(b₁.val : ℚ)| ≤ ((b₁.val : Dyadic) : ℚ)
      rw [abs_of_nonneg (by exact_mod_cast b₁.2 : (0 : ℚ) ≤ (b₁.val : ℚ))]
    exact boundOK_of_abs_le (by rwa [abs_of_nonneg hb₁_nn]) hb₁_ok
  push Not at hzb
  -- `b₁ < |z| ≤ M`; Lemma 5.3 through the `extend 2` containment excludes
  -- `|z| = M`, so `b₁ < |z| < M`.
  have h_notmem : z ∉ FiniteFormat.withBoundFF (F₁.extend 1)
      ((F₁.extend 1).toFormat.boundAfterNext) := by
    apply toOdd_notMem_of_extend_subset (F₂ := F₂.unbounded) ?_ hp_F₂ hz hxz
    intro d hd
    exact mem_unbounded_of_mem (F := F₂) (hsub d
      (Format.extend_one_extend_one_subset_extend_two
        (F₁.toFormat.withBound ((F₁.extend 1).toFormat.boundAfterNext)) d hd))
  have hM_G' : M ∈ FiniteFormat.withBoundFF (F₁.extend 1)
      ((F₁.extend 1).toFormat.boundAfterNext) := by
    have h := mid_mem_paperRN he₁ hF₁b hb₁_mem
    have he₁x : (F₁.extend 1).exp = ((e₁ - 1 : ℤ) : WithBot ℤ) := by
      change F₁.exp.map (· - ((1 : ℕ+) : ℤ)) = _
      rw [he₁]
      rfl
    have hb₁_memx : b₁.val ∈ (F₁.extend 1).unbounded := by
      have h' := Format.self_subset_extend F₁.toFormat.unbounded 1 b₁.val hb₁_mem_u
      exact ⟨h'.1, h'.2.1, trivial⟩
    have hM_mem : M ∈ (F₁.extend 1).unbounded := next_mem_unbounded he₁x hb₁_memx
    exact ⟨hM_mem.1, hM_mem.2.1,
      boundOK_boundAfterNext_next (F₁ := F₁.extend 1) hF₁b hM_nn⟩
  have hzM_lt : |(z : ℝ)| < (M : ℝ) := by
    rcases lt_or_eq_of_le hzM with h | h
    · exact h
    · exfalso
      rcases (abs_eq hM_nn).mp h with hz_eq | hz_eq
      · exact h_notmem ((Dyadic.coe_real_inj z M).mp hz_eq ▸ hM_G')
      · have h1 : z = -M := by
          apply (Dyadic.coe_real_inj z (-M)).mp
          rw [Dyadic.coe_real_neg]
          exact hz_eq
        exact h_notmem (h1 ▸ FiniteFormat.neg_mem hM_G')
  -- Sign split: the chained rounding must stay on the `±b₁` side.
  by_contra hbw
  have hbw' : ((b₁.val : Dyadic) : ℝ) < |(w : ℝ)| := by
    have h1 : ¬ |(w : ℚ)| ≤ ((b₁.val : Dyadic) : ℚ) := hbw
    push Not at h1
    rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast, ← Rat.cast_abs]
    exact_mod_cast h1
  by_cases hz_sign : 0 ≤ (z : ℝ)
  · -- `b₁ < z < M`.
    have hz_gt : ((b₁.val : Dyadic) : ℝ) < (z : ℝ) := by
      rwa [abs_of_nonneg hz_sign] at hzb
    have hz_lt : (z : ℝ) < (M : ℝ) := by rwa [abs_of_nonneg hz_sign] at hzM_lt
    -- `b₁` is RD-faithful at `z`.
    have hb₁_faithful : IsFaithfulRound F₁.unbounded ((z : Dyadic) : ℝ) b₁.val := by
      left
      refine ⟨hb₁_mem_u, hz_gt.le, ?_⟩
      intro v hv hvz
      by_contra hvb; push Not at hvb
      have h1 := next_min he₁ hb₁_mem_u hv hb₁_nn hvb
      linarith
    -- An out-of-bound `w` must be the RU candidate `≥ N`.
    have hw_ge_N : (N : ℝ) ≤ (w : ℝ) := by
      rcases hwfaithful with ⟨-, hw_le, hw_max⟩ | ⟨-, hw_ge, -⟩
      · exfalso
        have h1 : ((-(b₁.val) : Dyadic) : ℝ) ≤ (w : ℝ) := by
          apply hw_max _ (FiniteFormat.neg_mem hb₁_mem_u)
          rw [Dyadic.coe_real_neg]; linarith
        rw [Dyadic.coe_real_neg] at h1
        rcases le_or_gt 0 ((w : Dyadic) : ℝ) with h | h
        · rw [abs_of_nonneg h] at hbw'
          have h2 := next_min he₁ hb₁_mem_u hwmem hb₁_nn hbw'
          linarith
        · rw [abs_of_neg h] at hbw'
          linarith
      · have h1 : ((b₁.val : Dyadic) : ℝ) < (w : ℝ) := by linarith
        exact next_min he₁ hb₁_mem_u hwmem hb₁_nn h1
    -- Closest-distance contradiction across the midpoint.
    have h1 := hwclose b₁.val hb₁_mem_u hb₁_faithful
    have h2 : |((z : Dyadic) : ℝ) - ((b₁.val : Dyadic) : ℝ)|
        = (z : ℝ) - ((b₁.val : Dyadic) : ℝ) := abs_of_nonneg (by linarith)
    have h3 : |((z : Dyadic) : ℝ) - ((w : Dyadic) : ℝ)| = (w : ℝ) - (z : ℝ) := by
      rw [abs_sub_comm]
      exact abs_of_nonneg (by linarith)
    rw [h2, h3] at h1
    linarith
  · -- Mirror: `-M < z < -b₁`.
    push Not at hz_sign
    have hz_lt : (z : ℝ) < -((b₁.val : Dyadic) : ℝ) := by
      rw [abs_of_neg hz_sign] at hzb
      linarith
    have hz_gt : -(M : ℝ) < (z : ℝ) := by
      rw [abs_of_neg hz_sign] at hzM_lt
      linarith
    -- `-b₁` is RU-faithful at `z`.
    have hnb₁_faithful : IsFaithfulRound F₁.unbounded ((z : Dyadic) : ℝ)
        (-(b₁.val)) := by
      right
      refine ⟨FiniteFormat.neg_mem hb₁_mem_u,
        by rw [Dyadic.coe_real_neg]; linarith, ?_⟩
      intro v hv hzv
      rw [Dyadic.coe_real_neg]
      by_contra hvb; push Not at hvb
      have h1 : ((b₁.val : Dyadic) : ℝ) < ((-v : Dyadic) : ℝ) := by
        rw [Dyadic.coe_real_neg]; linarith
      have h2 := next_min he₁ hb₁_mem_u (FiniteFormat.neg_mem hv) hb₁_nn h1
      rw [Dyadic.coe_real_neg] at h2
      linarith
    -- An out-of-bound `w` must be the RD candidate `≤ -N`.
    have hw_le_nN : (w : ℝ) ≤ -(N : ℝ) := by
      rcases hwfaithful with ⟨-, hw_le, -⟩ | ⟨-, hw_ge, hw_min⟩
      · have h1 : ((b₁.val : Dyadic) : ℝ) < ((-w : Dyadic) : ℝ) := by
          rw [Dyadic.coe_real_neg]; linarith
        have h2 := next_min he₁ hb₁_mem_u (FiniteFormat.neg_mem hwmem) hb₁_nn h1
        rw [Dyadic.coe_real_neg] at h2
        linarith
      · exfalso
        have h1 : (w : ℝ) ≤ ((-(b₁.val) : Dyadic) : ℝ) := by
          apply hw_min _ (FiniteFormat.neg_mem hb₁_mem_u)
          rw [Dyadic.coe_real_neg]; linarith
        rw [Dyadic.coe_real_neg] at h1
        rcases le_or_gt 0 ((w : Dyadic) : ℝ) with h | h
        · rw [abs_of_nonneg h] at hbw'
          linarith
        · rw [abs_of_neg h] at hbw'
          have h2 := next_min he₁ hb₁_mem_u (FiniteFormat.neg_mem hwmem) hb₁_nn
            (by rw [Dyadic.coe_real_neg]; linarith)
          rw [Dyadic.coe_real_neg] at h2
          linarith
    -- Closest-distance contradiction across the midpoint.
    have h1 := hwclose (-(b₁.val)) (FiniteFormat.neg_mem hb₁_mem_u) hnb₁_faithful
    have h2 : |((z : Dyadic) : ℝ) - ((-(b₁.val) : Dyadic) : ℝ)|
        = -((b₁.val : Dyadic) : ℝ) - (z : ℝ) := by
      rw [Dyadic.coe_real_neg, abs_of_nonpos (by linarith)]
      ring
    have h3 : |((z : Dyadic) : ℝ) - ((w : Dyadic) : ℝ)| = (z : ℝ) - (w : ℝ) :=
      abs_of_nonneg (by linarith)
    rw [h2, h3] at h1
    linarith

/-- **rnd-RTO-RN**, total form, parameterized by the tie-break `tb` (covers
RNE and RNA). Either rounding `x` directly in `F₁` (RN) overflows, or the
RTO rounding of `x` in `F₂` does not overflow (finite `z`), the chained RN
rounding is finite (`w`), and double rounding holds. -/
theorem roundsRTO_RN {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
      ⊆ F₂.toFormat)
    (hreg : F₁.GridBound) (hp_F₂ : ((2 : ℕ+) : WithTop ℕ+) ≤ F₂.p)
    {tb : TieBreak} (h₁u : ¬ F₁.IsUndefined (.nearest tb)) (x : ℝ) :
    (∃ b, Rounds F₁ (.nearest tb) x (.overflow b)) ∨
    (∃ z w : Dyadic, Rounds F₂ .toOdd x (.finite z) ∧
      Rounds F₁ (.nearest tb) (z : ℝ) (.finite w) ∧
      Rounds F₁ (.nearest tb) x (.finite w)) := by
  have h₂u : ¬ F₂.IsUndefined .toOdd := not_isUndefined_of_two_le_p hp_F₂
  have hy := rndUnbounded_satisfies F₁ (.nearest tb) x h₁u
  set y := rndUnbounded F₁ (.nearest tb) x h₁u with hy_def
  by_cases hbOK : Format.boundOK F₁.b y
  · right
    have hz := rndUnbounded_satisfies F₂ .toOdd x h₂u
    set z := rndUnbounded F₂ .toOdd x h₂u with hz_def
    -- F₂ does not overflow.
    have hz_bnd : Format.boundOK F₂.b z := by
      rcases hF₁b : F₁.b with _ | b₁
      · have hB_top : (F₁.extend 1).toFormat.boundAfterNext = ⊤ :=
          Format.boundAfterNext_top hF₁b
        rw [hB_top] at hsub
        rw [bound_top_of_withBound_top_subset hsub]
        trivial
      · obtain ⟨hb₁_mem, hexp_ne⟩ := hreg b₁ hF₁b
        obtain ⟨e₁, he₁⟩ : ∃ e₁ : ℤ, F₁.exp = (e₁ : WithBot ℤ) := by
          cases hc : F₁.exp with
          | bot => exact absurd hc hexp_ne
          | coe e => exact ⟨e, rfl⟩
        obtain ⟨hymem, hyfaithful, hyclose⟩ := nearest_components hy
        have hxM : |x| ≤ (((F₁.extend 1).toFormat.next b₁.val : Dyadic) : ℝ) :=
          abs_le_mid_of_nearest_inbound he₁ hF₁b hb₁_mem hyfaithful hyclose hbOK
        have hM_F₂ : (F₁.extend 1).toFormat.next b₁.val ∈ F₂ :=
          hsub _ (mid_mem_paperRN he₁ hF₁b hb₁_mem)
        have hb₁_nn : 0 ≤ ((b₁.val : Dyadic) : ℝ) := by
          rw [Dyadic.coe_real_eq_ratCast]; exact_mod_cast b₁.2
        have hM_nn : 0 ≤ (((F₁.extend 1).toFormat.next b₁.val : Dyadic) : ℝ) := by
          have he₁x : (F₁.extend 1).exp = ((e₁ - 1 : ℤ) : WithBot ℤ) := by
            change F₁.exp.map (· - ((1 : ℕ+) : ℤ)) = _
            rw [he₁]
            rfl
          exact le_trans hb₁_nn (lt_next' he₁x b₁.val hb₁_nn).le
        have hz_abs : |(z : ℝ)| ≤ (((F₁.extend 1).toFormat.next b₁.val : Dyadic) : ℝ) :=
          abs_faithful_le_of_le (mem_unbounded_of_mem hM_F₂) hxM hz.2.1
        exact boundOK_of_abs_le (by rwa [abs_of_nonneg hM_nn]) hM_F₂.2.2
    have hzR : Rounds F₂ .toOdd x (.finite z) := ⟨h₂u, hz, hz_bnd⟩
    -- The chain does not overflow.
    have hw := rndUnbounded_satisfies F₁ (.nearest tb) (z : ℝ) h₁u
    set w := rndUnbounded F₁ (.nearest tb) (z : ℝ) h₁u with hw_def
    have hw_bnd : Format.boundOK F₁.b w :=
      toOdd_nearest_noOverflow_chain hsub hreg hp_F₂ h₁u hy hbOK hz hw
    have hwR : Rounds F₁ (.nearest tb) (z : ℝ) (.finite w) := ⟨h₁u, hw, hw_bnd⟩
    -- Double rounding holds.
    rcases roundsRTO_RN_of_chain hsub hzR hwR with ⟨b, hovf⟩ | hfin
    · exfalso
      obtain ⟨-, y', hy', hbn', -⟩ := hovf
      rw [rndUnbounded_unique F₁ (.nearest tb) x h₁u hy'] at hbn'
      exact hbn' hbOK
    · exact ⟨z, w, hzR, hwR, hfin⟩
  · left
    exact ⟨decide ((0 : ℚ) < (y : ℚ)), h₁u, y, hy, hbOK, by simp⟩

end Mpfx
