import Mpfx2.Digits
import Mpfx2.Rounding

/-!
# Correct double rounding (§5.2, Fig. 9)

The double-rounding rules, stated *spec-relationally*: given that `z` is the
rounding of `x` in `F₂` and `w` is the rounding of `z` in `F₁` (with
`F₁ ⊆ F₂`), conclude that `w` is also the rounding of `x` in `F₁` directly.
This matches the paper's reasoning and sidesteps overflow bookkeeping —
existence of `z`, `w` is taken as hypotheses.

Stated over `RoundsFinite` (membership + mode condition, no separate bound
check), the Mpfx2 analog of the paper's `rnd`-relation.
-/

namespace Mpfx2

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

/-- Promote `F : FiniteFormat` to `ParityFormat` from a
`¬ IsUndefined .toOdd` witness. (Local replica of the `private` definition
in `Mpfx2/RoundOp.lean`.) -/
private def FiniteFormat.toParityFormatOfToOdd
    (F : FiniteFormat) (h : ¬ F.IsUndefined .toOdd) : ParityFormat := by
  refine ⟨F, ?_⟩
  by_contra h_neg; push Not at h_neg
  exact h ⟨h_neg.1, h_neg.2, Or.inl rfl⟩

/-- If `F₁ ⊆ F₂`, `F₁.exp = ⊥`, and `F₁` contains a nonzero element `z`, then
`F₂.exp = ⊥` as well: an `exp = ⊥` (unbounded-quantum) format embeds values of
arbitrarily small quantum, which a finite-`exp` `F₂` cannot represent. -/
private theorem exp_bot_of_subset {F₁ F₂ : FiniteFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat) (hexp₁ : F₁.toFormat.exp = ⊥)
    {z : Dyadic} (hzF₁ : z ∈ F₁) (hz_ne : z ≠ 0) :
    F₂.toFormat.exp = ⊥ := by
  by_contra hF₂_exp
  -- F₂.exp = (e' : ℤ).
  obtain ⟨e', he'⟩ : ∃ e' : ℤ, F₂.toFormat.exp = (e' : WithBot ℤ) := by
    cases hc : F₂.toFormat.exp with
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
      cases hp₁ : F₁.toFormat.p with
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
      have hzbnd : Format.boundOK F₁.toFormat.b z := hzF₁.2.2
      have h2k_le_z : (2 : ℚ) ^ k ≤ |(z : ℚ)| := by
        have hlog_le : (2 : ℚ) ^ (Int.log 2 |(z : ℚ)|) ≤ |(z : ℚ)| :=
          Int.zpow_log_le_self (by norm_num) (abs_pos.mpr hz_ne_q)
        calc (2 : ℚ) ^ k ≤ (2 : ℚ) ^ (Int.log 2 |(z : ℚ)|) :=
              zpow_le_zpow_right₀ (by norm_num) hk_le_log
          _ ≤ |(z : ℚ)| := hlog_le
      have hzbnd' : Format.boundOK F₁.toFormat.b z := hzbnd
      rcases hb : F₁.toFormat.b with _ | b
      · trivial
      · rw [hb] at hzbnd'
        change |(w : ℚ)| ≤ ((b.val : Dyadic) : ℚ)
        simp only [Format.boundOK] at hzbnd'
        rw [hw_q, abs_of_pos h2k_pos]
        linarith
  -- But `w ∉ F₂`: quantum constraint fails since `k < e'`.
  have hwF₂ := hsub w hwF₁
  have hwq₂ : Dyadic.quantumAtLeast F₂.toFormat.exp w := hwF₂.2.1
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
    (hp_F₂ : ((2 : ℕ+) : WithTop ℕ+) ≤ F₂.toFormat.p)
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
          have hF₂'_exp_bot : F₂'.toFormat.exp = ⊥ :=
            exp_bot_of_subset (hF₂'eq ▸ hsub) hexp_bot hw'F₁ hz_ne
          obtain ⟨p₂, hp₂⟩ : ∃ p₂ : ℕ+, F₂'.toFormat.p = ((p₂ : ℕ+) : WithTop ℕ+) := by
            cases hc : F₂'.toFormat.p with
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
          have h_p_F₂' : ((2 : ℕ+) : WithTop ℕ+) ≤ F₂'.toFormat.p := by
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

end Mpfx2
