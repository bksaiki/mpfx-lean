import Mpfx2.Digits
import Mpfx2.Grid
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
    (hp_F₂ : ((2 : ℕ+) : WithTop ℕ+) ≤ F₂.toFormat.p)
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
  have hp_F₂' : ((2 : ℕ+) : WithTop ℕ+) ≤ F₂'.toFormat.p := by rw [hF₂'eq]; exact hp_F₂
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
  cases hF_b : F₁.toFormat.b with
  | top =>
    rw [Format.boundAfterNext_top hF_b]; trivial
  | coe b =>
    obtain ⟨h_nn, h_after⟩ := Format.boundAfterNext_coe hF_b
    rw [h_after]
    -- goal: |(y : ℚ)| ≤ ((F₁.next b.val : Dyadic) : ℚ).
    change |((y : Dyadic) : ℚ)| ≤ (((F₁.toFormat.next b.val : Dyadic)) : ℚ)
    -- y's own bound: |y| ≤ b.val (over ℚ), since (extend 1).b = F₁.b.
    change Format.boundOK (F₁.extend 1).toFormat.b y at hb_y
    rw [show (F₁.extend 1).toFormat.b = F₁.toFormat.b from rfl, hF_b] at hb_y
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
    ((2 : ℕ+) : WithTop ℕ+) ≤ F₂.toFormat.p ∨ ∀ d : Dyadic, d ∈ F₁ → (d : ℝ) = 0 := by
  by_contra h
  push Not at h
  obtain ⟨h_p_lt, ⟨d, hd_mem, hd_ne⟩⟩ := h
  -- F₁⁺.p = F₁.p + 1 ≥ 2 since F₁.p ≥ 1 (ℕ+ values are ≥ 1).
  have h_F₁ext_p_ge_2 :
      ((2 : ℕ+) : WithTop ℕ+) ≤ (F₁.extend 1).toFormat.p := by
    change ((2 : ℕ+) : WithTop ℕ+) ≤ F₁.toFormat.p.map (· + (1 : ℕ+))
    cases hp : F₁.toFormat.p with
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
      Dyadic.quantumAtLeast (F₁.toFormat.exp.map (· - (1 : ℤ))) (Dyadic.ofIntZpow 3 k) →
      Format.boundOK F₁.toFormat.boundAfterNext (Dyadic.ofIntZpow 3 k) →
      Dyadic.ofIntZpow 3 k ∈
        ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) := by
    intro k hq hb
    refine ⟨?_, ?_, ?_⟩
    · -- precisionAtMost (F₁.p + 1) (ofIntZpow 3 k)
      change Dyadic.precisionAtMost (F₁.extend 1).toFormat.p _
      exact Dyadic.precisionAtMost_mono h_F₁ext_p_ge_2
        (Dyadic.precisionAtMost_two_three_zpow k)
    · -- quantumAtLeast — withBound preserves exp = (extend 1).exp = F₁.exp.map (· - 1).
      change Dyadic.quantumAtLeast (F₁.extend 1).toFormat.exp _
      exact hq
    · -- boundOK — withBound's b = F₁.boundAfterNext.
      change Format.boundOK F₁.toFormat.boundAfterNext _
      exact hb
  rcases hF_exp : F₁.toFormat.exp with _ | e
  · -- F₁.exp = ⊥. F₁⁺.exp = ⊥ ⇒ quantumAtLeast trivial.
    have h_q_triv : ∀ k : ℤ, Dyadic.quantumAtLeast (F₁.toFormat.exp.map (· - (1 : ℤ)))
        (Dyadic.ofIntZpow 3 k) := by
      intro k; rw [hF_exp]; exact trivial
    rcases hF_b : F₁.toFormat.b with _ | b
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
    have h_q_d : Dyadic.quantumAtLeast (F₁.toFormat.exp) d := hd_mem.2.1
    rw [hF_exp] at h_q_d
    have hd_abs_ge : (2 : ℝ)^e ≤ |(d : ℝ)| :=
      Dyadic.abs_ge_two_zpow_of_quantum h_q_d hd_ne
    have h_q_v : ∀ k : ℤ, k ≥ e - 1 →
        Dyadic.quantumAtLeast (F₁.toFormat.exp.map (· - (1 : ℤ))) (Dyadic.ofIntZpow 3 k) := by
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
    rcases hF_b : F₁.toFormat.b with _ | b
    · -- F₁.b = ⊤. Witness 3·2^(e-1).
      refine ⟨Dyadic.ofIntZpow 3 (e - 1), h_mk_member (e - 1) (h_q_v (e - 1) (by omega)) ?_,
        Dyadic.not_precisionAtMost_one_three_zpow (e - 1)⟩
      rw [Format.boundAfterNext_top hF_b]; trivial
    · -- F₁.b = (b : NonNegDyadic). |d| ≤ b. With |d| ≥ 2^e: b ≥ 2^e.
      have hd_le_b_q : |((d : Dyadic) : ℚ)| ≤ ((b.val : Dyadic) : ℚ) := by
        have hb_OK : Format.boundOK F₁.toFormat.b d := hd_mem.2.2
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
      rcases hF_p : F₁.toFormat.p with _ | p
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
    (hp_F₂ : ((2 : ℕ+) : WithTop ℕ+) ≤ F₂.toFormat.p)
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
    (hp_F₂ : ((2 : ℕ+) : WithTop ℕ+) ≤ F₂.toFormat.p)
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
  cases hp : F₁.toFormat.p with
  | top =>
    cases he : F₁.toFormat.exp with
    | bot =>
        exact absurd F₁.finite (by push Not; exact ⟨hp, he⟩)
    | coe e' => exact midpoint_mem_extend_one_of_p_top F₁ hp he hy₁F hy₂F
  | coe p' =>
    cases he : F₁.toFormat.exp with
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
  cases hF_b : (F₁.extend 1).toFormat.b with
  | top =>
    rw [Format.boundAfterNext_top hF_b]; trivial
  | coe b =>
    obtain ⟨h_nn, h_after⟩ := Format.boundAfterNext_coe hF_b
    rw [h_after]
    change |((y : Dyadic) : ℚ)| ≤ (((F₁.extend 1).toFormat.next b.val : Dyadic) : ℚ)
    -- y ∈ F₁.extend 2 has |y| ≤ (F₁.extend 2).b = F₁.b = (F₁.extend 1).b = b.
    change Format.boundOK (F₁.extend 2).toFormat.b y at hb_y
    rw [show (F₁.extend 2).toFormat.b = (F₁.extend 1).toFormat.b from rfl, hF_b] at hb_y
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
    ((2 : ℕ+) : WithTop ℕ+) ≤ F₂.toFormat.p ∨ ∀ d : Dyadic, d ∈ F₁ → (d : ℝ) = 0 := by
  by_contra h
  push Not at h
  obtain ⟨h_p_lt, ⟨d, hd_mem, hd_ne⟩⟩ := h
  -- F₁⁺².p = F₁.p + 2 ≥ 2.
  have h_F₁ext2_p_ge_2 :
      ((2 : ℕ+) : WithTop ℕ+) ≤ (F₁.extend 2).toFormat.p := by
    change ((2 : ℕ+) : WithTop ℕ+) ≤ F₁.toFormat.p.map (· + (2 : ℕ+))
    cases hp : F₁.toFormat.p with
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
      Dyadic.quantumAtLeast (F₁.toFormat.exp.map (· - (2 : ℤ))) (Dyadic.ofIntZpow 3 k) →
      Format.boundOK (F₁.extend 1).toFormat.boundAfterNext (Dyadic.ofIntZpow 3 k) →
      Dyadic.ofIntZpow 3 k ∈
        ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext) := by
    intro k hq hb
    refine ⟨?_, ?_, ?_⟩
    · change Dyadic.precisionAtMost (F₁.extend 2).toFormat.p _
      exact Dyadic.precisionAtMost_mono h_F₁ext2_p_ge_2
        (Dyadic.precisionAtMost_two_three_zpow k)
    · change Dyadic.quantumAtLeast (F₁.extend 2).toFormat.exp _
      exact hq
    · change Format.boundOK (F₁.extend 1).toFormat.boundAfterNext _
      exact hb
  rcases hF_exp : F₁.toFormat.exp with _ | e
  · -- F₁.exp = ⊥. F₁⁺².exp = ⊥ ⇒ quantumAtLeast trivial.
    have h_q_triv : ∀ k : ℤ, Dyadic.quantumAtLeast (F₁.toFormat.exp.map (· - (2 : ℤ)))
        (Dyadic.ofIntZpow 3 k) := by
      intro k; rw [hF_exp]; exact trivial
    rcases hF_b : (F₁.extend 1).toFormat.b with _ | b
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
      have h_ext1_exp : (F₁.extend 1).toFormat.exp = ⊥ := by
        change F₁.toFormat.exp.map (· - ((1 : ℕ+) : ℤ)) = ⊥; rw [hF_exp]; rfl
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
    have h_q_d : Dyadic.quantumAtLeast (F₁.toFormat.exp) d := hd_mem.2.1
    rw [hF_exp] at h_q_d
    have hd_abs_ge : (2 : ℝ)^e ≤ |(d : ℝ)| :=
      Dyadic.abs_ge_two_zpow_of_quantum h_q_d hd_ne
    have h_q_v : ∀ k : ℤ, k ≥ e - 2 →
        Dyadic.quantumAtLeast (F₁.toFormat.exp.map (· - (2 : ℤ))) (Dyadic.ofIntZpow 3 k) := by
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
    have h_ext1_b : (F₁.extend 1).toFormat.b = F₁.toFormat.b := rfl
    rcases hF_b : F₁.toFormat.b with _ | b
    · -- F₁.b = ⊤. Witness 3·2^(e-1).
      refine ⟨Dyadic.ofIntZpow 3 (e - 1), h_mk_member (e - 1) (h_q_v (e - 1) (by omega)) ?_,
        Dyadic.not_precisionAtMost_one_three_zpow (e - 1)⟩
      have h_b_top : (F₁.extend 1).toFormat.b = ⊤ := by rw [h_ext1_b, hF_b]; rfl
      rw [Format.boundAfterNext_top h_b_top]; trivial
    · -- F₁.b = (b : NonNegDyadic). |d| ≤ b. With |d| ≥ 2^e: b ≥ 2^e.
      have hd_le_b_q : |((d : Dyadic) : ℚ)| ≤ ((b.val : Dyadic) : ℚ) := by
        have hb_OK : Format.boundOK F₁.toFormat.b d := hd_mem.2.2
        rw [hF_b] at hb_OK; exact hb_OK
      have hd_le_b : |((d : Dyadic) : ℝ)| ≤ ((b.val : Dyadic) : ℝ) := by
        rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast, ← Rat.cast_abs]
        exact_mod_cast hd_le_b_q
      have hb_ge : (2 : ℝ)^e ≤ ((b.val : Dyadic) : ℝ) := le_trans hd_abs_ge hd_le_b
      have h2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
      have hb_pos : 0 < ((b.val : Dyadic) : ℝ) := lt_of_lt_of_le h2e_pos hb_ge
      have h_ext1_b_coe : (F₁.extend 1).toFormat.b = (b : WithTop NonNegDyadic) := by
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
      have h_ext1_exp : (F₁.extend 1).toFormat.exp = ((e - 1 : ℤ) : WithBot ℤ) := by
        change F₁.toFormat.exp.map (· - ((1 : ℕ+) : ℤ)) = _
        rw [hF_exp]; rfl
      rcases hF_p : F₁.toFormat.p with _ | p
      · -- F₁.p = ⊤ ⇒ (F₁.extend 1).p = ⊤. next b = b + 2^(e-1).
        have h_ext1_p : (F₁.extend 1).toFormat.p = ⊤ := by
          change F₁.toFormat.p.map (· + (1 : ℕ+)) = _; rw [hF_p]; rfl
        have h_next_eq : (F₁.extend 1).toFormat.next b.val
            = b.val + Dyadic.ofIntZpow 1 (e - 1) :=
          Format.next_eq_p_top (F₁.extend 1).toFormat h_ext1_exp h_ext1_p b.val
        rw [h_next_eq, h_v_eq, abs_of_nonneg h_v_pos, h_v_split]
        push_cast
        rw [Dyadic.coe_ofIntZpow]; push_cast
        linarith
      · -- F₁.p = (p : ℕ+) ⇒ (F₁.extend 1).p = p + 1. Step ≥ 2^(e-1).
        have h_ext1_p : (F₁.extend 1).toFormat.p = (((p + 1 : ℕ+)) : WithTop ℕ+) := by
          change F₁.toFormat.p.map (· + (1 : ℕ+)) = _; rw [hF_p]; rfl
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
    (hp_F₂ : ((2 : ℕ+) : WithTop ℕ+) ≤ F₂.toFormat.p)
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

end Mpfx2
