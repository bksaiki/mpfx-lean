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

/-! ## The directed modes

RTN → RTN and RTP → RTP hold under the plain containment `F₁ ⊆ F₂`: each
bound and each extremality clause chains through `z`. Every other chain into
RTZ or RAZ reduces to them by sign: the intermediate `z` is a faithful
rounding of `x`, so it shares `x`'s sign, and on each side RTZ and RAZ agree
with one of the directed modes (`toZero_of_directed`, `awayZero_of_directed`). -/

/-- **rnd-RTN-RTN**. Chained round-toward-`−∞` collapses under `F₁ ⊆ F₂`. -/
theorem roundsRTN_RTN_finite {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toNegative x z) (hw : RoundsFinite F₁ .toNegative (z : ℝ) w) :
    RoundsFinite F₁ .toNegative x w :=
  ⟨hw.1, hw.2.1.trans hz.2.1, fun v hv hvx => hw.2.2 v hv (hz.2.2 v (hsub v hv) hvx)⟩

/-- **rnd-RTP-RTP**. Chained round-toward-`+∞` collapses under `F₁ ⊆ F₂`. -/
theorem roundsRTP_RTP_finite {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toPositive x z) (hw : RoundsFinite F₁ .toPositive (z : ℝ) w) :
    RoundsFinite F₁ .toPositive x w :=
  ⟨hw.1, hz.2.1.trans hw.2.1, fun v hv hxv => hw.2.2 v hv (hz.2.2 v (hsub v hv) hxv)⟩

/-- A chain into RTN and RTP gives the chain into RTZ: RTZ is RTN for `0 ≤ x`
and RTP for `x ≤ 0`, and the faithful intermediate `z` has the sign of `x`. -/
private theorem toZero_of_directed {F₁ F₂ : FiniteFormat} {x : ℝ} {z w : Dyadic}
    (hzx : IsFaithfulRound F₂ x z)
    (hdn : 0 ≤ x → RoundsFinite F₁ .toNegative (z : ℝ) w → RoundsFinite F₁ .toNegative x w)
    (hup : x ≤ 0 → RoundsFinite F₁ .toPositive (z : ℝ) w → RoundsFinite F₁ .toPositive x w)
    (hw : RoundsFinite F₁ .toZero (z : ℝ) w) : RoundsFinite F₁ .toZero x w := by
  rcases le_total 0 x with hx | hx
  · exact (RoundsFinite.toNegative_iff_toZero_of_nonneg F₁ hx w).mp
      (hdn hx ((RoundsFinite.toNegative_iff_toZero_of_nonneg F₁ (hzx.nonneg hx) w).mpr hw))
  · exact (RoundsFinite.toPositive_iff_toZero_of_nonpos F₁ hx w).mp
      (hup hx ((RoundsFinite.toPositive_iff_toZero_of_nonpos F₁ (hzx.nonpos hx) w).mpr hw))

/-- A chain into RTN and RTP gives the chain into RAZ: RAZ is RTP for `0 ≤ x`
and RTN for `x ≤ 0`, and the faithful intermediate `z` has the sign of `x`. -/
private theorem awayZero_of_directed {F₁ F₂ : FiniteFormat} {x : ℝ} {z w : Dyadic}
    (hzx : IsFaithfulRound F₂ x z)
    (hdn : x ≤ 0 → RoundsFinite F₁ .toNegative (z : ℝ) w → RoundsFinite F₁ .toNegative x w)
    (hup : 0 ≤ x → RoundsFinite F₁ .toPositive (z : ℝ) w → RoundsFinite F₁ .toPositive x w)
    (hw : RoundsFinite F₁ .awayZero (z : ℝ) w) : RoundsFinite F₁ .awayZero x w := by
  rcases le_total 0 x with hx | hx
  · exact (RoundsFinite.toPositive_iff_awayZero_of_nonneg F₁ hx w).mp
      (hup hx ((RoundsFinite.toPositive_iff_awayZero_of_nonneg F₁ (hzx.nonneg hx) w).mpr hw))
  · exact (RoundsFinite.toNegative_iff_awayZero_of_nonpos F₁ hx w).mp
      (hdn hx ((RoundsFinite.toNegative_iff_awayZero_of_nonpos F₁ (hzx.nonpos hx) w).mpr hw))

/-- **rnd-RTZ-RTZ**. Chained round-toward-zero collapses under `F₁ ⊆ F₂`. -/
theorem roundsRTZ_RTZ_finite {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toZero x z) (hw : RoundsFinite F₁ .toZero (z : ℝ) w) :
    RoundsFinite F₁ .toZero x w :=
  toZero_of_directed hz.isFaithfulRound
    (fun hx => roundsRTN_RTN_finite hsub
      ((RoundsFinite.toNegative_iff_toZero_of_nonneg F₂ hx z).mpr hz))
    (fun hx => roundsRTP_RTP_finite hsub
      ((RoundsFinite.toPositive_iff_toZero_of_nonpos F₂ hx z).mpr hz))
    hw

/-- **rnd-RAZ-RAZ**. Chained round-away-from-zero collapses under `F₁ ⊆ F₂`. -/
theorem roundsRAZ_RAZ_finite {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .awayZero x z) (hw : RoundsFinite F₁ .awayZero (z : ℝ) w) :
    RoundsFinite F₁ .awayZero x w :=
  awayZero_of_directed hz.isFaithfulRound
    (fun hx => roundsRTN_RTN_finite hsub
      ((RoundsFinite.toNegative_iff_awayZero_of_nonpos F₂ hx z).mpr hz))
    (fun hx => roundsRTP_RTP_finite hsub
      ((RoundsFinite.toPositive_iff_awayZero_of_nonneg F₂ hx z).mpr hz))
    hw

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

/-! ## RTO into the directed modes

An RTO rounding `z` of `x` in the wider `F₂`, then a directed rounding of `z`
in `F₁`, collapses to the directed rounding of `x` in `F₁`. The `_of_extend`
forms take `F₁.extend 1 ⊆ F₂` and `2 ≤ F₂.p`; the plain names take the relaxed
containment that bounds `F₁.extend 1` by `F₁`'s bound after the next value. -/

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
  have hF₂'_nd : F₂'.toFiniteFormat.numDigits (z : ℝ) = F₂.numDigits (z : ℝ) :=
    numDigits_congr (congrArg Format.p hF₂'eq :) (congrArg Format.exp hF₂'eq :) _
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
  have hF₂'_nd : F₂'.toFiniteFormat.numDigits (z : ℝ) = F₂.numDigits (z : ℝ) :=
    numDigits_congr (congrArg Format.p hF₂'eq :) (congrArg Format.exp hF₂'eq :) _
  rw [hF₂'_nd] at h_eq
  -- `numDigits F₁ z + 1 = numDigits F₂ z`, so the strict inequality holds.
  have hlt : F₁.numDigits (z : ℝ) < F₂.numDigits (z : ℝ) := by
    omega
  exact (toOdd_notMem_of_lower_numDigits hF₂'eq hF₂'odd hlt) hzF₁

/-- An RTO rounding to `0` is exact: `0` is never odd. -/
private theorem toOdd_eq_zero_of_eq_zero {F : FiniteFormat} {x : ℝ} {z : Dyadic}
    (hz : RoundsFinite F .toOdd x z) (hz0 : (z : ℝ) = 0) : x = 0 := by
  by_contra hx
  obtain ⟨_, _, hodd⟩ := hz.2.2 (by rw [hz0]; exact hx)
  exact hodd.ne_zero (eq_zero_of_coe_real_zero hz0)

/-- **rnd-RTO-RTN** under `F₁.extend 1 ⊆ F₂` and `2 ≤ F₂.p`, without the relaxed
bound. If `z` is the `F₂` round-down of `x`, every `F₁` value at most `x` is at
most `z`. If `z` is the round-up, a `w` above `x` would be an `F₂` value above
`x`, hence `w = z`; but an inexact `z` is not in `F₁`
(`toOdd_notMem_of_extend_subset`). -/
theorem roundsRTO_RTN_finite_of_extend {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toNegative (z : ℝ) w) :
    RoundsFinite F₁ .toNegative x w := by
  have hsub' : F₁.toFormat ⊆ F₂.toFormat := (Format.self_subset_extend _ 1).trans hsub
  obtain ⟨hwF₁, hwz, hw_max⟩ := hw
  rcases isFaithfulRound_iff_directed.mp hz.isFaithfulRound with
    ⟨-, hzx, hz_max⟩ | ⟨-, hxz, hz_min⟩
  · exact ⟨hwF₁, hwz.trans hzx, fun v hv hvx => hw_max v hv (hz_max v (hsub' v hv) hvx)⟩
  · refine ⟨hwF₁, ?_, fun v hv hvx => hw_max v hv (hvx.trans hxz)⟩
    by_contra hxw
    push Not at hxw
    have hwz' : (w : ℝ) = z := le_antisymm hwz (hz_min w (hsub' w hwF₁) hxw.le)
    have hzw : z = w := (Dyadic.coe_real_inj z w).mp hwz'.symm
    exact toOdd_notMem_of_extend_subset hsub hp_F₂ hz (hxw.trans_eq hwz').ne (hzw ▸ hwF₁)

/-- **rnd-RTO-RTP** under `F₁.extend 1 ⊆ F₂` and `2 ≤ F₂.p`, without the relaxed
bound. The mirror of `roundsRTO_RTN_finite_of_extend`. -/
theorem roundsRTO_RTP_finite_of_extend {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toPositive (z : ℝ) w) :
    RoundsFinite F₁ .toPositive x w := by
  have hsub' : F₁.toFormat ⊆ F₂.toFormat := (Format.self_subset_extend _ 1).trans hsub
  obtain ⟨hwF₁, hzw, hw_min⟩ := hw
  rcases isFaithfulRound_iff_directed.mp hz.isFaithfulRound with
    ⟨-, hzx, hz_max⟩ | ⟨-, hxz, hz_min⟩
  · refine ⟨hwF₁, ?_, fun v hv hxv => hw_min v hv (hzx.trans hxv)⟩
    by_contra hwx
    push Not at hwx
    have hwz' : (w : ℝ) = z := le_antisymm (hz_max w (hsub' w hwF₁) hwx.le) hzw
    have hzw' : z = w := (Dyadic.coe_real_inj z w).mp hwz'.symm
    exact toOdd_notMem_of_extend_subset hsub hp_F₂ hz (hwz'.symm.trans_lt hwx).ne'
      (hzw' ▸ hwF₁)
  · exact ⟨hwF₁, hxz.trans hzw, fun v hv hxv => hw_min v hv (hz_min v (hsub' v hv) hxv)⟩

/-- RTO then RTN into a trivial `F₁ = {0}`: `w = 0 ≤ z`, and an RTO rounding is
`0` only for `x = 0`, so `0 ≤ x`. -/
private theorem RoundsFinite.toNegative_of_trivial {F₁ F₂ : FiniteFormat}
    (hF₁_triv : ∀ d : Dyadic, d ∈ F₁ → (d : ℝ) = 0)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toNegative (z : ℝ) w) :
    RoundsFinite F₁ .toNegative x w := by
  have hw0 := hF₁_triv w hw.1
  refine ⟨hw.1, ?_, fun v hv _ => by rw [hF₁_triv v hv, hw0]⟩
  rw [hw0]
  by_contra hx
  push Not at hx
  have hz0 : (z : ℝ) = 0 :=
    le_antisymm (hz.isFaithfulRound.nonpos hx.le) (by linarith [hw.2.1])
  exact hx.ne (toOdd_eq_zero_of_eq_zero hz hz0)

/-- The mirror of `RoundsFinite.toNegative_of_trivial`. -/
private theorem RoundsFinite.toPositive_of_trivial {F₁ F₂ : FiniteFormat}
    (hF₁_triv : ∀ d : Dyadic, d ∈ F₁ → (d : ℝ) = 0)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toPositive (z : ℝ) w) :
    RoundsFinite F₁ .toPositive x w := by
  have hw0 := hF₁_triv w hw.1
  refine ⟨hw.1, ?_, fun v hv _ => by rw [hF₁_triv v hv, hw0]⟩
  rw [hw0]
  by_contra hx
  push Not at hx
  have hz0 : (z : ℝ) = 0 :=
    le_antisymm (by linarith [hw.2.1]) (hz.isFaithfulRound.nonneg hx.le)
  exact hx.ne' (toOdd_eq_zero_of_eq_zero hz hz0)

/-- **rnd-RTO-RTN** under the relaxed containment; `2 ≤ F₂.p` follows unless `F₁`
is trivial. -/
theorem roundsRTO_RTN_finite {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toNegative (z : ℝ) w) :
    RoundsFinite F₁ .toNegative x w := by
  rcases two_le_p_or_trivial_of_extend_one_withBound_subset hsub with hp_F₂ | hF₁_triv
  · exact roundsRTO_RTN_finite_of_extend (extend_one_subset_of_withBound_subset hsub) hp_F₂
      hz hw
  · exact RoundsFinite.toNegative_of_trivial hF₁_triv hz hw

/-- **rnd-RTO-RTP** under the relaxed containment; `2 ≤ F₂.p` follows unless `F₁`
is trivial. -/
theorem roundsRTO_RTP_finite {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toPositive (z : ℝ) w) :
    RoundsFinite F₁ .toPositive x w := by
  rcases two_le_p_or_trivial_of_extend_one_withBound_subset hsub with hp_F₂ | hF₁_triv
  · exact roundsRTO_RTP_finite_of_extend (extend_one_subset_of_withBound_subset hsub) hp_F₂
      hz hw
  · exact RoundsFinite.toPositive_of_trivial hF₁_triv hz hw

/-- **rnd-RTO-RTZ** under `F₁.extend 1 ⊆ F₂` and `2 ≤ F₂.p`, without the relaxed
bound. -/
theorem roundsRTO_RTZ_finite_of_extend {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toZero (z : ℝ) w) :
    RoundsFinite F₁ .toZero x w :=
  toZero_of_directed hz.isFaithfulRound
    (fun _ => roundsRTO_RTN_finite_of_extend hsub hp_F₂ hz)
    (fun _ => roundsRTO_RTP_finite_of_extend hsub hp_F₂ hz) hw

/-- **rnd-RTO-RTZ** under the relaxed containment. -/
theorem roundsRTO_RTZ_finite {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toZero (z : ℝ) w) :
    RoundsFinite F₁ .toZero x w :=
  toZero_of_directed hz.isFaithfulRound
    (fun _ => roundsRTO_RTN_finite hsub hz) (fun _ => roundsRTO_RTP_finite hsub hz) hw

/-- **rnd-RTO-RAZ** under `F₁.extend 1 ⊆ F₂` and `2 ≤ F₂.p`, without the relaxed
bound. -/
theorem roundsRTO_RAZ_finite_of_extend {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .awayZero (z : ℝ) w) :
    RoundsFinite F₁ .awayZero x w :=
  awayZero_of_directed hz.isFaithfulRound
    (fun _ => roundsRTO_RTN_finite_of_extend hsub hp_F₂ hz)
    (fun _ => roundsRTO_RTP_finite_of_extend hsub hp_F₂ hz) hw

/-- **rnd-RTO-RAZ** under the relaxed containment. -/
theorem roundsRTO_RAZ_finite {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .awayZero (z : ℝ) w) :
    RoundsFinite F₁ .awayZero x w :=
  awayZero_of_directed hz.isFaithfulRound
    (fun _ => roundsRTO_RTN_finite hsub hz) (fun _ => roundsRTO_RTP_finite hsub hz) hw

end Mpfx
