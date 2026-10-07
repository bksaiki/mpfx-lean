import Mpfx.DoubleRounding.Total

/-!
# Double rounding with special values and overflow

The total double-rounding rules as equalities of `rnd`: rounding `v` into `F₂`
and the result into `F₁` gives the direct rounding of `v` into `F₁`, for every
input, special or real, overflowing or not.

The tables must agree across the formats (`SpecialMap.Composes`,
`OverflowMap.Composes`): `F₁`'s rounding of an `F₂` table entry is the
matching `F₁` entry. `rnd_double` reduces each rule to its total form
(`roundsRTZ_RTZ_inBound`, …) and its no-overflow form (`roundsRTZ_RTZ_noOverflow`, …).
-/

namespace Mpfx

/-- `F₁`'s rounding of each entry of `S₂` is the matching entry of `S₁`. -/
def SpecialMap.Composes {F₂ : FiniteFormat} (S₂ : SpecialMap F₂.toFormat)
    {F₁ : FiniteFormat} (S₁ : SpecialMap F₁.toFormat) (O₁ : OverflowMap F₁.toFormat)
    (rm₁ : RoundingMode) : Prop :=
  ∀ t, rnd F₁ S₁ O₁ rm₁ (S₂.map t).toReal = .value (S₁.map t)

/-- `F₁`'s rounding of each entry of `O₂` is the matching entry of `O₁`. -/
def OverflowMap.Composes {F₂ : FiniteFormat} (O₂ : OverflowMap F₂.toFormat)
    {F₁ : FiniteFormat} (S₁ : SpecialMap F₁.toFormat) (O₁ : OverflowMap F₁.toFormat)
    (rm₁ : RoundingMode) : Prop :=
  ∀ negative, rnd F₁ S₁ O₁ rm₁ (O₂.map negative).toReal = .value (O₁.map negative)

/-- An out-of-bound value is nonzero. -/
private theorem ne_zero_of_not_boundOK {F : FiniteFormat} {y : Dyadic}
    (h : ¬ Format.boundOK F.b y) : (y : ℝ) ≠ 0 := fun h0 =>
  h (by rw [eq_zero_of_coe_real_zero h0]; exact Format.boundOK_zero _)

/-- **Double rounding with tables.** A rule's total form (`hP`) and no-overflow
form (`hC`), with composing tables, give `rnd₁ ∘ rnd₂ = rnd₁` on every input. -/
theorem rnd_double {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat} {rm₁ rm₂ : RoundingMode}
    (h₁u : ¬ F₁.IsUndefined rm₁)
    (hP : ∀ x : ℝ, Overflows F₁ rm₁ x ∨
      ∃ z w : Dyadic, RoundsInBound F₂ rm₂ x z ∧ RoundsInBound F₁ rm₁ (z : ℝ) w ∧
        RoundsInBound F₁ rm₁ x w)
    (hC : ∀ (x : ℝ) (z w : Dyadic), RoundsInBound F₂ rm₂ x z →
      RoundsInBound F₁ rm₁ (z : ℝ) w → ¬ Overflows F₁ rm₁ x)
    (hS : S₂.Composes S₁ O₁ rm₁) (hO : O₂.Composes S₁ O₁ rm₁)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic} (hu : rnd F₂ S₂ O₂ rm₂ v = .value u) :
    rnd F₁ S₁ O₁ rm₁ u.toReal = rnd F₁ S₁ O₁ rm₁ v := by
  cases v with
  | special t =>
    rw [rnd_special] at hu
    obtain rfl := RoundResult.value.inj hu
    rw [hS t, rnd_special]
  | finite x =>
    have h₂u : ¬ F₂.IsUndefined rm₂ := fun h => by
      simp only [rnd, dif_pos h] at hu
      exact RoundResult.noConfusion hu
    have hz := rndUnbounded_satisfies F₂ rm₂ x h₂u
    have hy := rndUnbounded_satisfies F₁ rm₁ x h₁u
    generalize rndUnbounded F₂ rm₂ x h₂u = z at hz
    generalize rndUnbounded F₁ rm₁ x h₁u = y at hy
    rw [rnd_finite_of_roundsFinite h₂u hz] at hu
    rw [rnd_finite_of_roundsFinite h₁u hy]
    -- If `F₂` overflows, so does the direct rounding: `hP` would put `z` in bound.
    have hyz : ¬ Format.boundOK F₂.b z → ¬ Format.boundOK F₁.b y := fun hbz hby => by
      rcases hP x with ⟨y', hy', hby'⟩ | ⟨z', -, hz', -, -⟩
      · exact hby' (RoundsFinite.unique h₁u hy hy' ▸ hby)
      · exact hbz (RoundsFinite.unique h₂u hz'.1 hz ▸ hz'.2)
    by_cases hbz : Format.boundOK F₂.b z
    · rw [if_pos hbz] at hu
      obtain rfl := RoundResult.value.inj hu
      have hw := rndUnbounded_satisfies F₁ rm₁ (z : ℝ) h₁u
      generalize rndUnbounded F₁ rm₁ (z : ℝ) h₁u = w at hw
      rw [WithSpecial.toReal_finite, rnd_finite_of_roundsFinite h₁u hw]
      by_cases hbw : Format.boundOK F₁.b w
      · -- Chain in bound: by `hC`, so is the direct rounding, and they agree.
        rcases hP x with hov | ⟨z', w', hz', hw', hy'⟩
        · exact absurd hov (hC x z w ⟨hz, hbz⟩ ⟨hw, hbw⟩)
        · obtain rfl := RoundsFinite.unique h₂u hz'.1 hz
          obtain rfl := RoundsFinite.unique h₁u hw'.1 hw
          obtain rfl := RoundsFinite.unique h₁u hy'.1 hy
          rw [if_pos hbw]
      · -- Chain overflows: so does the direct rounding (else `hP` puts `w` in bound),
        -- and both carry the sign of `x`.
        have hby : ¬ Format.boundOK F₁.b y := fun hby => by
          rcases hP x with ⟨y', hy', hby'⟩ | ⟨z', w', hz', hw', -⟩
          · exact hby' (RoundsFinite.unique h₁u hy hy' ▸ hby)
          · obtain rfl := RoundsFinite.unique h₂u hz'.1 hz
            exact hbw (RoundsFinite.unique h₁u hw'.1 hw ▸ hw'.2)
        have hz0 : (z : ℝ) ≠ 0 := fun h0 => hbw (by
          rw [eq_zero_of_coe_real_zero h0] at hw
          rw [RoundsFinite.eq_zero_of_zero (F := F₁.unbounded) (y := w) (by simpa using hw)]
          exact Format.boundOK_zero _)
        have hsign : decide ((w : ℚ) < 0) = decide ((y : ℚ) < 0) := by
          rw [hw.isFaithfulRound.decide_lt_zero (ne_zero_of_not_boundOK hbw),
            hy.isFaithfulRound.decide_lt_zero (ne_zero_of_not_boundOK hby),
            ← hz.isFaithfulRound.decide_lt_zero hz0]
          exact decide_eq_decide.mpr (by rw [Dyadic.coe_real_eq_ratCast, Rat.cast_lt_zero])
        rw [if_neg hbw, if_neg hby, hsign]
    · -- `F₂` overflows: the overflow tables compose, and the signs match.
      rw [if_neg hbz] at hu
      obtain rfl := RoundResult.value.inj hu
      have hsign : decide ((z : ℚ) < 0) = decide ((y : ℚ) < 0) := by
        rw [hz.isFaithfulRound.decide_lt_zero (ne_zero_of_not_boundOK hbz),
          hy.isFaithfulRound.decide_lt_zero (ne_zero_of_not_boundOK (hyz hbz))]
      rw [hO, if_neg (hyz hbz), hsign]

/-- **rnd-RTZ-RTZ** with tables: chained round-toward-zero is direct
round-toward-zero on every input, special or real, overflowing or not. -/
theorem rndRTZ_RTZ {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial)
    (hS : S₂.Composes S₁ O₁ .toZero) (hO : O₂.Composes S₁ O₁ .toZero)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .toZero v = .value u) :
    rnd F₁ S₁ O₁ .toZero u.toReal = rnd F₁ S₁ O₁ .toZero v :=
  rnd_double (not_isUndefined_toZero F₁) (roundsRTZ_RTZ_inBound hsub)
    (fun _ _ _ hz hw => roundsRTZ_RTZ_noOverflow hsub hnt hz hw) hS hO hu

/-- **rnd-RAZ-RAZ** with tables. -/
theorem rndRAZ_RAZ {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (hS : S₂.Composes S₁ O₁ .awayZero) (hO : O₂.Composes S₁ O₁ .awayZero)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .awayZero v = .value u) :
    rnd F₁ S₁ O₁ .awayZero u.toReal = rnd F₁ S₁ O₁ .awayZero v :=
  rnd_double (not_isUndefined_awayZero F₁) (roundsRAZ_RAZ_inBound hsub)
    (fun _ _ _ hz hw => roundsRAZ_RAZ_noOverflow hz hw) hS hO hu

/-- **rnd-RTO-RTO** with tables. -/
theorem rndRTO_RTO {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p) (h₁u : ¬ F₁.IsUndefined .toOdd)
    (hnt : F₁.toFormat.Nontrivial)
    (hS : S₂.Composes S₁ O₁ .toOdd) (hO : O₂.Composes S₁ O₁ .toOdd)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .toOdd v = .value u) :
    rnd F₁ S₁ O₁ .toOdd u.toReal = rnd F₁ S₁ O₁ .toOdd v :=
  rnd_double h₁u (roundsRTO_RTO_inBound hsub hp_F₂ h₁u)
    (fun _ _ _ hz hw => roundsRTO_RTO_noOverflow hsub hp_F₂ h₁u hnt hz hw) hS hO hu

/-- **rnd-RTO-RTZ** with tables. The IEEE tables do not compose here:
RTO overflows to `±Inf`, which RTZ keeps, while direct RTZ saturates. -/
theorem rndRTO_RTZ {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial)
    (hS : S₂.Composes S₁ O₁ .toZero) (hO : O₂.Composes S₁ O₁ .toZero)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .toOdd v = .value u) :
    rnd F₁ S₁ O₁ .toZero u.toReal = rnd F₁ S₁ O₁ .toZero v :=
  rnd_double (not_isUndefined_toZero F₁) (roundsRTO_RTZ_inBound hsub hnt)
    (fun _ _ _ hz hw => roundsRTO_RTZ_noOverflow hsub hnt hz hw) hS hO hu

/-- **rnd-RTO-RAZ** with tables. -/
theorem rndRTO_RAZ {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial)
    (hS : S₂.Composes S₁ O₁ .awayZero) (hO : O₂.Composes S₁ O₁ .awayZero)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .toOdd v = .value u) :
    rnd F₁ S₁ O₁ .awayZero u.toReal = rnd F₁ S₁ O₁ .awayZero v :=
  rnd_double (not_isUndefined_awayZero F₁) (roundsRTO_RAZ_inBound hsub hnt)
    (fun _ _ _ hz hw => roundsRTO_RAZ_noOverflow hsub hnt hz hw) hS hO hu

/-- **rnd-RTO-RNE** / **rnd-RTO-RNA** with tables. -/
theorem rndRTO_RN {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat} {tb : TieBreak}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
      ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial) (h₁u : ¬ F₁.IsUndefined (.nearest tb))
    (hS : S₂.Composes S₁ O₁ (.nearest tb)) (hO : O₂.Composes S₁ O₁ (.nearest tb))
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .toOdd v = .value u) :
    rnd F₁ S₁ O₁ (.nearest tb) u.toReal = rnd F₁ S₁ O₁ (.nearest tb) v :=
  rnd_double h₁u (roundsRTO_RN_inBound hsub hnt h₁u)
    (fun _ _ _ hz hw => roundsRTO_RN_noOverflow hsub hnt h₁u hz hw) hS hO hu

end Mpfx
