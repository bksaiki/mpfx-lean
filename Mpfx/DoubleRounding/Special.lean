import Mpfx.DoubleRounding.Total
import Mpfx.Rounding.Special

/-!
# Double rounding with special values and overflow

The total double-rounding rules as equalities of `rnd`: rounding `v` into `F₂`
and the result into `F₁` gives the direct rounding of `v` into `F₁`, for every
input, special or real, overflowing or not.

Three conditions on the tables: they compose (`SpecialMap.Composes`,
`OverflowMap.Composes`: `F₁`'s rounding of an `F₂` entry is the matching `F₁`
entry), and where exactly one side overflows, `F₁`'s overflow entry gives the
other side's value (`OverflowAgrees`). The rules (`rndRTZ_RTZ`, …) take the
plain containment and `OverflowAgrees`; the `…_of_bound` forms take the
paper's relaxed containment, under which `OverflowAgrees` holds for any tables
(`OverflowAgrees.of_bound`).

The IEEE tables compose for every rule but RTO → RTZ: exact specials always
(`SpecialMap.exact_composes`), `±Inf` overflow tables pairwise
(`OverflowMap.composes_of_inf`), and the RTZ tables under the plain
containment (`OverflowMap.ieee_toZero_composes`). Saturating tables compose and
satisfy `OverflowAgrees` for any modes under the plain containment
(`OverflowMap.saturate_composes`, `OverflowAgrees.of_saturate`).
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

/-! ### Composing the standard tables -/

/-- Exact specials compose with any `F₁` table: `F₁` rounds a special by its
own table. -/
theorem SpecialMap.exact_composes {F₂ : FiniteFormat} (h₂ : ∀ s, s ∈ F₂.specials)
    {F₁ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat} {O₁ : OverflowMap F₁.toFormat}
    {rm₁ : RoundingMode} : (SpecialMap.exact F₂.toFormat h₂).Composes S₁ O₁ rm₁ :=
  fun _ => rnd_special _ _ _ _ _

/-- Overflow tables that both send overflow to `±Inf` compose when `F₁` keeps
infinities exact. -/
theorem OverflowMap.composes_of_inf {F₂ F₁ : FiniteFormat} {O₂ : OverflowMap F₂.toFormat}
    {S₁ : SpecialMap F₁.toFormat} {O₁ : OverflowMap F₁.toFormat} {rm₁ : RoundingMode}
    (h₂ : ∀ s, O₂.map s = .special (.inf s)) (hS : ∀ s, S₁.map (.inf s) = .special (.inf s))
    (h₁ : ∀ s, O₁.map s = .special (.inf s)) : O₂.Composes S₁ O₁ rm₁ := fun s => by
  rw [h₂, WithSpecial.toReal_special, rnd_special, hS, h₁]

@[simp] theorem SpecialMap.exact_map (F : Format) (h : ∀ s, s ∈ F.specials) (s : Special) :
    (SpecialMap.exact F h).map s = .special s := rfl

theorem OverflowMap.ieee_map_awayZero (F : FiniteFormat) {hb hinf} (s : Bool) :
    (OverflowMap.ieee F .awayZero hb hinf).map s = .special (.inf s) := rfl

theorem OverflowMap.ieee_map_toOdd (F : FiniteFormat) {hb hinf} (s : Bool) :
    (OverflowMap.ieee F .toOdd hb hinf).map s = .special (.inf s) := rfl

theorem OverflowMap.ieee_map_nearest (F : FiniteFormat) (tb : TieBreak) {hb hinf} (s : Bool) :
    (OverflowMap.ieee F (.nearest tb) hb hinf).map s = .special (.inf s) := rfl

/-- An out-of-bound value is nonzero. -/
private theorem ne_zero_of_not_boundOK {F : FiniteFormat} {y : Dyadic}
    (h : ¬ Format.boundOK F.b y) : (y : ℝ) ≠ 0 := fun h0 =>
  h (by rw [eq_zero_of_coe_real_zero h0]; exact Format.boundOK_zero _)

/-- A nonzero chained rounding carries the sign of `x`. -/
private theorem decide_lt_zero_of_chain {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode}
    {x : ℝ} {z w : Dyadic} (hz : RoundsFinite F₂.unbounded rm₂ x z)
    (hw : RoundsFinite F₁.unbounded rm₁ (z : ℝ) w) (hw0 : (w : ℝ) ≠ 0) :
    decide ((w : ℚ) < 0) = decide (x < 0) := by
  have hz0 : (z : ℝ) ≠ 0 := fun h0 => hw0 (by
    rw [eq_zero_of_coe_real_zero h0, Dyadic.coe_real_zero] at hw
    rw [RoundsFinite.eq_zero_of_zero hw, Dyadic.coe_real_zero])
  rw [hw.isFaithfulRound.decide_lt_zero hw0, ← hz.isFaithfulRound.decide_lt_zero hz0]
  exact decide_eq_decide.mpr (by rw [Dyadic.coe_real_eq_ratCast, Rat.cast_lt_zero])

/-- Where exactly one side of a double rounding overflows, `F₁`'s overflow
table gives the other side's value. `s = decide (x < 0)` is the overflow sign. -/
structure OverflowAgrees (F₁ : FiniteFormat) (S₁ : SpecialMap F₁.toFormat)
    (O₁ : OverflowMap F₁.toFormat) (rm₁ : RoundingMode)
    (F₂ : FiniteFormat) (O₂ : OverflowMap F₂.toFormat) (rm₂ : RoundingMode) : Prop where
  /-- The chain stays in bound and the direct rounding overflows. -/
  direct : ∀ (x : ℝ) (z w : Dyadic), RoundsInBound F₂ rm₂ x z →
    RoundsInBound F₁ rm₁ (z : ℝ) w → Overflows F₁ rm₁ x →
    O₁.map (decide (x < 0)) = .finite w
  /-- `F₂` stays in bound, the chain overflows, the direct rounding does not. -/
  chain : ∀ (x : ℝ) (z y : Dyadic), RoundsInBound F₂ rm₂ x z → Overflows F₁ rm₁ (z : ℝ) →
    RoundsInBound F₁ rm₁ x y → O₁.map (decide (x < 0)) = .finite y
  /-- `F₂` overflows and the direct rounding does not. -/
  inner : ∀ (x : ℝ) (y : Dyadic), Overflows F₂ rm₂ x → RoundsInBound F₁ rm₁ x y →
    rnd F₁ S₁ O₁ rm₁ (O₂.map (decide (x < 0))).toReal = .value (.finite y)

/-- **Double rounding with tables.** Agreement in bound (`hA`), overflow
agreement where one side overflows (`hov`), and composing tables give
`rnd₁ ∘ rnd₂ = rnd₁` on every input. -/
theorem rnd_double {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat} {rm₁ rm₂ : RoundingMode}
    (h₁u : ¬ F₁.IsUndefined rm₁)
    (hA : ∀ (x : ℝ) (z w y : Dyadic), RoundsInBound F₂ rm₂ x z →
      RoundsInBound F₁ rm₁ (z : ℝ) w → RoundsInBound F₁ rm₁ x y → w = y)
    (hov : OverflowAgrees F₁ S₁ O₁ rm₁ F₂ O₂ rm₂)
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
    -- An overflowing rounding of `x` carries the sign of `x`.
    have hsgn : ∀ {F : FiniteFormat} {rm : RoundingMode} {d : Dyadic},
        RoundsFinite F.unbounded rm x d → ¬ Format.boundOK F.b d →
        decide ((d : ℚ) < 0) = decide (x < 0) := fun hd hbd =>
      hd.isFaithfulRound.decide_lt_zero (ne_zero_of_not_boundOK hbd)
    by_cases hbz : Format.boundOK F₂.b z
    · rw [if_pos hbz] at hu
      obtain rfl := RoundResult.value.inj hu
      have hw := rndUnbounded_satisfies F₁ rm₁ (z : ℝ) h₁u
      generalize rndUnbounded F₁ rm₁ (z : ℝ) h₁u = w at hw
      rw [WithSpecial.toReal_finite, rnd_finite_of_roundsFinite h₁u hw]
      by_cases hbw : Format.boundOK F₁.b w
      · rw [if_pos hbw]
        by_cases hby : Format.boundOK F₁.b y
        · rw [if_pos hby, hA x z w y ⟨hz, hbz⟩ ⟨hw, hbw⟩ ⟨hy, hby⟩]
        · rw [if_neg hby, hsgn hy hby, hov.direct x z w ⟨hz, hbz⟩ ⟨hw, hbw⟩ ⟨y, hy, hby⟩]
      · rw [if_neg hbw, decide_lt_zero_of_chain hz hw (ne_zero_of_not_boundOK hbw)]
        by_cases hby : Format.boundOK F₁.b y
        · rw [if_pos hby, hov.chain x z y ⟨hz, hbz⟩ ⟨w, hw, hbw⟩ ⟨hy, hby⟩]
        · rw [if_neg hby, hsgn hy hby]
    · rw [if_neg hbz] at hu
      obtain rfl := RoundResult.value.inj hu
      rw [hsgn hz hbz]
      by_cases hby : Format.boundOK F₁.b y
      · rw [if_pos hby, hov.inner x y ⟨z, hz, hbz⟩ ⟨hy, hby⟩]
      · rw [hO, if_neg hby, hsgn hy hby]

/-- A rule's total form (`hP`) and no-overflow form (`hC`) make every field of
`OverflowAgrees` vacuous, for any tables. -/
theorem OverflowAgrees.of_bound {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {O₂ : OverflowMap F₂.toFormat} {rm₁ rm₂ : RoundingMode}
    (h₁u : ¬ F₁.IsUndefined rm₁) (h₂u : ¬ F₂.IsUndefined rm₂)
    (hP : ∀ x : ℝ, Overflows F₁ rm₁ x ∨
      ∃ z w : Dyadic, RoundsInBound F₂ rm₂ x z ∧ RoundsInBound F₁ rm₁ (z : ℝ) w ∧
        RoundsInBound F₁ rm₁ x w)
    (hC : ∀ (x : ℝ) (z w : Dyadic), RoundsInBound F₂ rm₂ x z →
      RoundsInBound F₁ rm₁ (z : ℝ) w → ¬ Overflows F₁ rm₁ x) :
    OverflowAgrees F₁ S₁ O₁ rm₁ F₂ O₂ rm₂ where
  direct x z w hz hw hov := absurd hov (hC x z w hz hw)
  chain x z y hz hov hy := by
    obtain ⟨w, hw, hbw⟩ := hov
    rcases hP x with ⟨y', hy', hby'⟩ | ⟨z', w', hz', hw', -⟩
    · exact absurd (RoundsFinite.unique h₁u hy.1 hy' ▸ hy.2) hby'
    · obtain rfl := RoundsFinite.unique h₂u hz'.1 hz.1
      exact absurd (RoundsFinite.unique h₁u hw'.1 hw ▸ hw'.2) hbw
  inner x y hov hy := by
    obtain ⟨z, hz, hbz⟩ := hov
    rcases hP x with ⟨y', hy', hby'⟩ | ⟨z', -, hz', -, -⟩
    · exact absurd (RoundsFinite.unique h₁u hy.1 hy' ▸ hy.2) hby'
    · exact absurd (RoundsFinite.unique h₂u hz'.1 hz ▸ hz'.2) hbz

/-- The plain containment, from the relaxed containment. -/
private theorem subset_of_withBound_boundAfterNext_subset {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat) :
    F₁.toFormat ⊆ F₂.toFormat :=
  Format.subset_of_mem hsub.specials fun d hd =>
    hsub d ⟨hd.1, hd.2.1, boundOK_boundAfterNext_of_boundOK hd.2.2⟩

/-! ### The rules -/

/-- **rnd-RTZ-RTZ** with tables: chained round-toward-zero is direct
round-toward-zero on every input, special or real, overflowing or not. -/
theorem rndRTZ_RTZ {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (hov : OverflowAgrees F₁ S₁ O₁ .toZero F₂ O₂ .toZero)
    (hS : S₂.Composes S₁ O₁ .toZero) (hO : O₂.Composes S₁ O₁ .toZero)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .toZero v = .value u) :
    rnd F₁ S₁ O₁ .toZero u.toReal = rnd F₁ S₁ O₁ .toZero v :=
  rnd_double (not_isUndefined_toZero F₁) (fun _ _ _ _ => roundsRTZ_RTZ_agree hsub) hov hS hO hu

/-- **rnd-RTZ-RTZ** under the relaxed containment, for any tables. -/
theorem rndRTZ_RTZ_of_bound {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial)
    (hS : S₂.Composes S₁ O₁ .toZero) (hO : O₂.Composes S₁ O₁ .toZero)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .toZero v = .value u) :
    rnd F₁ S₁ O₁ .toZero u.toReal = rnd F₁ S₁ O₁ .toZero v :=
  rndRTZ_RTZ (subset_of_withBound_boundAfterNext_subset hsub)
    (.of_bound (not_isUndefined_toZero F₁) (not_isUndefined_toZero F₂)
      (roundsRTZ_RTZ_inBound hsub) fun _ _ _ hz hw => roundsRTZ_RTZ_noOverflow hsub hnt hz hw)
    hS hO hu

/-- **rnd-RAZ-RAZ** with tables. -/
theorem rndRAZ_RAZ {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (hov : OverflowAgrees F₁ S₁ O₁ .awayZero F₂ O₂ .awayZero)
    (hS : S₂.Composes S₁ O₁ .awayZero) (hO : O₂.Composes S₁ O₁ .awayZero)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .awayZero v = .value u) :
    rnd F₁ S₁ O₁ .awayZero u.toReal = rnd F₁ S₁ O₁ .awayZero v :=
  rnd_double (not_isUndefined_awayZero F₁) (fun _ _ _ _ => roundsRAZ_RAZ_agree hsub) hov
    hS hO hu

/-- **rnd-RAZ-RAZ** for any tables: `F₂` never overflows where `F₁` does not. -/
theorem rndRAZ_RAZ_of_bound {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (hS : S₂.Composes S₁ O₁ .awayZero) (hO : O₂.Composes S₁ O₁ .awayZero)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .awayZero v = .value u) :
    rnd F₁ S₁ O₁ .awayZero u.toReal = rnd F₁ S₁ O₁ .awayZero v :=
  rndRAZ_RAZ hsub
    (.of_bound (not_isUndefined_awayZero F₁) (not_isUndefined_awayZero F₂)
      (roundsRAZ_RAZ_inBound hsub) fun _ _ _ hz hw => roundsRAZ_RAZ_noOverflow hz hw)
    hS hO hu

/-- **rnd-RTO-RTO** with tables. -/
theorem rndRTO_RTO {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p) (h₁u : ¬ F₁.IsUndefined .toOdd)
    (hov : OverflowAgrees F₁ S₁ O₁ .toOdd F₂ O₂ .toOdd)
    (hS : S₂.Composes S₁ O₁ .toOdd) (hO : O₂.Composes S₁ O₁ .toOdd)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .toOdd v = .value u) :
    rnd F₁ S₁ O₁ .toOdd u.toReal = rnd F₁ S₁ O₁ .toOdd v :=
  rnd_double h₁u (fun _ _ _ _ => roundsRTO_RTO_agree hsub hp_F₂ h₁u) hov hS hO hu

/-- **rnd-RTO-RTO** under the relaxed containment, for any tables. -/
theorem rndRTO_RTO_of_bound {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p) (h₁u : ¬ F₁.IsUndefined .toOdd)
    (hnt : F₁.toFormat.Nontrivial)
    (hS : S₂.Composes S₁ O₁ .toOdd) (hO : O₂.Composes S₁ O₁ .toOdd)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .toOdd v = .value u) :
    rnd F₁ S₁ O₁ .toOdd u.toReal = rnd F₁ S₁ O₁ .toOdd v :=
  rndRTO_RTO (subset_of_withBound_boundAfterNext_subset hsub) hp_F₂ h₁u
    (.of_bound h₁u (not_isUndefined_of_two_le_p hp_F₂) (roundsRTO_RTO_inBound hsub hp_F₂ h₁u)
      fun _ _ _ hz hw => roundsRTO_RTO_noOverflow hsub hp_F₂ h₁u hnt hz hw)
    hS hO hu

/-- **rnd-RTO-RTZ** with tables. The IEEE tables do not compose here:
RTO overflows to `±Inf`, which RTZ keeps, while direct RTZ saturates. -/
theorem rndRTO_RTZ {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat}
    (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat) (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    (hov : OverflowAgrees F₁ S₁ O₁ .toZero F₂ O₂ .toOdd)
    (hS : S₂.Composes S₁ O₁ .toZero) (hO : O₂.Composes S₁ O₁ .toZero)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .toOdd v = .value u) :
    rnd F₁ S₁ O₁ .toZero u.toReal = rnd F₁ S₁ O₁ .toZero v :=
  rnd_double (not_isUndefined_toZero F₁) (fun _ _ _ _ => roundsRTO_RTZ_agree hsub hp_F₂) hov
    hS hO hu

/-- **rnd-RTO-RTZ** under the relaxed containment, for any tables. -/
theorem rndRTO_RTZ_of_bound {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial)
    (hS : S₂.Composes S₁ O₁ .toZero) (hO : O₂.Composes S₁ O₁ .toZero)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .toOdd v = .value u) :
    rnd F₁ S₁ O₁ .toZero u.toReal = rnd F₁ S₁ O₁ .toZero v :=
  have hp_F₂ := two_le_p_of_nontrivial hsub hnt
  rndRTO_RTZ (extend_one_subset_of_withBound_subset hsub) hp_F₂
    (.of_bound (not_isUndefined_toZero F₁) (not_isUndefined_of_two_le_p hp_F₂)
      (roundsRTO_RTZ_inBound hsub hnt) fun _ _ _ hz hw => roundsRTO_RTZ_noOverflow hsub hnt hz hw)
    hS hO hu

/-- **rnd-RTO-RAZ** with tables. -/
theorem rndRTO_RAZ {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat}
    (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat) (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    (hov : OverflowAgrees F₁ S₁ O₁ .awayZero F₂ O₂ .toOdd)
    (hS : S₂.Composes S₁ O₁ .awayZero) (hO : O₂.Composes S₁ O₁ .awayZero)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .toOdd v = .value u) :
    rnd F₁ S₁ O₁ .awayZero u.toReal = rnd F₁ S₁ O₁ .awayZero v :=
  rnd_double (not_isUndefined_awayZero F₁) (fun _ _ _ _ => roundsRTO_RAZ_agree hsub hp_F₂) hov
    hS hO hu

/-- **rnd-RTO-RAZ** under the relaxed containment, for any tables. -/
theorem rndRTO_RAZ_of_bound {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial)
    (hS : S₂.Composes S₁ O₁ .awayZero) (hO : O₂.Composes S₁ O₁ .awayZero)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .toOdd v = .value u) :
    rnd F₁ S₁ O₁ .awayZero u.toReal = rnd F₁ S₁ O₁ .awayZero v :=
  have hp_F₂ := two_le_p_of_nontrivial hsub hnt
  rndRTO_RAZ (extend_one_subset_of_withBound_subset hsub) hp_F₂
    (.of_bound (not_isUndefined_awayZero F₁) (not_isUndefined_of_two_le_p hp_F₂)
      (roundsRTO_RAZ_inBound hsub hnt) fun _ _ _ hz hw => roundsRTO_RAZ_noOverflow hsub hnt hz hw)
    hS hO hu

/-- **rnd-RTO-RNE** / **rnd-RTO-RNA** with tables. -/
theorem rndRTO_RN {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat} {tb : TieBreak}
    (hsub : (F₁.extend 2).toFormat ⊆ F₂.toFormat) (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    (h₁u : ¬ F₁.IsUndefined (.nearest tb))
    (hov : OverflowAgrees F₁ S₁ O₁ (.nearest tb) F₂ O₂ .toOdd)
    (hS : S₂.Composes S₁ O₁ (.nearest tb)) (hO : O₂.Composes S₁ O₁ (.nearest tb))
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .toOdd v = .value u) :
    rnd F₁ S₁ O₁ (.nearest tb) u.toReal = rnd F₁ S₁ O₁ (.nearest tb) v :=
  rnd_double h₁u (fun _ _ _ _ => roundsRTO_RN_agree hsub hp_F₂ h₁u) hov hS hO hu

/-- **rnd-RTO-RNE** / **rnd-RTO-RNA** under the relaxed containment, for any tables. -/
theorem rndRTO_RN_of_bound {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat}
    {O₂ : OverflowMap F₂.toFormat} {tb : TieBreak}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
      ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial) (h₁u : ¬ F₁.IsUndefined (.nearest tb))
    (hS : S₂.Composes S₁ O₁ (.nearest tb)) (hO : O₂.Composes S₁ O₁ (.nearest tb))
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ S₂ O₂ .toOdd v = .value u) :
    rnd F₁ S₁ O₁ (.nearest tb) u.toReal = rnd F₁ S₁ O₁ (.nearest tb) v :=
  have hp_F₂ := two_le_p_of_nontrivial_extend_two hsub hnt
  rndRTO_RN (extend_two_subset_of_withBound_subset hsub) hp_F₂ h₁u
    (.of_bound h₁u (not_isUndefined_of_two_le_p hp_F₂) (roundsRTO_RN_inBound hsub hnt h₁u)
      fun _ _ _ hz hw => roundsRTO_RN_noOverflow hsub hnt h₁u hz hw)
    hS hO hu

/-! ### Saturating tables

Saturating overflow tables on both sides satisfy `OverflowAgrees` and compose,
for any pair of modes, under the plain containment: whichever side overflows
lands on `±maxFinite₁`, which is also where any in-bound rounding of an
input of magnitude at least `maxFinite₁` sits. -/

/-- An input that overflows is at least `maxFinite` in magnitude. -/
private theorem maxFinite_le_abs_of_overflows {F : FiniteFormat} (hb : F.b ≠ ⊤)
    {rm : RoundingMode} {x : ℝ} (h : Overflows F rm x) : (F.maxFinite hb : ℝ) ≤ |x| := by
  obtain ⟨y, hy, hby⟩ := h
  have hM := F.maxFinite_mem hb
  refine not_lt.mp fun hlt => hby (boundOK_of_abs_le ?_ hM.2.2)
  rw [abs_of_nonneg (F.maxFinite_nonneg hb)]
  exact abs_faithful_le_of_le (mem_unbounded_of_mem hM) hlt.le hy.isFaithfulRound

/-- An in-bound rounding of an input of magnitude at least `maxFinite` is the
saturated value of the input's sign. -/
private theorem saturated_eq_of_roundsInBound {F : FiniteFormat} (hb : F.b ≠ ⊤)
    {rm : RoundingMode} {x : ℝ} {y : Dyadic} (hx : (F.maxFinite hb : ℝ) ≤ |x|)
    (hy : RoundsInBound F rm x y) : F.saturated hb (decide (x < 0)) = .finite y :=
  F.saturated_eq_finite hb (le_antisymm
    (F.abs_le_maxFinite hb (mem_of_mem_unbounded_of_boundOK hy.1.1 hy.2))
    (le_abs_faithful_of_le (mem_unbounded_of_mem (F.maxFinite_mem hb))
      (F.maxFinite_nonneg hb) hx hy.1.isFaithfulRound))
    hy.1.isFaithfulRound.decide_lt_zero

/-- With a saturating table, every `|x| ≥ maxFinite` rounds to `±maxFinite`
with the sign of `x`, overflowing or not. -/
private theorem rnd_saturate {F : FiniteFormat} (hb : F.b ≠ ⊤) {rm : RoundingMode}
    (hu : ¬ F.IsUndefined rm) (S : SpecialMap F.toFormat) {x : ℝ} {s : Bool}
    (hx : (F.maxFinite hb : ℝ) ≤ |x|) (hs : x ≠ 0 → decide (x < 0) = s) :
    rnd F S (OverflowMap.saturate F hb) rm (.finite x) = .value (F.saturated hb s) := by
  have hr := rndUnbounded_satisfies F rm x hu
  generalize rndUnbounded F rm x hu = r at hr
  rw [rnd_finite_of_roundsFinite hu hr]
  have hsign : (r : ℝ) ≠ 0 → decide ((r : ℚ) < 0) = s := fun hr0 => by
    rw [hr.isFaithfulRound.decide_lt_zero hr0]
    refine hs fun hx0 => hr0 ?_
    rw [hx0] at hr
    rw [RoundsFinite.eq_zero_of_zero hr, Dyadic.coe_real_zero]
  split_ifs with hbr
  · rw [F.saturated_eq_finite hb (le_antisymm
      (F.abs_le_maxFinite hb (mem_of_mem_unbounded_of_boundOK hr.1 hbr))
      (le_abs_faithful_of_le (mem_unbounded_of_mem (F.maxFinite_mem hb)) (F.maxFinite_nonneg hb)
        hx hr.isFaithfulRound)) hsign]
  · rw [hsign (ne_zero_of_not_boundOK hbr)]
    rfl

/-- Saturating tables compose under the plain containment: `F₁` rounds
`±maxFinite₂` onto `±maxFinite₁`. -/
theorem OverflowMap.saturate_composes {F₁ F₂ : FiniteFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat) (hb₁ : F₁.b ≠ ⊤) (hb₂ : F₂.b ≠ ⊤)
    {rm₁ : RoundingMode} (h₁u : ¬ F₁.IsUndefined rm₁) {S₁ : SpecialMap F₁.toFormat} :
    (OverflowMap.saturate F₂ hb₂).Composes S₁ (OverflowMap.saturate F₁ hb₁) rm₁ := by
  have hM := F₂.maxFinite_nonneg hb₂
  have hle : (F₁.maxFinite hb₁ : ℝ) ≤ (F₂.maxFinite hb₂ : ℝ) :=
    F₂.le_maxFinite hb₂ (hsub _ (F₁.maxFinite_mem hb₁))
  intro s
  cases s
  · change rnd F₁ S₁ _ rm₁ (.finite ((F₂.maxFinite hb₂ : Dyadic) : ℝ)) = _
    exact rnd_saturate hb₁ h₁u S₁ (by rwa [abs_of_nonneg hM])
      fun _ => decide_eq_false (not_lt.mpr hM)
  · change rnd F₁ S₁ _ rm₁ (.finite ((-F₂.maxFinite hb₂ : Dyadic) : ℝ)) = _
    rw [Dyadic.coe_real_neg]
    exact rnd_saturate hb₁ h₁u S₁ (by rwa [abs_neg, abs_of_nonneg hM])
      fun h0 => decide_eq_true (lt_of_le_of_ne (by linarith) h0)

/-- The IEEE RTZ tables compose under the plain containment. -/
theorem OverflowMap.ieee_toZero_composes {F₁ F₂ : FiniteFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat) (hb₁ : F₁.b ≠ ⊤) (hb₂ : F₂.b ≠ ⊤)
    (hinf₁ : ∀ s, Special.inf s ∈ F₁.specials) (hinf₂ : ∀ s, Special.inf s ∈ F₂.specials)
    {S₁ : SpecialMap F₁.toFormat} :
    (OverflowMap.ieee F₂ .toZero hb₂ hinf₂).Composes S₁
      (OverflowMap.ieee F₁ .toZero hb₁ hinf₁) .toZero :=
  OverflowMap.saturate_composes hsub hb₁ hb₂ (not_isUndefined_toZero F₁)

/-- Saturating tables agree under the plain containment, for any modes. -/
theorem OverflowAgrees.of_saturate {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
    {rm₁ rm₂ : RoundingMode} (hsub : F₁.toFormat ⊆ F₂.toFormat) (hb₁ : F₁.b ≠ ⊤)
    (hb₂ : F₂.b ≠ ⊤) (h₁u : ¬ F₁.IsUndefined rm₁) :
    OverflowAgrees F₁ S₁ (OverflowMap.saturate F₁ hb₁) rm₁
      F₂ (OverflowMap.saturate F₂ hb₂) rm₂ where
  direct x z w hz hw hov := by
    have hM := F₁.maxFinite_mem hb₁
    have hzM := le_abs_faithful_of_le (mem_unbounded_of_mem (hsub _ hM))
      (F₁.maxFinite_nonneg hb₁) (maxFinite_le_abs_of_overflows hb₁ hov) hz.1.isFaithfulRound
    exact F₁.saturated_eq_finite hb₁ (le_antisymm
      (F₁.abs_le_maxFinite hb₁ (mem_of_mem_unbounded_of_boundOK hw.1.1 hw.2))
      (le_abs_faithful_of_le (mem_unbounded_of_mem hM) (F₁.maxFinite_nonneg hb₁) hzM
        hw.1.isFaithfulRound))
      (decide_lt_zero_of_chain hz.1 hw.1)
  chain x z y hz hov hy := by
    -- `|x| < maxFinite₁` would pin the chain at or below `maxFinite₁`, in bound.
    obtain ⟨w, hw, hbw⟩ := hov
    have hM := F₁.maxFinite_mem hb₁
    refine saturated_eq_of_roundsInBound hb₁ (not_lt.mp fun hlt => hbw ?_) hy
    have hzM := abs_faithful_le_of_le (mem_unbounded_of_mem (hsub _ hM)) hlt.le
      hz.1.isFaithfulRound
    refine boundOK_of_abs_le ?_ hM.2.2
    rw [abs_of_nonneg (F₁.maxFinite_nonneg hb₁)]
    exact abs_faithful_le_of_le (mem_unbounded_of_mem hM) hzM hw.isFaithfulRound
  inner x y hov hy := by
    have hM := F₁.maxFinite_mem hb₁
    rw [OverflowMap.saturate_composes hsub hb₁ hb₂ h₁u]
    exact congrArg RoundResult.value (saturated_eq_of_roundsInBound hb₁
      ((F₂.le_maxFinite hb₂ (hsub _ hM)).trans (maxFinite_le_abs_of_overflows hb₂ hov)) hy)

end Mpfx
