import Mpfx.DoubleRounding.Special

/-!
# Double rounding with the IEEE tables

The standard tables discharge the table hypotheses of the `rnd*` rules, except
for RTO → RTZ.
-/

namespace Mpfx

variable {F₁ F₂ : FiniteFormat} (h₁ : ∀ s, s ∈ F₁.specials) (h₂ : ∀ s, s ∈ F₂.specials)
  (hb₁ : F₁.b ≠ ⊤) (hb₂ : F₂.b ≠ ⊤)

/-- RTO → RN with exact specials and IEEE overflow, on every input. -/
example (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
      ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial) {tb : TieBreak} (h₁u : ¬ F₁.IsUndefined (.nearest tb))
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ (SpecialMap.exact _ h₂) (OverflowMap.ieee F₂ .toOdd hb₂ fun _ => h₂ _)
      .toOdd v = .value u) :
    rnd F₁ (SpecialMap.exact _ h₁) (OverflowMap.ieee F₁ (.nearest tb) hb₁ fun _ => h₁ _)
        (.nearest tb) u.toReal =
      rnd F₁ (SpecialMap.exact _ h₁) (OverflowMap.ieee F₁ (.nearest tb) hb₁ fun _ => h₁ _)
        (.nearest tb) v :=
  rndRTO_RN_of_bound hsub hnt h₁u (SpecialMap.exact_composes h₂ _ _ _)
    (OverflowMap.composes_of_inf (OverflowMap.ieee_map_toOdd _ _ _)
      (fun _ => rfl) (OverflowMap.ieee_map_nearest _ _ _ _)) hu

/-- RTZ → RTZ with exact specials and IEEE (saturating) overflow, under the plain
containment. -/
example (hsub : F₁.toFormat ⊆ F₂.toFormat) {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ (SpecialMap.exact _ h₂) (OverflowMap.ieee F₂ .toZero hb₂ fun _ => h₂ _)
      .toZero v = .value u) :
    rnd F₁ (SpecialMap.exact _ h₁) (OverflowMap.ieee F₁ .toZero hb₁ fun _ => h₁ _)
        .toZero u.toReal =
      rnd F₁ (SpecialMap.exact _ h₁) (OverflowMap.ieee F₁ .toZero hb₁ fun _ => h₁ _)
        .toZero v :=
  rndRTZ_RTZ hsub (.of_saturate hsub hb₁ hb₂ (not_isUndefined_toZero F₁))
    (SpecialMap.exact_composes h₂ _ _ _)
    (OverflowMap.ieee_toZero_composes hsub hb₁ hb₂ (fun _ => h₁ _) (fun _ => h₂ _) _) hu

/-- RTO → RTZ: the IEEE overflow tables do not compose. RTO overflows to `+Inf`,
which RTZ keeps exact, while direct RTZ saturates to `+maxFinite₁`. -/
example : ¬ (OverflowMap.ieee F₂ .toOdd hb₂ fun _ => h₂ _).Composes
    (SpecialMap.exact _ h₁) (OverflowMap.ieee F₁ .toZero hb₁ fun _ => h₁ _) .toZero := by
  intro h
  have h' := RoundResult.value.inj ((rnd_special _ _ _ _ _).symm.trans (h false))
  cases h'

/-- RTO → RTZ composes once RTO overflow saturates, under the plain containment. -/
example (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat) (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ (SpecialMap.exact _ h₂) (OverflowMap.saturate F₂ hb₂) .toOdd v = .value u) :
    rnd F₁ (SpecialMap.exact _ h₁) (OverflowMap.ieee F₁ .toZero hb₁ fun _ => h₁ _)
        .toZero u.toReal =
      rnd F₁ (SpecialMap.exact _ h₁) (OverflowMap.ieee F₁ .toZero hb₁ fun _ => h₁ _)
        .toZero v :=
  have hsub₁ : F₁.toFormat ⊆ F₂.toFormat := Format.subset_of_mem hsub.specials fun y hy =>
    hsub y (Format.self_subset_extend F₁.toFormat 1 y hy)
  rndRTO_RTZ hsub hp_F₂ (.of_saturate hsub₁ hb₁ hb₂ (not_isUndefined_toZero F₁))
    (SpecialMap.exact_composes h₂ _ _ _)
    (OverflowMap.saturate_composes hsub₁ hb₁ hb₂ (not_isUndefined_toZero F₁) _) hu

/-- RTO → RTO with saturating overflow, under the plain containment. -/
example (hsub : F₁.toFormat ⊆ F₂.toFormat) (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    (h₁u : ¬ F₁.IsUndefined .toOdd) {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ (SpecialMap.exact _ h₂) (OverflowMap.saturate F₂ hb₂) .toOdd v = .value u) :
    rnd F₁ (SpecialMap.exact _ h₁) (OverflowMap.saturate F₁ hb₁) .toOdd u.toReal =
      rnd F₁ (SpecialMap.exact _ h₁) (OverflowMap.saturate F₁ hb₁) .toOdd v :=
  rndRTO_RTO hsub hp_F₂ h₁u (.of_saturate hsub hb₁ hb₂ h₁u) (SpecialMap.exact_composes h₂ _ _ _)
    (OverflowMap.saturate_composes hsub hb₁ hb₂ h₁u _) hu

/-- RTO → RN with the IEEE tables fails wherever `F₂` overflows and `F₁` does
not, a region the relaxed bound `b₂ ≥ M` of `rndRTO_RN_of_bound` rules out: the
chain gives `±Inf`, the direct rounding a finite value. -/
example {tb : TieBreak} (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    (h₁u : ¬ F₁.IsUndefined (.nearest tb)) {x : ℝ} {y : Dyadic}
    (hov : Overflows F₂ .toOdd x) (hy : RoundsInBound F₁ (.nearest tb) x y) :
    ∃ u, rnd F₂ (SpecialMap.exact _ h₂) (OverflowMap.ieee F₂ .toOdd hb₂ fun _ => h₂ _)
        .toOdd (.finite x) = .value u ∧
      rnd F₁ (SpecialMap.exact _ h₁) (OverflowMap.ieee F₁ (.nearest tb) hb₁ fun _ => h₁ _)
          (.nearest tb) u.toReal ≠
        rnd F₁ (SpecialMap.exact _ h₁) (OverflowMap.ieee F₁ (.nearest tb) hb₁ fun _ => h₁ _)
          (.nearest tb) (.finite x) := by
  obtain ⟨z, hz, hbz⟩ := hov
  refine ⟨_, by rw [rnd_finite_of_roundsFinite (not_isUndefined_of_two_le_p hp_F₂) hz,
    if_neg hbz], ?_⟩
  rw [rnd_finite_of_roundsFinite h₁u hy.1, if_pos hy.2, OverflowMap.ieee_map_toOdd,
    WithSpecial.toReal_special, rnd_special, SpecialMap.exact_map]
  intro h
  cases RoundResult.value.inj h

end Mpfx
