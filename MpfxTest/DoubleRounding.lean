import Mpfx.DoubleRounding.Special

/-!
# Double rounding with the IEEE tables

The standard tables discharge the composition hypotheses of the `rnd*` rules,
except for RTO → RTZ.
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
  rndRTO_RN hsub hnt h₁u (SpecialMap.exact_composes h₂ _ _ _)
    (OverflowMap.composes_of_inf (OverflowMap.ieee_map_toOdd _ _ _)
      (fun _ => rfl) (OverflowMap.ieee_map_nearest _ _ _ _)) hu

/-- RTZ → RTZ with exact specials and IEEE (saturating) overflow. -/
example (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial) {v : WithSpecial ℝ} {u : WithSpecial Dyadic}
    (hu : rnd F₂ (SpecialMap.exact _ h₂) (OverflowMap.ieee F₂ .toZero hb₂ fun _ => h₂ _)
      .toZero v = .value u) :
    rnd F₁ (SpecialMap.exact _ h₁) (OverflowMap.ieee F₁ .toZero hb₁ fun _ => h₁ _)
        .toZero u.toReal =
      rnd F₁ (SpecialMap.exact _ h₁) (OverflowMap.ieee F₁ .toZero hb₁ fun _ => h₁ _)
        .toZero v :=
  rndRTZ_RTZ hsub hnt (SpecialMap.exact_composes h₂ _ _ _)
    (OverflowMap.ieee_toZero_composes hsub hnt hb₁ hb₂ _ _ _) hu

/-- RTO → RTZ: the IEEE overflow tables do not compose. RTO overflows to `+Inf`,
which RTZ keeps exact, while direct RTZ saturates to `+maxFinite₁`. -/
example : ¬ (OverflowMap.ieee F₂ .toOdd hb₂ fun _ => h₂ _).Composes
    (SpecialMap.exact _ h₁) (OverflowMap.ieee F₁ .toZero hb₁ fun _ => h₁ _) .toZero := by
  intro h
  have h' := RoundResult.value.inj ((rnd_special _ _ _ _ _).symm.trans (h false))
  cases h'

end Mpfx
