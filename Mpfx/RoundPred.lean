import Mpfx.Rounding

/-!
# Round-predicate layer: uniqueness and faithfulness

The mode-generic consequences of the `RoundsFinite` spec, in the style of
Flocq's `Core/Round_pred.v`. Two families:

* `RoundsFinite.unique_*` — the spec pins its value. Flocq's `round_unique`
  gets this from monotonicity; for the directed modes the antisymmetry
  argument is direct, so it needs no monotonicity theory.
* `RoundsFinite.isFaithfulRound` — every mode rounds down or up (Flocq's
  `Zrnd_DN_or_UP` / `Rnd_N_pt_DN_or_UP`). Lets mode-generic arguments stop
  case-splitting on `rm`.

This file stays in constructive logic and depends only on
`Mpfx/Rounding.lean`: sign case splits go through `le_total`, never
`by_cases`, and nothing here mentions the `rnd` construction. The
uniqueness proofs for the parity-aware modes (`toOdd`, `nearest`) need the
grid-neighbour parity theory and so live in `Mpfx/RoundOp/`.
-/

namespace Mpfx

/-! ### Uniqueness for the directed modes -/

/-- Round-down is unique: two largest `F`-elements `≤ x` coincide. This is
Flocq's `Rnd_DN_pt_unique`. -/
theorem RoundsFinite.unique_toNegative {F : FiniteFormat} {x : ℝ} {y₁ y₂ : Dyadic}
    (h₁ : RoundsFinite F .toNegative x y₁) (h₂ : RoundsFinite F .toNegative x y₂) :
    y₁ = y₂ := by
  obtain ⟨hm₁, hle₁, hmax₁⟩ := h₁
  obtain ⟨hm₂, hle₂, hmax₂⟩ := h₂
  exact Dyadic.ext_real (le_antisymm (hmax₂ y₁ hm₁ hle₁) (hmax₁ y₂ hm₂ hle₂))

/-- Round-up is unique (Flocq's `Rnd_UP_pt_unique`). -/
theorem RoundsFinite.unique_toPositive {F : FiniteFormat} {x : ℝ} {y₁ y₂ : Dyadic}
    (h₁ : RoundsFinite F .toPositive x y₁) (h₂ : RoundsFinite F .toPositive x y₂) :
    y₁ = y₂ := by
  obtain ⟨hm₁, hge₁, hmin₁⟩ := h₁
  obtain ⟨hm₂, hge₂, hmin₂⟩ := h₂
  exact Dyadic.ext_real (le_antisymm (hmin₁ y₂ hm₂ hge₂) (hmin₂ y₁ hm₁ hge₁))

/-- Round-toward-zero is unique: it agrees with round-down on `0 ≤ x` and
with round-up on `x ≤ 0`. -/
theorem RoundsFinite.unique_toZero {F : FiniteFormat} {x : ℝ} {y₁ y₂ : Dyadic}
    (h₁ : RoundsFinite F .toZero x y₁) (h₂ : RoundsFinite F .toZero x y₂) :
    y₁ = y₂ := by
  rcases le_total 0 x with hx | hx
  · exact unique_toNegative
      ((RoundsFinite.toNegative_iff_toZero_of_nonneg F hx y₁).mpr h₁)
      ((RoundsFinite.toNegative_iff_toZero_of_nonneg F hx y₂).mpr h₂)
  · exact unique_toPositive
      ((RoundsFinite.toPositive_iff_toZero_of_nonpos F hx y₁).mpr h₁)
      ((RoundsFinite.toPositive_iff_toZero_of_nonpos F hx y₂).mpr h₂)

/-- Round-away-from-zero is unique. Sign-mirror of `unique_toZero`. -/
theorem RoundsFinite.unique_awayZero {F : FiniteFormat} {x : ℝ} {y₁ y₂ : Dyadic}
    (h₁ : RoundsFinite F .awayZero x y₁) (h₂ : RoundsFinite F .awayZero x y₂) :
    y₁ = y₂ := by
  rcases le_total 0 x with hx | hx
  · exact unique_toPositive
      ((RoundsFinite.toPositive_iff_awayZero_of_nonneg F hx y₁).mpr h₁)
      ((RoundsFinite.toPositive_iff_awayZero_of_nonneg F hx y₂).mpr h₂)
  · exact unique_toNegative
      ((RoundsFinite.toNegative_iff_awayZero_of_nonpos F hx y₁).mpr h₁)
      ((RoundsFinite.toNegative_iff_awayZero_of_nonpos F hx y₂).mpr h₂)

/-! ### Every mode rounds faithfully -/

/-- **Faithfulness, uniformly.** Whatever the mode, the rounded value is
either the round-down or the round-up of `x`. The directed modes reduce to
each other by the sign of `x`; `toOdd` and `nearest` carry the
`IsFaithfulRound` conjunct outright.

Use `isFaithfulRound_iff_directed` to read the result back as
`RoundsFinite .toNegative ∨ RoundsFinite .toPositive` when a case split on
the two sides is what is wanted.

Flocq derives the same fact once from the `Valid_rnd` class
(`Zrnd_DN_or_UP`, `Generic_fmt.v:577`) plus `Rnd_N_pt_DN_or_UP`. -/
theorem RoundsFinite.isFaithfulRound {F : FiniteFormat} {rm : RoundingMode} {x : ℝ}
    {y : Dyadic} (h : RoundsFinite F rm x y) :
    IsFaithfulRound F x y := by
  cases rm with
  | toNegative => exact isFaithfulRound_iff_directed.mpr (Or.inl h)
  | toPositive => exact isFaithfulRound_iff_directed.mpr (Or.inr h)
  | toZero =>
      rcases le_total 0 x with hx | hx
      · exact isFaithfulRound_iff_directed.mpr
          (Or.inl ((RoundsFinite.toNegative_iff_toZero_of_nonneg F hx y).mpr h))
      · exact isFaithfulRound_iff_directed.mpr
          (Or.inr ((RoundsFinite.toPositive_iff_toZero_of_nonpos F hx y).mpr h))
  | awayZero =>
      rcases le_total 0 x with hx | hx
      · exact isFaithfulRound_iff_directed.mpr
          (Or.inr ((RoundsFinite.toPositive_iff_awayZero_of_nonneg F hx y).mpr h))
      · exact isFaithfulRound_iff_directed.mpr
          (Or.inl ((RoundsFinite.toNegative_iff_awayZero_of_nonpos F hx y).mpr h))
  | toOdd => exact h.2.1
  | nearest tb => cases tb <;> exact h.2.1

/-- **Rounding fixes zero** (Flocq's `round_0`). Every mode sends `0` to `0`,
since `0` lies in every format. -/
theorem RoundsFinite.eq_zero_of_zero {F : FiniteFormat} {rm : RoundingMode}
    {y : Dyadic} (h : RoundsFinite F rm 0 y) : y = 0 :=
  RoundsFinite.eq_of_mem (F.zero_mem) (by rwa [Dyadic.coe_real_zero])

/-- Two *distinct* faithful roundings of `x` sit on opposite sides of it: one
is the round-down, the other the round-up. Same-side pairs collapse by
`unique_toNegative` / `unique_toPositive`. This is the case split behind
Flocq's `Rnd_NG_pt_unique` (`Round_pred.v:707`). -/
theorem IsFaithfulRound.opposite_sides_of_ne {F : FiniteFormat} {x : ℝ}
    {a b : Dyadic} (ha : IsFaithfulRound F x a) (hb : IsFaithfulRound F x b)
    (hab : a ≠ b) :
    (RoundsFinite F .toNegative x a ∧ RoundsFinite F .toPositive x b) ∨
    (RoundsFinite F .toNegative x b ∧ RoundsFinite F .toPositive x a) := by
  rcases isFaithfulRound_iff_directed.mp ha with hda | hua <;>
    rcases isFaithfulRound_iff_directed.mp hb with hdb | hub
  · exact absurd (RoundsFinite.unique_toNegative hda hdb) hab
  · exact Or.inl ⟨hda, hub⟩
  · exact Or.inr ⟨hdb, hua⟩
  · exact absurd (RoundsFinite.unique_toPositive hua hub) hab

end Mpfx
