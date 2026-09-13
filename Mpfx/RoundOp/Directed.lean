import Mpfx.RoundOp.Defs
import Mpfx.RoundPred

/-!
# Soundness of `rndUnbounded` for the directed modes

`toZero`/`awayZero` transport from `toNegative`/`toPositive` through the
sign-equivalences in `Mpfx/Rounding.lean` (Flocq `round_ZR_DN`/`round_AW_UP`).
-/

namespace Mpfx

attribute [local instance] Classical.propDecidable

theorem rndUnbounded_satisfies_toNegative (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .toNegative) :
    RoundsFinite F.unbounded .toNegative x (rndUnbounded F .toNegative x h) := by
  have h_rnd_eq : rndUnbounded F .toNegative x h =
      Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋ (F.canonicalExp x) := by
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.toNegative : RoundingMode) ≠ .toOdd)]
    rw [dif_neg (by decide : (RoundingMode.toNegative : RoundingMode) ≠ .nearest .toEven)]
    rfl
  rw [h_rnd_eq]
  exact RoundsFinite.toNegative_floor F x

theorem rndUnbounded_satisfies_toPositive (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .toPositive) :
    RoundsFinite F.unbounded .toPositive x (rndUnbounded F .toPositive x h) := by
  have h_rnd_eq : rndUnbounded F .toPositive x h =
      Dyadic.ofIntZpow ⌈x * (2 : ℝ) ^ (-(F.canonicalExp x))⌉ (F.canonicalExp x) := by
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.toPositive : RoundingMode) ≠ .toOdd)]
    rw [dif_neg (by decide : (RoundingMode.toPositive : RoundingMode) ≠ .nearest .toEven)]
    rfl
  rw [h_rnd_eq]
  exact RoundsFinite.toPositive_ceil F x

/-! ### Sign bridges

On each side of zero the `toZero`/`awayZero` rounding *function* coincides with a
one-sided directed mode; `rndInt` picks `⌊·⌋`/`⌈·⌉` by the sign of `x`. These
four definitional identities let the `toZero`/`awayZero` obligations reuse the
`toNegative`/`toPositive` proofs. -/

/-- On `0 ≤ x`, round-to-zero is round-to-negative. -/
private theorem rndUnbounded_toZero_eq_toNegative_of_nonneg (F : FiniteFormat) (x : ℝ)
    (hx : 0 ≤ x) (h : ¬ F.IsUndefined .toZero) (h' : ¬ F.IsUndefined .toNegative) :
    rndUnbounded F .toZero x h = rndUnbounded F .toNegative x h' := by
  have hz : rndUnbounded F .toZero x h =
      Dyadic.ofIntZpow (rndInt .toZero x (F.canonicalExp x)) (F.canonicalExp x) := by
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.toZero : RoundingMode) ≠ .toOdd),
        dif_neg (by decide : (RoundingMode.toZero : RoundingMode) ≠ .nearest .toEven)]
  have hn : rndUnbounded F .toNegative x h' =
      Dyadic.ofIntZpow (rndInt .toNegative x (F.canonicalExp x)) (F.canonicalExp x) := by
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.toNegative : RoundingMode) ≠ .toOdd),
        dif_neg (by decide : (RoundingMode.toNegative : RoundingMode) ≠ .nearest .toEven)]
  rw [hz, hn]; congr 1
  change (if 0 ≤ x then ⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋
        else ⌈x * (2 : ℝ) ^ (-(F.canonicalExp x))⌉)
      = ⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋
  rw [if_pos hx]

/-- On `x < 0`, round-to-zero is round-to-positive. -/
private theorem rndUnbounded_toZero_eq_toPositive_of_neg (F : FiniteFormat) (x : ℝ)
    (hx : x < 0) (h : ¬ F.IsUndefined .toZero) (h' : ¬ F.IsUndefined .toPositive) :
    rndUnbounded F .toZero x h = rndUnbounded F .toPositive x h' := by
  have hz : rndUnbounded F .toZero x h =
      Dyadic.ofIntZpow (rndInt .toZero x (F.canonicalExp x)) (F.canonicalExp x) := by
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.toZero : RoundingMode) ≠ .toOdd),
        dif_neg (by decide : (RoundingMode.toZero : RoundingMode) ≠ .nearest .toEven)]
  have hp : rndUnbounded F .toPositive x h' =
      Dyadic.ofIntZpow (rndInt .toPositive x (F.canonicalExp x)) (F.canonicalExp x) := by
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.toPositive : RoundingMode) ≠ .toOdd),
        dif_neg (by decide : (RoundingMode.toPositive : RoundingMode) ≠ .nearest .toEven)]
  rw [hz, hp]; congr 1
  change (if 0 ≤ x then ⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋
        else ⌈x * (2 : ℝ) ^ (-(F.canonicalExp x))⌉)
      = ⌈x * (2 : ℝ) ^ (-(F.canonicalExp x))⌉
  rw [if_neg (not_le.mpr hx)]

/-- On `0 ≤ x`, round-away-from-zero is round-to-positive. -/
private theorem rndUnbounded_awayZero_eq_toPositive_of_nonneg (F : FiniteFormat) (x : ℝ)
    (hx : 0 ≤ x) (h : ¬ F.IsUndefined .awayZero) (h' : ¬ F.IsUndefined .toPositive) :
    rndUnbounded F .awayZero x h = rndUnbounded F .toPositive x h' := by
  have ha : rndUnbounded F .awayZero x h =
      Dyadic.ofIntZpow (rndInt .awayZero x (F.canonicalExp x)) (F.canonicalExp x) := by
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.awayZero : RoundingMode) ≠ .toOdd),
        dif_neg (by decide : (RoundingMode.awayZero : RoundingMode) ≠ .nearest .toEven)]
  have hp : rndUnbounded F .toPositive x h' =
      Dyadic.ofIntZpow (rndInt .toPositive x (F.canonicalExp x)) (F.canonicalExp x) := by
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.toPositive : RoundingMode) ≠ .toOdd),
        dif_neg (by decide : (RoundingMode.toPositive : RoundingMode) ≠ .nearest .toEven)]
  rw [ha, hp]; congr 1
  change (if 0 ≤ x then ⌈x * (2 : ℝ) ^ (-(F.canonicalExp x))⌉
        else ⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋)
      = ⌈x * (2 : ℝ) ^ (-(F.canonicalExp x))⌉
  rw [if_pos hx]

/-- On `x < 0`, round-away-from-zero is round-to-negative. -/
private theorem rndUnbounded_awayZero_eq_toNegative_of_neg (F : FiniteFormat) (x : ℝ)
    (hx : x < 0) (h : ¬ F.IsUndefined .awayZero) (h' : ¬ F.IsUndefined .toNegative) :
    rndUnbounded F .awayZero x h = rndUnbounded F .toNegative x h' := by
  have ha : rndUnbounded F .awayZero x h =
      Dyadic.ofIntZpow (rndInt .awayZero x (F.canonicalExp x)) (F.canonicalExp x) := by
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.awayZero : RoundingMode) ≠ .toOdd),
        dif_neg (by decide : (RoundingMode.awayZero : RoundingMode) ≠ .nearest .toEven)]
  have hn : rndUnbounded F .toNegative x h' =
      Dyadic.ofIntZpow (rndInt .toNegative x (F.canonicalExp x)) (F.canonicalExp x) := by
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.toNegative : RoundingMode) ≠ .toOdd),
        dif_neg (by decide : (RoundingMode.toNegative : RoundingMode) ≠ .nearest .toEven)]
  rw [ha, hn]; congr 1
  change (if 0 ≤ x then ⌈x * (2 : ℝ) ^ (-(F.canonicalExp x))⌉
        else ⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋)
      = ⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋
  rw [if_neg (not_le.mpr hx)]

theorem rndUnbounded_satisfies_toZero (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .toZero) :
    RoundsFinite F.unbounded .toZero x (rndUnbounded F .toZero x h) := by
  by_cases hx : 0 ≤ x
  · rw [rndUnbounded_toZero_eq_toNegative_of_nonneg F x hx h (not_isUndefined_toNegative F)]
    exact (RoundsFinite.toNegative_iff_toZero_of_nonneg F.unbounded hx _).mp
      (rndUnbounded_satisfies_toNegative F x (not_isUndefined_toNegative F))
  · rw [rndUnbounded_toZero_eq_toPositive_of_neg F x (not_le.mp hx) h
        (not_isUndefined_toPositive F)]
    exact (RoundsFinite.toPositive_iff_toZero_of_nonpos F.unbounded (not_le.mp hx).le _).mp
      (rndUnbounded_satisfies_toPositive F x (not_isUndefined_toPositive F))

theorem rndUnbounded_satisfies_awayZero (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .awayZero) :
    RoundsFinite F.unbounded .awayZero x (rndUnbounded F .awayZero x h) := by
  by_cases hx : 0 ≤ x
  · rw [rndUnbounded_awayZero_eq_toPositive_of_nonneg F x hx h (not_isUndefined_toPositive F)]
    exact (RoundsFinite.toPositive_iff_awayZero_of_nonneg F.unbounded hx _).mp
      (rndUnbounded_satisfies_toPositive F x (not_isUndefined_toPositive F))
  · rw [rndUnbounded_awayZero_eq_toNegative_of_neg F x (not_le.mp hx) h
        (not_isUndefined_toNegative F)]
    exact (RoundsFinite.toNegative_iff_awayZero_of_nonpos F.unbounded (not_le.mp hx).le _).mp
      (rndUnbounded_satisfies_toNegative F x (not_isUndefined_toNegative F))

end Mpfx
