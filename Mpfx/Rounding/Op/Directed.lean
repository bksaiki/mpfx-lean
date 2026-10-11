import Mpfx.Rounding.Op.Defs
import Mpfx.Rounding.Basic

/-!
# Soundness of `rndUnbounded` for the directed modes

`rndInt` takes the floor or the ceiling at the canonical exponent, which are
the round-down and the round-up (`RoundsFinite.toNegative_floor`,
`toPositive_ceil`). `toZero`/`awayZero` pick one by the sign of `x` and
transport through the sign-equivalences (Flocq `round_ZR_DN`/`round_AW_UP`).
-/

namespace Mpfx

attribute [local instance] Classical.propDecidable

theorem rndUnbounded_satisfies_toNegative (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .toNegative) :
    RoundsFinite F.unbounded .toNegative x (rndUnbounded F .toNegative x h) :=
  RoundsFinite.toNegative_floor F x

theorem rndUnbounded_satisfies_toPositive (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .toPositive) :
    RoundsFinite F.unbounded .toPositive x (rndUnbounded F .toPositive x h) :=
  RoundsFinite.toPositive_ceil F x

theorem rndUnbounded_satisfies_toZero (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .toZero) :
    RoundsFinite F.unbounded .toZero x (rndUnbounded F .toZero x h) := by
  unfold rndUnbounded
  by_cases hx : 0 ≤ x
  · rw [show rndInt F .toZero x _ = _ from if_pos hx]
    exact (RoundsFinite.toNegative_iff_toZero_of_nonneg F.unbounded hx _).mp
      (RoundsFinite.toNegative_floor F x)
  · rw [show rndInt F .toZero x _ = _ from if_neg hx]
    exact (RoundsFinite.toPositive_iff_toZero_of_nonpos F.unbounded (not_le.mp hx).le _).mp
      (RoundsFinite.toPositive_ceil F x)

theorem rndUnbounded_satisfies_awayZero (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .awayZero) :
    RoundsFinite F.unbounded .awayZero x (rndUnbounded F .awayZero x h) := by
  unfold rndUnbounded
  by_cases hx : 0 ≤ x
  · rw [show rndInt F .awayZero x _ = _ from if_pos hx]
    exact (RoundsFinite.toPositive_iff_awayZero_of_nonneg F.unbounded hx _).mp
      (RoundsFinite.toPositive_ceil F x)
  · rw [show rndInt F .awayZero x _ = _ from if_neg hx]
    exact (RoundsFinite.toNegative_iff_awayZero_of_nonpos F.unbounded (not_le.mp hx).le _).mp
      (RoundsFinite.toNegative_floor F x)

end Mpfx
