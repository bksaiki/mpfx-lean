import Mpfx.Rounding.Op.Defs
import Mpfx.Rounding.Parity
import Mpfx.Rounding.Basic

/-!
# Soundness of `rndUnbounded` for `toOdd`

When the scaled mantissa is an integer the floor point is `x` itself. Otherwise
`rndInt` keeps the floor point, the round-down, when it is odd, and otherwise
takes its successor, the round-up, which is then odd by alternation (`neighbors_alternate`).
-/

namespace Mpfx

attribute [local instance] Classical.propDecidable

theorem rndUnbounded_satisfies_toOdd (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .toOdd) :
    RoundsFinite F.unbounded .toOdd x (rndUnbounded F .toOdd x h) := by
  set e := F.canonicalExp x
  set s := x * (2 : ℝ) ^ (-e)
  have hd := RoundsFinite.toNegative_floor F x
  change RoundsFinite F.unbounded .toOdd x
    (Dyadic.ofIntZpow (if (⌊s⌋ : ℝ) = s then ⌊s⌋
      else if F.IsOdd (Dyadic.ofIntZpow ⌊s⌋ e) then ⌊s⌋ else ⌊s⌋ + 1) e)
  split_ifs with hs hodd
  · -- An integer scaled mantissa: the floor point is `x`.
    have hx : x = (Dyadic.ofIntZpow ⌊s⌋ e : ℝ) := by
      rw [Dyadic.coe_ofIntZpow, hs, mul_zpow_neg_self]
    have := RoundsFinite.self (F := F.unbounded) .toOdd hd.1
    rwa [← hx] at this
  · exact ⟨hd.1, Or.inl hd, fun _ => hodd⟩
  · have hu := RoundsFinite.toPositive_floor_add_one F hs
    exact ⟨hu.1, Or.inr hu, fun _ => (neighbors_alternate x h hs).mpr hodd⟩

end Mpfx
