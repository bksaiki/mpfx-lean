import Mpfx.Rounding.Op.Defs
import Mpfx.Rounding.Parity
import Mpfx.Rounding.Basic

/-!
# Soundness of `rndUnbounded` for `toOdd`

On the grid the floor point is `x` itself. Off it, `rndInt` keeps the floor
point, the round-down, when it is odd, and otherwise takes its successor, the
round-up, which is then odd by alternation (`isOdd_alternate_of_bracketing`).
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
  · -- On the grid: the floor point is `x`.
    have hx : x = (Dyadic.ofIntZpow ⌊s⌋ e : ℝ) := by
      rw [Dyadic.coe_ofIntZpow, hs, mul_zpow_neg_self]
    have := RoundsFinite.self (F := F.unbounded) .toOdd hd.1
    rwa [← hx] at this
  · exact ⟨hd.1, Or.inl hd, fun _ => hodd⟩
  · have hu := RoundsFinite.toPositive_floor_add_one F hs
    have hne : x ≠ (Dyadic.ofIntZpow ⌊s⌋ e : ℝ) := fun hx => hs (by
      rw [Dyadic.coe_ofIntZpow] at hx
      change _ = x * _
      rw [hx, mul_assoc, ← zpow_add₀ two_ne_zero, add_neg_cancel, zpow_zero, mul_one])
    exact ⟨hu.1, Or.inr hu, fun _ => (isOdd_alternate_of_bracketing (F := F) h hd hu hne).mpr hodd⟩

end Mpfx
