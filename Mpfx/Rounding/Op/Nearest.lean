import Mpfx.Rounding.Op.Defs
import Mpfx.Rounding.Parity
import Mpfx.Rounding.Basic

/-!
# Soundness of `rndUnbounded` for the `nearest tb` modes

When the scaled mantissa is an integer the floor point is `x` itself. Otherwise
the floor point `dlo` and its successor `dhi` are the round-down and the
round-up, at distances `δ · 2^e` and `(1 − δ) · 2^e` for the fraction `δ` of the
scaled mantissa. Both modes take the nearer one, so
`RoundsFinite.nearest_*_of_bracket` applies; on a tie (`δ = ½`) RNA takes the one
of larger magnitude and RNE the even one, which alternation supplies
(`neighbors_alternate`).
-/

namespace Mpfx

attribute [local instance] Classical.propDecidable

theorem rndUnbounded_satisfies_nearest (F : FiniteFormat) (tb : TieBreak) (x : ℝ)
    (h : ¬ F.IsUndefined (.nearest tb)) :
    RoundsFinite F.unbounded (.nearest tb) x (rndUnbounded F (.nearest tb) x h) := by
  set e := F.canonicalExp x
  set s := x * (2 : ℝ) ^ (-e)
  set lo := ⌊s⌋
  set dlo := Dyadic.ofIntZpow lo e
  set dhi := Dyadic.ofIntZpow (lo + 1) e
  have hd : RoundsFinite F.unbounded .toNegative x dlo := RoundsFinite.toNegative_floor F x
  have h2e : (0 : ℝ) < 2 ^ e := zpow_pos two_pos e
  have hs_eq : s * 2 ^ e = x := mul_zpow_neg_self x e
  have hlo := Int.floor_le s
  by_cases hs : (lo : ℝ) = s
  · -- The fraction is `0`: both modes take the floor point, and it is `x`.
    have hδ : s - lo < 1 / 2 := by rw [← hs, sub_self]; norm_num
    have hval : rndUnbounded F (.nearest tb) x h = dlo := by
      cases tb <;> exact congrArg (Dyadic.ofIntZpow · e) (if_pos hδ)
    have hx : x = (dlo : ℝ) := by rw [Dyadic.coe_ofIntZpow, hs, hs_eq]
    have := RoundsFinite.self (F := F.unbounded) (.nearest tb) hd.1
    rw [hval]
    rwa [← hx] at this
  have hu : RoundsFinite F.unbounded .toPositive x dhi := RoundsFinite.toPositive_floor_add_one F hs
  -- Distances to the two neighbours, in units of the step.
  have hdlo : |x - (dlo : ℝ)| = (s - lo) * 2 ^ e := by
    rw [abs_of_nonneg (by linarith [hd.2.1]), Dyadic.coe_ofIntZpow, ← hs_eq]; ring
  have hdhi : |x - (dhi : ℝ)| = (1 - (s - lo)) * 2 ^ e := by
    rw [abs_of_nonpos (by linarith [hu.2.1]), Dyadic.coe_ofIntZpow, ← hs_eq]; push_cast; ring
  have hlt : s - lo < 1 / 2 → |x - (dlo : ℝ)| < |x - (dhi : ℝ)| := fun hδ => by
    rw [hdlo, hdhi]; exact mul_lt_mul_of_pos_right (by linarith) h2e
  have hgt : 1 / 2 < s - lo → |x - (dhi : ℝ)| < |x - (dlo : ℝ)| := fun hδ => by
    rw [hdlo, hdhi]; exact mul_lt_mul_of_pos_right (by linarith) h2e
  have htie : ¬ s - lo < 1 / 2 → ¬ 1 / 2 < s - lo → |x - (dlo : ℝ)| = |x - (dhi : ℝ)| :=
    fun h₁ h₂ => by rw [hdlo, hdhi]; congr 1; linarith
  -- On a tie `x` is the midpoint: `dlo + dhi = 2x`.
  have hmid : ¬ s - lo < 1 / 2 → ¬ 1 / 2 < s - lo → (dlo : ℝ) + dhi = 2 * x := fun h₁ h₂ => by
    have := htie h₁ h₂
    rw [abs_of_nonneg (by linarith [hd.2.1]), abs_of_nonpos (by linarith [hu.2.1])] at this
    linarith
  cases tb with
  | awayZero =>
    change RoundsFinite _ _ x (Dyadic.ofIntZpow (if s - lo < 1 / 2 then lo
      else if 1 / 2 < s - lo then lo + 1 else if 0 ≤ x then lo + 1 else lo) e)
    split_ifs with h₁ h₂ hx
    · exact RoundsFinite.nearest_awayZero_of_bracket hd hu (Or.inl rfl)
        ⟨le_rfl, (hlt h₁).le⟩ fun h _ => absurd h (hlt h₁).ne
    · exact RoundsFinite.nearest_awayZero_of_bracket hd hu (Or.inr rfl)
        ⟨(hgt h₂).le, le_rfl⟩ fun h _ => absurd h.symm (hgt h₂).ne
    · refine RoundsFinite.nearest_awayZero_of_bracket hd hu (Or.inr rfl)
        ⟨(htie h₁ h₂).ge, le_rfl⟩ fun _ _ => ⟨?_, le_rfl⟩
      rw [abs_of_nonneg (hx.trans hu.2.1), abs_le]
      constructor <;> linarith [hmid h₁ h₂, hd.2.1, hu.2.1]
    · refine RoundsFinite.nearest_awayZero_of_bracket hd hu (Or.inl rfl)
        ⟨le_rfl, (htie h₁ h₂).le⟩ fun _ _ => ⟨le_rfl, ?_⟩
      push Not at hx
      rw [abs_of_neg (hd.2.1.trans_lt hx), abs_le]
      constructor <;> linarith [hmid h₁ h₂, hd.2.1, hu.2.1]
  | toEven =>
    have hodd : ¬ F.IsUndefined .toOdd := fun ⟨h₁, h₂, _⟩ => h ⟨h₁, h₂, Or.inr rfl⟩
    change RoundsFinite _ _ x (Dyadic.ofIntZpow (if s - lo < 1 / 2 then lo
      else if 1 / 2 < s - lo then lo + 1 else if F.IsEven dlo then lo else lo + 1) e)
    split_ifs with h₁ h₂ hev
    · exact RoundsFinite.nearest_toEven_of_bracket hd hu (Or.inl rfl)
        ⟨le_rfl, (hlt h₁).le⟩ fun h _ => absurd h (hlt h₁).ne
    · exact RoundsFinite.nearest_toEven_of_bracket hd hu (Or.inr rfl)
        ⟨(hgt h₂).le, le_rfl⟩ fun h _ => absurd h.symm (hgt h₂).ne
    · exact RoundsFinite.nearest_toEven_of_bracket hd hu (Or.inl rfl)
        ⟨le_rfl, (htie h₁ h₂).le⟩ fun _ _ => hev
    · exact RoundsFinite.nearest_toEven_of_bracket hd hu (Or.inr rfl)
        ⟨(htie h₁ h₂).ge, le_rfl⟩ fun _ _ =>
          ⟨hu.1, fun ho => hev ⟨hd.1, (neighbors_alternate x hodd hs).mp ho⟩⟩

end Mpfx
