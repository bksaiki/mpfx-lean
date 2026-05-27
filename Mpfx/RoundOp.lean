import Mpfx.RoundOp.Defs
import Mpfx.RoundOp.Directed
import Mpfx.RoundOp.ToOdd
import Mpfx.RoundOp.Nearest

/-!
# Constructive rounding function

The noncomputable layer of the rounding architecture, aggregated from
`Mpfx/RoundOp/`. Provides the function `rnd` (in `Defs`), the per-mode
soundness/uniqueness proofs (in `Directed`/`ToOdd`/`Nearest`), the
mode dispatchers `rndUnbounded_satisfies`/`rndUnbounded_unique`, and the
bridge lemma `rnd_iff_rounds` connecting `rnd` to the relational spec
`Rounds` from `Mpfx/Rounding.lean`.
-/

namespace Mpfx

attribute [local instance] Classical.propDecidable

/-- The constructive `rndUnbounded` satisfies the unbounded rounding spec. -/
theorem rndUnbounded_satisfies (F : FiniteFormat) (rm : RoundingMode) (x : ℝ)
    (h : ¬ F.IsUndefined rm) :
    RoundsFinite F.unbounded rm x (rndUnbounded F rm x h) := by
  cases rm with
  | toNegative => exact rndUnbounded_satisfies_toNegative F x h
  | toPositive => exact rndUnbounded_satisfies_toPositive F x h
  | toZero => exact rndUnbounded_satisfies_toZero F x h
  | awayZero => exact rndUnbounded_satisfies_awayZero F x h
  | toOdd => exact rndUnbounded_satisfies_toOdd F x h
  | nearest tb => exact rndUnbounded_satisfies_nearest F tb x h


/-- Uniqueness: any `y` satisfying the unbounded rounding spec equals
`rndUnbounded F rm x h`. -/
theorem rndUnbounded_unique (F : FiniteFormat) (rm : RoundingMode) (x : ℝ)
    (h : ¬ F.IsUndefined rm) {y : Dyadic}
    (hy : RoundsFinite F.unbounded rm x y) :
    y = rndUnbounded F rm x h := by
  cases rm with
  | toNegative => exact rndUnbounded_unique_toNegative F x h hy
  | toPositive => exact rndUnbounded_unique_toPositive F x h hy
  | toZero => exact rndUnbounded_unique_toZero F x h hy
  | awayZero => exact rndUnbounded_unique_awayZero F x h hy
  | toOdd => exact rndUnbounded_unique_toOdd F x h hy
  | nearest tb => exact rndUnbounded_unique_nearest F tb x h hy

/-! ### Bridge lemma

The `RoundResult`-typed `Rounds` collapses the per-mode bridges to one
uniform statement: `rnd` and `Rounds` agree on the same `RoundResult`. -/

theorem rnd_iff_rounds (F : FiniteFormat) (rm : RoundingMode) (x : ℝ) (r : RoundResult) :
    rnd F rm x = r ↔ Rounds F rm x r := by
  cases r with
  | undefined =>
    -- `Rounds F rm x .undefined` reduces to `F.IsUndefined rm` by definition.
    -- `rnd F rm x = .undefined` is true iff the outer `if` of `rnd` fires,
    -- i.e., iff `F.IsUndefined rm` holds.
    change rnd F rm x = .undefined ↔ F.IsUndefined rm
    constructor
    · intro h_eq
      by_contra h_undef
      unfold rnd at h_eq
      rw [dif_neg h_undef] at h_eq
      -- `let y := rndUnbounded ...; if boundOK ... then .finite y else .overflow`
      -- doesn't auto-reduce; force it with `dsimp only` so `split_ifs`
      -- can see the inner conditional and decompose to constructor-mismatch.
      dsimp only at h_eq
      split_ifs at h_eq
    · intro h_undef
      unfold rnd
      rw [dif_pos h_undef]
  | overflow b =>
    change rnd F rm x = .overflow b ↔
      ¬ F.IsUndefined rm ∧
      ∃ y, RoundsFinite F.unbounded rm x y ∧ ¬ Format.boundOK F.b y ∧
           (b ↔ (0 : ℚ) < (y : ℚ))
    constructor
    · intro h_eq
      have h_undef : ¬ F.IsUndefined rm := by
        intro h
        unfold rnd at h_eq
        rw [dif_pos h] at h_eq
        exact RoundResult.noConfusion h_eq
      refine ⟨h_undef, rndUnbounded F rm x h_undef,
              rndUnbounded_satisfies F rm x h_undef, ?_, ?_⟩
      · intro hb
        unfold rnd at h_eq
        rw [dif_neg h_undef] at h_eq
        dsimp only at h_eq
        rw [if_pos hb] at h_eq
        exact RoundResult.noConfusion h_eq
      · unfold rnd at h_eq
        rw [dif_neg h_undef] at h_eq
        dsimp only at h_eq
        split_ifs at h_eq with hb hpos
        · injection h_eq with hb_eq
          subst hb_eq
          exact ⟨fun _ => hpos, fun _ => rfl⟩
        · injection h_eq with hb_eq
          subst hb_eq
          exact ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd h hpos⟩
    · rintro ⟨h_undef, y, hRF, hBN, hSign⟩
      have h_y_eq : y = rndUnbounded F rm x h_undef :=
        rndUnbounded_unique F rm x h_undef hRF
      unfold rnd
      rw [dif_neg h_undef]
      dsimp only
      rw [if_neg (h_y_eq ▸ hBN)]
      congr 1
      by_cases hpos : (0 : ℚ) < (rndUnbounded F rm x h_undef : ℚ)
      · rw [if_pos hpos]
        have hy_pos : (0 : ℚ) < (y : ℚ) := h_y_eq ▸ hpos
        exact (hSign.mpr hy_pos).symm
      · rw [if_neg hpos]
        have hy_npos : ¬ (0 : ℚ) < (y : ℚ) := fun h => hpos (h_y_eq ▸ h)
        cases hb : b
        · rfl
        · exfalso
          exact hy_npos (hSign.mp (by rw [hb]))
  | finite y =>
    change rnd F rm x = .finite y ↔
      ¬ F.IsUndefined rm ∧
      RoundsFinite F.unbounded rm x y ∧ Format.boundOK F.b y
    constructor
    · -- Forward: rnd = .finite y ⇒ ⟨h_undef, RoundsFinite y, boundOK y⟩.
      -- Reading off `rnd`'s `if`s: the equation pins y = rndUnbounded ... and
      -- the bound check succeeded.
      intro h_eq
      have h_undef : ¬ F.IsUndefined rm := by
        intro h
        unfold rnd at h_eq
        rw [dif_pos h] at h_eq
        exact RoundResult.noConfusion h_eq
      unfold rnd at h_eq
      rw [dif_neg h_undef] at h_eq
      dsimp only at h_eq
      split_ifs at h_eq with hb
      · have h_y_eq : rndUnbounded F rm x h_undef = y := by injection h_eq
        refine ⟨h_undef, ?_, ?_⟩
        · rw [← h_y_eq]; exact rndUnbounded_satisfies F rm x h_undef
        · rw [← h_y_eq]; exact hb
    · -- Reverse: ⟨h_undef, RoundsFinite y, boundOK y⟩ ⇒ rnd = .finite y.
      -- By uniqueness, y = rndUnbounded; the bound check succeeds.
      rintro ⟨h_undef, hRF, hBOK⟩
      have h_y_eq : y = rndUnbounded F rm x h_undef :=
        rndUnbounded_unique F rm x h_undef hRF
      unfold rnd
      rw [dif_neg h_undef]
      dsimp only
      rw [if_pos (h_y_eq ▸ hBOK)]
      exact congrArg _ h_y_eq.symm

end Mpfx
