import Mpfx.Rounding.Op.Defs
import Mpfx.Rounding.Op.Directed
import Mpfx.Rounding.Op.ToOdd
import Mpfx.Rounding.Op.Nearest

/-!
# The rounding function, assembled

The mode dispatcher `rndUnbounded_satisfies`, its uniqueness counterpart, the
overflow dichotomy `overflows_iff_not_roundsInBound`, and the bridge
`rnd_iff_rounds` tying `rnd` to the relational spec `Rounds`.
-/

namespace Mpfx

attribute [local instance] Classical.propDecidable

/-- `rndUnbounded` satisfies the unbounded rounding spec. -/
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


/-- Any `y` satisfying the spec equals `rndUnbounded F rm x h`. -/
theorem rndUnbounded_unique (F : FiniteFormat) (rm : RoundingMode) (x : ℝ)
    (h : ¬ F.IsUndefined rm) {y : Dyadic}
    (hy : RoundsFinite F.unbounded rm x y) :
    y = rndUnbounded F rm x h :=
  RoundsFinite.unique h hy (rndUnbounded_satisfies F rm x h)

/-- For a defined mode, a real either overflows or rounds within the bound. -/
theorem overflows_iff_not_roundsInBound {F : FiniteFormat} {rm : RoundingMode} {x : ℝ}
    (h : ¬ F.IsUndefined rm) : Overflows F rm x ↔ ¬ ∃ y, RoundsInBound F rm x y := by
  constructor
  · rintro ⟨y, hy, hnb⟩ ⟨y', hy', hb⟩
    exact hnb (RoundsFinite.unique h hy' hy ▸ hb)
  · intro hn
    refine ⟨rndUnbounded F rm x h, rndUnbounded_satisfies F rm x h, fun hb => hn ?_⟩
    exact ⟨_, rndUnbounded_satisfies F rm x h, hb⟩

/-! ### Bridge lemma -/

theorem rnd_iff_rounds (F : FiniteFormat) (S : SpecialMap F.toFormat)
    (O : OverflowMap F.toFormat) (rm : RoundingMode) (v : WithSpecial ℝ) (r : RoundResult) :
    rnd F S O rm v = r ↔ Rounds F S O rm v r := by
  cases v with
  | special s => exact eq_comm
  | finite x =>
    cases r with
    | undefined =>
      change rnd F S O rm (.finite x) = .undefined ↔ F.IsUndefined rm
      constructor
      · intro h_eq
        by_contra h_undef
        simp only [rnd, dif_neg h_undef] at h_eq
        split_ifs at h_eq
      · intro h_undef
        simp only [rnd, dif_pos h_undef]
    | value w =>
      change rnd F S O rm (.finite x) = .value w ↔ ¬ F.IsUndefined rm ∧ ∃ y,
        RoundsFinite F.unbounded rm x y ∧
          ((Format.boundOK F.b y ∧ w = .finite y) ∨
           (¬ Format.boundOK F.b y ∧ w = O.map (decide ((y : ℚ) < 0))))
      constructor
      · intro h_eq
        have h_undef : ¬ F.IsUndefined rm := by
          intro h
          simp only [rnd, dif_pos h] at h_eq
          exact RoundResult.noConfusion h_eq
        refine ⟨h_undef, rndUnbounded F rm x h_undef,
          rndUnbounded_satisfies F rm x h_undef, ?_⟩
        simp only [rnd, dif_neg h_undef] at h_eq
        split_ifs at h_eq with hb
        · exact Or.inl ⟨hb, (RoundResult.value.inj h_eq).symm⟩
        · exact Or.inr ⟨hb, (RoundResult.value.inj h_eq).symm⟩
      · rintro ⟨h_undef, y, hRF, h⟩
        obtain rfl := rndUnbounded_unique F rm x h_undef hRF
        simp only [rnd, dif_neg h_undef]
        rcases h with ⟨hb, rfl⟩ | ⟨hb, rfl⟩
        · rw [if_pos hb]
        · rw [if_neg hb]

end Mpfx
