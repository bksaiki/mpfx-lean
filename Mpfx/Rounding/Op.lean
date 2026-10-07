import Mpfx.Rounding.Op.Defs
import Mpfx.Rounding.Op.Directed
import Mpfx.Rounding.Op.ToOdd
import Mpfx.Rounding.Op.Nearest

/-!
# The rounding function, assembled

The mode dispatcher `rndUnbounded_satisfies`, its uniqueness counterpart, the
overflow dichotomy `overflows_iff_not_roundsInBound`, the bridge
`rnd_iff_rounds` tying `rnd` to the relational spec `Rounds`, and how special
inputs and overflow come out of `rnd` (`rnd_special`, `rnd_of_overflows_pos`/`_neg`).
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

/-- `rnd` on a real, read off any witness of the unbounded rounding. -/
theorem rnd_finite_of_roundsFinite {F : FiniteFormat} {S : SpecialMap F.toFormat}
    {O : OverflowMap F.toFormat} {rm : RoundingMode} {x : ℝ} {y : Dyadic}
    (h : ¬ F.IsUndefined rm) (hy : RoundsFinite F.unbounded rm x y) :
    rnd F S O rm (.finite x) =
      if Format.boundOK F.b y then .value (.finite y)
      else .value (O.map (decide ((y : ℚ) < 0))) := by
  rw [rndUnbounded_unique F rm x h hy]
  simp only [rnd, dif_neg h]

/-! ### Special inputs and overflow through `rnd` -/

@[simp] theorem rnd_special (F : FiniteFormat) (S : SpecialMap F.toFormat)
    (O : OverflowMap F.toFormat) (rm : RoundingMode) (s : Special) :
    rnd F S O rm (.special s) = .value (S.map s) := rfl

/-- A positive overflow selects the table's positive entry. -/
theorem rnd_of_overflows_pos {F : FiniteFormat} {S : SpecialMap F.toFormat}
    {O : OverflowMap F.toFormat} {rm : RoundingMode} {x : ℝ}
    (h : ¬ F.IsUndefined rm) (hov : Overflows F rm x) (hx : 0 < x) :
    rnd F S O rm (.finite x) = .value (O.map false) := by
  obtain ⟨y, hy, hnb⟩ := hov
  have hy0 : (0 : ℝ) ≤ (y : ℝ) := by
    rcases isFaithfulRound_iff_directed.mp hy.isFaithfulRound with hd | hu
    · exact RoundsFinite.toNegative_nonneg hx.le hd
    · exact hx.le.trans hu.2.1
  have hneg : decide ((y : ℚ) < 0) = false := by
    rw [decide_eq_false_iff_not, not_lt]
    rw [Dyadic.coe_real_eq_ratCast] at hy0
    exact_mod_cast hy0
  rw [rnd_iff_rounds]
  exact ⟨h, y, hy, Or.inr ⟨hnb, by rw [hneg]⟩⟩

/-- A negative overflow selects the table's negative entry. -/
theorem rnd_of_overflows_neg {F : FiniteFormat} {S : SpecialMap F.toFormat}
    {O : OverflowMap F.toFormat} {rm : RoundingMode} {x : ℝ}
    (h : ¬ F.IsUndefined rm) (hov : Overflows F rm x) (hx : x < 0) :
    rnd F S O rm (.finite x) = .value (O.map true) := by
  obtain ⟨y, hy, hnb⟩ := hov
  have hy0 : (y : ℝ) ≤ 0 := by
    rcases isFaithfulRound_iff_directed.mp hy.isFaithfulRound with hd | hu
    · exact hd.2.1.trans hx.le
    · exact RoundsFinite.toPositive_nonpos hx.le hu
  have hne : (y : ℝ) ≠ 0 := by
    intro h0
    apply hnb
    rw [show y = 0 from Subtype.ext (by
      rw [Dyadic.coe_real_eq_ratCast] at h0; exact_mod_cast h0)]
    exact Format.boundOK_zero _
  have hpos : decide ((y : ℚ) < 0) = true := by
    rw [decide_eq_true_iff]
    have h' : (y : ℝ) < 0 := lt_of_le_of_ne hy0 hne
    rw [Dyadic.coe_real_eq_ratCast] at h'
    exact_mod_cast h'
  rw [rnd_iff_rounds]
  exact ⟨h, y, hy, Or.inr ⟨hnb, by rw [hpos]⟩⟩

end Mpfx
