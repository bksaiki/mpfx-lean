import Mpfx.Rounding.Op

/-!
# Standard special-value and overflow tables

`FiniteFormat.maxFinite`, the largest finite value of a bounded format, and the
standard `SpecialMap` / `OverflowMap` instances: `SpecialMap.exact`, `.saturate`,
`.toNaN`; `OverflowMap.ieee` (IEEE 754 §7.4), `.saturate`, `.toNaN`. The
saturating tables need a finite bound.
-/

namespace Mpfx

/-! ### The largest finite value -/

namespace FiniteFormat

/-- The largest value of a bounded `F`: the round-down of `b` on `F`'s grid. -/
noncomputable def maxFinite (F : FiniteFormat) (hb : F.b ≠ ⊤) : Dyadic :=
  rndUnbounded F .toNegative (((F.b.untop hb).val : Dyadic) : ℝ) (not_isUndefined_toNegative F)

private theorem maxFinite_spec (F : FiniteFormat) (hb : F.b ≠ ⊤) :
    RoundsFinite F.unbounded .toNegative (((F.b.untop hb).val : Dyadic) : ℝ)
      (F.maxFinite hb) :=
  rndUnbounded_satisfies _ _ _ _

theorem maxFinite_nonneg (F : FiniteFormat) (hb : F.b ≠ ⊤) :
    (0 : ℝ) ≤ (F.maxFinite hb : ℝ) :=
  RoundsFinite.toNegative_nonneg (nonneg_coe_real _) (F.maxFinite_spec hb)

theorem maxFinite_mem (F : FiniteFormat) (hb : F.b ≠ ⊤) : F.maxFinite hb ∈ F := by
  obtain ⟨hmem, hle, -⟩ := F.maxFinite_spec hb
  refine mem_of_mem_unbounded_of_boundOK hmem ?_
  rw [← WithTop.coe_untop F.b hb]
  exact boundOK_coe_of_abs_le (by rw [abs_of_nonneg (F.maxFinite_nonneg hb)]; exact hle)

/-- Every value of a bounded `F` is at most `maxFinite`. -/
theorem le_maxFinite (F : FiniteFormat) (hb : F.b ≠ ⊤) {v : Dyadic} (hv : v ∈ F) :
    (v : ℝ) ≤ (F.maxFinite hb : ℝ) := by
  obtain ⟨-, -, hmax⟩ := F.maxFinite_spec hb
  refine hmax v (mem_unbounded_of_mem hv) ?_
  have h := hv.2.2
  rw [← WithTop.coe_untop F.b hb] at h
  exact (le_abs_self _).trans (abs_coe_real_le_of_boundOK h)

/-- Every value of a bounded `F` is at most `maxFinite` in magnitude. -/
theorem abs_le_maxFinite (F : FiniteFormat) (hb : F.b ≠ ⊤) {v : Dyadic} (hv : v ∈ F) :
    |(v : ℝ)| ≤ (F.maxFinite hb : ℝ) := by
  refine abs_le.mpr ⟨?_, F.le_maxFinite hb hv⟩
  have h := F.le_maxFinite hb (neg_mem hv)
  rw [Dyadic.coe_real_neg] at h
  linarith

/-- `±maxFinite`, the saturated value of the given sign. -/
noncomputable def saturated (F : FiniteFormat) (hb : F.b ≠ ⊤) (negative : Bool) :
    WithSpecial Dyadic :=
  .finite (if negative then -F.maxFinite hb else F.maxFinite hb)

theorem saturated_mem (F : FiniteFormat) (hb : F.b ≠ ⊤) (negative : Bool) :
    F.saturated hb negative ∈ F.values := by
  cases negative
  · exact F.maxFinite_mem hb
  · exact neg_mem (F.maxFinite_mem hb)

/-- A value of magnitude `maxFinite` with sign `negative` is the saturated value. -/
theorem saturated_eq_finite (F : FiniteFormat) (hb : F.b ≠ ⊤) {negative : Bool} {w : Dyadic}
    (habs : |(w : ℝ)| = (F.maxFinite hb : ℝ))
    (hsign : (w : ℝ) ≠ 0 → decide ((w : ℚ) < 0) = negative) :
    F.saturated hb negative = .finite w := by
  have hq := (Dyadic.coe_real_lt_zero_iff w).symm
  unfold saturated
  congr 1
  apply (Dyadic.coe_real_inj _ _).mp
  rcases lt_trichotomy (w : ℝ) 0 with hw | hw | hw
  · obtain rfl : negative = true := by rw [← hsign hw.ne]; exact decide_eq_true (hq.mpr hw)
    rw [if_pos rfl, Dyadic.coe_real_neg, ← habs, abs_of_neg hw, neg_neg]
  · rw [hw, abs_zero] at habs
    split_ifs <;> simp [← habs, hw]
  · obtain rfl : negative = false := by
      rw [← hsign hw.ne']; exact decide_eq_false fun h => absurd (hq.mp h) (not_lt.mpr hw.le)
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← habs, abs_of_pos hw]

end FiniteFormat

/-! ### Standard tables -/

namespace SpecialMap

/-- Specials are exact (IEEE): every special input maps to itself. -/
def exact (F : Format) (h : ∀ s, s ∈ F.specials) : SpecialMap F :=
  ⟨.special, h⟩

@[simp] theorem exact_map (F : Format) (h : ∀ s, s ∈ F.specials) (s : Special) :
    (exact F h).map s = .special s := rfl

/-- Infinities saturate to `±maxFinite`; NaN stays NaN. -/
noncomputable def saturate (F : FiniteFormat) (hb : F.b ≠ ⊤)
    (hnan : Special.nan ∈ F.specials) : SpecialMap F.toFormat where
  map
    | .inf negative => F.saturated hb negative
    | .nan => .special .nan
  mem
    | .inf negative => F.saturated_mem hb negative
    | .nan => hnan

/-- Every special input becomes NaN. -/
def toNaN (F : Format) (hnan : Special.nan ∈ F.specials) : SpecialMap F :=
  ⟨fun _ => .special .nan, fun _ => hnan⟩

end SpecialMap

namespace OverflowMap

/-- IEEE 754 §7.4: nearest overflows to `±Inf`, toward-zero to `±maxFinite`,
directed modes to `±Inf` on their side and `±maxFinite` on the other. The
non-IEEE modes away-from-zero and round-to-odd overflow to `±Inf`. -/
noncomputable def ieee (F : FiniteFormat) (rm : RoundingMode) (hb : F.b ≠ ⊤)
    (hinf : ∀ negative, Special.inf negative ∈ F.specials) : OverflowMap F.toFormat where
  map negative :=
    match rm with
    | .toZero => F.saturated hb negative
    | .toPositive => if negative then F.saturated hb true else .special (.inf false)
    | .toNegative => if negative then .special (.inf true) else F.saturated hb false
    | .awayZero | .toOdd | .nearest _ => .special (.inf negative)
  mem negative := by
    cases rm <;> dsimp only <;> (try split) <;>
      first | exact F.saturated_mem hb _ | exact hinf _

/-- Overflow saturates to `±maxFinite`. -/
noncomputable def saturate (F : FiniteFormat) (hb : F.b ≠ ⊤) : OverflowMap F.toFormat :=
  ⟨F.saturated hb, F.saturated_mem hb⟩

/-- The IEEE RTZ table is the saturating one. -/
theorem ieee_toZero (F : FiniteFormat) (hb : F.b ≠ ⊤) (hinf) :
    OverflowMap.ieee F .toZero hb hinf = OverflowMap.saturate F hb := rfl

/-- Overflow becomes NaN. -/
def toNaN (F : Format) (hnan : Special.nan ∈ F.specials) : OverflowMap F :=
  ⟨fun _ => .special .nan, fun _ => hnan⟩

end OverflowMap

end Mpfx
