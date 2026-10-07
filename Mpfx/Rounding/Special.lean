import Mpfx.Rounding.Op

/-!
# Special-value and overflow tables

Where a format sends what `RoundsFinite` cannot express:

* `SpecialMap F` — the result of rounding a special input (±Inf, NaN);
* `OverflowMap F` — the result of an overflowing real, keyed by its sign.

Every entry is a value of `F` (`F.values`). `FiniteFormat.maxFinite` is the
largest finite value of a bounded format, the saturation target. Standard
tables: `SpecialMap.exact`, `.saturate`, `.toNaN`; `OverflowMap.ieee` (IEEE 754
§7.4), `.saturate`, `.toNaN`. The saturating tables need a finite bound.
-/

namespace Mpfx

/-! ### Negation -/

/-- Negation of a special value: infinities flip sign, NaN is fixed. -/
def Special.neg : Special → Special
  | .inf negative => .inf !negative
  | .nan => .nan

@[simp] theorem Special.neg_neg (s : Special) : s.neg.neg = s := by
  cases s <;> simp [Special.neg]

/-- Negation through `WithSpecial`. -/
def WithSpecial.neg {α : Type} [Neg α] : WithSpecial α → WithSpecial α
  | .finite a => .finite (-a)
  | .special s => .special s.neg

/-- `F`'s specials are closed under negation. -/
def Format.NegClosed (F : Format) : Prop := ∀ s ∈ F.specials, s.neg ∈ F.specials

theorem Format.neg_mem_values {F : Format} (hF : F.NegClosed) {v : WithSpecial Dyadic}
    (hv : v ∈ F.values) : v.neg ∈ F.values := by
  cases v with
  | finite d => exact Format.neg_mem (F := F) hv
  | special s => exact hF s hv

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
    (0 : ℝ) ≤ (F.maxFinite hb : ℝ) := by
  obtain ⟨-, -, hmax⟩ := F.maxFinite_spec hb
  have h := hmax 0 F.unbounded.zero_mem
    (by rw [Dyadic.coe_real_zero]; exact nonneg_coe_real _)
  rwa [Dyadic.coe_real_zero] at h

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

/-- `±maxFinite`, the saturated value of the given sign. -/
noncomputable def saturated (F : FiniteFormat) (hb : F.b ≠ ⊤) (negative : Bool) :
    WithSpecial Dyadic :=
  .finite (if negative then -F.maxFinite hb else F.maxFinite hb)

theorem saturated_mem (F : FiniteFormat) (hb : F.b ≠ ⊤) (negative : Bool) :
    F.saturated hb negative ∈ F.values := by
  cases negative
  · exact F.maxFinite_mem hb
  · exact neg_mem (F.maxFinite_mem hb)

end FiniteFormat

/-! ### The tables -/

/-- Where special inputs go. -/
structure SpecialMap (F : Format) where
  map : Special → WithSpecial Dyadic
  mem : ∀ s, map s ∈ F.values

/-- Where overflow goes, keyed by `negative`. -/
structure OverflowMap (F : Format) where
  map : Bool → WithSpecial Dyadic
  mem : ∀ negative, map negative ∈ F.values

namespace SpecialMap

/-- Specials are exact (IEEE): every special input maps to itself. -/
def exact (F : Format) (h : ∀ s, s ∈ F.specials) : SpecialMap F :=
  ⟨.special, h⟩

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

/-- The table for the negated input: `(O.neg).map b = -(O.map (!b))`. -/
def neg {F : Format} (hF : F.NegClosed) (O : OverflowMap F) : OverflowMap F :=
  ⟨fun negative => (O.map !negative).neg, fun _ => Format.neg_mem_values hF (O.mem _)⟩

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

/-- Overflow becomes NaN. -/
def toNaN (F : Format) (hnan : Special.nan ∈ F.specials) : OverflowMap F :=
  ⟨fun _ => .special .nan, fun _ => hnan⟩

end OverflowMap

end Mpfx
