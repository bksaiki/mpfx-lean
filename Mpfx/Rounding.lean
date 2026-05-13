import Mpfx.Containment
import Mpfx.Digits

/-!
# Rounding modes and the rounding function

§3.2 of the paper defines five IEEE 754 rounding modes plus two extras (RAZ, RTO).
For our analysis (§5.2) we focus on `RTZ`, `RAZ`, `RTO`, and `RNE`, since RTP/RTN
collapse to RAZ/RTZ depending on sign and RNA differs from RNE only in tiebreaking.
-/

namespace Mpfx

/-- Tie-break for nearest rounding modes.

* `ToEven` — ties to the value with even significand parity.
* `AwayZero` — ties to the value with larger magnitude.
-/
inductive TieBreak
  | ToEven : TieBreak
  | AwayZero : TieBreak
deriving DecidableEq, Repr

/-- Rounding modes. Five IEEE 754 modes plus the paper's auxiliary RTO mode.

* `Nearest .ToEven` — round to nearest, ties to even (RNE).
* `Nearest .AwayZero` — round to nearest, ties away from zero (RNA).
* `ToZero` — round towards zero / truncate (RTZ).
* `AwayZero` — round away from zero (RAZ).
* `ToPositive` — round towards plus infinity (RTP / round-up).
* `ToNegative` — round towards minus infinity (RTN / round-down).
* `ToOdd` — round to the value with odd significand (RTO; not IEEE).
-/
inductive RoundingMode
  | Nearest (tieBreak : TieBreak)
  | ToZero : RoundingMode
  | AwayZero : RoundingMode
  | ToNegative : RoundingMode
  | ToPositive : RoundingMode
  | ToOdd : RoundingMode
deriving DecidableEq, Repr

/-- A rounding mode is *sign-symmetric* if rounding under it commutes with
negation (`Rounds F rm x y ↔ Rounds F rm (-x) (-y)`). The directed modes
`ToPositive`/`ToNegative` are not sign-symmetric (they're each other's
negation-duals); all other modes are. -/
def RoundingMode.IsSymmetric : RoundingMode → Prop
  | .Nearest _ => True
  | .ToZero => True
  | .AwayZero => True
  | .ToOdd => True
  | .ToPositive => False
  | .ToNegative => False

instance (rm : RoundingMode) : Decidable rm.IsSymmetric :=
  match rm with
  | .Nearest _ => instDecidableTrue
  | .ToZero => instDecidableTrue
  | .AwayZero => instDecidableTrue
  | .ToOdd => instDecidableTrue
  | .ToPositive => instDecidableFalse
  | .ToNegative => instDecidableFalse

namespace AbstractFormat

/-- `y = RTN-rounding of x in F` (round towards minus infinity) — i.e., `y` is
the largest element of `F` with `(y : ℝ) ≤ x`. This is the building block for
`RTZ` (when `x ≥ 0`) and `RTN`. -/
def RoundsRTN (F : AbstractFormat) (x : ℝ) (y : Dyadic) : Prop :=
  y ∈ F ∧ (y : ℝ) ≤ x ∧ ∀ z : Dyadic, z ∈ F → (z : ℝ) ≤ x → (z : ℝ) ≤ (y : ℝ)

/-- `y = RTP-rounding of x in F` (round towards plus infinity) — i.e., `y` is
the smallest element of `F` with `x ≤ (y : ℝ)`. -/
def RoundsRTP (F : AbstractFormat) (x : ℝ) (y : Dyadic) : Prop :=
  y ∈ F ∧ x ≤ (y : ℝ) ∧ ∀ z : Dyadic, z ∈ F → x ≤ (z : ℝ) → (y : ℝ) ≤ (z : ℝ)

/-- `y = RTZ-rounding of x in F` — round towards zero. For `x ≥ 0` this is
round-down to a non-negative element; for `x ≤ 0` it is round-up to a
non-positive element. -/
def RoundsRTZ (F : AbstractFormat) (x : ℝ) (y : Dyadic) : Prop :=
  y ∈ F ∧ |(y : ℝ)| ≤ |x| ∧ (y : ℝ) * x ≥ 0 ∧
  ∀ z : Dyadic, z ∈ F → |(z : ℝ)| ≤ |x| → (z : ℝ) * x ≥ 0 → |(z : ℝ)| ≤ |(y : ℝ)|

/-- `y = RAZ-rounding of x in F` — round away from zero. -/
def RoundsRAZ (F : AbstractFormat) (x : ℝ) (y : Dyadic) : Prop :=
  y ∈ F ∧ |x| ≤ |(y : ℝ)| ∧ (y : ℝ) * x ≥ 0 ∧
  ∀ z : Dyadic, z ∈ F → |x| ≤ |(z : ℝ)| → (z : ℝ) * x ≥ 0 → |(y : ℝ)| ≤ |(z : ℝ)|

/-- `y = RTO-rounding of x in F` — round to odd. The result `y ∈ F` is either
the round-down (`RoundsRTN`) or round-up (`RoundsRTP`) of `x`, and when `x` is
not exactly equal to `y`, the parity of `y` (in the `IsOdd F` sense) is odd:
parity is at precision `numDigits F.p F.exp y` and discriminated by `F.p` (odd
significand for `F.p ≥ 2`, odd exponent for `F.p = 1`). -/
def RoundsRTO (F : AbstractFormat) (x : ℝ) (y : Dyadic) : Prop :=
  y ∈ F ∧
  (RoundsRTN F x y ∨ RoundsRTP F x y) ∧
  (x ≠ (y : ℝ) → IsOdd F y)

/-- `y = RNE-rounding of x in F` — round to nearest, ties to even. The result
`y ∈ F` is one of the two adjacents bracketing `x`, chosen as the closer one;
ties (when `x` is exactly halfway between the two adjacents) are broken by
picking the value with `IsEven F` parity. -/
def RoundsRNE (F : AbstractFormat) (x : ℝ) (y : Dyadic) : Prop :=
  y ∈ F ∧
  (RoundsRTN F x y ∨ RoundsRTP F x y) ∧
  -- `y` is at least as close to `x` as any other adjacent
  (∀ z : Dyadic, z ∈ F → (RoundsRTN F x z ∨ RoundsRTP F x z) →
    |x - (y : ℝ)| ≤ |x - (z : ℝ)|) ∧
  -- Tie-break: if `x` is equidistant from `y` and another adjacent, `y` is even
  ((∃ z : Dyadic, z ∈ F ∧ (RoundsRTN F x z ∨ RoundsRTP F x z) ∧
      z ≠ y ∧ |x - (y : ℝ)| = |x - (z : ℝ)|) →
    IsEven F y)

/-- `y = RNA-rounding of x in F` — round to nearest, ties away from zero
(picking the value with the larger magnitude). Same shape as `RoundsRNE`
except the tie-break clause requires `|z| ≤ |y|` instead of `IsEven F y`. -/
def RoundsRNA (F : AbstractFormat) (x : ℝ) (y : Dyadic) : Prop :=
  y ∈ F ∧
  (RoundsRTN F x y ∨ RoundsRTP F x y) ∧
  (∀ z : Dyadic, z ∈ F → (RoundsRTN F x z ∨ RoundsRTP F x z) →
    |x - (y : ℝ)| ≤ |x - (z : ℝ)|) ∧
  (∀ z : Dyadic, z ∈ F → (RoundsRTN F x z ∨ RoundsRTP F x z) →
      z ≠ y → |x - (y : ℝ)| = |x - (z : ℝ)| → |(z : ℝ)| ≤ |(y : ℝ)|)

/-- Unified rounding relation: `Rounds F rm x y` holds iff `y` is the
`rm`-rounding of `x` in `F`. Dispatches to the per-mode predicate; useful
for stating mode-generic theorems. -/
def Rounds (F : AbstractFormat) (rm : RoundingMode) (x : ℝ) (y : Dyadic) : Prop :=
  match rm with
  | .Nearest .ToEven => RoundsRNE F x y
  | .Nearest .AwayZero => RoundsRNA F x y
  | .ToZero => RoundsRTZ F x y
  | .AwayZero => RoundsRAZ F x y
  | .ToNegative => RoundsRTN F x y
  | .ToPositive => RoundsRTP F x y
  | .ToOdd => RoundsRTO F x y

@[simp] theorem Rounds_nearest_toEven (F : AbstractFormat) (x : ℝ) (y : Dyadic) :
    Rounds F (.Nearest .ToEven) x y ↔ RoundsRNE F x y := Iff.rfl

@[simp] theorem Rounds_nearest_AwayZero (F : AbstractFormat) (x : ℝ) (y : Dyadic) :
    Rounds F (.Nearest .AwayZero) x y ↔ RoundsRNA F x y := Iff.rfl

@[simp] theorem Rounds_toZero (F : AbstractFormat) (x : ℝ) (y : Dyadic) :
    Rounds F .ToZero x y ↔ RoundsRTZ F x y := Iff.rfl

@[simp] theorem Rounds_awayZero (F : AbstractFormat) (x : ℝ) (y : Dyadic) :
    Rounds F .AwayZero x y ↔ RoundsRAZ F x y := Iff.rfl

@[simp] theorem Rounds_toNegative (F : AbstractFormat) (x : ℝ) (y : Dyadic) :
    Rounds F .ToNegative x y ↔ RoundsRTN F x y := Iff.rfl

@[simp] theorem Rounds_toPositive (F : AbstractFormat) (x : ℝ) (y : Dyadic) :
    Rounds F .ToPositive x y ↔ RoundsRTP F x y := Iff.rfl

@[simp] theorem Rounds_toOdd (F : AbstractFormat) (x : ℝ) (y : Dyadic) :
    Rounds F .ToOdd x y ↔ RoundsRTO F x y := Iff.rfl

/-- For `0 ≤ x`, RTP (smallest F-element ≥ x) coincides with RAZ
(smallest F-element with `|y| ≥ |x|` on x's side). -/
theorem RoundsRTP_iff_RAZ_of_nn {F : AbstractFormat} {x : ℝ} {y : Dyadic}
    (hx : 0 ≤ x) : Rounds F .ToPositive x y ↔ Rounds F .AwayZero x y := by
  constructor
  · rintro ⟨hyF, hxy, hmin⟩
    have hy_nn : 0 ≤ (y : ℝ) := le_trans hx hxy
    refine ⟨hyF, ?_, ?_, ?_⟩
    · rw [abs_of_nonneg hx, abs_of_nonneg hy_nn]; exact hxy
    · nlinarith
    · intro z hzF hxz hzx
      -- |x| ≤ |z| means x ≤ |z|. We want |y| ≤ |z|, i.e. y ≤ |z|.
      -- z * x ≥ 0 with x ≥ 0: either x = 0 (any z works for the sign) or z ≥ 0.
      by_cases hz_nn : 0 ≤ (z : ℝ)
      · -- z ≥ 0, so |z| = z and |x| = x
        have habs_z : |(z : ℝ)| = (z : ℝ) := abs_of_nonneg hz_nn
        have habs_x : |x| = x := abs_of_nonneg hx
        have habs_y : |(y : ℝ)| = (y : ℝ) := abs_of_nonneg hy_nn
        rw [habs_z, habs_x] at hxz
        have h_yz : (y : ℝ) ≤ (z : ℝ) := hmin z hzF hxz
        rw [habs_y, habs_z]; exact h_yz
      · -- z < 0. Then z * x ≥ 0 with x ≥ 0 forces x = 0, then y = 0 (smallest F-elt ≥ 0).
        push Not at hz_nn
        have hx_zero : x = 0 := by nlinarith
        have h0 : (y : ℝ) ≤ ((0 : Dyadic) : ℝ) := by
          apply hmin 0 F.zero_mem; rw [hx_zero]; rfl
        have hy0 : (y : ℝ) = 0 :=
          le_antisymm (by simpa using h0) (by rw [← hx_zero]; exact hxy)
        rw [hy0, abs_zero]
        exact abs_nonneg ((z : Dyadic) : ℝ)
  · rintro ⟨hyF, hxy, hsign, hmin⟩
    have hy_nn : 0 ≤ (y : ℝ) := by
      -- y * x ≥ 0 and x ≥ 0; either x = 0 (then |y| ≥ 0 only forces y ≠ 0... no) or y ≥ 0
      by_cases hx0 : x = 0
      · -- Need: y ≥ 0. From |x| ≤ |y| we get 0 ≤ |y|; we also need sign.
        -- Actually: with x = 0, y * 0 = 0 ≥ 0 trivially; we don't know y's sign.
        -- But the universal property: for z = 0, |x| = 0 ≤ |0| = 0 ✓, 0 * 0 = 0 ≥ 0 ✓,
        -- so |y| ≤ |0| = 0, forcing y = 0.
        have h0 : |(y : ℝ)| ≤ |((0 : Dyadic) : ℝ)| :=
          hmin 0 F.zero_mem (by rw [hx0]; simp) (by simp)
        have : |(y : ℝ)| = 0 := le_antisymm (by simpa using h0) (abs_nonneg _)
        have hy0 : (y : ℝ) = 0 := abs_eq_zero.mp this
        rw [hy0]
      · have hx_pos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
        nlinarith
    refine ⟨hyF, ?_, ?_⟩
    · rw [abs_of_nonneg hx, abs_of_nonneg hy_nn] at hxy; exact hxy
    · intro z hzF hxz
      have hz_nn : 0 ≤ (z : ℝ) := le_trans hx hxz
      have h1 : |x| ≤ |(z : ℝ)| := by
        rw [abs_of_nonneg hx, abs_of_nonneg hz_nn]; exact hxz
      have h2 : (z : ℝ) * x ≥ 0 := mul_nonneg hz_nn hx
      have key := hmin z hzF h1 h2
      rw [abs_of_nonneg hy_nn, abs_of_nonneg hz_nn] at key
      exact key

/-- For `x ≤ 0`, RTP (smallest F-element ≥ x) coincides with RTZ
(largest F-element on x's side with magnitude ≤ |x|). -/
theorem RoundsRTP_iff_RTZ_of_nonpos {F : AbstractFormat} {x : ℝ} {y : Dyadic}
    (hx : x ≤ 0) : Rounds F .ToPositive x y ↔ Rounds F .ToZero x y := by
  constructor
  · rintro ⟨hyF, hxy, hmin⟩
    -- For x ≤ 0, smallest F-elt ≥ x. Claim: y ≤ 0 since 0 ∈ F is ≥ x, so y ≤ 0.
    have hy_nonpos : (y : ℝ) ≤ 0 := by
      have := hmin 0 F.zero_mem hx
      simpa using this
    refine ⟨hyF, ?_, ?_, ?_⟩
    · rw [abs_of_nonpos hy_nonpos, abs_of_nonpos hx]; linarith
    · -- y * x ≥ 0 from y ≤ 0 and x ≤ 0
      nlinarith
    · intro z hzF hzx hzsign
      -- |z| ≤ |x| and z * x ≥ 0. With x ≤ 0, want |z| ≤ |y|.
      by_cases hz_nonpos : (z : ℝ) ≤ 0
      · -- z ≤ 0. Then |z| = -z, |x| = -x, so -z ≤ -x, i.e., x ≤ z.
        have habs_z : |(z : ℝ)| = -(z : ℝ) := abs_of_nonpos hz_nonpos
        have habs_x : |x| = -x := abs_of_nonpos hx
        have habs_y : |(y : ℝ)| = -(y : ℝ) := abs_of_nonpos hy_nonpos
        rw [habs_z, habs_x] at hzx
        have hxz : x ≤ (z : ℝ) := by linarith
        have h_yz : (y : ℝ) ≤ (z : ℝ) := hmin z hzF hxz
        rw [habs_z, habs_y]; linarith
      · -- z > 0. With x ≤ 0, z * x ≥ 0 forces x = 0; then |z| ≤ 0 gives z = 0
        -- — contradicting z > 0.
        push Not at hz_nonpos
        have hx_zero : x = 0 := by nlinarith
        have habs_x_zero : |x| = 0 := by rw [hx_zero, abs_zero]
        rw [habs_x_zero] at hzx
        have hz_zero_abs : |(z : ℝ)| = 0 := le_antisymm hzx (abs_nonneg (z : ℝ))
        have hz_zero : (z : ℝ) = 0 := abs_eq_zero.mp hz_zero_abs
        linarith
  · rintro ⟨hyF, hbnd, hsign, hmax⟩
    -- y ≤ 0: from |y| ≤ |x|, sign y * x ≥ 0, x ≤ 0
    have hy_nonpos : (y : ℝ) ≤ 0 := by
      by_cases hx0 : x = 0
      · -- Then |y| ≤ 0, so y = 0
        have habs_x : |x| = 0 := by rw [hx0, abs_zero]
        rw [habs_x] at hbnd
        have : |(y : ℝ)| = 0 := le_antisymm hbnd (abs_nonneg _)
        have : (y : ℝ) = 0 := abs_eq_zero.mp this
        linarith
      · have hx_neg : x < 0 := lt_of_le_of_ne hx hx0
        nlinarith
    refine ⟨hyF, ?_, ?_⟩
    · -- x ≤ y: |y| ≤ |x| with both nonpos gives -y ≤ -x, i.e., x ≤ y
      rw [abs_of_nonpos hy_nonpos, abs_of_nonpos hx] at hbnd
      linarith
    · intro z hzF hxz
      -- z ≥ x. Want y ≤ z. We use the maximality property in RTZ flavor.
      by_cases hz_nonpos : (z : ℝ) ≤ 0
      · -- z ≤ 0; |z| ≤ |x|; z * x ≥ 0
        have h1 : |(z : ℝ)| ≤ |x| := by
          rw [abs_of_nonpos hz_nonpos, abs_of_nonpos hx]; linarith
        have h2 : (z : ℝ) * x ≥ 0 := by nlinarith
        have key := hmax z hzF h1 h2
        rw [abs_of_nonpos hy_nonpos, abs_of_nonpos hz_nonpos] at key
        linarith
      · push Not at hz_nonpos
        linarith

/-- For `0 ≤ x`, RTN (largest F-element ≤ x) coincides with RTZ
(largest F-element on x's side with magnitude ≤ |x|). -/
theorem RoundsRTN_iff_RTZ_of_nn {F : AbstractFormat} {x : ℝ} {y : Dyadic}
    (hx : 0 ≤ x) : Rounds F .ToNegative x y ↔ Rounds F .ToZero x y := by
  constructor
  · rintro ⟨hyF, hyx, hmax⟩
    -- Largest F-elt ≤ x with x ≥ 0; 0 ∈ F is ≤ x so y ≥ 0.
    have hy_nn : 0 ≤ (y : ℝ) := by
      have := hmax 0 F.zero_mem hx
      simpa using this
    refine ⟨hyF, ?_, ?_, ?_⟩
    · rw [abs_of_nonneg hx, abs_of_nonneg hy_nn]; exact hyx
    · nlinarith
    · intro z hzF hzx hzsign
      by_cases hz_nn : 0 ≤ (z : ℝ)
      · have habs_z : |(z : ℝ)| = (z : ℝ) := abs_of_nonneg hz_nn
        have habs_x : |x| = x := abs_of_nonneg hx
        have habs_y : |(y : ℝ)| = (y : ℝ) := abs_of_nonneg hy_nn
        rw [habs_z, habs_x] at hzx
        have h_zy : (z : ℝ) ≤ (y : ℝ) := hmax z hzF hzx
        rw [habs_z, habs_y]; exact h_zy
      · push Not at hz_nn
        -- z < 0. z * x ≥ 0 with x ≥ 0 forces x = 0.
        have hx_zero : x = 0 := by nlinarith
        -- |z| ≤ |x| = 0 forces z = 0, contradicting z < 0.
        have habs_x : |x| = 0 := by rw [hx_zero, abs_zero]
        rw [habs_x] at hzx
        have : (z : ℝ) = 0 := abs_eq_zero.mp (le_antisymm hzx (abs_nonneg _))
        linarith
  · rintro ⟨hyF, hbnd, hsign, hmax⟩
    have hy_nn : 0 ≤ (y : ℝ) := by
      by_cases hx0 : x = 0
      · -- |y| ≤ 0 ⇒ y = 0
        have habs_x : |x| = 0 := by rw [hx0, abs_zero]
        rw [habs_x] at hbnd
        have : |(y : ℝ)| = 0 := le_antisymm hbnd (abs_nonneg _)
        have : (y : ℝ) = 0 := abs_eq_zero.mp this
        linarith
      · have hx_pos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
        nlinarith
    refine ⟨hyF, ?_, ?_⟩
    · rw [abs_of_nonneg hy_nn, abs_of_nonneg hx] at hbnd; exact hbnd
    · intro z hzF hzx
      by_cases hz_nn : 0 ≤ (z : ℝ)
      · have h1 : |(z : ℝ)| ≤ |x| := by
          rw [abs_of_nonneg hz_nn, abs_of_nonneg hx]; exact hzx
        have h2 : (z : ℝ) * x ≥ 0 := mul_nonneg hz_nn hx
        have key := hmax z hzF h1 h2
        rw [abs_of_nonneg hy_nn, abs_of_nonneg hz_nn] at key
        exact key
      · push Not at hz_nn
        linarith

/-- For `x ≤ 0`, RTN (largest F-element ≤ x) coincides with RAZ
(smallest F-element with `|y| ≥ |x|` on x's side). -/
theorem RoundsRTN_iff_RAZ_of_nonpos {F : AbstractFormat} {x : ℝ} {y : Dyadic}
    (hx : x ≤ 0) : Rounds F .ToNegative x y ↔ Rounds F .AwayZero x y := by
  constructor
  · rintro ⟨hyF, hyx, hmax⟩
    -- y ≤ x ≤ 0
    have hy_nonpos : (y : ℝ) ≤ 0 := le_trans hyx hx
    refine ⟨hyF, ?_, ?_, ?_⟩
    · rw [abs_of_nonpos hx, abs_of_nonpos hy_nonpos]; linarith
    · nlinarith
    · intro z hzF hxz hzsign
      by_cases hz_nonpos : (z : ℝ) ≤ 0
      · -- z ≤ 0. |x| ≤ |z| means -x ≤ -z, i.e., z ≤ x.
        have habs_z : |(z : ℝ)| = -(z : ℝ) := abs_of_nonpos hz_nonpos
        have habs_x : |x| = -x := abs_of_nonpos hx
        have habs_y : |(y : ℝ)| = -(y : ℝ) := abs_of_nonpos hy_nonpos
        rw [habs_z, habs_x] at hxz
        have hzx : (z : ℝ) ≤ x := by linarith
        have h_zy : (z : ℝ) ≤ (y : ℝ) := hmax z hzF hzx
        rw [habs_z, habs_y]; linarith
      · push Not at hz_nonpos
        -- z > 0; z * x ≥ 0 with x ≤ 0 forces x = 0
        have hx_zero : x = 0 := by nlinarith
        -- y ≤ 0 and largest F-elt ≤ 0 is 0 (since 0 ∈ F).
        have h0 : ((0 : Dyadic) : ℝ) ≤ (y : ℝ) := by
          apply hmax 0 F.zero_mem; rw [hx_zero]; rfl
        have hy0 : (y : ℝ) = 0 :=
          le_antisymm hy_nonpos (by simpa using h0)
        -- |x| = 0, |y| = 0, |z| > 0; need |y| ≥ |z|, but |y| = 0 < |z|.
        -- Wait, the hypothesis is |x| ≤ |z|, with |x| = 0; |z| > 0. So we just
        -- need 0 ≤ z's claim, but RAZ says |y| ≤ |z|, not |z| ≤ |y|.
        -- Re-reading: RAZ requires |y| ≤ |z|. y = 0 makes this |0| ≤ |z|, true.
        rw [hy0, abs_zero]
        exact abs_nonneg _
  · rintro ⟨hyF, hbnd, hsign, hmin⟩
    have hy_nonpos : (y : ℝ) ≤ 0 := by
      by_cases hx0 : x = 0
      · -- |x| = 0 ≤ |y|; not enough alone. Use the universal property at z = 0.
        -- For z = 0: |x| ≤ |0| means 0 ≤ 0 ✓; 0 * x = 0 ≥ 0 ✓. So |y| ≤ 0, y = 0.
        have h0 : |(y : ℝ)| ≤ |((0 : Dyadic) : ℝ)| :=
          hmin 0 F.zero_mem (by rw [hx0]; simp) (by simp)
        have : |(y : ℝ)| = 0 := le_antisymm (by simpa using h0) (abs_nonneg _)
        have : (y : ℝ) = 0 := abs_eq_zero.mp this
        linarith
      · have hx_neg : x < 0 := lt_of_le_of_ne hx hx0
        nlinarith
    refine ⟨hyF, ?_, ?_⟩
    · -- y ≤ x: |x| ≤ |y| with both nonpos gives -x ≤ -y, so y ≤ x
      rw [abs_of_nonpos hx, abs_of_nonpos hy_nonpos] at hbnd
      linarith
    · intro z hzF hzx
      -- z ≤ x ≤ 0; want z ≤ y.
      have hz_nonpos : (z : ℝ) ≤ 0 := le_trans hzx hx
      have h1 : |x| ≤ |(z : ℝ)| := by
        rw [abs_of_nonpos hx, abs_of_nonpos hz_nonpos]; linarith
      have h2 : (z : ℝ) * x ≥ 0 := by nlinarith
      have key := hmin z hzF h1 h2
      rw [abs_of_nonpos hy_nonpos, abs_of_nonpos hz_nonpos] at key
      linarith

/-- Composition lemma for RTN (round-down): if `F₁ ⊆ F₂`, then RTN through
`F₂` to `F₁` agrees with RTN directly to `F₁`. -/
theorem Rounds.compose_toNegative {F₁ F₂ : AbstractFormat} (hsub : F₁ ⊆ F₂)
    {x : ℝ} {z w : Dyadic}
    (hz : Rounds F₂ .ToNegative x z) (hw : Rounds F₁ .ToNegative (z : ℝ) w) :
    Rounds F₁ .ToNegative x w := by
  obtain ⟨hzF, hzx, hz_max⟩ := hz
  obtain ⟨hwF, hwz, hw_max⟩ := hw
  refine ⟨hwF, le_trans hwz hzx, ?_⟩
  intro y hyF₁ hyx
  have hyF₂ : y ∈ F₂ := hsub y hyF₁
  have hyz : (y : ℝ) ≤ (z : ℝ) := hz_max y hyF₂ hyx
  exact hw_max y hyF₁ hyz

/-- Composition lemma for RTP (round-up): if `F₁ ⊆ F₂`, then RTP through
`F₂` to `F₁` agrees with RTP directly to `F₁`. -/
theorem Rounds.compose_toPositive {F₁ F₂ : AbstractFormat} (hsub : F₁ ⊆ F₂)
    {x : ℝ} {z w : Dyadic}
    (hz : Rounds F₂ .ToPositive x z) (hw : Rounds F₁ .ToPositive (z : ℝ) w) :
    Rounds F₁ .ToPositive x w := by
  obtain ⟨hzF, hxz, hz_min⟩ := hz
  obtain ⟨hwF, hzw, hw_min⟩ := hw
  refine ⟨hwF, le_trans hxz hzw, ?_⟩
  intro y hyF₁ hxy
  have hyF₂ : y ∈ F₂ := hsub y hyF₁
  have hzy : (z : ℝ) ≤ (y : ℝ) := hz_min y hyF₂ hxy
  exact hw_min y hyF₁ hzy

/-- If `x ∈ F` and `y` is the RTO-rounding of `x` in `F`, then `y = x`. -/
theorem Rounds.toOdd_unique_of_mem {F : AbstractFormat} {x : Dyadic} (hx : x ∈ F)
    {y : Dyadic} (h : Rounds F .ToOdd (x : ℝ) y) : y = x := by
  obtain ⟨_, hadj, _⟩ := h
  rcases hadj with ⟨_, hyx, hmax⟩ | ⟨_, hxy, hmin⟩
  · -- RoundsRTN: (y:ℝ) ≤ (x:ℝ) and y is largest such
    have hxy : (x : ℝ) ≤ (y : ℝ) := hmax x hx (le_refl _)
    have heq : (y : ℝ) = (x : ℝ) := le_antisymm hyx hxy
    exact Subtype.ext heq
  · -- RoundsRTP: (x:ℝ) ≤ (y:ℝ) and y is smallest such
    have hyx : (y : ℝ) ≤ (x : ℝ) := hmin x hx (le_refl _)
    have heq : (y : ℝ) = (x : ℝ) := le_antisymm hyx hxy
    exact Subtype.ext heq

/-- The RTO-rounding of `0` in any format is `0` itself. -/
theorem Rounds.toOdd_eq_zero_of_zero {F : AbstractFormat} {z : Dyadic}
    (h : Rounds F .ToOdd 0 z) : z = 0 := by
  have h0 : Rounds F .ToOdd (((0 : Dyadic) : ℝ)) z := by
    have : ((0 : Dyadic) : ℝ) = 0 := rfl
    rw [this]; exact h
  exact Rounds.toOdd_unique_of_mem F.zero_mem h0

/-- The RTO-rounding of a positive `x` is non-negative. -/
theorem Rounds.toOdd_nonneg_of_pos {F : AbstractFormat} {x : ℝ} {z : Dyadic}
    (hx_pos : 0 < x) (h : RoundsRTO F x z) : 0 ≤ (z : ℝ) := by
  rcases h.2.1 with hRD | hRU
  · obtain ⟨_, _, hz_max⟩ := hRD
    have := hz_max 0 F.zero_mem hx_pos.le
    simpa using this
  · linarith [hRU.2.1]

/-- The RTO-rounding of a non-positive `x` is non-positive. -/
theorem Rounds.toOdd_nonpos_of_nonpos {F : AbstractFormat} {x : ℝ} {z : Dyadic}
    (hx : x ≤ 0) (h : RoundsRTO F x z) : (z : ℝ) ≤ 0 := by
  rcases h.2.1 with hRD | hRU
  · linarith [hRD.2.1]
  · obtain ⟨_, _, hz_min⟩ := hRU
    have := hz_min 0 F.zero_mem hx
    simpa using this

/-- The RTO-rounding of a non-negative `x` is non-negative (variant of
`nonneg_of_pos` covering `x = 0` too). -/
theorem Rounds.toOdd_nonneg_of_nn {F : AbstractFormat} {x : ℝ} {z : Dyadic}
    (hx : 0 ≤ x) (h : RoundsRTO F x z) : 0 ≤ (z : ℝ) := by
  rcases h.2.1 with hRD | hRU
  · obtain ⟨_, _, hz_max⟩ := hRD
    have := hz_max 0 F.zero_mem hx
    simpa using this
  · linarith [hRU.2.1]

/-- **Lemma 5.3 (spec-form corollary)**: when `x` is unrepresentable in `F`
(`x ≠ x'`), the RTO-rounded `x'` cannot coincide with *any* dyadic `y` that is
representable at strictly lower precision than the rounding precision at `x'`.

The hypothesis `hgt : (w : ℤ) < numDigits F.p F.exp x'` captures "the rounding
precision (at `x'`) exceeds `w`". In typical applications, this follows from
the rounding precision at `x` (Lemma 5.1) plus a magnitude-bin invariant. -/
theorem Rounds.toOdd_ne_of_precisionAtMost {F : AbstractFormat} {w : ℕ}
    {x : ℝ} {x' : Dyadic} (hround : RoundsRTO F x x')
    (hxne : x ≠ (x' : ℝ))
    (hgt : (w : ℤ) < numDigits F.p F.exp (x' : ℝ))
    {y : Dyadic} (hy : Dyadic.precisionAtMost (w : ℕ∞) y) :
    (x' : ℝ) ≠ (y : ℝ) := by
  intro hxy
  have hxy_eq : x' = y := Subtype.ext hxy
  obtain ⟨_, _, hodd_imp⟩ := hround
  have h_odd : IsOdd F x' := hodd_imp hxne
  -- Transport hgt and h_odd along x' = y
  have hgt_y : (w : ℤ) < numDigits F.p F.exp (y : ℝ) := by rw [← hxy]; exact hgt
  have h_odd_y : IsOdd F y := by rw [← hxy_eq]; exact h_odd
  exact (precisionAtMost_not_IsOdd hgt_y hy) h_odd_y

/-- **Lemma 5.3, applied form**: if `RoundsRTO F₂ x z` (with `x ≠ z`), then `z`
cannot be representable in any format `F₁` whose effective precision at `z`
(per Lemma 5.1) is strictly less than `F₂`'s. This is the form used by every
double-rounding theorem to rule out the case "F₂'s rounded value lands on an
`F₁`-representable point". -/
theorem Rounds.toOdd_notMem_of_lower_numDigits {F₁ F₂ : AbstractFormat}
    {x : ℝ} {z : Dyadic} (hz : RoundsRTO F₂ x z)
    (hxne : x ≠ (z : ℝ))
    (hlt : numDigits F₁.p F₁.exp (z : ℝ) < numDigits F₂.p F₂.exp (z : ℝ)) :
    z ∉ F₁ := by
  intro hzF₁
  have h_prec : Dyadic.precisionAtMost
      (((numDigits F₁.p F₁.exp ((z : Dyadic) : ℝ)).toNat : ℕ) : ℕ∞) z :=
    mem_imp_precisionAtMost_numDigits hzF₁
  have h_iod : IsOdd F₂ z := hz.2.2 hxne
  have h_nd_F₂_pos : 0 < numDigits F₂.p F₂.exp ((z : Dyadic) : ℝ) :=
    h_iod.numDigits_pos
  have hcast : ((numDigits F₁.p F₁.exp ((z : Dyadic) : ℝ)).toNat : ℤ)
      < numDigits F₂.p F₂.exp ((z : Dyadic) : ℝ) := by
    rcases le_or_gt 0 (numDigits F₁.p F₁.exp ((z : Dyadic) : ℝ)) with h | h
    · rw [Int.toNat_of_nonneg h]; exact hlt
    · rw [Int.toNat_of_nonpos (le_of_lt h)]
      push_cast; exact h_nd_F₂_pos
  exact (Rounds.toOdd_ne_of_precisionAtMost hz hxne hcast h_prec) rfl

/-- Paper-aligned form of Lemma 5.3. From `F₁.extend 1 ⊆ F₂` and an RTO
rounding `z` with `x ≠ z` (so `IsOdd F₂ z`), conclude `z ∉ F₁`.

Proof: `z ∈ F₁ ⊆ F₁.extend 1`. By `numDigits_eq_of_subset_of_isOdd`,
`numDigits (F₁.extend 1) z = numDigits F₂ z`. By `numDigits_extend`, the LHS
equals `numDigits F₁ z + 1`. So `numDigits F₁ z + 1 = numDigits F₂ z`, i.e.,
`numDigits F₁ z < numDigits F₂ z`. Then apply `notMem_of_lower_numDigits`. -/
theorem Rounds.toOdd_notMem_of_extend_subset {F₁ F₂ : AbstractFormat}
    (hsub : F₁.extend 1 ⊆ F₂)
    (hp_F₂ : 2 ≤ F₂.p)
    {x : ℝ} {z : Dyadic} (hz : RoundsRTO F₂ x z)
    (hxne : x ≠ (z : ℝ)) :
    z ∉ F₁ := by
  intro hzF₁
  have h_iod : IsOdd F₂ z := hz.2.2 hxne
  have hz_ne_zero : ((z : Dyadic) : ℝ) ≠ 0 := by
    intro h
    have hz_d : z = 0 := Subtype.ext (by rw [h]; rfl)
    rw [hz_d] at h_iod
    exact h_iod.ne_zero rfl
  -- z ∈ F₁ ⇒ z ∈ F₁.extend 1 (precision/quantum constraints weaken).
  have hzF₁_ext : z ∈ F₁.extend 1 := by
    obtain ⟨hp, hq, hb⟩ := hzF₁
    refine ⟨?_, ?_, ?_⟩
    · have h_p_le : F₁.p ≤ F₁.p + 1 := by
        cases F₁.p with
        | top => simp
        | coe n => exact WithTop.coe_le_coe.mpr (Nat.le_succ n)
      change Dyadic.precisionAtMost _ z
      exact Dyadic.precisionAtMost_mono h_p_le hp
    · change Dyadic.quantumAtLeast _ z
      have h_exp_ge : (F₁.exp.map (· - (1 : ℤ))) ≤ F₁.exp := by
        cases F₁.exp with
        | bot => simp
        | coe e =>
          change ((e - 1 : ℤ) : WithBot ℤ) ≤ ((e : ℤ) : WithBot ℤ)
          exact WithBot.coe_le_coe.mpr (by linarith)
      exact Dyadic.quantumAtLeast_anti h_exp_ge hq
    · exact hb
  -- Apply Lemma 5.3 corollary at F₁.extend 1 ⊆ F₂.
  have h_eq : numDigits (F₁.extend 1).p (F₁.extend 1).exp (z : ℝ) =
              numDigits F₂.p F₂.exp (z : ℝ) :=
    numDigits_eq_of_subset_of_isOdd hsub hp_F₂ hzF₁_ext h_iod
  rw [numDigits_extend F₁ 1 hz_ne_zero] at h_eq
  -- h_eq : numDigits F₁ z + 1 = numDigits F₂ z
  -- Convert to the strict shift and apply notMem_of_lower_numDigits.
  have h_F₂_pos : 0 < numDigits F₂.p F₂.exp (z : ℝ) := h_iod.numDigits_pos
  have h_lt : numDigits F₁.p F₁.exp (z : ℝ) < numDigits F₂.p F₂.exp (z : ℝ) := by
    omega
  exact (Rounds.toOdd_notMem_of_lower_numDigits hz hxne h_lt) hzF₁

/-- Sign-flip symmetry for RTZ rounding. -/
theorem RoundsRTZ.neg {F : AbstractFormat} {x : ℝ} {y : Dyadic}
    (h : RoundsRTZ F x y) : RoundsRTZ F (-x) (-y) := by
  obtain ⟨hyF, hbnd, hsign, hmax⟩ := h
  refine ⟨neg_mem hyF, ?_, ?_, ?_⟩
  · change |((-y : Dyadic) : ℝ)| ≤ |(-x)|
    push_cast
    rw [abs_neg, abs_neg]
    exact hbnd
  · change ((-y : Dyadic) : ℝ) * (-x) ≥ 0
    push_cast
    have : -(y : ℝ) * -x = (y : ℝ) * x := by ring
    rw [this]
    exact hsign
  · intro z hzF hzbnd hzsign
    rw [abs_neg] at hzbnd
    have hnz : (-z) ∈ F := neg_mem hzF
    have h1 : |((-z : Dyadic) : ℝ)| ≤ |x| := by push_cast; rw [abs_neg]; exact hzbnd
    have h2 : 0 ≤ ((-z : Dyadic) : ℝ) * x := by
      push_cast
      have hzs : 0 ≤ (z : ℝ) * (-x) := hzsign
      linarith
    have key := hmax (-z) hnz h1 h2
    have habs1 : |((-z : Dyadic) : ℝ)| = |(z : ℝ)| := by push_cast; rw [abs_neg]
    have habs2 : |((-y : Dyadic) : ℝ)| = |(y : ℝ)| := by push_cast; rw [abs_neg]
    rw [habs1] at key
    rw [habs2]
    exact key

/-- Sign-flip symmetry for RTO rounding. -/
theorem RoundsRTO.neg {F : AbstractFormat} {x : ℝ} {y : Dyadic}
    (h : RoundsRTO F x y) : RoundsRTO F (-x) (-y) := by
  obtain ⟨hyF, hadj, hodd_imp⟩ := h
  refine ⟨neg_mem hyF, ?_, ?_⟩
  · -- RoundsRTN ↔ RoundsRTP under negation
    rcases hadj with hRD | hRU
    · right
      obtain ⟨_, hyx, hmax⟩ := hRD
      refine ⟨neg_mem hyF, ?_, ?_⟩
      · push_cast; linarith
      · intro z hzF hxz
        push_cast
        have hnzF : (-z) ∈ F := neg_mem hzF
        have h1 : ((-z : Dyadic) : ℝ) ≤ x := by push_cast; linarith
        have key := hmax (-z) hnzF h1
        push_cast at key; linarith
    · left
      obtain ⟨_, hxy, hmin⟩ := hRU
      refine ⟨neg_mem hyF, ?_, ?_⟩
      · push_cast; linarith
      · intro z hzF hzx
        push_cast
        have hnzF : (-z) ∈ F := neg_mem hzF
        have h1 : x ≤ ((-z : Dyadic) : ℝ) := by push_cast; linarith
        have key := hmin (-z) hnzF h1
        push_cast at key; linarith
  · intro hxne
    have hxne' : x ≠ (y : ℝ) := by
      intro h_eq
      apply hxne
      rw [h_eq]; push_cast; rfl
    exact (hodd_imp hxne').neg

/-- `RoundsRTN ∨ RoundsRTP` is preserved (with the disjuncts flipped) under
joint negation of `x` and `y`. Used by `RoundsRTO.neg` and `RoundsRNE.neg`. -/
private lemma roundsAdj_neg {F : AbstractFormat} {a : ℝ} {b : Dyadic}
    (h : RoundsRTN F a b ∨ RoundsRTP F a b) :
    RoundsRTN F (-a) (-b) ∨ RoundsRTP F (-a) (-b) := by
  rcases h with hRD | hRU
  · right
    obtain ⟨hbF, hba, hmax⟩ := hRD
    refine ⟨neg_mem hbF, ?_, ?_⟩
    · push_cast; linarith
    · intro w hwF haw
      have hnwF : (-w) ∈ F := neg_mem hwF
      have h1 : ((-w : Dyadic) : ℝ) ≤ a := by push_cast; linarith
      have key := hmax (-w) hnwF h1
      push_cast at key ⊢; linarith
  · left
    obtain ⟨hbF, hab, hmin⟩ := hRU
    refine ⟨neg_mem hbF, ?_, ?_⟩
    · push_cast; linarith
    · intro w hwF hwa
      have hnwF : (-w) ∈ F := neg_mem hwF
      have h1 : a ≤ ((-w : Dyadic) : ℝ) := by push_cast; linarith
      have key := hmin (-w) hnwF h1
      push_cast at key ⊢; linarith

/-- Sign-flip symmetry for RAZ rounding: rounding `x` to `y` under RAZ in `F`
is equivalent to rounding `-x` to `-y`. Uses `neg_mem` (every format is closed
under negation). -/
theorem RoundsRAZ.neg {F : AbstractFormat} {x : ℝ} {y : Dyadic}
    (h : RoundsRAZ F x y) : RoundsRAZ F (-x) (-y) := by
  obtain ⟨hyF, hbnd, hsign, hmin⟩ := h
  refine ⟨neg_mem hyF, ?_, ?_, ?_⟩
  · change |(-x)| ≤ |((-y : Dyadic) : ℝ)|
    push_cast
    rw [abs_neg, abs_neg]
    exact hbnd
  · change ((-y : Dyadic) : ℝ) * (-x) ≥ 0
    push_cast
    have : -(y : ℝ) * -x = (y : ℝ) * x := by ring
    rw [this]
    exact hsign
  · intro z hzF hzbnd hzsign
    rw [abs_neg] at hzbnd
    have hnz : (-z) ∈ F := neg_mem hzF
    have h1 : |x| ≤ |((-z : Dyadic) : ℝ)| := by
      push_cast; rw [abs_neg]; exact hzbnd
    have h2 : 0 ≤ ((-z : Dyadic) : ℝ) * x := by
      push_cast
      have hzs : 0 ≤ (z : ℝ) * (-x) := hzsign
      linarith
    have key := hmin (-z) hnz h1 h2
    change |((-y : Dyadic) : ℝ)| ≤ |(z : ℝ)|
    push_cast
    rw [abs_neg]
    have hyz : |(y : ℝ)| ≤ |((-z : Dyadic) : ℝ)| := key
    rwa [show |((-z : Dyadic) : ℝ)| = |(z : ℝ)| from by push_cast; rw [abs_neg]] at hyz

/-- Sign-flip symmetry for RNE rounding. -/
theorem RoundsRNE.neg {F : AbstractFormat} {x : ℝ} {y : Dyadic}
    (h : RoundsRNE F x y) : RoundsRNE F (-x) (-y) := by
  obtain ⟨hyF, hadj, hclose, htie⟩ := h
  -- Distance identities used several times.
  have eq1 : ∀ (w : Dyadic),
      |x - ((-w : Dyadic) : ℝ)| = |(-x) - (w : ℝ)| := by
    intro w
    push_cast
    rw [show x - -(w : ℝ) = -((-x) - (w : ℝ)) from by ring, abs_neg]
  have eq2 : |x - (y : ℝ)| = |(-x) - ((-y : Dyadic) : ℝ)| := by
    push_cast
    rw [show x - (y : ℝ) = -((-x) - -(y : ℝ)) from by ring, abs_neg]
  refine ⟨neg_mem hyF, roundsAdj_neg hadj, ?_, ?_⟩
  · -- closeness: every adjacent of (-x) corresponds to its negation as adjacent of x
    intro z hzF hzadj
    have hnzF : (-z) ∈ F := neg_mem hzF
    have hnzadj : RoundsRTN F x (-z) ∨ RoundsRTP F x (-z) := by
      have := roundsAdj_neg hzadj
      simpa using this
    have key := hclose (-z) hnzF hnzadj
    rw [eq1 z] at key
    rw [← eq2]
    exact key
  · -- tie-break: a tie at (-x, -y) yields a tie at (x, y); apply IsEven.neg
    rintro ⟨z, hzF, hzadj, hzne, hzdist⟩
    have hnzF : (-z) ∈ F := neg_mem hzF
    have hnzadj : RoundsRTN F x (-z) ∨ RoundsRTP F x (-z) := by
      have := roundsAdj_neg hzadj
      simpa using this
    have hnzne : (-z) ≠ y := by
      intro h_eq
      apply hzne
      have h2 : -(-z) = -y := by rw [h_eq]
      rwa [neg_neg] at h2
    have hnzdist : |x - (y : ℝ)| = |x - ((-z : Dyadic) : ℝ)| := by
      rw [eq2, eq1 z]; exact hzdist
    exact (htie ⟨-z, hnzF, hnzadj, hnzne, hnzdist⟩).neg

/-- Sign-flip symmetry for RNA rounding (round-to-nearest, ties away from
zero). Mirrors `RoundsRNE.neg`; the larger-magnitude tie-break is
sign-invariant. -/
theorem RoundsRNA.neg {F : AbstractFormat} {x : ℝ} {y : Dyadic}
    (h : RoundsRNA F x y) : RoundsRNA F (-x) (-y) := by
  obtain ⟨hyF, hadj, hclose, htie⟩ := h
  have eq1 : ∀ (w : Dyadic),
      |x - ((-w : Dyadic) : ℝ)| = |(-x) - (w : ℝ)| := by
    intro w
    push_cast
    rw [show x - -(w : ℝ) = -((-x) - (w : ℝ)) from by ring, abs_neg]
  have eq2 : |x - (y : ℝ)| = |(-x) - ((-y : Dyadic) : ℝ)| := by
    push_cast
    rw [show x - (y : ℝ) = -((-x) - -(y : ℝ)) from by ring, abs_neg]
  refine ⟨neg_mem hyF, roundsAdj_neg hadj, ?_, ?_⟩
  · intro z hzF hzadj
    have hnzF : (-z) ∈ F := neg_mem hzF
    have hnzadj : RoundsRTN F x (-z) ∨ RoundsRTP F x (-z) := by
      have := roundsAdj_neg hzadj
      simpa using this
    have key := hclose (-z) hnzF hnzadj
    rw [eq1 z] at key
    rw [← eq2]
    exact key
  · intro z hzF hzadj hzne hzdist
    have hnzF : (-z) ∈ F := neg_mem hzF
    have hnzadj : RoundsRTN F x (-z) ∨ RoundsRTP F x (-z) := by
      have := roundsAdj_neg hzadj
      simpa using this
    have hnzne : (-z) ≠ y := by
      intro h_eq
      apply hzne
      have h2 : -(-z) = -y := by rw [h_eq]
      rwa [neg_neg] at h2
    have hnzdist : |x - (y : ℝ)| = |x - ((-z : Dyadic) : ℝ)| := by
      rw [eq2, eq1 z]; exact hzdist
    have key := htie (-z) hnzF hnzadj hnzne hnzdist
    have h_neg_z : |((-z : Dyadic) : ℝ)| = |(z : ℝ)| := by push_cast; rw [abs_neg]
    have h_neg_y : |((-y : Dyadic) : ℝ)| = |(y : ℝ)| := by push_cast; rw [abs_neg]
    rw [h_neg_y]
    rw [h_neg_z] at key
    exact key

/-- Sign-flip symmetry for the unified `Rounds` relation, on sign-symmetric
modes. Dispatches to the per-mode `.neg` helpers (`RoundsRTZ.neg`,
`RoundsRAZ.neg`, `RoundsRTO.neg`, `RoundsRNE.neg`, `RoundsRNA.neg`). The
directed modes `ToPositive`/`ToNegative` are excluded by `hrm`. -/
theorem Rounds.neg {F : AbstractFormat} {rm : RoundingMode}
    {x : ℝ} {y : Dyadic}
    (h : Rounds F rm x y) (hrm : rm.IsSymmetric) :
    Rounds F rm (-x) (-y) := by
  cases rm with
  | Nearest tb =>
    cases tb with
    | ToEven => exact RoundsRNE.neg h
    | AwayZero => exact RoundsRNA.neg h
  | ToZero => exact RoundsRTZ.neg h
  | AwayZero => exact RoundsRAZ.neg h
  | ToOdd => exact RoundsRTO.neg h
  | ToPositive => exact absurd hrm (by simp [RoundingMode.IsSymmetric])
  | ToNegative => exact absurd hrm (by simp [RoundingMode.IsSymmetric])

end AbstractFormat

end Mpfx
