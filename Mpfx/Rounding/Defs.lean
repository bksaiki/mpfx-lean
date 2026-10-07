import Mpfx.Format.Parity

/-!
# Rounding spec (relational layer)

Defines:

* `RoundingMode`, `TieBreak`, `RoundResult` — the modes and the result
  (`.value v` or `.undefined`).
* `FiniteFormat.IsUndefined` — when `.undefined` fires.
* `SpecialMap`, `OverflowMap` — where special inputs and overflow go.
* `IsFaithfulRound` — RoundDown or RoundUp.
* `RoundsFinite`, `RoundsInBound`, `Overflows` — the numeric spec.
* `Rounds F S O rm : WithSpecial ℝ → RoundResult → Prop` — the
  specification relation, all seven modes.

The companion file **`Mpfx/Rounding/Op.lean`** adds the noncomputable
function `rnd` and the bridge `rnd_iff_rounds`.
-/

namespace Mpfx

/-- Tie-breaking for the nearest-rounding modes. -/
inductive TieBreak where
  /-- Ties to the value with even significand (IEEE `roundTiesToEven`). -/
  | toEven : TieBreak
  /-- Ties to the value with larger magnitude (IEEE `roundTiesToAway`). -/
  | awayZero : TieBreak
deriving DecidableEq, Repr

/-- IEEE-754 + paper-extended rounding modes.

* `ToNegative` (RTN) — round toward `-∞`.
* `ToPositive` (RTP) — round toward `+∞`.
* `ToZero` (RTZ) — round toward `0`.
* `AwayZero` (RAZ) — round away from `0`.
* `ToOdd` (RTO; not IEEE) — round to the F-adjacent with odd significand.
* `Nearest tb` — round to nearest; ties broken by `tb`. -/
inductive RoundingMode where
  | toNegative : RoundingMode
  | toPositive : RoundingMode
  | toZero : RoundingMode
  | awayZero : RoundingMode
  | toOdd : RoundingMode
  | nearest : TieBreak → RoundingMode
deriving DecidableEq, Repr

/-- The result of rounding in a `Format` with some `RoundingMode`.

* `.value v` — the rounded value, numeric or special.
* `.undefined` — the `(Format, RoundingMode)` combination is degenerate
  and rounding has no semantic meaning. Fires only on
  `(p = 1, exp = ⊥, rm ∈ {.toOdd, .nearest .toEven})`. -/
inductive RoundResult where
  | value (v : WithSpecial Dyadic) : RoundResult
  | undefined : RoundResult

namespace RoundResult

/-- Negation through the value; `.undefined` is a fixed point. -/
def neg : RoundResult → RoundResult
  | .value v   => .value v.neg
  | .undefined => .undefined

@[simp] theorem neg_value (v : WithSpecial Dyadic) :
    (RoundResult.value v).neg = .value v.neg := rfl
@[simp] theorem neg_undefined : RoundResult.undefined.neg = .undefined := rfl

@[simp] theorem neg_neg (r : RoundResult) : r.neg.neg = r := by
  cases r <;> simp [neg]

end RoundResult

/-- The format/mode pair is degenerate (no meaningful rounding):
`(1, ⊥, rm)` for `rm ∈ {.toOdd, .nearest .toEven}` — precision `1` with
no quantum has no anchor for parity, so the modes that consult
`IsOdd`/`IsEven` are meaningless.

The `(⊤, ⊥)` case (fully unconstrained) is structurally excluded by
`FiniteFormat`'s `finite` invariant. -/
def FiniteFormat.IsUndefined (F : FiniteFormat) (rm : RoundingMode) : Prop :=
  F.p = (1 : ℕ) ∧ F.exp = ⊥ ∧
    (rm = .toOdd ∨ rm = .nearest .toEven)

/-- `IsUndefined` depends only on `(F.p, F.exp)`, both preserved by
`F.unbounded`. -/
@[simp] theorem FiniteFormat.unbounded_isUndefined (F : FiniteFormat)
    (rm : RoundingMode) :
    F.unbounded.IsUndefined rm = F.IsUndefined rm := rfl

/-- Promote to `ParityFormat` from a `¬ IsUndefined .toOdd` witness. -/
def FiniteFormat.toParityFormatOfToOdd
    (F : FiniteFormat) (h : ¬ F.IsUndefined .toOdd) : ParityFormat := by
  refine ⟨F, ?_⟩
  by_contra h_neg; push Not at h_neg
  exact h ⟨h_neg.1, h_neg.2, Or.inl rfl⟩

/-- Promote to `ParityFormat` from a `¬ IsUndefined (.nearest .toEven)`
witness. Proof-irrelevantly the same value as `toParityFormatOfToOdd`. -/
def FiniteFormat.toParityFormatOfNearestEven
    (F : FiniteFormat) (h : ¬ F.IsUndefined (.nearest .toEven)) : ParityFormat := by
  refine ⟨F, ?_⟩
  by_contra h_neg; push Not at h_neg
  exact h ⟨h_neg.1, h_neg.2, Or.inr rfl⟩

/-! ### Special-value and overflow tables -/

/-- Where special inputs go. -/
structure SpecialMap (F : Format) where
  map : Special → WithSpecial Dyadic
  mem : ∀ s, map s ∈ F.values

/-- Where overflow goes, keyed by `negative`. -/
structure OverflowMap (F : Format) where
  map : Bool → WithSpecial Dyadic
  mem : ∀ negative, map negative ∈ F.values

/-- The table for the negated input: `(O.neg hF).map b = (O.map !b).neg`. -/
def OverflowMap.neg {F : Format} (hF : F.NegClosed) (O : OverflowMap F) : OverflowMap F :=
  ⟨fun negative => (O.map !negative).neg, fun _ => Format.neg_mem_values hF (O.mem _)⟩

@[simp] theorem OverflowMap.neg_map {F : Format} (hF : F.NegClosed) (O : OverflowMap F)
    (negative : Bool) : (O.neg hF).map negative = (O.map !negative).neg := rfl

/-! ### The specification relation `Rounds`

`Rounds F S O rm v r : Prop` asserts that `r : RoundResult` is *the* answer
that mode `rm` gives for input `v` in format `F`:

* a special input `s` gives `.value (S.map s)`;
* a real input gives `.undefined` iff `F.IsUndefined rm`; otherwise its
  unbounded rounding `y`, as `.value (.finite y)` if `y` fits the bound
  `F.b`, else `.value (O.map (y < 0))` (overflow).

The mode-specific rounding spec `RoundsFinite` is evaluated against
`F.unbounded` (i.e., `F` with `b := ⊤`) — the bound check is a
*separate* conjunct, applied to the value chosen by the unbounded
spec. This ensures IEEE-style overflow: saturation isn't a "valid
answer" — the only candidate is the unbounded rounding, and overflow
fires if and only if that candidate is out of range. -/

/-- A *faithful* rounding of `x`: `y ∈ F` is either the largest F-element
≤ `x` (RTN) or the smallest F-element ≥ `x` (RTP). All of RTO, RNE, RNA
require their result to be faithful. -/
def IsFaithfulRound (F : FiniteFormat) (x : ℝ) (y : Dyadic) : Prop :=
  (y ∈ F ∧ (y : ℝ) ≤ x ∧ ∀ z : Dyadic, z ∈ F → (z : ℝ) ≤ x → (z : ℝ) ≤ (y : ℝ)) ∨
  (y ∈ F ∧ x ≤ (y : ℝ) ∧ ∀ z : Dyadic, z ∈ F → x ≤ (z : ℝ) → (y : ℝ) ≤ (z : ℝ))

/-- The mode-specific rounding spec: `y ∈ F` is the mode-`rm` rounding of `x`
(no bound check beyond membership). `Rounds` applies it to `F.unbounded`. -/
def RoundsFinite (F : FiniteFormat) (rm : RoundingMode) (x : ℝ) (y : Dyadic) :
    Prop :=
  y ∈ F ∧
  match rm with
  | .toNegative =>
      (y : ℝ) ≤ x ∧
      ∀ z : Dyadic, z ∈ F → (z : ℝ) ≤ x → (z : ℝ) ≤ (y : ℝ)
  | .toPositive =>
      x ≤ (y : ℝ) ∧
      ∀ z : Dyadic, z ∈ F → x ≤ (z : ℝ) → (y : ℝ) ≤ (z : ℝ)
  | .toZero =>
      |(y : ℝ)| ≤ |x| ∧ (y : ℝ) * x ≥ 0 ∧
      ∀ z : Dyadic, z ∈ F → |(z : ℝ)| ≤ |x| → (z : ℝ) * x ≥ 0 →
        |(z : ℝ)| ≤ |(y : ℝ)|
  | .awayZero =>
      |x| ≤ |(y : ℝ)| ∧ (y : ℝ) * x ≥ 0 ∧
      ∀ z : Dyadic, z ∈ F → |x| ≤ |(z : ℝ)| → (z : ℝ) * x ≥ 0 →
        |(y : ℝ)| ≤ |(z : ℝ)|
  | .toOdd =>
      IsFaithfulRound F x y ∧
      (x ≠ (y : ℝ) →
        ∃ F' : ParityFormat, F'.toFormat = F.toFormat ∧ F'.IsOdd y)
  | .nearest .toEven =>
      IsFaithfulRound F x y ∧
      (∀ z : Dyadic, z ∈ F → IsFaithfulRound F x z →
        |x - (y : ℝ)| ≤ |x - (z : ℝ)|) ∧
      ((∃ z : Dyadic, z ∈ F ∧ IsFaithfulRound F x z ∧
          z ≠ y ∧ |x - (y : ℝ)| = |x - (z : ℝ)|) →
        ∃ F' : ParityFormat, F'.toFormat = F.toFormat ∧ F'.IsEven y)
  | .nearest .awayZero =>
      IsFaithfulRound F x y ∧
      (∀ z : Dyadic, z ∈ F → IsFaithfulRound F x z →
        |x - (y : ℝ)| ≤ |x - (z : ℝ)|) ∧
      (∀ z : Dyadic, z ∈ F → IsFaithfulRound F x z →
          z ≠ y → |x - (y : ℝ)| = |x - (z : ℝ)| → |(z : ℝ)| ≤ |(y : ℝ)|)

/-- The unbounded rounding of `x` is `y`, and `y` is within `F`'s bound. -/
def RoundsInBound (F : FiniteFormat) (rm : RoundingMode) (x : ℝ) (y : Dyadic) : Prop :=
  RoundsFinite F.unbounded rm x y ∧ Format.boundOK F.b y

/-- The unbounded rounding of `x` leaves `F`'s bound. -/
def Overflows (F : FiniteFormat) (rm : RoundingMode) (x : ℝ) : Prop :=
  ∃ y, RoundsFinite F.unbounded rm x y ∧ ¬ Format.boundOK F.b y

/-- The rounding-specification relation. The mode-spec is against
`F.unbounded`; the bound `F.b` is checked separately on its result. -/
def Rounds (F : FiniteFormat) (S : SpecialMap F.toFormat) (O : OverflowMap F.toFormat)
    (rm : RoundingMode) : WithSpecial ℝ → RoundResult → Prop
  | .special s, r => r = .value (S.map s)
  | .finite _, .undefined => F.IsUndefined rm
  | .finite x, .value v =>
      ¬ F.IsUndefined rm ∧ ∃ y, RoundsFinite F.unbounded rm x y ∧
        ((Format.boundOK F.b y ∧ v = .finite y) ∨
         (¬ Format.boundOK F.b y ∧ v = O.map (decide ((y : ℚ) < 0))))

/-! ### Modes that are always defined -/

theorem not_isUndefined_toZero (F : FiniteFormat) :
    ¬ F.IsUndefined .toZero := by
  rintro ⟨-, -, h | h⟩ <;> simp at h

theorem not_isUndefined_awayZero (F : FiniteFormat) :
    ¬ F.IsUndefined .awayZero := by
  rintro ⟨-, -, h | h⟩ <;> simp at h

/-- Directed modes are never undefined. -/
theorem not_isUndefined_toNegative (F : FiniteFormat) :
    ¬ F.IsUndefined .toNegative := by
  rintro ⟨-, -, h | h⟩ <;> simp at h

theorem not_isUndefined_toPositive (F : FiniteFormat) :
    ¬ F.IsUndefined .toPositive := by
  rintro ⟨-, -, h | h⟩ <;> simp at h

/-- `2 ≤ F.p` rules out `IsUndefined` (which requires `p = 1`). -/
theorem not_isUndefined_of_two_le_p {F : FiniteFormat} {rm : RoundingMode}
    (hp : ((2 : ℕ) : Prec) ≤ F.p) : ¬ F.IsUndefined rm := by
  rintro ⟨h1, -, -⟩
  rw [h1] at hp
  simp at hp

end Mpfx
