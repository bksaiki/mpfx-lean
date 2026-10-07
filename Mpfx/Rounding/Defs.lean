import Mpfx.Format.Parity

/-!
# Rounding spec (relational layer)

The relational layer of the rounding architecture. Defines:

* `RoundingMode`, `TieBreak`, `RoundResult` — the modes and the
  result ADT (`.finite`, `.overflow`, `.undefined`).
* `Format.IsUndefined`, `Format.IsOverflow` — when each `RoundResult`
  case fires.
* `IsFaithfulRound` — RoundDown or RoundUp.
* `Rounds : Format → RoundingMode → ℝ → RoundResult → Prop` — the
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

/-- The result of rounding a real `x` in a `Format` with some `RoundingMode`.

* `.finite d` — `d : Dyadic` is the rounded value.
* `.overflow positive` — `|x|` exceeds the format's magnitude bound. The
  `positive : Bool` records the sign of the would-be result: `true` for
  positive overflow, `false` for negative. (The would-be result is never
  zero, since `0 ∈ F` always.)
* `.undefined` — the `(Format, RoundingMode)` combination is degenerate
  and rounding has no semantic meaning. Currently fires only on
  `(p = 1, exp = ⊥, rm ∈ {.toOdd, .nearest .toEven})`. -/
inductive RoundResult where
  | finite (d : Dyadic) : RoundResult
  | overflow (positive : Bool) : RoundResult
  | undefined : RoundResult

namespace RoundResult

/-- Pointwise negation on `RoundResult`. `.finite y` maps to `.finite (-y)`;
`.overflow positive` flips the sign bit; `.undefined` is a fixed point. -/
def neg : RoundResult → RoundResult
  | .finite y    => .finite (-y)
  | .overflow b  => .overflow !b
  | .undefined   => .undefined

@[simp] theorem neg_finite (y : Dyadic) : (RoundResult.finite y).neg = .finite (-y) := rfl
@[simp] theorem neg_overflow (b : Bool) :
    (RoundResult.overflow b).neg = .overflow !b := rfl
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

/-! ### The specification relation `Rounds`

`Rounds F rm x r : Prop` asserts that `r : RoundResult` is *the* answer
that mode `rm` gives for input `x : ℝ` in format `F`:

* `Rounds F rm x .undefined`  ↔  `F.IsUndefined rm`.
* `Rounds F rm x .overflow`   ↔  not undefined *and* the unbounded
                                 rounding produces a value that
                                 violates `F.b`. (IEEE-style overflow.)
* `Rounds F rm x (.finite y)` ↔  not undefined *and* `y` is the
                                 unbounded rounding *and* `y` fits the
                                 bound `F.b`.

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

-- `ParityFormat.IsOdd` and `ParityFormat.IsEven` live in
-- `Mpfx/Format/Parity.lean`, built on `Format.numDigits` (digit-count lemma) +
-- `Dyadic.IsRepresentableAtP`.

/-- The finite-result rounding spec: when `r = .finite y`, this is the
mode-specific condition `y` must satisfy. Lifted out of `Rounds` so the
`.overflow` clause can quantify over its negation. -/
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

/-- Per-mode, per-result rounding-specification predicate. Dispatches on
the `RoundResult` constructor; the mode-spec is always against
`F.unbounded` and the bound `F.b` is checked separately. -/
def Rounds (F : FiniteFormat) (rm : RoundingMode) (x : ℝ) (r : RoundResult) :
    Prop :=
  match r with
  | .undefined   => F.IsUndefined rm
  | .overflow b  =>
      ¬ F.IsUndefined rm ∧
      ∃ y, RoundsFinite F.unbounded rm x y ∧ ¬ Format.boundOK F.b y ∧
           (b ↔ (0 : ℚ) < (y : ℚ))
  | .finite y    =>
      ¬ F.IsUndefined rm ∧
      RoundsFinite F.unbounded rm x y ∧ Format.boundOK F.b y

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

/-- Package an out-of-bound unbounded rounding as an overflow `Rounds`
result (with the sign bit computed from the witness). -/
theorem rounds_overflow_of_not_boundOK {F : FiniteFormat} {rm : RoundingMode}
    {x : ℝ} {y : Dyadic} (h₁u : ¬ F.IsUndefined rm)
    (hy : RoundsFinite F.unbounded rm x y) (hbOK : ¬ Format.boundOK F.b y) :
    ∃ b, Rounds F rm x (.overflow b) :=
  ⟨decide ((0 : ℚ) < (y : ℚ)), h₁u, y, hy, hbOK, by simp⟩

end Mpfx
