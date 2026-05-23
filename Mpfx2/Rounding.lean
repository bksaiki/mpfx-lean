import Mpfx2.Format

/-!
# Rounding spec (Mpfx2, relational layer)

The constructive-logic layer of the rounding architecture. Defines:

* `RoundingMode`, `TieBreak`, `RoundResult` — the modes and the
  result ADT (`.finite`, `.overflow`, `.undefined`).
* `Format.IsUndefined`, `Format.IsOverflow` — when each `RoundResult`
  case fires.
* `IsFaithfulRound` — RoundDown or RoundUp.
* `Rounds : Format → RoundingMode → ℝ → RoundResult → Prop` — the
  specification relation, all seven modes.

Everything here is in pure constructive logic — no `Classical.choose`,
no implicit `Classical.dec` from `Real`-comparison `if-then-else`s.
Anything reasoned about `Rounds` alone stays constructive.

The companion file **`Mpfx2/RoundOp.lean`** adds the noncomputable
function `rnd` and the bridge `rnd_iff_rounds`. That file is where the
classical commitment lives.
-/

namespace Mpfx2

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
* `.overflow` — `|x|` exceeds the format's magnitude bound (no valid
  in-format result).
* `.undefined` — the `(Format, RoundingMode)` combination is degenerate
  and rounding has no semantic meaning. Currently fires only on
  `(p = 1, exp = ⊥, rm = ToOdd)`. -/
inductive RoundResult where
  | finite (d : Dyadic) : RoundResult
  | overflow : RoundResult
  | undefined : RoundResult

/-- The format/mode pair is degenerate (no meaningful rounding):

* `(⊤, ⊥, _)` — fully unconstrained; for non-dyadic `x` there is no
  canonical exponent, since dyadics are dense in `ℝ` but not closed
  under limits.
* `(1, ⊥, rm)` for `rm ∈ {.toOdd, .nearest .toEven}` — precision `1`
  with no quantum has no anchor for parity, so the modes that consult
  `IsOdd`/`IsEven` are meaningless. -/
def Format.IsUndefined (F : Format) (rm : RoundingMode) : Prop :=
  (F.p = ⊤ ∧ F.exp = ⊥) ∨
  (F.p = (1 : ℕ+) ∧ F.exp = ⊥ ∧
    (rm = .toOdd ∨ rm = .nearest .toEven))

/-- `x` overflows `F.b`: `F.b` is finite and `|x|` strictly exceeds it. -/
def Format.IsOverflow (F : Format) (x : ℝ) : Prop :=
  match F.b with
  | ⊤ => False
  | (b : NonNegDyadic) => ((b.val : Dyadic) : ℝ) < |x|

-- `Decidable` instances on these predicates would be computable iff
-- equality on `ℝ` were, which it isn't.  We use `Classical.dec` at call
-- sites in `rnd` (which is itself `noncomputable`).

/-! ### The specification relation `Rounds`

For each mode, `Rounds F rm x y` is a `Prop` asserting that `y : Dyadic`
is *the* rounding of `x : ℝ` in `F` under mode `rm`. This is the
*reference* against which the constructive `rnd` is verified. -/

/-- A *faithful* rounding of `x`: `y ∈ F` is either the largest F-element
≤ `x` (RTN) or the smallest F-element ≥ `x` (RTP). All of RTO, RNE, RNA
require their result to be faithful. -/
def IsFaithfulRound (F : Format) (x : ℝ) (y : Dyadic) : Prop :=
  (y ∈ F ∧ (y : ℝ) ≤ x ∧ ∀ z : Dyadic, z ∈ F → (z : ℝ) ≤ x → (z : ℝ) ≤ (y : ℝ)) ∨
  (y ∈ F ∧ x ≤ (y : ℝ) ∧ ∀ z : Dyadic, z ∈ F → x ≤ (z : ℝ) → (y : ℝ) ≤ (z : ℝ))

-- `ParityFormat.IsOdd` and `ParityFormat.IsEven` live in
-- `Mpfx2/Format.lean`, built on `Format.numDigits` (Lemma 5.1) +
-- `Dyadic.IsRepresentableAtP`.

/-- Per-mode, per-result rounding-specification predicate. The
`RoundResult`-typed conclusion folds in the `.undefined` and `.overflow`
cases uniformly:

* `Rounds F rm x .undefined`  iff  `F.IsUndefined rm`.
* `Rounds F rm x .overflow`   iff  `¬ IsUndefined ∧ IsOverflow`.
* `Rounds F rm x (.finite y)` iff  `¬ IsUndefined ∧ ¬ IsOverflow ∧
                                    y ∈ F ∧ <mode-specific spec on y>`.

For the parity modes (`.toOdd`, `.nearest .toEven`), the `IsOdd`/`IsEven`
predicates require a `ParityFormat`. Inside the `.finite` branch we
have `¬ F.IsUndefined rm` in scope, which is exactly the `ParityFormat`
invariant for those modes — so we use an existential `∃ F' : ParityFormat`
to bring the strengthened structure into the spec. -/
def Rounds (F : Format) (rm : RoundingMode) (x : ℝ) (r : RoundResult) : Prop :=
  match r with
  | .undefined => F.IsUndefined rm
  | .overflow  => ¬ F.IsUndefined rm ∧ F.IsOverflow x
  | .finite y  =>
      ¬ F.IsUndefined rm ∧ ¬ F.IsOverflow x ∧ y ∈ F ∧
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
            ∃ F' : ParityFormat, F'.toFormat = F ∧ F'.IsOdd y)
      | .nearest .toEven =>
          IsFaithfulRound F x y ∧
          (∀ z : Dyadic, z ∈ F → IsFaithfulRound F x z →
            |x - (y : ℝ)| ≤ |x - (z : ℝ)|) ∧
          ((∃ z : Dyadic, z ∈ F ∧ IsFaithfulRound F x z ∧
              z ≠ y ∧ |x - (y : ℝ)| = |x - (z : ℝ)|) →
            ∃ F' : ParityFormat, F'.toFormat = F ∧ F'.IsEven y)
      | .nearest .awayZero =>
          IsFaithfulRound F x y ∧
          (∀ z : Dyadic, z ∈ F → IsFaithfulRound F x z →
            |x - (y : ℝ)| ≤ |x - (z : ℝ)|) ∧
          (∀ z : Dyadic, z ∈ F → IsFaithfulRound F x z →
              z ≠ y → |x - (y : ℝ)| = |x - (z : ℝ)| → |(z : ℝ)| ≤ |(y : ℝ)|)

end Mpfx2
