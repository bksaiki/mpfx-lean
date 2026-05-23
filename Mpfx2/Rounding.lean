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
def IsFaithfulRound (F : Format) (x : ℝ) (y : Dyadic) : Prop :=
  (y ∈ F ∧ (y : ℝ) ≤ x ∧ ∀ z : Dyadic, z ∈ F → (z : ℝ) ≤ x → (z : ℝ) ≤ (y : ℝ)) ∨
  (y ∈ F ∧ x ≤ (y : ℝ) ∧ ∀ z : Dyadic, z ∈ F → x ≤ (z : ℝ) → (y : ℝ) ≤ (z : ℝ))

-- `ParityFormat.IsOdd` and `ParityFormat.IsEven` live in
-- `Mpfx2/Format.lean`, built on `Format.numDigits` (Lemma 5.1) +
-- `Dyadic.IsRepresentableAtP`.

/-- The finite-result rounding spec: when `r = .finite y`, this is the
mode-specific condition `y` must satisfy. Lifted out of `Rounds` so the
`.overflow` clause can quantify over its negation. -/
def RoundsFinite (F : Format) (rm : RoundingMode) (x : ℝ) (y : Dyadic) : Prop :=
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

/-- Per-mode, per-result rounding-specification predicate. Dispatches on
the `RoundResult` constructor; the mode-spec is always against
`F.unbounded` and the bound `F.b` is checked separately. -/
def Rounds (F : Format) (rm : RoundingMode) (x : ℝ) (r : RoundResult) : Prop :=
  match r with
  | .undefined => F.IsUndefined rm
  | .overflow  =>
      ¬ F.IsUndefined rm ∧
      ∃ y, RoundsFinite F.unbounded rm x y ∧ ¬ Format.boundOK F.b y
  | .finite y  =>
      ¬ F.IsUndefined rm ∧
      RoundsFinite F.unbounded rm x y ∧ Format.boundOK F.b y

end Mpfx2
