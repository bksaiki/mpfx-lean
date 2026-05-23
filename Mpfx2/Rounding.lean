import Mpfx2.Format

/-!
# Rounding (Mpfx2)

Two parallel formalizations of rounding, à la FLoPS
(`rutgers-apl/FLoPS`):

* `Rounds F rm x y : Prop` — the *specification* relation.
* `rnd F rm x : RoundResult` — the *constructive* function. Total over
  `ℝ`. Three outcomes:
  - `.finite d` — `d : Dyadic` is the rounded value.
  - `.overflow` — `|x|` exceeds the format's magnitude bound.
  - `.undefined` — the format/mode pair is degenerate:
    * `(p = ⊤, exp = ⊥)` — fully unconstrained.
    * `(p = 1, exp = ⊥, rm = ToOdd)` — parity meaningless.

`rnd` is **constructive** (no `Classical.choose`): it computes the
canonical exponent via `Int.log` and the integer significand via
`Int.floor`/`Int.ceil`, then packages as a `Dyadic.ofIntZpow`. It is
`noncomputable` only because `Int.log : ℝ → ℤ` is.

## Status

Done:
* `RoundingMode` (7 modes), `RoundResult` ADT.
* `Format.IsUndefined`, `Format.IsOverflow`.
* Spec `Rounds` for `.toZero`, `.toNegative`, `.toPositive`, `.awayZero`.
* Constructive `rnd` for the four directed modes.
* Bridge-lemma triples (`_unique` + `_satisfies_rounds` + iff) for
  each directed mode. The `_unique` and `_satisfies_rounds` proofs are
  currently `sorry` — discharging them is the main outstanding work.
* `IsFaithfulRound` defined (uses RTN/RTP).
* `IsOdd`, `IsEven` declared `opaque` as TODOs (placeholders for
  `Mpfx/Digits.lean` port).

TODO (in priority order):
1. Discharge the eight `sorry`s in `*_unique` and `*_satisfies_rounds`
   for the four directed modes. Mostly arithmetic + structural induction
   on the canonical exponent.
2. Port `numDigits` and `IsRepresentableAtP` from `Mpfx/Digits.lean`,
   then define `IsOdd`/`IsEven` concretely (replacing the `opaque`s).
3. Extend `Rounds` to `.toOdd`, `.nearest .toEven`, `.nearest .awayZero`.
4. Extend `rnd`'s `rndInt` to those modes.
5. Bridge-lemma triples for the parity modes.
6. Restate the 7 valid + 10 counterexample double-rounding theorems
   from `Mpfx/DoubleRounding*.lean` using `rnd … = .finite …`.
7. (optional) Typeclass generalization à la FLoPS
   `Faithful`/`Monotonic`/`ValidRound`.
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
* `(1, ⊥, .toOdd)` — precision `1` with no quantum has no anchor for
  parity. -/
def Format.IsUndefined (F : Format) (rm : RoundingMode) : Prop :=
  (F.p = ⊤ ∧ F.exp = ⊥) ∨
  (F.p = (1 : ℕ+) ∧ F.exp = ⊥ ∧ rm = .toOdd)

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

/-- Per-mode rounding-specification predicate. -/
def Rounds (F : Format) (rm : RoundingMode) (x : ℝ) (y : Dyadic) : Prop :=
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
  -- TODO: .toOdd (faithful + odd-when-inexact)
  -- TODO: .nearest .toEven, .nearest .awayZero (closeness + tiebreak)
  | _ => True  -- placeholder; replace as modes are implemented

/-- A *faithful* rounding of `x`: `y` is either the floor (RTN) or the
ceiling (RTP) of `x` in `F`. RTO/RNE/RNA all sit inside this union. -/
def IsFaithfulRound (F : Format) (x : ℝ) (y : Dyadic) : Prop :=
  Rounds F .toNegative x y ∨ Rounds F .toPositive x y

/-- Parity (odd) of a Dyadic in a Format. **TODO:** port from
`Mpfx/Digits.lean` (requires `numDigits` and `IsRepresentableAtP`). -/
opaque IsOdd : Format → Dyadic → Prop

/-- Parity (even) of a Dyadic in a Format. **TODO:** port. -/
opaque IsEven : Format → Dyadic → Prop

/-! ### The constructive function `rnd`

FLoPS-style construction. Total over `ℝ`. Strategy:

1. If `Format.IsUndefined F rm`, return `.undefined`.
2. If `Format.IsOverflow F x`, return `.overflow`.
3. Otherwise, compute `e = canonicalExp F x` and `c = rndInt rm x e`,
   then wrap `c · 2^e` as a `Dyadic`.

No `Classical.choose`. The function is `noncomputable` because of
`Int.log : ℝ → ℤ`, not because of choice. -/

/-- Canonical exponent for representing `x` in `F`. Junk value `0` when
`Format.IsUndefined F _` (those cases are filtered earlier). -/
noncomputable def Format.canonicalExp (F : Format) (x : ℝ) : ℤ :=
  match F.p, F.exp with
  | ⊤, ⊥ => 0  -- junk; never used (filtered by IsUndefined)
  | ⊤, (e : ℤ) => e
  | (p : ℕ+), ⊥ =>
      if x = 0 then 0 else Int.log 2 |x| + 1 - (p : ℤ)
  | (p : ℕ+), (e : ℤ) =>
      if x = 0 then e
      else max (Int.log 2 |x| + 1 - (p : ℤ)) e

/-- Integer-rounding step. Picks the integer `c` for which `c · 2^e` is
the F-grid value selected by mode `rm` from input `x`.
- `.toZero`: truncate toward `0`.
- `.toNegative`/`.toPositive`/`.awayZero`: floor/ceiling/away.
- Parity modes: TODO. -/
noncomputable def rndInt (rm : RoundingMode) (x : ℝ) (e : ℤ) : ℤ :=
  let s := x * (2 : ℝ) ^ (-e)
  match rm with
  | .toZero    => if 0 ≤ x then ⌊s⌋ else ⌈s⌉
  | .toNegative => ⌊s⌋
  | .toPositive => ⌈s⌉
  | .awayZero   => if 0 ≤ x then ⌈s⌉ else ⌊s⌋
  -- TODO: .toOdd, .nearest _ (need parity tie-breaking)
  | _ => ⌊s⌋   -- placeholder

/-- The rounded value of `x` in `F` under mode `rm`, as a `RoundResult`. -/
noncomputable def rnd (F : Format) (rm : RoundingMode) (x : ℝ) : RoundResult :=
  open Classical in
  if F.IsUndefined rm then
    .undefined
  else if F.IsOverflow x then
    .overflow
  else
    let e := F.canonicalExp x
    let c := rndInt rm x e
    .finite (Dyadic.ofIntZpow c e)

/-! ### Bridge lemmas

`rnd_eq_finite_iff_rounds` (per mode) connects the constructive function
to the `Rounds` spec. The forward direction follows by computation +
mode-specific arithmetic; the reverse needs *uniqueness* of `Rounds`
(any two values satisfying it are equal). -/

/-- Uniqueness of `Rounds F .toZero`. -/
theorem rounds_toZero_unique
    {F : Format} {x : ℝ} {y₁ y₂ : Dyadic}
    (h₁ : Rounds F .toZero x y₁) (h₂ : Rounds F .toZero x y₂) :
    y₁ = y₂ := by
  -- Both `|y₁| ≤ |y₂|` and `|y₂| ≤ |y₁|` from minimality; combined
  -- with sign agreement, this forces y₁ = y₂.
  -- TODO: discharge from `Rounds .toZero` clauses.
  sorry

/-- `rnd` produces a value satisfying `Rounds F .toZero` (under non-degenerate
domain conditions). The heart of the soundness of the constructive `rnd`. -/
theorem rnd_toZero_satisfies_rounds
    (F : Format) (x : ℝ)
    (_h_def : ¬ F.IsUndefined .toZero)
    (_h_ovf : ¬ F.IsOverflow x) :
    Rounds F .toZero x (Dyadic.ofIntZpow
      (rndInt .toZero x (F.canonicalExp x)) (F.canonicalExp x)) := by
  -- TODO: discharge from definitions. Requires showing membership
  -- (precisionAtMost, quantumAtLeast, boundOK) plus the minimality clause.
  sorry

theorem rnd_eq_finite_iff_rounds_toZero
    (F : Format) (x : ℝ) (y : Dyadic)
    (h_def : ¬ F.IsUndefined .toZero)
    (h_ovf : ¬ F.IsOverflow x) :
    rnd F .toZero x = .finite y ↔ Rounds F .toZero x y := by
  unfold rnd
  simp only [if_neg h_def, if_neg h_ovf]
  constructor
  · intro h_eq
    have h_inj :
        y = Dyadic.ofIntZpow (rndInt .toZero x (F.canonicalExp x)) (F.canonicalExp x) := by
      injection h_eq with h; exact h.symm
    rw [h_inj]
    exact rnd_toZero_satisfies_rounds F x h_def h_ovf
  · intro h_rounds
    have h_witness := rnd_toZero_satisfies_rounds F x h_def h_ovf
    have h_eq := rounds_toZero_unique h_rounds h_witness
    rw [h_eq]

/-! ### RTN / RTP / RAZ bridges (analogous to RTZ; proofs deferred) -/

theorem rounds_toNegative_unique
    {F : Format} {x : ℝ} {y₁ y₂ : Dyadic}
    (_h₁ : Rounds F .toNegative x y₁) (_h₂ : Rounds F .toNegative x y₂) :
    y₁ = y₂ := by
  -- Both y₁, y₂ are the maximum F-element ≤ x; hence y₁ ≤ y₂ and y₂ ≤ y₁.
  sorry

theorem rnd_toNegative_satisfies_rounds
    (F : Format) (x : ℝ)
    (_h_def : ¬ F.IsUndefined .toNegative)
    (_h_ovf : ¬ F.IsOverflow x) :
    Rounds F .toNegative x (Dyadic.ofIntZpow
      (rndInt .toNegative x (F.canonicalExp x)) (F.canonicalExp x)) := by
  sorry

theorem rnd_eq_finite_iff_rounds_toNegative
    (F : Format) (x : ℝ) (y : Dyadic)
    (h_def : ¬ F.IsUndefined .toNegative)
    (h_ovf : ¬ F.IsOverflow x) :
    rnd F .toNegative x = .finite y ↔ Rounds F .toNegative x y := by
  unfold rnd
  simp only [if_neg h_def, if_neg h_ovf]
  constructor
  · intro h_eq
    have h_inj :
        y = Dyadic.ofIntZpow (rndInt .toNegative x (F.canonicalExp x)) (F.canonicalExp x) := by
      injection h_eq with h; exact h.symm
    rw [h_inj]
    exact rnd_toNegative_satisfies_rounds F x h_def h_ovf
  · intro h_rounds
    have h_witness := rnd_toNegative_satisfies_rounds F x h_def h_ovf
    rw [rounds_toNegative_unique h_rounds h_witness]

theorem rounds_toPositive_unique
    {F : Format} {x : ℝ} {y₁ y₂ : Dyadic}
    (_h₁ : Rounds F .toPositive x y₁) (_h₂ : Rounds F .toPositive x y₂) :
    y₁ = y₂ := by
  sorry

theorem rnd_toPositive_satisfies_rounds
    (F : Format) (x : ℝ)
    (_h_def : ¬ F.IsUndefined .toPositive)
    (_h_ovf : ¬ F.IsOverflow x) :
    Rounds F .toPositive x (Dyadic.ofIntZpow
      (rndInt .toPositive x (F.canonicalExp x)) (F.canonicalExp x)) := by
  sorry

theorem rnd_eq_finite_iff_rounds_toPositive
    (F : Format) (x : ℝ) (y : Dyadic)
    (h_def : ¬ F.IsUndefined .toPositive)
    (h_ovf : ¬ F.IsOverflow x) :
    rnd F .toPositive x = .finite y ↔ Rounds F .toPositive x y := by
  unfold rnd
  simp only [if_neg h_def, if_neg h_ovf]
  constructor
  · intro h_eq
    have h_inj :
        y = Dyadic.ofIntZpow (rndInt .toPositive x (F.canonicalExp x)) (F.canonicalExp x) := by
      injection h_eq with h; exact h.symm
    rw [h_inj]
    exact rnd_toPositive_satisfies_rounds F x h_def h_ovf
  · intro h_rounds
    have h_witness := rnd_toPositive_satisfies_rounds F x h_def h_ovf
    rw [rounds_toPositive_unique h_rounds h_witness]

theorem rounds_awayZero_unique
    {F : Format} {x : ℝ} {y₁ y₂ : Dyadic}
    (_h₁ : Rounds F .awayZero x y₁) (_h₂ : Rounds F .awayZero x y₂) :
    y₁ = y₂ := by
  sorry

theorem rnd_awayZero_satisfies_rounds
    (F : Format) (x : ℝ)
    (_h_def : ¬ F.IsUndefined .awayZero)
    (_h_ovf : ¬ F.IsOverflow x) :
    Rounds F .awayZero x (Dyadic.ofIntZpow
      (rndInt .awayZero x (F.canonicalExp x)) (F.canonicalExp x)) := by
  sorry

theorem rnd_eq_finite_iff_rounds_awayZero
    (F : Format) (x : ℝ) (y : Dyadic)
    (h_def : ¬ F.IsUndefined .awayZero)
    (h_ovf : ¬ F.IsOverflow x) :
    rnd F .awayZero x = .finite y ↔ Rounds F .awayZero x y := by
  unfold rnd
  simp only [if_neg h_def, if_neg h_ovf]
  constructor
  · intro h_eq
    have h_inj :
        y = Dyadic.ofIntZpow (rndInt .awayZero x (F.canonicalExp x)) (F.canonicalExp x) := by
      injection h_eq with h; exact h.symm
    rw [h_inj]
    exact rnd_awayZero_satisfies_rounds F x h_def h_ovf
  · intro h_rounds
    have h_witness := rnd_awayZero_satisfies_rounds F x h_def h_ovf
    rw [rounds_awayZero_unique h_rounds h_witness]

end Mpfx2
