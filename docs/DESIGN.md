# Formalization design

Notes on the structural choices behind `mpfx-lean`. None of this is needed to
*check* the results (see the README for those) — it explains how the
development is put together.

## Layered format subtypes

`Format` carries only the natural type-level constraints:

```lean
structure Format where
  p   : WithTop ℕ+          -- precision ≥ 1, ⊤ = no precision constraint
  exp : WithBot ℤ           -- min-quantum exponent, ⊥ = no quantum constraint
  b   : WithTop NonNegDyadic -- magnitude bound ≥ 0, ⊤ = unbounded
```

`ℕ+` bakes in `p ≥ 1` and `NonNegDyadic` bakes in `b ≥ 0`, so those invariants
never need to be threaded as hypotheses. Two subtypes refine it:

- `FiniteFormat extends Format` adds `finite : p ≠ ⊤ ∨ exp ≠ ⊥` — rules out the
  doubly-unbounded format, which has no well-defined rounding.
- `ParityFormat extends FiniteFormat` adds `parity : p ≠ 1 ∨ exp ≠ ⊥` — the
  extra condition under which `IsOdd` / `IsEven` are well-anchored.

Rounding (`Rounds`, `rnd`) is stated over `FiniteFormat`; parity (`IsOdd`,
`IsEven`, Lemma 5.3) over `ParityFormat`. Parent fields are accessed directly
through inheritance (`F.p`, not `F.toFormat.p`); `.toFormat` appears only where
an operator lives on `Format` itself (`⊆`, `withBound`, `boundAfterNext`).

## `ℚ` substrate for `Dyadic`

`Dyadic` is the subring of dyadic rationals **inside `ℚ`**, not `ℝ`:

```lean
def IsDyadic (x : ℚ) : Prop := ∃ c e : ℤ, x = (c : ℚ) * (2 : ℚ) ^ e
abbrev Dyadic : Type := dyadicSubring  -- Subring ℚ
```

This gives decidable equality and a decidable linear order for free, while
retaining Mathlib's algebra/tactic suite. `ℝ` is confined to where it is
genuinely intrinsic — the real input `x` being rounded, and the
`Int.log` / `Int.floor` machinery (`numDigits`, the rounding spec comparing
dyadics against a real). The composite coercion `Dyadic → ℝ` factors as
`Dyadic → ℚ → ℝ`, and the `ℚ ↔ ℝ` boundary is localized to named bridge lemmas
(`coe_real_*`, `precisionAtMost_coe_real`, `quantumAtLeast_coe_real`).

`precisionAtMost` / `quantumAtLeast` and `IsRepresentableAtP` are all
`ℚ`-valued; only `numDigits` (which needs `Int.log`) is real-valued.

## Constructive rounding alongside the spec relation

Two complementary views of rounding:

- `Rounds : FiniteFormat → RoundingMode → ℝ → RoundResult → Prop` (and its
  finite-result core `RoundsFinite`) — the specification relation. The
  double-rounding theorems are stated against this.
- `rnd : FiniteFormat → RoundingMode → ℝ → RoundResult` — a function computing
  the result via `Int.log` + `Int.floor`/`Int.ceil` (FLoPS-style, no
  `Classical.choose`), bridged to the relation by
  `rnd_iff_rounds : rnd F rm x = r ↔ Rounds F rm x r`.

The constructive/classical split is at the file level: `Rounding.lean` is
constructive; `RoundOp.lean` makes the classical commitment (`rnd` is
`noncomputable` because real comparisons aren't computably decidable, and
`Int.log : ℝ → ℤ`). The overflow **sign bit** is a decidable `ℚ` comparison.

## RoundingMode coverage

`RoundingMode` covers the four IEEE 754 directed/nearest modes plus the
paper's round-to-odd:

- directed: `toNegative` (RTN), `toPositive` (RTP), `toZero` (RTZ),
  `awayZero` (RAZ);
- `toOdd` (RTO);
- `nearest tb` with `tb : TieBreak` ∈ {`toEven` (RNE), `awayZero` (RNA)}.

`rndRTO_RN` is stated once over an arbitrary `tb`, covering RNE and RNA
together.
