# Formalization design

Notes on the structural choices behind `mpfx-lean`. None of this is needed to
*check* the results (see the README for those) — it explains how the
development is put together.

## Layered format subtypes

`Format` carries only the natural type-level constraints:

```lean
structure Format where
  p        : Prec         -- precision; 0 = trivial {0}, ⊤ = no constraint
  exp      : QExp         -- min-quantum exponent, ⊥ = no quantum constraint
  b        : Bound        -- magnitude bound ≥ 0, ⊤ = unbounded
  specials : Set Special  -- which of ±Inf, NaN the format has
```

`specials` has no default: every format states it (see "Special values and
overflow" below).

The three field types are abbreviations, defined in `Mpfx/Dyadic.lean`:

| abbrev  | unfolds to             | eliminator        |
| ------- | ---------------------- | ----------------- |
| `Prec`  | `ℕ∞`                   | `ENat.recTopCoe`  |
| `QExp`  | `WithBot ℤ`            | `QExp.recBotCoe`  |
| `Bound` | `WithTop NonNegDyadic` | `Bound.recTopCoe` |

`Prec` is `ℕ∞` rather than `WithTop ℕ` so that the `ENat` lemma namespace
applies and mathlib's own `ENat.recTopCoe` can be used. The price is that `ENat`
is a `def`, not a reducible wrapper around `Option`: `⊤`, `1` and numerals at
type `ℕ∞` do **not** reduce into the `Option` matcher, so the `match`-on-`F.p`
definitions (`canonicalExp`, `numDigits`, `next`) need an explicit `rfl` after
`rw`/`simp` has substituted `F.p`. Their evaluator lemmas
(`numDigits_top_coe` and friends) exist so callers rarely meet this.

**Always case-split these with their eliminator, never a bare `cases`.** They are
reducible, so `cases` unfolds past `WithTop`/`WithBot` to `Option` and asks for
`none`/`some`. The eliminators also state the `coe` branch with the `↑x`
coercion, which matters for `Prec`: `WithTop ℕ` has a `NatCast` instance, so
`(p : Prec)` is `WithTop.some (Nat.cast p)` while a raw `cases` yields
`WithTop.some p` — defeq but not syntactically equal, so `rw`/`simp` with
`↑p`-shaped lemmas stop firing. `QExp` and `Bound` have no such instance
(`(e : QExp)` is `WithBot.some e` directly), so for them the eliminator is
purely about getting the right alternative names.

`p = 0` is the trivial format: `|c| < 2^0 = 1` forces `c = 0`
(`Dyadic.precisionAtMost_zero_iff_eq_zero`). `NonNegDyadic` bakes in `b ≥ 0`, so
that invariant never needs threading. Two subtypes refine `Format`:

- `FiniteFormat extends Format` adds `finite : p ≠ ⊤ ∨ exp ≠ ⊥` — rules out the
  doubly-unbounded format, which has no well-defined rounding — and
  `pos : p ≠ 0`, which recovers the `p ≥ 1` that `ℕ+` used to give for free.
  Use `FiniteFormat.p_pos` to get `0 < p` from `hp : F.p = ↑p`. At `Format`
  level, `Format.Nontrivial.p_ne_zero` plays the same role.
- `ParityFormat extends FiniteFormat` adds `parity : p ≠ 1 ∨ exp ≠ ⊥` — the
  extra condition under which `IsOdd` / `IsEven` are well-anchored.

Rounding (`Rounds`, `rnd`) is stated over `FiniteFormat`; parity (`IsOdd`,
`IsEven`, RTO-padding lemma) over `ParityFormat`. Parent fields are accessed directly
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

## An explicit rounding function alongside the spec relation

Two complementary views of rounding:

- `Rounds F S O rm : WithSpecial ℝ → RoundResult → Prop`, and its core
  `RoundsFinite F rm : ℝ → Dyadic → Prop` (the mode's rounding of a real, with
  no bound check), are the specification relations. The double-rounding
  theorems are stated against `RoundsFinite`, then lifted to `rnd`.
- `rnd F S O rm : WithSpecial ℝ → RoundResult` is a function computing the
  result via `Int.log` + `Int.floor`/`Int.ceil` (FLoPS-style, no
  `Classical.choose`), bridged to the relation by
  `rnd_iff_rounds : rnd F S O rm v = r ↔ Rounds F S O rm v r`.

"Explicit" means `rnd` is defined by a formula, not chosen from the spec;
it does not mean constructive logic. `rnd` is `noncomputable` (real
comparisons aren't computably decidable, and `Int.log : ℝ → ℤ`), and the
proofs are classical throughout: every theorem depends on `propext`,
`Classical.choice` and `Quot.sound`, as is usual for Mathlib's `ℝ` (FLoPS
too). The overflow **sign bit** is a decidable `ℚ` comparison.

## Special values and overflow

Inputs and outputs are `WithSpecial`: a finite value or a `Special`
(`inf (negative : Bool)` or `nan`). A format's values are
`Format.values F : Set (WithSpecial Dyadic)`, the finite members plus
`F.specials`. They are a `Set` rather than a second `Membership` instance,
since `Membership`'s element type is an `outParam` and would clash with
`Membership Dyadic Format`.

**Specials are values; overflow is an event.** `±Inf` and NaN are inputs and
outputs. Overflow happens to a real input and never appears as a value: what it
produces is chosen by the format. `rnd` takes two tables of `F`, independent
of the rounding mode:

| Table | Keyed by | Says |
| --- | --- | --- |
| `SpecialMap F` | `Special` | where a special input goes |
| `OverflowMap F` | `Bool` (`negative`) | where an overflowing real goes |

Each entry must be one of `F.values`. A table follows the mode only when built
to: `OverflowMap.ieee F rm` is IEEE 754 §7.4, so RTP sends `+overflow` to
`+Inf` but `−overflow` to `−maxFinite`. The other standard tables (all in
`Mpfx/Rounding/Special.lean`) are `SpecialMap.exact`/`saturate`/`toNaN` and
`OverflowMap.saturate`/`toNaN`. Tables are arbitrary; conditions on them (e.g.
`OverflowAgrees` for double rounding) are named predicates used as
hypotheses, so OCP E4M3 or P3109 saturation fit without special cases.

`RoundResult` is `value (v : WithSpecial Dyadic) | undefined`. `undefined` is
returned only for real inputs, when `(F, rm)` has no well-defined rounding
(`F.IsUndefined rm`: `p = 1`, `exp = ⊥` and RTO or RNE); special inputs always
go through `S`.

**Why overflow is a predicate.** `Overflows F rm x` says the unbounded
rounding of `x` leaves `F`'s bound; `RoundsInBound F rm x y` says it is `y`
and fits. A saturating table maps overflow to `±maxFinite`, which is also an
ordinary result, so overflow cannot be read off `rnd`'s output. Double rounding
still depends on it: whether `F₂` and `F₁` overflow on the same inputs decides
which table conditions the equality `rnd₁ (rnd₂ v) = rnd₁ v` needs. So
overflow is kept as a predicate on the input, not a constructor of the result.

Signed zero is out of scope: `Dyadic` has one zero, and no table touches it.

## RoundingMode coverage

`RoundingMode` covers the four IEEE 754 directed/nearest modes plus the
paper's round-to-odd:

- directed: `toNegative` (RTN), `toPositive` (RTP), `toZero` (RTZ),
  `awayZero` (RAZ);
- `toOdd` (RTO);
- `nearest tb` with `tb : TieBreak` ∈ {`toEven` (RNE), `awayZero` (RNA)}.

`roundsRTO_RN_finite` is stated once over an arbitrary `tb`, covering RNE and RNA
together.
