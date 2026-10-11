# mpfx-lean

A Lean 4 / Mathlib (`v4.29.0`) formalization of the abstract floating-point
results in *When Double Rounding is Correct* (Saiki, Zorn, Richey, Tatlock).

The paper studies the abstract format `𝒜(p, exp, b)` — `p` binary digits of
precision, minimum quantum `2^exp`, magnitude bound `b` — and characterizes
when rounding a real into a wide format then into a narrow one agrees with
rounding directly into the narrow format. This development mechanizes the
appendix, and extends it with special values: a format also states which of
`±Inf` and NaN it contains, and rounding is total over reals, infinities and
NaN, with overflow sent to a format-chosen value.

## Theorems

Each entry gives the paper result, the Lean name (relative to `namespace
Mpfx`), and its file. To inspect a statement, qualify with `Mpfx.`, e.g.
`#check @Mpfx.Format.containsPrec` or `#check @Mpfx.roundsRTO_RN_finite`.

### §5.1 — Format containment (Fig. 8)

| Paper | Lean | File |
| --- | --- | --- |
| `𝒜-Contains-Prec` | `Format.containsPrec` | `Mpfx/Format/Containment.lean` |
| `𝒜-Contains-Sub` | `Format.containsSub` | `Mpfx/Format/Containment.lean` |
| Completeness (`F₁ ⊆ F₂` iff a rule fires) | `Format.subset_iff_contains` | `Mpfx/Format/Containment.lean` |

Beyond the paper, `F₁ ⊆ F₂` also requires `F₁.specials ⊆ F₂.specials`, and both
rules carry that conjunct.

### Supporting lemmas

| Paper | Lean | File |
| --- | --- | --- |
| Lemma 5.1 (digit position is a function of `(p, exp, x)`) | `FiniteFormat.numDigits` | `Mpfx/Format/Defs.lean` |
| Lemma 5.2 (`w₂ = w₁ + k`) | `FiniteFormat.numDigits_extend` | `Mpfx/Format/Containment.lean` |
| Lemma 5.3 (RTO padding preserves representability) | `IsOdd.transfer_of_subset` | `Mpfx/Format/Digits.lean` |

### §5.2 — Correct double rounding (Fig. 9)

All positive rules, in `Mpfx/DoubleRounding/`, at three levels:

- **Finite form**: given `RoundsFinite F₂ rm₂ x z` and `RoundsFinite F₁ rm₁ z w`
  (with the stated containment of `F₁` in `F₂`), then `RoundsFinite F₁ rm₁ x w`.
  RTO → RTZ/RAZ/RN also have a `…_finite_of_extend` form taking the plain
  containment `F₁.extend k ⊆ F₂` and `2 ≤ F₂.p`.
- **Total form**, with bounds: either rounding `x` directly in `F₁` overflows
  (`Overflows`), or rounding `x` into `F₂` and the result into `F₁` stays in
  bound and agrees with it (`RoundsInBound`).
- **With tables**, on `rnd` over every input (real, `±Inf`, NaN):
  `rnd₁ (rnd₂ v) = rnd₁ v`. See below.

| Paper | Finite form | Total form | With tables |
| --- | --- | --- | --- |
| `rnd-RTZ-RTZ` | `roundsRTZ_RTZ_finite` | `roundsRTZ_RTZ_inBound` | `rndRTZ_RTZ` |
| `rnd-RAZ-RAZ` | `roundsRAZ_RAZ_finite` | `roundsRAZ_RAZ_inBound` | `rndRAZ_RAZ` |
| `rnd-RTO-RTO` | `roundsRTO_RTO_finite` | `roundsRTO_RTO_inBound` | `rndRTO_RTO` |
| `rnd-RTO-RTZ` | `roundsRTO_RTZ_finite` | `roundsRTO_RTZ_inBound` | `rndRTO_RTZ` |
| `rnd-RTO-RAZ` | `roundsRTO_RAZ_finite` | `roundsRTO_RAZ_inBound` | `rndRTO_RAZ` |
| `rnd-RTO-RNE` / `rnd-RTO-RNA` | `roundsRTO_RN_finite` (both tie-breaks) | `roundsRTO_RN_inBound` | `rndRTO_RN` |
| RTP→RTP, RTN→RTN (IEEE directed) | `roundsRTP_RTP_finite`, `roundsRTN_RTN_finite` | — | — |

### Double rounding with special values

`rnd F S O rm : WithSpecial ℝ → RoundResult` rounds with two tables of `F`:
`S : SpecialMap` says where `±Inf` and NaN inputs go, `O : OverflowMap` where
overflow goes, by sign. The table-level rules (`rndRTZ_RTZ`, …, in
`Mpfx/DoubleRounding/Special.lean`) take the plain containment and three table
conditions:

| Condition | Meaning |
| --- | --- |
| `SpecialMap.Composes`, `OverflowMap.Composes` | `F₁` rounds each `F₂` table entry to the matching `F₁` entry |
| `OverflowAgrees` | where exactly one side overflows, the overflow tables give the other side's in-bound value |

`OverflowAgrees` holds for any tables under the paper's relaxed containment
(`OverflowAgrees.of_bound`; the rules in that form are `rndRTZ_RTZ_of_bound`,
…), and for saturating tables on both sides under the plain one
(`OverflowAgrees.of_saturate`). Standard tables that compose:
`SpecialMap.exact_composes`, `OverflowMap.composes_of_inf` (`±Inf`),
`OverflowMap.saturate_composes`. The IEEE 754 tables
(`OverflowMap.ieee`) compose for every rule but RTO → RTZ, where RTO
overflows to `±Inf` and RTZ saturates. `MpfxTest/DoubleRounding.lean` shows
that failure, and full IEEE instances of RTO → RN and RTZ → RTZ.

### §5.2 — Counterexamples for the invalid pairings

The ten mode pairings that are *not* correct double rounding, in
`namespace Mpfx.Cex` (`Mpfx/DoubleRounding/Counterexample.lean`). For every
parity format `F₁`, bounded or not, and every `F₂` satisfying the containment,
each exhibits a real `x` whose chained rounding disagrees with the direct
rounding, with no rounding overflowing (`Disagrees`: `∃ x z w y,
RoundsInBound F₂ rm₂ x z ∧ RoundsInBound F₁ rm₁ z w ∧ RoundsInBound F₁ rm₁ x y ∧
w ≠ y`). `Disagrees.rnd_ne` turns the witness into a failure of
`rnd₁ ∘ rnd₂ = rnd₁` for any `SpecialMap` and `OverflowMap`, at a finite input
with a finite intermediate; `no_rnd<rm₂>_<rm₁>` state that for each pairing
(with an RNE intermediate, given `¬ F₂.IsUndefined (.nearest .toEven)`), and
`no_rounds<rm₂>_<rm₁>` give the `Disagrees` witness itself.

The only hypothesis on `F₁` is a count of its positive values
(`Format.HasPositive`; one is `Nontrivial`):

| Pairing | Positive values of `F₁` | In bound (`Disagrees`) | On `rnd` |
| --- | --- | --- | --- |
| RNE → RTZ | 1 | `no_roundsRNE_RTZ` | `no_rndRNE_RTZ` |
| RAZ → RTZ | 1 | `no_roundsRAZ_RTZ` | `no_rndRAZ_RTZ` |
| RTZ → RNE | 1 | `no_roundsRTZ_RNE` | `no_rndRTZ_RNE` |
| RNE → RNE | 1 | `no_roundsRNE_RNE` | `no_rndRNE_RNE` |
| RTZ → RAZ | 2 | `no_roundsRTZ_RAZ` | `no_rndRTZ_RAZ` |
| RNE → RAZ | 2 | `no_roundsRNE_RAZ` | `no_rndRNE_RAZ` |
| RAZ → RTO | 2 | `no_roundsRAZ_RTO` | `no_rndRAZ_RTO` |
| RNE → RTO | 2 | `no_roundsRNE_RTO` | `no_rndRNE_RTO` |
| RAZ → RNE | 2 | `no_roundsRAZ_RNE` | `no_rndRAZ_RNE` |
| RTZ → RTO | 3 | `no_roundsRTZ_RTO` | `no_rndRTZ_RTO` |

An unbounded `F₁` has every count (`FiniteFormat.hasPositive_of_b_top`). The
counts are believed least, since with one fewer an `F₂` without a minimum quantum
appears to agree on every in-bound input, but that is not proved.

### Operation-specific double rounding (Roux 2014)

Beyond the paper: Pierre Roux, *Innocuous Double Rounding of Basic Arithmetic
Operations* (JFR 7(1), 2014), radix 2. Double rounding of an operation on
`F₁`-values is correct under a precision margin weaker than the generic rules
need. Finite form, over `F₁.unbounded` and `F₂.unbounded`.

| Operation | Condition | Lean | File |
| --- | --- | --- | --- |
| `x × y`, any modes | `p₂ ≥ 2p₁` | `rndMul_expBot`, `rndMul_expFinite` | `Mpfx/DoubleRounding/Mul.lean` |
| `x + y`, nearest | `p₂ ≥ 2p₁ + 1` | `rndAdd` | `Mpfx/DoubleRounding/Add.lean` |
| `√x`, nearest | `p₂ ≥ 2p₁ + 2` | `rndSqrt_expBot`, `rndSqrt_expFinite` | `Mpfx/DoubleRounding/Sqrt.lean` |
| `x / y`, nearest | `p₂ ≥ 2p₁` | `rndDiv_expBot`, `rndDiv_expFinite` | `Mpfx/DoubleRounding/Div.lean` |

`_expBot` takes no minimum quantum, `_expFinite` a finite one; see each
docstring for the exponent conditions.

### §6.1 — Format inference

In `Mpfx/Format/Inference.lean`. The inferred format contains every result of
the unrounded operation:

| Paper | Lean |
| --- | --- |
| `⊗`-containment (`A ⊗ B ⊆ 𝒜(p₁+p₂, …)`) | `Format.mul_subset` |
| `⊕`-containment (`A ⊕ B ⊆ 𝒜(…)`) | `Format.add_subset` |
| `-A ⊆ A`, `\|A\| ⊆ A` | `Format.neg_subset`, `Format.abs_subset` |

## Verifying

Requires the toolchain pinned in `lean-toolchain`.

```sh
lake exe cache get   # prebuilt Mathlib oleans
lake build           # checks the whole development; exit 0 = all proofs check
lake test            # the examples in MpfxTest/
```

`lake build` compiles every file (including the `rnd` function layer).
To confirm a result rests on no unexpected axioms, e.g.:

```lean
import Mpfx
#print axioms Mpfx.rndRTO_RN
-- 'Mpfx.rndRTO_RN' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every theorem listed above depends on exactly these three standard axioms.

## Layout

| File | Contents |
| --- | --- |
| `Mpfx/Utils.lean` | Project-agnostic `ℝ`/integer helpers. |
| `Mpfx/Dyadic.lean` | `Dyadic` (subring of `ℚ`), `precisionAtMost`/`quantumAtLeast` (and quantum alignment under `±`, `×`), `IsRepresentableAtP`. |
| `Mpfx/Format/Defs.lean` | `Format`/`FiniteFormat`, membership, `canonicalExp`, `numDigits`; `Special`, `WithSpecial`, `Format.values`. |
| `Mpfx/Format/Parity.lean` | `ParityFormat`, `IsOdd`/`IsEven`, transport across formats. |
| `Mpfx/Format/Parity/Alternate.lean` | Parity alternation between adjacent canonical values. |
| `Mpfx/Format/Containment.lean` | §5.1 containment and completeness; `extend`, `numDigits_extend`. |
| `Mpfx/Format/Next.lean` | `withBound`, `next`, `boundAfterNext`; containment with a relaxed bound. |
| `Mpfx/Format/Digits.lean` | Digit-count lemma; RTO-padding lemma (`IsOdd.transfer_of_subset`). |
| `Mpfx/Format/Discrete.lean` | Canonical representation, F-adjacency, midpoint membership. |
| `Mpfx/Format/CanonicalExp.lean` | Closed forms of the canonical exponent. |
| `Mpfx/Format/Inference.lean` | §6.1 inference. |
| `Mpfx/Rounding/Defs.lean` | Rounding modes, `SpecialMap`/`OverflowMap`, the `Rounds`/`RoundsFinite` spec, `Overflows`, `IsFaithfulRound`. |
| `Mpfx/Rounding/Basic.lean` | Consequences of the spec: sign symmetry, uniqueness, faithfulness, monotonicity. |
| `Mpfx/Rounding/Restrict.lean` | Restrict/lift between bounded and unbounded rounding. |
| `Mpfx/Rounding/Parity.lean` | Adjacent grid points alternate in parity. |
| `Mpfx/Rounding/Op.lean`, `Op/` | The rounding function `rnd` and the bridge `rnd_iff_rounds`. |
| `Mpfx/Rounding/Special.lean` | `maxFinite` and the standard tables: `SpecialMap.exact`/`saturate`/`toNaN`, `OverflowMap.ieee`/`saturate`/`toNaN`. |
| `Mpfx/Rounding/Ulp.lean` | `ulp`, `rndDown`/`rndUp`/`midp`, `succ`/`pred`. |
| `Mpfx/DoubleRounding/Basic.lean` | §5.2 positive rules (finite form), except RTO→RN; `rndExact`. |
| `Mpfx/DoubleRounding/Nearest.lean` | `roundsRTO_RN_finite`. |
| `Mpfx/DoubleRounding/Propagation.lean` | Per-rule overflow propagation between direct, `F₂` and chained rounding. |
| `Mpfx/DoubleRounding/Total.lean` | §5.2 positive rules (total form); agreement in bound under plain containment. |
| `Mpfx/DoubleRounding/Special.lean` | §5.2 rules with tables; `Composes`, `OverflowAgrees`, standard tables. |
| `Mpfx/DoubleRounding/Counterexample.lean`, `Counterexample/` | §5.2 counterexamples. |
| `Mpfx/DoubleRounding/NearestMidpoint.lean` | Nearest double rounding below the midpoint (Roux Lemma 16). |
| `Mpfx/DoubleRounding/{Mul,Add,Sqrt,Div}.lean` | Roux: `×`, `+`/`−`, `√`, `/`. |
| `MpfxTest/` | `lake test` examples: the tables against IEEE 754 §7.4, IEEE double rounding. |

Formalization design notes are in [`docs/DESIGN.md`](docs/DESIGN.md); status and
remaining work in [`docs/agents/TODO.md`](docs/agents/TODO.md).
