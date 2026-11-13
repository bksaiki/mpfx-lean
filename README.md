# myna-lean

A Lean 4 / Mathlib (`v4.29.0`) formalization of correct double rounding over
the abstract format `𝒜(p, exp, b)` — `p` binary digits of
precision, minimum quantum `2^exp`, magnitude bound `b`. It characterizes when
rounding a real into a wide format then into a narrow one agrees with rounding
directly into the narrow format. Formats also state which of `±Inf` and NaN
they contain, and rounding is total over reals, infinities and NaN, with
overflow sent to a format-chosen value.

## Theorems

Each entry gives the result, the Lean name (relative to `namespace
Myna`), and its file. To inspect a statement, qualify with `Myna.`, e.g.
`#check @Myna.Format.containsPrec` or `#check @Myna.roundsRTO_RN_finite`.

### Format containment

| Result | Lean | File |
| --- | --- | --- |
| Containment by precision (`p₁ ≤ p₂`, `exp₂ ≤ exp₁`, `b₁ ≤ b₂`) | `Format.containsPrec` | `Myna/Format/Containment.lean` |
| Containment of a small-bound `F₁` | `Format.containsSub` | `Myna/Format/Containment.lean` |
| Completeness (`F₁ ⊆ F₂` iff a rule fires) | `Format.subset_iff_contains` | `Myna/Format/Containment.lean` |

`F₁ ⊆ F₂` also requires `F₁.specials ⊆ F₂.specials`, and both
rules carry that conjunct.

### Supporting lemmas

| Result | Lean | File |
| --- | --- | --- |
| Digit position is a function of `(p, exp, x)` | `FiniteFormat.numDigits` | `Myna/Format/Defs.lean` |
| Extending precision by `k` adds `k` digits (`w₂ = w₁ + k`) | `FiniteFormat.numDigits_extend` | `Myna/Format/Containment.lean` |
| RTO padding preserves representability | `toOdd_notMem_of_extend_subset`, `IsFaithfulRound.iff_of_between` | `Myna/DoubleRounding/Basic.lean`, `Myna/Rounding/Basic.lean` |

### Correct double rounding

All positive rules, in `Myna/DoubleRounding/`, at three levels:

- **Finite form**: given `RoundsFinite F₂ rm₂ x z` and `RoundsFinite F₁ rm₁ z w`
  (with the stated containment of `F₁` in `F₂`), then `RoundsFinite F₁ rm₁ x w`.
  RTO → RTN/RTP/RTZ/RAZ/RN also have a `…_finite_of_extend` form taking the plain
  containment `F₁.extend k ⊆ F₂` and `2 ≤ F₂.p`.
- **Total form**, with bounds: either rounding `x` directly in `F₁` overflows
  (`Overflows`), or rounding `x` into `F₂` and the result into `F₁` stays in
  bound and agrees with it (`RoundsInBound`).
- **With maps**, on `rnd` over every input (real, `±Inf`, NaN):
  `rnd₁ (rnd₂ v) = rnd₁ v`. See below.

| Modes | Finite form | Total form | With maps |
| --- | --- | --- | --- |
| RTZ→RTZ | `roundsRTZ_RTZ_finite` | `roundsRTZ_RTZ_inBound` | `rndRTZ_RTZ` |
| RAZ→RAZ | `roundsRAZ_RAZ_finite` | `roundsRAZ_RAZ_inBound` | `rndRAZ_RAZ` |
| RTO→RTO | `roundsRTO_RTO_finite` | `roundsRTO_RTO_inBound` | `rndRTO_RTO` |
| RTO→RTZ | `roundsRTO_RTZ_finite` | `roundsRTO_RTZ_inBound` | `rndRTO_RTZ` |
| RTO→RAZ | `roundsRTO_RAZ_finite` | `roundsRTO_RAZ_inBound` | `rndRTO_RAZ` |
| RTO→RNE, RTO→RNA | `roundsRTO_RN_finite` (both tie-breaks) | `roundsRTO_RN_inBound` | `rndRTO_RN` |
| RTP→RTP, RTN→RTN (IEEE directed) | `roundsRTP_RTP_finite`, `roundsRTN_RTN_finite` | — | — |
| RTO→RTP, RTO→RTN | `roundsRTO_RTP_finite`, `roundsRTO_RTN_finite` | — | — |

### Double rounding with special values

`rnd F S O rm : WithSpecial ℝ → RoundResult` rounds with two maps of `F`:
`S : SpecialMap` says where `±Inf` and NaN inputs go, `O : OverflowMap` where
overflow goes, by sign. The map-level rules (`rndRTZ_RTZ`, …, in
`Myna/DoubleRounding/Special.lean`) take the plain containment and three map
conditions:

| Condition | Meaning |
| --- | --- |
| `SpecialMap.Composes`, `OverflowMap.Composes` | `F₁` rounds each `F₂` map entry to the matching `F₁` entry |
| `OverflowAgrees` | where exactly one side overflows, the overflow maps give the other side's in-bound value |

`OverflowAgrees` holds for any maps under the relaxed containment
(`OverflowAgrees.of_bound`; the rules in that form are `rndRTZ_RTZ_of_bound`,
…), and for saturating maps on both sides under the plain one
(`OverflowAgrees.of_saturate`). Standard maps that compose:
`SpecialMap.exact_composes`, `OverflowMap.composes_of_inf` (`±Inf`),
`OverflowMap.saturate_composes`. The IEEE 754 maps
(`OverflowMap.ieee`) compose for every rule but RTO → RTZ, where RTO
overflows to `±Inf` and RTZ saturates. `MynaTest/DoubleRounding.lean` shows
that failure, and full IEEE instances of RTO → RN and RTZ → RTZ.

### Counterexamples for the invalid pairings

The ten mode pairings that are *not* correct double rounding, in
`namespace Myna.Cex` (`Myna/DoubleRounding/Counterexample.lean`). For every
format `F₁` (a parity format when the target is RTO or RNE), bounded or not,
and every `F₂` satisfying the containment, each exhibits a real `x` whose
double rounding disagrees with the direct rounding, with no rounding
overflowing (`Disagrees`: `∃ x z w y,
RoundsInBound F₂ rm₂ x z ∧ RoundsInBound F₁ rm₁ z w ∧ RoundsInBound F₁ rm₁ x y ∧
w ≠ y`). `Disagrees.rnd_ne` turns the witness into a failure of
`rnd₁ ∘ rnd₂ = rnd₁` for any `SpecialMap` and `OverflowMap`, at a finite input
with a finite intermediate. The `On rnd` theorems need
`¬ F₂.IsUndefined (.nearest .toEven)` when the intermediate is RNE.

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

Pierre Roux, *Innocuous Double Rounding of Basic Arithmetic
Operations* (JFR 7(1), 2014), radix 2. Double rounding of an operation on
`F₁`-values is correct under a precision margin weaker than the generic rules
need. Finite form, over `F₁.unbounded` and `F₂.unbounded`.

| Operation | Condition | Lean | File |
| --- | --- | --- | --- |
| `x × y`, any modes | `p₂ ≥ 2p₁` | `rndMul_expBot`, `rndMul_expFinite` | `Myna/DoubleRounding/Mul.lean` |
| `x + y`, nearest | `p₂ ≥ 2p₁ + 1` | `rndAdd` | `Myna/DoubleRounding/Add.lean` |
| `√x`, nearest | `p₂ ≥ 2p₁ + 2` | `rndSqrt_expBot`, `rndSqrt_expFinite` | `Myna/DoubleRounding/Sqrt.lean` |
| `x / y`, nearest | `p₂ ≥ 2p₁` | `rndDiv_expBot`, `rndDiv_expFinite` | `Myna/DoubleRounding/Div.lean` |

`_expBot` takes no minimum quantum, `_expFinite` a finite one; see each
docstring for the exponent conditions.

### Format inference

In `Myna/Format/Inference.lean`. The inferred format contains every result of
the unrounded operation, with special values propagated by IEEE 754 (NaN
propagates, `∞ × 0` and `∞ − ∞` are NaN, infinities take the product's XOR
sign or keep their own in a sum). The inferred specials are exactly those the
operation produces (`special_mem_opMul_iff`, `special_mem_opAdd_iff`,
`special_mem_opAbs_iff`).

| Result | Over values (with specials) | Finite form |
| --- | --- | --- |
| `⊗`-containment (`A ⊗ B ⊆ 𝒜(p₁+p₂, …)`) | `Format.mul_subset` | `Format.mul_subset_finite` |
| `⊕`-containment (`A ⊕ B ⊆ 𝒜(…)`) | `Format.add_subset` | `Format.add_subset_finite` |
| `-A ⊆ A` | `Format.neg_subset` (into `opNeg A`; `= A` for negation-closed specials, `opNeg_of_negClosed`) | `Format.neg_subset_finite` |
| `\|A\| ⊆ A` | `Format.abs_subset` (into `opAbs A`) | `Format.abs_subset_finite` |

## Verifying

Requires the toolchain pinned in `lean-toolchain`.

```sh
lake exe cache get   # prebuilt Mathlib oleans
lake build           # checks the whole development; exit 0 = all proofs check
lake test            # the examples in MynaTest/
```

`lake build` compiles every file (including the `rnd` function layer).
To confirm a result rests on no unexpected axioms, e.g.:

```lean
import Myna
#print axioms Myna.rndRTO_RN
-- 'Myna.rndRTO_RN' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every theorem listed above depends on exactly these three
standard axioms.

## Layout

| File | Contents |
| --- | --- |
| `Myna/Utils.lean` | Project-agnostic `ℝ`/integer helpers. |
| `Myna/Dyadic.lean` | `Dyadic` (subring of `ℚ`), `precisionAtMost`/`quantumAtLeast` (and quantum alignment under `±`, `×`), `IsRepresentableAtP`. |
| `Myna/Format/Defs.lean` | `Format`/`FiniteFormat`, membership, `canonicalExp`, `numDigits`; `Special`, `WithSpecial`, `Format.values`. |
| `Myna/Format/Parity.lean` | `ParityFormat`, `IsOdd`/`IsEven`; even values as the shrink `𝒜(p − 1, exp + 1)`, alternation at the canonical step, RTO-padding lemma (`IsOdd.transfer_of_subset`). |
| `Myna/Format/Containment.lean` | Containment and completeness; `extend`, `numDigits_extend`, `shrink`. |
| `Myna/Format/Next.lean` | `withBound`, `next`, `boundAfterNext`; containment with a relaxed bound. |
| `Myna/Format/Discrete.lean` | Canonical representation, midpoint of adjacent values in `F.extend 1`. |
| `Myna/Format/CanonicalExp.lean` | Floor and ceiling at the canonical exponent: `floor_minimality`, `ofIntZpow_mem_unbounded`, `floor_mantissa_lt`. |
| `Myna/Format/Inference.lean` | Format inference for unrounded operations. |
| `Myna/Rounding/Defs.lean` | Rounding modes, `SpecialMap`/`OverflowMap`, the `Rounds`/`RoundsFinite` spec, `Overflows`, `IsFaithfulRound`. |
| `Myna/Rounding/Basic.lean` | Consequences of the spec: sign symmetry, uniqueness, faithfulness. |
| `Myna/Rounding/Restrict.lean` | Restrict/lift between bounded and unbounded rounding. |
| `Myna/Rounding/Parity.lean` | Adjacent values alternate in parity; for `p ≠ 1`, a neighbour's parity is its significand's. |
| `Myna/Rounding/Monotone.lean` | Rounding is monotone in every mode (`RoundsFinite.mono`). |
| `Myna/Rounding/Op.lean`, `Op/` | The rounding function `rnd` and the bridge `rnd_iff_rounds`. |
| `Myna/Rounding/Special.lean` | `maxFinite` and the standard maps: `SpecialMap.exact`/`saturate`/`toNaN`, `OverflowMap.ieee`/`saturate`/`toNaN`. |
| `Myna/Rounding/Ulp.lean` | `ulp`, `rndDown`/`rndUp`/`midp`, nearest rounding around the midpoint. |
| `Myna/DoubleRounding/Basic.lean` | Positive double-rounding rules (finite form), except RTO→RN; `rndExact`. |
| `Myna/DoubleRounding/Nearest.lean` | `roundsRTO_RN_finite`. |
| `Myna/DoubleRounding/Total.lean` | Positive double-rounding rules (total form) from one locality theorem, `LocalDoubleRounding`; agreement in bound under plain containment. |
| `Myna/DoubleRounding/Special.lean` | Double-rounding rules with maps; `Composes`, `OverflowAgrees`, standard maps. |
| `Myna/DoubleRounding/Counterexample.lean`, `Counterexample/` | Counterexamples for the invalid pairings. |
| `Myna/DoubleRounding/NearestMidpoint.lean` | Nearest double rounding below the midpoint (Roux Lemma 16). |
| `Myna/DoubleRounding/{Mul,Add,Sqrt,Div}.lean` | Roux: `×`, `+`/`−`, `√`, `/`. |
| `MynaTest/` | `lake test` examples: the maps against IEEE 754 §7.4, IEEE double rounding. |

Formalization design notes are in [`docs/DESIGN.md`](docs/DESIGN.md).
