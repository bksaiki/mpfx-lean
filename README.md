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

A second library, `Fpy`, built on `Mpfx`, mechanizes the FPy compiler paper
(draft): the language's semantics, format inference, the digit-bound analysis,
and the compiler's rewrites ([FPy](#fpy)).

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
| Lemma 5.3 (RTO padding preserves representability) | `IsOdd.transfer_of_subset` | `Mpfx/Format/Parity.lean` |

### §5.2 — Correct double rounding (Fig. 9)

All positive rules, in `Mpfx/DoubleRounding/`, at three levels:

- **Finite form**: given `RoundsFinite F₂ rm₂ x z` and `RoundsFinite F₁ rm₁ z w`
  (with the stated containment of `F₁` in `F₂`), then `RoundsFinite F₁ rm₁ x w`.
  RTO → RTN/RTP/RTZ/RAZ/RN also have a `…_finite_of_extend` form taking the plain
  containment `F₁.extend k ⊆ F₂` and `2 ≤ F₂.p`.
- **Total form**, with bounds: either rounding `x` directly in `F₁` overflows
  (`Overflows`), or rounding `x` into `F₂` and the result into `F₁` stays in
  bound and agrees with it (`RoundsInBound`).
- **With maps**, on `rnd` over every input (real, `±Inf`, NaN):
  `rnd₁ (rnd₂ v) = rnd₁ v`. See below.

| Paper | Finite form | Total form | With maps |
| --- | --- | --- | --- |
| `rnd-RTZ-RTZ` | `roundsRTZ_RTZ_finite` | `roundsRTZ_RTZ_inBound` | `rndRTZ_RTZ` |
| `rnd-RAZ-RAZ` | `roundsRAZ_RAZ_finite` | `roundsRAZ_RAZ_inBound` | `rndRAZ_RAZ` |
| `rnd-RTO-RTO` | `roundsRTO_RTO_finite` | `roundsRTO_RTO_inBound` | `rndRTO_RTO` |
| `rnd-RTO-RTZ` | `roundsRTO_RTZ_finite` | `roundsRTO_RTZ_inBound` | `rndRTO_RTZ` |
| `rnd-RTO-RAZ` | `roundsRTO_RAZ_finite` | `roundsRTO_RAZ_inBound` | `rndRTO_RAZ` |
| `rnd-RTO-RNE` / `rnd-RTO-RNA` | `roundsRTO_RN_finite` (both tie-breaks) | `roundsRTO_RN_inBound` | `rndRTO_RN` |
| RTP→RTP, RTN→RTN (IEEE directed) | `roundsRTP_RTP_finite`, `roundsRTN_RTN_finite` | — | — |
| RTO→RTP, RTO→RTN | `roundsRTO_RTP_finite`, `roundsRTO_RTN_finite` | — | — |

### Double rounding with special values

`rnd F S O rm : WithSpecial ℝ → RoundResult` rounds with two maps of `F`:
`S : SpecialMap` says where `±Inf` and NaN inputs go, `O : OverflowMap` where
overflow goes, by sign. The map-level rules (`rndRTZ_RTZ`, …, in
`Mpfx/DoubleRounding/Special.lean`) take the plain containment and three map
conditions:

| Condition | Meaning |
| --- | --- |
| `SpecialMap.Composes`, `OverflowMap.Composes` | `F₁` rounds each `F₂` map entry to the matching `F₁` entry |
| `OverflowAgrees` | where exactly one side overflows, the overflow maps give the other side's in-bound value |

`OverflowAgrees` holds for any maps under the paper's relaxed containment
(`OverflowAgrees.of_bound`; the rules in that form are `rndRTZ_RTZ_of_bound`,
…), and for saturating maps on both sides under the plain one
(`OverflowAgrees.of_saturate`). Standard maps that compose:
`SpecialMap.exact_composes`, `OverflowMap.composes_of_inf` (`±Inf`),
`OverflowMap.saturate_composes`. The IEEE 754 maps
(`OverflowMap.ieee`) compose for every rule but RTO → RTZ, where RTO
overflows to `±Inf` and RTZ saturates. `MpfxTest/DoubleRounding.lean` shows
that failure, and full IEEE instances of RTO → RN and RTZ → RTZ.

### §5.2 — Counterexamples for the invalid pairings

The ten mode pairings that are *not* correct double rounding, in
`namespace Mpfx.Cex` (`Mpfx/DoubleRounding/Counterexample.lean`). For every
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
the unrounded operation, with special values propagated by IEEE 754 (NaN
propagates, `∞ × 0` and `∞ − ∞` are NaN, infinities take the product's XOR
sign or keep their own in a sum). The inferred specials are exactly those the
operation produces (`special_mem_opMul_iff`, `special_mem_opAdd_iff`,
`special_mem_opAbs_iff`).

| Paper | Over values (with specials) | Finite form |
| --- | --- | --- |
| `⊗`-containment (`A ⊗ B ⊆ 𝒜(p₁+p₂, …)`) | `Format.mul_subset` | `Format.mul_subset_finite` |
| `⊕`-containment (`A ⊕ B ⊆ 𝒜(…)`) | `Format.add_subset` | `Format.add_subset_finite` |
| `-A ⊆ A` | `Format.neg_subset` (into `opNeg A`; `= A` for negation-closed specials, `opNeg_of_negClosed`) | `Format.neg_subset_finite` |
| `\|A\| ⊆ A` | `Format.abs_subset` (into `opAbs A`) | `Format.abs_subset_finite` |

## FPy

The FPy compiler paper (PLDI draft) compiles hardware specifications with
explicit rounding into fast software models. `Fpy` mechanizes its semantics
(§3), format inference with Theorem 4.1 (§4.2), the digit-bound analysis with
Theorem 4.2 (§4.3), and each rewrite of §5. Names are relative to `namespace
Fpy`, e.g. `#check @Fpy.run_iff_of_rw`. Section, figure and table numbers follow
the draft. The theorems cover non-recursive programs: a recursive call has no
finite derivation.

The operators are abstract (a `Signature`) through the semantics, format
inference and the rewrite framework; `fpy decode` is FPy's own signature, with
contexts that round through `Mpfx.rnd` and any record layout `decode`.

### §3 — Syntax and semantics (Fig. 2, 3, 10)

| Paper | Lean | File |
| --- | --- | --- |
| Values, numbers `ℝ ∪ {±∞, NaN}` | `Val`, `Num` | `Fpy/Value.lean` |
| Syntax (Fig. 2) | `Expr`, `Stmt`, `Program` | `Fpy/Syntax.lean` |
| Big-step semantics (Fig. 3, 10) | `Eval`, `Exec`, `Run` | `Fpy/Semantics.lean` |
| Determinism (beyond the paper) | `Eval.det`, `Exec.det` | `Fpy/Semantics.lean` |
| FPy's operators and contexts | `fpy`, `ArithOp`, `ExactOp`, `RoundCtx` | `Fpy/Ops.lean` |

### §4.2 — Format inference (Fig. 4, 5, 11; Table 1)

| Paper | Lean | File |
| --- | --- | --- |
| Inference rules (Fig. 5, 11) | `AEval`, `AExec` | `Fpy/FormatInference/Defs.lean` |
| Soundness side conditions | `Analysis.Sound` | `Fpy/FormatInference/Defs.lean` |
| Theorem 4.1, any format domain | `eval_sound`, `exec_sound`, `run_sound` | `Fpy/FormatInference/Sound.lean` |
| Format domain (Fig. 4) | `Fmt`, `Fmt.domain` | `Fpy/FormatInference/Domain.lean` |
| Table 1 | `ArithOp.fmt`, `ArithOp.fmt_sound`, `ExactOp.aval_sound` | `Fpy/FormatInference/Ops.lean` |
| Condition refinement | `refine`, `refine_sound` | `Fpy/FormatInference/Refine.lean` |
| Theorem 4.1 for FPy | `fpy_run_sound` | `Fpy/FormatInference/Analysis.lean` |

### §4.3 — Digit-bound analysis (Fig. 7, 8, 12; Table 2)

Names are in `namespace Fpy.DigitBound`.

| Paper | Lean | File |
| --- | --- | --- |
| Rules (Fig. 8, 12) | `DEval`, `DExec` | `Fpy/DigitBound/Defs.lean` |
| D-Int; constraints from inferred formats | `DEval.int`, `DEval.fmt` | `Fpy/DigitBound/Defs.lean` |
| Theorem 4.2 | `eval_sound`, `exec_sound`, `run_sound` | `Fpy/DigitBound/Sound.lean` |
| Table 2, operators | `opOK_add`, `opOK_mul`, `opOK_exact`, `opOK_ext`, `opOK_exp2`, `opOK_logb`, `opOK_any` | `Fpy/DigitBound/Table.lean` |
| Table 2, rounding | `rndOK_real`, `rndOK_fixedRTZ`, `rndOK_fixed`, `rndOK_precRTZ`, `rndOK_prec`, `rndOK_any` | `Fpy/DigitBound/Table.lean` |
| D-Arith from Table 2 | `ArithOK.comp` | `Fpy/DigitBound/Table.lean` |

### §5 — Rewrites

Each rewrite is an `Equiv`, and its output is well formed (`wf_*`). A rewrite's
fresh variables are kept apart from the rest of the program by `Rw`, not by the
`equiv_*` statements.

| Paper | Lean | File |
| --- | --- | --- |
| Rewrite correctness | `Equiv` | `Fpy/Rewrite.lean` |
| Rewriting preserves `Run` | `Rw.sim`, `run_iff_of_rw` | `Fpy/Rewrite.lean` |
| Elim | `equiv_elim` | `Fpy/Rewrite/Separate.lean` |
| Insert | `equiv_insert` | `Fpy/Rewrite/Separate.lean` |
| Split | `equiv_split`; condition from any total Mpfx rule via `RoundCtx.round_round` | `Fpy/Rewrite/Separate.lean` |
| SplitOp | `equiv_splitOp`; conditions from Roux via `splitOp_add`, `splitOp_mul`, `splitOp_div`, `splitOp_sqrt` | `Fpy/Rewrite/Separate.lean` |
| Special | `equiv_special` | `Fpy/Rewrite/Lower.lean` |
| Overflow | `equiv_overflow`; threshold form `equiv_overflow_threshold`, with `overflows_iff_of_threshold` | `Fpy/Rewrite/Lower.lean` |
| Overflow threshold for MX E4M3 (`464`) | `FpyTest.e4m3_overflows_iff` | `FpyTest/Rewrite/Lower.lean` |
| FloatToFixed | `equiv_floatToFixed`, from `rndUnbounded_eq_fixed` | `Fpy/Rewrite/Lower.lean` |
| Rescale | `equiv_rescale`, from `rndUnbounded_scale` | `Fpy/Rewrite/Lower.lean` |

### Differences from the draft

Where a rule of the draft is unsound or underspecified, the Lean states a fixed
rule; the list is in [`docs/agents/FPY_PLAN.md`](docs/agents/FPY_PLAN.md).

Not mechanized: the composition of rewrites (e.g. Fig. 9), and the
implementation's fixpoint algorithm, which only constructs derivations of the
rules.

## Verifying

Requires the toolchain pinned in `lean-toolchain`.

```sh
lake exe cache get   # prebuilt Mathlib oleans
lake build           # checks the whole development; exit 0 = all proofs check
lake test            # the examples in MpfxTest/
lake build FpyTest   # the examples in FpyTest/
```

`lake build` compiles every file (including the `rnd` function layer).
To confirm a result rests on no unexpected axioms, e.g.:

```lean
import Mpfx
#print axioms Mpfx.rndRTO_RN
-- 'Mpfx.rndRTO_RN' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every theorem listed above, in `Mpfx` and `Fpy`, depends on exactly these three
standard axioms.

## Layout

| File | Contents |
| --- | --- |
| `Mpfx/Utils.lean` | Project-agnostic `ℝ`/integer helpers. |
| `Mpfx/Dyadic.lean` | `Dyadic` (subring of `ℚ`), `precisionAtMost`/`quantumAtLeast` (and quantum alignment under `±`, `×`), `IsRepresentableAtP`. |
| `Mpfx/Format/Defs.lean` | `Format`/`FiniteFormat`, membership, `canonicalExp`, `numDigits`; `Special`, `WithSpecial`, `Format.values`. |
| `Mpfx/Format/Parity.lean` | `ParityFormat`, `IsOdd`/`IsEven`; even values as the shrink `𝒜(p − 1, exp + 1)`, alternation at the canonical step, RTO-padding lemma (`IsOdd.transfer_of_subset`). |
| `Mpfx/Format/Containment.lean` | §5.1 containment and completeness; `extend`, `numDigits_extend`, `shrink`. |
| `Mpfx/Format/Next.lean` | `withBound`, `next`, `boundAfterNext`; containment with a relaxed bound. |
| `Mpfx/Format/Discrete.lean` | Canonical representation, midpoint of adjacent values in `F.extend 1`. |
| `Mpfx/Format/CanonicalExp.lean` | Floor and ceiling at the canonical exponent: `floor_minimality`, `ofIntZpow_mem_unbounded`, `floor_mantissa_lt`. |
| `Mpfx/Format/Inference.lean` | §6.1 inference. |
| `Mpfx/Rounding/Defs.lean` | Rounding modes, `SpecialMap`/`OverflowMap`, the `Rounds`/`RoundsFinite` spec, `Overflows`, `IsFaithfulRound`. |
| `Mpfx/Rounding/Basic.lean` | Consequences of the spec: sign symmetry, uniqueness, faithfulness. |
| `Mpfx/Rounding/Restrict.lean` | Restrict/lift between bounded and unbounded rounding. |
| `Mpfx/Rounding/Parity.lean` | Adjacent values alternate in parity; for `p ≠ 1`, a neighbour's parity is its significand's. |
| `Mpfx/Rounding/Monotone.lean` | Rounding is monotone in every mode (`RoundsFinite.mono`). |
| `Mpfx/Rounding/Op.lean`, `Op/` | The rounding function `rnd` and the bridge `rnd_iff_rounds`. |
| `Mpfx/Rounding/Special.lean` | `maxFinite` and the standard maps: `SpecialMap.exact`/`saturate`/`toNaN`, `OverflowMap.ieee`/`saturate`/`toNaN`. |
| `Mpfx/Rounding/Ulp.lean` | `ulp`, `rndDown`/`rndUp`/`midp`, nearest rounding around the midpoint. |
| `Mpfx/DoubleRounding/Basic.lean` | §5.2 positive rules (finite form), except RTO→RN; `rndExact`. |
| `Mpfx/DoubleRounding/Nearest.lean` | `roundsRTO_RN_finite`. |
| `Mpfx/DoubleRounding/Total.lean` | §5.2 positive rules (total form) from one locality theorem, `LocalDoubleRounding`; agreement in bound under plain containment. |
| `Mpfx/DoubleRounding/Special.lean` | §5.2 rules with maps; `Composes`, `OverflowAgrees`, standard maps. |
| `Mpfx/DoubleRounding/Counterexample.lean`, `Counterexample/` | §5.2 counterexamples. |
| `Mpfx/DoubleRounding/NearestMidpoint.lean` | Nearest double rounding below the midpoint (Roux Lemma 16). |
| `Mpfx/DoubleRounding/{Mul,Add,Sqrt,Div}.lean` | Roux: `×`, `+`/`−`, `√`, `/`. |
| `MpfxTest/` | `lake test` examples: the maps against IEEE 754 §7.4, IEEE double rounding. |
| `Fpy/Value.lean`, `Syntax.lean`, `Semantics.lean` | FPy values, syntax, semantics, determinism. |
| `Fpy/Ops.lean` | FPy's operators on `Num`, `RoundCtx`, the signature `fpy`. |
| `Fpy/FormatInference/Defs.lean`, `Sound.lean` | Format inference over any domain; Theorem 4.1. |
| `Fpy/FormatInference/Domain.lean`, `Ops.lean`, `Refine.lean`, `Analysis.lean` | The Fig. 4 domain, Table 1, condition refinement; Theorem 4.1 for FPy. |
| `Fpy/DigitBound/Defs.lean`, `Basic.lean`, `Digits.lean`, `Sound.lean`, `Table.lean` | §4.3 rules, their lemmas, digit positions of each operator, Theorem 4.2, Table 2. |
| `Fpy/Rewrite.lean` | `Equiv`, `Rw`, congruence, the whole-program theorem. |
| `Fpy/Rewrite/Separate.lean` | §5.1 rewrites and their FPy instances. |
| `Fpy/Rewrite/Lower.lean` | §5.2 rewrites and their rounding identities. |
| `FpyTest/` | `lake build FpyTest` examples: a toy signature, Table 1 checks, Split/SplitOp instances, the E4M3 threshold, Table 2 checks. |

Formalization design notes are in [`docs/DESIGN.md`](docs/DESIGN.md); status and
remaining work in [`docs/agents/TODO.md`](docs/agents/TODO.md) (Mpfx) and
[`docs/agents/FPY_PLAN.md`](docs/agents/FPY_PLAN.md) (FPy).
