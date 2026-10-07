# mpfx-lean

A Lean 4 / Mathlib (`v4.29.0`) formalization of the abstract floating-point
results in *When Double Rounding is Correct* (Saiki, Zorn, Richey, Tatlock).

The paper studies the abstract format `𝒜(p, exp, b)` — `p` binary digits of
precision, minimum quantum `2^exp`, magnitude bound `b` — and characterizes
when rounding a real into a wide format then into a narrow one agrees with
rounding directly into the narrow format. This development mechanizes the
appendix.

## Theorems

Each entry gives the paper result, the Lean name (relative to `namespace
Mpfx`), and its file. To inspect a statement, qualify with `Mpfx.`, e.g.
`#check @Mpfx.Format.containsPrec` or `#check @Mpfx.rndRTO_RN`.

### §5.1 — Format containment (Fig. 8)

| Paper | Lean | File |
| --- | --- | --- |
| `𝒜-Contains-Prec` | `Format.containsPrec` | `Mpfx/Containment.lean` |
| `𝒜-Contains-Sub` | `Format.containsSub` | `Mpfx/Containment.lean` |
| Completeness (`F₁ ⊆ F₂` iff a rule fires) | `Format.subset_iff_contains` | `Mpfx/Containment.lean` |

### Supporting lemmas

| Paper | Lean | File |
| --- | --- | --- |
| Lemma 5.1 (digit position is a function of `(p, exp, x)`) | `FiniteFormat.numDigits` | `Mpfx/Format.lean` |
| Lemma 5.2 (`w₂ = w₁ + k`) | `FiniteFormat.numDigits_extend` | `Mpfx/Containment.lean` |
| Lemma 5.3 (RTO padding preserves representability) | `IsOdd.transfer_of_subset` | `Mpfx/Digits.lean` |

### §5.2 — Correct double rounding (Fig. 9)

All positive rules, in `Mpfx/DoubleRounding.lean`. The finite form: given
`RoundsFinite F₂ rm₂ x z` and `RoundsFinite F₁ rm₁ z w` (with the stated
containment of `F₁` in `F₂`), then `RoundsFinite F₁ rm₁ x w`. The total form,
over `Rounds` with overflow: either rounding `x` directly in `F₁` overflows, or
the chained rounding is finite and agrees with it.

| Paper | Finite form | Total form |
| --- | --- | --- |
| `rnd-RTZ-RTZ` | `rndRTZ_RTZ` | `roundsRTZ_RTZ` |
| `rnd-RAZ-RAZ` | `rndRAZ_RAZ` | `roundsRAZ_RAZ` |
| `rnd-RTO-RTO` | `rndRTO_RTO` | `roundsRTO_RTO` |
| `rnd-RTO-RTZ` | `rndRTO_RTZ` | `roundsRTO_RTZ` |
| `rnd-RTO-RAZ` | `rndRTO_RAZ` | `roundsRTO_RAZ` |
| `rnd-RTO-RNE` / `rnd-RTO-RNA` | `rndRTO_RN` (both tie-breaks) | `roundsRTO_RN` |
| RTP→RTP, RTN→RTN (IEEE directed) | `rndRTP_RTP`, `rndRTN_RTN` | — |

### §5.2 — Counterexamples for the invalid pairings

The ten mode pairings that are *not* correct double rounding, in
`namespace Mpfx.Cex` (`Mpfx/DoubleRoundingCex.lean`). Each exhibits a witness
format `F₁` and a real `x` whose chained rounding disagrees with the direct
rounding (`∃ x z w, RoundsFinite F₂ rm₂ x z ∧ RoundsFinite F₁ rm₁ z w ∧
¬ RoundsFinite F₁ rm₁ x w`):

`no_rndRNE_RNE`, `no_rndRNE_RAZ`, `no_rndRNE_RTZ`, `no_rndRNE_RTO`,
`no_rndRTZ_RNE`, `no_rndRTZ_RAZ`, `no_rndRTZ_RTO`,
`no_rndRAZ_RNE`, `no_rndRAZ_RTZ`, `no_rndRAZ_RTO`.

### Operation-specific double rounding (Roux 2014)

Beyond the paper: Pierre Roux, *Innocuous Double Rounding of Basic Arithmetic
Operations* (JFR 7(1), 2014), radix 2. Double rounding of an operation on
`F₁`-values is correct under a precision margin weaker than the generic rules
need. Finite form, over `F₁.unbounded` and `F₂.unbounded`.

| Operation | Condition | Lean | File |
| --- | --- | --- | --- |
| `x × y`, any modes | `p₂ ≥ 2p₁` | `rndMul_expBot`, `rndMul_expFinite` | `Mpfx/DoubleRoundingMul.lean` |
| `x + y`, nearest | `p₂ ≥ 2p₁ + 1` | `rndAdd` | `Mpfx/DoubleRoundingAdd.lean` |
| `√x`, nearest | `p₂ ≥ 2p₁ + 2` | `rndSqrt_expBot`, `rndSqrt_expFinite` | `Mpfx/DoubleRoundingSqrt.lean` |
| `x / y`, nearest | `p₂ ≥ 2p₁` | `rndDiv_expBot`, `rndDiv_expFinite` | `Mpfx/DoubleRoundingDiv.lean` |

`_expBot` takes no minimum quantum, `_expFinite` a finite one; see each
docstring for the exponent conditions.

### §6.1 — Format inference

In `Mpfx/FormatInference.lean`. The inferred format contains every result of
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
```

`lake build` compiles every file (including the constructive `rnd` layer).
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
| `Mpfx/Dyadic.lean` | `Dyadic` (subring of `ℚ`), `precisionAtMost`/`quantumAtLeast`, `IsRepresentableAtP`. |
| `Mpfx/Format.lean` | `Format`/`FiniteFormat`/`ParityFormat`, membership, `numDigits`, `IsOdd`/`IsEven`. |
| `Mpfx/Rounding.lean` | Rounding modes, the `Rounds`/`RoundsFinite` spec, `IsFaithfulRound`. |
| `Mpfx/RoundPred.lean` | Consequences of the spec: uniqueness, faithfulness, monotonicity. |
| `Mpfx/Parity.lean` | Adjacent grid points alternate in parity. |
| `Mpfx/RoundOp.lean` | The constructive `rnd` and the bridge `rnd_iff_rounds`. |
| `Mpfx/Containment.lean` | §5.1 containment; `extend`/`withBound`/`next`. |
| `Mpfx/Ulp.lean` | `ulp`, `rndDown`/`rndUp`/`midp`, `succ`/`pred`. |
| `Mpfx/CanonicalExp.lean` | Closed forms of the canonical exponent; quantum alignment under `±`, `×`. |
| `Mpfx/NearestMidpoint.lean` | Nearest double rounding below the midpoint (Roux Lemma 16). |
| `Mpfx/Discrete.lean` | Canonical representation, F-adjacency, midpoint membership. |
| `Mpfx/Digits.lean` | Lemmas 5.2 and 5.3. |
| `Mpfx/DoubleRounding.lean` | §5.2 positive rules. |
| `Mpfx/DoubleRoundingCex.lean` | §5.2 counterexamples. |
| `Mpfx/DoubleRoundingMul.lean` | Roux: `×` and the exact-intermediate combinator `rndExact`. |
| `Mpfx/DoubleRoundingAdd.lean` | Roux: `+` / `−`. |
| `Mpfx/DoubleRoundingSqrt.lean` | Roux: `√`. |
| `Mpfx/DoubleRoundingDiv.lean` | Roux: `/`. |
| `Mpfx/FormatInference.lean` | §6.1 inference. |

Formalization design notes are in [`docs/DESIGN.md`](docs/DESIGN.md); status and
remaining work in [`docs/agents/TODO.md`](docs/agents/TODO.md).
