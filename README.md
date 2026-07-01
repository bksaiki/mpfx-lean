# mpfx-lean

A Lean 4 / Mathlib (`v4.29.0`) formalization of the abstract floating-point
results in *When Double Rounding is Correct*.

The paper studies the abstract format `𝒜(p, exp, b)` — `p` binary digits of
precision, minimum quantum `2^exp`, magnitude bound `b` — and characterizes
when rounding a real into a wide format then into a narrow one agrees with
rounding directly into the narrow format. This development mechanizes the
appendix.

## Definitions and Theorems

Each entry gives the paper result, the Lean name (relative to `namespace
Mpfx`), and its file. To inspect a statement, qualify with `Mpfx.`, e.g.
`#check @Mpfx.Format.containsPrec` or `#check @Mpfx.rndRTO_RN`.

### §3 — Number formats and rounding

| Paper | Lean | File |
| --- | --- | --- |
| Dyadic numbers `ℤ[½]` (§3.1) | `Dyadic` | `Mpfx/Dyadic.lean` |
| Representability of `x` in `F` (§3.1) | `Format.Mem` (`x ∈ F`) | `Mpfx/Format.lean` |
| Rounding modes RNE, RNA, RTP, RTN, RTZ, RAZ, RTO (§3.2) | `RoundingMode` | `Mpfx/Rounding.lean` |
| Rounding function `rnd_{F,rm}` (§3.2) | `RoundsFinite` / `Rounds` (spec), `rnd` (constructive) | `Mpfx/Rounding.lean`, `Mpfx/RoundOp.lean` |
| Even/odd classification of representable values (§3.2) | `ParityFormat.IsEven` / `IsOdd` | `Mpfx/Format.lean` |

### §4 — The abstract number format `𝒜(p, exp, b)`

| Paper | Lean | File |
| --- | --- | --- |
| Precision-bound generator (`p < ∞`, §4.1) | `precisionAtMost` | `Mpfx/Dyadic.lean` |
| Quantum-bound generator (`q > 0`, §4.1) | `quantumAtLeast` | `Mpfx/Dyadic.lean` |
| Representable at precision `p` (§4.1) | `IsRepresentableAtP` | `Mpfx/Dyadic.lean` |
| Abstract number format `𝒜(p, exp, b)` (§4.2) | `Format` / `FiniteFormat` | `Mpfx/Format.lean` |
| Maximum representable value / overflow bound `b` (§4.2) | `Format.b`, `Format.boundOK` | `Mpfx/Format.lean` |

### §5.1 — Format containment (Fig. 7)

| Paper | Lean | File |
| --- | --- | --- |
| `𝒜-Contains-Prec` | `Format.containsPrec` | `Mpfx/Containment.lean` |
| `𝒜-Contains-Sub` | `Format.containsSub` | `Mpfx/Containment.lean` |

### Supporting lemmas

| Paper | Lean | File |
| --- | --- | --- |
| Lemma 5.1 (digit position is a function of `(p, exp, x)`) | `FiniteFormat.numDigits` | `Mpfx/Format.lean` |
| Lemma 5.2 (`w₂ = w₁ + k`) | `FiniteFormat.numDigits_extend` | `Mpfx/Containment.lean` |
| Lemma 5.3 (RTO padding preserves representability) | `IsOdd.transfer_of_subset` | `Mpfx/Digits.lean` |

### §5.2 — Correct double rounding (Fig. 8)

All positive rules, in `Mpfx/DoubleRounding.lean`. Each has the form: given
`RoundsFinite F₂ rm₂ x z` and `RoundsFinite F₁ rm₁ z w` (with the stated
containment of `F₁` in `F₂`), then `RoundsFinite F₁ rm₁ x w`.

| Paper | Lean |
| --- | --- |
| `rnd-RTZ-RTZ` | `rndRTZ_RTZ` |
| `rnd-RAZ-RAZ` | `rndRAZ_RAZ` |
| `rnd-RTO-RTO` | `rndRTO_RTO` |
| `rnd-RTO-RTZ` | `rndRTO_RTZ` |
| `rnd-RTO-RAZ` | `rndRTO_RAZ` |
| `rnd-RTO-RNE` / `rnd-RTO-RNA` | `rndRTO_RN` (one theorem, both tie-breaks) |
| RTP→RTP, RTN→RTN (IEEE directed) | `rndRTP_RTP`, `rndRTN_RTN` |

### §5.2 — Counterexamples for the invalid pairings (Table 2)

The ten mode pairings that are *not* correct double rounding, in
`namespace Mpfx.Cex` (`Mpfx/DoubleRoundingCex.lean`). Each exhibits a witness
format `F₁` and a real `x` whose chained rounding disagrees with the direct
rounding (`∃ x z w, RoundsFinite F₂ rm₂ x z ∧ RoundsFinite F₁ rm₁ z w ∧
¬ RoundsFinite F₁ rm₁ x w`):

`no_rndRNE_RNE`, `no_rndRNE_RAZ`, `no_rndRNE_RTZ`, `no_rndRNE_RTO`,
`no_rndRTZ_RNE`, `no_rndRTZ_RAZ`, `no_rndRTZ_RTO`,
`no_rndRAZ_RNE`, `no_rndRAZ_RTZ`, `no_rndRAZ_RTO`.

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
```

## Layout

| File | Contents |
| --- | --- |
| `Mpfx/Utils.lean` | Project-agnostic `ℝ`/integer helpers. |
| `Mpfx/Dyadic.lean` | `Dyadic` (subring of `ℚ`), `precisionAtMost`/`quantumAtLeast`, `IsRepresentableAtP`. |
| `Mpfx/Format.lean` | `Format`/`FiniteFormat`/`ParityFormat`, membership, `numDigits`, `IsOdd`/`IsEven`. |
| `Mpfx/Rounding.lean` | Rounding modes, the `Rounds`/`RoundsFinite` spec, `IsFaithfulRound`. |
| `Mpfx/RoundOp.lean` | The constructive `rnd` and the bridge `rnd_iff_rounds`. |
| `Mpfx/Containment.lean` | §5.1 containment; `extend`/`withBound`/`next`. |
| `Mpfx/Grid.lean` | F-grid representation, F-adjacency, midpoint membership. |
| `Mpfx/Digits.lean` | Lemmas 5.2 and 5.3. |
| `Mpfx/DoubleRounding.lean` | §5.2 positive rules. |
| `Mpfx/DoubleRoundingCex.lean` | §5.2 counterexamples. |
| `Mpfx/FormatInference.lean` | §6.1 inference. |

Formalization design notes are in [`docs/DESIGN.md`](docs/DESIGN.md); status and
remaining work in [`docs/agents/TODO.md`](docs/agents/TODO.md).
