# mpfx-lean

A Lean 4 / Mathlib formalization of the abstract floating-point results in
*When Double Rounding is Correct* (Saiki, Zorn, Richey, Tatlock).

The paper studies the abstract number format `𝒜(p, exp, b)` — `p` binary
digits of precision, minimum quantum `2^exp`, magnitude bound `b` — and asks
when rounding a real into a wide format and then into a narrow one agrees with
rounding directly into the narrow format. This development mechanizes the
appendix: format containment, the supporting digit/parity lemmas, every
double-rounding rule of Fig. 9 (with counterexamples for the invalid mode
pairings), and the format-inference operators.

## What is formalized

- **§5.1 Format containment** (`Containment.lean`): `containsPrec`
  (`𝒜-Contains-Prec`) and `containsSub` (`𝒜-Contains-Sub`).
- **Lemmas 5.1–5.3** (`Format.lean`, `Containment.lean`, `Digits.lean`):
  `numDigits` (digit position as a function of `(p, exp, x)`),
  `numDigits_extend` (Lemma 5.2), and `IsOdd.transfer_of_subset` (Lemma 5.3,
  round-to-odd digit-padding preserves representability).
- **§5.2 Correct double rounding** (`DoubleRounding.lean`): all six positive
  rules of Fig. 9 — `rndRTZ_RTZ`, `rndRAZ_RAZ`, `rndRTO_RTO`, `rndRTO_RTZ`,
  `rndRTO_RAZ`, and `rndRTO_RN` (covering both tie-breaks) — plus the
  directed-mode chains `rndRTP_RTP` / `rndRTN_RTN`.
- **§5.2 Counterexamples** (`DoubleRoundingCex.lean`): the ten incorrectly
  double-rounding mode pairings, each refuted by an explicit witness format and
  real input where the chained rounding disagrees with the direct one.
- **§6.1 Format inference** (`FormatInference.lean`): the `⊗` (multiply) and
  `⊕` (add) operators with `mul_subset` / `add_subset` — every product / sum
  of representables lies in the inferred format — plus `neg`/`abs`.

The entire development is `sorry`-free.

## Design

- **Layered format subtypes.** `Format` carries only the natural type-level
  constraints (`p ≥ 1` via `WithTop ℕ+`, `b ≥ 0` via `WithTop NonNegDyadic`).
  `FiniteFormat extends Format` rules out the doubly-unbounded `(p = ⊤,
  exp = ⊥)` case; `ParityFormat extends FiniteFormat` additionally rules out
  `(p = 1, exp = ⊥)`, anchoring `IsOdd` / `IsEven`.
- **`ℚ` substrate.** `Dyadic` is a subring of `ℚ` (not `ℝ`), giving decidable
  equality and order for free. `ℝ` is confined to where it is intrinsic — the
  real input `x` and the `Int.log` / `Int.floor` rounding machinery — with the
  `Dyadic → ℚ → ℝ` boundary localized to named bridge lemmas.
- **Constructive rounding.** Alongside the specification relation `Rounds`,
  the function `rnd` (`RoundOp.lean`) computes the rounded result via
  `Int.log` + `Int.floor`/`Int.ceil`, bridged to the relation by
  `rnd_iff_rounds`. The constructive/classical split is at the file level:
  `Rounding.lean` is constructive, `RoundOp.lean` is classical.

## File map

| File | Contents |
| --- | --- |
| `Mpfx/Utils.lean` | Project-agnostic `ℝ`/integer arithmetic helpers. |
| `Mpfx/Dyadic.lean` | `Dyadic` (subring of `ℚ`), `precisionAtMost`/`quantumAtLeast`, `IsRepresentableAtP`. |
| `Mpfx/Format.lean` | `Format`/`FiniteFormat`/`ParityFormat`, membership, `numDigits` (Lemma 5.1), `IsOdd`/`IsEven`. |
| `Mpfx/Rounding.lean` | Rounding modes, `RoundResult`, the `Rounds`/`RoundsFinite` spec, `IsFaithfulRound`, sign-symmetry. |
| `Mpfx/RoundOp.lean` | The constructive function `rnd` and the bridge `rnd_iff_rounds`. |
| `Mpfx/Containment.lean` | §5.1 containment; `extend`/`withBound`/`next`/`boundAfterNext`. |
| `Mpfx/Grid.lean` | F-grid representation, F-adjacency, midpoint membership (prerequisite for `rndRTO_RN`). |
| `Mpfx/Digits.lean` | Lemmas 5.2 and 5.3. |
| `Mpfx/DoubleRounding.lean` | §5.2 positive rules (Fig. 9). |
| `Mpfx/DoubleRoundingCex.lean` | §5.2 counterexamples. |
| `Mpfx/FormatInference.lean` | §6.1 `⊗`/`⊕` inference. |

`docs/agents/TODO.md` tracks status and remaining work.

## Building

Requires the Lean toolchain pinned in `lean-toolchain` (Mathlib `v4.29.0`).

```sh
lake exe cache get   # fetch prebuilt Mathlib oleans
lake build
```
