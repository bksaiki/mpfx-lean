# Roadmap

Open threads the paper revision needs from this development,
forward-looking only; strike an item when it lands. The
formalization's own backlog stays in `docs/agents/`; this file holds
only what the paper depends on. References are Lean names under
`namespace Mpfx` and files under `Mpfx/`, never line numbers.

## Paper revision

**Double rounding**

- Round-to-odd into RTP and RTN, `rndRTO_RTP` and `rndRTO_RTN`
  (possible extensions in `docs/agents/TODO.md`): corollaries of
  `rndRTO_RTZ` and `rndRTO_RAZ` by the sign reduction `rndRTP_RTP`
  and `rndRTN_RTN` use. The paper's evaluation relies on this step
  for MPFX's RTP and RTN, and it is not mechanized.
- Round-to-even as a target (RTE: an inexact result goes to the
  neighbour whose last digit is even) is not in `RoundingMode`. On
  small formats, an RTO intermediate padded by one digit in both
  precision and minimum exponent serves it (p1 from 2 to 4 and ∞,
  exp1 from −2 to 0 and −∞, and bounded pairs with b1 ≤ 8 where F2
  does not overflow before the direct rounding), while precision or
  exponent alone fails in 9 of 12. p1 = 1 was not swept, and nothing
  is proved. Either add the mode with a `roundsRTO_RTE` theorem or
  the paper states the exclusion; decide with the library, which
  exposes the mode.
- A bounded negative for the nearest intermediate. `no_rndRNE_RNE`
  and the other `Mpfx.Cex` counterexamples assume `F₁.b = ⊤`, so for
  bounded targets the paper's "only in trivial cases" for RNE∘RNE
  rests on a sweep of small pairs. A counterexample theorem with a
  finite bound, in the same style.
- The per-operation double-rounding theorems (`DoubleRoundingAdd`,
  `Mul`, `Div`, `Sqrt`, with `CanonicalExp` and `NearestMidpoint`)
  are in the build but in neither the README nor
  `docs/agents/TODO.md`'s layout, and three of them cite a plan file
  `docs/agents/DOUBLE_ROUNDING_OPS_PLAN.md` that does not exist.
  Document them, fix the reference, and decide whether the paper
  claims them.

**Containment** (`Mpfx/Containment.lean`)

- The completeness section's witnesses that `BoundRep` and
  `Nontrivial` are each needed (A(∞, 0, 3/2) = A(∞, 0, 1) and
  A(∞, 0, 0) = A(∞, 1, 0), as in the paper's Appendix A) are stated
  in its docstring, not proved. `Mpfx.Cex`-style theorems would
  mechanize them.

**Docs**

- The README's tables list the finite forms (`rndRTZ_RTZ`, …) and no
  completeness theorem, while the paper's Appendix A table cites the
  total forms (`roundsRTZ_RTZ`, …, `roundsRTO_RN`) and the
  completeness theorem (`Format.subset_iff_contains`). Add them, with
  their `#print axioms` output.
- The paper's numbers have shifted: containment is Figure 7 (not 8),
  the double-rounding rules Figure 8 (not 9), the format instances
  Table 1, and the lemmas are 5.1 completeness, 5.2 digit count,
  5.3 `w₂ = w₁ + k`, and 5.4 RTO padding (not 5.1 to 5.3). Name
  results rather than number them in the module headers and
  docstrings in `Mpfx/`, `docs/agents/TODO.md`, and `docs/DESIGN.md`,
  so they survive the next shift; renumber the README once the paper
  is final.
