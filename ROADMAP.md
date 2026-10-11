# Roadmap

Open threads the papers need from this development, forward-looking
only; check an item off when it lands. The formalization's own backlog
stays in `docs/agents/`; this file holds only what the papers depend
on. The mechanization is the source of truth: where a paper and the
Lean disagree, the paper changes. References are Lean names under
`namespace Mpfx` or `namespace Fpy` and files under `Mpfx/` or `Fpy/`,
never line numbers.

## Paper revision

**Double rounding**

- [x] Round-to-odd into RTP and RTN, `roundsRTO_RTP_finite` and
  `roundsRTO_RTN_finite`, under the containment of `roundsRTO_RTZ_finite`.
  The paper's evaluation relies on this step for MPFX's RTP and RTN.
- [ ] Round-to-even as a target (RTE: an inexact result goes to the
  neighbour whose last digit is even) is not in `RoundingMode`. On
  small formats, an RTO intermediate padded by one digit in both
  precision and minimum exponent serves it (p1 from 2 to 4 and ∞,
  exp1 from −2 to 0 and −∞, and bounded pairs with b1 ≤ 8 where F2
  does not overflow before the direct rounding), while precision or
  exponent alone fails in 9 of 12. p1 = 1 was not swept, and nothing
  is proved. Either add the mode with a `roundsRTO_RTE` theorem or
  the paper states the exclusion; decide with the library, which
  exposes the mode.
- [x] A bounded negative for the nearest intermediate. The `Mpfx.Cex`
  counterexamples now take any `F₁` with one, two or three positive
  values (`Format.HasPositive`), with every rounding in bound.
- [ ] Tightness of the counterexample counts. The paper's "only in
  trivial cases" can name the counts: RNE→RTZ, RAZ→RTZ, RTZ→RNE and
  RNE→RNE fail once `F₁` is nontrivial, RTZ→RAZ, RNE→RAZ, RAZ→RTO,
  RNE→RTO and RAZ→RNE with two positive values, RTZ→RTO with three.
  That one fewer admits no in-bound counterexample for some `F₂`
  (without a minimum quantum) is argued by hand, not proved. Decide
  whether the paper states the converse; if so, mechanize it.
- [ ] Decide whether the paper claims the per-operation
  double-rounding theorems (Roux 2014: `rndMul_*`, `rndAdd`,
  `rndSqrt_*`, `rndDiv_*`). The README lists them as beyond the
  paper.

**Containment** (`Mpfx/Format/Containment.lean`)

- [ ] The completeness section's witnesses that `BoundRep` and
  `Nontrivial` are each needed (A(∞, 0, 3/2) = A(∞, 0, 1) and
  A(∞, 0, 0) = A(∞, 1, 0), as in the paper's Appendix A) are stated
  in its docstring, not proved. `Mpfx.Cex`-style theorems would
  mechanize them.

**Special values** (`Format.specials`, `Mpfx/DoubleRounding/Special.lean`)

- [ ] The paper's `𝒜(p, exp, b)` gains a fourth parameter, the set of
  specials (`±Inf`, NaN) the format contains. Either the paper states it, or
  it fixes `specials = ∅` and says so; every `Format` in the library states it.
- [ ] §5.1 containment gains a specials conjunct, `F₁.specials ⊆
  F₂.specials`, in `𝒜-Contains-Prec`, `𝒜-Contains-Sub` and completeness
  (`Format.containsPrec`, `Format.containsSub`, `Format.subset_iff_contains`).
- [ ] Appendix A cites the total forms `roundsRTZ_RTZ_inBound`, …,
  `roundsRTO_RN_inBound`, with the overflow disjunct. The library now also has
  equalities on `rnd` with tables: `rndRTZ_RTZ`, …, `rndRTO_RN` under plain
  containment and the table conditions, and `rndRTZ_RTZ_of_bound`, … under
  the paper's relaxed containment for any tables. Decide which the paper
  cites; both stay until then.

**Docs**

- [ ] Renumber the README once the paper is final: containment is
  Figure 7, the double-rounding rules Figure 8, the format instances
  Table 1, and the lemmas are 5.1 completeness, 5.2 digit count,
  5.3 `w₂ = w₁ + k`, and 5.4 RTO padding.

## FPy paper (PLDI draft)

Bugs in the draft's rules, found against the semantics. Each item is a
change to the paper; the Lean states the fixed rule. The phases that
mechanize them are in `docs/agents/FPY_PLAN.md`.

- [ ] Fig. 5, `rnd♯` under an unknown context `?`: with `F_? = R*` the
  first case `F ⊆ F_C` always fires, so the exact bound is kept under a
  context that may round (`t = round(xi)` in `fused_sum`). Fig. 6 shows
  `R*`, so only the rule is wrong. Fix: `rnd♯_?(F) = R*`.
- [ ] Fig. 5 and 11, `A-Context`/`A-Ctx`: `ctx(e)` is "known statically"
  and `ctx e : •`, but Fig. 6 line 5 needs the format of the parameter
  `out`, which no static `ctx(e)` gives. Fix: abstract values carry a
  known context `⟨C⟩` (`R : ⟨R⟩`, `ctx e : ⟨ctx fs⟩` for a known record),
  and `A-Context` reads it off `e`'s abstract value.
- [ ] Table 2, row `IEEE754(e, n, RTZ)`: `[max(l, m − p + 1), m]` is
  unsound, since `m` only bounds the leading digit from above (`v = 1`,
  interval `[0, 10]`, `p = 3`: the result `1` has digit `0 ∉ [8, 10]`).
  Fix: `[max(l, μ − p + 1), μ]` with fresh `μ ≤ m`, as in the next row.
- [ ] §4.2, the side condition that each context "leaves the values of
  `F_C` unchanged": an Mpfx context meets it only when its special map
  fixes the format's specials (e.g. `SpecialMap.exact`). State that
  hypothesis on contexts.
