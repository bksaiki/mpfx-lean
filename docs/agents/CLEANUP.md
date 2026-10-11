# Cleanup plan

Simplifications of the development, from a review of its structure and
proofs. Line counts are estimates and overlap, so they do not add up.
Declarations are named rather than located.

Status legend: `[ ]` not started · `[~]` in progress · `[x]` done · `[!]` blocked.

## Suggested order

1. The tie-break-uniform nearest clause (§S4), after checking the paper's
   wording.
2. The `rndInt`/`rndDown` definitions (§S4).
3. `.undefined` (§S5), once the paper settles it.

## S4. Modes as selections between round-down and round-up

`RoundsFinite` lists each mode separately, so several facts are proved per
mode. `FiniteFormat`'s two invariants are exactly "every real has a floor and a
ceiling in the grid", so every mode is "`x` if representable, else a choice
between `rndDown x` and `rndUp x`".

* [ ] `rndInt` and `rndParity` still carry unreachable fallback arms, and
  `rndDown`/`rndUp` in `Ulp.lean` are defined through `rndUnbounded` rather than
  as the floor and ceiling points (which would make `rndDown_eq` `rfl` and
  `rndDown_spec` `toNegative_floor`).
* [ ] One tie-break-uniform nearest clause (spec change; check the paper's
  wording first): `∀ z ∈ F, faithful z → z ≠ y → |x − y| = |x − z| →
  tb.Prefers F y z`. The `.toEven` and `.awayZero` clauses are the same shape
  after currying. This removes `cases tb` duplication from `eq_of_mem`, the
  nearest `neg_*`, `unique_nearest`, `nearest_min`,
  `nearest_restrict`/`nearest_lift`, `nearest_error_le_half_ulp`,
  `nearest_eq_of_close` and `DoubleRounding/Nearest.lean`. About 120 lines.

**Larger version (high churn).** Make rounding a function `sel_rm(x, down x,
up x)` with `RoundsFinite` characterisations as theorems. Per-mode uniqueness
disappears, `neg_*` and `monotone_*` become one lemma each, and the directed
double-rounding rules become `⌊⌊x⌋₂⌋₁ = ⌊x⌋₁` for any `V₁ ⊆ V₂` plus sign
reduction. It loses the bounded-`F` reading of `RoundsFinite` (RTZ saturates,
RAZ is partial past `b`), which is neither the paper's semantics nor the
unbounded one and exists only as a proof device. Entry point: a single
`RoundsFinite.iff_select` theorem, then migrate gradually.

## S5. `IsUndefined` and `.undefined`

Needs a paper decision.

* [ ] Whether `rnd` stays `.undefined` at `(1, ⊥)` with RTO/RNE. `IsOdd` already
  computes something there (exponent parity through `unbotD 0`), and it
  alternates; `(1, ⊥)` is only special in that no 2-colouring is invariant
  under doubling, which no theorem uses. If `.undefined` goes, `rnd` returns
  `WithSpecial Dyadic` directly, `rndUnbounded` loses its unused `_h_undef`
  argument, `ParityFormat` goes, and about 110 `IsUndefined`/`.undefined` hits
  go, including `h₁u` on RNA statements, where RNA is never undefined. If it
  stays, drop only `rndUnbounded`'s argument.

## Not worth doing now

* **`Special.lean` binders.** Each `rndX_Y` repeats six to eight lines of
  binders. A `section` with `variable` binders, or a `DoubleRule` structure,
  would only shorten signatures; each rule body is already one `rnd_double` or
  `.of_bound` call.

* **The four `not_isUndefined_*` lemmas.** Identical one-liners with about 60
  call sites; one lemma taking `rm ≠ .toOdd` and `rm ≠ .nearest .toEven` would
  make every call site longer.
* **`opposite_sides_of_ne` via `eq_or_eq`.** It needs the round-down and
  round-up in hand and the pair split afterwards, which is no shorter than the
  current eight-line proof.

* **`Mul.lean` merge.** `mul_mem_F₂_unbounded` already takes `F₂.exp ≤ F₁.exp +
  F₁.exp`, so `rndMul_expBot` and `rndMul_expFinite` are two instantiations of
  one theorem. Merging renames README-listed theorems, and each is already a
  one-line `rndExact`; it saves only a docstring.
* **The second successor.** `Format.next` (the paper's `next_{p,exp}`, four arms)
  sits beside `FiniteFormat.next` (`b + 2^cexp b`) because `boundAfterNext` is
  defined on `Format`. Restating `boundAfterNext` on `FiniteFormat` would remove
  about 100 lines of `Format.next` helpers, but it moves the relaxed-containment
  hypotheses of the README theorems off the paper's definition, and the two
  successors differ at `exp = ⊥, b = 0` (`1` against `0`), which needs its own
  argument there.
* **`Dyadic` over ℝ instead of ℚ.** The cast cost is real (53
  `coe_real_eq_ratCast`, 67 `ext_real`/`coe_real_inj`, about 500 cast-tactic
  lines), and the decidability it buys is used only for the overflow sign. But
  it touches every file and gives up the computable `rndQ` option in
  `TODO.md`. Revisit only if that option is abandoned.
* **Roux files** (`Add`, `Div`, `Sqrt`, `Mul`, `NearestMidpoint`). Mostly
  genuine `zpow`/floor arithmetic.
* **`Counterexample/`.** Already in the generic style.
* **`HasPositive` via `encard`.** Cosmetic.
