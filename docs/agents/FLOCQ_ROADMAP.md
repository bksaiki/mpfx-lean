# Flocq roadmap

Design ideas and missing lemma families to port from **Flocq 4.2.2**
(<https://flocq.gitlabpages.inria.fr/>). Scope is *extension*: `mpfx-lean` was
purpose-built for containment (§5.1), double rounding (§5.2) and format
inference (§6.1), and is complete there. This file records what a more
feature-complete rounding library would need, and which Flocq file to crib it
from.

## Where the two libraries line up

Both use a two-layer architecture, and the layers correspond directly:

| Layer         | Flocq                                                 | mpfx-lean                                |
| ------------- | ----------------------------------------------------- | ---------------------------------------- |
| Relational    | `Rnd_DN_pt` … `Rnd_odd_pt` (`Defs.v`, `Round_odd.v`)  | `RoundsFinite` (`Rounding.lean`)         |
| Function      | `round beta fexp rnd` (`Generic_fmt.v:614`)           | `rndUnbounded` (`RoundOp/Defs.lean:122`) |
| Bridge        | `round_DN_pt`, `round_N_pt`, … (per mode)             | `rnd_iff_rounds` (`RoundOp.lean:52`)     |

`F.canonicalExp` is Flocq's `cexp x = fexp (mag beta x)` specialized to
`FLT_exp e = max (e - prec) emin`; `p = ⊤` gives `FIX_exp`, `exp = ⊥` gives
`FLX_exp`. So our `(p, exp)` lattice is a sublattice of Flocq's `Valid_exp`
family: we lose FTZ and arbitrary `fexp`, we gain a concrete two-parameter
format with decidable, *complete* containment rules.

Divergences that are deliberate and should stay: binary-only radix; `Dyadic`
(a subring of `ℚ`) as the result type rather than `ℝ` with a `generic_format`
side condition; `b : Bound` inside the format with IEEE overflow modelled by
`RoundResult`; degenerate `(p=1, exp=⊥)` handled by a total function returning
`.undefined` rather than by theorem hypotheses (Flocq's `prec_gt_1`).

---

## 1. Rounding monotonicity — **done**

`Mpfx/RoundPred.lean` holds the relational consequences of the `RoundsFinite`
spec, none of which mention the `rnd` construction:

* uniqueness per mode and generic (`RoundsFinite.unique`, Flocq `round_unique`);
* faithfulness (`RoundsFinite.isFaithfulRound`);
* `eq_zero_of_zero`, `toNegative_nonneg`, `toPositive_nonpos`;
* monotonicity per mode and generic (`RoundsFinite.monotone`, Flocq `round_le`);
* the grid bridges `toNegative_floor` / `toPositive_ceil` and their equation
  forms, plus `isOdd_alternate_of_bracketing`.

`rndUnbounded_unique` is now one line on top of `RoundsFinite.unique`, and the
per-mode uniqueness wrappers are gone. The construction depends on the
relational layer rather than the reverse.

## 2. Faithfulness for every mode — **done**

`RoundsFinite.isFaithfulRound` concludes `IsFaithfulRound F x y` for all seven
modes; `isFaithfulRound_iff_directed` reads it back as the two-sided
disjunction.

## 3. The `abs` family

Done: `round_generic` (`RoundsFinite.eq_of_mem`), `round_0`
(`RoundsFinite.eq_zero_of_zero`), and sign preservation for the directed modes
(`toNegative_nonneg` / `toPositive_nonpos`).

Still missing: the `abs` family — `round_ZR_abs`, `round_AW_abs`,
`round_abs_abs`, `Rnd_N_pt_abs`. We have the `neg` family, which is the harder
half; these are cheap and get used constantly.

## 4. A real `Mpfx/Ulp.lean` — `Core/Ulp.v`

`NearestMidpoint.lean` already defines `ulp`, `rndDown`, `rndUp`, `midp` as
helpers for one proof. Flocq's `Ulp.v` is 2663 lines of exactly this theory.
Worth promoting to its own file, and adding:

- **`succ` / `pred` as total format functions**, with `succ_pred`, `pred_succ`,
  `succ_le_lt`, `pred_UP_eq_DN`, `succ_DN_eq_UP`. Our `Format.next`
  (`Containment.lean:495`) is bound-oriented and documented as returning "a junk
  value" outside its intended range. A total `succ`/`pred` pair with an
  involution law would simplify `Grid.lean` considerably.
- **Error bounds**: `error_lt_ulp` (faithful), `error_le_half_ulp` (nearest),
  `error_le_half_ulp_round`, `ulp_DN`, `ulp_round`. We have only
  `nearest_error_le_half_ulp`. These are the entry point to any
  numerical-analysis extension.
- **Bracket characterizations**: `round_DN_eq` (`d ≤ x < succ d → rndDown x = d`),
  `round_UP_eq`, `round_N_le_midp`, `round_N_ge_midp`, `round_N_eq_DN`,
  `round_N_eq_UP`, `round_N_eq_ties`. These turn "what does rounding do to *this*
  value" from a proof into a rewrite.

### Deferred: the "grid" vocabulary

**Revisit at the end**, once Tracks A–C are complete — not before, and not as a
standalone change.

`Grid.lean`'s "grid" convention has no counterpart in Flocq: the word appears
**zero times** in its source. The concept is split across four standard terms:

| mpfx | Flocq |
| ---- | ----- |
| grid step `2^e` | `ulp x = bpow (cexp x)` (`Ulp.v:93`) |
| grid point | canonical float — `canonical f := Fexp f = cexp (F2R f)` (`Generic_fmt.v:79`) |
| `exists_grid_rep` | `canonical_generic_format` / `generic_format_canonical` |
| `no_F_element_in_step_interval` | `generic_format_discrete` (`Generic_fmt.v:462`) |
| `F_adjacent_step_form` | `succ` / `pred` (`Ulp.v:391`); also `float_distribution_pos` |
| `midpoint` | `midp` (`Double_rounding.v:67`) — already matches |

`generic_format_discrete` is nearly our lemma verbatim: if `m·2^e < x <
(m+1)·2^e` at the canonical exponent then `x` is not in the format. Same
content, called discreteness rather than "no element in the step interval".

Caveat: none of these names the *set* of points at a given exponent, which is
what "grid" most naturally denotes. Flocq has no noun for it — it says "the
format" and uses `ulp` for spacing, moving between exponents with
`F2R_change_exp`. So "grid" is doing work Flocq distributes across `ulp`,
`canonical` and `discrete`; the issue is not that Flocq has a better word but
that it never needs one.

Why defer: half the vocabulary is already aligned (`NearestMidpoint.lean`
defines `ulp` and `midp` with docstrings citing Flocq), and the items above
*restructure* the very lemmas a rename would touch — `F_adjacent_step_form`
becomes a `succ` fact, `no_F_element_in_step_interval` becomes discreteness.
Renaming first means touching them twice.

### Latent divergence: `ulp 0`

`canonicalExp F 0 = 0` in the `(p finite, exp = ⊥)` branch
(`Format.lean:196`), so `ulp F 0 = 1` for FLX-shaped formats, and `ulp_pos`
(`NearestMidpoint.lean:34`) asserts `0 < ulp F x` unconditionally.

Flocq handles this deliberately with `negligible_exp : option Z`
(`Ulp.v:45`): `ulp 0 = 0` when there is no minimal exponent (FLX), and
`bpow (fexp n)` when there is (FIX, FLT). Harmless today — nothing states a
property of `ulp` at `0` — but it will bite the moment one does. Decide the
convention before building the ulp theory on top.

## 5. The `location` / `inbetween` abstraction — `Calc/Bracket.v`

Flocq's best design idea, and the only item here that changes the *shape* of the
library:

```coq
Inductive location := loc_Exact | loc_Inexact of comparison.
inbetween_float m e x l   (* x ∈ [m·β^e, (m+1)·β^e), l says where vs. the midpoint *)
round_N (p : bool) l      (* each mode is just: location -> bool *)
```

Three consequences:

1. Each mode becomes `Location → Bool` rather than a bespoke floor/ceil/midpoint
   comparison. Our `rndInt` (`RoundOp/Defs.lean:71`) inlines all of that per mode.
2. **It removes the `rndParity` asymmetry.** `rndParity`
   (`RoundOp/Defs.lean:97`) must take a whole `ParityFormat` because `IsOdd` is
   format-relative; Flocq passes one bool, `negb (Z.even mx)`, the parity of the
   canonical mantissa. If parity were "parity of the grid coefficient at
   `canonicalExp`", a single `rndInt : RoundingMode → Bool → Location → ℤ → ℤ`
   would cover all seven modes, and `ParityFormat` plus the two
   `toParityFormatOf*` promotions could go away.
3. It is the prerequisite for `Calc/{Div,Sqrt,Plus}.v` — actually *computing*
   correctly-rounded operations, the obvious extension after format inference.
   It also gives a computable mirror of `rnd` on dyadic inputs, which is what
   the "smoke tests" item in `TODO.md` wants.

## 6. `Grid.lean` case duplication — partly done, re-scoped

`exists_grid_rep` now rides a single `canonicalExp`-phrased engine,
`exists_grid_rep_canonical`, and the shared binade bound is factored out as
`log_le_of_canonical_rep`. `exists_canonical_rep` dropped from 24 lines to 6.

The original premise — that the `_exp_bot` twins collapse once phrased over
`canonicalExp` — held only in part. `exists_grid_rep_exp_bot` never mentions
`F.exp`: it is a *precision-only* statement true of any format, and `_exp_bot`
names its use site rather than a hypothesis. So it does not merge.

Three twin pairs remain unexamined (`F_adjacent_step_form`, two midpoint pairs).
Check whether each is a genuine `max`-vs-no-`max` split before assuming it
collapses.

## 7. Operation-level error lemmas — `Prop/`

`FormatInference.lean` gives the *forward* direction: the exact result of an
operation fits in an inferred format. Flocq has the *backward* direction, which
is what exact-arithmetic (EFT) work needs:

| Flocq                              | Statement                                             |
| ---------------------------------- | ----------------------------------------------------- |
| `sterbenz` (`Sterbenz.v:154`)      | `y/2 ≤ x ≤ 2y → x - y ∈ F`                            |
| `generic_format_plus`              | sum of two F-values with bounded exponents is in F     |
| `plus_error` (`Plus_error.v:119`)  | the rounding error of `+` is itself representable      |
| `mult_error_FLX` / `_FLT`          | same for `×`                                          |
| `div_error_FLX`, `sqrt_error_FLX_N`| same for `/`, `√`                                     |
| `format_REM` (`Div_sqrt_error.v`)  | the IEEE remainder is exact                            |

`Prop/Relative.v` additionally has the full relative-error theory
(`relative_error_N_FLX`, `u_ro`, and the FLT variants) — the standard
`|rnd x - x| ≤ u|x|` bounds.

## 8. Range-restricted containment — `Generic_fmt.v:2200`

`generic_inclusion_mag`, `generic_inclusion`, `generic_inclusion_le_ge`,
`generic_inclusion_le`, `generic_inclusion_ge`: "`F₁ ⊆ F₂` on `[a,b]`".

Our containment is global, decidable and *complete*, which is stronger where it
applies; range-restricted containment is the complementary tool for per-binade
reasoning. `generic_round_generic` (rounding an `F₁`-value into `F₂` stays in
`F₁`) is double-rounding-adjacent and we do not have it.

## 9. Smaller items

- **`Rnd_N0_pt`** — nearest, ties toward zero. Not IEEE, but a third `TieBreak`
  constructor is cheap and Flocq carries the full theory
  (`Round_pred.v:1030` onwards).
- **`Float_prop.v`**: `F2R_change_exp`, `F2R_prec_normalize`, `mag_F2R_bounds`,
  `mag_F2R_Zdigits`, `float_distribution_pos`. `Grid.lean` has ad hoc versions
  of several.
- **`Digits.v`**: `Zdigits_mult`, `Zdigits_mult_strong`, `Zdigits_mult_ge`,
  `Zdigits_div_Zpower`. Mathlib's `Int.log` covers much of this, but the
  digits-of-a-product results are what make precision arguments like
  `mul_subset` go through smoothly.
- **`Prop/Double_rounding.v`** — Flocq's own double-rounding development (97
  results). Already cited by `DoubleRoundingMul.lean` and
  `NearestMidpoint.lean`. Its `round_round_plus` / `_minus` / `_sqrt` /
  `_mult` families, each with FLX/FLT/FTZ specializations, are the closest
  existing comparison point for §5.2 and worth a systematic diff.

---

## Suggested order

§1 and §2 are done. Next:

1. **§4 `Ulp.lean`** (settling the `ulp 0` convention first) — everything
   numerical needs it, and the deferred "grid" rename travels with it.
2. **§5 `location` / `inbetween`** — the only structural change; removes
   `ParityFormat` as a side effect and opens the path to computable operations.

§3 and §6 are small and can be done opportunistically. §7 and §8 are new
feature surface, not cleanup.
