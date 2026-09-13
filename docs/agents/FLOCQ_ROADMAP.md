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

## 4. `Mpfx/Ulp.lean` — `Core/Ulp.v` — **done**

*Residual notes in [`ULP_TODO.md`](ULP_TODO.md).*

`ulp` (Goldberg's convention, `0` at zero when there is no minimum quantum),
`rndDown`/`rndUp`/`midp`, `succ`/`pred`/`predPos` as total format functions with
the involutions `succ_pred` / `pred_succ`, `succ_le_of_lt` and `le_pred_of_lt`
(Flocq `succ_le_lt`), and `FiniteFormat.next` as the `Dyadic` face of `succ`.
Adjacency in `Discrete.lean` is stated through `succ`, which collapsed the §6
twins as a side effect.

Error bounds: `faithful_error_lt_ulp` (Flocq `error_lt_ulp`),
`nearest_error_le_half_ulp_round` (`error_le_half_ulp_round`), `ulp_rndDown`
(`ulp_DN`), `ulp_round_pos` (`ulp_round`).

Bracket characterisations: `rndDown_eq_of_bracket` (`round_DN_eq`),
`rndUp_eq_of_bracket` (`round_UP_eq`), `nearest_le_of_lt_midp`
(`round_N_le_midp`), `le_nearest_of_midp_lt` (`round_N_ge_midp`). Flocq's
`round_N_eq_DN` / `round_N_eq_UP` are our `nearest_eq_rndDown_of_lt_midp` /
`nearest_eq_rndUp_of_midp_lt`, stated through `midp`; `midp_eq_midpoint_succ`
shows the two midpoint notions agree.

### The "grid" vocabulary — resolved

Retired in favour of `ulp`, `succ`/`pred`, discreteness and `binade`; see the
*Vocabulary* section of [`ULP_TODO.md`](ULP_TODO.md). The short version: Flocq
has no word for the set of representable values at a fixed exponent because,
given `ulp` and `succ`, it never needs one.

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

## 6. `Discrete.lean` case duplication — **done**

All the `_exp_bot` twins are gone, merged on `canonicalExp`:
`not_mem_between_adjacent`, `adjacent_canonical_form`,
`midpoint_mem_extend_one_of_adjacent_pos` and its wrapper. The two
`exists_grid_rep` variants were deleted outright once
`exists_canonical_rep_of_parts` absorbed their consumers. `Grid.lean` 753 →
`Discrete.lean` 626.

`midpoint_mem_extend_one_of_p_top` remains separate and should: with
unrestricted precision it needs no adjacency at all, so it is a different
argument rather than a case of the same one.

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
  `mag_F2R_Zdigits`, `float_distribution_pos`. `Discrete.lean` has ad hoc versions
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

§1, §2, §4 and §6 are done. The ordering below prioritises
**shrinking existing proofs** over adding capability. Measured reduction
potential:

| Item | What it shrinks | Estimate |
| ---- | --------------- | -------- |
| §5 `location` / `inbetween` | `Format.lean` parity (1217 of 2019 lines) + `Parity.lean` (515) | **~800–1000** |
| §9 `Float_prop` items | ad hoc versions in `Discrete.lean` | small |
| §3, §7, §8 | nothing existing | 0 — pure capability |

1. **§5 `location` / `inbetween`** — by far the largest reducer, and the reason
   is parity. Ours is format-relative (`numDigits` + `IsRepresentableAtP`), which
   costs ~1730 lines across `Format.lean` and `Parity.lean`. Flocq's is the
   parity of the canonical mantissa, where adjacent values alternate because
   consecutive integers do — `Int.even_add_one` in place of a six-leaf dispatch.

   Caveat: it will not remove all of it. The `p = 1` branch (302 lines) reads
   parity off the *exponent*, since the significand is constantly `±1`, and has
   no mantissa analogue; Flocq sidesteps that case with `prec_gt_1` and we
   cannot. Budget ~800–1000, not 1730.

   This is also the highest-risk item: it changes what `IsOdd` *means*, so
   everything consuming it is re-proved. Spike the `p ≠ 1` case first.

2. **§9** — the `Float_prop` items, small and self-contained.

§3, §7 and §8 add surface without touching existing proofs; take them when the
capability is wanted, not for cleanup.

## Notes on hunting for duplication

Two scans looked for further duplication to collapse. Real hits: the alternation
pair in `Parity.lean` (−419) and `gap_around_m_mem` / `gap_around_mid3_mem`, now
both wrappers over `gap_around_odd_mem` (odd `c`, `2^j < c < 2^(j+1)`). False
positives: the `Grid` `_exp_bot` twins were not a single theorem in two shapes,
and the `rounds*` family shares a narrative rather than a proof.

A near-duplicate similarity score detects *the same steps with different lemmas*
as readily as real duplication — check what varies before committing.
