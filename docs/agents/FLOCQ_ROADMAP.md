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

## 1. Rounding monotonicity — `Core/Round_pred.v`

*Planned in detail in [`ROUND_PRED_TODO.md`](ROUND_PRED_TODO.md).*

**Nothing in `Mpfx/` proves rounding is monotone.** Flocq builds its whole
predicate theory on it:

```coq
round_pred_monotone P := forall x y f g, P x f -> P y g -> (x <= y)%R -> (f <= g)%R
round_unique : round_pred_monotone rnd -> rnd x f1 -> rnd x f2 -> f1 = f2
```

Two payoffs:

- **`round_le`** (`x ≤ y → rnd x ≤ rnd y`) is Flocq's most-reused fact —
  `round_ge_generic`, `round_le_generic`, `abs_round_le_generic`, `mag_round`
  and every error bound route through it. We have none of these.
- Uniqueness *derives* from monotonicity. The six bespoke
  `rndUnbounded_unique_*` proofs dispatched at `RoundOp.lean:34` could collapse
  to one `round_unique` plus six monotonicity proofs, which are easier.

Suggested shape: a new `Mpfx/RoundPred.lean` with `Monotone (RoundsFinite F rm)`
per mode, then `round_unique`, `round_le`, and the cheap sign family
`round_pred_ge_0 / gt_0 / le_0 / lt_0`.

## 2. `round_DN_or_UP` for every mode — `Core/Generic_fmt.v:577`

Flocq's `Valid_rnd` class (`Zrnd_le` + `Zrnd_IZR`) yields, once and for all,
`Zrnd_DN_or_UP : rnd x = Zfloor x ∨ rnd x = Zceil x`, and `Zrnd_ZR_or_AW`.

We assert faithfulness *inside* the spec for RTO and the nearest modes
(`IsFaithfulRound`, `Rounding.lean:121`) but never state it for
RTZ/RAZ/RTN/RTP. Half the work is already done: `isFaithfulRound_iff_directed`
(`Rounding.lean:257`) converts a faithful witness into
`RoundsFinite .toNegative ∨ RoundsFinite .toPositive`. What is missing is the
all-modes version

```lean
theorem RoundsFinite.isFaithfulRound :
    RoundsFinite F rm x y → IsFaithfulRound F x y
```

which lets every mode-generic argument stop case-splitting on `rm`. Note
`isFaithfulRound_iff_directed` is currently used only in `DoubleRounding.lean` —
never in `RoundOp/`, where it would do the most good (see §1).

## 3. Exactness, zero, and the `abs` family

- **`round_generic`** — *already present* as `RoundsFinite.eq_of_mem`
  (`Rounding.lean:305`), covering every mode, with the `RoundResult`-level
  corollary `rndExact` (`DoubleRoundingMul.lean:45`). Nothing to do.
- **`round_0`**, `Rnd_DN_pt_refl`, `Rnd_DN_pt_idempotent`.
- **`abs` family**: `round_ZR_abs`, `round_AW_abs`, `round_abs_abs`,
  `Rnd_N_pt_abs`. We have the `neg` family (`Rounds.neg_*`) — the harder half;
  the `abs` half is cheap and gets used constantly.
- **Sign preservation**: `0 ≤ x → 0 ≤ rnd x`, `Rnd_N_pt_ge_0 / le_0 / 0`.

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

## 6. Collapse the `Grid.lean` case duplication

`Grid.lean` carries near-duplicate twins and triplets: `exists_grid_rep` /
`_exp_bot`, `F_adjacent_step_form` / `_exp_bot`,
`midpoint_mem_extend_one_of_F_adjacent` / `_pos` / `_pos_exp_bot` / `_exp_bot` /
`_of_p_top`.

Flocq has no such duplication because every statement is phrased through `fexp`,
which absorbs FLX/FLT/FIX into one function. We already have that unifier —
`canonicalExp` — and `CanonicalExp.lean` proves the `canonicalExp_FLX` /
`canonicalExp_FLT` specializations. Restating the `Grid.lean` lemmas in terms of
`canonicalExp`, instead of matching on `(F.p, F.exp)`, should collapse the
variants into single statements.

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

1. **§1 monotonicity / `round_pred`** — retroactively simplifies proofs already
   written, and unlocks the `round_le`-dependent lemmas in §3 and §4.
2. **§4 `Ulp.lean`** (settling the `ulp 0` convention first) — everything
   numerical needs it.
3. **§5 `location` / `inbetween`** — the only structural change; removes
   `ParityFormat` as a side effect and opens the path to computable operations.

§2, §3 and §6 are small and can be done opportunistically. §7 and §8 are new
feature surface, not cleanup.
