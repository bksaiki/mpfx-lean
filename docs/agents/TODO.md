# Autoformalization TODO — *When Double Rounding is Correct*

Paper reference: `When_Double_Rounding_is_Correct.pdf`.

A Lean 4 / Mathlib formalization of Appendix A: format containment (§5.1),
correct double rounding (§5.2, with counterexamples for the invalid mode
pairings), and format inference (§6.1). Three design decisions shape the
development:

1. **Looser top-level type, layered subtypes.** `Format` encodes only
   the natural type-level constraints (`p ≥ 1` via `WithTop ℕ+`, `b ≥ 0`
   via `WithTop NonNegDyadic`). `FiniteFormat extends Format` rules out
   `(p = ⊤, exp = ⊥)`; `ParityFormat extends FiniteFormat` additionally
   rules out `(p = 1, exp = ⊥)` so `IsOdd` / `IsEven` are anchored.
2. **Constructive rounding.** Alongside the spec relation
   `Rounds F rm x r : Prop`, a function `rnd F rm x : RoundResult`
   computes the rounded value via `Int.log` + `Int.floor`/`Int.ceil`
   (FLoPS-style). No `Classical.choose`. The function is
   `noncomputable` only because real comparisons aren't computably
   decidable. The constructive / classical boundary is at the file
   level: `Rounding.lean` is constructive, `RoundOp.lean` is classical.
3. **ℚ substrate.** `Dyadic` is a subring of `ℚ` (not `ℝ`), giving
   `DecidableEq` and a decidable `LinearOrder` for free from `ℚ`, while
   keeping the full Mathlib algebra/tactic suite. `ℝ` is confined to
   exactly where it is intrinsic: the real input `x`, the
   `Int.log`/`Int.floor`/`numDigits` machinery and the `Rounds` spec
   (compares dyadics to real `x`). Even `IsRepresentableAtP` and its
   lemmas (`unique`, `ne_zero`, `of_bounds`, `of_saturation`) are
   `ℚ`-valued — its body never references `numDigits`. The
   `Dyadic → ℝ` coercion factors as `Dyadic → ℚ → ℝ`; the
   `ℚ↔ℝ` boundary is localized to named bridge lemmas
   (`coe_real_*`, `precisionAtMost_coe_real`, `quantumAtLeast_coe_real`,
   `*_extract`). `rnd` is still `noncomputable` (real input `x`), but the
   overflow **sign bit** is a decidable `ℚ` comparison.

`rnd` and `Rounds` are parameterized over `FiniteFormat` — the
`(p = ⊤, exp = ⊥)` case is structurally excluded rather than being
filtered out by `IsUndefined` at runtime.

Status legend: `[ ]` not started · `[~]` in progress · `[x]` done · `[!]` blocked.

## File layout

```
Mpfx/
├── Utils.lean      project-agnostic helpers (two_zpow_pos, etc.)
├── Dyadic.lean     IsDyadic (ℚ), Dyadic := subring of ℚ, ofIntZpow (computable),
│                   coe_real_* / coe_rat_ofIntZpow / ext_real bridge lemmas,
│                   DecidableEq instance,
│                   precisionAtMost, quantumAtLeast (both ℚ-valued) + mono/anti,
│                   precisionAtMost_coe_real / quantumAtLeast_coe_real (ℝ bridges),
│                   IsRepresentableAtP (ℚ) + unique + ne_zero,
│                   precisionAtMost_of_abs_le (saturation renormalization),
│                   isRepresentableAtP_of_saturation, two_pow_succ_pred
├── Format.lean     Format / FiniteFormat / ParityFormat hierarchy,
│                   Mem, boundOK, Format.unbounded,
│                   FiniteFormat.unbounded, FiniteFormat.zero_mem,
│                   FiniteFormat.canonicalExp,
│                   numDigits (Lemma 5.1) + evaluators,
│                   IsOdd, IsEven, parity dichotomy + alternating
│                   + not_both lemmas across all 6 format cases
├── Rounding.lean   relational layer (constructive):
│                   TieBreak, RoundingMode,
│                   RoundResult (with signed overflow), RoundResult.neg,
│                   FiniteFormat.IsUndefined,
│                   IsFaithfulRound, RoundsFinite, Rounds.
│                   Sign-symmetry block: IsFaithfulRound.neg_iff,
│                   per-mode RoundsFinite.neg_*, Rounds.neg_*.
│                   Mode-vs-sign block: RTP/RTN ↔ RTZ/RAZ by sign of x.
├── RoundOp.lean    function layer (noncomputable, classical):
│                   abs_floor_le_of_abs_lt, log_two_pow_nat,
│                   cast_two_pow_pred, log_lt_p_of_abs_lt_two_pow,
│                   log_ge_p_pred_of_two_pow_pred_le,
│                   two_pow_pred_le_scaled, abs_floor_ge_two_pow_pred,
│                   rndInt, rndParity,
│                   FiniteFormat.toParityFormatOf{ToOdd,NearestEven},
│                   rndUnbounded, rnd (with overflow-sign computation),
│                   rnd_iff_rounds
├── Containment.lean §5.1 / Fig. 8: Format.Subset + HasSubset,
│                   boundOK_mono, nnPow, containsPrec, containsSub,
│                   Format.extend + self_subset_extend + extend_mono,
│                   FiniteFormat.extend + numDigits_extend (Lemma 5.2),
│                   withBound + next (+ next lemmas) — §5.2 bound API
├── Grid.lean       grid-step / midpoint-membership theory (prereq for
│                   rndRTO_RN): exists_grid_rep(_exp_bot), grid_rep_c_pos,
│                   no_F_element_in_step_interval(_exp_bot),
│                   F_adjacent_step_form(_exp_bot), prev_F_adjacent_of_log_eq,
│                   and the goal family midpoint_mem_extend_one_of_F_adjacent
│                   (+_pos/_pos_exp_bot/_exp_bot/_of_p_top), half_mem_extend_one.
│                   Built over the ℚ substrate.
├── Digits.lean     §5.1-supporting digit/parity-transfer lemmas (Lemma 5.3):
│                   numDigits_le_one_of_p_one, precisionAtMost_not_IsOdd
│                   (corollary), numDigits_eq_of_subset_of_isOdd(_aux),
│                   odd_index_of_p_one_corner, IsOdd.transfer_of_numDigits_eq,
│                   IsOdd.transfer_of_subset (capstone Lemma 5.3)
├── DoubleRounding.lean §5.2 / Fig. 9 rules (spec-relational over
                    RoundsFinite): rndRTZ_RTZ, rndRAZ_RAZ(_pos), rndRTO_RTO,
                    rndRTO_RTZ, rndRTO_RAZ, rndRTO_RN — ALL paper-exact.
                    RTO helper chain (toOdd_notMem_of_extend_subset, …),
                    paper-containment helpers (hp_F₂_or_F₁_trivial(_RN),
                    extend_{one,two}_subset_of_paper_subset, *_of_trivial),
                    RN web (rndRTO_RN_close_transfer, rndRTO_no_tie_contradiction,
                    rndRTO_nearest_facts) + bridges. Also rndRTP_RTP/rndRTN_RTN.
└── FormatInference.lean §6.1: ⊗/⊕ format inference. Dyadic.abs, Format.toSet,
                    opMul/opAdd/opAddPrec, mul_subset/add_subset (the inferred
                    format contains every product/sum), neg_subset/abs_subset.
```

## Substrate (done)

- [x] `IsDyadic` predicate (over `ℚ`) + closure (`zero`, `one`, `add`,
      `neg`, `mul`).
- [x] `dyadicSubring : Subring ℚ`, `Dyadic` abbrev, `instance : DecidableEq Dyadic`.
- [x] **ℚ-coercion bridge lemmas**: `coe_real_eq_ratCast`, `ext_real`,
      `coe_real_injective`/`coe_real_inj`, `coe_real_{neg,zero,add,sub,mul}`
      (`@[simp, norm_cast]`), `coe_rat_ofIntZpow`.
- [x] `Dyadic.ofIntZpow`, `coe_ofIntZpow` (ℝ), `coe_rat_ofIntZpow` (ℚ).
- [x] `Dyadic.precisionAtMost`, `Dyadic.quantumAtLeast` (ℚ-valued bodies),
      with `precisionAtMost_coe_real` / `quantumAtLeast_coe_real` ℝ bridges.
- [x] `Dyadic.IsRepresentableAtP` (ℚ body) + `unique` + `ne_zero`
      (all ℚ; `numDigits` only supplies the precision index at call sites).
- [x] `Dyadic.precisionAtMost_of_abs_le` (renormalization for saturation; ℚ).
- [x] `Dyadic.isRepresentableAtP_of_saturation`, `isRepresentableAtP_of_bounds`.
- [x] `Dyadic.two_pow_succ_pred`.
- [x] `NonNegDyadic := { d : Dyadic // 0 ≤ (d : ℚ) }`.
- [x] `Format` (`p : WithTop ℕ+`, `exp : WithBot ℤ`, `b : WithTop NonNegDyadic`).
- [x] `Format.boundOK` (ℚ comparison `|d| ≤ b`), `Format.Mem`,
      `Membership Dyadic Format`, `Format.zero_mem`, `Format.unbounded`.
- [x] `FiniteFormat extends Format` with `finite : p ≠ ⊤ ∨ exp ≠ ⊥`,
      `Membership Dyadic FiniteFormat`, `FiniteFormat.unbounded`
      (returns FiniteFormat), `FiniteFormat.zero_mem`,
      `FiniteFormat.canonicalExp`, `exp_le_canonicalExp`,
      `log_sub_p_le_canonicalExp`.
- [x] `FiniteFormat.numDigits` (Lemma 5.1) + evaluators
      (`numDigits_zero`, `numDigits_neg`, `numDigits_top_coe`,
      `numDigits_coe_bot`, `numDigits_coe_coe`, `numDigits_nonneg`).
- [x] `mem_imp_precisionAtMost_numDigits`.
- [x] `ParityFormat extends FiniteFormat` with `parity : p ≠ 1 ∨ exp ≠ ⊥`.
- [x] `ParityFormat.IsOdd`, `IsEven`, `nondegenerate`,
      `IsOdd.neg`, `IsEven.neg`, `IsOdd.numDigits_pos`, `IsOdd.ne_zero`,
      `isEven_zero`, `IsOdd_iff_of_toFormat_eq`, `IsEven_iff_of_toFormat_eq`.

## Parity infrastructure (done)

For each of the 6 format cases (fixedpoint, floating, mixed-subnormal-pne1,
mixed-normal-pne1, mixed-subnormal-p1, mixed-normal-p1), all of:

- [x] `isOdd_iff_odd_at_canonical_*` — characterization via canonical
      `(c, e)` with integer parity of `c` (or exponent index for `p = 1`).
- [x] `isEven_iff_even_at_canonical_*` and `isEven_p1_iff_at_canonical_*` —
      duals.
- [x] `isOdd_iff_odd_of_canonical`, `isEven_iff_even_of_canonical` —
      generic canonical-form characterizations.
- [x] `isEven_iff_not_isOdd_of_canonical`, `not_isEven_and_isOdd` —
      parity dichotomy and mutual exclusion.
- [x] `not_isOdd_at_saturation`, `not_isOdd_at_saturation_mixed_normal`,
      `isEven_at_saturation_floating`, `isEven_at_saturation_mixed_normal` —
      saturation behaviour.
- [x] **Consolidated alternation API** (refactored to single bulk-proof iff
      per case, with the previous three lemmas as thin wrappers):
  - `alternating_parity_*_iff` — `IsOdd dhi ↔ ¬ IsOdd dlo`. The bulk
    proof; combines forward and backward directions in one place.
  - `alternating_parity_*` — thin wrapper `(iff).mpr` (the original
    `¬ IsOdd dlo → IsOdd dhi` shape).
  - `not_both_isOdd_*` — thin wrapper via `not_both_isOdd_of_alternating_iff`.
  - `alternating_isEven_*` — uses the generic `alternating_isEven_of_alternating_iff`
    with saturation cases handled manually where applicable.
- [x] **Generic derivations** (case-independent, in Format.lean ~648):
  - `not_both_isOdd_of_alternating_iff` — `(IsOdd dhi ↔ ¬ IsOdd dlo) → ¬ (IsOdd dlo ∧ IsOdd dhi)`.
  - `alternating_isEven_of_alternating_iff` — same iff plus rep-or-zero
    on each side gives `¬ IsEven dlo → IsEven dhi`.
- [x] `private canonical_rep_*` helpers — extracted rep-construction
    helpers for all 5 sub-cases (`fixedpoint`, `floating`,
    `mixed_normal_pne1`, `mixed_subnormal_pne1`, `mixed_p1`). All
    consolidated near the top of the parity section.
- [x] Characterization wrappers reuse the rep helpers — each
    `isOdd_iff_odd_at_canonical_X` and `isEven_iff_even_at_canonical_X`
    is now a thin 7-22 line wrapper around `isOdd_iff_odd_of_canonical`
    (or `isEven_iff_even_of_canonical`) applied to the appropriate
    `canonical_rep_X`. Format.lean line count: 2155 → 1985 (−170 lines).
- [x] **Saturation lemmas refactored via dichotomy** (Tier 2). New
    helpers: `private two_le_p_of_pne1`, `canonical_rep_at_saturation_floating`,
    `canonical_rep_at_saturation_mixed_normal`, `not_odd_k_div_2_at_sat`.
    Each `*_at_saturation_*` (4 lemmas) now 3-5 lines:
    `not_isOdd_at_saturation_*` rewrites via `isOdd_iff_odd_of_canonical`
    + `not_odd_k_div_2_at_sat`; `isEven_at_saturation_*` derives from
    its `not_isOdd_*` counterpart via `isEven_iff_not_isOdd_of_canonical`.
    Format.lean: 1985 → 1925 (−60 lines).
- [x] `Dyadic.two_pow_succ_pred`, `log_abs_mul_zpow`.

## Rounding (done)

- [x] `TieBreak`, `RoundingMode`, `RoundResult` inductives.
      `RoundResult.overflow` carries a `Bool` sign field (`true` =
      positive overflow) so signed-infinity semantics are recoverable.
- [x] `RoundResult.neg` + simp lemmas (`neg_finite`, `neg_overflow`
      flips the sign bit, `neg_undefined`, `neg_neg`).
- [x] `FiniteFormat.IsUndefined` — `(p = 1, exp = ⊥, .toOdd ∨ .nearest .toEven)`
      (the `(⊤, ⊥)` case is structurally excluded by `FiniteFormat`).
- [x] `FiniteFormat.unbounded_isUndefined` (rfl-simp).
- [x] `IsFaithfulRound : FiniteFormat → ℝ → Dyadic → Prop`.
- [x] `RoundsFinite : FiniteFormat → RoundingMode → ℝ → Dyadic → Prop`.
- [x] `Rounds : FiniteFormat → RoundingMode → ℝ → RoundResult → Prop`
      (IEEE-style overflow via `F.unbounded` + separate `boundOK`;
      `.overflow b` clause adds the sign constraint
      `(b ↔ 0 < (y : ℚ))` — decidable ℚ sign — on the overflowing witness).
- [x] `rndInt`, `rndParity`.
- [x] `FiniteFormat.toParityFormatOfToOdd`, `toParityFormatOfNearestEven`.
- [x] `rndUnbounded`, `rnd` (computes overflow sign from the unbounded
      rounded value).

## Soundness (done — zero `sorry`)

- [x] `rnd_iff_rounds` — the keystone bridge.
- [x] **All 14 per-mode obligations** (`satisfies` + `unique` × 7 modes):
  - `_toNegative`, `_toPositive`, `_toZero`, `_awayZero` (directed
    modes — both satisfies and unique).
  - `_toOdd_satisfies`, `_toOdd_unique` — all 6 format sub-cases
    (fixedpoint, floating, mixed × {subnormal, normal} × {p = 1, p ≠ 1}).
  - `_nearest_satisfies`, `_nearest_unique` — both `.awayZero` and
    `.toEven` tie-breaks, with full format case-split for the
    `.toEven` parity-tie cases.

## Containment (§5.1, Fig. 8) — done

In `Mpfx/Containment.lean` (proved entirely over `ℚ`):

- [x] `Format.Subset` + `HasSubset Format` instance.
- [x] `Format.boundOK_mono` — bound-check monotone in the bound.
- [x] `Dyadic.precisionAtMost_mono` / `quantumAtLeast_anti` (substrate
      monotonicity, in `Dyadic.lean`).
- [x] `containsPrec` — `𝒜-Contains-Prec`: `p₁ ≤ p₂`, `exp₂ ≤ exp₁`,
      `b₁ ≤ b₂` ⟹ `F₁ ⊆ F₂`.
- [x] `containsSub` — `𝒜-Contains-Sub`: degenerate case where `F₁`'s bound
      `≤ 2^(exp₁+p₂)` lets `F₁.p > F₂.p`. Uses `nnPow` helper.
- [x] **Format-extension API**: `Format.extend k` (`p ↦ p+k`, `exp ↦ exp−k`,
      `b` unchanged; `k : ℕ+`), `self_subset_extend` (`F ⊆ F.extend k`),
      `extend_mono` (`j ≤ k → F.extend j ⊆ F.extend k`). All via `containsPrec`.
- [x] `FiniteFormat.extend` lift (preserves the `finite` invariant) +
      `extend_toFormat` simp lemma.
- [x] **Bound-changing API**: `Format.withBound b'` (swap the bound; no
      non-neg witness needed since `NonNegDyadic` carries it) + `withBound_*`
      simp lemmas; `Format.next b` (paper's `next_{p,exp}(b)`, smallest grid
      point above `b`) + `lt_next_of_finite`, `lt_next_of_p_top`,
      `next_nonneg`, `next_eq_finite_pos`, `next_eq_p_top`, `self_le_next`.

## Open: Digits + parity (§5.1 supporting)

- [x] **Lemma 5.2** (`FiniteFormat.numDigits_extend`): extending `F` by `k`
      increases `numDigits x` by exactly `k` (for `x ≠ 0`). In
      `Containment.lean`. (No separate raw-`(p,exp)` `numDigits_shift` —
      `numDigits` is keyed on `FiniteFormat`, so `numDigits_extend` *is* the
      Lemma 5.2 statement.)
- [x] **Lemma 5.3 corollary** — `ParityFormat.precisionAtMost_not_IsOdd`
      (+ prereq `FiniteFormat.numDigits_le_one_of_p_one`): if `y` has
      precision `≤ w` and `numDigits F y > w`, then `¬ F.IsOdd y`. In
      `Mpfx/Digits.lean`.
- [x] **Lemma 5.3** (RTO digit-padding preserves representability) —
      the pivotal lemma for all RTO-composition double-rounding rules.
      In `Mpfx/Digits.lean`, ~750 lines total:
  - [x] `numDigits_eq_of_subset_of_isOdd_aux` — the "≤" direction, the
        ~370-line finer-grid witness core. Hardest proof in the project.
  - [x] `numDigits_eq_of_subset_of_isOdd` — combines corollary (≥) + `_aux`
        (≤). Uses `FiniteFormat.numDigits_nonneg` for the `ℕ+` witness.
  - [x] `odd_index_of_p_one_corner` — the `F₁.p = 1` corner (~227 lines).
  - [x] `IsOdd.transfer_of_numDigits_eq` — `F₁ ⊆ F₂`, `F₂.IsOdd y`,
        `y ∈ F₁`, equal numDigits ⟹ `F₁.IsOdd y`.
  - [x] `IsOdd.transfer_of_subset` — **the capstone Lemma 5.3** (one line,
        composes the digit-count agreement + parity transfer): `F₁ ⊆ F₂`,
        `2 ≤ F₂.p`, `y ∈ F₁`, `F₂.IsOdd y` ⟹ `F₁.IsOdd y`. Consumed by the
        RTO-composition double-rounding rules.

## Rounding API extensions (done)

- [x] **Sign-symmetry helpers** (`Format.lean`, `Dyadic.lean`):
      `Dyadic.precisionAtMost_neg`/`_neg_iff`, `quantumAtLeast_neg`/`_neg_iff`,
      `Format.boundOK_neg`/`_neg_iff`, `Format.neg_mem`, `Format.mem_neg_iff`,
      `FiniteFormat.neg_mem`/`mem_neg_iff`, `Format.boundOK_zero`,
      `ParityFormat.IsOdd.neg_iff`, `IsEven.neg_iff`.
- [x] **`IsFaithfulRound.neg_iff`** — `IsFaithfulRound F x y ↔
      IsFaithfulRound F (-x) (-y)` (swaps RTN- and RTP-witness disjuncts).
- [x] **Per-mode `RoundsFinite.neg_*`** for all seven modes:
      `neg_toZero`, `neg_awayZero`, `neg_toOdd`, `neg_nearest_toEven`,
      `neg_nearest_awayZero`, `neg_toNegative_iff_toPositive`.
- [x] **Per-mode `Rounds.neg_*`** (six, since RTN/RTP are paired):
      `neg_toZero`, `neg_awayZero`, `neg_toOdd`, `neg_nearest_toEven`,
      `neg_nearest_awayZero`, `neg_toNegative_iff_toPositive`. Each
      overflow case threads the sign bit through `RoundResult.neg`'s
      Bool flip.
- [x] **Mode-vs-sign reductions** — `RoundsFinite.*`-level and
      `Rounds.*`-level theorems:
      - `toPositive_iff_awayZero_of_nonneg` (`0 ≤ x → RTP = RAZ`),
      - `toPositive_iff_toZero_of_nonpos` (`x ≤ 0 → RTP = RTZ`),
      - `toNegative_iff_toZero_of_nonneg` (derived via sign-symmetry),
      - `toNegative_iff_awayZero_of_nonpos` (derived via sign-symmetry).

## Open: Rounding API extensions

- [ ] `IsFaithfulRound`-extraction lemmas (split RTN-witness vs
      RTP-witness disjunct accessors).

## Double rounding (§5.2)

The headline application, in `Mpfx/DoubleRounding.lean`. Stated
spec-relationally over `RoundsFinite` (membership + mode condition):
`F₁ ⊆ F₂`, `RoundsFinite F₂ rm₂ x z`, `RoundsFinite F₁ rm₁ z w` ⟹
`RoundsFinite F₁ rm x w`.

**Positive (Fig. 9):**

- [x] `rndRTZ_RTZ` — chained round-to-zero. Sign-trichotomy + maximality
      transfer through `hsub`. No Lemma 5.3 needed.
- [x] `rndRAZ_RAZ` (+ `rndRAZ_RAZ_pos`) — chained round-away-zero. Positive
      case + sign-symmetry (`RoundsFinite.neg_awayZero`) + `x = 0` case.
- [x] `rndRTO_RTO` — chained round-to-odd. Uses Lemma 5.3
      (`IsOdd.transfer_of_subset`) for the `z = w'` parity case; 4-way
      `IsFaithfulRound` adjacency split otherwise. Helper `exp_bot_of_subset`
      (an `exp = ⊥` format can't embed in a finite-`exp` one) discharges the
      non-degeneracy needed to build the `∃ ParityFormat` witness.
- [x] `rndRTO_RTZ` — RTO (in `F₂`) then RTZ (in `F₁`). **Paper-exact** form:
      single bound-aware containment `(F₁.extend 1).withBound F₁.boundAfterNext
      ⊆ F₂` (no separate `hp_F₂`; derived internally via
      `hp_F₂_or_F₁_trivial`, trivial-`F₁` corner via
      `RoundsFinite.toZero_of_trivial`). The `_pos` body keeps the
      `F₁.extend 1 ⊆ F₂` + `hp_F₂` shape, fed by `extend_one_subset_of_paper_subset`.
      RTO helper chain: `toOdd_eq_zero_of_zero`, `toOdd_nonneg_of_nn`,
      `toOdd_notMem_of_lower_numDigits`, `toOdd_notMem_of_extend_subset`
      (Lemma 5.2 + 5.3), `rndRTO_RTZ_pos`.
- [x] `rndRTO_RAZ` (+ `rndRTO_RAZ_pos`) — RTO then RAZ; away-zero mirror of
      RTZ (paper-exact, `RoundsFinite.awayZero_of_trivial` for the corner).
      Lemma 5.3 application sits in the RTN branch (vs RTP for RTZ).
- [x] `rndRTO_RN` (both tie-breaks) — **DONE**, paper-exact form:
      `(F₁.extend 2).withBound (F₁.extend 1).boundAfterNext ⊆ F₂`. Rests on the
      grid/midpoint theory (`Mpfx/Grid.lean`): the midpoint of two F₁-adjacent
      points lies in `F₁.extend 1` (`midpoint_mem_extend_one_of_F_adjacent`),
      hence in `F₂`. The no-tie argument (`rndRTO_no_tie_contradiction`) forces
      a tie's `x = midpoint ∈ F₂`, so `z = x` — contradiction; this discharges
      BOTH tie-break clauses vacuously (no `∃ ParityFormat` witness needed for
      RNE or RNA). Web: `rndRTO_RN_close_transfer`, `rndRTO_no_tie_contradiction`,
      `rndRTO_nearest_facts`; bridges `isFaithfulRound_iff_directed`,
      `RoundsFinite.toOdd_unique_of_mem`, `nearest_midpoint_of_tie`,
      `F_adjacent_of_RN_round_pair`, `midpoint_F₁_in_F₂_of_F_adjacent`;
      containment `hp_F₂_or_F₁_trivial_RN`, `extend_two_subset_of_paper_RN_subset`,
      `RoundsFinite.nearest_of_trivial`.
- [x] `rndRTP_RTP` / `rndRTN_RTN` — directed-mode chains (round toward
      `±∞`). Reduce to RTZ/RAZ by sign regime via the `RoundsFinite`
      sign-bridge iffs (`toPositive/toNegative_iff_{awayZero,toZero}_of_*`;
      the two `toNegative` bridges were added, derived from the `toPositive`
      ones by joint negation). Only need `F₁ ⊆ F₂`.
- (NB: `rndRTO_RTO` legitimately keeps `F₁ ⊆ F₂` + `hp_F₂` — that *is* the
  paper statement for RTO→RTO; only RTZ/RAZ/RN carry the bound-aware
  containment that lets `hp_F₂` be derived.)

**Counterexamples (ten cases) — done** (`Mpfx/DoubleRoundingCex.lean`):
universally quantified over a witness format `F₁_g = 𝒜(p, e, ⊤)` (`p ≥ 2`)
and a compatible `F₂`; each exhibits a real `x` whose chained F₂-then-F₁
rounding disagrees with direct F₁ rounding.

- [x] `no_rndRNE_RNE` (core `no_rndRNE_RNE_arbitrary_F₂`), `no_rndRNE_RAZ`,
      `no_rndRNE_RTZ`, `no_rndRNE_RTO`.
- [x] `no_rndRTZ_RNE`, `no_rndRTZ_RAZ`, `no_rndRTZ_RTO`.
- [x] `no_rndRAZ_RNE`, `no_rndRAZ_RTZ`, `no_rndRAZ_RTO`.

## Format inference (§6.1) — done

The static analysis bounding the value of an *unrounded* operation by an
inferred format — paper §6.1, the `⊗` (mul) and `⊕` (add) operators. Ported
to `Mpfx/FormatInference.lean` (~435 lines). Self-contained (depends only on
`Dyadic`/`Format`).

- [x] `Dyadic.abs` (now **computable**, `if 0 ≤ (x:ℚ)`) + `coe_abs`/`coe_rat_abs`,
      `Format.abs_mem` (`x ∈ F → |x| ∈ F`).
- [x] `Format.toSet` + `mem_toSet` (set-level `⊆` phrasing).
- [x] `opMul` (`⊗`) and `opAdd`/`opAddPrec` (`⊕`) — inferred result formats.
      Since the base `Format` carries no `not_degenerate`/`p_pos`/`b_nn`
      invariants, `opMul`/`opAdd` return a plain `Format` with **no `exp ≠ ⊥`
      hypotheses**. Result bounds built by `match` on `F₁.b, F₂.b` into
      `WithTop NonNegDyadic` (any `⊤` operand ⇒ `⊤`).
- [x] `mul_inferred`/`add_inferred` (predicate level, ℚ), `add_prec_finite`
      (floor/clog bound, ℝ ratio bridged to ℚ), capstones `mul_subset` /
      `add_subset`.
- [x] `neg_subset`, `abs_subset`.
- `opAddPrec` uses a tighter floor-based precision `⌈log₂(⌊(b₁+b₂)/2^m⌋+1)⌉`
  than the paper's `⌈⌉`-inside form, saving a bit when the bound is misaligned
  with the inferred quantum.

## Open: New features

- [ ] **Fig. 7 format instances**: `binary64`, `binary32`, `E5M2`,
      `E4M3`, `int8`, `fixed<-4, 8>`. Concrete `FiniteFormat` or
      `ParityFormat` values; useful as smoke tests.
- [ ] **Smoke tests** (`Mpfx/Tests.lean`): concrete
      `rnd F rm x = .finite y` proofs. Since `rnd` is `noncomputable`,
      these are `rfl`/`decide`-style equational proofs, not `#eval`.
      *Computable-mirror option*: define `rndQ : FiniteFormat → RoundingMode
      → ℚ → RoundResult` for rational inputs and prove
      `rndQ F rm q = rnd F rm (q : ℝ)`, then close concrete tests by
      `decide`/`native_decide`. The `ℚ` substrate (decidable eq/order)
      makes this viable; Lean-core `Dyadic` could back the `native_decide`
      kernel via `toRat` if raw speed is ever needed.
- [ ] **Cross-references** to the paper: `binary32 ⊆ binary64` via
      `containsPrec`; `E5M2 ⊆ binary64` via `containsSub`.
- [ ] **§3.5 numeric example**: `rnd_{E5M2,RNE}(1.26)` evaluates as
      expected.
- [ ] **Concrete counterexample**: composing E2M1 and E4M3 RNE of
      1.26 differs from direct E2M1 RNE rounding (paper §3.5).

## Open: Refactoring / cleanup (low-priority)

- [ ] **`@[simp]` lemmas** for `F.toFormat.p = F.p`, etc., across the
      tier hierarchy. Currently `F.toFormat` projections need manual
      `change` in proofs. (Mathlib convention: prefer explicit `.toFormat`
      access; only add `simp` lemmas where they're load-bearing.)
- [ ] **Optional `Coe FiniteFormat Format` instance**. Currently we
      require `.toFormat` at call sites. Add only if noise becomes
      overwhelming.
- [ ] **Module docstrings** per file, paper-reference cross-links, and
      a top-level `Mpfx/README.md`.

## Open: substrate ergonomics (low-priority)

User-facing wrappers around the format-parameterized primitives, useful for
smoke tests and external use:

- [ ] Public `Dyadic.precision : Dyadic → WithTop ℕ+` (currently approximated
      by `numDigits`, which is format-parameterized).
- [ ] Public `Dyadic.quantum : Dyadic → WithBot ℤ`.
- [ ] `Dyadic.toCanonical : Dyadic → ℤ × ℤ` returning `(c, e)` with `c` odd or
      `c = 0`. Backbone exists in `exists_odd_canonical_of_precisionAtMost`.
- [ ] Format-independent `Dyadic.isOdd` / `Dyadic.isEven` predicates.
- [ ] `simp` set for `c · 2^e` normalization (assoc/comm, regrouping
      `c · 2^e = 2c · 2^(e-1)`).

## Documented non-theorems / possible extensions

- `rndRTO_RTP`, `rndRTO_RTN` (RTO then a directed mode) — provable by
  sign-reduction like `rndRTP_RTP`/`rndRTN_RTN`; not yet ported.
- `rndRNA_RNA` is **not** correct double rounding — RNA→RNA chains can fail at
  binade-boundary inputs (pen-and-paper). A counterexample analogous to
  `no_rndRNE_RNE` could be formalized.
- `rndRTE_RTE` (round-to-even, the dual of RTO) is **not** a theorem either.

## Long-term / out of scope

- Subnormal flushing, signed zero, ∞, NaN (paper §9).
- Overflow semantics for double rounding under saturation modes.
- Posits, P3109 unsigned floats.
- Stochastic rounding modes (FLoPS does these; not needed for
  *When Double Rounding is Correct*).
