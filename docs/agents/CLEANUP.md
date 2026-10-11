# Cleanup plan

Findings of a read-only review of the whole development at commit `2293cbc`
(about 19k lines). Four passes: a Lean-level pass over each of `Format/`,
`Rounding/` and `DoubleRounding/`, looking for de-duplication and simpler
proofs, and a structural pass asking whether the formalism is more complex than
its mathematics. Nothing here has been built. Line counts are estimates, and
the estimates overlap, so they do not add up. Declarations are named rather
than located; where a range helps it is given as of `2293cbc`.

The four passes converged on the same five structural causes. Together they
account for most of the size; scattered sloppiness accounts for little.

Status legend: `[ ]` not started · `[~]` in progress · `[x]` done · `[!]` blocked.

## Suggested order

1. Quick wins (§Q) and the unused-API decision (§U). Independent, low risk,
   about 1–1.5k lines.
2. A uniform `canonicalExp` and successor API (§S3). It unblocks §S1 and §S2.
3. Parity via coarsening (§S1). The largest remaining block of size and case
   splitting.
4. The generic overflow theorem (§S2), prototyped on RTO → RN.
5. Modes as selections between round-down and round-up (§S4), and the
   `ParityFormat` question (§S5) once the paper settles `.undefined`.

## Structural findings

### S1. Parity by coarsening, not by canonical significand

About 2.5k lines down to about 600. Medium risk.

`IsOdd` is defined through the canonical significand at `numDigits` precision,
so every parity fact is proved per regime: fixed point or floating, normal or
subnormal, `p = 1` or not, plus saturation at binade tops. That is
`Format/Parity/Alternate.lean` (1017 lines), most of `Format/Digits.lean`
(879), `Rounding/Parity.lean` (563) and the `IsEven` half of
`Format/Parity.lean`.

**The structure.** Let `C(𝒜(p, e, b)) = 𝒜(p − 1, e + 1, b)`, with `⊤` and `⊥`
preserved. For `p ≥ 2` or `p = ⊤`, and any `exp` including `⊥`:

* `IsEven_F y ↔ y ∈ C(F)` and `IsOdd_F y ↔ y ∈ F \ C(F)` (unbounded
  memberships). Checked by hand in the subnormal, normal, binade-crossing and
  fixed-point cases.
* `C ∘ extend 1 = id` on parameters, and `C` is monotone under `⊆` (both
  containment rules survive the shift `(p − 1, e + 1)`; completeness needs
  `BoundRep`, handled by replacing `b₁` with its grid floor).
* `p = 1` stays a separate case: its even set `{0, ±2^(e+1+2j)}` is not a
  format. It is short: an `F₂`-odd power of two with `p₂ ≥ 2` must be
  `2^exp₂`.

**What follows.**

* Lemma 5.3 (`toOdd_notMem_of_extend_subset`) in about three lines:
  `F₁ = C(F₁.extend 1) ⊆ C(F₂)`, so every `F₁` value is `F₂`-even and an
  `F₂`-odd RTO result is not in `F₁`.
* `IsOdd.transfer_of_subset` is monotonicity of `C`.
* Alternation is one lemma: at `e = canonicalExp x` with `0 < |c| ≤ 2^p`,
  `c · 2^e ∈ C(F)` iff `c` is even.

**What it replaces.**

* `Format/Digits.lean`: `numDigits_eq_of_subset_of_isOdd(_aux)` (about 320
  lines), `odd_index_of_p_one_corner` (about 185), `IsOdd.transfer_of_numDigits_eq`,
  `precisionAtMost_not_IsOdd`, and most of `mem_imp_precisionAtMost_numDigits`.
* `DoubleRounding/Basic.lean`: `toOdd_notMem_of_lower_numDigits`.
* `Format/Parity/Alternate.lean`: the per-regime `alternating_parity_*_iff`
  and `alternating_isEven_*` pairs, the `canonical_rep_*` and
  `*_at_saturation_*` helpers, and the copy-pasted `h_neg2_canon`/`h_2_canon`
  pairs.
* `Rounding/Parity.lean`: the six `alternate_*` leaves and the `Alternate`
  abbreviation.
* The `IsEven` twin of each `IsOdd` lemma (`IsEven.neg`, `.congr`,
  `isEven_iff_even_of_canonical`, `parity_witness_even_congr`), since `IsEven`
  and `IsOdd` become complementary on nonzero values by definition.

**Keep** `isOdd_iff_canonical` as a theorem for paper fidelity, and
`IsOdd.transfer_of_subset` under its current name. `rndParity` needs one lemma:
the floor neighbour is in `C(F)` iff `⌊s⌋` is even.

**What the counterexamples already use.** Only alternation, "`0` is even" and
discreteness (`alternate_of_adjacent`, `exists_pred`). That is the interface
this design provides directly.

**Intermediate option** if `C` is too large a change. Prove `IsOdd y ↔ Odd
(y · 2^-cexp y)` for `p ≠ 1`. Alternation then splits two ways (`cexp d = e`,
or `d = ±2^k` with even mantissa `2^(p−1)`) instead of six. Generically,
`IsEven y ↔ y = 0 ∨ ¬ IsOdd y` on `F.unbounded` removes the even half of every
alternation leaf.

### S2. Overflow stated once

About 1.8k lines down to about 400. Statements and names unchanged. Medium
risk.

`DoubleRounding/Propagation.lean` (908) and the rule bodies of
`DoubleRounding/Total.lean` (898) repeat one argument per rule:

1. Take `N`, the `F₁`-successor of `b₁`.
2. Bound `|x|`, `|z|`, `|w|`, `|y|` by `N` using faithfulness alone
   (`abs_faithful_le_of_le`, `le_abs_faithful_of_le`).
3. Restrict to `G = F₁.withBound N`, apply the finite rule, lift, and conclude
   `w = y` by uniqueness.

`toOdd_toOdd_noOverflow_chain` and `toOdd_toOdd_noOverflow_direct` already do
exactly this, and nothing in it depends on the modes. `F₁⁺ ⊆ F₂` is
`F₁ ⊆ F₂ ∧ N ∈ F₂`, since no grid value lies strictly between `b₁` and `N`;
the proofs already consume it in that form.

**Proposal.** One `total_of_local` taking the finite rule and a threshold
value `T ∈ F₂`. It gives the `_inBound` and `_noOverflow` forms and
`OverflowAgrees.of_bound`. The threshold is mode-specific twice:

* RAZ → RAZ: `T` is the largest `F₁` value, which is why plain containment
  suffices.
* RTO → RN: `T` is the midpoint `(F₁.extend 1).next b₁`. It needs one parity
  fact: the midpoint is in `F₁.extend 1 ⊆ C(F₂)`, so it is `F₂`-even and an
  inexact RTO result never lands on it (§S1).

Prototype on RTO → RN first.

**What it replaces.**

* `Propagation.lean`: `abs_lt_next_of_toZero_inbound`, `toZero_noOverflow_F₂`,
  `toZero_noOverflow_chain`, `toOdd_abs_le_of_awayZero`,
  `toOdd_toZero_noOverflow_chain`, `abs_lt_next_of_toOdd_inbound`,
  `toOdd_toOdd_noOverflow_chain`, `boundOK_of_abs_lt_next`,
  `toZero_noOverflow_direct`, `next_mem_of_*_subset`, `toOdd_awayZero_candidate`,
  `toOdd_toOdd_noOverflow_direct`. About 460 lines, replaced by about 70.
* `Total.lean`: the per-rule bodies; the four copies of the
  `suffices key` + `bound_floor_setup` + `rounds_floor_lift` block; the eight
  copies of the `set G; hsubG := …` step; the in-bound blocks for `F₂`.
* Possibly the grid-floor machinery itself (`bound_floor_setup`,
  `rounds_floor_lift`, `not_overflows_of_floor`, the `hreg` arguments, about
  320 lines). Only RN needs `b₁` on the grid; the other rules need only some
  grid point `N` with `b₁ < N ≤ Format.next b₁` (`next b₁` on the grid,
  `rndUp b₁` off it).
* Most of `Rounding/Restrict.lean`, which becomes one locality lemma.

**Check before relying on it.** The `hnt` (`Nontrivial`) hypotheses on the
`_noOverflow` forms may become unnecessary: at `exp = ⊥` and `b₁ = 0`,
`boundAfterNext = 1` forces `F₂.exp = ⊥`. Low confidence.

**Even without the generic theorem:**

* [ ] The two in-bound pin lemmas (`abs_lt_next_of_toZero_inbound`,
  `abs_lt_next_of_toOdd_inbound`) are six lines each: if `N ≤ |x|` then
  `le_abs_faithful_of_le` gives `N ≤ |y|`, contradicting `|y| ≤ b₁ < N`. This
  is already inlined in `toOdd_toOdd_noOverflow_direct`. About 55 lines.
* [ ] `eq_zero_of_toZero_zero` is subsumed by `eq_zero_of_faithful_zero`
  applied to `hy.isFaithfulRound`. The degenerate branch of
  `bound_floor_setup` is the same fact for RTN. The "`ofIntZpow 1 K ∈
  F.unbounded` when `exp = ⊥`" block appears three times here and again in
  `Next.lean` (`bound_top_of_withBound_top_subset`). `rounds_total_of_zero_bound`'s
  `hzero₁`/`hzero₂` parameters are always the same generic facts and can go.
  About 70 lines.
* [ ] The six `_inBound` theorems share one body. One `inBound_of` lemma
  taking the `F₂` and chain facts plus the `_agree` rule leaves each at about
  three lines. About 110 lines.
* [ ] `abs_le_mid_of_nearest_inbound` and `nearest_boundOK_of_abs_lt_mid`
  each write out `x ≥ 0` and `x < 0` in full. Reduce to `x ≥ 0` with
  `RoundsFinite.neg_nearest` and `FiniteFormat.neg_mem`, as `rndNeg` in
  `NearestMidpoint.lean` already does. About 90 lines.

### S3. One successor and a uniform `canonicalExp` API

Several hundred lines. Low risk. Unblocks §S1 and §S2.

About 105 `recBotCoe`/`recTopCoe` case splits sit in `Format/`, concentrated in
`Next.lean` (35), `Digits.lean` (19), `Containment.lean` (19), `Defs.lean` (17)
and `CanonicalExp.lean` (14). The cause: `canonicalExp`, `numDigits` and
`Format.next` are each defined by a four-arm match with no characterising
lemma, and the import order (`CanonicalExp` after `Discrete`, `Next` not
importing `CanonicalExp`) hides the generic lemmas that do exist, so files
re-unfold the definitions.

* [ ] Move the pure `canonicalExp` algebra (`canonicalExp_eq_of_log_eq`,
  `_neg`, `_closed`) to `Format/Defs.lean` or an early file.
* [ ] Add `canonicalExp_le_iff (hx : x ≠ 0) : F.canonicalExp x ≤ k ↔ (∀ p,
  F.p = p → log|x| + 1 − p ≤ k) ∧ (∀ e, F.exp = e → e ≤ k)`.
  `canonicalExp_mono`, `isAboveQuantum_of_exp_le`,
  `canonicalExp_binade_below_le` and the inline bounds in `Discrete.lean` and
  `Next.lean` become one-liners.
* [ ] Generalise `extend_one_canonicalExp` to `(F.extend k).canonicalExp x =
  F.canonicalExp x − k`.
* [ ] Define `numDigits x := if x = 0 then 0 else Int.log 2 |x| + 1 −
  F.canonicalExp x`. Checked equal to the current definition in all three
  branches. This removes `numDigits_top_coe`/`_coe_bot`/`_coe_coe`,
  `numDigits_neg`, `numDigits_congr`, `numDigits_extend` (40 lines to 2),
  `numDigits_le_one_of_p_one` and `numDigits_nonneg`. About 250 lines.
* [ ] One generic representation lemma: `z ∈ F.unbounded → ∃ m, z = m ·
  2^cexp z`, with the converse "`m · 2^k` with `k ≥ cexp z` is in
  `F.unbounded`". It replaces `Next.exists_step_rep(_le)` and
  `Discrete.exists_canonical_rep_of_parts` with its private helpers
  `canonical_rep_reconstruct` and `log_le_of_canonical_rep`. The `|m| < 2^p`
  bound comes from `floor_mantissa_lt`. About 120 lines.
* [ ] Keep one successor. Three exist: `Format.next` (four-arm match with junk
  arms), `FiniteFormat.next` (via `canonicalExp`) and `Ulp.succ` (real-valued),
  bridged by `next_eq_format_next` and `next_coe`. Define `boundAfterNext` from
  the one kept. At minimum add `next_zero (he : F.exp = e) : F.next 0 =
  ofIntZpow 1 e` beside `next_pos_eq`; `lt_next` and `next_mono` (68 lines,
  five-way split) then follow from `canonicalExp_mono`. Removes the
  `lt_next_of_*` and `next_eq_bot_*` families and four inline re-derivations of
  the `b ≤ 0` reduction. About 200 lines.
* [ ] `two_le_p_or_trivial_of_extend_one_withBound_subset` (170 lines) builds
  a `3 · 2^k` witness in each of eight cases. Generic witness: a positive
  `d ∈ F₁`, and `m = (F₁.extend 1).next d = (d + next d)/2`
  (`next_extend_midpoint'`), which is in the extended grid, at most
  `next b`, and has odd significand, so `¬ precisionAtMost 1`. About 130
  lines.
* [ ] Grid discreteness is proved four times: `Discrete.adjacent_canonical_form`
  (needs finite `p`), `Next.next_min'`, `Ulp.succ_le_of_lt`, and
  `Cex.exists_isolated` with `Cex.Adjacent`. Make one canonical; the
  `Cex.exists_isolated` form needs no shape split.
* [ ] `floor_minimality` repeats "`z = k · 2^e`, `z ≤ x` implies `k ≤ ⌊x ·
  2^-e⌋`" three times. Generically: if `cexp z ≥ e` then `z` is a multiple of
  `2^e`, else `|z| < 2^log|x|`, which is on the grid. This removes
  `binade_le_floor` and `abs_lt_two_pow_log_of_precision` (`Utils.lean`, about
  90 lines). `ceil_minimality` re-proves `canonicalExp_neg`,
  `precisionAtMost_neg` and `quantumAtLeast_neg`; three lines instead. About
  150 lines.
* [ ] `Discrete.lean`'s midpoint lemmas (`half_mem_extend_one`,
  `midpoint_mem_extend_one_of_p_top`, the quantum part of
  `midpoint_mem_extend_one_of_adjacent_pos`, the dispatch in
  `midpoint_in_F₁_extend_one_of_F_adjacent`) re-split on `exp` and sign. With
  the generalised `extend` lemma and the converse above, the midpoint
  `(2c + 1) · 2^(k−1)` lands in `F.extend 1` without splitting. About 100
  lines.
* [ ] "No multiple of `2^f` lies strictly between `t · 2^f` and `(t + 1) ·
  2^f`" is proved five times: `quantum_floor_of_mem`, `quantum_ceil_of_mem`
  (floor under negation), `ulp_interval_squeeze_absurd`, `next_ulp_min`, and
  inline in `floor_minimality`. One `Int` lemma. About 50 lines.

### S4. Modes as selections between round-down and round-up

About 1k lines in `Rounding/`. Medium churn.

`RoundsFinite` lists each mode separately, so `neg_*`, `restrict`/`lift`,
`unique_*`, `monotone_*` and `eq_of_mem` are each proved per mode, with both
sign directions written as mirrored copies. `FiniteFormat`'s two invariants
are exactly "every real has a floor and a ceiling in the grid", so it is the
natural tier; every mode is then "`x` if representable, else a choice between
`rndDown x` and `rndUp x`".

**Low-risk entry points:**

* [ ] Add `IsRoundDown`/`IsRoundUp` defs and use them in the `.toNegative`/
  `.toPositive` clauses of `RoundsFinite` and in `IsFaithfulRound := IsRoundDown
  ∨ IsRoundUp`. `isFaithfulRound_iff_directed` is already definitional (its
  proof is the identity); its 30 uses become no-ops.
* [ ] `IsFaithfulRound.eq_or_eq (hd : round-down x d) (hu : round-up x u) :
  IsFaithfulRound x y → y = d ∨ y = u`, three lines via
  `unique_toNegative`/`unique_toPositive`. It replaces `opposite_sides_of_ne`,
  `faithful_eq_of_third` (Restrict), `h_faithful_eq` in
  `nearest_neighbors_setup` (Op/Nearest) and `hfaith` in
  `Cex.roundsRNE_of_bracket`. About 35 lines.
* [ ] `eq_of_mem` (35 lines, a case per mode), `eq_of_abs_eq_of_mul_nonneg`
  and `toOdd_unique_of_mem` all follow from `IsFaithfulRound F d y → d ∈ F →
  y = d` applied to `h.isFaithfulRound`. Needs `isFaithfulRound` moved above
  `eq_of_mem`; nothing blocks that. About 45 lines.

**Sign symmetry (about 140 lines in `Rounding/Basic.lean`):**

* [ ] Add `FiniteFormat.forall_mem_neg : (∀ z ∈ F, P z) ↔ ∀ z ∈ F, P (-z)`
  (`rw`, not `simp`: it loops) with an `∃` twin, and `RoundingMode.neg`
  swapping RTN and RTP. Prove one `RoundsFinite.neg_iff : RoundsFinite F rm x y
  ↔ RoundsFinite F rm.neg (-x) (-y)`. It replaces `IsFaithfulRound.neg_iff`,
  `neg_toZero`, `neg_toNegative_iff_toPositive`, `neg_awayZero`,
  `neg_nearest_awayZero`, `neg_toOdd`, `neg_nearest_toEven`; keep
  `neg_awayZero`, `neg_toZero`, `neg_toOdd`, `neg_nearest` as one-line aliases
  for their 18 external call sites. Fallback: prove one direction of each and
  get the other at `-x, -y` by `neg_neg`, which halves every proof.
* [ ] `toPositive_iff_awayZero_of_nonneg` (50 lines) and
  `toPositive_iff_toZero_of_nonpos` (68 lines) each re-handle `x = 0` with
  manual `abs` algebra. After `eq_of_mem`, `eq_zero_of_zero` disposes of it
  once. About 50 lines.

**Construction (`Op/`, about 400 lines):**

* [ ] Build `rndUnbounded` by pattern match on all seven modes as a choice
  between `d := ofIntZpow ⌊s⌋ e` and `u := ofIntZpow ⌈s⌉ e`. Today it
  dispatches through `if h : rm = .toOdd`, and the same
  `unfold rndUnbounded; rw [dif_neg …, dif_neg …]` appears 14 times across
  `Directed`, `Nearest`, `ToOdd` and `Ulp.nearest_eq_of_close`. `rndInt` and
  `rndParity` lose their unreachable fallback arms. Define `rndDown`/`rndUp` as
  those grid points, so `rndDown_eq` is `rfl` and `rndDown_spec :=
  toNegative_floor`.
* [ ] `Op/Directed.lean`: the four 20-line sign-bridge lemmas become
  `simp [rndUnbounded, rndInt, hx]`. About 150 lines to 30.
* [ ] `Op/ToOdd.lean` rebuilds membership and the round-down/round-up specs
  that `RoundsFinite.toNegative_floor` and `toPositive_ceil` give; the parity
  step is `alternate_of_bracketing`. About 133 lines to 40.
* [ ] `Op/Nearest.lean`: generalise `Cex.roundsRNE_of_bracket` to take
  round-down/round-up specs instead of `Cex.Adjacent`, add an `awayZero`
  sibling, and move both to `Rounding/Basic.lean`. The six hand-assembled
  `refine ⟨h_dlo_mem, …⟩` blocks then collapse; the `awayZero` tie arguments
  are `abs_le_abs` from `dlo + dhi = 2x`. About 381 lines to 120.
* [ ] "Ceiling = floor + 1 off the grid" is proved four times (in
  `alternate_of_bracketing`, `Op/ToOdd`, `Op/Nearest`, `Ulp.rndUp_eq`). Mathlib
  has `Int.ceil_eq_floor_add_one_iff_notMem`. `toPositive_ceil` mirrors
  `toNegative_floor` and can be derived from it via `Int.floor_neg` and
  `canonicalExp_neg`. About 20 lines.

**Spec changes (check the paper's wording first):**

* [ ] One tie-break-uniform nearest clause: `∀ z ∈ F, faithful z → z ≠ y →
  |x − y| = |x − z| → tb.Prefers F y z`. The `.toEven` and `.awayZero` clauses
  are the same shape after currying. This removes `cases tb` duplication from
  `eq_of_mem`, the nearest `neg_*`, `unique_nearest`, `nearest_min`,
  `nearest_restrict`/`nearest_lift`, `nearest_error_le_half_ulp`,
  `nearest_eq_of_close` and `DoubleRounding/Nearest.lean`. About 120 lines.
* [ ] One generic `RoundsFinite.restrict`/`lift` by `cases rm`, replacing
  `toZero_restrict`, `awayZero_restrict`, `toOdd_restrict`, `nearest_restrict`
  and the lifts. It lets `Total.lean`'s `_agree` lemmas and `eq_of_inBound`
  drop two parameters each. `IsFaithfulRound.unbounded_lift` and
  `nearest_close_upgrade` have mirror halves derivable by negation. About 35
  lines in `Restrict.lean`, more downstream.

**Larger version (high churn).** Make rounding a function `sel_rm(x, down x,
up x)` with `RoundsFinite` characterisations as theorems. Per-mode uniqueness
disappears, `neg_*` and `monotone_*` become one lemma each, and the directed
double-rounding rules become `⌊⌊x⌋₂⌋₁ = ⌊x⌋₁` for any `V₁ ⊆ V₂` plus sign
reduction. It loses the bounded-`F` reading of `RoundsFinite` (RTZ saturates,
RAZ is partial past `b`), which is neither the paper's semantics nor the
unbounded one and exists only as a proof device. Entry point: a single
`RoundsFinite.iff_select` theorem, then migrate gradually.

### S5. `ParityFormat`, `IsUndefined` and `.undefined`

Low proof risk. Dropping `.undefined` needs a paper decision.

`ParityFormat.parity` is used in three places, all in `Digits.lean` (via
`nondegenerate`). The two uses on `F₂` are implied by `2 ≤ F₂.p` and
`FiniteFormat.finite`; the `F₁` use in `odd_index_of_p_one_corner` is
derivable. `IsOdd` already computes something at `(1, ⊥)` (exponent parity
through `unbotD 0`), and it alternates. `(1, ⊥)` is only special in that no
2-colouring is invariant under doubling, which no theorem uses.

* [ ] Define `IsOdd`/`IsEven` on `Format` from `(p, exp)` only. Remove the
  `∃ F' : ParityFormat, F'.toFormat = F.toFormat ∧ …` wrappers in the
  `RoundsFinite` spec (10 sites), `parity_witness_congr`,
  `IsOdd_iff_of_toFormat_eq`, and the separate `toParityFormatOfToOdd`/
  `toParityFormatOfNearestEven` (the same value twice). Nearly free alongside
  §S1.
* [ ] Paper decision: whether `rnd` stays `.undefined` at `(1, ⊥)` with
  RTO/RNE. If not, `rnd` returns `WithSpecial Dyadic` directly and about 190
  `IsUndefined`/`.undefined` hits go, including `h₁u` on RNA statements, where
  RNA is never undefined. If it stays, keep `IsUndefined` as a documented
  predicate but still drop the `ParityFormat` structure and the existential
  witnesses. Either way the counterexamples can stay on the current class.
* [ ] Smaller: the four `not_isUndefined_{toZero,awayZero,toNegative,toPositive}`
  are identical one-liners and could be one lemma.

### Not worth doing now

* **`Dyadic` over ℝ instead of ℚ.** The cast cost is real (53
  `coe_real_eq_ratCast`, 67 `ext_real`/`coe_real_inj`, about 500 cast-tactic
  lines), and the decidability it buys is used only for the overflow sign. But
  it touches every file and gives up the computable `rndQ` option in
  `TODO.md`. Revisit only if that option is abandoned.
* **Containment's characterisation.** The two rules are already the natural
  one ("`F₁`'s effective precision is at most `p₂`"). Only expose `extend k`
  and `C^k` as inverse shifts for §S1.
* **Roux files** (`Add`, `Div`, `Sqrt`, `Mul`, `NearestMidpoint`, about 2.4k
  lines). Mostly genuine `zpow`/floor arithmetic; see §R for the removable
  part.
* **`Counterexample/`.** Already in the generic style.
* **`HasPositive` via `encard`.** Cosmetic.

## Double-rounding rules

* [ ] Rebase the directed rules on RTN → RTN and RTP → RTP. RTN → RTN is a
  four-line direct proof (`w ≤ z ≤ x`, and any `v ∈ F₁ ⊆ F₂` with `v ≤ x` has
  `v ≤ z`, hence `v ≤ w`). RTZ → RTZ and RAZ → RAZ then follow in about ten
  lines each from the sign bridges (`toNegative_iff_toZero_of_nonneg`, …),
  replacing `roundsRTZ_RTZ_finite` and `roundsRAZ_RAZ_finite(_pos)`. Today the
  derivation runs the other way: `roundsRTP_RTP_finite` and
  `roundsRTN_RTN_finite`, which nothing uses, are derived from them. About 155
  lines.
* [ ] Prove RTO → RTN and RTO → RTP once, without sign cases, and derive
  RTO → RTZ and RTO → RAZ from them. If `z ≤ x`, `z` is the `F₂` round-down and
  maximality transfers. If `x < z`, `z` is the `F₂` round-up and `z ∉ F₁` by
  `toOdd_notMem_of_extend_subset`; `x < w` would force `w = z ∈ F₁`. This
  replaces `roundsRTO_RTZ_finite_pos` + `_of_extend` and
  `roundsRTO_RAZ_finite_pos` + `_of_extend` (about 200 lines, each a mirrored
  positive/negative/zero split), and **closes the ROADMAP item "Round-to-odd
  into RTP and RTN"**. About 140 lines saved.
* [ ] `roundsRTO_RTO_finite` derives `¬ F₁.IsUndefined .toOdd` through
  `numDigits` (about 28 lines). Every caller already has it; take it as a
  hypothesis. This weakens a README-listed theorem only to what its `rnd` form
  already assumes.
* [ ] Factor `IsFaithfulRound.trans_of_ne`: if `z` is faithful for `x` in
  `F₂ ⊇ F₁`, `w` is faithful for `z` in `F₁`, and `w ≠ z`, then `w` is faithful
  for `x` in `F₁`. It is proved twice, as the `z ≠ w'` four-way split in
  `roundsRTO_RTO_finite` and as `h_adj_x` in `rndRTO_nearest_facts`. The
  `z = w'` branch is a generic `IsFaithfulRound.of_subset`, of which
  `Restrict`'s private `IsFaithfulRound.restrict` is an instance. About 40
  lines.
* [ ] `DoubleRounding/Nearest.lean`:
  * `rndRTO_RN_close_transfer` (215 lines) is two mirrored branches; one half
    plus a swap, or `RoundsFinite.neg_nearest`, halves it.
  * In `rndRTO_no_tie_contradiction`, `h_F_adj_pair` (48 lines) re-derives
    what two calls to `F_adjacent_of_RN_round_pair` give.
  * `roundsRTO_RN_finite_of_extend` has two identical `cases tb` branches;
    extract faithfulness and minimality before splitting.

  About 150 lines in total.
* [ ] `DoubleRounding/Special.lean`: every `rndX_Y` and `rndX_Y_of_bound` is
  `rnd_double` (or `.of_bound`) applied to existing lemmas, and six to eight of
  each theorem's twelve to fourteen lines are repeated binders. A `section` with
  `variable` binders saves about 60 lines and keeps the names. Stronger:
  bundle each rule as a `DoubleRule F₁ F₂ rm₁ rm₂` structure (`h₁u`, `agree`)
  and a `RelaxedRule` (adding the in-bound and no-overflow facts), and prove the
  `rnd` lifts once.

## R. Roux per-operation files

About 300 lines, mostly medium confidence.

* [ ] `Add.lean`: `rndAdd_pos` and `rndSub_pos` are the same three-way
  dispatcher (small gap exact, subnormal exact, normal to midpoint);
  `sum_precisionAtMost` and `diff_precisionAtMost` differ only in the sign of
  `cy`; `rndAdd_pos_normal` and `rndSub_pos_normal` repeat about 45 lines of
  setup. Both contain a dead `by_cases hgapc … exact absurd`, `hcE1r` is
  computed twice in `rndSub_pos_normal`, and several `hlog*` derivations
  should be `log_eq_of_zpow_bounds`. About 120 lines.
* [ ] `Mul.lean`: `mul_mem_F₂_unbounded` already takes `F₂.exp ≤ F₁.exp +
  F₁.exp`, so `rndMul_expBot` and `rndMul_expFinite` are two instantiations of
  one theorem, as in `Add.lean`. About 20 lines.
* [ ] `Sqrt.lean`: `rndSqrt_expBot` and `_expFinite` share about 15 lines of
  setup. About 40 lines.
* [ ] `Div.lean`: `rndDiv_pos` and `rndDiv_pos_normal_expFinite` are nearly
  identical given `log_sub_p_le_canonicalExp` and an upper bound on `cexp₂`;
  the sliver case in `rndDiv_pos_expFinite` recomputes `hca_lo`, `hcb_lo`,
  `hlogpair`, `hab`. About 50 lines.
* [ ] "`rndDown F x + ulp F x ≤ 2^(log x + 1)` when `cexp x ≤ log x + 1`" is
  proved in `NearestMidpoint.canonicalExp_eq_of_lt_mid` and in
  `Sqrt.round_round_sqrt_aux`; move it to `Ulp.lean`. `rnd_gt_mid` redoes
  `rndNeg` inline. About 30 lines.

## U. Unused API (decision needed)

Each block below is referenced only inside its own file (checked by grep over
`Mpfx/` and `MpfxTest/`).

* [x] **`Rounding/Ulp.lean`, succ/pred (about 610 lines):** `predPos`, `succ`,
  `pred`, `succ_le_of_lt(_pos)`, `pred_mem`, `binade_walls`, `succ_predPos`,
  `predPos_succ`, `succ_pred`, `pred_succ`, `le_pred_of_lt`,
  `rndDown_eq_of_bracket`, `rndUp_eq_of_bracket`, `midp_eq_midpoint_succ`,
  `nearest_le_of_lt_midp`, `le_nearest_of_midp_lt`, `next_coe`, `next_mem`,
  `succ_mem`, `succ_eq_of_adjacent`.
* [x] **`Rounding/Ulp.lean`, ulp under rounding (about 125 lines):**
  `canonicalExp_rndDown`, `ulp_rndDown`, `faithful_error_lt_ulp`,
  `ulp_rndUp_pos`, `ulp_round_pos`, `canonicalExp_le_of_faithful_pos`,
  `ulp_le_ulp_of_faithful`, `nearest_error_le_half_ulp_round`.
  `canonicalExp_rndDown` and `ulp_rndUp_pos` are the binade facts a generic
  alternation proof (§S1, intermediate option) would use.
* [x] **`Rounding/Basic.lean` and `Defs.lean`, the `Rounds` sign layer (about
  150 lines):** `Rounds.neg_congr`, the six `Rounds.neg_*`,
  `Rounds.congr_of_roundsFinite`, the four `Rounds.to*_iff_*`, the private
  `decide_neg_lt_zero`; and, used only by them, `RoundResult.neg` with its simp
  lemmas and `OverflowMap.neg`/`neg_map`.
* [x] **`Rounding/Basic.lean`, monotonicity (about 130 lines):**
  `monotone_toNegative` through `RoundsFinite.monotone`. Keep `nearest_min`,
  which `Propagation.lean` uses.

All four were deleted, with `Format.neg_mem_values` (used only by
`OverflowMap.neg`); they are recoverable from commit `2293cbc`. The note below
records the alternative that was not taken.

The Ulp and monotonicity blocks are deliberate Flocq-parity API
(`FLOCQ_ROADMAP.md` §4, `ULP_TODO.md`). Options: delete; move to an API-only
file; or keep them and drop their `hp : F.p = (p : Prec)` hypotheses. The last
is about 50 lines of change: `succ_le_of_lt_pos` is three lines from
`next_coe`, `next_eq_format_next` and `next_min'` (no `hp`); `next_mem`
duplicates `next_mem_unbounded'`; and every remaining `hp` comes from
`exists_canonical_rep` (use `exists_step_rep`), `canonicalExp_binade_below_le`
(its `p = ⊤` case is `exp_le_log_of_mem`), or explicit `unfold canonicalExp`
computations whose coefficient bounds are vacuous at `p = ⊤`.

## Q. Quick wins

High confidence, low risk, independent of the structural work.

**Format layer**

* [x] `Inference.lean`: `add_inferred_q` is `quantumAtLeast_add
  (quantumAtLeast_anti min_le_left hqx) (quantumAtLeast_anti min_le_right
  hqy)`; the quantum half of `mul_inferred_pq` is `Dyadic.quantumAtLeast_mul`;
  the precision half duplicates the private `mul_precisionAtMost` in
  `DoubleRounding/Mul.lean`. Add `Dyadic.precisionAtMost_mul` and use it in
  both. About 70 lines.
* [x] "`y = c · 2^e ≠ 0` implies `e ≤ ⌊log₂|y|⌋`" is proved four times:
  `Digits.quantum_exp_le_log` (private), the inlined `e'_le_e_y` in the same
  file, `CanonicalExp.exp_le_log_of_mem`, and `Dyadic.abs_ge_two_zpow_of_quantum`.
  Keep one `Dyadic.le_log_of_quantum`. About 50 lines.
* [x] "`c · 2^k` has quantum at least `e` when `e ≤ k`" is re-proved inline in
  `ofIntZpow_mem_unbounded`, `Next.lean` (twice), `Digits.lean`,
  `Discrete.lean` (twice) and the body of `quantumAtLeast_anti`. Add
  `Dyadic.quantumAtLeast_ofIntZpow`, and make `ofIntZpow_mem_unbounded` a thin
  wrapper of `Format.ofIntZpow_mem`. Three membership constructors overlap:
  `Format.ofIntZpow_mem`, `ofIntZpow_mem_unbounded`, `Format.mem_unbounded_of_le`.
  About 80 lines.
* [x] `Utils.lean`: `two_zpow_split_toNat`, `two_zpow_diff_eq`,
  `two_zpow_split`, `two_zpow_shift_real`/`_rat`, `coeff_eq_of_shift_real`/`_rat`
  exist as ℚ and ℝ twins, with further inline copies in `IsDyadic.add_aux`,
  `quantumAtLeast_anti`, `IsRepresentableAtP.unique`, `CanonicalExp.lean`,
  `Next.lean` and `Inference.lean`. State them once over any `DivisionRing`.
  About 70 lines.
* [x] `Dyadic.lean`: `IsRepresentableAtP.unique` (83 lines) is about 25 via
  `log_eq_of_zpow_bounds`; `Int.exists_odd_factor(_aux)` is Mathlib
  `Nat.exists_eq_two_pow_mul_odd` on `c.natAbs`; `precisionAtMost_of_abs_le`
  has mirror sign branches. `ParityFormat.IsOdd.ne_zero` and the `y = 0`
  branch of `isEven_iff_even_of_canonical` are `IsRepresentableAtP.ne_zero`.
  About 110 lines.
* [~] Bridging boilerplate (34 `change |…| ≤ …`, 39 `change
  Dyadic.precisionAtMost/quantumAtLeast/boundOK …`, about 15
  `rw [coe_real_eq_ratCast, …, ← Rat.cast_abs]; exact_mod_cast`):
  * make `boundOK_coe_iff_real : boundOK (b : Bound) d ↔ |(d : ℝ)| ≤ (b.val :
    ℝ)` one `Iff` (today two lemmas);
  * add simp `Format.mem_def : d ∈ F ↔ precisionAtMost F.p d ∧ quantumAtLeast
    F.exp d ∧ boundOK F.b d := Iff.rfl` and a ℚ-form `boundOK_coe_iff`;
  * add `Format.extend_p`/`extend_exp_coe` evaluators (the `change F.exp.map
    (· - ((1 : ℕ) : ℤ)) = _; rw [h]; rfl` step appears about eight times);
  * add a norm_cast `Dyadic.coe_real_ne_zero_iff`;
  * use `nonneg_coe_real` instead of re-deriving it.

  About 120 lines. Done in part: `exact_mod_cast` bridges Dyadic→ℝ casts by
  itself, so 27 `rw [Dyadic.coe_real_eq_ratCast, …, ← Rat.cast_abs]` steps were
  dropped, and `extend_p`/`extend_exp_coe`/`extend_exp_bot` were added. The
  `mem_def` and `boundOK` iff sweep over the `change` lines remains.
* [ ] `Format/Parity.lean`: `IsOdd`/`IsEven` lemmas are duplicated pairwise.
  Factor through an index `idx F c e := if F.p = 1 then e − exp.unbotD 0 + 1
  else c` and a private witness predicate, and prove `neg` once for any
  sign-invariant predicate. `IsOdd_iff_of_toFormat_eq` is a corollary of
  `IsOdd.congr`. About 90 lines. Superseded by §S1 if that lands.
* [x] `Format.extend_extend : (F.extend j).extend k = F.extend (j + k)`
  replaces the hand proofs in `extend_one_extend_one_subset_extend_two`,
  `extend_one_extend_one_p_exp` and `extend_one_extend_one_withBound_subset`.
  About 45 lines.
* [x] `Next.bound_top_of_withBound_top_subset` (43 lines) duplicates the top
  branch of `Containment.b_le_of_subset`; make `exists_zpow_gt` public. About
  30 lines.
* [x] Small: `log_abs_mul_zpow` (`Parity/Alternate.lean`, 28 lines) is five via
  `log_eq_of_zpow_bounds`, and belongs in `Utils.lean`. The private
  `one_lt_two_pow` in `Containment.lean` duplicates `abs_one_lt_two_pow` and
  Mathlib's `one_lt_two_pow`. `Format.zero_mem` re-proves `boundOK_zero`
  inline.

**Rounding layer**

* [ ] `Rounding/Parity.lean` (only if §S1 is deferred): `alternate_normal_p1`
  re-proves `canonicalExp_closed`, `two_pow_pred_le_scaled`,
  `abs_floor_ge_two_pow_pred` and `abs_floor_add_one_ge_two_pow_pred`, which
  `alternate_normal_pne1` already uses at any `p`; `alternate_expBot` repeats
  the setup. Factor one lemma giving `2^(p−1) ≤ |lo|, |lo + 1| ≤ 2^p` from
  `e = log|x| + 1 − p`. In `alternate_subnormal_pne1`, `h_x_lt`/`h_s_lt` is
  `floor_mantissa_lt hp_F`. `neighbors_alternate` restates the private
  `Alternate` verbatim; `toOdd_neighbors_alternate` and
  `nearest_toEven_neighbors_alternate` go once callers use
  `alternate_of_bracketing`. About 250 lines.
* [x] `nearest_error_le_half_ulp` re-derives `nearest_min` by `cases tb` and
  rebuilds faithfulness that `(rndDown_spec F x).isFaithfulRound` gives.
  `maxFinite_nonneg` is `RoundsFinite.toNegative_nonneg`, and `maxFinite` is
  `rndDown F b`. About 15 lines.

**Double-rounding layer**

* [~] `Propagation.nearest_components` is `⟨h.1, h.isFaithfulRound,
  nearest_min⟩`; `Nearest.midpoint_F₁_in_F₂_of_F_adjacent` is a one-line
  wrapper; `cases tb₂ <;> exact hz.2.1` in `NearestMidpoint` is
  `hz.isFaithfulRound`; paired `rndUnbounded_unique` rewrites in
  `Propagation`, `NearestMidpoint` and `Add` are `RoundsFinite.unique`. About
  20 lines. Done except the two wrappers, kept: each has four or five callers
  that would otherwise repeat the expansion.

**Dead code**

* [~] `Utils.nonneg_of_mul_nonneg_pos`, `Utils.two_zpow_split_minus_two`,
  `Format.mem_congr`, `Format.neg_subset_finite`, `Format.abs_subset_finite`
  (unused since the last PR). Done except `neg_subset_finite`/`abs_subset_finite`,
  kept as the README's paper-facing finite forms, and `coe_abs`/`coe_rat_abs`,
  kept as the coercion API of `Dyadic.abs`. `Dyadic.coe_abs`/`coe_rat_abs` are simp-tagged
  but `Dyadic.abs` is only ever unfolded; consider Mathlib's `|·|` on the
  subring. `Dyadic.isRepresentableAtP_of_bounds` is a bare constructor wrapper
  with one use. About 45 lines.
