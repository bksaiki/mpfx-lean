# Autoformalization TODO — *When Double Rounding is Correct*

Paper reference: `When_Double_Rounding_is_Correct.pdf`.

A Lean 4 / Mathlib formalization of Appendix A: format containment (§5.1),
correct double rounding (§5.2, with counterexamples for the invalid mode
pairings), and format inference (§6.1). Three design decisions shape the
development:

1. **Looser top-level type, layered subtypes.** `Format` encodes only
   the natural type-level constraints (`p : Prec = WithTop ℕ`, where `p = 0`
   is the trivial format `{0}`; `b ≥ 0` via `WithTop NonNegDyadic`).
   `FiniteFormat extends Format` rules out `(p = ⊤, exp = ⊥)` and `p = 0`;
   `ParityFormat extends FiniteFormat` additionally
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
Completed work is pruned from this file; see `README.md` for what is formalized
and `docs/DESIGN.md` for how it is put together.

## File layout

```
Mpfx/
├── Utils.lean      project-agnostic helpers (two_zpow_pos, etc.) and the
│                   format-free scaled-mantissa arithmetic
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
│                   IsFaithfulRound, RoundsFinite, Rounds,
│                   FiniteFormat.toParityFormatOf{ToOdd,NearestEven}.
│                   Sign-symmetry block: IsFaithfulRound.neg_iff,
│                   per-mode RoundsFinite.neg_*, Rounds.neg_*.
│                   Mode-vs-sign block: RTP/RTN ↔ RTZ/RAZ by sign of x.
├── RoundPred.lean  relational consequences of the spec: uniqueness per mode
│                   and generic, isFaithfulRound, eq_zero_of_zero,
│                   opposite_sides_of_ne, the grid bridges
│                   toNegative_floor/toPositive_ceil (+ equation forms),
│                   isOdd_alternate_of_bracketing, monotonicity per mode
│                   and generic. Mentions no construction.
├── Parity.lean     neighbors_alternate: adjacent grid points alternate in
│                   parity; the toOdd and nearest .toEven forms
├── RoundOp.lean    function layer (noncomputable, classical):
│                   rndInt, rndParity, rndUnbounded, rnd, per-mode soundness,
│                   rndUnbounded_satisfies/_unique, rnd_iff_rounds
├── Containment.lean §5.1 / Fig. 8: Format.Subset + HasSubset,
│                   boundOK_mono, nnPow, containsPrec, containsSub,
│                   Format.extend + self_subset_extend + extend_mono,
│                   FiniteFormat.extend + numDigits_extend (Lemma 5.2),
│                   withBound + next (+ next lemmas) — §5.2 bound API
├── Ulp.lean        ulp/rndDown/rndUp/midp, the nearest error bound and the
│                   below/above-midpoint characterisations, succ/pred/predPos
│                   and their membership + adjacency lemmas
├── Discrete.lean   canonical representation / adjacency / midpoint-membership
│                   (prereq for rndRTO_RN): log_le_of_canonical_rep,
│                   exists_canonical_rep(_of_parts), canonical_rep_pos,
│                   not_mem_between_adjacent, adjacent_canonical_form,
│                   midpoint_mem_extend_one_of_adjacent(_pos/_of_p_top),
│                   half_mem_extend_one. Built over the ℚ substrate.
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

## Open: Rounding API extensions

- [x] **Generalise `gap_around_m_mem` / `gap_around_mid3_mem`**
      (`DoubleRoundingCex.lean`, −118 lines). Both are now `simpa` wrappers over
      `gap_around_odd_mem`, stated for odd `c` with `2^j < c < 2^(j+1)`; `j`
      fixes the binade, so the bracketing powers stop being constants.

- [ ] **Move `nearest_neighbors_setup` out of `RoundOp/`.** It is
      construction-free and now slim, but still sits under the function layer.
      Its only consumer is `rndUnbounded_satisfies_nearest`, so inlining may
      beat relocating.

- [ ] `IsFaithfulRound`-extraction lemmas (split RTN-witness vs
      RTP-witness disjunct accessors).

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

- [ ] **Optional `Coe FiniteFormat Format` instance** — would let `⊆`/
      `withBound`/`boundAfterNext` drop their explicit `.toFormat` too. Add
      only if that noise becomes overwhelming.
- [ ] **Per-file module docstrings** + paper-reference cross-links (`README`
      is done; individual file headers could still gain `§`-references).
- (Considered, not done: merging the Grid `_exp_bot`/`_of_p_top` twin lemmas
  under a unified `k` form — the twin structure with the dispatcher in
  `midpoint_F₁_in_F₂_of_F_adjacent` is clearer; deferred.)
- (Considered, not done: de-`change`-ing `RoundOp.lean` — its ~60 `change`s
  are legitimate definitional unfolds of `canonicalExp`/`rndInt`/arithmetic,
  not the `.toFormat` pattern; removing them needs per-def unfold lemmas with
  no real payoff. Splitting `RoundOp.lean` (~4000 lines) is a mechanical reorg
  with no correctness benefit — deferred unless it causes friction.)

## Open: substrate ergonomics (low-priority)

User-facing wrappers around the format-parameterized primitives, useful for
smoke tests and external use:

- [ ] Public `Dyadic.precision : Dyadic → Prec` (currently approximated
      by `numDigits`, which is format-parameterized).
- [ ] Public `Dyadic.quantum : Dyadic → QExp`.
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
