# Autoformalization TODO — *When Double Rounding is Correct*

Plan reference: `~/.claude/plans/i-d-like-to-autoformalize-warm-kurzweil.md`
Paper reference: `When_Double_Rounding_is_Correct.pdf` (Appendix A holds the proofs).

Status legend: `[ ]` not started · `[~]` in progress · `[x]` done · `[!]` blocked.

## Phase 1 — Dyadic substrate (`Mpfx/Dyadic.lean`)

- [x] Define `Dyadic := { x : ℝ // ∃ c e : ℤ, x = c * (2 : ℝ) ^ e }` (via `Subring`, free `CommRing` + `LinearOrder`).
- [x] Coercion `Dyadic → ℝ` via `Subtype.val`; `@[simp]` lemmas about the coercion.
- [x] `Zero`, `One`, `Neg`, `Add`, `Sub`, `Mul` instances; closure proofs.
- [x] `CommRing Dyadic` instance (free via `SubringClass`).
- [x] `LinearOrder Dyadic` instance (free via `Subring`).
- [ ] `Dyadic.toCanonical : Dyadic → ℤ × ℤ` returning `(c, e)` with `c` odd or `c = 0`.
- [ ] `Dyadic.precision : Dyadic → ℕ∞` (≥ 1 for nonzero, `0` for `0`).
- [ ] `Dyadic.quantum : Dyadic → WithBot ℤ`.
- [ ] `Dyadic.isOdd`, `Dyadic.isEven` predicates on canonical `c`.
- [x] Power-of-two helper: `Dyadic.ofIntZpow (c : ℤ) (e : ℤ) : Dyadic` (noncomputable).
- [ ] `simp` set for `c * 2^e` normalization.

## Phase 2 — Abstract format (`Mpfx/Format.lean`)

- [x] `structure AbstractFormat` with `p : ℕ∞`, `exp : WithBot ℤ`, `b : WithTop Dyadic`, and structural invariants:
  - `p_pos : 1 ≤ p` (paper §4.2: `p ∈ ℤ≥1 ∪ {∞}`),
  - `not_degenerate : (p ≠ ⊤ ∧ p ≠ 1) ∨ exp ≠ ⊥` (rules out doubly-unbounded `(⊤, ⊥)` and parity-ambiguous `(1, ⊥)` corners),
  - `b_nn` (bound non-negative when finite — guarantees `0` is representable).
  - *(Future cleanup option: encode `p` directly as `WithTop ℕ+` to drop `p_pos`. Deferred — see "Future work".)*
- [x] `AbstractFormat.Mem` predicate per the plan.
- [x] `Membership Dyadic AbstractFormat` instance.
- [x] `AbstractFormat.extend (F : AbstractFormat) (k : ℕ) : AbstractFormat` — produces `A(p+k, exp-k, b)`. Used to express the paper's "`F⁺ ⊆ F₂`" hypotheses for the RTO double-rounding rules.
- [ ] `AbstractFormat.next : AbstractFormat → Dyadic → Option Dyadic` (next representable above).
- [ ] Smoke-test: instantiate `binary64`, `binary32`, `E5M2`, `E4M3`, `int8`, `fixed<-4,8>` from Fig. 7.
- [ ] Concrete `decide` / `native_decide` membership examples for each instance.

## Phase 3 — Format containment (`Mpfx/Containment.lean`)

- [x] Theorem `containsPrec` (Fig. 8, `𝒜-Contains-Prec`) — direct via monotonicity lemmas.
- [x] Theorem `containsSub` (Fig. 8, `𝒜-Contains-Sub`) — bound argument with `precisionAtMost_of_abs_le` helper.
- [ ] Cross-check: `binary32 ⊆ binary64`, `E5M2 ⊆ binary64` via either rule.

## Phase 4 — Rounding (`Mpfx/Rounding.lean`)

- [ ] `inductive RoundingMode := RTZ | RAZ | RTO | RNE`.
- [ ] `AbstractFormat.adjacents : AbstractFormat → ℝ → Option (Dyadic × Dyadic)` returning the bracketing pair when `x` is unrepresentable.
- [ ] Existence + uniqueness lemma for adjacents (off-overflow).
- [ ] `rnd : AbstractFormat → RoundingMode → ℝ → Dyadic`.
- [ ] Lemma: `rnd F rm x ∈ F` for nonoverflow inputs.
- [ ] Lemma: `rnd F rm x = ⟨x, …⟩` when `x` is already representable.

## Phase 5 — Digit lemmas (`Mpfx/Digits.lean`)

- [ ] `roundedDigitPosition F x : ℤ` (the `exp'` of the proof).
- [ ] **Lemma 5.1**: `roundedDigitPosition` depends only on `(p, exp, x)` (not on `b` or `rm`).
- [ ] **Lemma 5.2**: rounding to `𝒜(p+k, exp-k, b)` keeps `w + k` digits when rounding to `𝒜(p, exp, b)` keeps `w`.
- [ ] **Lemma 5.3**: RTO digit-padding preserves representability (and bracketing).

## Phase 6 — Double rounding (`Mpfx/DoubleRounding.lean`)

Spec-relational form: stated as `RoundsXX F₂ x z → RoundsXX F₁ z w → RoundsXX F₁ x w`
(matches paper's reasoning style; sidesteps constructive `rnd` definition).

- [x] `rndRTZ_RTZ` (general `x ∈ ℝ`).
- [x] `rndRAZ_RAZ` (general `x ∈ ℝ`; combines `_pos` case + `RoundsRAZ.neg` for `x < 0` + `neg_mem`-based handling of `x = 0`).
- [x] **`rndRTO_RTO` (general, all `x ∈ ℝ`)**: dropped `h_prec` and `hp_F₁`. Single hypothesis `hp_F₂ : 2 ≤ F₂.p` (needed because the F₁.p = 1 corner uses index-counting parity). Internally derives the strict numDigits shift via `numDigits_eq_of_subset_of_isOdd` (Lemma 5.3 corollary, fully proven in `Digits.lean` via the y'' construction). The F₁.p = 1 corner additionally derives `F₁.exp = F₂.exp = e_z` to fix the parity bit.
- [x] `rndRTO_RTZ_pos`, `rndRTO_RAZ_pos`: positive case `0 < x` (private; used by the public theorems).
- [x] **`rndRTO_RTZ`, `rndRTO_RAZ` (general, all `x ∈ ℝ`), paper-aligned**: take `(hsub : F₁.extend 1 ⊆ F₂)` matching the paper's Fig. 9 directly, plus auxiliary `hp_F₂ : 2 ≤ F₂.p` (tracked in Future Work for removal). Use `RoundsRTO.notMem_of_extend_subset` (in `Rounding.lean`) to discharge the contradiction step in the RoundsUp (RTZ) / RoundsDown (RAZ) branch.
- [~] **`rndRTO_RNE` (paper-aligned)**: takes `(hsub : F₁.extend 2 ⊆ F₂) (hp_F₂ : 2 ≤ F₂.p)` matching the paper's Fig. 9 structural part. The proof internally derives:
  - `F₁ ⊆ F₁.extend 1 ⊆ F₁.extend 2 ⊆ F₂` chain.
  - `z ∉ F₁` via `RoundsRTO.notMem_of_extend_subset` (using `F₁.extend 1 ⊆ F₂`, derived transitively).
  - The four-way adjacency transfer (same as `rndRTO_RTO`).
  - The no-tie via `RoundsRTO.unique_of_mem` applied to a midpoint that lies in F₂.
  - Helper `RoundsRNE.midpoint_of_tie` (`x = (w' + z')/2` from `|x - w'| = |x - z'| ∧ w' ≠ z'`).
  - Auxiliary helpers `Dyadic.half`, `Dyadic.midpoint`, `Dyadic.coe_midpoint`.
  - Auxiliary `rndRTO_RNE_via_transfers` (low-level wrapper taking pre-built transfers) is kept for callers that supply transfers directly.
- **Remaining auxiliary hypotheses on `rndRTO_RNE`** (still inputs, to be derived from `hsub` in future work):
  - `h_close`: closeness transfer `∀ z' ∈ F₁ adjacent to x, |x - w'| ≤ |x - z'|`. Provable via a same-side-of-midpoint argument when the midpoint lies in F₂; needs F₁-adjacency precision analysis on the midpoint.
  - `h_mid_in_F₂`: midpoints of F₁-pairs lie in F₂. Provable from `F₁.extend 2 ⊆ F₂` for F₁-adjacent pairs (midpoint precision ≤ F₁.p + 1 in that case), but the precision bound needs a delicate analysis across binade boundaries.

**Infrastructure added along the way:**
- [x] `RoundsDown`, `RoundsUp`, `RoundsRTZ`, `RoundsRAZ`, `RoundsRTO`, `RoundsRNE` predicates (`Mpfx/Rounding.lean`).
- [x] `RoundsDown.compose`, `RoundsUp.compose` (parametric building blocks).
- [x] `RoundsRTZ.neg`, `RoundsRAZ.neg`, `RoundsRTO.neg`, `RoundsRNE.neg` symmetry lemmas + shared `roundsAdj_neg` helper.
- [x] `AbstractFormat.neg_mem`: every format is closed under negation (`Mpfx/Format.lean`).
- [x] `Dyadic.IsOddAtP`, `Dyadic.IsEvenAtP`: parity at exactly `p` bits (`Mpfx/Dyadic.lean`).
- [x] `RoundsRTO.of_mem`, `RoundsRTO.unique_of_mem` (trivial case `x ∈ F`).
- [x] **Lemma 5.1 (`AbstractFormat.numDigits`)**: defines the digit count `w` as a function of `(p, exp, x)` only — the type signature `ℕ∞ → WithBot ℤ → ℝ → ℤ` *is* the lemma's content.
- [x] **Lemma 5.2 (`AbstractFormat.numDigits_shift`)**: `numDigits (p+k) (exp-k) x = numDigits p exp x + k` for non-degenerate formats and `x ≠ 0`.
- [x] **`numDigits_le_of_subformat`** (loose Lemma 5.2): `F₁.p ≤ F₂.p ∧ F₂.exp ≤ F₁.exp ⇒ numDigits F₁ x ≤ numDigits F₂ x`.
- [x] **`numDigits_succ_le_of_subformat_succ`** (strict Lemma 5.2): `F₁.p + 1 ≤ F₂.p ∧ F₂.exp + 1 ≤ F₁.exp ⇒ numDigits F₁ x + 1 ≤ numDigits F₂ x` for `x ≠ 0`. Encodes the paper's `F⁺ ⊆ F₂` shift in numDigits-form.
- [x] **Lemma 5.3 core (`Dyadic.precisionAtMost_not_isOddAtP`)**: precision-`w`-representable values cannot be odd at `w + k` bits (`k ≥ 1`).
- [x] **Lemma 5.3 spec form (`RoundsRTO.ne_of_precisionAtMost`)**: when `x` is unrepresentable in an `(w + k)`-bit format, the RTO-rounded `x'` cannot equal any precision-`w`-representable dyadic. (Refined to use `numDigits F.p F.exp x = w + k` for subnormal correctness.)
- [x] **`RoundsRTO` refined**: parity check uses `IsOdd F y` (format-parameterized) instead of `IsOddAtP F.p`.
- [x] **`AbstractFormat.IsOdd / IsEven` (format-parameterized parity)**: parity is intrinsic to `(F, y)` — precision is `numDigits F.p F.exp y`, discriminator is `F.p` (oddness of significand for `F.p ≥ 2`, *index-counting* oddness `Odd (e − F.exp + 1)` for `F.p = 1`).
  - `IsOdd.neg`, `isOdd_neg_iff`, `IsEven.neg`, `isEven_neg_iff`, `IsOdd.ne_zero`, `IsOdd.numDigits_pos`, `precisionAtMost_not_IsOdd` (Lemma 5.3 corollary).
  - **`mem_imp_precisionAtMost_numDigits`**: `y ∈ F → precisionAtMost (numDigits F.p F.exp y).toNat y`. Handles all four `(F.p, F.exp)` shapes.
  - **`numDigits_eq_of_subset_of_isOdd`** (in `Digits.lean`): from `F₁ ⊆ F₂`, `2 ≤ F₂.p`, `y ∈ F₁`, `IsOdd F₂ y`, derive `numDigits F₁ y = numDigits F₂ y`. Proof uses the y'' = (2c − sign c)·2^(e−1) "finer-grid" construction to contradict the strict-greater case (full ~280-line proof).
  - **`RoundsRTO.notMem_of_lower_numDigits`**: applied form of Lemma 5.3 — `RoundsRTO F₂ x z`, `x ≠ z`, `numDigits F₁ z < numDigits F₂ z` ⇒ `z ∉ F₁`. The canonical hook used by every double-rounding theorem.
- [x] **`Mpfx/Utils.lean`**: project-agnostic helpers (`abs_mul_two_zpow`, `two_zpow_split_toNat`, `Int.two_pow_succ_pred`, `Odd.abs_int`, `mul_two_zpow_cancel_right`, `two_zpow_pos`, `two_zpow_ne_zero`).

## Phase 7 — Smoke tests / sanity (`Mpfx/Tests.lean`)

- [ ] `#check @containsPrec`, `@containsSub`, all seven `rnd*_*`.
- [ ] Concrete numeric example: `rnd_{E5M2,RNE}(1.26)` from §3.5 evaluates correctly.
- [ ] Counterexample: composing E2M1 and E4M3 RNE roundings of 1.26 ≠ direct E2M1 rounding.

## Future work

- **Drop `h_close` and `h_mid_in_F₂` auxiliary hypotheses on `rndRTO_RNE`.** **Status: semantically resolved, formalization tracked.** With `hp_F₂ : 3 ≤ F₂.p` (now in place) plus `hsub : F₁.extend 2 ⊆ F₂`, the edge cases really are ruled out: for `F₁.p = 1` we get the full structural shift `F₂.p ≥ F₁.p + 2`, and for `F₁.p ≥ 2` the constraint `F₁.extend 2 ⊆ F₂` forces `F₁.b` small enough that the problematic F₁-adjacent pairs (binade-crossing with odd-significand midpoints) don't exist. To turn this into a complete Lean proof:
  - **Prerequisite — `Dyadic.toCanonical : Dyadic → ℤ × ℤ`** returning the canonical `(c, e)` pair with `c` odd or `c = 0` (~50 lines via `Int.log 2 |c|`-style reasoning to strip even factors).
  - **Main lemma — `Dyadic.midpoint_mem_extend_one_of_F_adjacent`**: for F-adjacent `y₁ < y₂ ∈ F`, `Dyadic.midpoint y₁ y₂ ∈ F.extend 1`. Proof structure:
    1. Extract canonical reps `(c₁, e₁), (c₂, e₂)` for `y₁, y₂`.
    2. WLOG `e₁ ≤ e₂`. Case-split on `δ := e₂ − e₁`:
       - **Same-quantum `(δ = 0)`**: F-adjacency forces `c₂ = c₁ + 2`; both odd. Midpoint at quantum `e₁` has coefficient `c₁ + 1`, with `|c₁ + 1| ≤ 2^{F.p}`.
       - **Binade-crossing `(δ = F.p)`**: `c₁ = ±(2^{F.p} − 1)` (max canonical), `c₂ = ±1` (min canonical at next binade). Midpoint coefficient at quantum `e₁ − 1` is `2^{F.p+1} − 1`.
       - **Intermediate `(1 ≤ δ < F.p)`**: ruled out by F-adjacency — construct an explicit Dyadic witness in `F` strictly between `y₁` and `y₂`, contradicting `h_adj`.
    3. Apply `Dyadic.precisionAtMost_of_abs_le` with `p = F.p + 1`.
  - **Total scope**: ~250–300 lines. Once proven, `h_close` and `h_mid_in_F₂` follow via the same-side-of-midpoint argument and the `F₁.extend 1 ⊆ F₁.extend 2 ⊆ F₂` chain.
  - Best done as a focused multi-day effort, with `toCanonical` and per-case lemmas split out for testability.

- **`hp_F₂ : 2 ≤ F₂.p` is load-bearing under the weaker `F₁.extend k ⊆ F₂` form**, but **droppable under the paper's stronger `A(F.p + k, F.exp - k, F.next F.b) ⊆ F₂` form**. **(Status update: investigated; original TODO claim was wrong.)** The original claim that the theorem held without `hp_F₂` was based on a hand-check of `F₁ = A(1, 0, 1)`, `F₁.extend 1 = F₂ = A(1, -1, 1)` — a special case where `Odd(0 - (-1) + 1) = Odd(2) = false`, so `z` always lands on a non-`F₁` value and the contradiction step is vacuous. **Concrete counter-example with `F₁.extend 1 ⊆ F₂` but `F₂.p = 1`**: take `F₁ = A(2, 0, 1)`, `F₂ = A(1, -2, 1)`. Then `F₁ = {-1, 0, 1}`, `F₁.extend 1 = {0, ±1/2, ±1}` ⊆ `F₂ = {0, ±1/4, ±1/2, ±1}`. For `x = 0.7`: `IsOdd F₂ 1 = Odd(0 - (-2) + 1) = Odd(3) = true`, so `RoundsRTO F₂ 0.7 1` (z = 1). `z = 1 ∈ F₁` gives `RoundsRTZ F₁ 1 1`. Conclusion would require `RoundsRTZ F₁ 0.7 1`, but `|1| > 0.7` violates RTZ's bound clause — **theorem genuinely fails** under the weak hypothesis.
  - The paper's hypothesis `A(p₁+1, exp₁-1, next_{p₁,exp₁}(b₁)) ⊆ F₂` rules out this counter-example via the `next(b₁)` bound — for `F₁ = A(2, 0, 1)`, `next_{2,0}(1) = 2`, so paper requires `F₂` to contain values up to `2`, which forces `3/2 ∈ F₂` (precision 2), excluding `F₂.p = 1`.
  - **`AbstractFormat.next` now defined** in `Mpfx/Format.lean`: `next F b := b + 2^F.exp` (a "loose" version sufficient for the bound's structural role). Lemmas `next_coe_exp`, `next_bot_exp`, `lt_next_of_exp_coe` provided.
  - **Pending refactor**: change `rndRTO_RTZ` / `rndRTO_RAZ` / `rndRTO_RNE` hypotheses to the paper's `A(F.p+k, F.exp-k, F.next F.b) ⊆ F₂` form, and drop `hp_F₂`. Internally derive `F₂.p ≥ 2` from the strengthened bound: the test value `3·2^(F.exp - 1) ∈ A(p+1, exp-1, F.next b)` (when `F.b ≥ 2^F.exp`) forces `F₂` to contain a precision-2 value, hence `F₂.p ≥ 2`. Approximately 50–100 lines per RTO theorem to add the derivation.

- **Encode `1 ≤ p` at the type level** by changing `p : ℕ∞` to `p : WithTop ℕ+` (positive naturals + ∞). Would drop the `p_pos` field. Significant refactor: numeric literals (`(2 : ℕ∞)`), `F.p + k`, and many `exact_mod_cast`s would need to be threaded through `ℕ+ → ℕ → ℕ∞` coercions. Deferred — `p_pos` is fine in practice.
