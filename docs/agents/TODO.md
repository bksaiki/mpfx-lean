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

- [x] `structure AbstractFormat` with `p : ℕ∞`, `exp : WithBot ℤ`, `b : WithTop Dyadic`, structural invariants `not_degenerate : p ≠ ⊤ ∨ exp ≠ ⊥` (paper §4.2: format must be precision- or quantum-limited) and `b_nn` (bound non-negative when finite).
- [x] `AbstractFormat.Mem` predicate per the plan.
- [x] `Membership Dyadic AbstractFormat` instance.
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
- [x] `rndRTO_RTO` (general, all `x ∈ ℝ`): unified `_O`/`_E` subcases via spec-relational form. Requires extra `h_prec` hypothesis: `numDigits F₁ z = numDigits F₁ x` (true when `F₁`-adjacents of `x` lie in same magnitude bin).
- [x] `rndRTO_RTZ_pos`, `rndRTO_RAZ_pos`: positive case `0 < x`.
- [x] **`rndRTO_RTZ`, `rndRTO_RAZ` (general, all `x ∈ ℝ`)**: combine `_pos` + `RoundsRTO.neg` / `RoundsRTZ.neg` / `RoundsRAZ.neg` symmetry; `x = 0` case is vacuous from `hwk` + `hk : 1 ≤ k`.
- [~] `rndRTO_RNE`: progressively-stronger wrappers in place.
  - `rndRTO_RNE_of_eq` proven (trivial case `z = x`).
  - `rndRTO_RNE_via_transfers` packages the structural transfers as hypotheses.
  - **`rndRTO_RNE`**: derives the adjacency transfer fully via Lemma 5.3 + `RoundsDown`/`RoundsUp` 4-way case-split (same as `rndRTO_RTO`). Takes `h_close` and `h_no_tie` as hypotheses.
  - **`rndRTO_RNE_with_mid`**: further derives `h_no_tie` from a structural hypothesis `h_mid_in_F₂` (midpoints of `F₁`-pairs are in `F₂`). Uses `RoundsRTO.unique_of_mem` to show: a tie at `x` means `x = midpoint`, which forces `z = midpoint = x`, contradicting `z ≠ x`. Helper `RoundsRNE.midpoint_of_tie` extracts `x = (w' + z')/2` from `|x - w'| = |x - z'| ∧ w' ≠ z'`.
  - **`Dyadic.half`, `Dyadic.midpoint`, `Dyadic.coe_midpoint`**: concrete midpoint construction added (so `(midpoint y₁ y₂ : ℝ) = ((y₁ : ℝ) + (y₂ : ℝ)) / 2` definitionally).
  - Remaining work: (1) prove `h_close` from `hk : 2 ≤ k` (needs F₂-adjacency analysis showing `x` and `z` are on the same side of any `F₁`-midpoint); (2) prove `h_mid_in_F₂` from `F₁ ⊆ F₂` plus a "F₂ has finer quantum and ≥ `w + 1` precision" hypothesis (using `Dyadic.midpoint` as the explicit `m`).

**Infrastructure added along the way:**
- [x] `RoundsDown`, `RoundsUp`, `RoundsRTZ`, `RoundsRAZ` predicates (`Mpfx/Rounding.lean`).
- [x] `RoundsDown.compose`, `RoundsUp.compose` (parametric building blocks).
- [x] `AbstractFormat.neg_mem`: every format is closed under negation (`Mpfx/Format.lean`).
- [x] `Dyadic.IsOddAtP`, `Dyadic.IsEvenAtP`: parity at exactly `p` bits (`Mpfx/Dyadic.lean`).
- [x] `RoundsRTO` predicate; `RoundsRTO.of_mem`, `RoundsRTO.unique_of_mem` (trivial case `x ∈ F`).
- [x] **Lemma 5.1 (`AbstractFormat.numDigits`)**: defines the digit count `w` as a function of `(p, exp, x)` only — the type signature `ℕ∞ → WithBot ℤ → ℝ → ℤ` *is* the lemma's content.
- [x] **Lemma 5.2 (`AbstractFormat.numDigits_shift`)**: `numDigits (p+k) (exp-k) x = numDigits p exp x + k` for non-degenerate formats and `x ≠ 0`.
- [x] **Lemma 5.3 core (`Dyadic.precisionAtMost_not_isOddAtP`)**: precision-`w`-representable values cannot be odd at `w + k` bits (`k ≥ 1`).
- [x] **Lemma 5.3 spec form (`RoundsRTO.ne_of_precisionAtMost`)**: when `x` is unrepresentable in an `(w + k)`-bit format, the RTO-rounded `x'` cannot equal any precision-`w`-representable dyadic. (Refined to use `numDigits F.p F.exp x = w + k` instead of `F.p = w + k`, for subnormal correctness.)
- [x] **`RoundsRTO` refined**: parity check now uses `IsOddAtP (numDigits F.p F.exp x)` instead of `IsOddAtP F.p`, correctly handling subnormal regime.
- [x] **`AbstractFormat.IsOdd / IsEven` (format-parameterized parity)**: Replaces `IsOddAtP w y` / `IsEvenAtP w y` in `RoundsRTO` / `RoundsRNE`. Parity is now intrinsic to `(F, y)` — precision is `numDigits F.p F.exp y` (the dyadic's natural F-precision), discriminator is `F.p` (oddness of significand for `F.p ≥ 2`, oddness of exponent for `F.p = 1`).
  - `IsOdd.neg`, `IsOdd.ne_zero`, `precisionAtMost_not_IsOdd` (Lemma 5.3 corollary in new form).
  - `RoundsRTO.ne_of_precisionAtMost` now takes `hgt : (w : ℤ) < numDigits F.p F.exp x'` (precision at the rounded value, not at x).
  - `rndRTO_RTO`, `rndRTO_RTZ_pos`, `rndRTO_RAZ_pos`, `rndRTO_RNE` and their general counterparts now take `hzgt : x ≠ z → (w : ℤ) < numDigits F₂.p F₂.exp z` instead of `hwk` at x. Caller is responsible for providing the F₂-precision-at-z bound.
  - `rndRTO_RTO` no longer needs `h_prec` — parity transfer is automatic since `IsOdd F₁ w'` is intrinsic to `(F₁, w')`.

## Phase 7 — Smoke tests / sanity (`Mpfx/Tests.lean`)

- [ ] `#check @containsPrec`, `@containsSub`, all seven `rnd*_*`.
- [ ] Concrete numeric example: `rnd_{E5M2,RNE}(1.26)` from §3.5 evaluates correctly.
- [ ] Counterexample: composing E2M1 and E4M3 RNE roundings of 1.26 ≠ direct E2M1 rounding.

## Cleanup

- [ ] Remove `def hello := "world"` from `Mpfx/Basic.lean` (or repurpose).
- [ ] `Mpfx.lean` re-exports each module.
- [ ] `lake build` is clean, `git grep -n sorry Mpfx/` is empty.

## Future work

- **Drop `h_prec` hypothesis from `rndRTO_RTO`** (and possibly `rndRTO_RNE`).
  Currently `rndRTO_RTO` requires
  `h_prec : numDigits F₁.p F₁.exp z = numDigits F₁.p F₁.exp x`
  to transfer parity of `w'` from `z`'s view to `x`'s view (since
  `IsOddAtP p w'` depends on `p`). This holds automatically when `x` is in
  `F₁`'s normal range (both `numDigits` equal `F₁.p = w`) but can fail when
  `z` and `x` straddle a power-of-two boundary in the subnormal regime.
  Three options to drop it:
  1. Restrict to `x` in `F₁`'s normal range (`numDigits F₁ x = F₁.p`).
  2. Strengthen Lemma 5.3 to also assert `numDigits F₁ z = numDigits F₁ x`
     (needs adjacency-bin machinery).
  3. Reformulate `RoundsRTO`'s parity clause with a precision-invariant
     property (e.g. parity at `y`'s own canonical precision).
