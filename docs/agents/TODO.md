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

- [x] `structure AbstractFormat` with `p : ℕ∞`, `exp : WithBot ℤ`, `b : WithTop Dyadic`.
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
- [ ] `rndRTO_RTO_O` (case `b₁` odd in `𝒜(p₁, exp₁, b₁)`).
- [ ] `rndRTO_RTO_E` (case `b₁` even).
- [ ] `rndRTO_RTZ`.
- [ ] `rndRTO_RAZ`.
- [ ] `rndRTO_RNE`.

**Infrastructure added along the way:**
- [x] `RoundsDown`, `RoundsUp`, `RoundsRTZ`, `RoundsRAZ` predicates (`Mpfx/Rounding.lean`).
- [x] `RoundsDown.compose`, `RoundsUp.compose` (parametric building blocks).
- [x] `AbstractFormat.neg_mem`: every format is closed under negation (`Mpfx/Format.lean`).
- [x] `Dyadic.IsOddAtP`, `Dyadic.IsEvenAtP`: parity at exactly `p` bits (`Mpfx/Dyadic.lean`).
- [x] `RoundsRTO` predicate; `RoundsRTO.of_mem` (trivial case `x ∈ F`).

## Phase 6.5 — Conventions

- All RTO/RNE theorems require `2 ≤ p` (where `p` is the format precision).
  At `p = 1`, every nonzero value has `c ∈ {±1}` (both odd), so RTO/RNE
  degenerate. The simpler modes (RTZ/RAZ) and containment theorems do not
  need this constraint.

## Future work

- **Relax `2 ≤ p` to `1 ≤ p` for RTO/RNE.** Requires a different definition
  of odd/even at `p = 1`. Candidates:
  - Use parity of the canonical `c` (always odd for nonzero `y`) — needs
    auxiliary tagging based on exponent parity to disambiguate.
  - Treat `0` specially as an "even" value RTO can pick when adjacents collide.
  - Define a "round-to-canonical-odd" mode whose meaning at `p = 1` differs
    from the general formula.
  Add a test suite once we have one to validate the relaxed definitions
  agree with the strict `p ≥ 2` ones.

## Phase 7 — Smoke tests / sanity (`Mpfx/Tests.lean`)

- [ ] `#check @containsPrec`, `@containsSub`, all seven `rnd*_*`.
- [ ] Concrete numeric example: `rnd_{E5M2,RNE}(1.26)` from §3.5 evaluates correctly.
- [ ] Counterexample: composing E2M1 and E4M3 RNE roundings of 1.26 ≠ direct E2M1 rounding.

## Cleanup

- [ ] Remove `def hello := "world"` from `Mpfx/Basic.lean` (or repurpose).
- [ ] `Mpfx.lean` re-exports each module.
- [ ] `lake build` is clean, `git grep -n sorry Mpfx/` is empty.
