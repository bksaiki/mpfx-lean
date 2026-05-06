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

Each: state per Fig. 9, prove using Phase 4–5 infrastructure.

- [ ] `rndRTZ_RTZ`.
- [ ] `rndRAZ_RAZ`.
- [ ] `rndRTO_RTO_O` (case `b₁` odd in `𝒜(p₁, exp₁, b₁)`).
- [ ] `rndRTO_RTO_E` (case `b₁` even).
- [ ] `rndRTO_RTZ`.
- [ ] `rndRTO_RAZ`.
- [ ] `rndRTO_RNE`.

## Phase 7 — Smoke tests / sanity (`Mpfx/Tests.lean`)

- [ ] `#check @containsPrec`, `@containsSub`, all seven `rnd*_*`.
- [ ] Concrete numeric example: `rnd_{E5M2,RNE}(1.26)` from §3.5 evaluates correctly.
- [ ] Counterexample: composing E2M1 and E4M3 RNE roundings of 1.26 ≠ direct E2M1 rounding.

## Cleanup

- [ ] Remove `def hello := "world"` from `Mpfx/Basic.lean` (or repurpose).
- [ ] `Mpfx.lean` re-exports each module.
- [ ] `lake build` is clean, `git grep -n sorry Mpfx/` is empty.
