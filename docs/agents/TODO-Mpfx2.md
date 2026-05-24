# Mpfx2 TODO

A parallel re-implementation of the formalization in `Mpfx2/`, exploring
two design changes from `Mpfx/`:

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

Status legend: `[ ]` not started · `[~]` in progress · `[x]` done · `[!]` blocked.

## File layout

```
Mpfx2/
├── Utils.lean      project-agnostic helpers (two_zpow_pos, etc.)
├── Dyadic.lean     IsDyadic, Dyadic subring, ofIntZpow, precisionAtMost,
│                   quantumAtLeast, IsRepresentableAtP,
│                   precisionAtMost_of_abs_le (renormalization)
├── Format.lean     Format / FiniteFormat / ParityFormat hierarchy,
│                   Mem, boundOK, unbounded, zero_mem,
│                   numDigits, IsOdd, IsEven
├── Rounding.lean   relational layer (constructive):
│                   TieBreak, RoundingMode, RoundResult, IsUndefined,
│                   IsFaithfulRound, RoundsFinite, Rounds
└── RoundOp.lean    function layer (noncomputable, classical):
                    canonicalExp, exp_le_canonicalExp,
                    log_sub_p_le_canonicalExp, abs_floor_le_of_abs_lt,
                    rndInt, rndParity, toParityFormatOf{ToOdd,NearestEven},
                    rndUnbounded, rnd, rnd_iff_rounds (full proof),
                    per-mode satisfies/unique decomposition
```

## Substrate (done)

- [x] `IsDyadic` predicate + closure (`zero`, `one`, `add`, `neg`, `mul`).
- [x] `dyadicSubring`, `Dyadic` abbrev.
- [x] `Dyadic.ofIntZpow`, `coe_ofIntZpow`.
- [x] `Dyadic.precisionAtMost : WithTop ℕ+ → Dyadic → Prop`.
- [x] `Dyadic.quantumAtLeast : WithBot ℤ → Dyadic → Prop`.
- [x] `Dyadic.IsRepresentableAtP`.
- [x] `Dyadic.precisionAtMost_of_abs_le` (renormalization for saturation).
- [x] `NonNegDyadic := { d : Dyadic // 0 ≤ (d : ℝ) }`.
- [x] `Format` (`p : WithTop ℕ+`, `exp : WithBot ℤ`, `b : WithTop NonNegDyadic`).
- [x] `Format.boundOK`, `Format.Mem`, `Membership Dyadic Format`, `zero_mem`.
- [x] `Format.unbounded` (sets `b := ⊤`).
- [x] `FiniteFormat extends Format` with `finite : p ≠ ⊤ ∨ exp ≠ ⊥`.
- [x] `FiniteFormat.numDigits` (Lemma 5.1).
- [x] `ParityFormat extends FiniteFormat` with `parity : p ≠ 1 ∨ exp ≠ ⊥`.
- [x] `ParityFormat.IsOdd`, `IsEven`, `isEven_zero`, `nondegenerate`.

## Rounding (done)

- [x] `TieBreak`, `RoundingMode`, `RoundResult` inductives (lowercase
      constructors).
- [x] `Format.IsUndefined` (covers `(⊤, ⊥, _)` and `(1, ⊥, .toOdd ∨ .nearest .toEven)`).
- [x] `IsFaithfulRound` on `Format`.
- [x] `RoundsFinite` per-mode spec (extracted for the existential in
      `Rounds .overflow`).
- [x] `Rounds : Format → RoundingMode → ℝ → RoundResult → Prop` with
      IEEE-style overflow (uses `F.unbounded` + separate `boundOK`).
- [x] `Format.canonicalExp` (FLoPS-style canonical exponent).
- [x] `rndInt` for directed modes + `.nearest .awayZero`.
- [x] `rndParity` for `.toOdd`, `.nearest .toEven` (takes ParityFormat).
- [x] `Format.toParityFormatOfToOdd`, `toParityFormatOfNearestEven`
      (extract ParityFormat witness from `¬ IsUndefined`).
- [x] `rndUnbounded` (no-bound rounding).
- [x] `rnd` (full: dispatches undefined / overflow / finite).
- [x] `Format.exp_le_canonicalExp` helper.
- [x] `Format.log_sub_p_le_canonicalExp` helper.
- [x] `abs_floor_le_of_abs_lt` helper.
- [x] `rnd_iff_rounds` — single uniform bridge, **fully discharged**
      modulo the per-mode `rndUnbounded_*` obligations below.
- [x] Per-mode `rndUnbounded_unique_*` for directed modes
      (`toNegative`, `toPositive`, `toZero`, `awayZero`).

## Open: complete the soundness chain (P0)

All structural plumbing (helpers, canonical-exponent inequalities,
`precisionAtMost_of_abs_le`, `abs_floor_le_of_abs_lt`,
`abs_ceil_le_of_abs_lt`) is in place. What remains is mode-specific.

**Membership + middle-clause** (done for all four directed modes):

- [x] `rndUnbounded_satisfies_toNegative` — membership + `y ≤ x` done;
      *minimality remaining*.
- [x] `rndUnbounded_satisfies_toPositive` — membership + `x ≤ y` done;
      *minimality remaining*.
- [x] `rndUnbounded_satisfies_toZero` — membership + `|y| ≤ |x| ∧ y·x ≥ 0`
      done; *minimality remaining*.
- [x] `rndUnbounded_satisfies_awayZero` — membership + `|x| ≤ |y| ∧ y·x ≥ 0`
      done; *minimality remaining*.

**Per-mode obligations** still open (8 total `sorry`s):

- [ ] `rndUnbounded_satisfies_toNegative` minimality clause —
      argument: case-split on whether `z`'s canonical exponent is ≥ `e`
      (then `z` is a multiple of `2^e` and `z · 2^(-e)` is an integer
      ≤ `⌊x · 2^(-e)⌋ = c`, so `z ≤ y`); or `< e` (then `z`'s binade
      is strictly smaller than `x`'s, and `y ≥ 2^(Int.log 2 x) > z`).
- [ ] `rndUnbounded_satisfies_toPositive` minimality — mirror.
- [ ] `rndUnbounded_satisfies_toZero` minimality — sign-split version.
- [ ] `rndUnbounded_satisfies_awayZero` minimality — mirror sign-split.
- [ ] `rndUnbounded_satisfies_toOdd` — faithful (RoundDown ∨ RoundUp)
      + parity tie-break via `ParityFormat.IsOdd`. Needs port of
      `IsRepresentableAtP` uniqueness from `Mpfx/Digits.lean`.
- [ ] `rndUnbounded_satisfies_nearest` — faithful + closeness +
      tie-break by `tb`.
- [ ] `rndUnbounded_unique_toOdd` — needs faithful-uniqueness + parity
      uniqueness (`IsOdd y` distinguishes the two F-adjacents).
- [ ] `rndUnbounded_unique_nearest` — closeness + tie-break uniqueness.

## Open: theorems to port from `Mpfx/`

The Mpfx implementation has ~3000 lines of mature theorems that haven't
been ported. The substantive ones, in rough porting order:

### Containment (Mpfx/Containment.lean)

- [ ] `containsPrec` — `precisionAtMost p₁ y → precisionAtMost p₂ y` when
      `p₁ ≤ p₂`, with quantum/bound adjustments. From the paper §5.1.
- [ ] `containsSub` — subformat with explicit `k` shift on
      `(p, exp)`. Paper §5.1.
- [ ] Format-extension lemmas (`F.extend k` and its containment).

### Digits + parity (Mpfx/Digits.lean)

- [ ] `numDigits_shift` — Lemma 5.2: shifting `(p, exp)` by `(+k, -k)`
      shifts digit count by `+k`.
- [ ] `numDigits_extend` — Lemma 5.2 applied to `F.extend`.
- [ ] `IsOdd.neg`, `IsEven.neg` — parity is negation-invariant.
- [ ] `IsOdd.numDigits_pos`, `IsOdd.ne_zero` — basic API on `IsOdd`.
- [ ] `precisionAtMost_not_IsOdd` — Lemma 5.3 corollary: low-precision
      values can't be `IsOdd` at higher numDigits.
- [ ] `IsRepresentableAtP` uniqueness (canonical form is unique at
      fixed digit count).

### Rounding API (Mpfx/Rounding.lean)

- [ ] Sign-symmetry: `Rounds.neg_toZero`, `neg_awayZero`, `neg_toOdd`,
      `neg_nearest`, `Rounds.neg` unified.
- [ ] Mode-conversion: `Rounds.toPositive_iff_awayZero_of_nn`,
      `Rounds.toNegative_iff_awayZero_of_np` (for sign-reduction proofs).
- [ ] `IsFaithfulRound`-extraction lemmas (split RTN/RTP from
      `IsFaithfulRound`).
- [ ] `Rounds` uniqueness theorems per mode (the strict version, not
      just the soundness of `rnd`).

### Double rounding (Mpfx/DoubleRounding.lean and DoubleRoundingCex.lean)

These are the headline application — once `rnd_iff_rounds` is fully
discharged, restating them on `rnd … = .finite …` is mechanical.

**Positive (Fig. 9):**

- [ ] `rndRTZ_RTZ`.
- [ ] `rndRAZ_RAZ`.
- [ ] `rndRTO_RTO` (both `_O` and `_E` clauses).
- [ ] `rndRTO_RTZ`.
- [ ] `rndRTO_RAZ`.
- [ ] `rndRTO_RN` (both tie-breaks).

**Counterexamples (ten cases):**

- [ ] `no_rndRNE_RNE`.
- [ ] `no_rndRNE_RAZ`.
- [ ] `no_rndRNE_RTZ`.
- [ ] `no_rndRNE_RTO`.
- [ ] `no_rndRTZ_RNE`.
- [ ] `no_rndRTZ_RAZ`.
- [ ] `no_rndRTZ_RTO`.
- [ ] `no_rndRAZ_RNE`.
- [ ] `no_rndRAZ_RTZ`.
- [ ] `no_rndRAZ_RTO`.

## Open: new features

- [ ] **Fig. 7 format instances**: `binary64`, `binary32`, `E5M2`,
      `E4M3`, `int8`, `fixed<-4, 8>`. Concrete `FiniteFormat` or
      `ParityFormat` values; useful as smoke tests.
- [ ] **Smoke tests**: `Mpfx2/Tests.lean` with concrete `rnd F rm x`
      evaluations. Needs `decide`/`native_decide` once `rnd` is
      sound — but since `rnd` is `noncomputable`, these would be
      `rfl`-style equational proofs not `#eval`.
- [ ] **Cross-references** to the paper: `binary32 ⊆ binary64` via
      `containsPrec`; `E5M2 ⊆ binary64` via `containsSub`.
- [ ] **§3.5 numeric example**: `rnd_{E5M2,RNE}(1.26)` evaluates to
      its expected value.
- [ ] **Concrete counterexample**: composing E2M1 and E4M3 RNE of
      1.26 differs from direct E2M1 RNE rounding (from the paper).

## Open: refactoring / cleanup

- [ ] **Cast bridge lemma**: pull out `(2 : ℝ) ^ ((n : ℕ) : ℤ) =
      ((2 : ℤ) ^ n : ℝ)` (or similar) as a named helper. Currently
      buried inside attempted proofs.
- [ ] **Decide on `Coe FiniteFormat Format`** (and `ParityFormat
      Format`/`ParityFormat FiniteFormat`). Mathlib convention is to
      *not* add the `Coe` and require `.toFormat` at call sites; but
      if `.toFormat`-noise becomes overwhelming, add the instance.
- [ ] **`@[simp]` lemmas** for `F.toFormat.p = F.p`, etc., across the
      tier hierarchy. Currently `F.toFormat` projections need manual
      `change` in proofs.
- [ ] **Inline the `Format.toParityFormatOf*` helpers** if `tactic`-mode
      `cases` propagation improves — currently they're `private` due
      to one-off use in `rnd`'s dispatch.
- [ ] **Constructive `rndInt` variants**: explore decidable-via-Dyadic
      versions that *don't* require Classical (if input is restricted
      to `Dyadic` rather than `ℝ`).
- [ ] **FLoPS-style typeclass generalization**: `class Faithful`,
      `class Monotonic`, `class ValidRound` parameterizing over the
      integer kernel. Optional — only valuable if the mode-specific
      proofs end up sharing structure.
- [ ] **Documentation pass**: per-file module docstrings, paper-reference
      cross-links, and a top-level `Mpfx2/README.md`.

## Long-term / out of scope

- Subnormal flushing, signed zero, ∞, NaN (paper §9).
- Overflow semantics for double rounding under saturation modes.
- Posits, P3109 unsigned floats.
- Stochastic rounding modes (FLoPS does these; not needed for
  *When Double Rounding is Correct*).
- Migration: deciding whether `Mpfx2/` eventually replaces `Mpfx/`
  or remains a parallel exploration.
