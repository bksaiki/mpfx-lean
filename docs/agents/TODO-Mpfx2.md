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

**Per-mode obligations** still open (4 total `sorry`s):

All directed-mode minimality clauses are now done via two top-level
helpers `floor_minimality` and `ceil_minimality` (built on the
lower-level `binade_le_floor` / `ceil_le_binade` arithmetic):

- [x] `rndUnbounded_satisfies_toNegative` minimality — `floor_minimality`.
- [x] `rndUnbounded_satisfies_toPositive` minimality — `ceil_minimality`.
- [x] `rndUnbounded_satisfies_toZero` minimality — sign-split:
      `floor_minimality` for `0 ≤ x`, `ceil_minimality` for `x < 0`.
- [x] `rndUnbounded_satisfies_awayZero` minimality — sign-split mirror:
      `ceil_minimality` for `0 < x`, `floor_minimality` for `x < 0`,
      `x = 0` short-circuits to `y = 0 ≤ |z|`.
- [ ] `rndUnbounded_satisfies_toOdd` — faithful (RoundDown ∨ RoundUp)
      + parity tie-break via `ParityFormat.IsOdd`. Proof outline
      sketched in the theorem body. **Blockers** (each ≥ 50 LoC):
      (a) port of `numDigits_*` evaluator lemmas from
      `Mpfx/Digits.lean`; (b) port of `mem_imp_precisionAtMost_numDigits`;
      (c) `IsRepresentableAtP` uniqueness; (d) "alternating parity"
      (`¬ IsOdd dlo → IsOdd dhi`) which uses (c).
      Also: `F.toFormat`-vs-`F.unbounded` ParityFormat bridge needed
      since `RoundsFinite F.unbounded` asks for `F'.toFormat = F.unbounded`
      while `rndUnbounded` uses `F.toParityFormatOfToOdd` (toFormat = F).
- [ ] `rndUnbounded_satisfies_nearest` — faithful + closeness +
      tie-break by `tb`. Tie-break case needs (a)–(d) above for `.toEven`.
- [ ] `rndUnbounded_unique_toOdd` — needs faithful-uniqueness + parity
      uniqueness (`IsOdd y` distinguishes the two F-adjacents).
      Same blockers as satisfies.
- [ ] `rndUnbounded_unique_nearest` — closeness + tie-break uniqueness.
      Same blockers.

**Helpers + infrastructure added** (this session):
- In `Mpfx2/RoundOp.lean`:
  - `ofIntZpow_mem_unbounded` — `Dyadic.ofIntZpow k e ∈ F.unbounded`.
  - `floor_mantissa_lt` — `|x · 2^(-canonicalExp x)| < 2^p`.
  - **Refactoring**: `_toNegative`, `_toPositive`, `_toZero`,
    `_awayZero` `_satisfies` proofs now use `ofIntZpow_mem_unbounded`
    + `floor_mantissa_lt` for membership (~180 LoC removed from
    duplicated inline mantissa-bound and quantum-shift proofs).
    File reduced from 1589 → 1412 lines.
- In `Mpfx2/Format.lean`:
  - `numDigits_zero`, `numDigits_neg`, `numDigits_top_coe`,
    `numDigits_coe_bot`, `numDigits_coe_coe` — evaluators.
  - `numDigits_nonneg` — `numDigits y ≥ 1` for nonzero `y ∈ F`.
  - `mem_imp_precisionAtMost_numDigits` — existence of `(c, e)`
    representation at `numDigits y` bits for nonzero `y ∈ F`.
  - `IsOdd.neg`, `IsEven.neg`, `IsOdd.numDigits_pos`, `IsOdd.ne_zero`.
- In `Mpfx2/Dyadic.lean`:
  - `IsRepresentableAtP.unique` — uniqueness of canonical form.
    The keystone for parity-uniqueness arguments.
  - `IsRepresentableAtP.ne_zero` — having a witness implies `y ≠ 0`.
  - `isRepresentableAtP_of_bounds` — constructor wrapper.
- In `Mpfx2/Format.lean`:
  - `isOdd_iff_odd_of_canonical`, `isEven_iff_even_of_canonical` —
    given an `IsRepresentableAtP` witness at `numDigits y`, parity
    reduces to `Odd c` / `Even c`.
- In `Mpfx2/Rounding.lean`:
  - `Format.unbounded_isUndefined` — `F.unbounded.IsUndefined rm =
    F.IsUndefined rm` (by `rfl`). Resolves the F-vs-F.unbounded
    bridge issue cleanly.

**`_toOdd` satisfies — structural proof complete; floating-point
case fully discharged**:
- Full structural assembly of `_toOdd` satisfies (~150 LoC).
- Exact case (`(lo : ℝ) = s`): ✓ vacuous parity.
- `IsOdd dlo` case: ✓ direct via bridge.
- `¬ IsOdd dlo` case, `F.p = (p:ℕ+) ≠ 1, F.exp = ⊥`: ✓ uses
  `alternating_parity_floating` with bounds derived from canonical
  exponent (~80 LoC of bounds derivation).
- Remaining sub-sorries in `_toOdd` satisfies:
  - `F.p = ⊤, F.exp = (e' : ℤ)` case.
  - `F.p = (p:ℕ+), F.exp = (e' : ℤ)` case.

**`_toOdd_unique` — floating-point case fully proven**:
- `h_mixed_eq` helper: handles "y RoundDown, y' RoundUp" via case-split.
- **`y = x` and `y' = x` sub-cases**: ✓ proven via min/max property.
- **Strict sub-case (`y < x < y'`)**:
  - **F.p = (p:ℕ+), F.exp = ⊥** (floating-point): ✓ fully proven.
    Identifies `y = dlo` (via `_satisfies_toNegative` + uniqueness) and
    `y' = dhi` (via `_satisfies_toPositive` + `⌈⌉ = ⌊⌋+1` in non-exact),
    bridges `F_y.IsOdd ↔ F''.IsOdd` via `IsOdd_iff_of_toFormat_eq`,
    derives `2^(p-1) ≤ |lo|, |lo+1|` from canonical exponent + strict
    inequality, applies `not_both_isOdd_floating` → contradiction.
  - **F.p = ⊤** (fixed-point): sub-sorry. Needs analog of
    `not_both_isOdd_floating` for fixed-point case.
  - **F.exp = (e':ℤ)** (mixed): sub-sorry. Same.
- Both RoundDown / Both RoundUp cases: ✓ fully proved.

**New keystone**: `IsOdd_iff_of_toFormat_eq` (in `Format.lean`):
`F1.IsOdd y ↔ F2.IsOdd y` when `F1.toFormat = F2.toFormat`.
Proven via destructuring + `cases h; rfl` using Lean's proof
irrelevance for ParityFormat's Prop fields. This unblocks all
parity-mode proofs that need to bridge between different ParityFormat
witnesses.

**Mixed case (`F.p = (p:ℕ+), F.exp = (e':ℤ)`) — scope clarified, deferred**:
The mixed case has **three** sub-cases:
1. `F.p ≠ 1`, normal regime (`e = log|x|+1-p > e'`): like floating-point.
   `numDigits y = min(p, log|y|-e'+1) = p`. Saturation at `|c| = 2^p` possible.
2. `F.p ≠ 1`, subnormal regime (`e = e' ≥ log|x|+1-p`): like fixed-point.
   `numDigits y = log|y|-e'+1`. No saturation.
3. **`F.p = 1`**: critical insight — `(p = 1, exp = (e':ℤ))` is NOT undefined
   (the undefined clause requires `exp = ⊥`). So `p = 1` must be handled, and
   it uses **exponent-index parity** (the second branch of `IsOdd`'s `if`),
   fundamentally different from significand-c parity.

Each sub-case needs analog of `alternating_parity_*` / `not_both_isOdd_*`:
- Sub-cases 1, 2: analogous to existing floating/fixed lemmas; case-split
  on regime, then derive bounds + apply IsRepresentableAtP characterization.
- Sub-case 3 (`p = 1`): requires new infrastructure for exponent-index
  parity in `IsOdd` (the `Odd (e - e' + 1)` branch).

**Fixed-point parity infrastructure complete** (`F.p = ⊤, F.exp = (e':ℤ)`):
- `log_abs_mul_zpow` — `Int.log 2 |k·2^e'| = Int.log 2 |k| + e'`.
- `isOdd_iff_odd_at_canonical_fixedpoint` — `IsOdd (k·2^e') ↔ Odd k`.
  No saturation since `numDigits = log|k| + 1` adapts to `|k|`.
- `alternating_parity_fixedpoint` — `¬ IsOdd dlo → IsOdd dhi`.
  Handles `lo = 0` (dlo = 0) and `lo = -1` (lo+1 = 0) edge cases.
- `not_both_isOdd_fixedpoint` — XOR direction.
- **Applied in `_toOdd_satisfies` F.p = ⊤ case** ✓ closed.
- **Applied in `_toOdd_unique` F.p = ⊤ case** ✓ closed.

**Parity infrastructure now complete for floating-point case
(`F.exp = ⊥`)**:
- `Dyadic.two_pow_succ_pred` — `2^p = 2 · 2^(p-1)` for `p ≥ 1`.
- `Dyadic.isRepresentableAtP_of_saturation` — renormalize `|c| = 2^p`
  to canonical `(c/2, e+1)` form.
- `isOdd_iff_odd_at_canonical_floating` — `F.IsOdd (k · 2^e) ↔ Odd k`
  when `|k| ∈ [2^(p-1), 2^p)` (non-saturation).
- `not_isOdd_at_saturation` — `¬ F.IsOdd (k · 2^e)` when `|k| = 2^p`.
- `alternating_parity_floating` — `¬ F.IsOdd dlo → F.IsOdd dhi`
  at canonical exponent for `F.exp = ⊥, F.p ≠ 1`. **Keystone**.

**Now needed to finish `_toOdd` satisfies**:
1. Alternating-parity lemma: at canonical `e`, exactly one of
   `IsOdd dlo`, `IsOdd dhi` holds. Proof structure:
   - Non-saturation case (`|lo| < 2^p` AND `|lo+1| < 2^p`):
     `isRepresentableAtP_of_bounds` gives canonical forms.
     `isOdd_iff_odd_of_canonical` reduces to `Odd lo` vs
     `Odd (lo+1)` — these alternate trivially.
   - Saturation case (`|lo| = 2^p` for `x < 0`; `|lo+1| = 2^p`
     for `x > 0`): need renormalization
     (`y = c · 2^e = (c/2) · 2^(e+1)`) — the `c/2` has even
     significand (`±2^(p-1)`), so the saturated side is Even.
     The non-saturated side (`lo = ±(2^p − 1)`) is Odd.
2. Handling for `F.p = ⊤` (`F.exp = (e' : ℤ)`) case — different
   `numDigits` formula.
3. Handling for `F.p = 1` parity case (exponent-index parity).

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
