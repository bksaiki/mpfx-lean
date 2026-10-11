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
2. **Explicit rounding.** Alongside the spec relation
   `Rounds F S O rm v r : Prop`, a function `rnd F S O rm v : RoundResult`
   (`S`, `O`: the special-value and overflow tables) computes the rounded value via `Int.log` + `Int.floor`/`Int.ceil`
   (FLoPS-style). No `Classical.choose` in the definition; it is
   `noncomputable` because real comparisons aren't computably
   decidable. Proofs are classical throughout (see `docs/DESIGN.md`).
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
├── Utils.lean        project-agnostic helpers: two_zpow_* power-of-two lemmas
│                     (the shift lemmas two_zpow_shift / coeff_eq_of_shift over
│                     any field of characteristic zero), log_abs_mul_zpow,
│                     sign helpers, format-free scaled-mantissa arithmetic
├── Dyadic.lean       IsDyadic (ℚ), Dyadic := subring of ℚ, ofIntZpow (computable),
│                     coe_real_* / coe_rat_ofIntZpow / ext_real bridge lemmas,
│                     DecidableEq instance,
│                     precisionAtMost, quantumAtLeast (both ℚ-valued) + mono/anti,
│                     precisionAtMost_coe_real / quantumAtLeast_coe_real (ℝ bridges),
│                     quantumAtLeast_neg/add/sub/mul/ofIntZpow, precisionAtMost_mul,
│                     abs_ge_two_zpow_of_quantum / le_log_of_quantum, Dyadic.abs,
│                     IsRepresentableAtP (ℚ) + unique + ne_zero,
│                     precisionAtMost_of_abs_le (saturation renormalization),
│                     isRepresentableAtP_of_log
├── Format/
│   ├── Defs.lean     Special, WithSpecial (+ neg, toReal), Format (with
│   │                 specials) / FiniteFormat, Mem, Format.values, NegClosed,
│   │                 boundOK, Format.unbounded, FiniteFormat.unbounded,
│   │                 FiniteFormat.zero_mem, FiniteFormat.canonicalExp with
│   │                 canonicalExp_le_iff and the closed forms (canonicalExp_closed,
│   │                 _expBot, _expFinite, _pTop, _neg, …), the representation
│   │                 exists_mul_zpow_canonicalExp and its converse
│   │                 mem_unbounded_of_mul_zpow_canonicalExp,
│   │                 numDigits (= ⌊log₂|x|⌋ + 1 − canonicalExp x)
│   ├── Parity.lean   ParityFormat, IsOdd, IsEven, negation, transport
│   │                 (IsOdd/IsEven.congr, *_iff_of_toFormat_eq,
│   │                 parity_witness_congr); isOdd/isEven_iff_canonical, the
│   │                 shrink characterization isEven/isOdd_iff_mem_shrink,
│   │                 ofIntZpow_mem_shrink_iff (alternation), the p = 1 forms
│   │                 is{Odd,Even}_ofIntZpow_of_p_one, isEven_of_subset,
│   │                 exp_eq_canonicalExp_of_p_one, IsOdd.transfer_of_subset
│   │                 (RTO-padding lemma)
│   ├── Containment.lean §5.1: Format.Subset (numeric members and specials)
│   │                 + HasSubset, subset_of_mem, Subset.trans,
│   │                 FiniteFormat.subset_unbounded,
│   │                 boundOK_mono, nnPow, containsPrec, containsSub,
│   │                 subset_iff_contains (completeness),
│   │                 Format.extend + self_subset_extend + extend_mono,
│   │                 extend_p / extend_exp_coe / extend_exp_bot, extend_extend,
│   │                 FiniteFormat.extend + numDigits_extend (digit-shift lemma),
│   │                 shrink (inverse of extend 1) + canonicalExp_shrink,
│   │                 mem_shrink_of_subset
│   ├── Next.lean     withBound (+ withBound_mono), next (+ next lemmas), boundAfterNext — §5.2
│   │                 bound API; containment with a relaxed bound:
│   │                 extend_{one,two}_subset_of_withBound_subset,
│   │                 two_le_p_or_trivial_of_extend_{one,two}_withBound_subset
│   ├── Discrete.lean canonical representation and midpoint membership
│   │                 (prereq for roundsRTO_RN_finite): exists_canonical_rep(_of_parts),
│   │                 midpoint_mem_extend_one_of_adjacent(_pos), half_mem_extend_one,
│   │                 midpoint_in_F₁_extend_one_of_F_adjacent; quantum_floor/ceil_of_mem,
│   │                 binade_quantum
│   ├── CanonicalExp.lean floor_minimality,
│   │                 ofIntZpow_mem_unbounded, floor_mantissa_lt
│   └── Inference.lean §6.1: ⊗/⊕ format inference. IEEE 754 *, +, -, abs on
│                     WithSpecial Dyadic; Format.toSet, opMul/opAdd/opAddPrec,
│                     opNeg/opAbs, mul/add/absSpecials (+ special_mem_op*_iff:
│                     exactly the produced specials); mul/add/neg/abs_subset over
│                     values, *_subset_finite over toSet; opNeg_of_negClosed.
├── Rounding/
│   ├── Defs.lean     relational layer:
│   │                 TieBreak, RoundingMode,
│   │                 RoundResult (value | undefined),
│   │                 FiniteFormat.IsUndefined, SpecialMap, OverflowMap,
│   │                 IsFaithfulRound, RoundsFinite, RoundsInBound, Overflows,
│   │                 Rounds,
│   │                 FiniteFormat.toParityFormatOf{ToOdd,NearestEven}
│   ├── Basic.lean    relational consequences of the spec. Sign symmetry:
│   │                 IsFaithfulRound.neg_iff, per-mode RoundsFinite.neg_*.
│   │                 Mode-vs-sign: RTP/RTN ↔ RTZ/RAZ by sign of x.
│   │                 RoundsFinite.self (every mode), uniqueness per mode and
│   │                 generic, isFaithfulRound, eq_of_mem, eq_zero_of_zero,
│   │                 IsFaithfulRound.eq_or_eq, opposite_sides_of_ne, of_subset,
│   │                 same_side, iff_of_between (shared neighbours), the grid
│   │                 bridges toNegative_floor/toPositive_ceil/
│   │                 toPositive_floor_add_one (+ equation forms), the nearest
│   │                 modes between round-down and round-up
│   │                 (nearest_toEven_of_bracket, nearest_awayZero_of_bracket),
│   │                 isOdd_alternate_of_bracketing, sign and magnitude of a
│   │                 faithful rounding (decide_lt_zero, mul_nonneg,
│   │                 abs_faithful_le_of_le, le_abs_faithful_of_le),
│   │                 ne_zero_of_not_boundOK, nearest_min. Mentions no
│   │                 construction.
│   ├── Restrict.lean restrict/lift between RoundsFinite F and F.unbounded for
│   │                 every mode (RoundsFinite.restrict / RoundsFinite.lift)
│   ├── Parity.lean   neighbors_alternate: adjacent values alternate in
│   │                 parity
│   ├── Op.lean, Op/  function layer (noncomputable):
│   │                 rndInt, rndParity, rndUnbounded (+ rndUnbounded_of_ne and
│   │                 the parity-mode equations), rnd, per-mode soundness,
│   │                 rndUnbounded_satisfies/_unique, rnd_iff_rounds,
│   │                 rnd_special, rnd_of_overflows
│   ├── Special.lean  maxFinite (+ abs_le_maxFinite, saturated_eq_finite), the
│   │                 standard tables: SpecialMap.exact/saturate/toNaN,
│   │                 OverflowMap.ieee/saturate/toNaN
│   └── Ulp.lean      ulp/rndDown/rndUp/midp, the nearest error bound and the
│                     below/above-midpoint characterisations
└── DoubleRounding/
    ├── Basic.lean    §5.2 rules, spec-relational over RoundsFinite:
    │                 roundsRTN_RTN_finite, roundsRTP_RTP_finite, and RTZ/RAZ from
    │                 them by sign (toZero_of_directed, awayZero_of_directed);
    │                 roundsRTO_RTO_finite; roundsRTO_RTN/RTP_finite(_of_extend), and
    │                 RTO → RTZ/RAZ from them; toOdd_notMem_of_extend_subset, rndExact
    ├── Nearest.lean  roundsRTO_RN_finite(_of_extend), from shared neighbours,
    │                 the midpoint of two faithful roundings, and same-side
    │                 (midpoint_mem_extend_one_of_faithful, closer_of_same_side)
    ├── Total.lean    LocalDoubleRounding (+ .inBound, .not_overflows), BelowValue,
    │                 localDoubleRounding_of_below/_of_above, exists_mem_above; the
    │                 RTO → RN midpoint facts (abs_le_mid_of_nearest,
    │                 abs_le_of_nearest_of_abs_lt_mid, abs_ne_of_toOdd);
    │                 roundsRTZ_RTZ_inBound, …, roundsRTO_RN_inBound and *_noOverflow
    │                 from per-rule instances; roundsRTZ_RTZ_agree, …: agreement in
    │                 bound, plain containment
    ├── Special.lean  rules with tables: rndRTZ_RTZ, …, rndRTO_RN and *_of_bound;
    │                 rnd_double, SpecialMap/OverflowMap.Composes, OverflowAgrees
    │                 (+ of_bound, of_saturate), the standard tables' composition
    ├── Counterexample.lean Cex.no_rounds* (Disagrees witnesses), Cex.no_rnd*
    │                 (on rnd, via Disagrees.rnd_ne)
    ├── Counterexample/ Basic: format-generic grid facts (Isolated,
    │                 exists_isolated, Adjacent, exists_pred, alternate_of_adjacent,
    │                 roundings near an isolated value, roundsRNE_of_bracket)
    ├── NearestMidpoint.lean Roux Lemma 16: rnd_lt_mid(')
    ├── Mul.lean      Roux ×: rndMul_expBot/_expFinite
    ├── Add.lean      Roux +/−: rndAdd
    ├── Sqrt.lean     Roux √: rndSqrt_expBot/_expFinite
    └── Div.lean      Roux /: rndDiv_expBot/_expFinite
MpfxTest/             `lake test` examples
├── SpecialValues.lean the tables against IEEE 754 §7.4, special inputs
└── DoubleRounding.lean IEEE double rounding with tables; RTO → RTZ and
                      RTO → RN failures
```

## Open: Rounding API extensions

- [ ] `IsFaithfulRound`-extraction lemmas (split RTN-witness vs
      RTP-witness disjunct accessors).

## Open: New features

- [ ] **Paper format instances**: `binary64`, `binary32`, `E5M2`,
      `E4M3`, `int8`, `fixed<-4, 8>`. Concrete `FiniteFormat` or
      `ParityFormat` values; useful as smoke tests.
- [ ] **Smoke tests** (in `MpfxTest/`): concrete
      `rnd F S O rm (.finite x) = .value (.finite y)` proofs. Since `rnd` is
      `noncomputable`, these are equational proofs, not `#eval`.
      *Computable-mirror option*: define `rndQ F S O rm : ℚ → RoundResult`
      for rational inputs and prove
      `rndQ F S O rm q = rnd F S O rm (.finite (q : ℝ))`, then close concrete tests by
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

The full cleanup plan, from a review of the whole development, is in
[`CLEANUP.md`](CLEANUP.md).

- [ ] **Optional `Coe FiniteFormat Format` instance** — would let `⊆`/
      `withBound`/`boundAfterNext` drop their explicit `.toFormat` too. Add
      only if that noise becomes overwhelming.
- [ ] **Per-file module docstrings** + paper-reference cross-links (`README`
      is done; individual file headers could still gain `§`-references).
- (Considered, not done: de-`change`-ing `Rounding/Op/` — its ~60 `change`s
  are legitimate definitional unfolds of `canonicalExp`/`rndInt`/arithmetic,
  not the `.toFormat` pattern; removing them needs per-def unfold lemmas with
  no real payoff.)

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

## Open: special values (provisional calls)

Each stands until its reopen condition holds.

- [ ] **Names** in `DoubleRounding/Special.lean`: `OverflowAgrees` and its
      fields `direct`/`chain`/`inner`, `of_bound`, `of_saturate`, the
      `…_agree` and `…_of_bound` families.
- [ ] **IEEE RTO overflow** goes to `±Inf` (`OverflowMap.ieee`), which is what
      makes RTO → RTZ fail to compose. Saturating it would make RTO → RTZ
      compose (`MpfxTest/DoubleRounding.lean`).
- [ ] **Unchecked:** RTO → RN with a saturating RTO table and the IEEE RN
      table. By hand, `b₂ ≥ M` is still needed.
- **`.undefined` is numeric-only**: special inputs always go through `S`.
  Reopen if a double-rounding statement becomes awkward because of it.
- **Tables are arbitrary**, with constraints as named predicates. Reopen if
  the same predicate appears on most theorems.
- **`S` and `O` are separate parameters**, not a bundled policy. Reopen if
  call sites are noisy.
- **The overflow sign is that of the unbounded rounding `y`** (`y < 0`). It
  equals that of `x` whenever overflow fires.
- **`specials : Set Special`**, not two `Bool`s. Reopen if a computable `rnd`
  or `decide`-based tests are wanted.

## Documented non-theorems / possible extensions

- `rndRNA_RNA` is **not** correct double rounding — RNA→RNA chains can fail at
  binade-boundary inputs (pen-and-paper). A counterexample analogous to
  `no_rndRNE_RNE` could be formalized.
- `rndRTE_RTE` (round-to-even, the dual of RTO) is **not** a theorem either.

## Long-term / out of scope

- Subnormal flushing and signed zero (paper §9). `±Inf`, NaN and overflow
  tables are done (`Format.specials`, `SpecialMap`, `OverflowMap`).
- Posits, P3109 unsigned floats.
- Stochastic rounding modes (FLoPS does these; not needed for
  *When Double Rounding is Correct*).
