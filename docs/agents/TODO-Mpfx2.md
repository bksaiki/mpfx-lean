# Mpfx2 TODO

A parallel re-implementation of the formalization in `Mpfx2/`, exploring
two design changes from `Mpfx/`:

1. **Looser top-level type.** `Format` encodes only the natural
   type-level constraints (`p ≥ 1` via `WithTop ℕ+`, `b ≥ 0` via
   `WithTop NonNegDyadic`). The non-degeneracy invariant lives on a
   subtype, `FiniteFormat extends Format`. Most theorems target the
   loose `Format`; only those that actually use non-degeneracy promote
   to `FiniteFormat`.
2. **Constructive rounding.** Alongside the spec relation
   `Rounds F rm x y : Prop`, a function `rnd F rm x : RoundResult`
   computes the rounded value via `Int.log` + `Int.floor`/`Int.ceil`
   (FLoPS-style). No `Classical.choose`. The function is
   `noncomputable` only because `Int.log : ℝ → ℤ` is.

The unified `Rounds`/`rnd` API is connected by bridge lemmas
`rnd_eq_finite_iff_rounds_*` per mode.

Status legend: `[ ]` not started · `[~]` in progress · `[x]` done · `[!]` blocked.

## File layout

```
Mpfx2/
├── Utils.lean      # project-agnostic helpers (two_zpow_pos, etc.)
├── Dyadic.lean     # IsDyadic, Dyadic subring, ofIntZpow,
│                   #   precisionAtMost, quantumAtLeast
├── Format.lean     # NonNegDyadic, Format, boundOK, Mem,
│                   #   FiniteFormat
└── Rounding.lean   # TieBreak, RoundingMode, RoundResult,
                    #   IsUndefined, IsOverflow, Rounds, rnd,
                    #   IsFaithfulRound, IsOdd, IsEven (opaque)
```

## Substrate (done)

- [x] `IsDyadic` predicate + closure (`zero`, `one`, `add`, `neg`, `mul`).
- [x] `dyadicSubring`, `Dyadic` abbrev.
- [x] `Dyadic.ofIntZpow`, `coe_ofIntZpow`.
- [x] `Dyadic.precisionAtMost : WithTop ℕ+ → Dyadic → Prop`.
- [x] `Dyadic.quantumAtLeast : WithBot ℤ → Dyadic → Prop`.
- [x] `NonNegDyadic := { d : Dyadic // 0 ≤ (d : ℝ) }`.
- [x] `Format` (`p : WithTop ℕ+`, `exp : WithBot ℤ`, `b : WithTop NonNegDyadic`).
- [x] `Format.boundOK`, `Format.Mem`, `Membership Dyadic Format`.
- [x] `FiniteFormat extends Format` with `wf` invariant.

## Rounding scaffold (done)

- [x] `TieBreak` (`toEven`, `awayZero`).
- [x] `RoundingMode` (six constructors).
- [x] `RoundResult` (`finite`, `overflow`, `undefined`).
- [x] `Format.IsUndefined` (covers `(⊤, ⊥, _)` and `(1, ⊥, .toOdd)`).
- [x] `Format.IsOverflow`.
- [x] Constructive `Format.canonicalExp` (via `Int.log`).
- [x] Constructive `rndInt` for directed modes (`toNegative`, `toPositive`,
      `toZero`, `awayZero`).
- [x] Constructive `rnd : Format → RoundingMode → ℝ → RoundResult` (no
      `Classical.choose`).
- [x] `IsFaithfulRound := Rounds .toNegative ∨ Rounds .toPositive`.

## Open: directed-mode soundness (P0)

Eight `sorry`s in `Mpfx2/Rounding.lean`. Each pair `(_unique,
_satisfies_rounds)` is the workhorse for one directed mode.

- [ ] `rounds_toZero_unique`.
- [ ] `rnd_toZero_satisfies_rounds`.
- [ ] `rounds_toNegative_unique`.
- [ ] `rnd_toNegative_satisfies_rounds`.
- [ ] `rounds_toPositive_unique`.
- [ ] `rnd_toPositive_satisfies_rounds`.
- [ ] `rounds_awayZero_unique`.
- [ ] `rnd_awayZero_satisfies_rounds`.

Dependencies: each `_satisfies_rounds` proof needs to discharge the
three membership clauses (`precisionAtMost`, `quantumAtLeast`,
`boundOK`) at the constructed value plus the mode-specific minimality
clause. Suggested first target: `rnd_toZero_satisfies_rounds`. Once
solved, the other three directed modes follow by renaming +
floor↔ceiling.

## Open: parity machinery (P1)

`IsOdd` and `IsEven` are currently `opaque` placeholders. Concrete
definitions need supporting infrastructure.

- [ ] Port `Dyadic.IsRepresentableAtP` from `Mpfx/Dyadic.lean`.
- [ ] Define `Format.numDigits : Format → ℝ → ℤ` (Lemma 5.1 form).
- [ ] Replace `opaque IsOdd` with the canonical-significand definition.
- [ ] Replace `opaque IsEven` with the canonical-significand definition
      (handle `y = 0` as the even base case).
- [ ] Port the basic API: `IsOdd.neg`, `IsEven.neg`, `IsOdd.ne_zero`,
      `precisionAtMost_not_IsOdd` (Lemma 5.3 corollary).

## Open: parity-mode rounding (P2)

Once parity is real, three more modes come online.

- [ ] Extend `Rounds` to `.toOdd`: `IsFaithfulRound F x y ∧ (x ≠ y → IsOdd F y)`.
- [ ] Extend `Rounds` to `.nearest .toEven`: faithful + closeness + tie
      breaks to even.
- [ ] Extend `Rounds` to `.nearest .awayZero`: faithful + closeness + tie
      breaks to larger magnitude.
- [ ] Extend `rndInt` to `.toOdd` and `.nearest _`. Requires identifying
      the F-adjacents (not just the floor/ceiling of the scaled
      mantissa) and choosing per the parity/tie-break rule.
- [ ] Bridge-lemma triples (`_unique`, `_satisfies_rounds`, iff) for
      `.toOdd`, `.nearest .toEven`, `.nearest .awayZero`.

## Open: double-rounding theorems on `=` (P3)

Restate the Mpfx theorems using `rnd … = .finite …` rather than
`Rounds … x y`.

Positive (Fig. 9):

- [ ] `rndRTZ_RTZ`.
- [ ] `rndRAZ_RAZ`.
- [ ] `rndRTO_RTO` (both `_O` and `_E` clauses).
- [ ] `rndRTO_RTZ`.
- [ ] `rndRTO_RAZ`.
- [ ] `rndRTO_RN` (both tie-breaks).

Counterexamples (`Mpfx/DoubleRoundingCex.lean`, ten cases):

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

The witness-construction in each counterexample carries over; what
changes is the conclusion shape (`rnd … ≠ rnd …` rather than a triple
`Rounds`-conjunction).

## Open: ergonomics (P4)

- [ ] `Format.toFiniteFormat` projection / `Coe FiniteFormat Format` —
      decide whether to add the coercion. Mathlib idiom is *not* to
      auto-coerce; calls write `.toFormat` explicitly. Pick a side
      project-wide.
- [ ] `@[simp]` lemmas bridging `F.toFormat.p = F.p` (etc.) for proofs
      working on `FiniteFormat`.
- [ ] Smoke tests in `Mpfx2/Tests.lean`: Fig. 7 formats instantiated
      and basic membership / rounding checks. Requires the directed-mode
      soundness sorries to be discharged first.

## Open: optional, FLoPS-style generalization (P5)

- [ ] `class Faithful (rndInt : ℤ → ℝ → ℤ)` — `rndInt e r ∈ {⌊r⌋, ⌈r⌉}`.
- [ ] `class Monotonic (rndInt : ℤ → ℝ → ℤ)`.
- [ ] `class ValidRound` extending both.
- [ ] Mode-agnostic facts proven once at the typeclass level (e.g.,
      monotonicity of `rnd` in `x`, idempotence on in-format inputs).
- [ ] `to_rndInt : RoundingMode → (ℤ → ℝ → ℤ)` dispatcher with
      per-mode `[ValidRound]` instances.

## Out of scope (paper §9)

- Subnormal flushing, signed zero, ∞, NaN.
- Overflow semantics for double rounding under saturation modes.
- Posits, P3109 unsigned floats.
- Stochastic rounding modes (FLoPS does these; not needed for the
  *When Double Rounding is Correct* paper).
