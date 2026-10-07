# Special values: total rounding with ±Inf, NaN and overflow

Implementation plan. The design is settled; what follows is the phase
breakdown, one phase per commit.

## Working policy

- **Pause after each phase for review.** Do not begin the next phase until the
  current one has been looked at.
- **Do not commit.** The author of the change leaves the working tree dirty;
  commits are made by the repository owner.
- **Build only what the phase touches.** Each phase lists the modules to build
  (`lake build Mpfx.<Module> …`). The full `lake build` runs once, after the
  last phase. Never run two builds at once (memory).
- **Comments stay succinct**, and notes about *process* (what was tried, what
  a phase decided, why an ordering was chosen) belong in this document, not in
  source comments.

## Context

### What exists

Rounding a real is specified in two layers:

| Symbol | File | Meaning today |
| --- | --- | --- |
| `RoundsFinite F rm x y` | `Rounding/Defs.lean` | `y ∈ F` is the mode-`rm` rounding of `x` (no bound check) |
| `RoundResult` | `Rounding/Defs.lean` | `finite d \| overflow (positive : Bool) \| undefined` |
| `Rounds F rm x r` | `Rounding/Defs.lean` | `r` is *the* result: undefined iff `F.IsUndefined rm`; else the unbounded rounding `y`, `.finite y` if `y` fits `F.b`, `.overflow (0 < y)` if not |
| `rnd F rm x` | `Rounding/Op/Defs.lean` | the function; `rnd_iff_rounds` (`Rounding/Op.lean`) |
| `Rounds.neg_*` | `Rounding/Basic.lean` | sign symmetry of `Rounds` over `RoundResult.neg` |
| `roundsRTZ_RTZ`, …, `roundsRTO_RN` | `DoubleRounding/Total.lean` | total double rounding: "direct rounding overflows, **or** the chain is finite and agrees" |
| `Format` | `Format/Defs.lean` | `𝒜(p, exp, b)`; `Membership Dyadic Format` |
| `Format.Subset`, `ContainsPrec`, `ContainsSub`, `subset_iff_contains` | `Format/Containment.lean` | §5.1 containment over `Dyadic` membership |

### What is missing

| Input / event | Today | Wanted |
| --- | --- | --- |
| `x : ℝ`, fits the bound | `.finite d` | `.value (.finite d)` |
| `x : ℝ`, unbounded rounding exceeds `b` | `.overflow s`, no value | `.value (O s)`: format-chosen, e.g. ±Inf, ±MAX, NaN |
| `+Inf`, `−Inf`, `NaN` input | not expressible | `.value (S s)`: format-chosen |
| format contains Inf / NaN | not expressible | `F.specials` |
| `(p = 1, exp = ⊥, RTO/RNE)` | `.undefined` | `.undefined` (kept) |

Overflow being an outcome rather than a value is also why every total
double-rounding theorem carries an "overflows" disjunct.

## Design

### Settled decisions

1. **Specials are values; overflow is an event.** ±Inf and NaN are inputs and
   outputs. Overflow is something that happens to a real input; it never
   appears as a value.
2. **`Format` gets a fourth field**, `specials : Set Special`, with no default:
   every format states its specials. No separate `ExtFormat`.
3. **Containment includes specials** (option (b)): `F₁ ⊆ F₂` requires
   `F₁.specials ⊆ F₂.specials`. `ContainsPrec`, `ContainsSub`, `containsPrec`,
   `containsSub` and `subset_iff_contains` gain that conjunct.
4. **Sign Bools are named `negative`** everywhere (`Special.inf`,
   `OverflowMap`), matching the IEEE sign bit.
5. **Two lookup tables**, split by concern: `SpecialMap` (where special inputs
   go) and `OverflowMap` (where overflow goes, keyed by sign). Both are
   parameters of `rnd`, independent of the rounding mode; a table follows the
   mode only when it is built to, as `OverflowMap.ieee rm` is (RTP sends
   `+ovf` to +Inf but `−ovf` to −MAX).
6. **`RoundResult` loses `finite`/`overflow`, keeps `undefined`.** Overflow
   survives as the predicate `Overflows`, because saturating tables make it
   unobservable from the output while double rounding conditions on it.

### Types and names

```lean
inductive Special | inf (negative : Bool) | nan

inductive WithSpecial (α : Type) | finite (a : α) | special (s : Special)

structure Format where
  p : Prec
  exp : QExp
  b : Bound
  specials : Set Special

-- .finite d ∈ F.values ↔ d ∈ F;  .special s ∈ F.values ↔ s ∈ F.specials
def Format.values (F : Format) : Set (WithSpecial Dyadic)

def Overflows (F : FiniteFormat) (rm : RoundingMode) (x : ℝ) : Prop :=
  ∃ y, RoundsFinite F.unbounded rm x y ∧ ¬ Format.boundOK F.b y

structure SpecialMap (F : Format) where
  map : Special → WithSpecial Dyadic
  mem : ∀ s, map s ∈ F.values

structure OverflowMap (F : Format) where
  map : Bool → WithSpecial Dyadic          -- keyed by `negative`
  mem : ∀ b, map b ∈ F.values

inductive RoundResult | value (v : WithSpecial Dyadic) | undefined

rnd F S O rm : WithSpecial ℝ → RoundResult
--   .finite x     ↦ .undefined                  if F.IsUndefined rm
--              ↦ .value (O.map (y < 0))      if Overflows F rm x (y the unbounded rounding)
--              ↦ .value (.finite y)
--   .special s ↦ .value (S.map s)
```

`Rounds F S O rm v r` is the relational form, and `rnd_iff_rounds` keeps its
role.

| Name | Meaning |
| --- | --- |
| `FiniteFormat.maxFinite F hb` | largest member of a bounded `F` (`hb : F.b ≠ ⊤`) |
| `SpecialMap.exact` | Inf ↦ Inf, NaN ↦ NaN; needs both in `F.specials` |
| `SpecialMap.saturate`, `SpecialMap.toNaN` | Inf ↦ ±`maxFinite`; everything ↦ NaN |
| `OverflowMap.ieee rm` | IEEE 754 §7.4: RNE/RNA ±Inf; RTZ ±MAX; RTP +Inf/−MAX; RTN +MAX/−Inf; RAZ/RTO ±Inf |
| `OverflowMap.saturate`, `OverflowMap.toNaN` | ±`maxFinite`; NaN |
| `OverflowMap.neg` | swaps the two entries; the sign-symmetry lemmas need it (RTP ↔ RTN) |

### Double rounding after the change

The total theorems become equalities, `rnd₁ (rnd₂ x) = rnd₁ x`, under
table-compatibility side conditions. Example: if `O₂` sends overflow to
`+Inf`, then `S₁ (.inf false)` must equal `O₁ false`. The existing
no-overflow propagation lemmas in `Total.lean` become the non-overflow case.

## Phases

### Phase 1: special-value types and the `Format.specials` field

**Done.** Diverged from the plan in two ways:

- **No `Membership (WithSpecial Dyadic) Format` instance.** `Membership`'s
  element type is an `outParam`, so a second instance on `Format` clashes with
  `Membership Dyadic Format` (tested: `.finite 3 ∈ F` fails to elaborate). Values
  are `Format.values F : Set (WithSpecial Dyadic)`, written `v ∈ F.values`,
  with `simp` lemmas `finite_mem_values` and `special_mem_values`.
- **No default for `specials`** (owner's call). The eight from-scratch
  constructions state it: `Format.extend` keeps `F.specials`; `opMul`, `opAdd`,
  the literal in `mem_unbounded_of_le` and the four counterexample formats use
  `∅`.

Also added `simp` lemmas `unbounded_specials`, `extend_specials`,
`withBound_specials`. `Subset` is unchanged.

The counterexamples broke: `eq_F₁_g` and its three siblings identified an
arbitrary unbounded `F₁` with a concrete format, and the concrete formats have
`specials := ∅`. They are replaced by `AnchorNeighborhood.transport`
(`Counterexample/Neighborhood.lean`), which moves a neighborhood between formats
agreeing on `p`, `exp`, `b`, using the new `Format.mem_congr` and
`IsOdd.congr`/`IsEven.congr`. The ten `no_rnd*` theorems keep their statements
and now hold for any `F₁.specials`.

### Phase 2: containment includes specials

**Done.** Diverged from the plan:

- **No mass `hsub.mem` rewrite.** A `CoeFun (F₁ ⊆ F₂)` instance applies a
  subset proof to a numeric member, so the ~150 `hsub y hy` sites compile
  unchanged; only tactic `apply hsub` became `apply hsub.mem` (4 sites).
- Subset proofs are built with the new `Format.subset_of_mem hs fun y hy => …`
  (specials first, so tactic proofs keep their shape). About 20 sites in
  `Format/Next`, `DoubleRounding/{Basic,Nearest,Total}`; their specials come
  from the hypothesis they already use (`hsub.specials`), definitionally equal
  through `extend`/`withBound`/`unbounded`.
- `subset_unbounded_of_le` gained a specials hypothesis;
  `AnchorNeighborhood.transport` gained `hs : G.specials ⊆ F.specials`
  (`Set.empty_subset _` at its four uses).

- `Format/Containment.lean`: `Subset` becomes a structure,
  `mem : ∀ x : Dyadic, x ∈ F₁ → x ∈ F₂` plus `specials : F₁.specials ⊆ F₂.specials`.
  `ContainsPrec`/`ContainsSub` gain the conjunct; `containsPrec`,
  `containsSub`, `subset_iff_contains`, `self_subset_extend`,
  `subset_unbounded_of_le`, `b_le_of_subset`, `exp_le_of_subset` are updated.
- About 150 applications `hsub y hy` across `Format/*`, `Rounding/*` and
  `DoubleRounding/*` become `hsub.mem y hy`; subset proofs written as
  `intro y hy` become `⟨fun y hy => …, specials⟩`.
- `Format/Next.lean`: the relaxed-bound lemmas
  (`extend_one_subset_of_withBound_subset`, …) carry `specials` through.
- `AnchorNeighborhood.transport` derives `G ⊆ F₂` from `F ⊆ F₂`; it now also
  needs `G.specials ⊆ F.specials`, which holds for the concrete formats (`∅`).

Separate because it is the only phase that changes the paper's §5.1
statements, and its churn is mechanical; mixing it with semantic changes would
hide them.

Build: `lake build` (the change reaches most modules).

### Phase 3: `Overflows`, and total theorems without `RoundResult.overflow`

**Done.** Diverged from the plan:

- Added `RoundsInBound F rm x y := RoundsFinite F.unbounded rm x y ∧
  boundOK F.b y` next to `Overflows` (`Rounding/Defs.lean`), so the six total
  theorems keep their shape: `Overflows F₁ rm₁ x ∨ ∃ z w, RoundsInBound … ∧ …`.
  Neither predicate carries `¬ IsUndefined`; the old `.finite` conjuncts did,
  and the proofs simply stopped re-packaging it.
- Bridges `rounds_finite_iff` and `exists_rounds_overflow_iff` relate them to
  the current `Rounds`; nothing uses them yet (Phase 5 may drop them).
- `rounds_withBoundFF_floor_iff` split into `overflows_withBoundFF_floor_iff`
  and `roundsInBound_withBoundFF_floor_iff`; `rounds_overflow_of_not_boundOK`
  is gone (its only users were here). `Total.lean` no longer mentions `Rounds`
  or `RoundResult`.

- `Rounding/Defs.lean`: add `Overflows`; prove
  `Rounds F rm x (.overflow b) ↔ ¬ F.IsUndefined rm ∧ Overflows F rm x ∧ …`
  against the *current* `Rounds`.
- `DoubleRounding/Total.lean`: restate `roundsRTZ_RTZ`, …, `roundsRTO_RN` with
  `Overflows F₁ rm x ∨ …` and numeric conclusions (`RoundsFinite` plus
  `boundOK`) instead of `Rounds … (.finite _)` / `(.overflow _)`.

Separate because it removes `Total.lean`'s dependence on `RoundResult` while
the old `Rounds` still exists, so Phase 5 can replace `RoundResult` without
touching 1400 lines of double-rounding proofs at the same time.

Build: `lake build Mpfx.Rounding.Defs Mpfx.DoubleRounding.Total`.

### Phase 4: lookup tables and `maxFinite`

**Done.** Decisions taken here:

- `FiniteFormat.maxFinite F hb` is the RTN rounding of `b` on `F`'s grid and
  requires `hb : F.b ≠ ⊤` (no junk value: saturating an Inf input in an
  unbounded format has no meaningful target). The tables built on it
  (`SpecialMap.saturate`, `OverflowMap.saturate`, `OverflowMap.ieee`) take `hb`.
  Lemmas `maxFinite_mem`, `maxFinite_nonneg`, `le_maxFinite`; `saturated F hb
  negative = .finite ±maxFinite`.
- `OverflowMap.ieee` covers all six modes: RAZ and RTO overflow to ±Inf like
  the nearest modes (owner's call; neither is an IEEE mode).
- `OverflowMap.neg` negates entries, so it needs `F.NegClosed` (specials
  closed under `Special.neg`). `Special.neg`, `WithSpecial.neg` and
  `Format.neg_mem_values` live in `Rounding/Special.lean` for now; Phase 5 may
  move the negations next to the types.
- `SpecialMap.exact` takes `∀ s, s ∈ F.specials`; `saturate`/`toNaN` need only
  NaN.

- New `Rounding/Special.lean`: `SpecialMap`, `OverflowMap`, `OverflowMap.neg`,
  `FiniteFormat.maxFinite`, and the instances `SpecialMap.exact`/`saturate`/
  `toNaN`, `OverflowMap.ieee`/`saturate`/`toNaN` with their membership proofs.
- `maxFinite` lemmas: membership, `≤ b`, maximality.

Separate because the definitions are independent of the `RoundResult` change
and their membership side conditions are where mistakes would show.

Build: `lake build Mpfx.Rounding.Special`.

### Phase 5: total `rnd` over `WithSpecial`

**Done.** Placement, chosen so each definition sits with its subject and the
import graph stays acyclic (`Rounds` needs the tables, so they cannot live in
`Rounding/Special.lean`, which imports `Rounding.Op`):

| What | Where |
| --- | --- |
| `Special.neg`, `WithSpecial.neg` (+ `simp`) | `Format/Defs.lean`, after the types |
| `Format.NegClosed`, `Format.neg_mem_values` | `Format/Defs.lean`, after `Format.neg_mem` |
| `SpecialMap`, `OverflowMap`, `OverflowMap.neg` | `Rounding/Defs.lean`, before `Rounds` |
| `RoundResult` (`value \| undefined`), `Rounds F S O rm` | `Rounding/Defs.lean` |
| `Rounds.neg_*`, `congr_of_roundsFinite`, mode equivalences | `Rounding/Basic.lean` |
| `rnd F S O rm` | `Rounding/Op/Defs.lean` |
| `rnd_iff_rounds`, `overflows_iff_not_roundsInBound` | `Rounding/Op.lean` (needs existence) |
| `maxFinite`, all standard tables | `Rounding/Special.lean` |

Other notes:

- `Rounds F S O rm (.finite x) (.value v)` has one witness `y` with
  `(boundOK ∧ v = .finite y) ∨ (¬ boundOK ∧ v = O.map (decide (y < 0)))`, so no
  decidability instance is needed in `Rounding/Defs`.
- The `Rounds.neg_*` lemmas take `hF : F.NegClosed` and use `O.neg hF` on the
  negated side. `Rounds.toNegative_iff_*` are now proved directly from their
  `RoundsFinite` counterparts instead of through a double negation.
- The Phase 3 bridges (`rounds_finite_iff`, `exists_rounds_overflow_iff`) are
  removed.

- `Rounding/Defs.lean`: `RoundResult` becomes `value | undefined`;
  `RoundResult.neg` negates through `WithSpecial`; `Rounds F S O rm v r`.
- `Rounding/Op/Defs.lean`, `Rounding/Op.lean`: `rnd F S O rm` and
  `rnd_iff_rounds`, with the overflow sign taken as `y < 0`.
- `Rounding/Basic.lean`: `Rounds.neg_congr`, `Rounds.neg_*` and the
  `Rounds.to*_iff_*` mode equivalences, using `OverflowMap.neg` for RTP ↔ RTN.
- Remove the Phase 3 bridge lemma if nothing uses it.

Separate because it is the semantic core: the definition of rounding changes,
and review should see that change alone.

Build: `lake build Mpfx.Rounding.Op Mpfx.Rounding.Basic`.

### Phase 6: sanity theorems for the standard tables

- `Rounding/Special.lean` (or a sibling): IEEE agreement for overflow, e.g.
  under `OverflowMap.ieee .nearest .toEven`, `Overflows F rm x` with `x > 0`
  gives `+Inf`; under RTZ gives `.finite maxFinite`. Specials under
  `SpecialMap.exact` are fixed points of `rnd`.

Separate because these are the regression net for Phases 4–5: they pin the
tables to IEEE 754 §7.4 before double rounding builds on them.

Build: `lake build Mpfx.Rounding.Special`.

### Phase 7: total double rounding as equalities

- `DoubleRounding/Total.lean`: for each rule, `rnd₁ (rnd₂ x) = rnd₁ x` for
  `x : WithSpecial ℝ`, under table-compatibility hypotheses, derived from the
  Phase 3 forms. Special inputs are a one-line case: `S₁ ∘ S₂` against `S₁`.
- State the compatibility conditions as named predicates so the IEEE instances
  can discharge them once.

Separate because it is new mathematics on top of a settled API; doing it
before Phase 6 would mean proving against tables that are not yet checked.

Build: `lake build Mpfx.DoubleRounding.Total`.

### Phase 8: documentation

- `README.md`: the theorem tables (total forms, containment conjunct),
  `#print axioms` output, layout row for `Rounding/Special.lean`.
- `docs/DESIGN.md`: `Format.specials`, the two tables, why overflow is a
  predicate.
- `docs/agents/TODO.md` layout tree; `ROADMAP.md`: the paper's 𝒜 gains a
  fourth parameter and §5.1 a specials conjunct.

Build: none (docs only).

### After the last phase

```sh
lake build                      # full build; linters run as part of it
```

Then `#print axioms` for every theorem in the README tables (expect
`propext`, `Classical.choice`, `Quot.sound`).

## Open items

Reviewed 2026-10-06: every provisional call below is accepted. Each stays
listed with the condition that would reopen it.

### Which specials does an inferred format get (`opMul`, `opAdd`)?

§6.1 inference builds the format of `x ∘ y`. With specials, `Inf · 0 = NaN`
and `Inf + (−Inf) = NaN`, so the honest answer depends on both operands'
specials. Phase 1 sets `∅`, which keeps `mul_subset`/`add_subset` (numeric
`toSet` statements) true but says nothing about special arithmetic.
Provisional: `∅`. Reopen if the paper's §6.1 is meant to cover specials.

### Is `.undefined` numeric-only?

Today `.undefined` depends only on `(F, rm)` and is returned for every real
input. Special inputs go through `S`, which never consults parity, so the
sketch keeps them defined. The other reading is that a degenerate
(format, mode) pair is undefined everywhere. Provisional: numeric-only.
Reopen if a double-rounding statement becomes awkward because of it.

### Are tables arbitrary, or constrained?

Arbitrary tables describe OCP E4M3, P3109 saturation and integer saturation.
But some entries are senseless, e.g. `S (.inf false) = .finite 0`, or
`O false = −MAX` for RTP. Constraints (e.g. "Inf input is exact when
`F.specials` has it", "positive overflow maps to something `≥ maxFinite`")
would make monotonicity and double rounding hold without per-theorem
hypotheses. Provisional: arbitrary tables, with constraints as named
predicates used as hypotheses. Reopen if the same hypothesis appears on most
Phase 7 theorems.

### Bundle `S` and `O`?

`rnd F S O rm` vs `rnd F P rm` with `P : Policy F`. Separate is clearer about
which table a condition constrains; bundled is shorter at call sites.
Provisional: separate. Reopen after Phase 7 if call sites are noisy.

### Is the overflow sign that of `x` or of the unbounded rounding `y`?

They agree whenever overflow fires (`y ≠ 0`, same sign as `x`), so this is
about which is easier to prove with. Provisional: `y < 0`, matching today's
`(b ↔ 0 < y)`. Reopen only if Phase 5 proofs need the other.

### `Set Special` or two `Bool`s?

A `Set` covers NaN-only formats (OCP E4M3) and future specials, but is not
decidable. Two `Bool`s (`hasInf`, `hasNaN`) are decidable but cannot express
`+Inf` without `−Inf`. Provisional: `Set Special`. Reopen if a computable
`rnd` or `decide`-based tests are wanted.

### Signed zero

IEEE distinguishes `−0` (e.g. `−tiny` rounds to `−0`). `Dyadic` cannot, and
the tables do not touch it. Provisional: out of scope. Reopen if IEEE fidelity
of zero results is needed, by adding `Special.zero (negative : Bool)` or a
signed `finite`.

### What happens to the paper's cited total forms?

Appendix A cites `roundsRTZ_RTZ`, …, `roundsRTO_RN` with the overflow
disjunct. Phase 3 changes their statements and Phase 7 adds equality forms.
Either keep the Phase 3 forms under their names (the paper's statement), or
retire them in favour of the equalities. Provisional: keep both until the
paper revision decides.
