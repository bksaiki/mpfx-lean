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
| `roundsRTZ_RTZ_inBound`, …, `roundsRTO_RN_inBound` | `DoubleRounding/Total.lean` | total double rounding: "direct rounding overflows, **or** the chain is finite and agrees" |
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
- `DoubleRounding/Total.lean`: restate `roundsRTZ_RTZ_inBound`, …, `roundsRTO_RN_inBound` with
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

**Done.** Split between the library and a new test library:

- Library (`Rounding/Op.lean`, next to `rnd_iff_rounds`): `rnd_special`
  (`simp`), `rnd_of_overflows_pos` / `rnd_of_overflows_neg` — for any tables,
  a defined mode and an overflowing real select `O.map false` / `O.map true`.
  Phase 7 builds on these.
- Tests (`MpfxTest/SpecialValues.lean`, a new top-level `MpfxTest` lib in
  `lakefile.toml` with `testDriver`, as Mathlib's `MathlibTest`; CI runs
  `lake test`):
  `example`s pinning `OverflowMap.ieee` to IEEE 754 §7.4 for RNE/RNA, RTZ,
  RTP and RTN on both signs, `OverflowMap.saturate`/`toNaN`, and special inputs
  under `SpecialMap.exact`/`saturate`/`toNaN` (including an undefined mode).
  Kept as examples rather than library theorems, since each is the table
  definition read back through `rnd`.

- `Rounding/Special.lean` (or a sibling): IEEE agreement for overflow, e.g.
  under `OverflowMap.ieee .nearest .toEven`, `Overflows F rm x` with `x > 0`
  gives `+Inf`; under RTZ gives `.finite maxFinite`. Specials under
  `SpecialMap.exact` are fixed points of `rnd`.

Separate because these are the regression net for Phases 4–5: they pin the
tables to IEEE 754 §7.4 before double rounding builds on them.

Build: `lake build Mpfx.Rounding.Special`.

### Phase 7: total double rounding as equalities

**Split into 7a–7c.** Two findings while starting:

- **The Phase 3 forms are not enough.** They give "direct overflows ∨ chain in
  bound and agrees", which says nothing about the chain when the direct
  rounding overflows but `F₂` does not. Each rule also needs the way back (`*_noOverflow`):
  if the chain stays in bound, so does the direct rounding
  (`roundsRTZ_RTZ_noOverflow`, …). This is new per-rule mathematics, mirroring the
  no-overflow propagation in `Total.lean`.
- **`F₁` must be nontrivial.** For `F₁ = {0}` (`exp = ⊥`, `b₁ = 0`) and
  `F₂ = 𝒜(p, 0, ∞)`, `x = 0.5` rounds RTZ to `0` through the chain but
  overflows directly. The equalities take `F₁.toFormat.Nontrivial` (§4.2).

**7a. Done.** Framework and RTZ → RTZ end to end:

- `WithSpecial.toReal` (`Format/Defs`), `IsFaithfulRound.decide_lt_zero`
  (`Rounding/Basic`: a nonzero faithful rounding has the sign of `x`),
  `rnd_finite_of_roundsFinite` (`Rounding/Op`: `rnd` read off any witness).
- `roundsRTZ_RTZ_noOverflow` (`Total.lean`), with its regular-bound core next to
  the RTZ propagation lemmas and the same grid-floor reduction.
- New `DoubleRounding/Special.lean`: `SpecialMap.Composes`,
  `OverflowMap.Composes`, the generic `rnd_double` (from a rule's total form,
  its no-overflow form and composing tables), and `rndRTZ_RTZ`.
- `Total.lean` is now 1506 lines; 7b splits it (the grid-floor reduction is
  the natural cut) before adding the other rules.

**7b. Done.** The remaining five rules:

- `Total.lean` split: per-rule propagation moved to the new
  `DoubleRounding/Propagation.lean` (no-overflow lemmas, now with
  `*_noOverflow_direct` cores); `Total.lean` keeps the grid-floor reduction, the
  total forms and the new `rounds*_noOverflow` theorems (lifted through
  `not_overflows_of_floor`).
- Naming: `*_noOverflow_F₂` / `*_noOverflow_chain` (direct in bound ⇒ F₂ /
  chain in bound) are joined by `*_noOverflow_direct` (chain in bound ⇒ direct
  in bound); the public forms are `roundsRTZ_RTZ_noOverflow`, ….
- Arguments per rule: RTZ outer modes need `next(b₁) ∈ F₂` (`|z| < next(b₁)` pins
  `|x|`); RAZ → RAZ needs no hypotheses (the chain's `w` is a candidate for the
  direct RAZ); RTO → RAZ uses padding to make `w` a candidate; RTO → RTO pins
  `|x| < next(b₁)` and composes the finite rule at `G = F₁.withBound next(b₁)`;
  RTO → RN pins `|z| < M` by padding and then `|x| < M`.
- Extracted from the RTO → RN chain proof and shared: `abs_lt_mid_of_toOdd`,
  `nearest_boundOK_of_abs_lt_mid`.
- Equalities `rnd_double_{RAZ_RAZ, RTO_RTO, RTO_RTZ, RTO_RAZ, RTO_RN}` in
  `DoubleRounding/Special.lean`. `rndRAZ_RAZ` needs no `Nontrivial`;
  `rndRTO_RTO` adds it to the total form's hypotheses.

**Naming (owner's call, after 7b).** The prefix names the object a theorem is
about; one family per rule, suffixes mark the level:

| Level | Name |
| --- | --- |
| on `rnd`, with tables (the headline) | `rndRTZ_RTZ`, …, `rndRTO_RN` |
| finite form, on `RoundsFinite` | `roundsRTZ_RTZ_finite`, … (incl. `roundsRTP_RTP_finite`, `_finite_pos`) |
| total form, on `Overflows`/`RoundsInBound` | `roundsRTZ_RTZ_inBound`, … |
| no overflow from the chain | `roundsRTZ_RTZ_noOverflow`, … |

The old finite forms were `rndRTZ_RTZ`, …; the old total forms `roundsRTZ_RTZ`,
…; the table forms `rnd_double_RTZ_RTZ`, …. The generic `rnd_double` keeps its
name.

**7c. Done.** The standard tables compose for every rule but RTO → RTZ
(`DoubleRounding/Special.lean`):

- `SpecialMap.exact_composes`: exact specials compose with any `F₁` table.
- `OverflowMap.composes_of_inf` with `ieee_map_awayZero`/`_toOdd`/`_nearest`:
  `±Inf` overflow tables compose when `F₁` keeps infinities exact (RAZ → RAZ,
  RTO → RTO, RTO → RAZ, RTO → RN).
- `OverflowMap.ieee_toZero_composes`: the IEEE RTZ tables compose under the
  RTZ containment, by `overflows_of_maxFinite_le` (`Total.lean`): every
  faithful rounding into `F₁` overflows at `±maxFinite₂`, since `F₂` holds the
  successor of `F₁`'s floored bound.
- `rnd_of_overflows_pos`/`_neg` now take `0 ≤ x` / `x ≤ 0`, so they apply at
  `±maxFinite₂`.
- Tests (`MpfxTest/DoubleRounding.lean`): full IEEE RTO → RN and RTZ → RTZ
  double rounding with the hypotheses discharged, and the negation showing the
  IEEE tables do not compose for RTO → RTZ.

**7d. Done** (steps 1–6 in one pass, at the owner's request). Diverged from
the steps below:

- Step 1 as planned: `roundsRTO_{RTZ,RAZ,RN}_finite_of_extend`.
- Step 2: the region A lemmas are `roundsXX_YY_agree` (`Total.lean`, section
  "Agreement in bound"), all through a private `eq_of_inBound`. Plain
  containment only; `hz` is used only for its unbounded rounding.
- Step 3: `OverflowAgrees` as designed; `hA` stays a separate hypothesis of
  `rnd_double`. The sign bookkeeping moved to `decide_lt_zero_of_chain`.
- Step 4: `OverflowAgrees.of_bound` also takes `¬ F₂.IsUndefined rm₂` (for
  uniqueness of `z`). `rndRAZ_RAZ_of_bound` keeps plain containment, since
  RAZ → RAZ never had a relaxed form.
- Steps 5–6 merged and generalized: `OverflowAgrees.of_saturate` and
  `OverflowMap.saturate_composes` hold for **any** pair of modes under plain
  `F₁ ⊆ F₂`. They only use faithfulness and `maxFinite₁ ∈ F₂`. In `chain`, the
  chain overflowing forces `|x| ≥ maxFinite₁`, so `y = ±maxFinite₁`; it is not
  vacuous. So the saturating-RTO discharges for RTO → RTO and RTO → RTZ are
  `MpfxTest` examples, not library theorems. `ieee_toZero_composes` is
  restated under plain containment; `overflows_of_maxFinite_le` (its only
  user) is gone. New in `Rounding/Special.lean`: `abs_le_maxFinite`,
  `saturated_eq_finite`, `OverflowMap.ieee_toZero` (`rfl`).
- Step 6's RTO → RN test shows failure on the region where `F₂` overflows and
  `F₁` does not (IEEE tables), rather than building a concrete `b₂ < M`
  instance. The "if RTO saturated" RTO → RN cell (IEEE RN table, saturated RTO)
  is still unchecked.
- Test changes: the IEEE RTZ → RTZ example now uses plain containment; the
  IEEE `hinf` arguments must be passed explicitly there, because the tables
  unify as `saturate` first.

The original handoff follows.

Make each rule's hypotheses as general as possible.

*Why the current bounds are not minimal.* The relaxed containment
(`b₂ ≥ next(b₁)`, or `b₂ ≥ M` for RN) exists so `F₂` never overflows where `F₁`
does not. With tables that is only needed where the overflow entry disagrees
with `F₁`'s rounding. Hand analysis (unproved):

| Rule | IEEE tables (RTO → ±Inf) | if RTO saturated |
| --- | --- | --- |
| RTZ → RTZ | plain `F₁ ⊆ F₂` suffices (RTZ saturates = bounded spec) | same |
| RAZ → RAZ | already plain | — |
| RTO → RAZ | plain likely suffices (padding keeps `z` off `maxFinite₁`) | not checked |
| RTO → RTO | relaxed bound tight | plain likely suffices |
| RTO → RTZ | tables do not compose at all | plain likely suffices |
| RTO → RN | `b₂ ≥ M` tight | `b₂ ≥ M` still needed |

*Design (settled with the owner): region conditions.* For a real `x`, let `z`
be its unbounded rounding into `F₂`, `w` that of `z` into `F₁` (chain), `y`
that of `x` into `F₁` (direct). The equality `rnd₁ (rnd₂ v) = rnd₁ v` needs:

| Region | Situation | Needed | Supplied by |
| --- | --- | --- | --- |
| A | `z`, `w`, `y` all in bound | `w = y` | finite form under plain containment (`hA`) |
| C1 | chain in bound, direct overflows | `O₁.map s = .finite w` | `OverflowAgrees.direct` |
| C2 | direct in bound, chain overflows | `O₁.map s = .finite y` | `OverflowAgrees.chain` |
| C3 | chain and direct overflow | signs agree | automatic (`IsFaithfulRound.decide_lt_zero`) |
| D1 | `F₂` overflows, direct in bound | `rnd₁ (O₂.map s).toReal = .value (.finite y)` | `OverflowAgrees.inner` |
| D2 | `F₂` and direct overflow | `rnd₁ (O₂.map s).toReal = .value (O₁.map s)` | `OverflowMap.Composes` |

(`s = decide (x < 0)`; it equals the sign of any nonzero rounding of `x`.)

```lean
structure OverflowAgrees (F₁ : FiniteFormat) (S₁ : SpecialMap F₁.toFormat)
    (O₁ : OverflowMap F₁.toFormat) (rm₁ : RoundingMode)
    (F₂ : FiniteFormat) (O₂ : OverflowMap F₂.toFormat) (rm₂ : RoundingMode) : Prop where
  direct : ∀ x z w, RoundsInBound F₂ rm₂ x z → RoundsInBound F₁ rm₁ z w →
    Overflows F₁ rm₁ x → O₁.map (decide (x < 0)) = .finite w
  chain : ∀ x z y, RoundsInBound F₂ rm₂ x z → Overflows F₁ rm₁ z →
    RoundsInBound F₁ rm₁ x y → O₁.map (decide (x < 0)) = .finite y
  inner : ∀ x y, Overflows F₂ rm₂ x → RoundsInBound F₁ rm₁ x y →
    rnd F₁ S₁ O₁ rm₁ (O₂.map (decide (x < 0))).toReal = .value (.finite y)
```

*Target signatures.* Headline (`DoubleRounding/Special.lean`):

| Theorem | Hypotheses (besides `hS`, `hO`, `hov : OverflowAgrees …`, `hu`) |
| --- | --- |
| `rndRTZ_RTZ` | `F₁ ⊆ F₂` |
| `rndRAZ_RAZ` | `F₁ ⊆ F₂` |
| `rndRTO_RTO` | `F₁ ⊆ F₂`, `2 ≤ F₂.p`, `¬ F₁.IsUndefined .toOdd` |
| `rndRTO_RTZ` | `F₁.extend 1 ⊆ F₂`, `2 ≤ F₂.p` |
| `rndRTO_RAZ` | `F₁.extend 1 ⊆ F₂`, `2 ≤ F₂.p` |
| `rndRTO_RN` | `F₁.extend 2 ⊆ F₂`, `2 ≤ F₂.p`, `¬ F₁.IsUndefined (.nearest tb)` |

No `Nontrivial` on the headline: it only enters through `of_bound`. The current
headline signatures survive as `rndXX_YY_of_bound` corollaries (relaxed
containment + `Nontrivial`), so the paper's forms stay available.

*Steps (one commit each, pause between).*

1. **Finite forms under plain containment.** `roundsRTO_RTZ_finite`,
   `roundsRTO_RAZ_finite` (`DoubleRounding/Basic.lean`) and `roundsRTO_RN_finite`
   (`Nearest.lean`) take the paper-form relaxed containment and derive
   `2 ≤ F₂.p` or triviality from it. Split each: a new `…_finite_of_extend`
   taking `F₁.extend k ⊆ F₂` and `2 ≤ F₂.p` holds the current main case (the
   sign split around the private `…_pos` cores; for RN the core
   `rndRTO_nearest_facts` already takes plain containment), and the paper form
   becomes the trivial-`F₁` case plus a call. RTZ/RAZ/RTO-RTO finite forms are
   already plain. Build: `lake build Mpfx.DoubleRounding.Nearest`.
2. **Region A lemma per rule.** From the plain finite form by restrict/lift
   (`RoundsFinite.*_restrict`, `*_lift`, `RoundsFinite.unique`): all three in
   bound ⇒ `w = y`. Pattern: see the in-bound branch of `roundsRTZ_RTZ_inBound`.
3. **`OverflowAgrees` and the new generic theorem.** Replace `rnd_double`'s
   `hP`/`hC` by `hA` (region A) and `hov`. The proof follows today's
   `rnd_double`: the in-bound/overflow case split on `z`, then on `w`/`y`,
   using `rnd_finite_of_roundsFinite` and the sign lemma.
4. **`OverflowAgrees.of_bound`.** Generic: from a rule's `…_inBound` and
   `…_noOverflow` forms every field is vacuous (C1: `noOverflow`; C2 and D1:
   the `inBound` disjunct contradicts uniqueness). Then rewrite the six
   headline theorems to the target signatures and add the `…_of_bound`
   corollaries (relaxed ⇒ plain containment via `extend_*_subset_of_withBound_subset`
   and `boundOK_boundAfterNext_of_boundOK`; `2 ≤ F₂.p` via
   `two_le_p_of_nontrivial` / `…_extend_two`). Update `MpfxTest/DoubleRounding.lean`.
5. **`OverflowAgrees.of_saturate` for RTZ outer** (`O₁ = OverflowMap.saturate F₁ hb₁`,
   `O₂ = OverflowMap.saturate F₂ hb₂`, plain `F₁ ⊆ F₂`). Sketch: C1 — `|x| > b₁ ≥ maxFinite₁`,
   `maxFinite₁ ∈ F₂` so `|z| ≥ maxFinite₁`, so `|w| ≥ maxFinite₁`, and in bound
   gives `|w| ≤ maxFinite₁` (`le_maxFinite`), so `w = ±maxFinite₁` with `x`'s sign;
   C2 — vacuous (`|w| ≤ |z| ≤ |x|` makes `w` a candidate below `y`);
   D1 — same as C1 for `y`, and `rnd₁(±maxFinite₂) = ±maxFinite₁` whether or
   not it overflows. Also `OverflowMap.saturate_toZero_composes` under plain
   containment (the D2 computation; generalizes `ieee_toZero_composes`) and
   `OverflowMap.ieee F .toZero hb hinf = OverflowMap.saturate F hb` (likely
   `rfl`). Test: IEEE RTZ → RTZ under plain `F₁ ⊆ F₂`.
6. *(Optional.)* Saturating-RTO discharges for RTO → RTO and RTO → RTZ, and an
   `MpfxTest` example showing RTO → RN fails for `b₂ < M`.

*Pitfalls met in 7a–7c.*

- Subset proofs passed inline as arguments may elaborate before the implicit
  format is known; state them with `have hsubG : <type> := …` first (see the
  `…_noOverflow` proofs in `Total.lean`).
- After `rcases hF₁b : F₁.b with _ | b₁` the equation reads `F₁.b = some b₁`;
  `hF₁b ▸ h` then fails where `↑b₁` is expected — use `rw [hF₁b] at h`.
- `rw` does not reduce `if false = true then …`; expose table entries with
  `change` (see `ieee_toZero_composes`).
- Inside a theorem named `X.mul_nonneg`, `mul_nonneg` resolves to itself; use
  `_root_.mul_nonneg`.
- Never run two builds at once; stop builds by PID, not `pkill -f "lake build"`
  (that matches the calling shell).

*Open questions for 7d.* Field and structure names (`OverflowAgrees`,
`direct`/`chain`/`inner`, `of_bound`, `of_saturate`); whether `hA` stays a
separate hypothesis of the generic theorem or folds into `OverflowAgrees`;
whether RTO's IEEE table should switch to saturation (owner chose `±Inf`; it is
what makes RTO → RTZ fail).


Settled before starting:

- The compatibility conditions are uniform: F₁'s rounding of F₂'s table entry
  is F₁'s table entry, `rnd₁ (S₂.map t) = .value (S₁.map t)` and
  `rnd₁ (O₂.map s) = .value (O₁.map s)`. Name them as predicates on the table
  pairs.
- Proof shape: if F₂ does not overflow, the finite-form rules on the unbounded
  formats give agreement of the unbounded values, hence of overflow status and
  sign; if F₂ overflows, F₁ overflows too (`b₂ ≥ next(b₁)` under the
  relaxed-bound containment), and the overflow condition closes it.
- **IEEE tables and RTO → RTZ are incompatible**, and that stays: RTO
  overflows to ±Inf (`OverflowMap.ieee`), so the chain gives
  `rnd_RTZ(+Inf) = +Inf` while direct RTZ gives `+maxFinite₁`. The RTO → RTZ
  theorem carries the compatibility hypothesis like every rule; the IEEE
  instances discharge it for the other rule pairs. Record the failure as a
  test (`MpfxTest`) showing the condition is false for the IEEE tables.

- `DoubleRounding/Total.lean`: for each rule, `rnd₁ (rnd₂ x) = rnd₁ x` for
  `x : WithSpecial ℝ`, under table-compatibility hypotheses, derived from the
  Phase 3 forms. Special inputs are a one-line case: `S₁ ∘ S₂` against `S₁`.
- State the compatibility conditions as named predicates so the IEEE instances
  can discharge them once.

Separate because it is new mathematics on top of a settled API; doing it
before Phase 6 would mean proving against tables that are not yet checked.

Build: `lake build Mpfx.DoubleRounding.Total`.

### Phase 8: documentation

**Done.** README: the §5.2 table gained a "With tables" column and a section
on the table conditions; containment notes the specials conjunct; the axioms
example now matches its output (it printed `rndRTO_RN`'s output under
`roundsRTO_RN_finite`); `lake test` and the new modules are in the layout.
DESIGN: `specials`, the two tables, `RoundResult`, why overflow is a
predicate. TODO: layout tree; ∞/NaN and saturation dropped from out of scope.
ROADMAP: a "Special values" group, including the open item on which total
forms the paper cites. After the last phase: full `lake build` and `lake test`
pass; `#print axioms` over the 54 README theorems gives only `propext`,
`Classical.choice`, `Quot.sound`.

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
lake test                       # the test library
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

Appendix A cites `roundsRTZ_RTZ_inBound`, …, `roundsRTO_RN_inBound` with the overflow
disjunct. Phase 3 changes their statements and Phase 7 adds equality forms.
Either keep the Phase 3 forms under their names (the paper's statement), or
retire them in favour of the equalities. Provisional: keep both until the
paper revision decides.
