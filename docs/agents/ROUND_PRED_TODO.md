# Round-predicate layer

Implementation plan for item 1 of [`FLOCQ_ROADMAP.md`](FLOCQ_ROADMAP.md):
rounding monotonicity and the uniqueness theory it sits on, ported from Flocq's
`Core/Round_pred.v`.

**Working policy.** Each phase below is sized to be roughly one commit and
carries a suggested one-line commit message. Stop after each phase for review
before starting the next. Do not commit — the author commits.

Status legend: `[ ]` not started · `[~]` in progress · `[x]` done · `[!]` blocked.

Every phase's acceptance criterion is `lake build` exiting 0 with no new
`sorry`; only the extra criteria are listed per phase.

## Why

Nothing in `Mpfx/` currently proves rounding is monotone, so we also lack
`round_le` and everything downstream of it (`round_ge_generic`,
`round_le_generic`, `abs_round_le_generic`, `mag_round`, and every error bound
in roadmap §4).

The secondary motive is collapsing existing proofs. Measured sizes before any
work:

| Proof | Lines | Collapsible? |
| ----- | ----- | ------------ |
| `rndUnbounded_unique_{toNegative,toPositive,toZero,awayZero}` (`Directed.lean:198`) | 52 | Barely — already Flocq's argument |
| `rndUnbounded_unique_toOdd` (`ToOdd.lean:592`) | 142 | Yes — verified, see Spike |
| `rndUnbounded_unique_nearest` (`Nearest.lean:886`) | 180 | Yes, same shape as RTO |

**The collapse does not come from monotonicity.** It comes from uniqueness via
faithfulness. Flocq's dependency order runs the same way: `Rnd_N_pt_monotone`
(`Round_pred.v:435`) holds only for **strict** `x < y`, and full monotonicity
for nearest (`Rnd_NG_pt_monotone`) takes uniqueness as an *input*. So the
uniqueness phases must precede the monotonicity phases regardless.

Root cause of the two large proofs: neither uses `isFaithfulRound_iff_directed`
(`Rounding.lean:257`), which already exists and converts a faithful witness into
`RoundsFinite .toNegative ∨ RoundsFinite .toPositive`. Instead they reach into
the construction — `unique_toOdd` does `unfold rndUnbounded` and rebuilds the
grid neighbours (`ToOdd.lean:638`), and `unique_nearest`'s `awayZero` branch
squares both distances to derive `x = 0` (`Nearest.lean:912`).

---

# Track A — relational uniqueness

## Phase 1 — directed uniqueness + `isFaithfulRound`

New file `Mpfx/RoundPred.lean`, importing only `Mpfx.Rounding` (constructive;
no `Classical.propDecidable`, no `rndUnbounded`).

- [x] `RoundsFinite.unique_toNegative` / `_toPositive`:
      `RoundsFinite F rm x y₁ → RoundsFinite F rm x y₂ → y₁ = y₂`. Lift the
      bodies out of `Directed.lean:198-222`, dropping the `rndUnbounded`
      mention. ~6 lines each.
- [x] `RoundsFinite.isFaithfulRound` (roadmap §2), all seven modes:
      `toNegative`/`toPositive` trivial; `toZero`/`awayZero` via the existing
      `RoundsFinite.toNegative_iff_toZero_of_nonneg` bridges; `toOdd`/`nearest`
      read the conjunct off directly. Callers wanting the two-sided split go
      through `isFaithfulRound_iff_directed`.

No existing proof changes in this phase — it is purely additive, which makes it
cheap to review.

**Done.** `Mpfx/RoundPred.lean`, 98 lines, imports only `Mpfx.Rounding`. Also
included `unique_toZero` / `_awayZero` (the sign-bridge plumbing was already
needed for `isFaithfulRound`, so they cost ~8 lines each and Phases 3–4 would
otherwise re-derive them). `isFaithfulRound` concludes `IsFaithfulRound F x y`
rather than the `toNegative ∨ toPositive` disjunction; callers wanting the
split compose with `isFaithfulRound_iff_directed`.

Extra acceptance: `Mpfx/RoundPred.lean` imports nothing from `Mpfx/RoundOp/`.

Commit message: `Add directed-mode uniqueness and mode-generic faithfulness`

— **pause for review** —

## Phase 2 — RTO uniqueness

Cleaned-up landing of the spike (see below). Touches `Mpfx/RoundOp/ToOdd.lean`.

- [x] `RoundsFinite.toNegative_eq_floor` / `toPositive_eq_ceil` — our
      `round_DN_eq` / `round_UP_eq`.
- [x] `isOdd_alternate_of_bracketing` — `toOdd_neighbors_alternate` restated
      over the relational DN/UP specs.
- [x] `RoundsFinite.unique_toOdd`, with diagonal cases going through **Phase 1**
      rather than `rndUnbounded_unique_toNegative`.
- [x] Rewire `rndUnbounded_unique_toOdd` to the 5-line form.

Extra acceptance: `rndUnbounded` appears nowhere in `unique_toOdd`'s statement,
and only via the two bridges in its proof. Net ≈ −26 lines.

**Done.** `rndUnbounded_unique_toOdd` went 142 lines → 5; `ToOdd.lean`
733 → 682. The two bridges landed in `Directed.lean` (+29) rather than
`ToOdd.lean` — they are directed-mode facts and belong beside the uniqueness
lemmas they use. All four spike cleanups applied. Net −23 lines overall,
better than the spike's −26-on-one-file because the probes are gone.

Commit message: `Prove RTO uniqueness relationally, collapsing its 142-line proof`

— **pause for review** —

## Phase 3 — nearest uniqueness

Touches `Mpfx/RoundOp/Nearest.lean`. Mirrors `Rnd_NG_pt_unique`
(`Round_pred.v:707`).

- [x] `RoundsFinite.unique_nearest`. Four cases; diagonals by Phase 1;
      off-diagonals by the tie-break clause. `.toEven` mixed case is the
      parity-alternation contradiction; `.awayZero` uses `DN ≤ x ≤ UP` with
      `|DN| = |UP|` ⟹ either `DN = UP` or `DN = -UP`, the latter forcing
      `x = 0` where Phase 1 closes it — same content as the current squaring
      argument, structured.
- [x] Rewire `rndUnbounded_unique_nearest` to the one-line form.

Extra acceptance: the squaring detour at `Nearest.lean:912` is gone.
Expect ≈ −120 lines.

**Done.** `rndUnbounded_unique_nearest` went 180 lines → 5; `Nearest.lean`
1065 → 991. Net −152 lines across the two files. Two more relational helpers
landed in `RoundPred.lean` (+22): `RoundsFinite.eq_zero_of_zero` (Flocq's
`round_0`, also roadmap §3) and `IsFaithfulRound.opposite_sides_of_ne` (the
case split behind `Rnd_NG_pt_unique`). The `.toEven` branch reuses Phase 2's
`isOdd_alternate_of_bracketing`, so `Nearest.lean` now imports
`Mpfx.RoundOp.ToOdd`; `nearest_toEven_neighbors_alternate` has exactly one
consumer left, the soundness proof `rndUnbounded_satisfies_nearest` — see
*Adjacent* below.

Commit message: `Prove nearest uniqueness relationally, dropping the squaring detour`

— **pause for review** —

## Phase 4 — collapse the dispatcher

Touches `Mpfx/RoundOp.lean` and the three `RoundOp/` files.

- [x] Replace `rndUnbounded_unique` (`RoundOp.lean:34`) with a single generic
      call: `RoundsFinite.unique` applied to the hypothesis and
      `rndUnbounded_satisfies`.
- [x] Delete all six now-trivial `rndUnbounded_unique_*` wrappers.

Extra acceptance: `grep -c rndUnbounded_unique_ Mpfx/` returns 0.

**Done.** 25 insertions, 76 deletions. `RoundsFinite.unique` (the mode-generic
uniqueness, Flocq's `round_unique`) lives in `RoundOp.lean` since it needs both
`unique_toOdd` and `unique_nearest`; `rndUnbounded_unique` is now one line on
top of it, signature unchanged, so its 16 downstream call sites were untouched.
Unplanned: the Phase 2 grid bridges were themselves built on the deleted
`rndUnbounded_unique_toNegative` / `_toPositive`, so they were rewired onto
Phase 1's relational lemmas composed with `rndUnbounded_satisfies_*`.

**Track A complete.** The four `rndUnbounded_unique_*` bodies totalling ~374
lines are gone, replaced by ~145 lines of format-agnostic lemmas in
`RoundPred.lean` plus the two grid bridges. `RoundsFinite.unique` now holds of
anything satisfying the spec, which is what Phase 7 needs.

Commit message: `Collapse the six per-mode uniqueness wrappers into one dispatcher`

— **pause for review** —

---

# Track B — restore the layering

`Rounding.lean` and `RoundPred.lean` are the relational layer; `RoundOp/` is
meant to hold the rounding *function* and nothing else. Track A broke that:
`RoundsFinite.unique_toOdd`, `unique_nearest` and `RoundsFinite.unique` are
statements about `RoundsFinite` that ended up under `RoundOp/` purely because
their proofs detoured through the construction.

Investigation showed the detour is avoidable and `RoundOp/` was already
over-stuffed before Track A:

* `toOdd_neighbors_alternate` (`ToOdd.lean:26`, 446 lines) mentions
  `rndUnbounded` / `rndInt` / `rndParity` **zero times**. It depends on
  `RoundOp/Defs.lean` only for `toParityFormatOfToOdd` (a *format* promotion
  built from `IsUndefined`) and seven arithmetic helpers about
  `⌊x · 2^(-e)⌋`. Neither is a fact about the function.
* The one real construction dependency is the Phase 2 grid bridges, and that
  is an artifact of how they were written — `rndUnbounded_satisfies_toNegative`
  (`Directed.lean:21`) already contains the whole argument, just stated about
  `rndUnbounded F .toNegative x h` rather than about the grid point. Turning it
  inside out removes the dependency; `Grid.lean` (which imports only
  `Containment`) supplies `exists_grid_rep` and `no_F_element_in_step_interval`.

Target layering:

```
Grid.lean       structural: grid reps, F-adjacency      (no rounding at all)
Mantissa.lean   ⌊x · 2^(-e)⌋ arithmetic                 ← out of RoundOp/Defs
Parity.lean     both alternation lemmas + promotions    ← out of ToOdd, Nearest
Rounding.lean   relational spec
RoundPred.lean  every relational consequence            ← unique_toOdd, …
RoundOp/        the function, and nothing else
```

## Phase 5 — rehome the scaled-mantissa arithmetic

Flocq splits this block by whether a lemma mentions format data: the pure
real/integer facts live in `Core/Raux.v` (`Section Floor_Ceil`, `Section pow`,
`mag`), a project-wide toolbox that does not know what a format is; the
format-dependent ones live in `Core/Generic_fmt.v` beside `cexp` and
`scaled_mantissa` (`scaled_mantissa_lt_bpow`, `mantissa_small_pos`,
`mantissa_DN_small_pos`, …). There is no `Mantissa.v`. Our block splits on the
same line, 12 pure to 4 format-dependent.

- [x] Twelve pure lemmas → `Mpfx/Utils.lean` (our `Raux.v`):
      `abs_floor_le_of_abs_lt`, `abs_ceil_le_of_abs_lt`,
      `abs_floor_add_one_le_of_abs_lt`, `abs_floor_ge_two_pow_pred`,
      `abs_lt_two_pow_log_of_precision`, `binade_le_floor`,
      `mul_zpow_neg_self`, `log_lt_p_of_abs_lt_two_pow`, `log_two_pow_nat`,
      `log_ge_p_pred_of_two_pow_pred_le`, `cast_two_pow_pred`,
      `two_pow_pred_le_scaled`.
- [x] Four format-dependent lemmas → `Mpfx/CanonicalExp.lean` (our
      `Generic_fmt.v` for this purpose): `floor_minimality`, `ceil_minimality`,
      `ofIntZpow_mem_unbounded`, `floor_mantissa_lt`. Adds the import edge
      `RoundOp/Defs → CanonicalExp → Grid → Containment`; verified acyclic,
      since nothing in that chain imports `Rounding` or `RoundOp`.
- [x] Pure move — no proof should change.

Alternative for the four: `Format.lean`, where `canonicalExp` is actually
defined. No new import edges and closer to Flocq's literal placement, but adds
~300 lines to a 2018-line file.

Extra acceptance: `git diff -M` shows the blocks as renames, not rewrites;
`Utils.lean` still mentions no format type.

**Done.** 520 insertions, 509 deletions; the net-change audit shows every
unpaired line is an import, one of the two new section headers, or the orphaned
"Per-mode soundness obligations" comment that described the departed block — no
proof text changed. `RoundOp/Defs.lean` 632 → 122 lines, now just the four
definitions plus the two parity promotions Phase 7 takes. `Utils.lean` mentions
a format type only in docstrings.

`CanonicalExp.lean` needed **no** `Classical.propDecidable`: its four `by_cases`
uses are all inside proofs, where Lean falls back to `Classical.byCases`. The
instance now appears only in the five `RoundOp/` files, each branching on real
comparisons inside a *definition* — the legitimate case. The move narrowed the
taint, since those 257 lines previously sat in a file that had it in scope.

Commit message: `Rehome the scaled-mantissa arithmetic out of the function layer`

— **pause for review** —

## Phase 6 — construction-free grid bridges

The only phase in Track B with real proof work.

- [x] `RoundsFinite.toNegative_floor` / `toPositive_ceil`: the grid point at
      the canonical exponent *satisfies* the directed spec, stated without
      mentioning `rndUnbounded`. Invert the bodies of
      `rndUnbounded_satisfies_toNegative` / `_toPositive`.
- [x] Rederive `rndUnbounded_satisfies_toNegative` / `_toPositive` from them
      (one line each, after the `unfold rndUnbounded` rewrite).
- [x] Rederive the Phase 2 bridges `toNegative_eq_floor` / `toPositive_eq_ceil`
      as `unique_toNegative hy (toNegative_floor F x)` — no construction.

Extra acceptance: neither bridge mentions `rndUnbounded`.

**Done.** 73 insertions, 81 deletions. The inversion went as predicted — the
whole argument already sat in `rndUnbounded_satisfies_toNegative`, aimed at the
wrong object. The four lemmas live in `RoundPred.lean`, which gained one import
(`Mpfx.CanonicalExp`) and still imports nothing from `RoundOp/`.

The dependency direction is now reversed, which is the point: before,
bridge → `rndUnbounded_unique` → construction; after,
`rndUnbounded_satisfies_toNegative` → `RoundsFinite.toNegative_floor`. The
function layer depends on the relational layer instead of the reverse, and both
`satisfies` proofs are 11 lines that unfold `rndUnbounded` to the grid point and
hand off.

Commit message: `Prove the grid bridges without reference to the construction`

— **pause for review** —

## Phase 7 — move the parity theory out

- [x] New `Mpfx/Parity.lean` above `Grid.lean`, holding
      `toOdd_neighbors_alternate` (446 lines) and
      `nearest_toEven_neighbors_alternate` (476 lines).
- [x] Move `toParityFormatOfToOdd` / `toParityFormatOfNearestEven` there too,
      or to `Rounding.lean` beside `IsUndefined` — they are format promotions,
      not rounding constructions.
- [x] Drop `private` where the move requires it, but no wider.

Extra acceptance: `Mpfx/Parity.lean` imports nothing from `Mpfx/RoundOp/`.

With both alternation lemmas finally in one file, the duplication recorded
under *Adjacent* below becomes a single-file change. Out of scope here; do it
as a follow-up so this phase stays a pure move.

**Done.** 969 insertions, 946 deletions; the unpaired-line audit shows the only
non-move changes are the two `private` → public transitions and the new file's
header/imports. `Parity.lean` is 950 lines importing `Mpfx.Rounding` +
`Mpfx.CanonicalExp` and nothing from `RoundOp/`. The promotions went to
`Rounding.lean` beside `IsUndefined`. `ToOdd.lean` 677 → 221,
`Nearest.lean` 987 → 511.

Two notes. `Parity.lean` needed no `Classical.propDecidable` — 950 lines that
had the instance in scope and never used it; it is now confined to four
`RoundOp/` files. And `RoundOp/Defs.lean` is down to **108 lines** from 632
before Track B: exactly `rndInt`, `rndParity`, `rndUnbounded`, `rnd` and the
soundness doc block.

Commit message: `Move the parity-alternation theory out of the function layer`

— **pause for review** —

## Phase 8 — relational consequences come home

- [x] Move `isOdd_alternate_of_bracketing`, `RoundsFinite.unique_toOdd`,
      `RoundsFinite.unique_nearest` and `RoundsFinite.unique` into
      `Mpfx/RoundPred.lean`.
- [x] `RoundOp.lean` keeps only `rndUnbounded_satisfies`,
      `rndUnbounded_unique` and `rnd_iff_rounds`.

Extra acceptance: every theorem left under `Mpfx/RoundOp/` mentions `rnd`,
`rndUnbounded`, `rndInt` or `rndParity` in its statement. `RoundPred.lean`
still imports nothing from `Mpfx/RoundOp/`.

**Done.** 199 insertions, 200 deletions — a pure move. `RoundPred.lean` 386
lines, importing `Rounding` + `CanonicalExp` + `Parity` and nothing from
`RoundOp/`. Sizes after Track B: `RoundOp.lean` 149, `Defs` 108, `Directed` 156,
`ToOdd` 139, `Nearest` 413.

**One documented exception to the acceptance criterion.**
`nearest_neighbors_setup` (`Nearest.lean:24`, private) is construction-free but
stays put. Several of its thirteen conjuncts are now redundant against the
relational layer — the two rounding directions are
`RoundsFinite.toNegative_floor` / `toPositive_ceil`, the dichotomy is
`isFaithfulRound_iff_directed` composed with the `_eq_floor` / `_eq_ceil`
bridges — so moving the bundle wholesale would carry that redundancy into the
clean file. Slimming it first is proof work, not a move.

- [ ] **Follow-up:** slim `nearest_neighbors_setup` against the relational
      lemmas, then move what remains out of `RoundOp/`.

Commit message: `Move the relational uniqueness theorems into RoundPred`

— **pause for review** —

---

# Track C — monotonicity

None of Track C shortens existing proofs. It is what unlocks roadmap §3's sign
lemmas and all of §4's error bounds. Settle the `round_le` open question below
before starting Phase 12.

## Phase 9 — directed monotonicity

- [x] `Monotone (RoundsFinite F .toNegative)` / `.toPositive`
      (`Rnd_DN_pt_monotone`). A few lines each.
- [x] `toZero` / `awayZero` via the sign bridges (`Rnd_ZR_pt_monotone`).

**Done.** +70 lines in `RoundPred.lean`, nothing else touched. Six lemmas:
`monotone_{toNegative,toPositive,toZero,awayZero}` plus the two sign facts
`toNegative_nonneg` / `toPositive_nonpos` (Flocq `round_pred_ge_0` /
`round_pred_le_0`), which the `toZero` zero-crossing case needs and which
roadmap §3 wants anyway. The directed proofs are three lines each. No `rnd`
mentions; no `by_cases` — the sign splits go through `le_total`.

Commit message: `Add monotonicity for the four directed rounding modes`

— **pause for review** —

## Phase 10 — RTO monotonicity

- [ ] `toOdd`. Flocq gets this from `Valid_rnd Zrnd_odd` (`Round_odd.v:37`);
      we need a direct argument. Size unknown — spike first if it resists.

Commit message: `Add monotonicity for round-to-odd`

— **pause for review** —

## Phase 11 — nearest monotonicity

- [ ] Strict version (`x < y`), then patch `x = y` using Phase 3's `unique_nearest`, as
      `Rnd_NG_pt_monotone` does.

Commit message: `Add monotonicity for the nearest modes, via Phase 3 uniqueness`

— **pause for review** —

## Phase 12 — `round_le`

- [ ] `round_le` on `RoundsFinite`. See the open question below on whether to
      also state it at `RoundResult` level.

Commit message: `Add round_le, the monotonicity of rounding in its input`

— **pause for review** —

---

## Spike (2026-09-12)

Ran to size Track A. Everything below was checked with `lake build`; the
working tree was then restored to HEAD. The patch lived in the session
scratchpad and is **not** preserved — the statements here are what is needed to
redo it (~1 hour). Phase 2 is the cleaned-up version of this.

Verified:

- `rndUnbounded_unique_toOdd` collapses from **142 lines to 5**:
  ```lean
  theorem rndUnbounded_unique_toOdd (F : FiniteFormat) (x : ℝ)
      (h : ¬ F.IsUndefined .toOdd) {y : Dyadic}
      (hy : RoundsFinite F.unbounded .toOdd x y) :
      y = rndUnbounded F .toOdd x h :=
    RoundsFinite.unique_toOdd h hy (rndUnbounded_satisfies_toOdd F x h)
  ```
  `ToOdd.lean` 733 → 707 lines; full build green.
- Two new reusable bridges (~11 lines each):
  ```lean
  theorem RoundsFinite.toNegative_eq_floor (F : FiniteFormat) (x : ℝ) {y : Dyadic}
      (hy : RoundsFinite F.unbounded .toNegative x y) :
      y = Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋ (F.canonicalExp x)
  ```
  (and `toPositive_eq_ceil` with `⌈·⌉`). Both are `rndUnbounded_unique_*`
  followed by unfolding `rndUnbounded`.
- `isOdd_alternate_of_bracketing` (~33 lines) and `RoundsFinite.unique_toOdd`
  (~47 lines): four cases via `isFaithfulRound_iff_directed`, diagonals by
  directed uniqueness, off-diagonals by alternation.

Net on `ToOdd.lean` alone is −26 lines: 137 saved, 107 spent on the new
lemmas. **Track A does not pay for itself on the first mode** — it pays on the
second, and in what the bridges unlock.

### Fixes the spike needs before landing as Phase 2

- [ ] Route `unique_toOdd`'s diagonal cases through Phase 1 instead of
      `rndUnbounded_unique_toNegative`.
- [ ] Replace the `field_simp; rw [← zpow_add₀ …]; simp` flailing in
      `isOdd_alternate_of_bracketing` with `mul_zpow_neg_self`, which the
      codebase already has and the proof being replaced already used.
- [ ] Stop `rintro`-destructuring `RoundsFinite` in the `mixed` helper only to
      re-assemble the same anonymous constructors when passing them on.
- [ ] Drop the two `example` probes, the `SPIKE` markers, the unprivating of
      `toOdd_neighbors_alternate`, and the `import Mpfx.RoundOp.ToOdd` added to
      `Nearest.lean` — all of those existed only to run the probes.

### Caveat (superseded by Track B)

`isOdd_alternate_of_bracketing` was proved through
`rndUnbounded_unique_toNegative`, so Track A gave a relational *statement*
layer with construction-backed *proofs*. That was taken as unavoidable at the
time; it is not. Track B removes the detour — see Phase 6.

## Adjacent: the alternation duplication

Found while sizing. After **Phase 7** puts both alternation lemmas in
`Mpfx/Parity.lean` this becomes a single-file change; do it as a follow-up to
that phase rather than inside it, so Phase 7 stays a pure move.
`isOdd_alternate_of_bracketing` is the natural shared statement.

`toOdd_neighbors_alternate` (`ToOdd.lean:26`, 446 lines) and
`nearest_toEven_neighbors_alternate` (`Nearest.lean:21`, 476 lines) are
near-duplicates. Two probes confirmed it:

- `F.toParityFormatOfToOdd h = F.toParityFormatOfNearestEven h'` is **`rfl`**
  (`ParityFormat.parity` is a `Prop` field, so proof irrelevance applies).
- Consequently **part 1 of the 476-line nearest proof is derivable in 3 lines**
  from the toOdd one, modulo a one-line `IsUndefined` bridge
  (`fun ⟨h1, h2, _⟩ => h ⟨h1, h2, Or.inr rfl⟩`). This compiled.

The `IsEven` half does *not* fall out for free:
`alternating_isEven_of_alternating_iff` (`Format.lean:705`) needs canonical
representations on both sides, and neither proof exports them
(`IsRepresentableAtP` appears 0 times in both files — they route through the
`ParityFormat.alternating_parity_*_iff` family, and the saturated branches build
`IsEven` by hand). So this is "share the iff, keep a smaller `IsEven` tail,"
not a clean delete — but the iff component is ~100% redundant across ~450
lines, against ~200 saved by the whole uniqueness collapse.

## Open questions

- [ ] **Deferred to the end of Track C:** the `Grid.lean` "grid" vocabulary has
      no Flocq counterpart (the word appears zero times there; the concept is
      `ulp` + `canonical` + `discrete` + `succ`/`pred`). Recorded under item 4
      of `FLOCQ_ROADMAP.md`, to travel with the `Ulp.lean` work rather than as a
      standalone rename.

- [x] **File placement.** Resolved by Track B: the Phase 2–3 dependency on the
      construction turned out to be avoidable, so the relational uniqueness
      theorems do *not* have to stay in `RoundOp/`. Phase 8 moves them into
      `RoundPred.lean`.
- [ ] **`round_le` at `RoundResult` level (Phase 12).** Flocq has no overflow,
      so `round_le` transfers cleanly only to the unbounded layer. A
      `RoundResult`-level statement needs an order with
      `overflow false < finite y < overflow true`. Suggest stating it on
      `RoundsFinite` only and deferring the `RoundResult` order until something
      needs it.
