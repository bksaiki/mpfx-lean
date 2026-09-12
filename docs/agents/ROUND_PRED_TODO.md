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

- [ ] `RoundsFinite.unique_toNegative` / `_toPositive`:
      `RoundsFinite F rm x y₁ → RoundsFinite F rm x y₂ → y₁ = y₂`. Lift the
      bodies out of `Directed.lean:198-222`, dropping the `rndUnbounded`
      mention. ~6 lines each.
- [ ] `RoundsFinite.isFaithfulRound` (roadmap §2), all seven modes:
      `toNegative`/`toPositive` trivial; `toZero`/`awayZero` via the existing
      `RoundsFinite.toNegative_iff_toZero_of_nonneg` bridges; `toOdd`/`nearest`
      read the conjunct off directly. Callers wanting the two-sided split go
      through `isFaithfulRound_iff_directed`.

No existing proof changes in this phase — it is purely additive, which makes it
cheap to review.

Extra acceptance: `Mpfx/RoundPred.lean` imports nothing from `Mpfx/RoundOp/`.

Commit message: `Add directed-mode uniqueness and mode-generic faithfulness`

— **pause for review** —

## Phase 2 — RTO uniqueness

Cleaned-up landing of the spike (see below). Touches `Mpfx/RoundOp/ToOdd.lean`.

- [ ] `RoundsFinite.toNegative_eq_floor` / `toPositive_eq_ceil` — our
      `round_DN_eq` / `round_UP_eq`.
- [ ] `isOdd_alternate_of_bracketing` — `toOdd_neighbors_alternate` restated
      over the relational DN/UP specs.
- [ ] `RoundsFinite.unique_toOdd`, with diagonal cases going through **Phase 1**
      rather than `rndUnbounded_unique_toNegative`.
- [ ] Rewire `rndUnbounded_unique_toOdd` to the 5-line form.

Extra acceptance: `rndUnbounded` appears nowhere in `unique_toOdd`'s statement,
and only via the two bridges in its proof. Net ≈ −26 lines.

Commit message: `Prove RTO uniqueness relationally, collapsing its 142-line proof`

— **pause for review** —

## Phase 3 — nearest uniqueness

Touches `Mpfx/RoundOp/Nearest.lean`. Mirrors `Rnd_NG_pt_unique`
(`Round_pred.v:707`).

- [ ] `RoundsFinite.unique_nearest`. Four cases; diagonals by Phase 1;
      off-diagonals by the tie-break clause. `.toEven` mixed case is the
      parity-alternation contradiction; `.awayZero` uses `DN ≤ x ≤ UP` with
      `|DN| = |UP|` ⟹ either `DN = UP` or `DN = -UP`, the latter forcing
      `x = 0` where Phase 1 closes it — same content as the current squaring
      argument, structured.
- [ ] Rewire `rndUnbounded_unique_nearest` to the one-line form.

Extra acceptance: the squaring detour at `Nearest.lean:912` is gone.
Expect ≈ −120 lines.

Commit message: `Prove nearest uniqueness relationally, dropping the squaring detour`

— **pause for review** —

## Phase 4 — collapse the dispatcher

Touches `Mpfx/RoundOp.lean` and the three `RoundOp/` files.

- [ ] Replace `rndUnbounded_unique` (`RoundOp.lean:34`) with a single generic
      call: `RoundsFinite.unique` applied to the hypothesis and
      `rndUnbounded_satisfies`.
- [ ] Delete all six now-trivial `rndUnbounded_unique_*` wrappers.

Extra acceptance: `grep -c rndUnbounded_unique_ Mpfx/` returns 0.

Commit message: `Collapse the six per-mode uniqueness wrappers into one dispatcher`

— **pause for review** —

---

# Track B — monotonicity

None of Track B shortens existing proofs. It is what unlocks roadmap §3's sign
lemmas and all of §4's error bounds. Settle the `round_le` open question below
before starting Phase 8.

## Phase 5 — directed monotonicity

- [ ] `Monotone (RoundsFinite F .toNegative)` / `.toPositive`
      (`Rnd_DN_pt_monotone`). A few lines each.
- [ ] `toZero` / `awayZero` via the sign bridges (`Rnd_ZR_pt_monotone`).

Commit message: `Add monotonicity for the four directed rounding modes`

— **pause for review** —

## Phase 6 — RTO monotonicity

- [ ] `toOdd`. Flocq gets this from `Valid_rnd Zrnd_odd` (`Round_odd.v:37`);
      we need a direct argument. Size unknown — spike first if it resists.

Commit message: `Add monotonicity for round-to-odd`

— **pause for review** —

## Phase 7 — nearest monotonicity

- [ ] Strict version (`x < y`), then patch `x = y` using Phase 3, as
      `Rnd_NG_pt_monotone` does.

Commit message: `Add monotonicity for the nearest modes, via Phase 3 uniqueness`

— **pause for review** —

## Phase 8 — `round_le`

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

### Caveat

`isOdd_alternate_of_bracketing` is itself proved through
`rndUnbounded_unique_toNegative`, so this gives a relational *statement* layer
with construction-backed *proofs* — not a construction-free Track A. Still
worth having, since statements are what downstream consumes and
`rnd_iff_rounds` already isolates the construction, but it is why Phase 1 is
the only phase that lands in a constructive `Mpfx/RoundPred.lean`.

## Adjacent: the alternation duplication

Found while sizing, **not** part of this item, but it wants to be done
*together* with Phases 2–3 since `isOdd_alternate_of_bracketing` is the natural
shared statement.

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

- [ ] **File placement.** Phase 1 is constructive and belongs in
      `Mpfx/RoundPred.lean` importing only `Mpfx.Rounding`, preserving the
      constructive/classical split documented in `TODO.md`. Phases 2–3 depend
      on the construction (see Caveat) and must stay in `RoundOp/`. Confirm
      before creating the file.
- [ ] **`round_le` at `RoundResult` level (Phase 8).** Flocq has no overflow,
      so `round_le` transfers cleanly only to the unbounded layer. A
      `RoundResult`-level statement needs an order with
      `overflow false < finite y < overflow true`. Suggest stating it on
      `RoundsFinite` only and deferring the `RoundResult` order until something
      needs it.
