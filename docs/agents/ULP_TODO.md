# ulp, succ and pred

Implementation plan for item 4 of [`FLOCQ_ROADMAP.md`](FLOCQ_ROADMAP.md).

**Working policy.** Each phase is sized to be roughly one commit and carries a
suggested one-line commit message. Stop after each phase for review before
starting the next. Do not commit — the author commits.

Status legend: `[ ]` not started · `[~]` in progress · `[x]` done · `[!]` blocked.

Every phase's acceptance criterion is `lake build` exiting 0 with no new
`sorry`; only the extra criteria are listed per phase.

## Which convention `ulp` follows

`ulp(x)` is not a single notion — definitions disagree at powers of two, where
the gap below `x` is half the gap above. Ours is:

```
ulp F x = 2 ^ canonicalExp F x       canonicalExp F x = max (⌊log₂|x|⌋ + 1 − p) exp
```

At `x = 2^e` this gives `2^(e+1−p)`: the spacing of the binade **above** `x`,
twice the spacing immediately below it. That is Goldberg's convention, and
Flocq's — `mag (2^e) = e+1`, so `cexp = fexp (mag x)` lands in the upper binade
too. Harrison's definition (the distance between the closest straddling pair
`a ≤ x ≤ b`, `a ≠ b`) takes the *smaller* value there, and Kahan's differs
again. We follow Flocq; do not mix conventions mid-development.

**Where this bites, concretely.** With the upper-binade convention,

* `succ x = x + ulp x` is correct at a power of two — the step up really is the
  larger one;
* `pred x = x − ulp x` is **wrong** there — the step down is half that.

So `succ` is uniform and `pred` is not. Flocq handles it by special-casing the
binade floor:

```coq
Definition pred_pos x :=
  if Req_bool x (bpow (mag beta x - 1)) then x - bpow (fexp (mag beta x - 1))
  else x - ulp x.
```

Phase 3 must reproduce that asymmetry. Any lemma pairing `succ` with `pred`
needs checking at `|x| = 2^e`.

## Vocabulary

`Grid.lean`'s "grid" has no Flocq counterpart — the word appears nowhere in
Flocq's source. That is not an oversight: once you have `ulp`, `succ` and
discreteness you never need to name the set of representable values at a fixed
exponent.

| concept | word |
| ------- | ---- |
| spacing at `x` | `ulp` |
| next / previous representable value | `succ` / `pred` |
| nothing lies strictly between | discreteness |
| the interval `[2^e, 2^(e+1))` | **`binade`** — already used ~100 times across eight files |
| the lattice at a fixed exponent | *no name needed* |

`binade` is **not** a synonym for "grid". They agree in the normal range, one
binade to one grid, but diverge below it: under `FLT(p, emin)` everything under
`2^(emin+p−1)` has `canonicalExp = emin`, so one grid of spacing `2^emin` spans
many binades. That divergence is exactly what produced the `_exp_bot` twins.

So "grid" is retired by attrition, not substitution: `exists_grid_rep` becomes
"`y` is canonical", `no_F_element_in_step_interval` becomes "nothing lies
strictly between `y` and `succ y`", `F_adjacent_step_form` becomes
`y₂ = succ y₁`. None of them mentions a lattice, so `Grid.lean` does not get
renamed — it dissolves.

## Why

The reducing half of roadmap §4. `Grid.lean`'s F-adjacency theory is `succ` and
`pred` in disguise — `F_adjacent_step_form` says `y₂ = succ y₁` and
`no_F_element_in_step_interval` is discreteness — so restating it collapses the
roadmap §6 twins as a side effect rather than as separate work.

---

## Phase 1 — `ulp` at zero

`canonicalExp F 0 = 0` in the `(p finite, exp = ⊥)` branch, so `ulp F 0 = 1`
for FLX-shaped formats while `ulp_pos` asserts `0 < ulp F x` unconditionally.
Inert today, but `succ`/`pred` are the first things to touch it.

There is no right value for `canonicalExp F 0` when `exp = ⊥`: the format holds
`c·2^k` at arbitrarily negative `k`, so the gap at zero has infimum 0. Flocq
takes the same view — `mag 0` is junk and `cexp` is never applied at 0. Fix
`ulp` instead:

- [ ] `ulp F x = if x = 0 ∧ F.exp = ⊥ then 0 else 2 ^ canonicalExp F x`.
      `canonicalExp F 0` already returns `e` in the finite-`exp` branches, so
      only `⊥` needs the guard.
- [ ] `ulp_of_ne_zero`, `ulp_nonneg`; `ulp_pos` gains `x ≠ 0`.
- [ ] Fix the 16 sites that `unfold ulp` and would newly meet the `if`, and the
      three `ulp_pos` call sites.
- [ ] `rnd_lt_mid` (`NearestMidpoint.lean`) has no positivity hypothesis, and
      `h21 : F₂.canonicalExp x < F₁.canonicalExp x` does **not** force `x ≠ 0` —
      two formats with different finite `exp` satisfy it at zero. Either add
      `x ≠ 0` (and push it to callers) or rearrange. Confirm the statement is
      vacuous at zero rather than assuming it.

This is Flocq's `negligible_exp`, which we get for free: Flocq needs `LPO_Z` to
decide whether a minimal exponent exists, because `fexp : Z → Z` is arbitrary.
Our `F.exp : WithBot ℤ` *is* that decision, in the type.

Commit message: `Give ulp the right value at zero`

— **pause for review** —

## Phase 2 — `Mpfx/Ulp.lean`

- [ ] Move `ulp`, `rndDown`, `rndUp`, `midp` and their basic lemmas out of
      `NearestMidpoint.lean` into their own file, leaving the double-rounding
      midpoint theory behind.
- [ ] Pure move — no proof should change.

Extra acceptance: `git diff -M` shows the block as a move, not a rewrite.

Commit message: `Split the ulp/rndDown/rndUp API into its own file`

— **pause for review** —

## Phase 3 — `succ` and `pred`

The one phase with real proof work, and the one the convention section is
about.

- [ ] `succ` (uniform: `x + ulp x` for `0 ≤ x`) and `pred` with the
      binade-floor special case.
- [ ] Membership: `succ`/`pred` of an `F`-value is an `F`-value.
- [ ] The involution pair `succ_pred` / `pred_succ`, and `succ_gt_id` /
      `pred_lt_id`.
- [ ] `succ_le_lt` — `succ x ≤ y` iff `x < y` for `F`-values, the form that
      makes `succ` usable as adjacency.

Extra acceptance: a test that `pred (2^e) = 2^e − 2^(e−p)`, not `2^e − 2^(e+1−p)`.

Commit message: `Add succ and pred as total format functions`

— **pause for review** —

## Phase 4 — retire `Format.next`

`succ` supersedes it. For `b > 0` they are already the same function:
`next`'s step exponent `max e (⌊log₂ b⌋ − p + 1)` *is* `canonicalExp F b`, so
`next F b = b + ulp F b`. All of `next`'s junk is in the `b ≤ 0` branches
(`2^e` for finite `exp`, `b + 1` for `⊥`), and the Phase 1 `ulp` fix removes the
reason those existed: with `ulp F 0 = 0` when `exp = ⊥`, `succ 0 = 0`, so `succ`
of a representable value is always representable.

The obstacle is typing, not size. Only **7 lines** unfold `next`; the rest goes
through an 18-lemma interface. But `next` lives on `Format` (the §5.1
containment theory is `Format`-level) while `canonicalExp` needs
`FiniteFormat`'s invariant — and the excluded `(p = ⊤, exp = ⊥)` case is exactly
where `next` returns `b + 1`.

- [ ] Move `boundAfterNext` to `FiniteFormat`. `withBound : Format → Bound →
      Format` stays put, so hypotheses go from
      `F₁.toFormat.withBound F₁.toFormat.boundAfterNext ⊆ F₂.toFormat` to
      `F₁.toFormat.withBound F₁.boundAfterNext ⊆ F₂.toFormat` — a rename, with
      the `⊆` still `Format`-level and theorem shapes unchanged.
- [ ] Replace the 18 `next_*` lemmas with their `succ` counterparts, and the
      ~200 call sites with the renamed forms.
- [ ] Delete `Format.next`. Add it back only if a use case appears that `succ`
      cannot serve.

Doing this immediately after Phase 3 exercises `succ`'s lemma set against a
demanding consumer before more is built on it, and avoids a window where both
notions coexist. Note it only exercises non-negative arguments, so `pred`'s
binade-floor case stays untested until Phase 5.

Commit message: `Retire Format.next in favour of succ`

— **pause for review** —

## Phase 5 — adjacency through `succ`/`pred`

- [ ] Restate `Grid.lean`'s F-adjacency as `succ`: `F_adjacent_step_form`
      becomes `y₂ = succ y₁`, `no_F_element_in_step_interval` becomes
      discreteness.
- [ ] Keep the old names as wrappers if the call sites are many; otherwise
      rewire them.

Commit message: `Restate F-adjacency in terms of succ`

— **pause for review** —

## Phase 6 — merge the `Grid` twins (roadmap §6)

With adjacency phrased through `succ`, the three remaining `_exp_bot` pairs
should collapse: `no_F_element_in_step_interval` (43+29),
`F_adjacent_step_form` (43+38), `midpoint_mem_extend_one_of_F_adjacent_pos`
(31+22). The shared cores are already extracted, so expect ~60–70 lines.

- [ ] Merge bottom-up: the `no_F_element` pair first, since the others call it.

Commit message: `Collapse the remaining Grid exponent-case twins`

— **pause for review** —

## Phase 7 — vocabulary sweep

Most lemma renames happen on their own in Phases 5–6, where
`F_adjacent_step_form` dissolves into `succ` facts and
`no_F_element_in_step_interval` becomes discreteness. This phase is the
residue.

- [ ] Hypothesis names: `h_step`, `hstep`, `h_step_pos` → `h_ulp` and friends
      (~50 sites). Mechanical, noisy in the diff, hence its own commit.
- [ ] Survivors: `grid_rep_c_pos` → `canonical_rep_pos`, `grid_rep_reconstruct`,
      `step_interval_bounds`, `step_interval_squeeze_absurd`,
      `next_step_precision`, `next_step_min`, `coe_add_step_halves`,
      `grid_floor_setup`, `float_window_step`.
- [ ] Resolve the `exists_canonical_rep` collision: `Grid`'s component-taking
      version and `CanonicalExp`'s membership-taking version are the same fact;
      keep one name with the other as a wrapper.
- [ ] Dissolve `Grid.lean`. Canonical-rep, discreteness and adjacency belong in
      `Ulp.lean`; the `midpoint_mem_extend_one_*` family is §5.2 containment
      groundwork for `rndRTO_RN`, not spacing theory, so it goes with
      `Containment.lean` or into its own file.

Extra acceptance: `grep -ri "grid" Mpfx/` returns nothing outside prose.

Commit message: `Retire the grid vocabulary in favour of ulp and succ`

— **pause for review** —

## Phase 8 — error bounds (capability, not reduction)

- [ ] `error_lt_ulp` (faithful), `error_le_half_ulp` (nearest),
      `error_le_half_ulp_round`, `ulp_DN`, `ulp_round`.

Flocq's `ulp_round` carries an `Exp_not_FTZ` hypothesis and a disjunctive
conclusion — `ulp (round x) = ulp x ∨ |round x| = 2 ^ mag x` — whose second
disjunct is exactly the binade-boundary case. We have no FTZ regime, so check
whether the hypothesis is needed here.

Commit message: `Add the ulp error bounds`

— **pause for review** —

## Phase 9 — bracket characterizations (capability, not reduction)

- [ ] `round_DN_eq` (`d ≤ x < succ d → rndDown x = d`), `round_UP_eq`,
      `round_N_le_midp`, `round_N_ge_midp`, `round_N_eq_DN`, `round_N_eq_UP`,
      `round_N_eq_ties`.
- [ ] Reconcile with `NearestMidpoint.lean`'s hand-rolled equivalents
      (`nearest_eq_of_close`, `nearest_eq_rndDown_of_lt_midp`,
      `nearest_eq_rndUp_of_midp_lt`) — these are the same facts, so this should
      replace rather than duplicate.

Commit message: `Add the bracket characterizations of rounding`

— **pause for review** —

## Open questions

- [x] **`Format.next` vs `succ`.** Resolved: `succ` supersedes it. See Phase 4.
- [x] **The "grid" vocabulary.** Resolved: see *Vocabulary* above. Retired by
      attrition across Phases 5–6, with the residue swept in Phase 7.
