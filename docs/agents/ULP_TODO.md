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

- [x] `ulp F x = if x = 0 ∧ F.exp = ⊥ then 0 else 2 ^ canonicalExp F x`.
      `canonicalExp F 0` already returns `e` in the finite-`exp` branches, so
      only `⊥` needs the guard.
- [x] `ulp_of_ne_zero`, `ulp_nonneg`; `ulp_pos` gains `x ≠ 0`.
- [x] Fix the 16 sites that `unfold ulp` and would newly meet the `if`, and the
      three `ulp_pos` call sites.
- [x] `rnd_lt_mid` (`NearestMidpoint.lean`) has no positivity hypothesis, and
      `h21 : F₂.canonicalExp x < F₁.canonicalExp x` does **not** force `x ≠ 0` —
      two formats with different finite `exp` satisfy it at zero. Either add
      `x ≠ 0` (and push it to callers) or rearrange. Confirm the statement is
      vacuous at zero rather than assuming it.

This is Flocq's `negligible_exp`, which we get for free: Flocq needs `LPO_Z` to
decide whether a minimal exponent exists, because `fexp : Z → Z` is arbitrary.
Our `F.exp : WithBot ℤ` *is* that decision, in the type.

**Done.** Bigger than estimated: not 16 mechanical rewrites, but ~10 theorems
whose statements or proofs genuinely changed, because several were only true by
accident of `ulp 0` being junk-positive.

* `lt_rndDown_add_ulp` is *false* at `0` with no minimum quantum — there is no
  next value above zero. It now takes the guard negation `¬(x = 0 ∧ F.exp = ⊥)`,
  which is weaker than `x ≠ 0` and still true at zero when `exp` is finite.
* `ulp_le_half_ulp_of_canonicalExp_lt`, `rnd_lt_mid`, `rnd_gt_mid` gained
  `x ≠ 0`; their callers already had it.
* `rndUp_le_rndDown_add_ulp` and `nearest_error_le_half_ulp` stayed
  unconditional — true at zero, only their proofs needed case splits. Worth the
  effort, since a hypothesis there would have rippled to every caller.
* Two proofs needed real work rather than rewriting: one branch of
  `rnd_lt_mid`'s neighbour analysis is contradictory at `z = 0`, the other
  genuinely admits it and needed a sub-case where both roundings are zero.

`ulp_guard_of_midp_ne` fell out and is reusable: without a minimum quantum `0`
is its own midpoint, so any strict comparison of `ξ` against `midp F ξ` rules
the guard out. It discharged the sites with no positivity available.

Commit message: `Give ulp the right value at zero`

— **pause for review** —

## Phase 2 — `Mpfx/Ulp.lean`

- [x] Move `ulp`, `rndDown`, `rndUp`, `midp` and their basic lemmas out of
      `NearestMidpoint.lean` into their own file, leaving the double-rounding
      midpoint theory behind.
- [x] Pure move — no proof should change.

Extra acceptance: `git diff -M` shows the block as a move, not a rewrite.

**Done.** `Mpfx/Ulp.lean` is 361 lines; `NearestMidpoint.lean` 786 → 318.
`canonicalExp_neg` went to `CanonicalExp.lean` where it belongs, which let
`ulp_neg` sit beside `ulp_pos`. Every unpaired diff line is a module docstring,
an import, a section header or `namespace`/`end` — no proof text changed.

Commit message: `Split the ulp/rndDown/rndUp API into its own file`

— **pause for review** —

## Phase 3 — `succ` and `pred`

The one phase with real proof work, and the one the convention section is
about.

- [x] `succ` (uniform: `x + ulp x` for `0 ≤ x`) and `pred` with the
      binade-floor special case.
- [x] Membership: `succ`/`pred` of an `F`-value is an `F`-value.
- [ ] The involution pair `succ_pred` / `pred_succ`, and `succ_gt_id` /
      `pred_lt_id`.
- [x] `succ_le_lt` — `succ x ≤ y` iff `x < y` for `F`-values, the form that
      makes `succ` usable as adjacency.

Extra acceptance: a test that `pred (2^e) = 2^e − 2^(e−p)`, not `2^e − 2^(e+1−p)`.

**Done, except the involutions.** Both convention checks pass:
`ulp F (2^k) = 2^(k+1−p)` (spacing above) and `pred F (2^k) = 2^k − 2^(k−p)`
(the smaller step down).

Flocq's `bpow (fexp (mag x − 1))` translated neatly: at a power of two it is
just `ulp F (x/2)`, since `x/2` lies in the binade below and `canonicalExp`
there is exactly that step. No exponent-level `fexp` was needed.

Landed: `predPos`/`succ`/`pred` with their reduction lemmas, `succ_mem`,
`pred_mem`, `lt_succ`, `pred_lt`, `pred_eq_predPos`, `succ_le_of_lt`, plus
`log_two_zpow` (`Utils.lean`) and `unbounded_canonicalExp` (`Format.lean`).

`succ_le_of_lt` is what Phase 5 needs: `canonicalExp_mono` gives `ex ≤ ey`, so
`y` is an integer multiple of `2^ex` as well, and `y > x` forces the multiplier
up by at least one. That is discreteness, stated through `succ`.

`pred_mem` needed the boundary case: away from a floor it is `(c−1)·2^e`; at a
floor it is `2^k − 2^(e')` with coefficient `2^(k−e') − 1`, in range because
`e' ≥ k − p` gives `k − e' ≤ p`.

- [ ] **Outstanding:** the involutions `succ_pred` / `pred_succ`. Flocq spends
      `pred_pos_plus_ulp` and three auxiliaries on these. Nothing in Phases 4–6
      needs them; pick them up if Phase 9 does.

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

**Three findings while starting this, which split the phase in two.**

*Typing.* `next : Dyadic → Dyadic` but `succ : ℝ → ℝ`. `boundAfterNext` must
produce a `NonNegDyadic`, and `succ_mem` gives only existence, so `succ` cannot
define it. The wrapper instead makes `next`'s *real value* be `succ`:

```lean
noncomputable def FiniteFormat.next (F : FiniteFormat) (b : Dyadic) : Dyadic :=
  if (b : ℝ) = 0 ∧ F.exp = ⊥ then b
  else b + Dyadic.ofIntZpow 1 (F.canonicalExp (b : ℝ))

theorem next_coe (hb : 0 ≤ ((b : Dyadic) : ℝ)) :
    ((F.next b : Dyadic) : ℝ) = succ F ((b : Dyadic) : ℝ)
```

This agrees with the current `next` wherever it is sensible — for `b > 0` the
old step exponent `max e (⌊log₂ b⌋ − p + 1)` *is* `canonicalExp b`. It differs
only in the junk branches: at `b = 0` with `exp = ⊥` the old gives `b + 1`, the
new gives `0`, matching `succ 0 = 0`. For `b < 0` the bridge is not stated —
`succ` there goes through `predPos`, mirroring which needs machinery nothing
uses, and every call site is at a non-negative bound.

*Import order.* `Containment` sits below `Ulp`, so `next` cannot be defined via
`ulp`. It does not need to: `canonicalExp` alone suffices, and that is in
`Format.lean`. The definition stays in `Containment.lean`; `next_coe` goes in
`Ulp.lean` where both are visible.

*Namespace.* 13 of the declarations sit inside `namespace Format`
(`Containment.lean` 18–690), six more at `Mpfx` level after `end FiniteFormat`.
Migrating relocates 13 declarations across a namespace boundary in the file
holding the §5.1 results.

### Phase 4a — add the wrapper — **done**

- [x] `FiniteFormat.next` (`Containment.lean`), `next_of_ne`,
      `next_eq_format_next`; `next_coe` and `next_mem` (`Ulp.lean`).

`next_mem` needs no sign hypothesis: the guard branch returns `b` itself and the
other is the next grid point up, which is representable for any `b ∈ F`.

Commit message: `Add a succ-backed successor on FiniteFormat`

### Phase 4b — **will not do**

`Format.next` stays. Its value at a degenerate format is not junk, it is
load-bearing.

`hp_F₂_or_F₁_trivial_extend` (`DoubleRounding.lean:563`) builds a witness
`3·2^k` that must satisfy `|3·2^k| ≤ boundAfterNext F₁`. In the
`F₁.exp = ⊥, F₁.b = 0` branch it uses `next 0 = 1` to get `3/4 ≤ 1`. Under the
succ-backed definition `next 0 = 0`, so `boundAfterNext = 0` and *no* witness can
exist — `withBound 0` holds only zero, so there is genuinely no 2-precision
element. That branch would become false, not merely unproved.

So the two are different operations that agree where both are meaningful:

| | |
| --- | --- |
| `Format.next` | advances a **bound**, with a convention at degenerate formats |
| `FiniteFormat.next` / `succ` | the **successor** in the grid; `0` when there is none |

`next_eq_format_next` records that they coincide for `b > 0`.

- [ ] **Optional follow-up:** rename `Format.next` to something bound-flavoured
      (`nextBound`, `boundStep`) so the two do not read as the same notion.
      ~200 call sites, mechanical.

## Phase 5 — adjacency through `succ` — **done, redirected**

The phase as written wanted to restate `Grid.lean`'s adjacency in `succ` terms.
That is not possible: the import chain is

```
Format < Containment < Grid < CanonicalExp < RoundOp < Ulp
```

so `Grid.lean` sits **below** `succ` and cannot mention it. (`canonicalExp` is
in `Format.lean`, which is why `Grid` can already use *that*.) Moving the
`ulp`/`succ`/`pred` definitions down — they need only `Format.lean` — would fix
it, but costs a restructure this phase does not justify.

Done additively in `Ulp.lean` instead, where both notions are visible:

- [x] `succ_eq_of_adjacent` — if nothing of `F` lies strictly between a positive
      `y₁` and `y₂`, then `y₂ = succ y₁`. `succ_le_of_lt` gives one direction;
      the other is that `succ y₁` is representable (`next_mem`) and above `y₁`,
      so adjacency bounds `y₂` by it. This is `F_adjacent_step_form` in `succ`
      form.
- [x] `not_mem_between_succ` — discreteness, i.e.
      `no_F_element_in_step_interval` restated.

**Consequence for Phase 6:** it does not depend on this. The `_exp_bot` twins
differ by `max exp (…)` versus plain, which `canonicalExp` unifies — and `Grid`
can see `canonicalExp`. So Phase 6 proceeds on its own terms, as roadmap §6
originally proposed, and the "do §6 after §4" ordering note no longer applies.

Commit message: `Restate F-adjacency through succ`

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
