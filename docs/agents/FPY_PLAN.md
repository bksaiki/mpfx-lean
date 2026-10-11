# FPy: mechanizing the compiler paper's theorems

Implementation plan.  The design is settled; what follows is the phase
breakdown, one phase per commit.

## Working policy

- **Pause after each phase for review.** Do not begin the next phase until the
  current one has been looked at.
- **Do not commit.** The author of the change leaves the working tree dirty;
  commits are made by the repository owner.
- **Run only the tests relevant to the phase.** The full unit suite runs once,
  at the end, after the last phase.
- **Comments stay succinct**, and notes about *process* (what was tried, what
  a phase decided, why an ordering was chosen) belong in this document, not in
  source comments.
- **The Lean is the source of truth.** A bug found in the paper goes into the
  FPy section of `ROADMAP.md` when it is found, and the Lean states the fixed
  rule.

## Context

The PLDI draft (`main.pdf`, untracked) makes three technical claims:

| Section | Claim | Stated as |
| --- | --- | --- |
| §3, Fig. 2/3/10 | FPy: big-step semantics with first-class, dynamically scoped rounding contexts | definition |
| §4.2, Fig. 4/5/11, Table 1 | Format inference over full FPy is sound | Theorem 4.1, proof sketch |
| §4.3, Fig. 7/8/12, Table 2 | Digit-bound analysis is sound | Theorem 4.2, proof sketch |
| §5.1 | `Elim`, `Insert`, `Split`, `SplitOp` preserve semantics under their conditions | prose ("the rewrite is correct because …") |
| §5.2 | `Special`, `Overflow`, `FloatToFixed`, `Rescale` preserve semantics | prose |
| §1, §7 | "Each rewrite has a safety condition, so compilation preserves semantics"; "safety conditions proved in Lean (ideally)" | claim |

Mpfx today has no language. It has what the rewrites rest on: `Format`, the
rounding function `rnd` and its spec, the double-rounding rules (which back
`Split`/`SplitOp`: `rndRTO_RN`, Roux's `rndAdd`, `rndMul_*`, …), and §6.1
format arithmetic (`Format.mul_subset`, `add_subset`, `neg_subset`,
`abs_subset`), which backs part of Table 1.

### What a PL paper of this kind proves

Reviewers expect, for a compiler paper with a semantics, analyses and
rewrites:

1. **Soundness of each analysis** against the semantics (Theorems 4.1, 4.2).
2. **Semantic preservation of each rewrite**: a local equivalence under its
   condition, plus a congruence theorem lifting local equivalence to the whole
   program. Together these give the compiler-correctness statement the
   introduction already makes. Without the congruence theorem, per-rewrite
   lemmas do not add up to "compilation preserves semantics".
3. Not expected here: type safety (FPy has no type system), completeness or
   optimality of the analyses, and termination of the implementation's
   fixpoint (widening makes it routine and the paper says so).

### Problems found in the draft

Reading the rules against the semantics turned up two unsound rules and two
gaps. Each fix below is a change to the paper, and each is a todo in
`ROADMAP.md`.

| Where | As written | Failure | Fix |
| --- | --- | --- | --- |
| Fig. 5 `rnd♯`, with `ctx(e) = ?` | `rnd♯_?(F) = F` if `F ⊆ F_? = R*` | Always keeps the exact bound under an unknown context, which may round. `t = round(xi)` in `fused_sum` would keep the inputs' format. Fig. 6 shows `R*` there, so the implementation is right and the rule is wrong. | `rnd♯_?(F) = R*`. The side condition "`C` leaves `F_C` unchanged" is false for `?`. |
| Fig. 5/11 `A-Context`, `A-Ctx` | `ctx(e)` "known statically"; `ctx e : •` | Fig. 6 line 5 needs "the format of `out`", but `out` is a parameter with abstract value `•`, so no static `ctx(out)` exists. | Abstract values carry a known context `⟨C⟩`. `R : ⟨R⟩`; `ctx e : ⟨ctx fs⟩` when the record is known. `A-Context` reads the context off `e`'s abstract value. Call-site specialization (A-App) then carries `out`. |
| Table 2, `IEEE754(e, n, RTZ)` | `[max(l, m − p + 1), m]` | `m` is only an upper bound on the leading digit. `v = 1` with interval `[0, 10]` and `p = 3` rounds to `1`, whose digit `0 ∉ [8, 10]`. | Same shape as the next row: `[max(l, μ − p + 1), μ]` with fresh `μ ≤ m`. |
| §4.2 soundness side condition | each context "leaves the values of `F_C` unchanged" | A Mpfx `SpecialMap` need not fix the specials in `F`, so an Mpfx context meets this only when it does (e.g. `SpecialMap.exact`). | State that hypothesis on contexts in the paper. |

Two more points are not wrong but are unspecified. Theorem 4.2's
per-value assignments, and its statement for statements and loops, are open
items below.

## Design

### One package, a second library

`Fpy` is a new `lean_lib` in this Lake package, beside `Mpfx`. `Fpy` imports
`Mpfx`, and `Mpfx` never imports `Fpy`. `defaultTargets` includes `Fpy`, so
CI's `lake build` checks it. Sharing the package avoids a second Mathlib
checkout and toolchain pin.

### Operators are abstract

A `Signature` names the rounded (`ArithOp`) and unrounded (`ExactOp`)
operators, their meaning (`arith`, `exact`), and the map `ρ` from records to
rounding functions. The semantics and both soundness theorems hold for every
signature. This is the paper's own claim made literal: "any representation of
formats that meets the interface is sound". The concrete operators of Table 1
arrive as one signature, `Fpy.Std`, in Phase 3.

### Semantics, rule for rule

- `Num := Mpfx.WithSpecial ℝ`.
- `Val`: `bool`, `num`, `list`, `record`, and the two contexts, `real` (`R`)
  and `ctx fs`.
- `Eval`, `EvalList`, `EvalFields` and `Exec` form one mutual inductive. They
  follow Fig. 10 rule for rule, including `E-While-True` unrolling through
  `seq`.
- `Val.rnd` is `C(·)`. A value that is not a context has none, so arithmetic
  under it is stuck.

### Analyses are declarative judgments

Each analysis is an inductive relation mirroring its figure: `AEval`/`AExec`
for Fig. 11, and the digit-bound analogue for Fig. 12. Soundness is proved of
the rules, not of the implementation's fixpoint algorithm.

Where a rule needs a domain operation, it uses a function with a soundness
obligation:

- join;
- the containment check;
- `op♯`;
- `ctxFmt` (`F_C`);
- condition refinement `⟦e⟧♯`.

The obligations are bundled as the hypotheses of the soundness theorem.

`Γ ⊑ Γ'` is semantic: every store in `Γ` is in `Γ'`. This is weaker than the
pointwise order, so the theorem is stronger.

### Proof shape

The paper's sketch is used directly. The proof recurses mutually and
structurally on the concrete derivation and inverts the abstract one. Loops
need no separate inner induction: `whileTrue` matches its unrolled
`seqNormal`, and the proof recurses on the remaining loop derivation.

## Phases

### Phase 1 - Syntax and semantics

**Done.** Fig. 10 leaves some cases unstated. The Lean settles them as
follows; none contradicts the paper:

- `E-Index` takes an index that evaluates to a finite natural `k < m`.
- `E-Proj` takes the first field with the label (`List.lookup`).
- `E-Context` does not check that `e` gives a context; an arithmetic
  operation under a non-context is stuck, since it has no `Val.rnd`.
- `ctx e` requires `e` to give a record in `dom(ρ)`.
- A guard that does not give a boolean, and an operator outside its
  domain, are stuck.

- `Fpy/Value.lean`: `Num`, `Label`, `Val`.
- `Fpy/Syntax.lean`: `Signature`, `Expr`, `Stmt`, `Program`.
- `Fpy/Semantics.lean`: `Store` (`single`, `update`), `Outcome`, `Val.rnd`,
  the mutual `Eval`/`EvalList`/`EvalFields`/`Exec`, `Run` (E-Program).
- `Fpy.lean` root; `lakefile.toml` gains `[[lean_lib]] name = "Fpy"`, and
  `defaultTargets` gains `"Fpy"`.

This is a separate phase because every later phase states its theorems
against these definitions. A wrong rule here, such as scoping, `E-App`'s
fresh store, or `E-Index`, would be found only when its proof fails.

Test: `~/.elan/bin/lake build Fpy`.

### Phase 2 - Format inference and Theorem 4.1

- `Fpy/FormatInference.lean`:
  - `FormatDomain`: `Fmt`, `γ`, `top`, `bot`, `join`, `sub`, `ofNum`, with
    their soundness fields.
  - `AVal`: `fmt`, `list`, `record`, `other` (`•`), `known` (`⟨C⟩`), `top`.
  - `Describes`/`DescribesFields`, `AVal.join`, `joinAll`, and `AEnv` with
    `Holds`, `join`, `update` and semantic `⊑`.
  - `Analysis`: `arith`, `exact`, `ctxFmt`, `ctxOf`, `refine`, and `rnd♯` with
    the `?` fix.
  - The mutual `AEval`/`AEvalList`/`AEvalFields`/`AExec`, mirroring Fig. 11
    with the context fixes.
  - `Analysis.Sound`, the obligations.
  - `eval_sound` (Theorem 4.1), `exec_sound` (the statement form), and
    `run_sound` (A-Program).
- `FpyTest/FormatInference.lean`: a two-operator toy signature. It has a
  derivation for `fma` (§3.2) and one showing that `with ? in` loses the
  bound.

This phase depends only on Phase 1. Everything after it either instantiates
it (Phase 3) or uses its soundness to transport `Γ` to a rewrite site
(Phase 5).

Test: `~/.elan/bin/lake build Fpy.FormatInference FpyTest`.

### Phase 3 - The paper's domain on Mpfx formats

- `Fpy/Std.lean`, the concrete signature `Std`:
  - arith: `+ − × ÷ √ fma neg abs logb exp2 min max round cast`;
  - exact: `< ≤ = len isnan isinf and or not`.
  - Their meaning follows IEEE 754 special-value rules, reusing
    `Mpfx.WithSpecial` arithmetic where Mpfx has it.
  - `ρ` reads a record as `(F, S, O, rm)` and rounds with `Mpfx.rnd`.
    Records whose `(F, rm)` is `IsUndefined` are outside `dom(ρ)`.
- `Fpy/FormatInference/Domain.lean`, Fig. 4:
  - `Fmt ::= set S | abs F | top`, where `F : Mpfx.Format`;
  - join, including `⌈S⌉`;
  - `ctxFmt` with its obligation: an Mpfx context rounds into `F.values`, and
    fixes `F.values` when `S` fixes `F.specials`.
- `Fpy/FormatInference/Table1.lean`: soundness of each `op♯` row.
  - `×`, `+`, `−`, `neg` and `abs` reduce to `Format.mul_subset`,
    `add_subset`, `neg_subset` and `abs_subset`.
  - `logb`, `exp2`, `min`, `max` and `round` are new.
- `Fpy/FormatInference/Refine.lean`: refinement by `x ⋈ c`, and the `|x|` and
  `logb` unfoldings of §4.2. This includes the narrowing
  `A(p, exp, b) → A(p, max(exp, k − p + 1), b)`.

This is a separate phase because it is the only one that grows Mpfx-facing
proof obligations, and Table 1 is large. If review prefers, it can split
into domain plus contexts, Table 1, and refinement, one commit each.

Test: `~/.elan/bin/lake build Fpy.FormatInference.Domain Fpy.FormatInference.Table1 Fpy.FormatInference.Refine FpyTest`.

### Phase 4 - Digit-bound analysis and Theorem 4.2

- `Fpy/DigitBound.lean`:
  - terms `τ`, constraints `φ`, `digits(v)`, digit intervals with `∅`, and
    assignments `ι`;
  - the mutual judgment of Fig. 12, with fresh variables made explicit;
  - Table 2 with the RTZ-row fix, each row with its soundness lemma.
- `eval_sound` and `exec_sound` in the form fixed by the open item on
  assignments.
- The format-inference constraint import ("each interval lies within the
  inferred format's range") is a premise discharged by Phase 2's soundness.

This phase comes after Phase 3 because Table 2's context rows read
`Fixed`/`IEEE754` off `Std`'s `ρ`.

Test: `~/.elan/bin/lake build Fpy.DigitBound FpyTest`.

### Phase 5 - Rewrite framework

- `Fpy/Rewrite.lean`:
  - `Equiv Γ C s s'`: for every store in `Γ` and every outcome, `s` and `s'`
    reach the same outcome under `C`, with fresh variables treated as decided
    in the open items;
  - congruence through every statement form;
  - the whole-program theorem: rewriting one site whose condition holds, for
    the `Γ` and `C` that format inference assigns there, preserves `Run`.

This is separate from the individual rewrites because it is the
compiler-correctness theorem, and it is the same for all eight rewrites.

Test: `~/.elan/bin/lake build Fpy.Rewrite FpyTest`.

### Phase 6 - Rewrites of §5.1

- `Fpy/Rewrite/Separate.lean`:
  - `Elim` and `Insert`, from `ctxFmt`'s fixes-`F_C` obligation;
  - `Split`, under the hypothesis `C ∘ C' = C`, with instances from
    `rndRTO_RN`, `rndRTO_RTZ`, … and the trivial `C' = R`;
  - `SplitOp`, with instances from Roux (`rndAdd`, `rndMul_*`, `rndDiv_*`,
    `rndSqrt_*`).

Test: `~/.elan/bin/lake build Fpy.Rewrite.Separate FpyTest`.

### Phase 7 - Rewrites of §5.2

- The rounding identities, one per rewrite:
  - `FloatToFixed`: for finite nonzero `t`,
    `rnd A(p, exp, ∞) t = rnd A(∞, max(logb t − p + 1, exp), ∞) t`;
  - `Rescale`: `rnd A(∞, n, b) t = 2ⁿ · rnd A(∞, 0, 2⁻ⁿ b) (2⁻ⁿ t)`;
  - `Overflow`, with its threshold form via monotonicity (the `464` example);
  - `Special`.
- `Fpy/Rewrite/Lower.lean`: each identity as a rewrite through Phase 5.

Test: `~/.elan/bin/lake build Fpy.Rewrite.Lower FpyTest` (plus the Mpfx file
holding the identities, per the open item).

### Phase 8 - Docs

- README: an FPy section, a theorem table in the Mpfx section's style
  (paper → Lean name → file), and layout rows.

Test: none (markdown).

### After the last phase

```sh
~/.elan/bin/lake build              # Mpfx and Fpy; the Mathlib linter set runs here
~/.elan/bin/lake test               # MpfxTest
~/.elan/bin/lake build FpyTest
```

There is no separate lint command: `weak.linter.mathlibStandardSet` runs
during the build, and a clean build has no warnings.

## Open items

Every item below was settled with its provisional call. Each reopen condition
still stands.

### Same Lake package, or a separate `Fpy/` package requiring `mpfx`?

A separate package (`Fpy/lakefile.toml`, `require mpfx from ".."`) makes
the dependency direction structural and lets FPy pin its own Mathlib. The
cost is a second Mathlib checkout, and CI building two packages.

Provisional: same package, second `lean_lib`. Reopen if FPy needs a different Mathlib or toolchain, or should be
published apart from Mpfx.

### Abstract `Signature`, or concrete operators throughout?

Abstract operators make Theorem 4.1 literally the paper's interface claim and
keep the core proofs small. A concrete operator type would let rules
mention `+` or `logb` by name (Fig. 8's `D-Linear`, `D-Logb`, `D-Max`) without
an interface for "integer operators with term transfers".

Provisional: abstract through Phase 2, then `Std` from Phase 3. The digit
analysis takes an interface for integer-term transfers, as Table 2 already
tabulates them. Reopen if that interface needs more than Table 2's rows.

### Does the paper adopt the four fixes above?

The Lean statements will follow the fixed rules. If the paper keeps the
original `rnd♯_?`, `ctx(e)` or Table 2 row, the mechanization proves a
different system from the one printed.

Provisional: Phases 2 and 4 use the fixes, which are recorded in
`ROADMAP.md`.

### Theorem 4.2: one assignment per run, or one per value?

The draft says different values of `x` "may use different assignments", but
`D-Sum` and `D-List` relate several values at once, so a list's elements need
one shared assignment. Whether two loop iterations share one decides the
statement form for loops, which the draft does not give.

`D-Logb` sets `val(logb x) = msb(x)`, which is sound only if the assignment
can make `msb(x)` tight. That fails if any constraint bounds `msb(x)` from
below. `logb 0` is unspecified.

Provisional: one assignment per value of an expression; lists share one; at a
loop, an assignment per iteration that agrees on `Δ`'s variables. Reopen at
the first proof obligation in Phase 4 that does not go through.

### What does "up to fresh variables" mean for rewrite equivalence?

The options:

- outcomes agree on all variables except a declared fresh set;
- fresh variables must be dead after the site;
- the rewrite's output resets them.

The first is simplest to state, but congruence then needs the fresh set to
avoid variables the context reads.

Provisional: agreement outside a fresh set disjoint from the program's
variables. Reopen if Phase 5's congruence needs liveness.

### Mechanize only the rules, or also the implementation's algorithm?

The theorems cover any derivation. They do not cover the implementation's
widening iteration, set-size cap and Z3 maximization, which only produce
derivations. A reviewer could ask for the algorithm, or the paper could
claim only the rules.

Provisional: rules only. The paper should say "the rules are sound" and
describe the implementation as constructing derivations. Reopen if the paper
wants an extracted checker.

### Where do the §5.2 rounding identities live?

`FloatToFixed`, `Rescale` and `Overflow` are facts about `Mpfx.rnd` and
formats, with no FPy in them. They fit `Mpfx/Rounding/` next to `Ulp.lean`,
and they make Mpfx more useful on its own. Putting them in `Fpy/` keeps Mpfx
scoped to the double-rounding paper.

Provisional: `Mpfx/Rounding/Lower.lean`, cited from `Fpy/Rewrite/Lower.lean`.

### `FpyTest` as its own library, or inside `MpfxTest`?

Lake has one `testDriver`, so a separate `FpyTest` needs its own CI step.
Folding it into `MpfxTest` keeps `lake test` covering everything, at the cost
of mixing the projects.

Provisional: a separate `FpyTest` library and a CI step
`lake build FpyTest`, added in Phase 2.

### Prove determinism of the semantics?

It is not needed: equivalence is stated over outcomes, so it is a relation
either way. It would let the paper read rewrites as equalities of functions,
and it is cheap, since every rule is syntax-directed except `iteTrue` and
`iteFalse`, which disagree on the guard.

Provisional: no. Add it to Phase 5 if the paper's prose wants
"computes the same value".
