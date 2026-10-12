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

Reading the rules against the semantics turned up the problems below. Each
fix is a change to the paper; the first four are todos in `ROADMAP.md`.

| Where | As written | Failure | Fix |
| --- | --- | --- | --- |
| Fig. 5 `rnd♯`, with `ctx(e) = ?` | `rnd♯_?(F) = F` if `F ⊆ F_? = R*` | Always keeps the exact bound under an unknown context, which may round. `t = round(xi)` in `fused_sum` would keep the inputs' format. Fig. 6 shows `R*` there, so the implementation is right and the rule is wrong. | `rnd♯_?(F) = R*`. The side condition "`C` leaves `F_C` unchanged" is false for `?`. |
| Fig. 5/11 `A-Context`, `A-Ctx` | `ctx(e)` "known statically"; `ctx e : •` | Fig. 6 line 5 needs "the format of `out`", but `out` is a parameter with abstract value `•`, so no static `ctx(out)` exists. | Abstract values carry a known context `⟨C⟩`. `R : ⟨R⟩`; `ctx e : ⟨ctx fs⟩` when the record is known. `A-Context` reads the context off `e`'s abstract value. Call-site specialization (A-App) then carries `out`. |
| Table 2, `IEEE754(e, n, RTZ)` | `[max(l, m − p + 1), m]` | `m` is only an upper bound on the leading digit. `v = 1` with interval `[0, 10]` and `p = 3` rounds to `1`, whose digit `0 ∉ [8, 10]`. | Same shape as the next row: `[max(l, μ − p + 1), μ]` with fresh `μ ≤ m`. |
| §4.2 soundness side condition | each context "leaves the values of `F_C` unchanged" | A Mpfx `SpecialMap` need not fix the specials in `F`, so an Mpfx context meets this only when it does (e.g. `SpecialMap.exact`). | State that hypothesis on contexts in the paper. |
| Table 2, `IEEE754(e, n, RTZ)` and "all others" | `[max(l, μ − p + 1), μ]` (fixed) and `[l, μ]` | Both assume rounding never lowers the least significant digit, which fails when a context overflows, or sends a special, to a finite value. IEEE 754 RTZ overflows to the largest finite value: `v = 2^(emax+1)` has interval `[emax+1, emax+1]` but rounds to a value with digit `emax − p + 1`. `Int(n, rm)` with saturation, and any `OverflowMap` or `SpecialMap` with a finite nonzero image, fail the same way. | Join each row with the digits of the context's overflow and special values, or require those to be non-finite (the digit-bound analogue of the §4.2 hypothesis). |
| §4.3, Fig. 6 loop bound | "an accumulating loop that runs `L` times" adds at most `⌈log₂ L⌉` positions | No rule gives this. D-While's `Δ_I = Δ ⊔ Δ′`, with upper endpoints bounded only from above, yields `msb_I ≤ max(msb₀, msb_I + 1)`, which every large `msb_I` satisfies. D-Sum has the bound, but `sum` and `for` are not core FPy, so Fig. 6's bound on `fused_sum` follows from no rule. | A counted-loop rule, or `sum` as an operator with D-Sum. |
| Fig. 12 `D-Logb` | `val(logb x) = msb(x)` | Sound only if the assignment can make `msb(x)` exact, which fails once a constraint bounds `msb(x)` from below. `logb 0 = −∞` gives a non-finite integer term (`e − k` in `fused_sum`), which Theorem 4.2, stated for finite values, does not cover. | Open; settled with the open item on assignments. |
| §5.2 Overflow, the test | `if \|r\| > b` under `C` | `\|·\|` is a rounded operator, so the test sees `C(\|r\|)`. When `C` overflows to NaN (MX E4M3, the running example) or saturates to `b`, an `r` beyond `b` fails the test and `x = r` leaves `F`. | Compare exactly: `r < −b`, `b < r` (unrounded `<`), or under `R`. |
| §5.2 Overflow, the input | no condition on `t` | For `t = ±∞` the rewrite returns `ovf_C`, but `C(±∞)` is the special map's value, which differs when overflow saturates and infinities are kept. | Require `t` finite. The draft applies Overflow after Special, but the rule should say so. |
| §5.2 Special and Overflow | `copysign(C(∞), t)`, `copysign(ovf_C, r)` | Assumes `C(−∞) = −C(∞)` and symmetric overflow; a context's maps need not be symmetric. | Branch on the sign, with one constant per sign. |
| §5.2 FloatToFixed | any `𝒜(p, exp, ∞)` | At `p = 1`, RTO and RNE read parity off the exponent in `𝒜(1, exp)` but off the significand in `𝒜(∞, n)`, so the two can pick different neighbours. This is argued by hand, not proved. | Require `p ≠ 1`, or a mode without parity. |
| §5.2 Rescale | `C_{𝒜(∞,0,2⁻ⁿb)}` "behaves like `C`" | `2ⁿ × C₀(2⁻ⁿt) = C(t)` needs `C₀`'s special and overflow values to be `C`'s scaled by `2⁻ⁿ`; saturation to `b` must become saturation to `2⁻ⁿb`. | State the scaling (`RoundCtx.Scaled`). |

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
arrive as one signature, `fpy`, in Phase 3.

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
- Record labels are distinct by well-formedness, not by a semantic premise:
  `Program.WF` requires every record literal to have distinct labels, and a
  theorem assumes it only where its proof needs it.
- `E-Context` does not check that `e` gives a context; an arithmetic
  operation under a non-context is stuck, since it has no `Val.rnd`.
- `ctx e` requires `e` to give a record in `dom(ρ)`.
- A guard that does not give a boolean, and an operator outside its
  domain, are stuck.

- `Fpy/Value.lean`: `Num`, `Label`, `Val`.
- `Fpy/Syntax.lean`: `Signature`, `Expr`, `Stmt`, `Program`, and
  `Expr.WF`/`Stmt.WF`/`Program.WF`.
- `Fpy/Semantics.lean`: `Store` (`single`, `update`), `Outcome`, `Val.rnd`,
  the mutual `Eval`/`EvalList`/`EvalFields`/`Exec`, `Run` (E-Program).
- `Fpy.lean` root; `lakefile.toml` gains `[[lean_lib]] name = "Fpy"`, and
  `defaultTargets` gains `"Fpy"`.

This is a separate phase because every later phase states its theorems
against these definitions. A wrong rule here, such as scoping, `E-App`'s
fresh store, or `E-Index`, would be found only when its proof fails.

Test: `~/.elan/bin/lake build Fpy`.

### Phase 2 - Format inference and Theorem 4.1

**Done.** It diverged from the plan in these places:

- Lists are described through a mutual `DescribesAll`, so that every proof
  stays structural.
- `A-Arith` takes arguments of any abstract value: `AVal.toFmt` reads a
  non-format as `⊤`.
- `A-Assert` takes any abstract value for its condition. The draft requires
  `•`.
- A statement that cannot return has the return bound `fmt bot`.
- The environment join leaves unbound a variable bound on one side only.
- Two known contexts join to `known C` when they are equal and to `top`
  otherwise. Deciding equality of `Val`s, which contain reals, is the one use
  of `Classical`.
- `with e in s` has two rules, `withCtx` for a known context and
  `withUnknown` for `?`.
- The test file has no `fma` derivation. It has:
  - the collecting analysis, which shows the obligations can be met;
  - `draft_rnd_unknown_unsound`, a witness that the draft's `rnd♯_?` is
    unsound;
  - a derivation in which a context passed as an argument stays known.
- `lakefile.toml` gains the `FpyTest` library, and CI gains the step
  `lake build FpyTest`.

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

Split into three commits, 3a to 3c. It is the only phase that grows
Mpfx-facing proof obligations, and Table 1 is large.

#### Phase 3a - The FPy signature, contexts and the Fig. 4 domain

**Done.** As built:

- `Fpy/Ops.lean`:
  - the IEEE operators on `Num`: `Num.add`, `mul`, `neg`, `sub`, `div`,
    `sqrt`, `fma`, `abs`, `logb`, `exp2`, `min`, `max`, the comparisons, and
    `isNaN`/`isInf`;
  - `ArithOp`, `ExactOp` and their `eval`;
  - `RoundCtx`, which is `(F, S, O, rm)` with `¬ F.IsUndefined rm`, and its
    `round` through `Mpfx.rnd`;
  - the signature `fpy decode`.
- `Fpy/FormatInference/Domain.lean`:
  - `Format.reals`, `fmtJoin` and its containment lemmas;
  - `Fmt` (`set`/`abs`/`top`), `Fmt.join` and `Fmt.domain`;
  - `fpyCtxFmt` and `fpyCtxFmt_sound`, which is the `Analysis.Sound.ctxFmt`
    obligation for Mpfx contexts.
- `Mpfx/Rounding/Op.lean` gains `rnd_mem_values` (`rnd` lands in
  `F.values`) and `rnd_of_mem_values` (`rnd` fixes `F.values` when `S` fixes
  `F.specials`).
- `FpyTest/Ops.lean` checks the special-value choices listed below.

It diverged from the plan in these places:

- The signature is `fpy` in `Fpy/Ops.lean`. The plan's `Std` would shadow
  Lean's `Std` namespace inside `Fpy`.
- `fpy` takes the record layout as a parameter: `decode` reads a record as a
  `RoundCtx`. The draft's `IEEE754(e, n, rm)`, `Fixed(n, rm)` and
  `Int(n, rm)` are particular decodings, and the theorems hold for every one.
- The operators are defined on `Num` (`ℝ`) beside Mpfx's on `Dyadic`, rather
  than reusing them. Phase 3b bridges the two with `toReal`.
- `⌈S⌉` is any `Ceiling`, meaning any abstract format containing `S`. The
  draft's smallest one is an instance; soundness needs only containment.
- The containment check `sub` is exact: it decides `γ F₁ ⊆ γ F₂`
  classically.
- `F_C` is an Mpfx context's format only when `S` fixes the format's
  specials (the fourth `ROADMAP.md` item). Other contexts get `none`, so
  their roundings are bounded by `⊤`.

Special-value choices, none of which the draft states:

- `x / 0` is an infinity of `x`'s sign, `0 / 0` is NaN, and a finite value
  over an infinity is `0`.
- `√` of a negative number, or of `−∞`, is NaN.
- `logb 0 = −∞` and `logb (±∞) = +∞`, as IEEE `logB`.
- `exp2 (−∞) = 0`.
- `min` and `max` propagate NaN, as IEEE 754-2019 `minimum`/`maximum`.
- Comparisons involving NaN are false.

Test: `~/.elan/bin/lake build Fpy.Ops Fpy.FormatInference.Domain FpyTest`.

#### Phase 3b - Table 1

**Done.** As built:

- `Fpy/FormatInference/Ops.lean`, the abstract counterpart of `Fpy/Ops.lean`.
  The plan called it `Table1.lean`. It holds:
  - `ArithOp.fmt`, which is `op♯`, with `ArithOp.fmt_sound`;
  - `ExactOp.aval`, which is `exact♯`, with `ExactOp.aval_sound`;
  - the `toReal` bridges between the `Num` operators and Mpfx's `Dyadic`
    ones;
  - the rows `addFmt`, `mulFmt` (`p̂₁ ⊞ p̂₂` through `precMul` and
    `Format.pHat`), `logbFmt` and `exp2Fmt`;
  - `lift2`, `lift1` and `liftCeil`, which act element-wise on sets and use
    `⌈S⌉` where a set meets an abstract format.
- `Mpfx/Format/Inference.lean` gains `Format.bitsFor` and
  `precisionAtMost_bitsFor`, the precision a value needs given its quantum and
  a bound. `add_prec_finite` now goes through it.
- `FpyTest/FormatInference/Ops.lean` checks `bitsFor` and `precMul`.

It diverged from the plan in these places:

- Each row also states the specials its operator can produce:
  - `logbSpecials` and `exp2Specials` for the new rows;
  - Mpfx's `mulSpecials`, `addSpecials` and `absSpecials`, and negation, for
    the rest.

  Table 1 has none, which is unsound for `logb` (`ROADMAP.md`).
- `−` is `addFmt F₁ (opNeg F₂)`: Table 1's "same as `x + y`", with the
  specials of `−F₂`.
- `min` and `max` use the join `fmtJoin`, as Table 1's `A₁ ⊔ A₂`.
- `len` gives the integers `𝒜(∞, 0, ∞)`. The draft gives list lengths
  finite sets, but a list's abstract value does not track its length.
- `÷`, `√` and `fma` are `R*` on sets too, as in Table 1.

#### Phase 3c - Condition refinement

**Done.** As built:

- `Fpy/FormatInference.lean` is split into `Fpy/FormatInference/Defs.lean`
  (the domain interface, abstract values, environments, `Analysis`, the
  rules and `Analysis.Sound`) and `Fpy/FormatInference/Sound.lean` (their
  lemmas and Theorem 4.1). `Fpy/FormatInference/Domain.lean` and
  `Ops.lean` need only `Defs`.
- `Fpy/FormatInference/Refine.lean`:
  - `Atom` is a test `g(x) ⋈ c`, or `c ⋈ g(x)`, with `g` one of `x`, `|x|`
    and `logb x`, and `⋈` one of `<`, `≤` and `=`. `parseAtom` reads one off
    an expression.
  - `Atom.narrow` and `Atom.narrowFmt` narrow a format by a test.
  - `refine` handles atoms, `not`, a true `and` and a false `or`.
  - `refine_sound` is the `Analysis.Sound.refine` obligation.
- `Fpy/FormatInference/Analysis.lean`:
  - `fpyAnalysis` assembles the pieces;
  - `ctxOfAVal` reads a known context off a constant record, through
    `AVal.const?`;
  - `fpyAnalysis_sound` discharges every obligation;
  - `fpy_run_sound` is Theorem 4.1 for FPy.
- `FpyTest/FormatInference/Refine.lean` checks the §4.2 example: `{1, 2, 4}`
  refined by `x < 3` keeps `2` and drops `4`.

How refinement is pinned down, since the draft gives only examples:

- `|x|` and `logb x` are unfolded only under `R`, where they are exact. Under
  a rounding context, `round(|x|) ⋈ c` says nothing exact about `|x|`.
- The conditions for narrowing are semantic: "every finite `g(x)` passing
  the test is at most `c`" for the bound, and "at least `c`, and not `−∞`"
  for the exponent. This covers every comparison and outcome that implies
  the bound, without a case for each operator. For example, the false
  branch of `|x| > c` lowers the bound to `c`.
- The bound must be a dyadic constant, and the exponent uses `k = ⌈c⌉`.
- Narrowing changes only the bound or exponent, never the specials. A true
  comparison excludes NaN, and could remove it from the specials; the
  draft does not ask for this.
- `isNaN` and `isInf` tests are not refined. Fig. 9's `isnan(t) or …` would
  need them to drop NaN in the else branch. That is an extension; the
  draft's §4.2 lists only comparisons.

Test: `~/.elan/bin/lake build Fpy.FormatInference.Refine Fpy.FormatInference.Analysis FpyTest`.

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
`Fixed`/`IEEE754` off `fpy`'s `ρ`.

Test: `~/.elan/bin/lake build Fpy.DigitBound FpyTest`.

### Phase 5 - Rewrite framework

- `Fpy/Rewrite.lean`:
  - `Equiv Γ C s s'`: for every store in `Γ` and every outcome, `s` and `s'`
    reach the same outcome under `C`, with fresh variables treated as decided
    in the open items;
  - congruence through every statement form;
  - the whole-program theorem: rewriting one site whose condition holds, for
    the `Γ` and `C` that format inference assigns there, preserves `Run`;
  - each rewrite preserves `Program.WF`.

This is separate from the individual rewrites because it is the
compiler-correctness theorem, and it is the same for all eight rewrites.

**Done**, ahead of Phase 4, which waits on a rewrite of the draft's §4.3. It
needs only Phase 2. As built:

- `Fpy/Rewrite.lean`:
  - `Store.Agree`/`Outcome.Agree`: agreement outside the fresh set `X`.
  - `Equiv Φ X Γ κ s s'`, the correctness of a local rewrite: from the same
    store in `Γ`, both directions, outcomes agreeing outside `X`.
  - `Sim Φ Φ' X Γ κ s s'`: the same across two programs, from stores that
    agree outside `X`.
  - `Rw`/`RwExpr`, the placement of rewrites: a judgment that follows
    format inference through each statement, with a `site` rule taking any
    `Sim`.
  - `Rw.sim` (congruence), `Sim.equiv` (a local `Equiv` at a site), and
    `run_iff_of_rw` (the whole-program theorem).
- `FpyTest/Rewrite.lean`: `x = e ⇝ t = e; x = t` with a fresh `t`, proved as
  an `Equiv` and carried through `run_iff_of_rw` on a toy program.

It diverged from the plan in these places:

- `Rw` allows any number of sites, not one; a single site is the special
  case.
- A site inside a callee is checked at every call the analysis visits:
  `RwExpr.call` requires `Rw` of the callee's body under that call's
  argument bound. Functions the analysis never reaches may differ freely
  between `Φ` and `Φ'`.
- Both directions are proved (`exec_fwd`, `exec_bwd`), so `Run` is
  preserved as an iff.
- `Rw` takes the `AExec`/`AEval` derivations it needs as premises (at `seq`,
  `whileDo` and `withCtx`) rather than mirroring every rule of Fig. 11.
  Guards get `RwExpr` premises, which `AExec` does not have.
- `Program.WF` preservation is per rewrite, so it moves to Phases 6 and 7.

Test: `~/.elan/bin/lake build Fpy.Rewrite FpyTest`.

### Phase 6 - Rewrites of §5.1

- `Fpy/Rewrite/Separate.lean`:
  - `Elim` and `Insert`, from `ctxFmt`'s fixes-`F_C` obligation;
  - `Split`, under the hypothesis `C ∘ C' = C`, with instances from
    `rndRTO_RN`, `rndRTO_RTZ`, … and the trivial `C' = R`;
  - `SplitOp`, with instances from Roux (`rndAdd`, `rndMul_*`, `rndDiv_*`,
    `rndSqrt_*`).

**Done.** As built:

- `Fpy/Rewrite/Separate.lean`:
  - two cores with semantic conditions on the values `Γ` allows for `y⃗`:
    `equiv_reround`, which rounds under `C'` instead of `C`, and
    `equiv_split_of`, which rounds under `C'` into a fresh `t` and then
    applies `round(t)`;
  - the draft's four rewrites as corollaries: `equiv_elim`, `equiv_insert`,
    `equiv_split` and `equiv_splitOp`;
  - `wf_reround` and `wf_split`;
  - for FPy:
    - `fpy_rnd_ctx` and `fpy_round`;
    - `RoundCtx.round_round`, which turns any total rule (`rndRTO_RN`,
      `rndRTZ_RTZ`, …) into Split's condition;
    - `RoundCtx.round_round_of`, the same at one input;
    - `splitOp_add`, `splitOp_mul`, `splitOp_div` and `splitOp_sqrt`, which
      take Roux's finite rule as a hypothesis.
- `Fpy/Rewrite.lean` gains `Store.Agree.update_fresh`.
- `FpyTest/Rewrite/Separate.lean` checks two instances:
  - Split through round-to-odd (`rndRTO_RN`);
  - SplitOp for `+` (`rndAdd`).

It diverged from the plan in these places:

- The rewrites act on `x = op(y⃗)` over variables, as the draft writes them.
  Arguments that are expressions would be evaluated under the new context.
- `C'` is written by any expression that denotes it (`Denotes`), and
  `round` is any operator computing the identity.
- Both contexts must have rounding functions (`C.rnd L = some r`). `with e in s`
  does not check that `e` gives a context, so the current context may have
  none.
- SplitOp takes any set `S` containing each `fmt(yᵢ)`. The draft's `S = F_C`
  is one instance.
- The SplitOp instances need:
  - an unbounded intermediate format (`F₂.b = ⊤`), since Roux's rules ignore
    bounds;
  - `F₂`'s special map to compose with `F₁`'s (`SpecialMap.Composes`).

  A bounded intermediate would need `OverflowAgrees` at one input, which
  Mpfx states only for all inputs.
- The source `x = op(y⃗)` is always well formed, so preserving `Program.WF`
  means the target is well formed when the context expression is.

Test: `~/.elan/bin/lake build Fpy.Rewrite.Separate FpyTest`.

### Phase 7 - Rewrites of §5.2

- The rounding identities, one per rewrite:
  - `FloatToFixed`: for finite nonzero `t`,
    `rnd A(p, exp, ∞) t = rnd A(∞, max(logb t − p + 1, exp), ∞) t`;
  - `Rescale`: `rnd A(∞, n, b) t = 2ⁿ · rnd A(∞, 0, 2⁻ⁿ b) (2⁻ⁿ t)`;
  - `Overflow`, with its threshold form via monotonicity (the `464` example);
  - `Special`.
- `Fpy/Rewrite/Lower.lean`: each identity as a rewrite through Phase 5.

**Done.** As built:

- `Fpy/Rewrite/Lower.lean`:
  - the identities:
    - `rndInt_congr`: the integer step depends on the format only through the
      parity of the floor point;
    - `rndUnbounded_eq_fixed` (FloatToFixed, `p ≠ 1`);
    - `rndUnbounded_scale` (Rescale);
  - `overflows_iff_of_threshold`: Overflow's threshold condition from
    monotonicity;
  - on contexts:
    - `RoundCtx.round_finite`, `round_special`, `round_zero` and
      `round_of_overflows`;
    - `round_unbounded`, `round_fixed` and `round_scale`;
    - `RoundCtx.Scaled`;
  - the rewrites: `equiv_special`, `equiv_overflow`,
    `equiv_overflow_threshold`, `equiv_floatToFixed` and `equiv_rescale`.
    Special's three branches are optional (`nanBranch`, `infBranch`,
    `zeroBranch`): a branch computes what `round(t)` would, so the draft's
    omission of unreachable branches needs no condition;
  - `wf_special`, `wf_overflow`, `wf_overflow_threshold`, `wf_floatToFixed`
    and `wf_rescale`.
- `Fpy/Semantics.lean` gains determinism: `Eval.det`, `EvalList.det`,
  `EvalFields.det` and `Exec.det`.
- `Fpy/Rewrite.lean` gains:
  - `Equiv.of_fwd`: by determinism, one direction plus "the target runs only
    where the source does";
  - `Store.agree_update_of_mem`.
- `Fpy/Rewrite/Separate.lean`: `Denotes` is `DenotesAt` at every store.
- Mpfx:
  - `Mpfx/Rounding/Parity.lean` exposes `neighbor_abs_le`,
    `isOdd_neighbor_iff` and `isEven_neighbor_iff`, factored out of
    `neighbors_alternate`;
  - `Mpfx/Rounding/Monotone.lean`: `RoundsFinite.mono` in every mode.
- `FpyTest/Rewrite/Lower.lean`: MX E4M3 under RNE overflows exactly beyond
  `±464` (`e4m3_overflows_iff`), and the threshold rewrite for an E4M3 context.

It diverged from the plan in these places:

- The identities live in FPy, not Mpfx: Mpfx keeps formats and rounding, and
  lowering is FPy's. Monotonicity is a rounding fact, so it is in Mpfx.
- The draft's rules are fixed as in the problem table:
  - Overflow compares exactly and needs finite `t`;
  - `copysign` becomes a sign branch;
  - FloatToFixed needs `p ≠ 1`;
  - Rescale states the scaling of the maps.
- Contexts built at run time are expressions with a store-dependent
  denotation. FloatToFixed takes `cf` with `DenotesAt` at every store where
  `n` holds an integer `k`, giving a context into `𝒜(∞, k, ∞)` with `C`'s mode.
- The claim is each rewrite on its own, not their composition. Out of scope:
  - Fig. 9's derivation;
  - Rescale after FloatToFixed, whose site has a context known only at run
    time;
  - establishing one rewrite's conditions from another's output, e.g. finite
    `t` after Special, which would need `refine` to narrow on `isnan`/`isinf`.
- Rescale takes a constant `k`, as `F_C = 𝒜(∞, k, b)` states.
- Finiteness conditions are semantic, over the stores of `Γ`.
- Determinism, an open item, is proved here because it halves each rewrite's
  proof.

Test: `~/.elan/bin/lake build Fpy.Rewrite.Lower FpyTest`, and `lake test` for
the Mpfx changes.

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

Provisional: abstract through Phase 2, then `fpy` from Phase 3. The digit
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

Settled in Phase 5 without liveness: outcomes agree outside `X`, the
original program reads no variable of `X` (`RwExpr.var`), and the `Γ` at
each site binds none (`Sim.equiv`).

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

Settled in Phase 7: in `Fpy/Rewrite/Lower.lean`. Mpfx provides formats and
rounding; lowering is FPy's.

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

Settled in Phase 7: proved (`Exec.det`, …), because `Equiv.of_fwd` uses it to
derive each rewrite's reverse direction.

### Should `min`/`max` propagate NaN, or return the other operand?

IEEE 754-2019 has both: `minimum`/`maximum` propagate NaN, and
`minimumNumber`/`maximumNumber` return the non-NaN operand. Hardware
specifications use either, and C's `fmin` is the second.

Provisional: NaN propagates (`Num.min`, `Num.max`). Reopen if a benchmark
specification needs the other. The fix is then a second pair of operators,
not a change to these.
