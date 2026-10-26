# Roadmap: digit-bound analysis as a constraint-based analysis

One of three parallel roadmaps answering the same criticism of the FPy paper's
§4.3: the digit-bound analysis generates constraints and hands them to Z3,
instead of computing a sound abstract value at each program point by
iteration. The roadmaps differ only in how the paper frames the analysis:

| Roadmap | Framing |
|---|---|
| `DIGIT_BOUND_ROADMAP.md` | Abstract interpretation over a logical domain, with widening at loops |
| **This file** | **Constraint-based analysis; no claim to be an abstract interpretation** |
| `DIGIT_BOUND_SYMBOLIC_ROADMAP.md` | Symbolic abstraction (Reps–Sagiv–Yorsh): constraints as a symbolic description, Z3 as the abstraction function |

Check an item off when it lands. References are Lean names under
`namespace Fpy.DigitBound` and files under `Fpy/DigitBound/`, never line
numbers. The implementation lives in the `fpy` repository under
`fpy2/analysis/digit_bound/`.

**Framing:** the analysis is split into generating constraints and solving
them.

| Part | In the formalism |
|---|---|
| Unknowns | Integer variables standing for each value's least and most significant digit positions |
| Generation | The rules (`DEval`, `DExec`) emit constraints over those variables |
| Soundness | The run's actual digit positions satisfy every constraint (`exec_sound`) |
| Solving | Z3 bounds `msb − lsb + 1` over all solutions (`prec♮`) |
| Loops | Each loop-carried value gets fresh variables bounded by format inference's loop invariant; no fixpoint is computed |

The paper states plainly that there is no fixpoint iteration. Soundness rests
on every constraint holding for every execution. It does not present the
rules in the style of type inference.

**What this framing gives up:** it does not answer "this is not an abstract
interpretation" by agreeing to become one. It must instead argue that
constraint-based analysis is an established alternative. A reviewer
committed to abstract interpretation may remain unconvinced.

**Pending experiment:** `fpy/docs/todos/digit-bound-no-smt.md` tests whether
zones or linear templates match Z3's bounds.

## Lean

- [ ] **Syntactic constraints.** `Con` becomes a fresh variable plus a list
  of `t ≤ t'` pairs over `Term`, with `P` defined by evaluation. Port the five
  constructions `Con.ext`, `Con.lower`, `Con.upper`, `Con.between`
  (`Defs.lean`) and `Con.copy` (`Copy.lean`), which becomes renaming
  variables inside a term. This is what makes "decidable constraints" a
  theorem rather than a claim.
- [ ] **The query as a definition.** Define
  `prec♮ Ψ l m := sup {m(ι) − l(ι) + 1 | ι ⊨ Ψ}` and state `run_precision`
  (`Sound.lean`) with it.
- [ ] **A loop rule matching the implementation.** Today D-While
  (`DExec.whileDo`) takes an invariant, and its back-edge premise compares
  digit-bound states without format inference's facts, so it may not accept
  the implementation's invariant. Here, replace or supplement it with a
  primitive rule:
  - each loop-carried value gets fresh variables bounded by its format in
    format inference's `Γᵢ`;
  - the body is analyzed from that state;
  - there is no back-edge premise.

  Prove it sound directly in `exec_sound`, from format inference's soundness
  at every iteration. This avoids changing the order (`DEnv.Le`), which the
  abstract-interpretation roadmap needs.
- [ ] **Integer encoding.** A lemma that a constraint over ℤ ∪ {±∞} (`EInt`)
  holds exactly when its integer encoding with "not `+∞`" / "not `−∞`" guard
  literals does, as `DigitBoundStore.high` and `DigitBoundStore.not_neg_inf`
  build it. New file `Encode.lean`.
- [ ] **Every rounding, not only the result.** A semantics that records each
  evaluation of a subexpression (`Fpy/Semantics.lean`), and a corollary of
  `eval_sound` over it.
- [ ] **Docs.** Add the new theorems to the README's §4.3 table. The "Rules
  only, not the implementation's algorithm" decision in
  `docs/agents/FPY_PLAN.md` stands, except that the loop rule now matches the
  implementation.
- [ ] *(Only if the paper claims it.)* **A `for` rule** matching the
  implementation's "one generic iteration plus a copy of the previous one".
  `Stmt` has no `for` today.

## Paper

- [ ] **Figure 9 matches the Lean.** Apply the table under "Figure 9 and the
  Lean" (below) to `fig:inference:digits-domain` in
  `pldi27-fpy/sections/04-inference.tex`, and drop `c` from its caption.
  Under the constraint-based framing, also retitle it from "Abstract domain
  of digit-bound analysis" to "Constraints of digit-bound analysis".
  Proposed grammar:

  ```latex
  \begin{array}{rcl@{\qquad}l}
  \tau & ::= & n \mid x \mid \tau_1 + \tau_2 \mid -\tau
    \mid \max(\tau_1, \tau_2) \mid \min(\tau_1, \tau_2)
    & \text{terms} \\
  x & ::= & \mathit{msb}(e) \mid \mathit{lsb}(e) \mid \mathit{val}(e) \mid \lambda \mid \mu
    & \text{variables} \\
  \phi & ::= & \tau_1 \leq \tau_2
    & \text{constraints} \\
  d & ::= & \langle [\tau_1, \tau_2], \tau \rangle \mid \langle [\tau_1, \tau_2], \_ \rangle
    & \text{abstract values}
  \end{array}
  ```

  Caption changes:
  - `n ∈ ℤ ∪ {±∞}`;
  - `λ` and `μ` are fresh variables;
  - `τ₁ = τ₂` abbreviates `τ₁ ≤ τ₂` and `τ₂ ≤ τ₁`;
  - drop the sentence about `c`.
- [ ] **§4.3 framing.** Present the analysis as the table above. Say there is
  no fixpoint iteration, and say why that is sound.
- [ ] **Decidability.** Once constraints are syntactic, `prec♮` is a question
  in Presburger arithmetic extended with ±∞.
- [ ] **State the cost.** Loop-carried values keep only format inference's
  bounds.
- [ ] **Related work** (verify each citation before use):
  - constraint-based program analysis as a recognized approach (Nielson,
    Nielson & Hankin, *Principles of Program Analysis*, ch. 3; Møller &
    Schwartzbach, *Static Program Analysis*, Preface);
  - analysis by handing constraints to a solver (Ernst, *Notes on Program
    Analysis*, ch. 1);
  - LP-based amortized resource analysis (Hofmann–Jost, POPL'03), the
    closest analogue: rules generate linear constraints, and a solver picks
    the optimal bound;
  - SMT-based bit-width analysis (Kinsman–Nicolici, TCAD 2010).
- [ ] **Tightness evaluation.** For each rounding site, report the analysis's
  precision bound against the largest precision observed on adversarial
  inputs.

## Implementation (`fpy`)

- [ ] **Tightness measurement.** Extend
  `tests/unit/analysis/digit_bound_oracle.py` to record the largest
  precision observed at each rounding site, beside
  `DigitBoundAnalysis.bounds`.
- [ ] **Zone experiment.** Collect the verdict from
  `docs/todos/digit-bound-no-smt.md`.

## Depends on the experiment

- [ ] **If zones or templates match Z3:** a graph-based solver replaces Z3,
  and the integer encoding lemma is moot.
- [ ] **If they lose precision:** keep Z3. The losing cases (products,
  correlated `max` constraints) become the paper's justification for SMT.

## Lean implementation plan

Implementation plan for the Lean items above.  The design is settled; what
follows is the phase breakdown, one phase per commit.  The paper and `fpy`
items are tracked separately above.

### Working policy

- **Pause after each phase for review.** Do not begin the next phase until the
  current one has been looked at.
- **Do not commit.** The author of the change leaves the working tree dirty;
  commits are made by the repository owner.
- **Build only what the phase touches.** The full build and tests run once,
  at the end, after the last phase.
- **Comments stay succinct**, and notes about *process* -- what was tried, what
  a phase decided, why an ordering was chosen -- belong in this document, not
  in source comments.
- **Every phase keeps `exec_sound`, `run_sound` and `run_precision` proved.**
  No `sorry` survives a phase.

### Context

| Today | Where | Problem for this framing |
|---|---|---|
| A constraint is an arbitrary predicate, `Con.P : Asgn → Prop` | `Defs.lean` | "The constraints are decidable" cannot be stated |
| The bound is a premise, `∀ ι, Sat ι Ψ → m ≤ l + p − 1` | `run_precision`, `precision_of_bound` (`Sound.lean`) | The paper has no named quantity for "what Z3 computes" |
| D-While takes an invariant, checked by `DEnv.Le` on entry and on the back edge | `DExec.whileDo` (`Defs.lean`); `loop_sound` (`Sound.lean`) | It may not accept the implementation's invariant (fresh variables bounded by format inference), because `DEnv.Le` cannot use format inference's facts |
| Constraints range over ℤ ∪ {±∞} (`EInt`) | `Term.eval` (`Defs.lean`) | Z3 sees integers plus guard literals; the translation is unverified |
| Only the program's result is bounded | `run_precision` | The implementation bounds every rounding site |

Five constructions build constraints: `Con.ext`, `Con.lower`, `Con.upper`,
`Con.between` (`Defs.lean`) and `Con.copy` (`Copy.lean`). `bounds` and the
Table 2 lemmas (`Table.lean`) reuse them. The files that mention `Con` are
`Defs.lean`, `Basic.lean`, `Copy.lean`, `Join.lean`, `Table.lean`,
`Sum.lean`, `Sound.lean` and `FpyTest/DigitBound.lean`.

### Settled decisions

- **Framing:** constraint-based, as at the top of this file. No order change
  (`DEnv.Le` stays as it is), no widening, no abstract-interpretation
  vocabulary.
- **The loop rule is primitive, not derived.** It is a new constructor
  proved sound inside `exec_sound`, beside `DExec.whileDo`, which stays.
- **Constraint language:** a constraint is a fresh variable plus a list of
  atoms `t ≤ t'` over the existing `Term` (`const`, `var`, `add`, `neg`,
  `max`, `min`). Equalities are two atoms. This is the Lean counterpart of
  the paper's Figure 9 (`fig:inference:digits-domain`), up to the
  differences under Open items.
- **The query's name:** `precBound` in Lean, `prec♮` in the paper.

### Figure 9 and the Lean

The Lean is the source of truth; the paper's Figure 9
(`fig:inference:digits-domain`) changes to match it. Figure 10's convention,
"a compound endpoint stands for a fresh variable it bounds", already matches
the Lean's `bounds`, so Figure 10 needs no change.

| | Figure 9 today | Lean | Figure 9 after |
|---|---|---|---|
| Constants | integer `n` | `const` over ℤ ∪ {±∞} (D-Const gives `0` the interval `[+∞, −∞]`) | `n ∈ ℤ ∪ {±∞}` |
| Variables | `msb(e)`, `lsb(e)`, `val(e)` | `var` (numbered) | those, plus the fresh `λ`, `μ` that Figure 10 already uses |
| Operations | `τ₁ + τ₂`, `c · τ` | `add`, `neg`, `max`, `min` | `τ₁ + τ₂`, `−τ`, `max(τ₁, τ₂)`, `min(τ₁, τ₂)` |
| Constraints | `τ₁ ≤ τ₂`, `τ₁ = τ₂`, `τ ≤ max(τ₁, …, τₖ)` | atoms `t ≤ t'` | `τ₁ ≤ τ₂`, with `τ₁ = τ₂` as shorthand for two |
| Abstract values | `⟨[τ₁, τ₂], τ⟩`, `⟨[τ₁, τ₂], _⟩` | `DVal.num l m (τ : Option Term)` | unchanged |

On the Lean side, Phase 1 closes the remaining distance with names, not new
syntax: docstrings on `Term` and `Con` cite Figure 9, and the README pairs
them.

### Phases

#### Phase 1 -- Syntactic constraints (Figure 9)

- **Changes:**
  - `Defs.lean`: `Con` gets `atoms : List (Term × Term)`, with `P` defined by
    evaluating the atoms. Each atom's terms must be `Below (head + 1)`, which
    makes `dep` a theorem. `sat` stays a field (see Open items).
  - Rewrite `Con.ext`, `Con.lower`, `Con.upper` and `Con.between` as atom
    lists.
  - `Copy.lean`: rewrite `Con.copy` as renaming each atom with the existing
    `Term.rename` and `Term.eval_rename`.
  - Fix up proofs in `Basic.lean`, `Join.lean`, `Table.lean`, `Sum.lean`,
    `Sound.lean` and `FpyTest/DigitBound.lean`. Most should go through
    unchanged, because they use `Con.P` through `Sat`.
  - Docstrings on `Term` and `Con` cite Figure 9. Add a README row in the
    §4.3 table pairing Figure 9 with `Term` and `Con`.
- **Why first:** every later phase writes or reads constraints, and the
  integer encoding (Phase 4) needs the syntax. It touches every file but
  changes no theorem statements; bundling it with a new rule would hide
  regressions.
- **Tests:** the existing examples in `FpyTest/DigitBound.lean` must build
  unchanged.

      lake build Fpy FpyTest.DigitBound

#### Phase 2 -- The query as a definition

- **Changes:**
  - In `Sound.lean`, define
    `precBound (Ψ : List Con) (l m : Term) : EInt` as the supremum of
    `m.eval ι − l.eval ι + 1` over `ι` with `Sat ι Ψ`.
  - Add `precision_of_precBound`: if `precBound Ψ l m ≤ p`, the conclusion of
    `precision_of_bound` holds.
  - Restate `run_precision` with `precBound`. Keep the old premise form as a
    corollary, if anything uses it.
  - Add a README row in the §4.3 table.
- **Why separate:** small, and gives the paper its named quantity.
- **Tests:** add an example to `FpyTest/DigitBound.lean` computing
  `precBound` for a two-constraint system.

      lake build Fpy.DigitBound.Sound FpyTest.DigitBound

#### Phase 3 -- A loop rule matching the implementation

- **Changes:**
  - `Fpy/Semantics.lean`: add `Stmt.assigned` (the variables a statement
    may assign). Prove a frame lemma: `Exec` leaves every other variable
    unchanged.
  - `Defs.lean`: add `Covers`. For any store satisfying format inference's
    invariant `Γᵢ`, it requires that some re-choice of the fresh variables
    `[n₀, n₁)` satisfies `Ψᵢ` and makes `Δᵢ` describe the assigned variables.
    Unassigned variables keep `Δ`'s description.
  - `Defs.lean`: add the constructor `DExec.whileFmt`. Its premises are:
    - `Covers`;
    - `Fresh n₀ n₁ Ψᵢ`;
    - A-While's premises for `Γᵢ`;
    - the body's derivation from `Δᵢ`.

    It has **no back-edge `DEnv.Le` premise**.
  - `Sound.lean`: a `loop_sound` variant for `whileFmt`. At each iteration it
    rebuilds the state from `Γᵢ` (format inference's soundness), the frame
    lemma and `Covers`, instead of carrying it along the back edge. Add the
    `whileFmt` case of `exec_sound`.
  - `Join.lean` (or a new `Loop.lean`): `covers_fmt`, building `Covers` from
    digit bounds of `Γᵢ`'s formats as D-Fmt does (`InRange`, `bounds`).
  - Update the README, and the "Rules only" decision in
    `docs/agents/FPY_PLAN.md`.
- **Why separate:** the only new rule, and the only change to
  `exec_sound`'s case analysis. It builds on Phase 1 so its constraints are
  written once, in the new form.
- **Tests:** add an example to `FpyTest/DigitBound.lean` deriving
  `whileFmt` for a one-variable loop, as a check that the premises can be
  met.

      lake build Fpy.Semantics Fpy.DigitBound.Sound FpyTest.DigitBound

#### Phase 4 -- Integer encoding

- **Changes:**
  - New `Fpy/DigitBound/Encode.lean`. Encode an assignment over
    ℤ ∪ {±∞} as an integer assignment plus two flags per variable ("not
    `+∞`", "not `−∞`"). Encode each atom as a guarded integer constraint.
  - Prove that `Sat ι Ψ` holds exactly when the encoded constraints have a
    model, and that `precBound` is preserved under the queried variables'
    flags.
  - Record in this document how the encoding corresponds to
    `DigitBoundStore.high` and `DigitBoundStore.not_neg_inf`.
- **Why separate:** needs Phase 1's syntax, and touches nothing else.
- **Tests:** examples in `FpyTest/DigitBound.lean` encoding a constraint with
  an infinite endpoint.

      lake build Fpy.DigitBound.Encode FpyTest.DigitBound

#### Phase 5 -- Every rounding, not only the result

- **Changes:**
  - `Fpy/Semantics.lean`: a semantics that records each evaluated
    subexpression and its value (see Open items for the shape). Prove it
    agrees with `Eval`/`Exec`.
  - `Sound.lean`: a corollary of `eval_sound`. For every recorded evaluation
    of a rounding `e` whose derivation gives `⟨[l, m], τ⟩`, the value has at
    most `precBound` digits.
  - Add a README row.
- **Why separate:** largest semantic change, and independent of Phases 3–4.
  It goes last, so it does not block the loop rule.
- **Tests:** an example in `FpyTest/DigitBound.lean` bounding an
  intermediate rounding in a two-statement program.

      lake build Fpy.Semantics Fpy.DigitBound.Sound FpyTest.DigitBound

#### After the last phase

    lake build
    lake test
    lake build FpyTest

These are the same as CI (`.github/workflows/ci.yml`).

### Open items

#### Does the paper need `c · τ` with `c ≠ −1`?

The Lean has only `neg`, and no Lean rule scales by any other constant. The
implementation does scale terms (index terms `a + s · k`).
**Provisional:** Figure 9 drops `c · τ` for `−τ`, as decided under "Figure 9
and the Lean" below.  **Reopen** if the paper's rules need another `c`; then
`Term` gains `smul`.

#### Is `sat` a field or derived from the atoms?

`Con.sat` says some value of the fresh variable satisfies the constraint
whatever the other variables are.
- **Derived:** state it as a syntactic condition, e.g. the fresh variable
  appears alone on one side of each atom. That is cleaner, but it may not
  cover `Con.ext`'s two-sided bounds or copies.
- **Field:** each construction proves it once.

**Provisional:** a field.  **Reopen** if the paper wants "every generated
constraint is satisfiable" as a syntactic fact.

#### What does `Covers` give values that are not numbers?

Format inference's values (`AVal`) can be lists, records, contexts or `top`.
`DVal` has no top element, so a loop-carried `top` value cannot be covered.
**Provisional:**
- cover numbers with a fresh interval;
- cover lists of numbers with a fresh element interval;
- cover records field by field;
- leave `whileFmt` inapplicable when any assigned variable is `top`, and use
  D-While there.

**Reopen** if the implementation relies on loops with such variables; then
add a top element to `DVal`.

#### Does `Stmt.assigned` need calls?

A callee runs on its own store, so a call cannot assign the caller's
variables. If the semantics shares stores in some case, the frame lemma
needs a premise.
**Provisional:** syntactic assignments only.  **Reopen** if the frame lemma
fails.

#### Which encoding: a clean one, or exactly the implementation's?

`store.py` guards bounds per direction, with literals per variable and per
coefficient sign. Mirroring it exactly ties the proof to the
implementation's details. A clean encoding is easier to prove, with the
correspondence argued in prose.
**Provisional:** clean encoding plus a written correspondence.  **Reopen** if
a reviewer asks for the implementation's encoding itself.

#### How should Phase 5 record evaluations?

- A semantics that records each evaluation is explicit, and agreement
  follows from determinism (`Eval.det`).
- An "occurs in this run" relation over subderivations avoids a new
  semantics, but is harder to state for loops, where one expression is
  evaluated many times.

**Provisional:** the recording semantics.

#### Is a `for` rule needed?

The implementation's `for` loops use "one generic iteration plus a copy of
the previous one", which no Lean rule covers, and `Stmt` has no `for`.
**Provisional:** no phase. The paper limits the loop claim to `while`.
**Reopen** if the paper's examples depend on `for`.
