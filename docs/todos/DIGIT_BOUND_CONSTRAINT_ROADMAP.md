# Roadmap: digit-bound analysis as a constraint-based analysis

The active roadmap. `DIGIT_BOUND_ROADMAP.md` (abstract interpretation) and
`DIGIT_BOUND_SYMBOLIC_ROADMAP.md` (symbolic abstraction) record the framings
not pursued.

## The change

A reviewer criticized §4.3: the digit-bound analysis generates constraints and
hands them to Z3, instead of computing a sound abstract value at each program
point by iteration.

The paper answers by presenting the analysis as what it is: a constraint-based
analysis layered on format inference, not an abstract interpretation.
- **Format inference is the abstract interpretation:** one format per
  variable, with a fixpoint at loops.
- **Digit-bound analysis generates constraints.** Its rules generate
  constraints over integer variables for digit positions and integer values.
- **Soundness:** the digit positions of every execution satisfy the
  constraints (Theorem 4.2).
- **The query:** precision is bounded by maximizing `msb − lsb + 1` over all
  solutions.
- **Loops:** no fixpoint. A loop-carried value takes fresh variables bounded
  by format inference's loop invariant, so the fixpoint lives in format
  inference.

The Lean now backs this. The README's §4.3 table lists each name:
- **Syntactic constraints:** `Term` (with `smul`), `Atom` (`t ≤ t'`) and
  `Con`.
- **The query:** `precBound`, and `precBoundFin`, the implementation's query
  over finite digits.
- **The implementation's loop rule:** D-While (`DExec.whileDo`, `Covers`),
  which has no back-edge premise.
- **The integer encoding Z3 sees:** `Encode.lean`.

No whole-run "every rounding site" theorem is needed: the paper claims
precision per expression under Theorem 4.2's hypotheses.

The solver experiment (`fpy/docs/todos/digit-bound-no-smt.md`) found that the
constraints **do not need SMT** on the test corpus:
- difference bounds with `max`/`min` hyperedges, over variables and
  linear-form nodes, give Z3's answer on all 173,800 queries;
- every test is unchanged;
- it takes 50 s of solver time to Z3's 188 s.

Zones alone, without the linear-form nodes, lose precision only through
products.

## Writing changes

All edits are to `pldi27-fpy`, recorded here and not made in the paper. Line
references are to `sections/04-inference.tex` as of this writing.

- [ ] **Decide which solver the paper describes.** This is a decision for the
  author before "Solving constraints" is rewritten:
  - **Keep Z3:** say SMT is convenient but not essential, and cite the
    experiment.
  - **Switch the implementation to the difference-bound solver:** describe it
    in "Solving constraints", and drop SMT from the story.
- [ ] **Introduction (`01-intro.tex`).** In the overview paragraph and the
  contributions list, call it "a novel constraint-based digit-bound
  analysis". Keep "formulated as an abstract interpretation" for format
  inference only, so the contrast is deliberate.
- [ ] **§4 opening.** After "formulates format inference as an abstract
  interpretation", introduce §4.3 as "a constraint-based analysis that
  refines it".
- [ ] **§4.3 framing paragraph.** Insert after the paragraph ending "`k + 2`
  significant digits" (the worked `msb`/`lsb` example), before the reference
  to Figure 9:

  > Unlike format inference, digit-bound analysis is not an abstract
  > interpretation. The quantity it bounds, `msb(e) − lsb(e) + 1`, depends
  > on relations between digit positions and run-time values such as
  > `emax`, which no per-variable domain expresses. Rather than maintain a
  > relational state at each program point, the analysis is
  > constraint-based. Its rules generate constraints over integer variables
  > that the digit positions of every execution satisfy, and a solver
  > bounds each expression's precision over all their solutions. Loops need
  > no fixpoint iteration: a loop-carried value takes fresh variables
  > bounded by the loop invariant that format inference computes, so
  > constraints generated in one pass hold in every iteration.

- [ ] **Remove abstract-interpretation vocabulary from §4.3.**
  - "summarizes the abstract domain" → "summarizes the constraint language".
  - "has an abstract value ⟨[lsb(e), msb(e)], τ⟩" → "has a *digit bound*
    ⟨[lsb(e), msb(e)], τ⟩". Use "digit bound" for `d` throughout §4.3,
    Figure 10's caption and prose, and the appendix.
  - "An element of the abstract domain is a pair (Δ, Ψ)" → "The analysis
    maintains an environment Δ, mapping each variable to a digit bound
    whose endpoints and symbolic value are terms, and generates a set of
    constraints Ψ on the variables in those terms." Keep the next sentence
    ("describes a store σ if …") as is.
  - "the join of the elements' abstract values" → "a single digit bound that
    each element satisfies under its own assignment". This also corrects
    the text: the Lean has no join here (`DescribesAll`).
- [ ] **Figure 9 matches the Lean** (`fig:inference:digits-domain`). Retitle
  it from "Abstract domain of digit-bound analysis" to "Constraint language
  of digit-bound analysis".

  | | Figure 9 today | Figure 9 after (the Lean) |
  |---|---|---|
  | Constants | integer `n` | `n ∈ ℤ ∪ {±∞}` |
  | Variables | `msb(e)`, `lsb(e)`, `val(e)` | those, plus the fresh `λ`, `μ` that Figure 10 already uses |
  | Operations | `τ₁ + τ₂`, `c · τ` | `τ₁ + τ₂`, `−τ`, `c · τ`, `max(τ₁, τ₂)`, `min(τ₁, τ₂)` |
  | Constraints | `τ₁ ≤ τ₂`, `τ₁ = τ₂`, `τ ≤ max(τ₁, …, τₖ)` | `τ₁ ≤ τ₂`, with `τ₁ = τ₂` as shorthand for two |

  ```latex
  \begin{array}{rcl@{\qquad}l}
  \tau & ::= & n \mid x \mid \tau_1 + \tau_2 \mid -\tau \mid c \cdot \tau
    \mid \max(\tau_1, \tau_2) \mid \min(\tau_1, \tau_2)
    & \text{terms} \\
  x & ::= & \mathit{msb}(e) \mid \mathit{lsb}(e) \mid \mathit{val}(e) \mid \lambda \mid \mu
    & \text{variables} \\
  \phi & ::= & \tau_1 \leq \tau_2
    & \text{constraints} \\
  d & ::= & \langle [\tau_1, \tau_2], \tau \rangle \mid \langle [\tau_1, \tau_2], \_ \rangle
    & \text{digit bounds}
  \end{array}
  ```

  Caption changes:
  - `n ∈ ℤ ∪ {±∞}`;
  - `λ` and `μ` are fresh variables;
  - `c ∈ ℤ`, with `0 · ±∞ = 0`;
  - `τ₁ = τ₂` abbreviates `τ₁ ≤ τ₂` and `τ₂ ≤ τ₁`.
- [ ] **Rules prose.** "gives `e` the abstract value `d`" → "gives `e` the
  digit bound `d`, generating constraints". Keep Figure 10 itself: its
  convention ("a compound endpoint stands for a fresh variable it bounds")
  already matches the Lean's `bounds`.
- [ ] **New "Loops" paragraph** before "Soundness":
  - state D-While-Fmt: fresh variables bounded by format inference's
    invariant, and the body analyzed once, with no back-edge check;
  - name the cost: a loop-carried value keeps only its format's bounds;
  - replace the appendix's D-While (`A-appendix.tex`) with D-While-Fmt
    (`DExec.whileDo`).
- [ ] **Soundness paragraph.**
  - Add: "Theorem 4.2 holds for any derivation; it needs no fixpoint
    argument, because every constraint holds of every execution."
  - Replace "Each iteration of a loop chooses its own assignment" with a
    pointer to the Loops paragraph.
  - Optional: write `⟦d⟧_ι` instead of `γ_ι(d)`, so the notation does not
    invite comparison with format inference's `γ`.
- [ ] **"Solving constraints" paragraph** (after the solver decision):
  - name the bound `prec♮(e)`;
  - say it is the most precise answer the constraints support, so any
    looseness comes from the rules, not the solver (Reps, Sagiv & Yorsh,
    TR1468 §6);
  - state decidability: the constraints are Presburger arithmetic extended
    with ±∞, and their integer encoding is mechanized;
  - report the experiment's result:
    - difference bounds alone match the solver on 99.93% of queries;
    - adding linear-form nodes matches it on all of them;
    - the only shapes beyond differences are products, whose sums of
      positions must cancel (`msb(ps_i) ≤ msb(x_i) + msb(y_i) + 1` against
      `emax ≥ msb(x_i) + msb(y_i)`, i.e. the running example).
- [ ] **Related work (`08-related.tex`)**, a paragraph on constraint-based
  and solver-based analyses (verify each citation before use):
  - constraint-based analysis as an established approach (Nielson, Nielson
    & Hankin, *Principles of Program Analysis*, ch. 3);
  - LP-based amortized resource analysis (Hofmann–Jost, POPL'03), the
    closest analogue: rules generate linear constraints, and a solver picks
    the optimal bound;
  - SMT-based bit-width analysis (Kinsman–Nicolici, TCAD 2010);
  - relational numerical domains. If the difference-bound solver is adopted,
    cite zones (Miné, PADO 2001) and octagons (Miné, HOSC 2006) as the
    source of its closure. Either way, contrast with polyhedra
    (Cousot–Halbwachs, POPL'78) and max-plus polyhedra (Allamigeon et al.,
    SAS'08): they would need a fixpoint at each program point.
- [ ] **Tightness evaluation (optional).** For each rounding site, report the
  analysis's precision bound against the largest precision observed on
  adversarial inputs.
