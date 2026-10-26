# FPy: open items

What is mechanized, and where, is in the FPy section of the README. This file
keeps only what is open: problems found in the draft, what is not claimed, and
provisional decisions with their reopen conditions.

## Working policy

- **Do not commit.** Commits are made by the repository owner.
- **Run only the tests relevant to the change.** The full suite is below.
- **Comments stay succinct**, and notes about process belong here, not in
  source comments.
- **The Lean is the source of truth.** A bug found in the draft goes into the
  table below, and the Lean states the fixed rule.
- **Mechanize only what the draft states.** Where its rules do not reach,
  record the gap rather than adding rules.

## Problems found in the draft

Each fix is a change to the draft; the Lean states the fixed rule.

| Where | As written | Failure | Fix |
| --- | --- | --- | --- |
| §4.3 `γ`, special values | `γ_ι(⟨[l, m], τ⟩)` by `inf digits(v)` and `sup digits(v)` | These are defined only for finite `v`, yet D-Const gives `±∞` and NaN an interval, and a store may hold them mid-program. Theorem 4.2's "`v` finite" restricts only the final value, so the induction has no description for an infinite or NaN intermediate. | NaN lies in every interval and `±∞` has digits `[+∞, +∞]` (`lsbOf`, `msbOf`, `NumIn`). |
| Table 2, lone endpoints | upper `m` in `Fixed(τ, RTZ)` and `IEEE754(es, nb, RTZ)`; lower `l` in "? and all others" | Under the exact `γ`, a lone endpoint says the result's digit equals the input's. Rounding toward zero can reach `0`, whose `sup digits` is `−∞` (`0.75` under `Fixed(0, RTZ)`), and rounding can carry, raising the least digit (`3` to one digit under RNE is `4`). | A fresh variable bounded by the endpoint: `μ ≤ m`, `λ ≥ l` (`rndOK_*`, `bounds`). |
| Fig. 8/12 `D-Sum` | `sum(e) : ⟨[l, m + ⌈log₂ L⌉], _⟩` for `e : [⟨[l, m], τ⟩]` | `l` and `m` are the list summary's variables, which each element re-chooses; as with D-Index before its fix, the result fixes them to one assignment. Its lone `l` also fails when the sum carries (`1 + 1 = 2`) or cancels to `0`. | Restate with common bounds: if `Ψ` implies `lo ≤ l` and `m ≤ hi`, for terms `lo`, `hi` over variables created before `d`'s, then `sum(e) : ⟨[λ, μ], _⟩` with fresh `λ ≥ lo`, `μ ≤ hi + ⌈log₂ L⌉` (`fused_sum`: `lo = val(emax) − k`, `hi = val(emax) + 1`). A fresh copy of `d`, as in D-Index, does not suffice: one assignment cannot bound elements whose digits differ. The Lean proves it over the analysis as a theorem beside the core rules (`eval_sum_sound`). |

### Fixed in the draft

Found by the mechanization and adopted by the draft:

- Fig. 5: `rnd♯_?(F) = R*` (witness `FpyTest.draft_rnd_unknown_unsound`).
- Abstract values carry known contexts; A-Context reads `κ′` off `e`.
- §4.2: `F_C` is the image of `C`, which fixes it, special values included.
- Table 1: each row carries the special values its operator produces.
- Table 2: rounding rows are joined with the context's finite special and
  overflow values; IEEE `μ ≤ max(m + 1, q)` (witness
  `FpyTest.draft_ieee_rm_bound`).
- §4.3: endpoints range over `ℤ ∪ {±∞}`, so `0` and values with infinitely
  many digits have intervals, and `logb 0 = −∞ = msb(0)`.
- D-While takes an invariant; D-Index returns a fresh copy with its
  constraints; list elements agree with `ι` on the variables created before
  the summary's; D-Logb, D-Max, D-Min are under `R`.
- §5.2: Overflow compares exactly and needs finite `t`; Special and Overflow
  branch on the sign; FloatToFixed needs `p ≠ 1`; Rescale's `C₀` is `C`
  scaled.

## Not claimed

The claim is each rewrite on its own. Not mechanized:

- **Composition of rewrites**, e.g. Fig. 9's derivation. Two obstacles:
  - Rescale after FloatToFixed has a site whose context is known only at run
    time, and `Rw` needs it statically;
  - finite `t` after Special would need `refine` to narrow on `isnan` and
    `isinf`, which §4.2 does not list.
- **SplitOp with a bounded intermediate format.** The instances
  (`splitOp_add`, …) need `F₂.b = ⊤`; a bounded `F₂` would need
  `OverflowAgrees` at one input, which Mpfx states only for all inputs.
- **The paper's concrete setting**: a decoding of `IEEE754`, `Fixed` and `Int`
  records into Mpfx contexts, the second pass refining formats by digit bounds,
  and the worked examples (`mac`, `fdpa`, `fused_sum`).
- **Digit bounds at every rounding of a run.** Theorem 4.2 and the precision
  bound are per expression, under their hypotheses. The second pass needs
  every intermediate rounding bounded; D-If and D-While do not analyze their
  conditions, so a rounding inside one has no bound.

## Provisional decisions

- **Same Lake package**, as a second `lean_lib`. Reopen if FPy needs its own
  Mathlib or toolchain, or should be published apart from Mpfx.
- **Separate `FpyTest` library**, with the CI step `lake build FpyTest`.
- **Abstract `Signature`** through the semantics, format inference and the
  rewrite framework; `fpy` from Table 1 on, and in the digit-bound analysis,
  whose integer rules name FPy's operators.
- **The draft adopts the fixes above.** If it keeps a rule as printed, the
  mechanization proves a different system.
- **Theorem 4.2's assignments.** One assignment per value of an expression,
  and per loop iteration, agreeing on `Δ`'s variables. Descriptions take the
  constraints generated so far; a list's elements each get an assignment
  satisfying them and agreeing below the summary's variables.
- **Rules only, not the implementation's algorithm.** The theorems cover any
  derivation; widening, the set-size cap and Z3 only construct derivations.
  The draft should say "the rules are sound". D-While-Fmt is the exception:
  it is the implementation's loop rule. Reopen if it wants an extracted
  checker.
- **`min`/`max` propagate NaN** (IEEE 754-2019 `minimum`/`maximum`). Reopen if
  a specification needs `minimumNumber`/`maximumNumber`; the fix is a second
  pair of operators.

## Verifying

```sh
~/.elan/bin/lake build              # Mpfx and Fpy; the Mathlib linter set runs here
~/.elan/bin/lake test               # MpfxTest
~/.elan/bin/lake build FpyTest
```

A clean build has no warnings.
