# FPy: open items

What is mechanized, and where, is in the FPy section of the README. This file
keeps only what is open: problems found in the draft, what is not claimed,
and provisional decisions with their reopen conditions.

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
| Fig. 5 `rnd♯`, with `ctx(e) = ?` | `rnd♯_?(F) = F` if `F ⊆ F_? = R*` | Always keeps the exact bound under an unknown context, which may round. `t = round(xi)` in `fused_sum` would keep the inputs' format. Fig. 6 shows `R*` there, so the implementation is right and the rule is wrong. | `rnd♯_?(F) = R*` (`Analysis.rnd`; witness `FpyTest.draft_rnd_unknown_unsound`). The side condition "`C` leaves `F_C` unchanged" is false for `?`. |
| Fig. 5/11 `A-Context`, `A-Ctx` | `ctx(e)` "known statically"; `ctx e : •` | Fig. 6 line 5 needs "the format of `out`", but `out` is a parameter with abstract value `•`, so no static `ctx(out)` exists. | Abstract values carry a known context `⟨C⟩`. `R : ⟨R⟩`; `ctx e : ⟨ctx fs⟩` when the record is known. `A-Context` reads the context off `e`'s abstract value (`AEval.ctx`, `AExec.withCtx`, `AExec.withUnknown`). Call-site specialization (A-App) then carries `out`. |
| §4.2 soundness side condition | each context "leaves the values of `F_C` unchanged" | An Mpfx `SpecialMap` need not fix the specials in `F`, so an Mpfx context meets this only when it does (e.g. `SpecialMap.exact`). | State that hypothesis on contexts in the paper. |
| Table 1, special values | rows state no specials | Every format contains `0`, `logb 0 = −∞` (IEEE `logB`), and the `logb` row's format has no infinities, so the row is unsound. The other rows say nothing about `∞ × 0`, `∞ − ∞`, `2^(+∞)` or NaN operands. | Each row carries the specials its operator produces (`logbSpecials`, `exp2Specials`, Mpfx's `mulSpecials`, `addSpecials`, `absSpecials`). |
| Table 2, `IEEE754(es, nb, RTZ)`, `IEEE754(es, nb, rm)` and "all others" | `[max(l, m − p + 1), m]`, `[max(l, μ − p + 1), μ]` and `[l, μ]` | Each assumes rounding never lowers the least significant digit, which fails when a context overflows, or sends a special, to a finite value. IEEE 754 RTZ overflows to the largest finite value: `v = 2^(emax+1)` has interval `[emax+1, emax+1]` but rounds to a value with digits `emax − p + 1` to `emax`. RTP and RTN do the same on their saturating side, as does `Int(n, rm)` with saturation and any `OverflowMap` or `SpecialMap` with a finite nonzero image. | Join each row with the digits of the context's overflow and special values (`ImagesIn`, `rndOK_of`). An overflow to `±∞` then leaves `μ` unbounded, since `∞` has digits `[+∞, +∞]`; `λ ≥ μ − p + 1` still bounds the precision. |
| Table 2, `IEEE754(es, nb, rm)` | `μ ≤ m + 1` | Below the smallest subnormal `2^q`, RTP, RAZ and RTO round up to `2^q`: `2⁻¹¹` (`m = −11`) rounds to `2⁻⁹` in MX E4M3 (`FpyTest.draft_ieee_rm_bound`). | `μ ≤ max(m + 1, q)`, as the `Fixed(τ, rm)` row (`rndOK_prec`). |
| §4.3, Fig. 6 loop bound | "an accumulating loop that runs `L` times" adds at most `⌈log₂ L⌉` positions | No rule gives this. D-While's `Δ_I = Δ ⊔ Δ′`, with upper endpoints bounded only from above, yields `msb_I ≤ max(msb₀, msb_I + 1)`, which every large `msb_I` satisfies. D-Sum has the bound, but `sum` and `for` are not core FPy, so Fig. 6's bound on `fused_sum` follows from no rule. | A counted-loop rule, or `sum` as an operator with D-Sum. |
| Fig. 12 `D-Logb`, at zero | `logb(e) : ⟨[0, μ], m⟩` | Every interval concretizes `0` under every assignment, but `logb 0 = −∞`, so the symbolic value `m` is unconstrained by a zero `e`. `e = max(logb(x), 5)` with `σ(x) = 0` and `ι(msb(x)) = 100`: `ι` satisfies `val(e) ≥ msb(x)`, `val(e) ≥ 5`, yet `e` evaluates to `5`, and no `ι'` agreeing with `ι` on `msb(x)` (a variable of `Δ`) has `ι'(val(e)) = 5`. `max_e` in `fdpa` applies `logb` to inputs that may be `0`. | Extended endpoints: `0` has `[+∞, −∞]`, so `logb 0 = −∞ = msb(0)` (`lsbOf`, `msbOf`). |
| Theorem 4.2, values with infinitely many digits | `γ_ι([l, m])` requires `min digits(v) = ι(l)` | `0.1`, or `√2` and `x / 3` under `R`, have no least significant digit, so no interval concretizes them; yet D-Const gives `0.1` the value `⟨[λ, μ], _⟩` and Table 2's "all others" covers `√` and `÷`. | Extended endpoints: such a value has lsb `−∞`. |
| Fig. 12 `D-While` | `Δ_I = Δ ⊔ Δ′` | The invariant's variables depend on the body's outputs, which depend on the invariant, so the constraints are cyclic and the proof cannot re-choose variables in order. For a variable the body leaves unchanged, `μ_I ≤ max(m, μ_I)` bounds nothing. | An invariant with `Δ ⊑ Δ_I` and `Δ′ ⊑ Δ_I`, as A-While; the join is an instance. |
| Fig. 12 `D-Index` | `e₁[e₂] : d` | Each list element is described under its own assignment of `d`'s variables, but once the list is in a variable those are variables of `Δ`, which the theorem keeps fixed. `xs = [1, 4]; z = xs[1]` needs `val = 4` while `Δ` fixes it at the value describing another element. | The result is a fresh copy of `d`, with `Ψ`'s constraints on `d`'s variables renamed onto the copy. |
| §4.3, list concretization | `vⱼ ∈ γ_ιⱼ(d)` for some `ιⱼ ⊨ Ψ` agreeing with `ι` outside the variables of `d` | `Ψ` keeps growing, and a later constraint can mention `d`'s variables (`ν ≤ μ + 1` after the list): `ιⱼ` changes `μ` but must keep `ι`'s `ν`, so `ιⱼ ⊨ Ψ` can fail. | `ιⱼ` agrees with `ι` on the variables created before `d`'s, and re-chooses the rest. |
| Fig. 12 `D-Logb`, `D-Max`, `D-Min` | under any context `C` | Each rounds under `C`, which can change an integer result (`Fixed(3, RTZ)` sends `5` to `0`), so the symbolic value no longer matches. | State them under `R`, as `D-Linear`. |
| §5.2 Overflow, the test | `if \|r\| > b` under `C` | `\|·\|` is a rounded operator, so the test sees `C(\|r\|)`. When `C` overflows to NaN (MX E4M3, the running example) or saturates to `b`, an `r` beyond `b` fails the test and `x = r` leaves `F`. | Compare exactly: `r < −b`, `b < r` (unrounded `<`), or under `R`. |
| §5.2 Overflow, the input | no condition on `t` | For `t = ±∞` the rewrite returns `ovf_C`, but `C(±∞)` is the special map's value, which differs when overflow saturates and infinities are kept. | Require `t` finite. The draft applies Overflow after Special, but the rule should say so. |
| §5.2 Special and Overflow | `copysign(C(∞), t)`, `copysign(ovf_C, r)` | Assumes `C(−∞) = −C(∞)` and symmetric overflow; a context's maps need not be symmetric. | Branch on the sign, with one constant per sign. |
| §5.2 FloatToFixed | any `𝒜(p, exp, ∞)` | At `p = 1`, RTO and RNE read parity off the exponent in `𝒜(1, exp)` but off the significand in `𝒜(∞, n)`, so the two can pick different neighbours. This is argued by hand, not proved. | Require `p ≠ 1`, or a mode without parity. |
| §5.2 Rescale | `C_{𝒜(∞,0,2⁻ⁿb)}` "behaves like `C`" | `2ⁿ × C₀(2⁻ⁿt) = C(t)` needs `C₀`'s special and overflow values to be `C`'s scaled by `2⁻ⁿ`; saturation to `b` must become saturation to `2⁻ⁿb`. | State the scaling (`RoundCtx.Scaled`). |

Theorem 4.2 is stated for expressions only; its form for statements and loops
is unspecified (provisional decisions, below).

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
- **D-Index keeps none of a list summary's bounds.** `DVal.Copy` must hold for
  any constraints generated before the derivation, which Theorem 4.2 cannot
  name. Threading the global `Ψ` through the judgment would close this.
- **The paper's concrete setting**: a decoding of `IEEE754`, `Fixed` and `Int`
  records into Mpfx contexts, the second pass refining formats by digit bounds,
  and the worked examples (`mac`, `fdpa`, `fused_sum`).

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
  satisfying them (§4.3 list concretization, above).
- **Rules only, not the implementation's algorithm.** The theorems cover any
  derivation; widening, the set-size cap and Z3 only construct derivations.
  The draft should say "the rules are sound". Reopen if it wants an extracted
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
