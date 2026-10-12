# FPy: open items

What is mechanized, and where, is in the FPy section of the README. This file
keeps only what is open: problems found in the draft, remaining work, and
provisional decisions with their reopen conditions.

## Working policy

- **Pause after each phase for review.**
- **Do not commit.** Commits are made by the repository owner.
- **Run only the tests relevant to the change.** The full suite runs at the
  end (below).
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
| Table 2, `IEEE754(e, n, RTZ)` | `[max(l, m − p + 1), m]` | `m` is only an upper bound on the leading digit. `v = 1` with interval `[0, 10]` and `p = 3` rounds to `1`, whose digit `0 ∉ [8, 10]`. | Same shape as the next row: `[max(l, μ − p + 1), μ]` with fresh `μ ≤ m`. |
| §4.2 soundness side condition | each context "leaves the values of `F_C` unchanged" | A Mpfx `SpecialMap` need not fix the specials in `F`, so an Mpfx context meets this only when it does (e.g. `SpecialMap.exact`). | State that hypothesis on contexts in the paper. |
| Table 1, special values | rows state no specials | Every format contains `0`, `logb 0 = −∞` (IEEE `logB`), and the `logb` row's format has no infinities, so the row is unsound. The other rows say nothing about `∞ × 0`, `∞ − ∞`, `2^(+∞)` or NaN operands. | Each row carries the specials its operator produces (`logbSpecials`, `exp2Specials`, Mpfx's `mulSpecials`, `addSpecials`, `absSpecials`). |
| Table 2, `IEEE754(e, n, RTZ)` and "all others" | `[max(l, μ − p + 1), μ]` (fixed) and `[l, μ]` | Both assume rounding never lowers the least significant digit, which fails when a context overflows, or sends a special, to a finite value. IEEE 754 RTZ overflows to the largest finite value: `v = 2^(emax+1)` has interval `[emax+1, emax+1]` but rounds to a value with digit `emax − p + 1`. `Int(n, rm)` with saturation, and any `OverflowMap` or `SpecialMap` with a finite nonzero image, fail the same way. | Join each row with the digits of the context's overflow and special values, or require those to be non-finite (the digit-bound analogue of the §4.2 hypothesis). |
| §4.3, Fig. 6 loop bound | "an accumulating loop that runs `L` times" adds at most `⌈log₂ L⌉` positions | No rule gives this. D-While's `Δ_I = Δ ⊔ Δ′`, with upper endpoints bounded only from above, yields `msb_I ≤ max(msb₀, msb_I + 1)`, which every large `msb_I` satisfies. D-Sum has the bound, but `sum` and `for` are not core FPy, so Fig. 6's bound on `fused_sum` follows from no rule. | A counted-loop rule, or `sum` as an operator with D-Sum. |
| Fig. 12 `D-Logb` | `val(logb x) = msb(x)` | Sound only if the assignment can make `msb(x)` exact, which fails once a constraint bounds `msb(x)` from below. `logb 0 = −∞` gives a non-finite integer term (`e − k` in `fused_sum`), which Theorem 4.2, stated for finite values, does not cover. | Open; settled with the open item on assignments. |
| §5.2 Overflow, the test | `if \|r\| > b` under `C` | `\|·\|` is a rounded operator, so the test sees `C(\|r\|)`. When `C` overflows to NaN (MX E4M3, the running example) or saturates to `b`, an `r` beyond `b` fails the test and `x = r` leaves `F`. | Compare exactly: `r < −b`, `b < r` (unrounded `<`), or under `R`. |
| §5.2 Overflow, the input | no condition on `t` | For `t = ±∞` the rewrite returns `ovf_C`, but `C(±∞)` is the special map's value, which differs when overflow saturates and infinities are kept. | Require `t` finite. The draft applies Overflow after Special, but the rule should say so. |
| §5.2 Special and Overflow | `copysign(C(∞), t)`, `copysign(ovf_C, r)` | Assumes `C(−∞) = −C(∞)` and symmetric overflow; a context's maps need not be symmetric. | Branch on the sign, with one constant per sign. |
| §5.2 FloatToFixed | any `𝒜(p, exp, ∞)` | At `p = 1`, RTO and RNE read parity off the exponent in `𝒜(1, exp)` but off the significand in `𝒜(∞, n)`, so the two can pick different neighbours. This is argued by hand, not proved. | Require `p ≠ 1`, or a mode without parity. |
| §5.2 Rescale | `C_{𝒜(∞,0,2⁻ⁿb)}` "behaves like `C`" | `2ⁿ × C₀(2⁻ⁿt) = C(t)` needs `C₀`'s special and overflow values to be `C`'s scaled by `2⁻ⁿ`; saturation to `b` must become saturation to `2⁻ⁿb`. | State the scaling (`RoundCtx.Scaled`). |

Theorem 4.2 leaves its per-value assignments, and its statement for
statements and loops, unspecified (provisional decisions, below).

## Remaining work

### Phase 4 - Digit-bound analysis and Theorem 4.2

Deferred until the draft's §4.3 is rewritten; the table's Table 2, loop-bound
and `D-Logb` rows bear on it.

- `Fpy/DigitBound.lean`:
  - terms `τ`, constraints `φ`, `digits(v)`, digit intervals with `∅`, and
    assignments `ι`;
  - the mutual judgment of Fig. 12, with fresh variables made explicit;
  - Table 2 with the fixes above, each row with its soundness lemma.
- `eval_sound` and `exec_sound` in the form fixed by the assignment decision.
- The format-inference constraint import ("each interval lies within the
  inferred format's range") is a premise discharged by Theorem 4.1.

Test: `~/.elan/bin/lake build Fpy.DigitBound FpyTest`.

### Not claimed

The claim is each rewrite on its own. Not mechanized:

- **Composition of rewrites**, e.g. Fig. 9's derivation. Two obstacles:
  - Rescale after FloatToFixed has a site whose context is known only at run
    time, and `Rw` needs it statically;
  - finite `t` after Special would need `refine` to narrow on `isnan` and
    `isinf`, which §4.2 does not list.
- **SplitOp with a bounded intermediate format.** The instances
  (`splitOp_add`, …) need `F₂.b = ⊤`; a bounded `F₂` would need
  `OverflowAgrees` at one input, which Mpfx states only for all inputs.
- **The `p = 1` failure of FloatToFixed**, argued by hand, not proved.

## Provisional decisions

- **Same Lake package**, as a second `lean_lib`. Reopen if FPy needs its own
  Mathlib or toolchain, or should be published apart from Mpfx.
- **Separate `FpyTest` library**, with the CI step `lake build FpyTest`.
- **Abstract `Signature`** through the semantics, format inference and the
  rewrite framework; `fpy` from Table 1 on. Phase 4 takes an interface for
  integer-term transfers, as Table 2 tabulates them. Reopen if that interface
  needs more than Table 2's rows.
- **The draft adopts the fixes above.** If it keeps a rule as printed, the
  mechanization proves a different system.
- **Theorem 4.2's assignments.** One assignment per value of an expression;
  a list's elements share one; at a loop, one per iteration agreeing on `Δ`'s
  variables. Reopen at the first Phase 4 obligation that does not go through.
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
