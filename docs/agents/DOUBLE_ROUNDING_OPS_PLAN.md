# Plan — Operation-specific double rounding (Roux 2014) in `𝒜(p, exp, b)`

**Status:** proposal, awaiting review. Do not implement yet.

Paper: Pierre Roux, *Innocuous Double Rounding of Basic Arithmetic
Operations*, JFR 7(1), 2014. Formalized in Flocq; the current source lives in
`flocq-4.2.2/src/Prop/Double_rounding.v` (theorems renamed `round_round_*`).

## 1. What this adds, and how it differs from what we have

The existing development (`DoubleRounding.lean`, Fig. 9) proves double rounding
correct **for every real `x`** — the containment `F₁ ⊆ F₂` (plus mode-specific
side conditions) is enough because the result holds pointwise for arbitrary
inputs. Roux instead proves double rounding innocuous **for the results of
specific operations** (`×`, `+`/`−`, `√`, `÷`) under *weaker* precision
relationships, exploiting that an operation's output is far more structured than
an arbitrary real:

> `∀ x, y ∈ F₁,  ◦₁(◦₂(x ∘ y)) = ◦₁(x ∘ y)`   for `∘ ∈ {×, +, −, ÷}` (and `√`).

Roux's radix-2 FLX bounds (Table I): `×` needs `p₂ ≥ 2p₁`; `+`/`−` need
`p₂ ≥ 2p₁+1`; `√` needs `p₂ ≥ 2p₁+2`; `÷` needs `p₂ ≥ 2p₁`. Underflow (Tables
II/III) adds `exp`/`b` side conditions.

**Radix-2 restriction.** `𝒜(p, exp, b)` is fixed to radix 2. Roux's odd-radix
(Thms 12, 24, 28, 32) and `β ≥ 3`/`β ≥ 4` refinements therefore **do not apply**
and are out of scope. What remains is the "even radix" column of Table I, i.e.
Figueroa's classical bounds. Division for radix 2 falls in the even-radix case,
so it *is* in scope (only odd-radix division needs the RNA restriction).

## 2. The two proof techniques in the paper

Everything reduces to one of two mechanisms:

### (A) Exact intermediate ("`round_generic`")
If the exact result `x ∘ y` is **representable in `F₂`**, then `◦₂(x ∘ y) =
x ∘ y`, so the outer `◦₁` sees the same input in both terms and the equation is
immediate. This is *all* that multiplication needs (Flocq
`round_round_mult` = `round_round_mult_aux` + `round_generic`), and it works for
**any** rounding modes, not just round-to-nearest.

We already have the "representable" half:
`Format.mul_subset : F₁.toSet * F₂.toSet ⊆ (opMul F₁ F₂).toSet` and
`Format.add_subset` (`FormatInference.lean`). We are missing the
"`round_generic`" half — a lemma that rounding fixes representable values.

### (B) Midpoint reasoning (Roux Lemma 16)
When the exact result is **not** representable in `F₂` (the interesting case for
`+`, `√`, `÷`), the result still holds because the value sits far enough from an
`F₁`-midpoint that both roundings land on the same `F₁`-value. The engine is:

`round_round_lt_mid_further_place` (Lemma 16): for `0 < x`, if `ϕ₂(mag x) ≤
ϕ₁(mag x) − 1`, `ϕ₁(mag x) ≤ mag x`, and `x < midp_{F₁}(x) − ½·ulp_{F₂}(x)`,
then `◦₁(◦₂(x)) = ◦₁(x)` for any two round-to-nearest modes.

This lemma (and its helper `…_place'`, plus `midp`, `ulp`, `mag`) has **no
counterpart in the current development**. `Grid.lean`'s midpoint machinery
(`midpoint_mem_extend_one_of_F_adjacent`, `F_adjacent_step_form`) is built for
the RTO/parity argument (Lemma 5.3) and proves *membership* of midpoints, not
the RTN distance inequality Lemma 16 needs. Building Lemma 16 is the dominant
cost of anything beyond multiplication.

## 3. Feasibility by operation

| Op | Bound (radix 2) | Technique | mpfx status | Effort |
|---|---|---|---|---|
| `×` | `p₂ ≥ 2p₁` | (A) exact | `mul_subset` ✔ + `eq_of_mem` (new, small) | **Low** |
| `+`/`−` | `p₂ ≥ 2p₁+1` | (A) for large `y`, (B) for tiny `y` | `add_subset` ✔; needs Lemma 16 | **High** |
| `√` | `p₂ ≥ 2p₁+2` | (B) + algebraic "no midpoint" | needs Lemma 16 + `Real.sqrt` algebra | **High** |
| `÷` | `p₂ ≥ 2p₁` | (B) + midpoint-representable (even radix) | needs Lemma 16 + rational algebra | **High** |

### 3.1 Multiplication — clean and tight
The full Flocq `round_round_mult` transcribes directly:

- Product membership: `x, y ∈ F₁ ⟹ x·y ∈ opMul F₁ F₁ = 𝒜(2p₁, 2·exp₁, b₁²)`
  via `mul_subset`. If `opMul F₁ F₁ ⊆ F₂`, then `x·y ∈ F₂`.
- `eq_of_mem` (new): the `F₂`-rounding of a member is that member, so the
  intermediate `z = x·y`.
- Substitute; the chained rounding is literally the direct rounding.

Works for **all** modes (matches Roux's "`◦₁`, `◦₂` any roundings"). The
`exp`/`b` conjuncts of `opMul F₁ F₁ ⊆ F₂` (namely `exp₂ ≤ 2·exp₁`,
`b₁² ≤ b₂`) are exactly Roux's FLT/FTZ underflow side conditions — so the single
theorem subsumes his `_FLX`/`_FLT`/`_FTZ` corollaries.

### 3.2 Addition — two sub-options
- **Tight (`p₂ ≥ 2p₁+1`, faithful to the paper):** requires Lemma 16 for the
  tiny-`y` case (`ln y < ϕ₁(ln x) − 2`) plus Roux Lemma 22 (the exact-intermediate
  large-`y` case). Round-to-nearest only. **High effort** (Lemma 16 is the bulk).
- **Exact-intermediate only (via `add_subset`, sound but NOT tight):** if
  `opAdd F₁ F₁ ⊆ F₂`, then `x+y ∈ F₂` and the equation is immediate for all
  modes. But `opAdd`'s precision is `⌈log₂(⌊2b₁/2^exp₁⌋+1)⌉` — the format's
  **dynamic range**, which for wide-range formats (e.g. binary32: ~277) is far
  larger than `2p₁+1` (49). This reproduces the paper's *conclusion* only under
  a much stronger hypothesis; it is essentially "the sum happens to fit," not
  Roux's theorem. Low effort, but arguably not worth stating on its own.

### 3.3 Square root & division — hardest
Both are genuine (B) arguments and their exact results are **not dyadic**
(`√` of a dyadic, `x/y`), so (A) cannot apply and the spec must round a general
real (`RoundsFinite F rm (Real.sqrt x) z`, `… (x/y) z`) — the `Rounds` spec
already supports arbitrary real inputs, so *stating* them is fine; only the
proofs are expensive. Both need Lemma 16 plus an operation-specific "the value
is never within `½·ulp₂` of an `F₁`-midpoint" argument (`√`: a quadratic
divisibility argument; `÷`: even-radix midpoint representability). **High
effort, on top of Lemma 16.**

## 4. Concrete work items

**Phase 0 — shared primitive (needed by everything).**
- `RoundsFinite.eq_of_mem {F rm d} (hd : d ∈ F) (h : RoundsFinite F rm (d:ℝ) y) : y = d`
  — "rounding fixes representable values", the spec-relational form of Flocq
  `round_generic`. One case per mode (directed: antisymmetry; RTZ/RAZ: `|y|=|d|`
  + same sign ⟹ `y=d`; RTO: reuse `toOdd_unique_of_mem`; nearest: `d` is its own
  faithful rounding so `|d−y| ≤ |d−d| = 0`). Small helpers:
  `isFaithfulRound_self` and a real lemma `|a|=|b| ∧ a·b ≥ 0 ⟹ a = b`.
  Home: `Rounding.lean`, beside `toOdd_unique_of_mem`.

**Phase 1 — multiplication (recommended first deliverable).**
- New file `Mpfx/DoubleRoundingOps.lean`.
- `rndExact` — the general (A) collapse: `v ∈ F₂` ⟹ chained = direct, any modes.
- `rndMul` — corollary via `mul_subset`, hypothesis `opMul F₁ F₁ ⊆ F₂`.
- Corollary(ies) deriving the hypothesis from explicit `𝒜`-parameter
  inequalities (`2·p₁ ≤ p₂`, `exp₂ ≤ 2·exp₁`, `b₁² ≤ b₂`) via `containsPrec`
  — the analog of Roux's `_FLX`/`_FLT`/`_FTZ`.
- (Optional) `rndAdd` exact-intermediate corollary via `add_subset`, clearly
  documented as the non-tight containment version (§3.2).

**Phase 2 — Lemma 16 apparatus (gate for everything else).**
- Decide the mpfx spelling of `midp`, `ulp`, `mag` (we have `numDigits`,
  `canonicalExp`, `Grid` step forms — likely reusable) and prove Lemma 16 for
  the `RoundsFinite (.nearest _)` spec. Large; scope/verify before committing to
  Phase 3.

**Phase 3 — addition (tight), square root, division.** Each builds on Phase 2.

## 5. Decisions (locked in 2026-07-14)

1. **Scope.** Multiplication first — Phases 0–1 only. Stop and review before any
   Lemma-16 work (Phase 2). Addition/√/÷ are deferred pending that review.
   **Relational `RoundsFinite` layer only** — no overflow-aware `Rounds`-level
   companion (`roundsMul`) for now.
   **README deferred (FLAG):** the new theorems are intentionally *not* yet wired
   into `README.md`'s theorem tables; do that once the Roux effort is further
   along (also add a `TODO.md` entry then).
2. **Statement form.** **Relational over `RoundsFinite`**, matching the existing
   `rndRTZ_RTZ` et al.: take the `hz` (round `x∘y` in `F₂` to `z`) and `hw`
   (round `z` in `F₁` to `w`) chain hypotheses and conclude
   `RoundsFinite F₁ rm₁ (x∘y) w`. A `rnd`-function-equation corollary (via
   `rnd_iff_rounds`) may be added later but is not the primary form.
3. **Hypothesis form.** Project-standard containment `⊆`, applied to the inferred
   product format: **`Format.opMul F₁.toFormat F₁.toFormat ⊆ F₂.toFormat`**
   (identical `HasSubset Format` relation as `rndRTZ_RTZ`; `opMul F₁ F₁`
   evaluates to `𝒜(2p₁, 2·exp₁, b₁²)`, so this reads `𝒜(2p₁,2·exp₁,b₁²) ⊆ F₂` =
   Roux's `p₂ ≥ 2p₁` + underflow conjuncts). Plus a convenience corollary
   deriving that `⊆` from explicit `2·p₁ ≤ p₂ ∧ exp₂ ≤ 2·exp₁ ∧ b₁² ≤ b₂` via
   `containsPrec` — the analog of Roux's `_FLX`/`_FLT`/`_FTZ`.
4. **Modes.** `rndMul` stated for arbitrary `rm₁ rm₂` (as the paper does) — free,
   since `eq_of_mem` covers all modes.
5. **File/naming.** `Mpfx/DoubleRoundingOps.lean`; theorems `rndExact`, `rndMul`
   (+ the explicit-parameter corollary). `eq_of_mem` goes in `Rounding.lean`.

### Deliverable shape (Phases 0–1)

```lean
-- Rounding.lean
theorem RoundsFinite.eq_of_mem {F rm d}
    (hd : d ∈ F) (h : RoundsFinite F rm (d : ℝ) y) : y = d

-- Mpfx/DoubleRoundingOps.lean
theorem rndExact {F₁ F₂ rm₁ rm₂} {v : Dyadic} (hv : v ∈ F₂)
    (hz : RoundsFinite F₂ rm₂ (v : ℝ) z) (hw : RoundsFinite F₁ rm₁ (z : ℝ) w) :
    RoundsFinite F₁ rm₁ (v : ℝ) w

theorem rndMul {F₁ F₂ rm₁ rm₂} {x y : Dyadic}
    (hsub : Format.opMul F₁.toFormat F₁.toFormat ⊆ F₂.toFormat)
    (hx : x ∈ F₁) (hy : y ∈ F₁)
    (hz : RoundsFinite F₂ rm₂ ((x * y : Dyadic) : ℝ) z)
    (hw : RoundsFinite F₁ rm₁ (z : ℝ) w) :
    RoundsFinite F₁ rm₁ ((x * y : Dyadic) : ℝ) w

-- explicit-parameter corollary: 2·p₁ ≤ p₂ ∧ exp₂ ≤ 2·exp₁ ∧ b₁² ≤ b₂ → rndMul hyp
```

## 6. Phase 2 scoping (Lemma 16) — gate for addition/√/÷

**Status:** scoped, *not* started. This is the review gate from §5.1.

**Goal.** Roux Lemma 16 `round_round_lt_mid_further_place` in the mpfx
`RoundsFinite (.nearest _)` world — the sole engine behind tight addition,
√, and ÷.

**What exists / what's missing.**
- Have: `Dyadic.midpoint` (of two dyadics), `FiniteFormat.canonicalExp`
  (= Flocq `cexp` = `ϕ(mag x)`), `Int.log 2` (= `mag` up to `+1`), and a
  large RN/faithful toolbox in `DoubleRounding.lean` (`nearest_components`,
  `abs_le_mid_of_nearest_inbound`, `faithful_below/above_unique`,
  `nearest_close_upgrade`, `F_adjacent_of_RN_round_pair`, Grid F-adjacency).
- Missing: `ulp F x := (2:ℝ) ^ F.canonicalExp x`; `midp F x` (the midpoint
  *bracketing a real* `x`, = round-down value `+ ulp/2`); a `mag` wrapper; and
  the key step **"`ξ` strictly below `midp F x` ⟹ nearest rounds `ξ` down"**.
- **`ulp` is not a new notion.** Grid.lean's grid step
  `k = max(exp, ⌊log₂ y⌋ − p + 1)` *is* `canonicalExp`, and `exists_grid_rep` /
  `F_adjacent_step_form` already prove F-adjacent values differ by exactly
  `2^k`. So `ulp F x := (2:ℝ)^(F.canonicalExp x)` coincides with the step the
  whole Grid theory rests on — the adjacency/step lemmas are reusable directly,
  and `quantumAtLeast` supplies the "multiple of `2^k`" facts. This is the main
  de-risking finding for Phase 2.

**Proposed statement (relational, matching the project).**
```lean
theorem rnd_lt_mid {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {x : ℝ}
    (hx : 0 < x)
    (h21 : F₂.canonicalExp x < F₁.canonicalExp x)
    (hle : F₁.canonicalExp x ≤ Int.log 2 x + 1)          -- ϕ₁(mag x) ≤ mag x
    (hmid : x < midp F₁ x - ulp F₂ x / 2)
    {z w : Dyadic}
    (hz : RoundsFinite F₂ (.nearest tb₂) x z)
    (hw : RoundsFinite F₁ (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁ (.nearest tb₁) x w
```
**Proof sketch.** `x < midp₁` ⟹ nearest-`F₁` of `x` is the round-down `a`.
Nearest-`F₂` gives `|z − x| ≤ ulp₂/2`, and `hmid` ⟹ `z < midp₁`; `h21`/`hle`
(⟹ `ulp₂ < ulp₁`) keep `z` in `[a, midp₁)`, so nearest-`F₁` of `z` is also `a`.
Hence `w = a =` direct rounding. The `[a, midp₁)` containment is the fiddly
core (Roux's Fig. 2; Flocq splits off `round_round_lt_mid_further_place'`).

**Estimated shape:** ~3 defs (`ulp`, `midp`, `mag`) + ~6–10 supporting lemmas
(below-midpoint⟹round-down, ulp monotonicity, the interval containment) + the
main proof. Then Phase 3 addition = Lemma 16 + Roux Lemma 22 (small-`y` exact
case) + `add_subset` (large-`y` case) glued by a `mag`-gap split.

### Phase 2 progress (in `Mpfx/NearestMidpoint.lean`)

Built and verified (all rest on `[propext, Classical.choice, Quot.sound]`, no `sorry`):

- **Definitions:** `ulp`, `rndDown`, `rndUp`, `midp` (as agreed — real-valued
  `ulp = 2^canonicalExp`, `rndDown/rndUp` from `rndUnbounded`, `midp = rndDown + ulp/2`).
- **Foundations:** `ulp_pos`, `rndDown_le/_mem/_max`, `lt_rndDown_add_ulp`
  (`x < rndDown + ulp`), `le_rndUp`/`rndUp_min`/`rndUp_mem`,
  `rndUp_le_rndDown_add_ulp` (`rndUp ≤ rndDown + ulp`).
- **L1** `ulp_le_half_ulp_of_canonicalExp_lt`: `cexp₂ < cexp₁ ⟹ ulp₂ ≤ ulp₁/2`.
- **L2** `nearest_error_le_half_ulp`: `|z − x| ≤ ulp/2` for a nearest `z`
  (stated over `F.unbounded`, overflow-free — matches Roux's FLX setting).
- **L3** `nearest_eq_rndDown_of_lt_midp`: `x < midp F x ⟹` nearest rounds to
  `rndDown F x`. Proved via the *constructive* rounding (`x < midp` ⟺ scaled
  fraction `< ½` ⟺ `rndInt`/`rndParity` pick the floor) — cheaper than the
  faithful-competitor/adjacency route.

Also built and verified since:

- **L3′** `nearest_eq_rndUp_of_midp_lt`: `midp F x < x ⟹` nearest rounds to
  `rndUp F x` (scaled fraction `> ½` ⟹ `⌈·⌉ = ⌊·⌋+1`).
- **Lemma 16** `rnd_lt_mid` — **proved** (rests on `[propext, Classical.choice,
  Quot.sound]`, no `sorry`), in Flocq's `_place'` form: it takes binade
  consistency `hcexp : F₁.canonicalExp z = F₁.canonicalExp x` as an explicit
  hypothesis. The full assembly works: from `|z − a| < ulp₁/2` (L2+L1) and
  `hcexp`, the two cell sub-cases (`z ≥ a` via L3, `z < a` via L3′) both give
  `◦₁(z) = a = rndDown F₁ x`, then `w = a` by nearest-uniqueness
  (`rndUnbounded_unique`), closing with L3 on `x`.

**L4 — binade consistency: DONE.**

- `canonicalExp_eq_of_log_eq` — `canonicalExp` depends only on `Int.log 2 |·|`.
- `canonicalExp_eq_of_lt_mid` — **proved** `F₁.canonicalExp z = F₁.canonicalExp x`
  from `0 < x`, `h21`, `hle`, `hmid`. Clean argument (no `mag_round_ge` needed):
  `z` lands in `x`'s binade `[2^k, 2^(k+1))` where `k = Int.log 2 x`, because
  **(lower)** `h21 ⟹ F₂.canonicalExp x ≤ k ⟹ 2^k ∈ F₂`, and `z` (faithful) is
  `≥` the `F₂` round-down `≥ 2^k`; **(upper)** `z < midp F₁ x < 2^(k+1)`, the
  latter from `hle` via a floor bound on `rndDown F₁ x`.
- `rnd_lt_mid'` — **Lemma 16, hypothesis-free** (Roux
  `round_round_lt_mid_further_place`): discharges `hcexp` via
  `canonicalExp_eq_of_lt_mid`.

**Phase 2 is COMPLETE.** All of `Mpfx/NearestMidpoint.lean` builds, no `sorry`,
axioms `[propext, Classical.choice, Quot.sound]`.

## 7. Phase 3 — addition (in `Mpfx/DoubleRoundingAdd.lean`)

Roux Theorem 20 (radix 2): tight `p₂ ≥ 2p₁+1`. Proof splits on the exponent gap:
Case 1 (`ln y ≥ φ₁(ln x) − 1`) → `x+y` fits in `2p₁+1` bits, exact intermediate;
Case 2 (`ln y ≤ φ₁(ln x) − 2`, tiny `y`) → `rnd_lt_mid'` + Roux Lemma 22.

**Done & verified** (shared infrastructure):
- `exists_canonical_rep` — positive `y ∈ F` (prec `p`) is `c·2^(canonicalExp y)`,
  `|c| < 2^p`; unifies the `exp=⊥`/finite grid lemmas.
- `canonicalExp_mono` — `canonicalExp` monotone in `|·|`.

**Case 1 precision bound: DONE.**
- `mantissa_pos` (helper) and `sum_precisionAtMost` — **proved**: for `x,y ∈ F₁`,
  `0<y≤x`, gap `≤ p₁+1`, `x+y = C·2^(canonicalExp y)` with `|C| < 2^(2p₁+1)`
  (integer-power algebra, `|C| ≤ 2^(2p₁+1)−2^p₁−1`). Gives `precisionAtMost (2p₁+1)`
  + `quantumAtLeast (canonicalExp y)` for `x+y`. Axioms clean, no `sorry`.

**`rndAdd_pos` (Roux's core case `0 < y ≤ x`, FLX): DONE.** Both cases proved:
- **Case 1** (gap `≤ p₁+1`): `x+y ∈ F₂.unbounded` via `sum_precisionAtMost` +
  `precisionAtMost_mono` + `exp=⊥` (quantum free), then `rndExact`.
- **Case 2** (gap `> p₁+1`, tiny `y`): no binade crossing (since `cx < 2^p₁` ⟹
  `x+y < 2^(ln x)`), so `rndDown F₁(x+y) = x`, `x+y` sits `< ¼·ulp₁` above it,
  well below `midp − ½ulp₂`; `rnd_lt_mid'` closes it. All the `canonicalExp`/
  `midp`/`ulp` facts computed from the shared binade `Int.log 2(x+y) = ex+p₁−1`.

Axioms clean, no `sorry`; whole `Mpfx` aggregate builds.

**`rndAdd` (all same-sign operands, FLX): DONE.** `rndAdd_nonneg` handles both
`≥ 0` (swap via `add_comm` when `x < y`; a zero operand → exact `rndExact`);
`rndAdd` lifts to `0 ≤ x·y` — the both-`≤ 0` case by joint negation
(`RoundsFinite.neg_nearest`), the mixed-with-a-zero cases by exactness, and
`x·y < 0` (true mixed sign) is excluded by the hypothesis. Axioms clean, no
`sorry`; whole `Mpfx` builds. Addition is complete in the same-sign sense.

### Closing the sign gap (subtraction / mixed-sign) — DONE & verified

The FLX sign gap with Flocq is **closed**: the top-level **`rndAdd` now takes
arbitrary-sign operands** (no `hsign` hypothesis) and matches Flocq's
`round_round_plus` in generality.

**Above-midpoint toolkit** (`NearestMidpoint.lean`): neg-reflection helpers
`canonicalExp_neg`, `ulp_neg`, `rndDown_neg_real`, `RoundsFinite.neg_nearest`;
`rnd_gt_mid`/`rnd_gt_mid'` (above-midpoint double rounding by negation of
`rnd_lt_mid`); `canonicalExp_eq_of_gt_mid`; and the unifiers
`nearest_eq_of_close` / `nearest_eq_of_close'` (nearest rounding = grid point `g`
when `|v − g| < ½·2^(cexp v)`).

**Subtraction (`DoubleRoundingAdd.lean`):**
- `diff_precisionAtMost` — `x−y` fits `2p₁+1` bits when the gap `≤ p₁+1`;
  `canonicalExp_lt_of_prec_lt`, `canonicalExp_FLX`.
- **`sub_key_bound`** — the boundary inequality `2^(k−p₂−1) + y < 2^(k−p₁−1)`
  (i.e. `½ulp₂ + y < ¼ulp₁`) when `x = 2^k`. This is what dissolves the feared
  "double-tie edge": it is **strict**, so the intermediate `z = ◦₂(x−y)` never
  lands on the F₁ midpoint. Strictness comes exactly from `y ∈ F₁`
  (`y ≤ 2^(ey+p₁) − 2^ey`, i.e. mantissa `≤ 2^p₁−1`) together with `p₂ ≥ 2p₁+1`,
  via a two-way case split on `eb` vs `k−p₂−1`. (The earlier worry that this hits
  *equality* was mis-analysis: `y ∈ F₁` forces `y` strictly below the edge.)
- **`rndSub_pos`** — `0 < y < x`. Case 1 (gap `≤ p₁+1`): exact via
  `diff_precisionAtMost`. Case 2 (`y` tiny): split on whether `x` is a binade
  boundary. **2a** (`2^k < x`): `x−y` stays in `x`'s binade, `z` stays there too,
  both `◦₁(x−y)` and `◦₁(z)` equal `x` via `nearest_eq_of_close'` at scale `ex`.
  **2b** (`x = 2^k`): `x−y` drops a binade; `sub_key_bound` gives `|z−x| < ¼ulp₁`,
  and a `z < 2^k` / `z ≥ 2^k` split feeds `nearest_eq_of_close'` at the right
  scale. `w = x` by nearest-uniqueness in both.
- **`rndDiff`** — `0 ≤ a, 0 ≤ b`: `a−b ∈ F₁` ⟹ exact; else `rndSub_pos` (order
  `a<b` by negation).
- **`rndAdd`** (all signs): same-sign ⟹ `rndAdd_nonneg` (+ joint negation);
  mixed ⟹ `rndDiff` on `x−(−y)` or `y−(−x)`.

All new theorems verified; axioms `[propext, Classical.choice, Quot.sound]`.

**Still future:** FLT (`exp` finite, `emin₂ ≤ emin₁`); √ (Thm 25), ÷ (Thm 29).

**Open design decision (resolved — recorded for history):**
1. **Represent `ulp`/`midp`/round-down how?** (a) real-valued
   `ulp F x : ℝ := (2:ℝ)^F.canonicalExp x` with the round-down value taken from
   the constructive `rndUnbounded`/`rnd` layer (`RoundOp.lean`); or (b) keep it
   fully relational (round-down as a `RoundsFinite .toNegative` witness, no new
   functions). (a) is closer to Flocq and reads cleanly; (b) avoids depending on
   the constructive layer. *Recommendation:* (a).
2. **Commit now?** Phase 2+3 is a large, multi-lemma effort with the fiddly
   interval-containment core. Multiplication (Phases 0–1) is already a complete,
   self-contained result. Confirm before I invest.

## 7. References
- `flocq-4.2.2/src/Prop/Double_rounding.v`: `round_round_mult` (L661),
  `round_round_mult_hyp` (L613), `round_round_lt_mid_further_place` (L167),
  `round_round_plus` (L1562), `round_round_sqrt` (L2804), `round_round_div`.
- mpfx: `Format.mul_subset`/`add_subset` (`FormatInference.lean`),
  `RoundsFinite`/`IsFaithfulRound` (`Rounding.lean`), `containsPrec`
  (`Containment.lean`), `Grid.lean` midpoint lemmas.
