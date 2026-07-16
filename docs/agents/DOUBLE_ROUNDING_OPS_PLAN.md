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

### Underflow gap (FLT) — status

**Multiplication FLT: already done.** `rndMul`/`rndMul_of_params`
(`DoubleRoundingOps.lean`) are stated via the format-generic containment
`opMul F₁ F₁ ⊆ F₂` / `containsPrec`, whose `exp₂ ≤ 2·exp₁` conjunct *is* Roux's
Table-II condition `emin₂ ≤ 2·emin₁`. No FLX assumption anywhere — the FLT (and
FTZ) corollaries are immediate.

**Addition/subtraction FLT: DONE & verified.** Roux's Table II for `+`/`−`
(β=2): keep `p₂ ≥ 2p₁+1` and add `emin₂ ≤ emin₁`. The top-level `rndAdd`,
`rndDiff`, `rndSub_pos`, `rndAdd_pos`, `rndAdd_nonneg` all now take the single
hypothesis **`hexp : F₂.exp ≤ F₁.exp`** in place of `F₁.exp = ⊥ ∧ F₂.exp = ⊥` —
one statement covering FLX (`⊥ ≤ ⊥`) and FLT (`↑emin₂ ≤ ↑emin₁`). Arbitrary
signs, all round-to-nearest tie-breaks.

The clean structure (as implemented):

> Split on whether `x±y ∈ F₂`. The complement forces **every** relevant value
> into the *normal* range (`canonicalExp = log+1−p`, no `emin` clamp), where the
> FLX Case-2 midpoint proof runs verbatim.

Why: if `x±y ∉ F₂` then its precision `> p₂ ≥ 2p₁+1`, so `mag(x±y) − ey > 2p₁`
(`ey = canonicalExp F₁ y ≥ emin₁ ≥ emin₂`), giving `mag > emin₁+2p₁` — hence
`x±y` normal in `F₁` and `F₂`, and `z ≈ x±y` normal in `F₁`. The exact case
`x±y ∈ F₂` subsumes the old small-gap Case 1 **and** all subnormal cases
(subnormals of `F₂` are always representable since `x±y` is a multiple of `2^ey`,
`ey ≥ emin₂`).

Implementation (`DoubleRoundingAdd.lean`):
- **`canonicalExp_closed`** — FLX closed form under normality hyp
  `F.exp ≤ ↑(log|v|+1−p)` (vacuous for `⊥`); `exp_le_canonicalExp_coe`.
- **`quantumAtLeast_sub`/`quantumAtLeast_add`** — `x±y` inherits `F₁`'s quantum;
  **`mem_F₂_of_subnormal`** — a subnormal-in-`F₂` result is exactly representable.
- **`rndSub_pos_normal`/`rndAdd_pos_normal`** — the midpoint core, taking `hgap`
  (gap `> p₁+1`) and `hF2norm` (`x±y` normal in `F₂`); discharge `F₁`-normality
  of `x`/`x±y`/`z` via `cE1` (a local `canonicalExp_closed` wrapper) using the
  binade facts the body already computes.
- **`rndSub_pos`/`rndAdd_pos`** — three-case dispatchers (small-gap exact /
  subnormal exact / normal→`_normal`).

All verified; axioms `[propext, Classical.choice, Quot.sound]`.

**Still future:** √ (Thm 25), ÷ (Thm 29). These produce non-`Dyadic` results, so
"exact intermediate" no longer applies — but that is *fine*: `RoundsFinite`
rounds a real, so the statements just take `Real.sqrt x` / `x / y` as input and
lean entirely on the midpoint engine (which is two-sided: `rnd_lt_mid'` +
`rnd_gt_mid'`). What they add is operation-specific algebra bounding the result
away from `F₁`-midpoints.

### Step 1 (shared √/÷ prerequisite): DONE — `round_round_mid_cases`

Built in `NearestMidpoint.lean`: **`midp'`** (upper midpoint `rndUp − ½ulp`) and
**`round_round_mid_cases`** (Flocq's dispatcher). Given `0 < x`, `F₂` finer at
`x` (`h21`), `hle`, `htop`, it reduces double rounding to a *near-midpoint*
obligation `hcmid : |x − midp₁ x| ≤ ½ulp₂ → …`; the two far cases go to
`rnd_lt_mid'` / `rnd_gt_mid'`. The √/÷ proofs discharge `hcmid` by `exfalso` from
the separation lemma. Verified, axioms `[propext, Classical.choice, Quot.sound]`.

*Caveat / known follow-up:* `round_round_mid_cases` currently carries `htop`
(result bounded `½ulp₂` away from the binade top `2^(mag x)`), inherited from
`rnd_gt_mid'`. Flocq's `gt_mid_further_place` instead handles the binade-top
crossing internally (`round_round_gt_mid_further_place'`, the `x'' = bpow(mag x)`
branch). For √/÷ this is expected to be dischargeable by the *same* separation
argument that kills `hcmid` (the result is not within `½ulp₂` of `2^(mag x)`
either, since that is an `F₁` point); if a case genuinely needs it, harden the
gt-path to drop `htop` (the abstract crossing argument: the intermediate `z`
lands on `2^(mag x)`, which is in `F₁`, and `nearest_eq_of_close'` closes both
`◦₁(z)` and `◦₁(x)` to it).

**Step 2: square root** (in `Mpfx/DoubleRoundingSqrt.lean`).
- (a) **DONE** — `log_sqrt_bounds`: `2L ≤ Int.log 2 x ≤ 2L+1` for `L = Int.log 2 √x`
  (Flocq `mag_sqrt_disj`), by squaring the `Int.log` bounds on `√x`. Verified.
- (b) **DONE** — `round_round_sqrt_aux`: `½ulp₂ < |√x − midp₁(√x)|`. Ported the
  Figueroa squaring argument: assume `√x` within `½ulp₂` of the midpoint `a+½u₁`
  (`a = rndDown₁ √x`), so `a+½(u₁−u₂) ≤ √x ≤ a+½(u₁+u₂)`; square (`x = (√x)²`) to
  trap `x` strictly between `A := a²+u₁a` and `A + u₁²`; both `A` and `x` are integer
  multiples of `M := 2^(2e₁) = u₁²` (using `a = ma·2^e₁`, `x = mx·2^(cexp₁ x)`,
  `cexp₁ x ≥ 2e₁`), and no multiple of `M` lies strictly in `(A, A+M)`. Hypotheses:
  `hxrep` (x on F₁ grid), `hf1` (`2e₁ ≤ cexp₁ x`), `hle`, `hquant`
  (`e₂+log√x+1 ≤ 2e₁−2`, i.e. Roux's `p₂ ≥ 2p₁+2`). Key Lean notes: `clear_value`
  the `let`s (`ma`,`a`,`A`,`M`) or `linarith`/`ring` `whnf`-timeout unfolding `⌊·⌋`;
  watch `2^e₁^2` precedence (`(2^e₁)^2`). Verified, axioms clean.
- (c) **DONE** — `rndSqrt` (FLX): `x ∈ F₁`, `0 < x`, `p₂ ≥ 2p₁+2` ⟹ double rounding
  of `√x` innocuous. Assembled via `round_round_mid_cases`; `hcmid` discharged by
  `absurd … (not_le.mpr (round_round_sqrt_aux …))`; `hf1`/`hle`/`hquant`/`h21` all
  fall out of `canonicalExp_FLX` + `log_sqrt_bounds` + `omega`; `hxrep` from
  `exists_canonical_rep`. Verified, axioms clean.

  **`htop` sub-issue RESOLVED (option i, in `NearestMidpoint.lean`):** hardened the
  midpoint engine — added `canonicalExp_eq_of_gt_mid'` (takes `z < 2^(mag x)`
  directly) and **`rnd_gt_mid_robust`** (drops `htop`): if `z` stays in `x`'s binade
  use `_gt_mid'`; else `z` crosses, and since `z` is the round-up of `x` bounded above
  by `2^(mag x) ∈ F₂`, `z = 2^(mag x)` exactly ∈ `F₁`, so `◦₁(z)=z` and
  `◦₁(x)=z` (both close via `nearest_eq_of_close'`). `round_round_mid_cases` no longer
  takes `htop`. This is reused directly by `÷`.

- (d) **DONE** — square root FLX+FLT, as two explicit top-level theorems
  **`rndSqrt_FLX`** and **`rndSqrt_FLT`** over a shared format-agnostic
  **`rndSqrt_core`** (takes the discharged `hxrep`/`hf1`/`hle`/`hquant`, derives
  `h21` from `hquant`+`hle`, runs `round_round_mid_cases` + aux). `rndSqrt_FLX`
  (`F₁.exp = F₂.exp = ⊥`) and `rndSqrt_FLT` (`emin₁ ≤ 0` plus Table-II
  `emin₂ ≤ emin₁−p₁−2 ∨ 2emin₂ ≤ emin₁−4p₁−2`) each discharge the core hypotheses
  via `canonicalExp_FLX`/`canonicalExp_FLT` (`max(log|v|+1−p, emin)`) + member bound
  `2^emin₁ ≤ x` + `log_sqrt_bounds`, then **`omega` (handles `max` on ℤ)** closes
  `hf1`/`hle`/`hquant` (`rcases hE <;> omega` for the FLT underflow disjunction).
  No `Valid_exp` machinery needed. Verified, axioms clean. **Square root complete.**

**Division (Thm 29) — in progress** (`Mpfx/DoubleRoundingDiv.lean`). See the
dedicated plan in §9 below.

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

## 8. Cleanup / refactor pass (2026-07-15)

Structural cleanup only — no change to theorem statements or the mathematical
content of proofs; all still verified, axioms `[propext, Classical.choice,
Quot.sound]`. Current names/locations **supersede references earlier in this doc**:

- **New module `Mpfx/CanonicalExp.lean`** holds the format-generic `canonicalExp`
  lemmas, moved out of `DoubleRoundingAdd`/`DoubleRoundingSqrt`:
  `exists_canonical_rep`, `canonicalExp_mono`, `canonicalExp_closed`,
  `canonicalExp_FLX` (now a one-line corollary of `_closed`), `canonicalExp_FLT`
  (no longer `private`), `exp_le_canonicalExp_coe`.
- **`canonicalExp_eq_of_gt_mid'` → renamed `canonicalExp_eq_of_binade_top`** (the
  shared "binade consistency from a direct upper bound `z < 2^(mag x)`" lemma);
  `canonicalExp_eq_of_lt_mid` now derives the upper bound then calls it.
- **`nearest_eq_rndDown_of_lt_midp` / `nearest_eq_rndUp_of_midp_lt`** are now thin
  wrappers over `nearest_eq_of_close` (moved above them; the four grid-point
  lemmas are colocated).
- **`sum_precisionAtMost` / `diff_precisionAtMost`** share
  `add_sub_mantissa_setup` + `two_pow_two_p_split`; the small-gap/subnormal
  branches of `rndSub_pos`/`rndAdd_pos` share `rndSmallGap_exact` /
  `rndSubnormal_exact`; `quantumAtLeast_sub` derives from `quantumAtLeast_add` +
  a new `quantumAtLeast_neg`.
- **Deleted (dead):** `rnd_gt_mid'`, `canonicalExp_eq_of_gt_mid` (non-primed),
  `midp'`, `rndDown_lt_midp`, `midp_lt_rndDown_add_ulp` (NearestMidpoint);
  `canonicalExp_lt_of_prec_lt` (Add). The two-sided engine's far cases now go to
  `rnd_lt_mid'` / `rnd_gt_mid_robust` (the deleted `rnd_gt_mid'` and its `htop`
  are gone — see §Step 1 caveat, resolved).

## 9. Division (Theorem 29) — implementation plan

**Statement (Roux Thm 29, radix 2 / even β).** For `p₂ ≥ 2p₁` (same bound as ×,
and tight — Remark 30 counterexample at `p₂ = 2p₁−1`), `◦₁(◦₂(x/y)) = ◦₁(x/y)`
for `x,y ∈ FLXp₁`, `y ≠ 0`, both roundings to nearest (any tie). Even radix is
*required* (odd radices need a directed tie-break — out of scope). FLT variant
also holds (no underflow issue for IEEE binary).

**Engine reuse.** Unlike Flocq's finer `round_round_all_mid_cases` (which pre-splits
the near-mid region into aux0/aux1/aux2/eq-mid), we reuse our existing
`round_round_mid_cases`: it reduces to one near-mid obligation
`hcmid : |x/y − midp₁| ≤ ½ulp₂ → RoundsFinite …`. Inside `hcmid` we case-split on
`x/y = midp₁ (x/y)`:
- **≠ (near but not equal):** *impossible* — the division separation lemma (below)
  gives `¬ (0 < |x/y − midp₁| ≤ ½ulp₂)`. Analogue of `round_round_sqrt_aux`.
- **= (exact midpoint):** the even-radix lemma (below) puts `x/y ∈ F₂`, so the
  intermediate is exact (`z = x/y` via `RoundsFinite.eq_of_mem`), and
  `◦₁(z) = ◦₁(x/y)` closes it (like `rndSmallGap_exact`/`rndSubnormal_exact`).

Binade consistency + the two far cases (`< m−½ulp₂`, `> m+½ulp₂`) are already
handled by `round_round_mid_cases` (`rnd_lt_mid'` / `rnd_gt_mid_robust`); the
binade-top/aux0 boundary is subsumed by `rnd_gt_mid_robust`.

**Pieces** (FLX all **DONE**, verified, axioms `[propext, Classical.choice, Quot.sound]`).
1. **DONE — `log_div_bounds`** (Flocq `mag_div_disj`): `Lx−Ly−1 ≤ Int.log 2 (x/y)
   ≤ Lx−Ly`. Proved by dividing the binade bounds on `x`, `y`.
2. **DONE — `midp_mem_F₂` (even radix = radix 2).** If `0 < v`, `v = midp F₁ v`,
   and `F₂.canonicalExp v ≤ F₁.canonicalExp v − 1`, then the midpoint dyadic
   `g := ofIntZpow (2ma+1) (e₁−1)` (`ma = ⌊v·2^(−e₁)⌋`) has `(g:ℝ) = v` and
   `g ∈ F₂`. Multiple of `2^(e₁−1)` with `e₁−1 ≥ e₂ ≥ F₂.exp` (quantum), and
   `|v·2^(−e₂)| < 2^p₂` (precision, from `log_sub_prec_le_canonicalExp`). Mirrors
   `mem_F₂_of_subnormal`.
3. **DONE — `round_round_div_aux` (separation, Figueroa).** For `v = x/y` with
   `x,y ∈ F₁`, if `v ≠ midp₁ v` then `½ulp₂ < |v − midp₁ v|`. Multiplying the
   midpoint gap by `y` gives `x − m·y = K·2^(e₁−1+ey)` with `K` a *nonzero integer*
   (`e₁−1+ey ≤ ex`, `hex_ge`); so `|x−m·y| ≥ 2^(e₁−1+ey)`, clashing with the
   `≤ 2^(e₂−1)·y < 2^(e₂−1+ey+p₁)` bound once `e₂ ≤ e₁−p₁` (`hquant`, i.e.
   `p₂ ≥ 2p₁`). Cleaner (linear/integrality) than the √ quadratic argument.
4. **DONE — `rndDiv_core`** (format-agnostic): runs `round_round_mid_cases`;
   discharges `hcmid` by `by_cases (v = midp₁ v)` → `midp_mem_F₂` (exact) /
   `absurd … (not_le.mpr (round_round_div_aux …))` (impossible).
5. **DONE — `rndDiv_pos` / `rndDiv_posden` / `rndDiv_FLX` (FLX).** `rndDiv_pos` (a,b>0)
   discharges the core hyps via `canonicalExp_FLX` + `log_div_bounds` + `omega`;
   `rndDiv_posden` adds arbitrary-sign numerator (`a<0` via `neg_nearest`, `a=0`
   via `rndExact`); the top-level **`rndDiv_FLX`** adds negative denominator
   (`a/b = (−a)/(−b)`). Full statement: `a,b ∈ F₁`, `b ≠ 0`, `p₂ ≥ 2p₁`, nearest.

**FLT division — DONE** (`emin₂ ≤ emin₁ − p₁ − 2` ∧ `p₂ ≥ 2p₁`, Flocq
`round_round_div_FLT`), after a **rework of the separation lemma**. FLT `x/y`
splits by `cexp₁ v` vs `mag v` into: deeply-subnormal, boundary
(`cexp₁ v = mag v + 1`), and normal (`cexp₁ v ≤ mag v`). FLX only ever hits the
normal regime (`cexp = mag − p₁ < mag`), which is why the original FLX-tuned
`round_round_div_aux` sufficed there but broke for FLT.

*The obstacle (now solved).* The first `round_round_div_aux` fixed the integrality
scale at `2^(cexp₁ v − 1 + cexp₁ b)`, needing `cexp₁ v − 1 + cexp₁ b ≤ cexp₁ a`. In
FLT the `max` inflates a subnormal operand's `cexp` to `emin₁`, breaking it —
counterexample `p₁=5, emin₁=5, a=512, b=32 ⇒ v=16` (all in `F₁`, regime 3): it
wants `5−1+5 ≤ 5` (false); FLX gives `0 ≤ 5` ✓.

*The fix (min-scale).* Reworked `round_round_div_aux` to a **`min`-scale**
integrality `x − m·y = K·2^min(cexp₁ x, cexp₁ v−1+cexp₁ y)` — always valid with no
ordering assumption. The contradiction then needs two bounds, taken as hypotheses:
`hA : cexp₂ v + Int.log y ≤ cexp₁ x` and `hB : cexp₂ v + Int.log y ≤ cexp₁ v − 1 +
cexp₁ y`. These are **`omega`-provable for both FLX and FLT** from `hquant`, the
regime bound, `log_div_bounds`, and `cexp = max(…) ≥ mag − p₁` (`le_max_left`) —
the `mag`-based lower bounds dodge the `cexp`-inflation. A bonus: because `hA`/`hB`
hold in the boundary regime too, the reworked aux *itself* excludes the boundary
sliver, so **Flocq's ~90-line `div_aux0` never had to be ported**.

*Pieces (all DONE, verified).* `round_round_div_aux` (min-scale, `hA`/`hB`);
`nearest_zero_of_small` (FLT `0 ≤ x' < 2^(emin₁−1)` rounds to `0`);
`round_round_div_zero` (deep-underflow: rounds to `0`); `rndDiv_pos_normal_FLT`
(regime 3 via `rndDiv_core`); `rndDiv_pos_FLT` (regime dispatch: normal → regime-3
lemma; underflow → far via `div_zero`, sliver → `div_aux` contradiction);
`rndDiv_posden_FLT` / `rndDiv_FLT` (sign wrappers). Full statement: `a,b ∈ F₁`,
`b ≠ 0`, `p₂ ≥ 2p₁`, `emin₂ ≤ emin₁ − p₁ − 2`, both roundings to nearest.

**All operations complete: ×, +, −, √, ÷ for both FLX and FLT.**

## 7. References
- `flocq-4.2.2/src/Prop/Double_rounding.v`: `round_round_mult` (L661),
  `round_round_mult_hyp` (L613), `round_round_lt_mid_further_place` (L167),
  `round_round_plus` (L1562), `round_round_sqrt` (L2804), `round_round_div`.
- mpfx: `Format.mul_subset`/`add_subset` (`FormatInference.lean`),
  `RoundsFinite`/`IsFaithfulRound` (`Rounding.lean`), `containsPrec`
  (`Containment.lean`), `Grid.lean` midpoint lemmas.
