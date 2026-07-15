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

## 6. References
- `flocq-4.2.2/src/Prop/Double_rounding.v`: `round_round_mult` (L661),
  `round_round_mult_hyp` (L613), `round_round_lt_mid_further_place` (L167),
  `round_round_plus` (L1562), `round_round_sqrt` (L2804), `round_round_div`.
- mpfx: `Format.mul_subset`/`add_subset` (`FormatInference.lean`),
  `RoundsFinite`/`IsFaithfulRound` (`Rounding.lean`), `containsPrec`
  (`Containment.lean`), `Grid.lean` midpoint lemmas.
