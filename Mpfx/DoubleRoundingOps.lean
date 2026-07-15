import Mpfx.FormatInference
import Mpfx.Containment
import Mpfx.Rounding

/-!
# Operation-specific double rounding (Roux 2014)

Pierre Roux, *Innocuous Double Rounding of Basic Arithmetic Operations*
(JFR 7(1), 2014; Flocq `src/Prop/Double_rounding.v`), proves double rounding
innocuous for the *results of specific operations* under precision
relationships weaker than the generic §5.2 rules (`DoubleRounding.lean`).
Where the generic rules hold for every real `x`, these hold only for the
outputs of `×`/`+`/… but let `F₂` be narrower relative to `F₁`.

This file transcribes the **multiplication** result (Roux Thm 10 /
Flocq `round_round_mult`), radix 2. The rest of the paper (addition, square
root, division) needs Roux's round-to-nearest midpoint Lemma 16
(`round_round_lt_mid_further_place`), which has no counterpart here yet; see
`docs/agents/DOUBLE_ROUNDING_OPS_PLAN.md`.

## Technique: exact intermediate

Roux's multiplication proof is `round_generic`: the exact product `x · y` is
*representable in `F₂`*, so the intermediate rounding `◦₂(x · y) = x · y` is a
no-op and the chained rounding collapses to the direct one. This holds for
**any** rounding modes, not just round-to-nearest.

Both halves already exist: `RoundsFinite.eq_of_mem` (`Rounding.lean`) is the
`round_generic` step, and `Format.mul_subset` (`FormatInference.lean`) gives
`x · y ∈ opMul F₁ F₁`. The precision hypothesis is the project-standard
containment `opMul F₁ F₁ ⊆ F₂` — since `opMul F₁ F₁` evaluates to
`𝒜(2p₁, 2·exp₁, b₁²)`, this reads `𝒜(2p₁, 2·exp₁, b₁²) ⊆ F₂`, i.e. Roux's
`p₂ ≥ 2p₁` together with the underflow side conditions (`exp₂ ≤ 2·exp₁`,
`b₁² ≤ b₂`) of his FLT/FTZ corollaries.

Stated relationally over `RoundsFinite`, matching the §5.2 rules: given `z`
the `F₂`-rounding of the input and `w` the `F₁`-rounding of `z`, conclude `w`
is the direct `F₁`-rounding of the input.
-/

namespace Mpfx

open scoped Pointwise

/-- **Exact-intermediate collapse.** If the input `v` is already representable
in the wide format `F₂`, double rounding is trivially correct for *any* modes:
the intermediate rounding fixes `v` (`z = v` by `RoundsFinite.eq_of_mem`), so
the chained rounding of `v` is the direct one. This is the spec-relational
form of Flocq's `round_generic`-based collapse and the shared core of every
"exact intermediate" operation rule. -/
theorem rndExact {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode}
    {v : Dyadic} (hv : v ∈ F₂) {z w : Dyadic}
    (hz : RoundsFinite F₂ rm₂ (v : ℝ) z) (hw : RoundsFinite F₁ rm₁ (z : ℝ) w) :
    RoundsFinite F₁ rm₁ (v : ℝ) w := by
  rw [RoundsFinite.eq_of_mem hv hz] at hw
  exact hw

/-- **rnd-mult** (Roux Thm 10 / Flocq `round_round_mult`). Operation-specific
double rounding for multiplication.

If the inferred product format `F₁ ⊗ F₁` is contained in the wide format `F₂`
(`opMul F₁ F₁ ⊆ F₂` — the mpfx analog of `p₂ ≥ 2p₁`, with `exp₂ ≤ 2·exp₁` and
`b₁² ≤ b₂` covering underflow), then for `x, y ∈ F₁` and **any** rounding modes
`rm₁ rm₂`, rounding `x · y` into `F₂` (to `z`) and then into `F₁` (to `w`)
agrees with rounding `x · y` directly into `F₁`.

Unlike the generic §5.2 rules this needs no per-mode side conditions, because
the intermediate rounding is *exact*: `x · y ∈ F₂`, so `z = x · y`. -/
theorem rndMul {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode}
    (hsub : Format.opMul F₁.toFormat F₁.toFormat ⊆ F₂.toFormat)
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁) {z w : Dyadic}
    (hz : RoundsFinite F₂ rm₂ ((x * y : Dyadic) : ℝ) z)
    (hw : RoundsFinite F₁ rm₁ (z : ℝ) w) :
    RoundsFinite F₁ rm₁ ((x * y : Dyadic) : ℝ) w := by
  -- `x · y ∈ opMul F₁ F₁` (Format.mul_subset), hence `x · y ∈ F₂` (hsub).
  have hxy_prod : (x * y : Dyadic) ∈ Format.opMul F₁.toFormat F₁.toFormat :=
    Format.mem_toSet.mp
      (Format.mul_subset F₁.toFormat F₁.toFormat
        (Set.mul_mem_mul (Format.mem_toSet.mpr hx) (Format.mem_toSet.mpr hy)))
  have hxy_mem : (x * y : Dyadic) ∈ F₂ := hsub _ hxy_prod
  exact rndExact hxy_mem hz hw

/-- **rnd-mult, explicit parameters** (analog of Roux's `_FLX`/`_FLT`/`_FTZ`
corollaries). The containment hypothesis of `rndMul` follows from the three
`𝒜`-parameter orderings via `containsPrec`:

* `F₁.p + F₁.p ≤ F₂.p`  (`p₂ ≥ 2p₁`),
* `F₂.exp ≤ F₁.exp + F₁.exp`  (`exp₂ ≤ 2·exp₁`),
* `(opMul F₁ F₁).b ≤ F₂.b`  (`b₁² ≤ b₂`).

The `.p`/`.exp` bounds are `opMul`'s components by definition; the bound
conjunct is left as the `opMul`-level order since `opMul`'s `b` is `b₁·b₁`
only when both operand bounds are finite (else `⊤`). -/
theorem rndMul_of_params {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode}
    (hp : F₁.p + F₁.p ≤ F₂.p)
    (he : F₂.exp ≤ F₁.exp + F₁.exp)
    (hb : (Format.opMul F₁.toFormat F₁.toFormat).b ≤ F₂.b)
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁) {z w : Dyadic}
    (hz : RoundsFinite F₂ rm₂ ((x * y : Dyadic) : ℝ) z)
    (hw : RoundsFinite F₁ rm₁ (z : ℝ) w) :
    RoundsFinite F₁ rm₁ ((x * y : Dyadic) : ℝ) w :=
  rndMul (Format.containsPrec hp he hb) hx hy hz hw

end Mpfx
