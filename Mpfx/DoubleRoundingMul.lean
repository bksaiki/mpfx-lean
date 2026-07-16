import Mpfx.FormatInference
import Mpfx.Containment
import Mpfx.Rounding
import Mpfx.CanonicalExp

/-!
# Operation-specific double rounding: multiplication (Roux 2014)

Pierre Roux, *Innocuous Double Rounding of Basic Arithmetic Operations*
(JFR 7(1), 2014; Flocq `src/Prop/Double_rounding.v`), proves double rounding
innocuous for the *results of specific operations* under precision
relationships weaker than the generic §5.2 rules (`DoubleRounding.lean`).
Where the generic rules hold for every real `x`, these hold only for the
outputs of `×`/`+`/… but let `F₂` be narrower relative to `F₁`.

This file transcribes the **multiplication** result (Roux Thm 10 /
Flocq `round_round_mult`), radix 2, and the shared **exact-intermediate**
combinator `rndExact` on which it — and the underflow/exact cases of the other
operations — rests. Addition/subtraction, square root, and division live in
`DoubleRoundingAdd`/`DoubleRoundingSqrt`/`DoubleRoundingDiv`; see
`docs/agents/DOUBLE_ROUNDING_OPS_PLAN.md`.

## Technique: exact intermediate

Roux's multiplication proof is `round_generic`: the exact product `x · y` is
*representable in `F₂`*, so the intermediate rounding `◦₂(x · y) = x · y` is a
no-op and the chained rounding collapses to the direct one (`rndExact`). This
holds for **any** rounding modes, not just round-to-nearest.

`rndMul_FLX`/`rndMul_FLT` establish `x · y ∈ F₂.unbounded` from the explicit
bounds `p₂ ≥ 2p₁` (mantissas multiply, `mul_precisionAtMost`) and `exp₂ ≤ 2·exp₁`
(quanta add, `quantumAtLeast_mul`), then apply `rndExact`. Stated relationally
over `RoundsFinite`: given `z` the `F₂`-rounding of the input and `w` the
`F₁`-rounding of `z`, conclude `w` is the direct `F₁`-rounding of the input.
-/

namespace Mpfx

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

/-- A product of two `p₁`-bit dyadics fits in `p₂` bits when `2p₁ ≤ p₂`
(mantissas multiply, `|cx·cy| < 2^(2p₁) ≤ 2^p₂`). -/
private theorem mul_precisionAtMost {p₁ p₂ : ℕ+} (hpp : 2 * p₁ ≤ p₂)
    {x y : Dyadic} (hx : Dyadic.precisionAtMost ((p₁ : ℕ+) : WithTop ℕ+) x)
    (hy : Dyadic.precisionAtMost ((p₁ : ℕ+) : WithTop ℕ+) y) :
    Dyadic.precisionAtMost ((p₂ : ℕ+) : WithTop ℕ+) (x * y) := by
  obtain ⟨cx, ex, hcx, hcxb⟩ := (Dyadic.precisionAtMost_coe_real p₁ x).mp hx
  obtain ⟨cy, ey, hcy, hcyb⟩ := (Dyadic.precisionAtMost_coe_real p₁ y).mp hy
  refine (Dyadic.precisionAtMost_coe_real p₂ (x * y)).mpr ⟨cx * cy, ex + ey, ?_, ?_⟩
  · rw [show ((x * y : Dyadic) : ℝ) = (x : ℝ) * (y : ℝ) from by push_cast; ring, hcx, hcy,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; push_cast; ring
  · rw [abs_mul]
    have hpn : 2 * (p₁ : ℕ) ≤ (p₂ : ℕ) := by exact_mod_cast hpp
    calc |cx| * |cy| < (2 : ℤ) ^ (p₁ : ℕ) * (2 : ℤ) ^ (p₁ : ℕ) :=
          mul_lt_mul'' hcxb hcyb (abs_nonneg _) (abs_nonneg _)
      _ = (2 : ℤ) ^ (2 * (p₁ : ℕ)) := by rw [← pow_add]; congr 1; ring
      _ ≤ (2 : ℤ) ^ (p₂ : ℕ) := pow_le_pow_right₀ (by norm_num) hpn

/-- **Product exactly representable in the finer format.** For `x, y ∈ F₁` with
`2p₁ ≤ p₂` and `F₂.exp ≤ F₁.exp + F₁.exp` (`exp₂ ≤ 2·exp₁`), the product `x · y`
lies in `F₂.unbounded`. -/
private theorem mul_mem_F₂_unbounded {F₁ F₂ : FiniteFormat} {p₁ p₂ : ℕ+}
    (hp₁ : F₁.p = ((p₁ : ℕ+) : WithTop ℕ+)) (hp₂ : F₂.p = ((p₂ : ℕ+) : WithTop ℕ+))
    (hpp : 2 * p₁ ≤ p₂) (he : F₂.exp ≤ F₁.exp + F₁.exp)
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁) :
    (x * y : Dyadic) ∈ F₂.unbounded := by
  refine ⟨?_, ?_, trivial⟩
  · rw [FiniteFormat.unbounded_p, hp₂]
    exact mul_precisionAtMost hpp (hp₁ ▸ hx.1) (hp₁ ▸ hy.1)
  · rw [FiniteFormat.unbounded_exp]
    exact Dyadic.quantumAtLeast_anti he (quantumAtLeast_mul hx.2.1 hy.2.1)

/-- **rnd-mult, FLX** (Roux Thm 10 / Figueroa, radix 2). For `x, y ∈ F₁` in an FLX
format (`exp = ⊥`) with `p₂ ≥ 2p₁`, double rounding of `x · y` is innocuous for
**any** rounding modes `rm₁, rm₂` — the product is exactly `F₂`-representable, so
the intermediate rounding is a no-op (`rndExact`). -/
theorem rndMul_FLX {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode} {p₁ p₂ : ℕ+}
    (hp₁ : F₁.p = ((p₁ : ℕ+) : WithTop ℕ+)) (hp₂ : F₂.p = ((p₂ : ℕ+) : WithTop ℕ+))
    (hpp : 2 * p₁ ≤ p₂) (hexp₁ : F₁.exp = ⊥) (hexp₂ : F₂.exp = ⊥)
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁) {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded rm₂ ((x * y : Dyadic) : ℝ) z)
    (hw : RoundsFinite F₁.unbounded rm₁ (z : ℝ) w) :
    RoundsFinite F₁.unbounded rm₁ ((x * y : Dyadic) : ℝ) w :=
  rndExact (mul_mem_F₂_unbounded hp₁ hp₂ hpp
    (by rw [hexp₁, hexp₂]; simp) hx hy) hz hw

/-- **rnd-mult, FLT** (Roux Thm 10 / Figueroa, radix 2). The FLT version:
`F₁.exp = emin₁`, `F₂.exp = emin₂`, with `p₂ ≥ 2p₁` and `emin₂ ≤ 2·emin₁`. Again
holds for any modes, via exact representability of the product. -/
theorem rndMul_FLT {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode} {p₁ p₂ : ℕ+}
    {emin₁ emin₂ : ℤ}
    (hp₁ : F₁.p = ((p₁ : ℕ+) : WithTop ℕ+)) (hp₂ : F₂.p = ((p₂ : ℕ+) : WithTop ℕ+))
    (hpp : 2 * p₁ ≤ p₂)
    (hexp₁ : F₁.exp = (emin₁ : WithBot ℤ)) (hexp₂ : F₂.exp = (emin₂ : WithBot ℤ))
    (hemin : emin₂ ≤ 2 * emin₁)
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁) {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded rm₂ ((x * y : Dyadic) : ℝ) z)
    (hw : RoundsFinite F₁.unbounded rm₁ (z : ℝ) w) :
    RoundsFinite F₁.unbounded rm₁ ((x * y : Dyadic) : ℝ) w :=
  rndExact (mul_mem_F₂_unbounded hp₁ hp₂ hpp
    (by rw [hexp₁, hexp₂, ← WithBot.coe_add]; exact_mod_cast (by omega : emin₂ ≤ emin₁ + emin₁))
    hx hy) hz hw

end Mpfx
