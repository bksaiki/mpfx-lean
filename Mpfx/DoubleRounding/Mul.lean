import Mpfx.Format.Inference
import Mpfx.DoubleRounding.Basic
import Mpfx.Format.CanonicalExp

/-!
# Operation-specific double rounding: multiplication (Roux 2014)

Pierre Roux, *Innocuous Double Rounding of Basic Arithmetic Operations*
(JFR 7(1), 2014), proves double rounding
innocuous for the *results of specific operations* under precision
relationships weaker than the generic §5.2 rules (`Mpfx/DoubleRounding/Basic.lean`).
Where the generic rules hold for every real `x`, these hold only for the
outputs of `×`/`+`/… but let `F₂` be narrower relative to `F₁`.

This file transcribes the **multiplication** result (Roux Thm 10 /
Flocq `round_round_mult`), radix 2. Addition/subtraction, square root, and
division live in `DoubleRounding.Add`/`.Sqrt`/`.Div`.

## Technique: exact intermediate

Roux's multiplication proof is `round_generic`: the exact product `x · y` is
*representable in `F₂`*, so the intermediate rounding `◦₂(x · y) = x · y` is a
no-op and the chained rounding collapses to the direct one (`rndExact`). This
holds for **any** rounding modes, not just round-to-nearest.

`rndMul_expBot`/`rndMul_expFinite` establish `x · y ∈ F₂.unbounded` from the explicit
bounds `p₂ ≥ 2p₁` (mantissas multiply, `Dyadic.precisionAtMost_mul`) and `exp₂ ≤ 2·exp₁`
(quanta add, `Dyadic.quantumAtLeast_mul`), then apply `rndExact`. Stated relationally
over `RoundsFinite`: given `z` the `F₂`-rounding of the input and `w` the
`F₁`-rounding of `z`, conclude `w` is the direct `F₁`-rounding of the input.
-/

namespace Mpfx

/-- **Product exactly representable in the finer format.** For `x, y ∈ F₁` with
`2p₁ ≤ p₂` and `F₂.exp ≤ F₁.exp + F₁.exp` (`exp₂ ≤ 2·exp₁`), the product `x · y`
lies in `F₂.unbounded`. -/
private theorem mul_mem_F₂_unbounded {F₁ F₂ : FiniteFormat} {p₁ p₂ : ℕ}
    (hp₁ : F₁.p = (p₁ : Prec)) (hp₂ : F₂.p = (p₂ : Prec))
    (hpp : 2 * p₁ ≤ p₂) (he : F₂.exp ≤ F₁.exp + F₁.exp)
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁) :
    (x * y : Dyadic) ∈ F₂.unbounded :=
  -- the product lives in the intermediate format `𝒜(2p₁, exp₁+exp₁, ⊤)`, which
  -- is contained in `F₂.unbounded` by `𝒜-Contains-Prec` (`mem_unbounded_of_le`).
  Format.mem_unbounded_of_le (p := ((2 * p₁ : ℕ) : Prec))
    (by rw [hp₂]; exact_mod_cast hpp) he
    (by rw [two_mul, Nat.cast_add]; exact Dyadic.precisionAtMost_mul (hp₁ ▸ hx.1) (hp₁ ▸ hy.1))
    (Dyadic.quantumAtLeast_mul hx.2.1 hy.2.1)

/-- **rnd-mult, no minimum quantum** (Roux Thm 10 / Figueroa, radix 2). With
`exp = ⊥` formats
`F₁ = 𝒜(p₁, ⊥, b₁)` and `F₂ = 𝒜(p₂, ⊥, b₂)`, double rounding of a product `x · y`
(`x, y ∈ F₁`) is innocuous for **any** rounding modes when

* **precision:** `p₂ ≥ 2·p₁`,
* **exponent:** both `⊥` (no minimum quantum),
* **bounds:** no relationship required — the roundings are overflow-free (`unbounded`).

*Containment view:* an exact product of two `p₁`-bit values needs `2p₁` bits, so
`p₂ ≥ 2p₁` says the product format `𝒜(2p₁, ⊥, ⊤) ⊆ F₂`; hence `x · y` is exactly
`F₂`-representable and the inner rounding is a no-op (`rndExact`). -/
theorem rndMul_expBot {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode} {p₁ p₂ : ℕ}
    (hp₁ : F₁.p = (p₁ : Prec)) (hp₂ : F₂.p = (p₂ : Prec))
    (hpp : 2 * p₁ ≤ p₂) (hexp₁ : F₁.exp = ⊥) (hexp₂ : F₂.exp = ⊥)
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁) {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded rm₂ ((x * y : Dyadic) : ℝ) z)
    (hw : RoundsFinite F₁.unbounded rm₁ (z : ℝ) w) :
    RoundsFinite F₁.unbounded rm₁ ((x * y : Dyadic) : ℝ) w :=
  rndExact (mul_mem_F₂_unbounded hp₁ hp₂ hpp
    (by rw [hexp₁, hexp₂]; simp) hx hy) hz hw

/-- **rnd-mult, minimum quantum** (Roux Thm 10, radix 2). With `exp = emin`
formats
`F₁ = 𝒜(p₁, emin₁, b₁)` and `F₂ = 𝒜(p₂, emin₂, b₂)`, double rounding of `x · y`
(`x, y ∈ F₁`) is innocuous for **any** rounding modes when

* **precision:** `p₂ ≥ 2·p₁`,
* **exponent:** `emin₂ ≤ 2·emin₁`,
* **bounds:** no relationship required (overflow-free `unbounded` roundings).

*Containment view:* the exact product lives in `𝒜(2p₁, 2·emin₁, ⊤)` (precisions
double, minimum quanta add), and the two conditions say that product format
`⊆ F₂` — so `x · y` is exactly `F₂`-representable (`rndExact`). -/
theorem rndMul_expFinite {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode} {p₁ p₂ : ℕ}
    {emin₁ emin₂ : ℤ}
    (hp₁ : F₁.p = (p₁ : Prec)) (hp₂ : F₂.p = (p₂ : Prec))
    (hpp : 2 * p₁ ≤ p₂)
    (hexp₁ : F₁.exp = (emin₁ : QExp)) (hexp₂ : F₂.exp = (emin₂ : QExp))
    (hemin : emin₂ ≤ 2 * emin₁)
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁) {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded rm₂ ((x * y : Dyadic) : ℝ) z)
    (hw : RoundsFinite F₁.unbounded rm₁ (z : ℝ) w) :
    RoundsFinite F₁.unbounded rm₁ ((x * y : Dyadic) : ℝ) w :=
  rndExact (mul_mem_F₂_unbounded hp₁ hp₂ hpp
    (by rw [hexp₁, hexp₂, ← WithBot.coe_add]; exact_mod_cast (by omega : emin₂ ≤ emin₁ + emin₁))
    hx hy) hz hw

end Mpfx
