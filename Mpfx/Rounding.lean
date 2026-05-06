import Mpfx.Containment

/-!
# Rounding modes and the rounding function

§3.2 of the paper defines five IEEE 754 rounding modes plus two extras (RAZ, RTO).
For our analysis (§5.2) we focus on `RTZ`, `RAZ`, `RTO`, and `RNE`, since RTP/RTN
collapse to RAZ/RTZ depending on sign and RNA differs from RNE only in tiebreaking.
-/

namespace Mpfx

/-- Rounding modes covered by Fig. 9 of the paper:

* `RTZ` — round towards zero (truncate).
* `RAZ` — round away from zero.
* `RTO` — round to odd: pick the value with odd significand.
* `RNE` — round to nearest, ties to even.
-/
inductive RoundingMode
  | RTZ : RoundingMode
  | RAZ : RoundingMode
  | RTO : RoundingMode
  | RNE : RoundingMode
deriving DecidableEq, Repr

namespace AbstractFormat

/-- `y = round-down of x in F` — i.e., `y` is the largest element of `F` with
`(y : ℝ) ≤ x`. This is the building block for `RTZ` (when `x ≥ 0`) and
`RTN`. -/
def RoundsDown (F : AbstractFormat) (x : ℝ) (y : Dyadic) : Prop :=
  y ∈ F ∧ (y : ℝ) ≤ x ∧ ∀ z : Dyadic, z ∈ F → (z : ℝ) ≤ x → (z : ℝ) ≤ (y : ℝ)

/-- `y = round-up of x in F` — i.e., `y` is the smallest element of `F` with
`x ≤ (y : ℝ)`. -/
def RoundsUp (F : AbstractFormat) (x : ℝ) (y : Dyadic) : Prop :=
  y ∈ F ∧ x ≤ (y : ℝ) ∧ ∀ z : Dyadic, z ∈ F → x ≤ (z : ℝ) → (y : ℝ) ≤ (z : ℝ)

/-- `y = RTZ-rounding of x in F` — round towards zero. For `x ≥ 0` this is
round-down to a non-negative element; for `x ≤ 0` it is round-up to a
non-positive element. -/
def RoundsRTZ (F : AbstractFormat) (x : ℝ) (y : Dyadic) : Prop :=
  y ∈ F ∧ |(y : ℝ)| ≤ |x| ∧ (y : ℝ) * x ≥ 0 ∧
  ∀ z : Dyadic, z ∈ F → |(z : ℝ)| ≤ |x| → (z : ℝ) * x ≥ 0 → |(z : ℝ)| ≤ |(y : ℝ)|

/-- `y = RAZ-rounding of x in F` — round away from zero. -/
def RoundsRAZ (F : AbstractFormat) (x : ℝ) (y : Dyadic) : Prop :=
  y ∈ F ∧ |x| ≤ |(y : ℝ)| ∧ (y : ℝ) * x ≥ 0 ∧
  ∀ z : Dyadic, z ∈ F → |x| ≤ |(z : ℝ)| → (z : ℝ) * x ≥ 0 → |(y : ℝ)| ≤ |(z : ℝ)|

/-- Composition lemma for round-down: if `F₁ ⊆ F₂`, then rounding down through
`F₂` to `F₁` agrees with rounding down directly to `F₁`. -/
theorem RoundsDown.compose {F₁ F₂ : AbstractFormat} (hsub : F₁ ⊆ F₂)
    {x : ℝ} {z w : Dyadic} (hz : RoundsDown F₂ x z) (hw : RoundsDown F₁ (z : ℝ) w) :
    RoundsDown F₁ x w := by
  obtain ⟨hzF, hzx, hz_max⟩ := hz
  obtain ⟨hwF, hwz, hw_max⟩ := hw
  refine ⟨hwF, le_trans hwz hzx, ?_⟩
  intro y hyF₁ hyx
  have hyF₂ : y ∈ F₂ := hsub y hyF₁
  have hyz : (y : ℝ) ≤ (z : ℝ) := hz_max y hyF₂ hyx
  exact hw_max y hyF₁ hyz

/-- Composition lemma for round-up: if `F₁ ⊆ F₂`, then rounding up through
`F₂` to `F₁` agrees with rounding up directly to `F₁`. -/
theorem RoundsUp.compose {F₁ F₂ : AbstractFormat} (hsub : F₁ ⊆ F₂)
    {x : ℝ} {z w : Dyadic} (hz : RoundsUp F₂ x z) (hw : RoundsUp F₁ (z : ℝ) w) :
    RoundsUp F₁ x w := by
  obtain ⟨hzF, hxz, hz_min⟩ := hz
  obtain ⟨hwF, hzw, hw_min⟩ := hw
  refine ⟨hwF, le_trans hxz hzw, ?_⟩
  intro y hyF₁ hxy
  have hyF₂ : y ∈ F₂ := hsub y hyF₁
  have hzy : (z : ℝ) ≤ (y : ℝ) := hz_min y hyF₂ hxy
  exact hw_min y hyF₁ hzy

/-- `y = RTO-rounding of x in F` — round to odd. The result `y ∈ F` is either
the round-down (`RoundsDown`) or round-up (`RoundsUp`) of `x`, and when `x` is
not exactly equal to `y`, the significand `c` of `y` at `F.p` bits is odd
(see `Dyadic.IsOddAtP`).

For unrepresentable `x`, this picks the adjacent representable value with odd
`p`-bit significand; for representable `x`, it returns `x` itself. -/
def RoundsRTO (F : AbstractFormat) (x : ℝ) (y : Dyadic) : Prop :=
  y ∈ F ∧
  (RoundsDown F x y ∨ RoundsUp F x y) ∧
  (x ≠ (y : ℝ) → ∃ p : ℕ, F.p = (p : ℕ∞) ∧ Dyadic.IsOddAtP p y)

/-- For `x ∈ F`, the RTO rounding is `x` itself. -/
theorem RoundsRTO.of_mem {F : AbstractFormat} {x : Dyadic} (hx : x ∈ F) :
    RoundsRTO F (x : ℝ) x := by
  refine ⟨hx, Or.inl ?_, ?_⟩
  · refine ⟨hx, le_refl _, ?_⟩
    intro z _ hzx
    exact hzx
  · intro hne
    exact absurd rfl hne

/-- If `x ∈ F` and `y` is the RTO-rounding of `x` in `F`, then `y = x`. -/
theorem RoundsRTO.unique_of_mem {F : AbstractFormat} {x : Dyadic} (hx : x ∈ F)
    {y : Dyadic} (h : RoundsRTO F (x : ℝ) y) : y = x := by
  obtain ⟨_, hadj, _⟩ := h
  rcases hadj with ⟨_, hyx, hmax⟩ | ⟨_, hxy, hmin⟩
  · -- RoundsDown: (y:ℝ) ≤ (x:ℝ) and y is largest such
    have hxy : (x : ℝ) ≤ (y : ℝ) := hmax x hx (le_refl _)
    have heq : (y : ℝ) = (x : ℝ) := le_antisymm hyx hxy
    exact Subtype.ext heq
  · -- RoundsUp: (x:ℝ) ≤ (y:ℝ) and y is smallest such
    have hyx : (y : ℝ) ≤ (x : ℝ) := hmin x hx (le_refl _)
    have heq : (y : ℝ) = (x : ℝ) := le_antisymm hyx hxy
    exact Subtype.ext heq

/-- **Lemma 5.3 (spec-form corollary)**: when `x` is unrepresentable in `F`
(`x ≠ x'`), the RTO-rounded `x'` (at format precision `w + k`) cannot coincide
with *any* dyadic `y` representable at the strictly lower precision `w`.

This is the directly useful form of the paper's Lemma 5.3 in our spec
framework. It says: "RTO at `w + k` bits dodges every precision-`w` value" — so
in particular, `x'` lies strictly between the precision-`w` adjacents of `x`. -/
theorem RoundsRTO.ne_of_precisionAtMost {F : AbstractFormat} {w k : ℕ}
    (hp : F.p = ((w + k) : ℕ∞)) (hk : 1 ≤ k)
    {x : ℝ} {x' : Dyadic} (hround : RoundsRTO F x x')
    (hxne : x ≠ (x' : ℝ))
    {y : Dyadic} (hy : Dyadic.precisionAtMost (w : ℕ∞) y) :
    (x' : ℝ) ≠ (y : ℝ) := by
  intro hxy
  have hxy_eq : x' = y := Subtype.ext hxy
  obtain ⟨_, _, hodd_imp⟩ := hround
  obtain ⟨p, hpx, hodd⟩ := hodd_imp hxne
  rw [hp] at hpx
  have hp_eq : p = w + k := by exact_mod_cast hpx.symm
  rw [hp_eq, hxy_eq] at hodd
  exact (Dyadic.precisionAtMost_not_isOddAtP hk hy) hodd

end AbstractFormat

end Mpfx
