import Mpfx.Containment
import Mpfx.Digits

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
not exactly equal to `y`, the parity of `y` (in the `IsOdd F` sense) is odd:
parity is at precision `numDigits F.p F.exp y` and discriminated by `F.p` (odd
significand for `F.p ≥ 2`, odd exponent for `F.p = 1`). -/
def RoundsRTO (F : AbstractFormat) (x : ℝ) (y : Dyadic) : Prop :=
  y ∈ F ∧
  (RoundsDown F x y ∨ RoundsUp F x y) ∧
  (x ≠ (y : ℝ) → IsOdd F y)

/-- `y = RNE-rounding of x in F` — round to nearest, ties to even. The result
`y ∈ F` is one of the two adjacents bracketing `x`, chosen as the closer one;
ties (when `x` is exactly halfway between the two adjacents) are broken by
picking the value with `IsEven F` parity. -/
def RoundsRNE (F : AbstractFormat) (x : ℝ) (y : Dyadic) : Prop :=
  y ∈ F ∧
  (RoundsDown F x y ∨ RoundsUp F x y) ∧
  -- `y` is at least as close to `x` as any other adjacent
  (∀ z : Dyadic, z ∈ F → (RoundsDown F x z ∨ RoundsUp F x z) →
    |x - (y : ℝ)| ≤ |x - (z : ℝ)|) ∧
  -- Tie-break: if `x` is equidistant from `y` and another adjacent, `y` is even
  ((∃ z : Dyadic, z ∈ F ∧ (RoundsDown F x z ∨ RoundsUp F x z) ∧
      z ≠ y ∧ |x - (y : ℝ)| = |x - (z : ℝ)|) →
    IsEven F y)

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

/-- The RTO-rounding of `0` in any format is `0` itself. -/
theorem RoundsRTO.eq_zero_of_zero {F : AbstractFormat} {z : Dyadic}
    (h : RoundsRTO F 0 z) : z = 0 := by
  have h0 : RoundsRTO F (((0 : Dyadic) : ℝ)) z := by
    have : ((0 : Dyadic) : ℝ) = 0 := rfl
    rw [this]; exact h
  exact RoundsRTO.unique_of_mem F.zero_mem h0

/-- The RTO-rounding of a positive `x` is non-negative. -/
theorem RoundsRTO.nonneg_of_pos {F : AbstractFormat} {x : ℝ} {z : Dyadic}
    (hx_pos : 0 < x) (h : RoundsRTO F x z) : 0 ≤ (z : ℝ) := by
  rcases h.2.1 with hRD | hRU
  · obtain ⟨_, _, hz_max⟩ := hRD
    have := hz_max 0 F.zero_mem hx_pos.le
    simpa using this
  · linarith [hRU.2.1]

/-- **Lemma 5.3 (spec-form corollary)**: when `x` is unrepresentable in `F`
(`x ≠ x'`), the RTO-rounded `x'` cannot coincide with *any* dyadic `y` that is
representable at strictly lower precision than the rounding precision at `x'`.

The hypothesis `hgt : (w : ℤ) < numDigits F.p F.exp x'` captures "the rounding
precision (at `x'`) exceeds `w`". In typical applications, this follows from
the rounding precision at `x` (Lemma 5.1) plus a magnitude-bin invariant. -/
theorem RoundsRTO.ne_of_precisionAtMost {F : AbstractFormat} {w : ℕ}
    {x : ℝ} {x' : Dyadic} (hround : RoundsRTO F x x')
    (hxne : x ≠ (x' : ℝ))
    (hgt : (w : ℤ) < numDigits F.p F.exp (x' : ℝ))
    {y : Dyadic} (hy : Dyadic.precisionAtMost (w : ℕ∞) y) :
    (x' : ℝ) ≠ (y : ℝ) := by
  intro hxy
  have hxy_eq : x' = y := Subtype.ext hxy
  obtain ⟨_, _, hodd_imp⟩ := hround
  have h_odd : IsOdd F x' := hodd_imp hxne
  -- Transport hgt and h_odd along x' = y
  have hgt_y : (w : ℤ) < numDigits F.p F.exp (y : ℝ) := by rw [← hxy]; exact hgt
  have h_odd_y : IsOdd F y := by rw [← hxy_eq]; exact h_odd
  exact (precisionAtMost_not_IsOdd hgt_y hy) h_odd_y

/-- **Lemma 5.3, applied form**: if `RoundsRTO F₂ x z` (with `x ≠ z`), then `z`
cannot be representable in any format `F₁` whose effective precision at `z`
(per Lemma 5.1) is strictly less than `F₂`'s. This is the form used by every
double-rounding theorem to rule out the case "F₂'s rounded value lands on an
`F₁`-representable point". -/
theorem RoundsRTO.notMem_of_lower_numDigits {F₁ F₂ : AbstractFormat}
    {x : ℝ} {z : Dyadic} (hz : RoundsRTO F₂ x z)
    (hxne : x ≠ (z : ℝ))
    (hlt : numDigits F₁.p F₁.exp (z : ℝ) < numDigits F₂.p F₂.exp (z : ℝ)) :
    z ∉ F₁ := by
  intro hzF₁
  have h_prec : Dyadic.precisionAtMost
      (((numDigits F₁.p F₁.exp ((z : Dyadic) : ℝ)).toNat : ℕ) : ℕ∞) z :=
    mem_imp_precisionAtMost_numDigits hzF₁
  have h_iod : IsOdd F₂ z := hz.2.2 hxne
  have h_nd_F₂_pos : 0 < numDigits F₂.p F₂.exp ((z : Dyadic) : ℝ) :=
    h_iod.numDigits_pos
  have hcast : ((numDigits F₁.p F₁.exp ((z : Dyadic) : ℝ)).toNat : ℤ)
      < numDigits F₂.p F₂.exp ((z : Dyadic) : ℝ) := by
    rcases le_or_gt 0 (numDigits F₁.p F₁.exp ((z : Dyadic) : ℝ)) with h | h
    · rw [Int.toNat_of_nonneg h]; exact hlt
    · rw [Int.toNat_of_nonpos (le_of_lt h)]
      push_cast; exact h_nd_F₂_pos
  exact (RoundsRTO.ne_of_precisionAtMost hz hxne hcast h_prec) rfl

/-- Paper-aligned form of Lemma 5.3. From `F₁.extend 1 ⊆ F₂` and an RTO
rounding `z` with `x ≠ z` (so `IsOdd F₂ z`), conclude `z ∉ F₁`.

Proof: `z ∈ F₁ ⊆ F₁.extend 1`. By `numDigits_eq_of_subset_of_isOdd`,
`numDigits (F₁.extend 1) z = numDigits F₂ z`. By `numDigits_extend`, the LHS
equals `numDigits F₁ z + 1`. So `numDigits F₁ z + 1 = numDigits F₂ z`, i.e.,
`numDigits F₁ z < numDigits F₂ z`. Then apply `notMem_of_lower_numDigits`. -/
theorem RoundsRTO.notMem_of_extend_subset {F₁ F₂ : AbstractFormat}
    (hsub : F₁.extend 1 ⊆ F₂)
    (hp_F₂ : 2 ≤ F₂.p)
    {x : ℝ} {z : Dyadic} (hz : RoundsRTO F₂ x z)
    (hxne : x ≠ (z : ℝ)) :
    z ∉ F₁ := by
  intro hzF₁
  have h_iod : IsOdd F₂ z := hz.2.2 hxne
  have hz_ne_zero : ((z : Dyadic) : ℝ) ≠ 0 := by
    intro h
    have hz_d : z = 0 := Subtype.ext (by rw [h]; rfl)
    rw [hz_d] at h_iod
    exact h_iod.ne_zero rfl
  -- z ∈ F₁ ⇒ z ∈ F₁.extend 1 (precision/quantum constraints weaken).
  have hzF₁_ext : z ∈ F₁.extend 1 := by
    obtain ⟨hp, hq, hb⟩ := hzF₁
    refine ⟨?_, ?_, ?_⟩
    · have h_p_le : F₁.p ≤ F₁.p + 1 := by
        cases F₁.p with
        | top => simp
        | coe n => exact WithTop.coe_le_coe.mpr (Nat.le_succ n)
      change Dyadic.precisionAtMost _ z
      exact Dyadic.precisionAtMost_mono h_p_le hp
    · change Dyadic.quantumAtLeast _ z
      have h_exp_ge : (F₁.exp.map (· - (1 : ℤ))) ≤ F₁.exp := by
        cases F₁.exp with
        | bot => simp
        | coe e =>
          change ((e - 1 : ℤ) : WithBot ℤ) ≤ ((e : ℤ) : WithBot ℤ)
          exact WithBot.coe_le_coe.mpr (by linarith)
      exact Dyadic.quantumAtLeast_anti h_exp_ge hq
    · exact hb
  -- Apply Lemma 5.3 corollary at F₁.extend 1 ⊆ F₂.
  have h_eq : numDigits (F₁.extend 1).p (F₁.extend 1).exp (z : ℝ) =
              numDigits F₂.p F₂.exp (z : ℝ) :=
    numDigits_eq_of_subset_of_isOdd hsub hp_F₂ hzF₁_ext h_iod
  rw [numDigits_extend F₁ 1 hz_ne_zero] at h_eq
  -- h_eq : numDigits F₁ z + 1 = numDigits F₂ z
  -- Convert to the strict shift and apply notMem_of_lower_numDigits.
  have h_F₂_pos : 0 < numDigits F₂.p F₂.exp (z : ℝ) := h_iod.numDigits_pos
  have h_lt : numDigits F₁.p F₁.exp (z : ℝ) < numDigits F₂.p F₂.exp (z : ℝ) := by
    omega
  exact (RoundsRTO.notMem_of_lower_numDigits hz hxne h_lt) hzF₁

/-- Sign-flip symmetry for RTZ rounding. -/
theorem RoundsRTZ.neg {F : AbstractFormat} {x : ℝ} {y : Dyadic}
    (h : RoundsRTZ F x y) : RoundsRTZ F (-x) (-y) := by
  obtain ⟨hyF, hbnd, hsign, hmax⟩ := h
  refine ⟨neg_mem hyF, ?_, ?_, ?_⟩
  · change |((-y : Dyadic) : ℝ)| ≤ |(-x)|
    push_cast
    rw [abs_neg, abs_neg]
    exact hbnd
  · change ((-y : Dyadic) : ℝ) * (-x) ≥ 0
    push_cast
    have : -(y : ℝ) * -x = (y : ℝ) * x := by ring
    rw [this]
    exact hsign
  · intro z hzF hzbnd hzsign
    rw [abs_neg] at hzbnd
    have hnz : (-z) ∈ F := neg_mem hzF
    have h1 : |((-z : Dyadic) : ℝ)| ≤ |x| := by push_cast; rw [abs_neg]; exact hzbnd
    have h2 : 0 ≤ ((-z : Dyadic) : ℝ) * x := by
      push_cast
      have hzs : 0 ≤ (z : ℝ) * (-x) := hzsign
      linarith
    have key := hmax (-z) hnz h1 h2
    have habs1 : |((-z : Dyadic) : ℝ)| = |(z : ℝ)| := by push_cast; rw [abs_neg]
    have habs2 : |((-y : Dyadic) : ℝ)| = |(y : ℝ)| := by push_cast; rw [abs_neg]
    rw [habs1] at key
    rw [habs2]
    exact key

/-- Sign-flip symmetry for RTO rounding. -/
theorem RoundsRTO.neg {F : AbstractFormat} {x : ℝ} {y : Dyadic}
    (h : RoundsRTO F x y) : RoundsRTO F (-x) (-y) := by
  obtain ⟨hyF, hadj, hodd_imp⟩ := h
  refine ⟨neg_mem hyF, ?_, ?_⟩
  · -- RoundsDown ↔ RoundsUp under negation
    rcases hadj with hRD | hRU
    · right
      obtain ⟨_, hyx, hmax⟩ := hRD
      refine ⟨neg_mem hyF, ?_, ?_⟩
      · push_cast; linarith
      · intro z hzF hxz
        push_cast
        have hnzF : (-z) ∈ F := neg_mem hzF
        have h1 : ((-z : Dyadic) : ℝ) ≤ x := by push_cast; linarith
        have key := hmax (-z) hnzF h1
        push_cast at key; linarith
    · left
      obtain ⟨_, hxy, hmin⟩ := hRU
      refine ⟨neg_mem hyF, ?_, ?_⟩
      · push_cast; linarith
      · intro z hzF hzx
        push_cast
        have hnzF : (-z) ∈ F := neg_mem hzF
        have h1 : x ≤ ((-z : Dyadic) : ℝ) := by push_cast; linarith
        have key := hmin (-z) hnzF h1
        push_cast at key; linarith
  · intro hxne
    have hxne' : x ≠ (y : ℝ) := by
      intro h_eq
      apply hxne
      rw [h_eq]; push_cast; rfl
    exact (hodd_imp hxne').neg

/-- `RoundsDown ∨ RoundsUp` is preserved (with the disjuncts flipped) under
joint negation of `x` and `y`. Used by `RoundsRTO.neg` and `RoundsRNE.neg`. -/
theorem roundsAdj_neg {F : AbstractFormat} {a : ℝ} {b : Dyadic}
    (h : RoundsDown F a b ∨ RoundsUp F a b) :
    RoundsDown F (-a) (-b) ∨ RoundsUp F (-a) (-b) := by
  rcases h with hRD | hRU
  · right
    obtain ⟨hbF, hba, hmax⟩ := hRD
    refine ⟨neg_mem hbF, ?_, ?_⟩
    · push_cast; linarith
    · intro w hwF haw
      have hnwF : (-w) ∈ F := neg_mem hwF
      have h1 : ((-w : Dyadic) : ℝ) ≤ a := by push_cast; linarith
      have key := hmax (-w) hnwF h1
      push_cast at key ⊢; linarith
  · left
    obtain ⟨hbF, hab, hmin⟩ := hRU
    refine ⟨neg_mem hbF, ?_, ?_⟩
    · push_cast; linarith
    · intro w hwF hwa
      have hnwF : (-w) ∈ F := neg_mem hwF
      have h1 : a ≤ ((-w : Dyadic) : ℝ) := by push_cast; linarith
      have key := hmin (-w) hnwF h1
      push_cast at key ⊢; linarith

/-- Sign-flip symmetry for RAZ rounding: rounding `x` to `y` under RAZ in `F`
is equivalent to rounding `-x` to `-y`. Uses `neg_mem` (every format is closed
under negation). -/
theorem RoundsRAZ.neg {F : AbstractFormat} {x : ℝ} {y : Dyadic}
    (h : RoundsRAZ F x y) : RoundsRAZ F (-x) (-y) := by
  obtain ⟨hyF, hbnd, hsign, hmin⟩ := h
  refine ⟨neg_mem hyF, ?_, ?_, ?_⟩
  · change |(-x)| ≤ |((-y : Dyadic) : ℝ)|
    push_cast
    rw [abs_neg, abs_neg]
    exact hbnd
  · change ((-y : Dyadic) : ℝ) * (-x) ≥ 0
    push_cast
    have : -(y : ℝ) * -x = (y : ℝ) * x := by ring
    rw [this]
    exact hsign
  · intro z hzF hzbnd hzsign
    rw [abs_neg] at hzbnd
    have hnz : (-z) ∈ F := neg_mem hzF
    have h1 : |x| ≤ |((-z : Dyadic) : ℝ)| := by
      push_cast; rw [abs_neg]; exact hzbnd
    have h2 : 0 ≤ ((-z : Dyadic) : ℝ) * x := by
      push_cast
      have hzs : 0 ≤ (z : ℝ) * (-x) := hzsign
      linarith
    have key := hmin (-z) hnz h1 h2
    change |((-y : Dyadic) : ℝ)| ≤ |(z : ℝ)|
    push_cast
    rw [abs_neg]
    have hyz : |(y : ℝ)| ≤ |((-z : Dyadic) : ℝ)| := key
    rwa [show |((-z : Dyadic) : ℝ)| = |(z : ℝ)| from by push_cast; rw [abs_neg]] at hyz

/-- Sign-flip symmetry for RNE rounding. -/
theorem RoundsRNE.neg {F : AbstractFormat} {x : ℝ} {y : Dyadic}
    (h : RoundsRNE F x y) : RoundsRNE F (-x) (-y) := by
  obtain ⟨hyF, hadj, hclose, htie⟩ := h
  -- Distance identities used several times.
  have eq1 : ∀ (w : Dyadic),
      |x - ((-w : Dyadic) : ℝ)| = |(-x) - (w : ℝ)| := by
    intro w
    push_cast
    rw [show x - -(w : ℝ) = -((-x) - (w : ℝ)) from by ring, abs_neg]
  have eq2 : |x - (y : ℝ)| = |(-x) - ((-y : Dyadic) : ℝ)| := by
    push_cast
    rw [show x - (y : ℝ) = -((-x) - -(y : ℝ)) from by ring, abs_neg]
  refine ⟨neg_mem hyF, roundsAdj_neg hadj, ?_, ?_⟩
  · -- closeness: every adjacent of (-x) corresponds to its negation as adjacent of x
    intro z hzF hzadj
    have hnzF : (-z) ∈ F := neg_mem hzF
    have hnzadj : RoundsDown F x (-z) ∨ RoundsUp F x (-z) := by
      have := roundsAdj_neg hzadj
      simpa using this
    have key := hclose (-z) hnzF hnzadj
    rw [eq1 z] at key
    rw [← eq2]
    exact key
  · -- tie-break: a tie at (-x, -y) yields a tie at (x, y); apply IsEven.neg
    rintro ⟨z, hzF, hzadj, hzne, hzdist⟩
    have hnzF : (-z) ∈ F := neg_mem hzF
    have hnzadj : RoundsDown F x (-z) ∨ RoundsUp F x (-z) := by
      have := roundsAdj_neg hzadj
      simpa using this
    have hnzne : (-z) ≠ y := by
      intro h_eq
      apply hzne
      have h2 : -(-z) = -y := by rw [h_eq]
      rwa [neg_neg] at h2
    have hnzdist : |x - (y : ℝ)| = |x - ((-z : Dyadic) : ℝ)| := by
      rw [eq2, eq1 z]; exact hzdist
    exact (htie ⟨-z, hnzF, hnzadj, hnzne, hnzdist⟩).neg

end AbstractFormat

end Mpfx
