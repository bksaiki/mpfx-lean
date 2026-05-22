import Mpfx.Format
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log

/-!
# Format inference for unrounded operations (Section 6.1 of the paper)

Section 6.1 of *When Double Rounding is Correct* introduces **format
inference**: a static analysis bounding the possible values of each
subexpression by the smallest `AbstractFormat` containing them.  For
unrounded operations, the paper states:

* `neg` and `abs` preserve the format.
* `mul`: `𝒜(p₁, exp₁, b₁) ⊗ 𝒜(p₂, exp₂, b₂) ⊆
          𝒜(p₁ + p₂, exp₁ + exp₂, b₁ × b₂)`.
* `add`: `𝒜(p₁, exp₁, b₁) ⊕ 𝒜(p₂, exp₂, b₂) ⊆
          𝒜(⌈log₂((b₁+b₂)/2^min(exp₁,exp₂) + 1)⌉, min(exp₁, exp₂), b₁ + b₂)`.

## Top-level statements vs. the paper

The public API of this file mirrors the paper:

| Paper (§6.1)               | Lean (this file)                                         |
|----------------------------|----------------------------------------------------------|
| `-A ⊆ A`                   | `neg_subset : -F.toSet ⊆ F.toSet`                       |
| `|A| ⊆ A`                  | `abs_subset : Dyadic.abs '' F.toSet ⊆ F.toSet`          |
| `A ⊗ B ⊆ 𝒜(p₁+p₂, …)`     | `mul_subset : F₁.toSet * F₂.toSet ⊆ (opMul F₁ F₂ _ _).toSet` |
| `A ⊕ B ⊆ 𝒜(⌈log₂…⌉, …)`   | `add_subset : F₁.toSet + F₂.toSet ⊆ (opAdd F₁ F₂ _ _).toSet` |

One intentional deviation from the paper:

**Validity hypothesis on `opMul` and `opAdd`.** Returning an
`AbstractFormat` requires its `not_degenerate` invariant
`(p ≠ ⊤ ∧ p ≠ 1) ∨ exp ≠ ⊥` to hold.  The literal `(p₁+p₂, exp₁+exp₂, …)`
tuple can violate this in edge cases (e.g., `F₁.p = ⊤` forces `F₁.exp`
finite, but `F₂.exp = ⊥` is allowed if `F₂.p` is finite ≥ 2 — then the sum
is `(⊤, ⊥, …)`, degenerate).  We rule this out by requiring
`F₁.exp ≠ ⊥` and `F₂.exp ≠ ⊥` in the hypothesis of `opMul`/`opAdd`.  The
paper doesn't state such a precondition; our formalization makes it
explicit so the inferred bounding format is itself a valid
`AbstractFormat`.

For the `⊕`-precision we use a *slightly tighter* formula than the paper:
`opAddPrec` returns `⌈log₂(⌊(b₁+b₂)/2^min(exp₁,exp₂)⌋ + 1)⌉` (floor inside),
matching the actual integer bound on `|c|` rather than the paper's
real-arithmetic `⌈log₂(N + 1)⌉` (which over-allocates by 1 bit when
`(b₁+b₂)/2^m` is non-integer).  For practical formats where the bound `b`
aligns with the exponent — `binary64`, fixed-point, etc. — the two
formulas agree; ours just doesn't waste a bit in misaligned edge cases.
-/

namespace Mpfx

namespace Dyadic

/-- Absolute value of a dyadic, as a dyadic.  Equal to `x` if `0 ≤ x`,
otherwise `-x`.  Lives in `Dyadic` because the underlying subring is closed
under negation. -/
noncomputable def abs (x : Dyadic) : Dyadic :=
  if 0 ≤ (x : ℝ) then x else -x

@[simp] theorem coe_abs (x : Dyadic) : (Dyadic.abs x : ℝ) = |(x : ℝ)| := by
  unfold Dyadic.abs
  by_cases h : 0 ≤ (x : ℝ)
  · rw [if_pos h]; exact (_root_.abs_of_nonneg h).symm
  · rw [if_neg h]
    push_cast
    rw [_root_.abs_of_neg (lt_of_not_ge h)]

end Dyadic

namespace AbstractFormat

/-! ## `abs` preserves format

`neg_mem` is already in `Mpfx.Format`; the `abs` analog follows from `neg_mem`
plus the two-case definition of `Dyadic.abs`. -/

/-- `Dyadic.abs x ∈ F` whenever `x ∈ F`. -/
theorem abs_mem {F : AbstractFormat} {x : Dyadic} (hx : x ∈ F) :
    Dyadic.abs x ∈ F := by
  unfold Dyadic.abs
  by_cases h : 0 ≤ (x : ℝ)
  · rw [if_pos h]; exact hx
  · rw [if_neg h]; exact neg_mem hx

/-! ## Predicate-level helpers (private)

The two `_inferred` helpers below establish, at the predicate level, that
every product / sum of representables satisfies the inferred format's
membership predicates.  They're stated without the `not_degenerate`
validity hypothesis so they're more general (they don't need to construct
an `AbstractFormat`).  The public `mul_subset` / `add_subset` theorems
below specialize them to the `⊆`-form. -/

/-- For `x ∈ F₁, y ∈ F₂`, the product `x · y` satisfies the inferred
multiplicative parameters (precision sum, quantum sum, bound product). -/
private theorem mul_inferred {F₁ F₂ : AbstractFormat} {x y : Dyadic}
    (hx : x ∈ F₁) (hy : y ∈ F₂) :
    Dyadic.precisionAtMost (F₁.p + F₂.p) (x * y) ∧
    Dyadic.quantumAtLeast (F₁.exp + F₂.exp) (x * y) ∧
    (∀ d₁ d₂ : Dyadic, F₁.b = (d₁ : WithTop Dyadic) → F₂.b = (d₂ : WithTop Dyadic) →
        |((x * y : Dyadic) : ℝ)| ≤ ((d₁ * d₂ : Dyadic) : ℝ)) := by
  obtain ⟨hpx, hqx, hbx⟩ := hx
  obtain ⟨hpy, hqy, hby⟩ := hy
  refine ⟨?_, ?_, ?_⟩
  · -- precisionAtMost (p₁ + p₂) (x * y)
    by_cases hF1_p : F₁.p = ⊤
    · have : F₁.p + F₂.p = (⊤ : ℕ∞) := by rw [hF1_p]; rfl
      rw [this]; trivial
    by_cases hF2_p : F₂.p = ⊤
    · have : F₁.p + F₂.p = (⊤ : ℕ∞) := by rw [hF2_p]; cases F₁.p <;> rfl
      rw [this]; trivial
    obtain ⟨p1, hp1⟩ := WithTop.ne_top_iff_exists.mp hF1_p
    obtain ⟨p2, hp2⟩ := WithTop.ne_top_iff_exists.mp hF2_p
    rw [← hp1] at hpx
    rw [← hp2] at hpy
    obtain ⟨c1, e1, hxeq, hc1⟩ := hpx
    obtain ⟨c2, e2, hyeq, hc2⟩ := hpy
    have h_p_eq : F₁.p + F₂.p = ((p1 + p2 : ℕ) : ℕ∞) := by
      rw [← hp1, ← hp2]; push_cast; rfl
    rw [h_p_eq]
    refine ⟨c1 * c2, e1 + e2, ?_, ?_⟩
    · change ((x * y : Dyadic) : ℝ) = _
      push_cast
      rw [hxeq, hyeq, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      ring
    · rw [abs_mul, pow_add]
      exact mul_lt_mul'' hc1 hc2 (abs_nonneg _) (abs_nonneg _)
  · -- quantumAtLeast (exp₁ + exp₂) (x * y)
    by_cases hF1_exp : F₁.exp = ⊥
    · have : F₁.exp + F₂.exp = (⊥ : WithBot ℤ) := by rw [hF1_exp]; rfl
      rw [this]; trivial
    by_cases hF2_exp : F₂.exp = ⊥
    · have : F₁.exp + F₂.exp = (⊥ : WithBot ℤ) := by rw [hF2_exp]; cases F₁.exp <;> rfl
      rw [this]; trivial
    obtain ⟨e1, he1⟩ := WithBot.ne_bot_iff_exists.mp hF1_exp
    obtain ⟨e2, he2⟩ := WithBot.ne_bot_iff_exists.mp hF2_exp
    have hqx' : Dyadic.quantumAtLeast (e1 : WithBot ℤ) x := by rw [he1]; exact hqx
    have hqy' : Dyadic.quantumAtLeast (e2 : WithBot ℤ) y := by rw [he2]; exact hqy
    obtain ⟨c1, hxeq⟩ := hqx'
    obtain ⟨c2, hyeq⟩ := hqy'
    have h_exp_eq : F₁.exp + F₂.exp = ((e1 + e2 : ℤ) : WithBot ℤ) := by
      rw [← he1, ← he2]; push_cast; rfl
    rw [h_exp_eq]
    refine ⟨c1 * c2, ?_⟩
    change ((x * y : Dyadic) : ℝ) = _
    push_cast
    rw [hxeq, hyeq, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  · -- bound: |x*y| ≤ d₁ · d₂ when both finite.
    intro d1 d2 hF1_b hF2_b
    rw [hF1_b] at hbx
    rw [hF2_b] at hby
    change |(x : ℝ)| ≤ ((d1 : Dyadic) : ℝ) at hbx
    change |(y : ℝ)| ≤ ((d2 : Dyadic) : ℝ) at hby
    have hd1_nn : 0 ≤ ((d1 : Dyadic) : ℝ) := F₁.b_nn_of_coe hF1_b
    push_cast
    rw [abs_mul]
    exact mul_le_mul hbx hby (abs_nonneg _) hd1_nn

/-- For `x ∈ F₁, y ∈ F₂`, the sum `x + y` satisfies the inferred additive
parameters: quantum is `min(exp₁, exp₂)`, bound is `b₁ + b₂`.  (Precision
is left as `⊤`; see this file's doc-block.) -/
private theorem add_inferred {F₁ F₂ : AbstractFormat} {x y : Dyadic}
    (hx : x ∈ F₁) (hy : y ∈ F₂) :
    Dyadic.quantumAtLeast (min F₁.exp F₂.exp) (x + y) ∧
    (∀ d₁ d₂ : Dyadic, F₁.b = (d₁ : WithTop Dyadic) → F₂.b = (d₂ : WithTop Dyadic) →
        |((x + y : Dyadic) : ℝ)| ≤ ((d₁ + d₂ : Dyadic) : ℝ)) := by
  obtain ⟨_, hqx, hbx⟩ := hx
  obtain ⟨_, hqy, hby⟩ := hy
  refine ⟨?_, ?_⟩
  · -- quantumAtLeast (min F₁.exp F₂.exp) (x + y).
    by_cases hF1_exp : F₁.exp = ⊥
    · have : min F₁.exp F₂.exp = (⊥ : WithBot ℤ) := by
        rw [hF1_exp]; exact min_eq_left bot_le
      rw [this]; trivial
    by_cases hF2_exp : F₂.exp = ⊥
    · have : min F₁.exp F₂.exp = (⊥ : WithBot ℤ) := by
        rw [hF2_exp]; exact min_eq_right bot_le
      rw [this]; trivial
    obtain ⟨e1, he1⟩ := WithBot.ne_bot_iff_exists.mp hF1_exp
    obtain ⟨e2, he2⟩ := WithBot.ne_bot_iff_exists.mp hF2_exp
    have hqx' : Dyadic.quantumAtLeast (e1 : WithBot ℤ) x := by rw [he1]; exact hqx
    have hqy' : Dyadic.quantumAtLeast (e2 : WithBot ℤ) y := by rw [he2]; exact hqy
    obtain ⟨c1, hxeq⟩ := hqx'
    obtain ⟨c2, hyeq⟩ := hqy'
    have h_min_eq : min F₁.exp F₂.exp = ((min e1 e2 : ℤ) : WithBot ℤ) := by
      rw [← he1, ← he2]
      rcases le_total e1 e2 with hle | hle
      · rw [min_eq_left (by exact_mod_cast hle : (e1 : WithBot ℤ) ≤ (e2 : WithBot ℤ))]
        rw [min_eq_left hle]
      · rw [min_eq_right (by exact_mod_cast hle : (e2 : WithBot ℤ) ≤ (e1 : WithBot ℤ))]
        rw [min_eq_right hle]
    rw [h_min_eq]
    set m := min e1 e2 with hm
    have he1_ge : m ≤ e1 := min_le_left _ _
    have he2_ge : m ≤ e2 := min_le_right _ _
    refine ⟨c1 * 2 ^ (e1 - m).toNat + c2 * 2 ^ (e2 - m).toNat, ?_⟩
    change ((x + y : Dyadic) : ℝ) = _
    push_cast
    rw [hxeq, hyeq]
    rw [two_zpow_split_toNat he1_ge, two_zpow_split_toNat he2_ge]
    ring
  · -- bound: |x+y| ≤ d₁ + d₂ when both finite.
    intro d1 d2 hF1_b hF2_b
    rw [hF1_b] at hbx
    rw [hF2_b] at hby
    change |(x : ℝ)| ≤ ((d1 : Dyadic) : ℝ) at hbx
    change |(y : ℝ)| ≤ ((d2 : Dyadic) : ℝ) at hby
    push_cast
    calc |(x : ℝ) + (y : ℝ)|
        ≤ |(x : ℝ)| + |(y : ℝ)| := abs_add_le _ _
      _ ≤ ((d1 : Dyadic) : ℝ) + ((d2 : Dyadic) : ℝ) := add_le_add hbx hby

/-! ## Public `⊆`-level API (paper's notation)

This is the layer that downstream users should interact with.  Each
theorem here mirrors the paper's `⊆` form between formats. -/

open scoped Pointwise

/-- Coerce an `AbstractFormat` to its underlying set of representable
Dyadics.  Used to express `⊆` between formats at the `Set Dyadic` level. -/
def toSet (F : AbstractFormat) : Set Dyadic := {x | x ∈ F}

@[simp] theorem mem_toSet {F : AbstractFormat} {x : Dyadic} :
    x ∈ F.toSet ↔ x ∈ F := Iff.rfl

/-- Paper's `⊗`: multiplicative format inference.  Returns
`𝒜(p₁ + p₂, exp₁ + exp₂, b₁ × b₂)`.  The `F.exp ≠ ⊥` hypotheses ensure
the result satisfies `not_degenerate`. -/
noncomputable def opMul (F₁ F₂ : AbstractFormat)
    (h₁ : F₁.exp ≠ ⊥) (h₂ : F₂.exp ≠ ⊥) : AbstractFormat where
  p := F₁.p + F₂.p
  exp := F₁.exp + F₂.exp
  b := F₁.b * F₂.b
  p_pos := by
    calc (1 : ℕ∞) ≤ 1 + 1 := by norm_num
      _ ≤ F₁.p + F₂.p := add_le_add F₁.p_pos F₂.p_pos
  not_degenerate := by
    refine Or.inr ?_
    obtain ⟨e₁, he₁⟩ := WithBot.ne_bot_iff_exists.mp h₁
    obtain ⟨e₂, he₂⟩ := WithBot.ne_bot_iff_exists.mp h₂
    have : F₁.exp + F₂.exp = ((e₁ + e₂ : ℤ) : WithBot ℤ) := by
      rw [← he₁, ← he₂]; push_cast; rfl
    rw [this]
    exact WithBot.coe_ne_bot
  b_nn := by
    cases hF1_b : F₁.b with
    | top => cases hF2_b : F₂.b with
      | top => simp
      | coe d2 =>
        by_cases hd2_zero : (d2 : Dyadic) = 0
        · rw [hd2_zero, WithTop.coe_zero, mul_zero]
        · rw [WithTop.top_mul (by exact_mod_cast hd2_zero)]; exact le_top
    | coe d1 => cases hF2_b : F₂.b with
      | top =>
        by_cases hd1_zero : (d1 : Dyadic) = 0
        · rw [hd1_zero, WithTop.coe_zero, zero_mul]
        · rw [WithTop.mul_top (by exact_mod_cast hd1_zero)]; exact le_top
      | coe d2 =>
        rw [← WithTop.coe_mul]
        refine WithTop.coe_le_coe.mpr ?_
        change (0 : ℝ) ≤ ((d1 * d2 : Dyadic) : ℝ)
        push_cast
        exact mul_nonneg (F₁.b_nn_of_coe hF1_b) (F₂.b_nn_of_coe hF2_b)

/-- Tight precision bound for `⊕`, slightly sharper than the paper's:
`p = ⌈log₂(⌊(b₁+b₂)/2^min(exp₁,exp₂)⌋ + 1)⌉`.  The paper writes the formula
with `⌈⌉` instead of `⌊⌋` (matching `⌈log₂(N + 1)⌉` in real arithmetic);
since `|c|` is an integer with `|c| ≤ (b₁+b₂)/2^m`, the floor gives a tight
bound on the integer significand (`|c| ≤ ⌊(b₁+b₂)/2^m⌋`), saving 1 bit when
`(b₁+b₂)/2^m` is non-integer (which happens precisely when some `bᵢ` has
quantum strictly finer than `min(exp₁, exp₂)` — i.e., when `bᵢ`'s
representation isn't naturally aligned with the inferred quantum).  Defined
as `⊤` when either of the operand bounds or exponents is infinite.  The
`max 1 …` ensures `p ≥ 1` (the degenerate `b₁ = b₂ = 0` case otherwise
gives `Nat.clog 2 1 = 0`, violating `AbstractFormat.p_pos`). -/
noncomputable def opAddPrec (F₁ F₂ : AbstractFormat) : ℕ∞ :=
  match (F₁.b + F₂.b : WithTop Dyadic), (min F₁.exp F₂.exp : WithBot ℤ) with
  | (b : Dyadic), (m : ℤ) =>
      ((max 1 (Nat.clog 2 (Int.toNat ⌊((b : ℝ) / (2 : ℝ) ^ m)⌋ + 1)) : ℕ) : ℕ∞)
  | _, _ => ⊤

/-- Paper's `⊕`: additive format inference.  Returns the inferred
`AbstractFormat` `𝒜(⌈log₂((b₁+b₂)/2^min(exp₁,exp₂) + 1)⌉, min(exp₁, exp₂),
b₁ + b₂)`, matching the paper.  The `F.exp ≠ ⊥` hypotheses ensure the
result satisfies `not_degenerate`. -/
noncomputable def opAdd (F₁ F₂ : AbstractFormat)
    (h₁ : F₁.exp ≠ ⊥) (h₂ : F₂.exp ≠ ⊥) : AbstractFormat where
  p := opAddPrec F₁ F₂
  exp := min F₁.exp F₂.exp
  b := F₁.b + F₂.b
  p_pos := by
    -- Either p = ⊤ (trivial) or p = max 1 _ (≥ 1).
    show 1 ≤ opAddPrec F₁ F₂
    unfold opAddPrec
    split
    · -- Finite case: opAddPrec = ((max 1 _ : ℕ) : ℕ∞).
      exact_mod_cast le_max_left _ _
    · exact le_top
  not_degenerate := by
    refine Or.inr ?_
    obtain ⟨e₁, he₁⟩ := WithBot.ne_bot_iff_exists.mp h₁
    obtain ⟨e₂, he₂⟩ := WithBot.ne_bot_iff_exists.mp h₂
    have : min F₁.exp F₂.exp = ((min e₁ e₂ : ℤ) : WithBot ℤ) := by
      rw [← he₁, ← he₂]
      rcases le_total e₁ e₂ with hle | hle
      · rw [min_eq_left (by exact_mod_cast hle : (e₁ : WithBot ℤ) ≤ (e₂ : WithBot ℤ))]
        rw [min_eq_left hle]
      · rw [min_eq_right (by exact_mod_cast hle : (e₂ : WithBot ℤ) ≤ (e₁ : WithBot ℤ))]
        rw [min_eq_right hle]
    rw [this]
    exact WithBot.coe_ne_bot
  b_nn := by
    cases hF1_b : F₁.b with
    | top => rw [WithTop.top_add]; exact le_top
    | coe d1 => cases hF2_b : F₂.b with
      | top => rw [WithTop.add_top]; exact le_top
      | coe d2 =>
        rw [← WithTop.coe_add]
        refine WithTop.coe_le_coe.mpr ?_
        change (0 : ℝ) ≤ ((d1 + d2 : Dyadic) : ℝ)
        push_cast
        linarith [F₁.b_nn_of_coe hF1_b, F₂.b_nn_of_coe hF2_b]

/-- **Mul ⊆ inferred** — paper's `⊗`-containment:
`{x · y | x ∈ F₁, y ∈ F₂} ⊆ opMul F₁ F₂`. -/
theorem mul_subset (F₁ F₂ : AbstractFormat)
    (h₁ : F₁.exp ≠ ⊥) (h₂ : F₂.exp ≠ ⊥) :
    F₁.toSet * F₂.toSet ⊆ (opMul F₁ F₂ h₁ h₂).toSet := by
  rintro z ⟨x, hx, y, hy, rfl⟩
  obtain ⟨h_prec, h_quant, h_bnd⟩ :=
    mul_inferred (mem_toSet.mp hx) (mem_toSet.mp hy)
  refine ⟨h_prec, h_quant, ?_⟩
  change AbstractFormat.boundOK (F₁.b * F₂.b) (x * y)
  -- Casework on the bounds, using the zero-degenerate cases when needed.
  cases hF1_b : F₁.b with
  | top => cases hF2_b : F₂.b with
    | top => simp
    | coe d2 =>
      by_cases hd2_zero : (d2 : Dyadic) = 0
      · -- F₂.b = 0 forces y = 0, so x*y = 0.
        rw [hd2_zero, WithTop.coe_zero, mul_zero]
        have hy_bnd := (mem_toSet.mp hy).2.2
        rw [hF2_b] at hy_bnd
        change |(y : ℝ)| ≤ ((d2 : Dyadic) : ℝ) at hy_bnd
        have hy_zero : ((y : Dyadic) : ℝ) = 0 := by
          rw [hd2_zero] at hy_bnd
          exact abs_nonpos_iff.mp (by push_cast at hy_bnd; exact hy_bnd)
        change |((x * y : Dyadic) : ℝ)| ≤ ((0 : Dyadic) : ℝ)
        push_cast
        rw [hy_zero, mul_zero, abs_zero]
      · rw [WithTop.top_mul (by exact_mod_cast hd2_zero)]; trivial
  | coe d1 => cases hF2_b : F₂.b with
    | top =>
      by_cases hd1_zero : (d1 : Dyadic) = 0
      · rw [hd1_zero, WithTop.coe_zero, zero_mul]
        have hx_bnd := (mem_toSet.mp hx).2.2
        rw [hF1_b] at hx_bnd
        change |(x : ℝ)| ≤ ((d1 : Dyadic) : ℝ) at hx_bnd
        have hx_zero : ((x : Dyadic) : ℝ) = 0 := by
          rw [hd1_zero] at hx_bnd
          exact abs_nonpos_iff.mp (by push_cast at hx_bnd; exact hx_bnd)
        change |((x * y : Dyadic) : ℝ)| ≤ ((0 : Dyadic) : ℝ)
        push_cast
        rw [hx_zero, zero_mul, abs_zero]
      · rw [WithTop.mul_top (by exact_mod_cast hd1_zero)]; trivial
    | coe d2 =>
      rw [← WithTop.coe_mul]
      exact h_bnd d1 d2 hF1_b hF2_b

/-- Precision bound for the tight `opAdd`: if every bound and exponent is
finite, the specific significand of `x + y` at the finer quantum is bounded
by `⌊(b₁+b₂)/2^m⌋` (since `|c|` is an integer and `|c| ≤ (b₁+b₂)/2^m`
as a real), hence its bit-length fits in the floor-based tight precision
formula.  This is the technical heart of `add_subset`'s precision claim. -/
private theorem add_prec_finite {F₁ F₂ : AbstractFormat} {x y : Dyadic}
    {b1 b2 : Dyadic} {e1 e2 : ℤ}
    (hF1_b : F₁.b = (b1 : WithTop Dyadic)) (hF2_b : F₂.b = (b2 : WithTop Dyadic))
    (hF1_exp : F₁.exp = (e1 : WithBot ℤ)) (hF2_exp : F₂.exp = (e2 : WithBot ℤ))
    (hx : x ∈ F₁) (hy : y ∈ F₂) :
    Dyadic.precisionAtMost
      ((max 1 (Nat.clog 2 (Int.toNat ⌊(((b1 + b2 : Dyadic) : ℝ)) /
                                         (2 : ℝ) ^ (min e1 e2)⌋ + 1)) : ℕ) : ℕ∞)
      (x + y) := by
  obtain ⟨_, hqx, hbx⟩ := hx
  obtain ⟨_, hqy, hby⟩ := hy
  rw [hF1_exp] at hqx
  rw [hF2_exp] at hqy
  rw [hF1_b] at hbx
  rw [hF2_b] at hby
  change |(x : ℝ)| ≤ ((b1 : Dyadic) : ℝ) at hbx
  change |(y : ℝ)| ≤ ((b2 : Dyadic) : ℝ) at hby
  obtain ⟨c1, hxeq⟩ := hqx
  obtain ⟨c2, hyeq⟩ := hqy
  set m := min e1 e2 with hm
  have he1_ge : m ≤ e1 := min_le_left _ _
  have he2_ge : m ≤ e2 := min_le_right _ _
  -- Construct the significand of x+y at quantum m.
  set c : ℤ := c1 * 2 ^ (e1 - m).toNat + c2 * 2 ^ (e2 - m).toNat with hc_def
  have h_xy_eq : ((x + y : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ) ^ m := by
    push_cast
    rw [hxeq, hyeq, hc_def]
    push_cast
    rw [two_zpow_split_toNat he1_ge, two_zpow_split_toNat he2_ge]
    ring
  -- Bound |c|: |c|·2^m ≤ |x|+|y| ≤ b1+b2.
  have h2m_pos : (0 : ℝ) < (2 : ℝ) ^ m := zpow_pos (by norm_num) _
  have h_b1_nn : 0 ≤ ((b1 : Dyadic) : ℝ) := F₁.b_nn_of_coe hF1_b
  have h_b2_nn : 0 ≤ ((b2 : Dyadic) : ℝ) := F₂.b_nn_of_coe hF2_b
  have h_c_bound : |(c : ℝ)| * (2 : ℝ) ^ m ≤ ((b1 : Dyadic) : ℝ) + ((b2 : Dyadic) : ℝ) := by
    calc |(c : ℝ)| * (2 : ℝ) ^ m
        = |((x + y : Dyadic) : ℝ)| := by rw [h_xy_eq, abs_mul_two_zpow]
      _ ≤ |(x : ℝ)| + |(y : ℝ)| := by push_cast; exact abs_add_le _ _
      _ ≤ ((b1 : Dyadic) : ℝ) + ((b2 : Dyadic) : ℝ) := add_le_add hbx hby
  -- Therefore |c| ≤ (b1+b2) / 2^m (as reals).
  have h_c_le_ratio : |(c : ℝ)| ≤ (((b1 + b2 : Dyadic) : ℝ)) / (2 : ℝ) ^ m := by
    rw [le_div_iff₀ h2m_pos]; push_cast at h_c_bound ⊢; linarith
  -- |c| (as ℤ) ≤ ⌊(b₁+b₂)/2^m⌋ — since |c| is an integer.
  set N : ℕ := Int.toNat ⌊(((b1 + b2 : Dyadic) : ℝ)) / (2 : ℝ) ^ m⌋ with hN_def
  have h_ratio_nn : 0 ≤ (((b1 + b2 : Dyadic) : ℝ)) / (2 : ℝ) ^ m :=
    div_nonneg (by push_cast; linarith) (le_of_lt h2m_pos)
  have h_floor_nn : 0 ≤ ⌊(((b1 + b2 : Dyadic) : ℝ)) / (2 : ℝ) ^ m⌋ :=
    Int.floor_nonneg.mpr h_ratio_nn
  have hN_floor : (N : ℤ) = ⌊(((b1 + b2 : Dyadic) : ℝ)) / (2 : ℝ) ^ m⌋ := by
    rw [hN_def, Int.toNat_of_nonneg h_floor_nn]
  have h_abs_c_le : |c| ≤ (N : ℤ) := by
    rw [hN_floor]
    exact Int.le_floor.mpr (by push_cast; exact h_c_le_ratio)
  -- Build the precisionAtMost witness.
  refine ⟨c, m, h_xy_eq, ?_⟩
  -- Goal: |c| < (2 : ℤ) ^ max 1 (Nat.clog 2 (N + 1)).
  -- Have: |c| ≤ N, hence |c| + 1 ≤ N + 1 ≤ 2 ^ Nat.clog 2 (N+1) ≤ 2 ^ p.
  have h_natAbs_le : c.natAbs ≤ N := by
    have : (c.natAbs : ℤ) ≤ (N : ℤ) := by rw [Int.natCast_natAbs]; exact h_abs_c_le
    exact_mod_cast this
  have h_clog : N + 1 ≤ 2 ^ Nat.clog 2 (N + 1) :=
    Nat.le_pow_clog (by norm_num : 1 < 2) _
  have h_pow_mono : Nat.clog 2 (N + 1) ≤ max 1 (Nat.clog 2 (N + 1)) := le_max_right _ _
  have h_pow_le : 2 ^ Nat.clog 2 (N + 1) ≤ 2 ^ max 1 (Nat.clog 2 (N + 1)) :=
    Nat.pow_le_pow_right (by norm_num) h_pow_mono
  have h_final : c.natAbs + 1 ≤ 2 ^ max 1 (Nat.clog 2 (N + 1)) := by
    calc c.natAbs + 1 ≤ N + 1 := Nat.add_le_add_right h_natAbs_le 1
      _ ≤ 2 ^ Nat.clog 2 (N + 1) := h_clog
      _ ≤ _ := h_pow_le
  -- |c| = c.natAbs as a ℤ.
  change |c| < (2 : ℤ) ^ max 1 (Nat.clog 2 (N + 1))
  rw [Int.abs_eq_natAbs]
  have h_lt : c.natAbs < 2 ^ max 1 (Nat.clog 2 (N + 1)) := by omega
  exact_mod_cast h_lt

/-- **Add ⊆ inferred** — paper's `⊕`-containment:
`{x + y | x ∈ F₁, y ∈ F₂} ⊆ opAdd F₁ F₂`. -/
theorem add_subset (F₁ F₂ : AbstractFormat)
    (h₁ : F₁.exp ≠ ⊥) (h₂ : F₂.exp ≠ ⊥) :
    F₁.toSet + F₂.toSet ⊆ (opAdd F₁ F₂ h₁ h₂).toSet := by
  rintro z ⟨x, hx, y, hy, rfl⟩
  obtain ⟨h_quant, h_bnd⟩ :=
    add_inferred (mem_toSet.mp hx) (mem_toSet.mp hy)
  refine ⟨?_, h_quant, ?_⟩
  · -- precisionAtMost (opAddPrec F₁ F₂) (x + y)
    change Dyadic.precisionAtMost (opAddPrec F₁ F₂) (x + y)
    unfold opAddPrec
    cases hsum : (F₁.b + F₂.b : WithTop Dyadic) with
    | top => simp
    | coe sumB =>
      cases hmin : (min F₁.exp F₂.exp : WithBot ℤ) with
      | bot =>
        -- Contradiction: h₁ ∧ h₂ ⇒ min ≠ ⊥.
        exfalso
        obtain ⟨e₁, he₁⟩ := WithBot.ne_bot_iff_exists.mp h₁
        obtain ⟨e₂, he₂⟩ := WithBot.ne_bot_iff_exists.mp h₂
        have : min F₁.exp F₂.exp = ((min e₁ e₂ : ℤ) : WithBot ℤ) := by
          rw [← he₁, ← he₂]
          rcases le_total e₁ e₂ with hle | hle
          · rw [min_eq_left (by exact_mod_cast hle : (e₁ : WithBot ℤ) ≤ (e₂ : WithBot ℤ))]
            rw [min_eq_left hle]
          · rw [min_eq_right (by exact_mod_cast hle : (e₂ : WithBot ℤ) ≤ (e₁ : WithBot ℤ))]
            rw [min_eq_right hle]
        rw [this] at hmin
        exact (WithBot.coe_ne_bot hmin).elim
      | coe m =>
        -- Both bounds and exponents finite: extract b1, b2, e1, e2.
        obtain ⟨b1, b2, hF1_b, hF2_b, h_sum_eq⟩ := WithTop.add_eq_coe.mp hsum
        obtain ⟨e₁, he₁⟩ := WithBot.ne_bot_iff_exists.mp h₁
        obtain ⟨e₂, he₂⟩ := WithBot.ne_bot_iff_exists.mp h₂
        have h_min_eq : min e₁ e₂ = m := by
          have : min F₁.exp F₂.exp = ((min e₁ e₂ : ℤ) : WithBot ℤ) := by
            rw [← he₁, ← he₂]
            rcases le_total e₁ e₂ with hle | hle
            · rw [min_eq_left (by exact_mod_cast hle : (e₁ : WithBot ℤ) ≤ (e₂ : WithBot ℤ))]
              rw [min_eq_left hle]
            · rw [min_eq_right (by exact_mod_cast hle : (e₂ : WithBot ℤ) ≤ (e₁ : WithBot ℤ))]
              rw [min_eq_right hle]
          rw [this] at hmin
          exact_mod_cast hmin
        have h_sum_dyadic : b1 + b2 = sumB := h_sum_eq
        have := add_prec_finite hF1_b.symm hF2_b.symm he₁.symm he₂.symm
          (mem_toSet.mp hx) (mem_toSet.mp hy)
        rw [h_sum_dyadic, h_min_eq] at this
        exact this
  · -- boundOK
    change AbstractFormat.boundOK (F₁.b + F₂.b) (x + y)
    cases hF1_b : F₁.b with
    | top => rw [WithTop.top_add]; trivial
    | coe d1 => cases hF2_b : F₂.b with
      | top => rw [WithTop.add_top]; trivial
      | coe d2 =>
        rw [← WithTop.coe_add]
        exact h_bnd d1 d2 hF1_b hF2_b

/-- **Neg ⊆ self** — paper: `format(neg(e)) = format(e)`. -/
theorem neg_subset (F : AbstractFormat) : -F.toSet ⊆ F.toSet := by
  intro z hz
  have h_neg_z : -z ∈ F := mem_toSet.mp hz
  have h := neg_mem h_neg_z
  rw [neg_neg] at h
  exact mem_toSet.mpr h

/-- **Abs ⊆ self** — paper: `format(abs(e)) = format(e)`. -/
theorem abs_subset (F : AbstractFormat) :
    (Dyadic.abs '' F.toSet) ⊆ F.toSet := by
  rintro z ⟨x, hx, rfl⟩
  exact mem_toSet.mpr (abs_mem (mem_toSet.mp hx))

end AbstractFormat

end Mpfx
