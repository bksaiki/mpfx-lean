import Mpfx.Format
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Format inference for unrounded operations (Section 6.1 of the paper)

Section 6.1 of *When Double Rounding is Correct* introduces **format
inference**: a static analysis bounding the possible values of each
subexpression by the smallest `AbstractFormat` containing them.  For
unrounded operations:

* `neg` and `abs` preserve the format.
* `mul`: `𝒜(p₁, exp₁, b₁) ⊗ 𝒜(p₂, exp₂, b₂) ⊆
          𝒜(p₁ + p₂, exp₁ + exp₂, b₁ × b₂)`.
* `add`: `𝒜(p₁, exp₁, b₁) ⊕ 𝒜(p₂, exp₂, b₂) ⊆
          𝒜(⌈log₂((b₁+b₂)/2^min(exp₁,exp₂) + 1)⌉, min(exp₁, exp₂), b₁ + b₂)`.

The file is in two layers:

**Predicate-level (lower layer)**: `mul_inferred` and `add_inferred` show
that the result satisfies the three `AbstractFormat` membership predicates
(`precisionAtMost`, `quantumAtLeast`, `boundOK`) at the inferred
parameters.  No `AbstractFormat`-validity hypotheses; works unconditionally.

**`⊆`-level (upper layer)**: `opMul` and `opAdd` construct the actual
inferred `AbstractFormat`, returning it via the paper's notation.  These
require both input formats to have finite exponents (`F.exp ≠ ⊥`) to ensure
the result's `not_degenerate` invariant.  The corresponding `mul_subset`
and `add_subset` theorems then have the paper's form
`F₁.toSet * F₂.toSet ⊆ (opMul F₁ F₂ _ _).toSet`.

In the paper, one would write: "The equation applies when the inferred
bounding number format is itself a valid `AbstractFormat` — namely, when
both operand formats have finite exponents.  Edge cases like
`𝒜(⊤, e, b) ⊗ 𝒜(p, ⊥, b')` produce a `(⊤, ⊥, ·)` tuple, which is excluded
as a degenerate parameterization."

The five results:

* `abs_mem` — `x ∈ F → Dyadic.abs x ∈ F`.
* `mul_inferred` / `mul_subset` — multiplicative containment (paper's `⊗`).
* `add_inferred` / `add_subset` — additive containment (paper's `⊕`).
* `neg_subset` / `abs_subset` — set-level forms of `neg_mem` and `abs_mem`.
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

/-! ## `abs` preserves format (neg is already in `Format.lean`) -/

/-- `Dyadic.abs x ∈ F` whenever `x ∈ F`.  Follows from `neg_mem` (the format
is closed under negation) and the case analysis in `Dyadic.abs`. -/
theorem abs_mem {F : AbstractFormat} {x : Dyadic} (hx : x ∈ F) :
    Dyadic.abs x ∈ F := by
  unfold Dyadic.abs
  by_cases h : 0 ≤ (x : ℝ)
  · rw [if_pos h]; exact hx
  · rw [if_neg h]; exact neg_mem hx

/-! ## `mul` containment: predicate-level form of `F₁ ⊗ F₂` -/

/-- **Mul format inference** (Section 6.1).  If `x ∈ F₁` and `y ∈ F₂`, then
`x · y` satisfies the inferred parameters of `F₁ ⊗ F₂ = 𝒜(p₁ + p₂,
exp₁ + exp₂, b₁ × b₂)`: precision adds, quantum adds, bound multiplies. -/
theorem mul_inferred {F₁ F₂ : AbstractFormat} {x y : Dyadic}
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
    -- hp1 : ↑p1 = F₁.p, hp2 : ↑p2 = F₂.p
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
    -- he1 : ↑e1 = F₁.exp, he2 : ↑e2 = F₂.exp
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

/-! ## `add` containment: predicate-level form of `F₁ ⊕ F₂`

For addition we prove the quantum and bound parts of the paper's `⊕`
formula exactly.  The paper also gives a tight precision bound
`p = ⌈log₂((b₁+b₂)/2^min(exp₁,exp₂) + 1)⌉`; we do not yet prove the
precision part — see the doc on `add_inferred` for details. -/

/-- **Add format inference** (Section 6.1).  If `x ∈ F₁` and `y ∈ F₂`, then
`x + y` satisfies:

* quantum at least `min(F₁.exp, F₂.exp)`,
* bound `|x + y| ≤ F₁.b + F₂.b` (when both bounds are finite).

The paper also gives a *tight* precision bound
`⌈log₂((b₁+b₂)/2^min(exp₁,exp₂) + 1)⌉`; that part is omitted here (it would
require `Nat.clog` machinery and a careful derivation of the sum's
significand at the finer quantum).  Any precision ≥ this bound, including
`⊤`, gives a valid containing format. -/
theorem add_inferred {F₁ F₂ : AbstractFormat} {x y : Dyadic}
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

/-! ## `⊆`-form statements (paper's notation)

The paper writes `A ⊗ B ⊆ A(p₁+p₂, …)` directly between formats.  To produce
the RHS as a valid `AbstractFormat`, we require the input formats to satisfy
a precondition ensuring the inferred output's `not_degenerate` invariant
holds.  The failing edge case is when one operand has `p = ⊤` (forcing its
`exp` to be finite by its own `not_degenerate`) and the other has `exp = ⊥`
with finite `p ≥ 2`: the natural `(p₁+p₂, exp₁+exp₂, …)` formula then
produces `(⊤, ⊥, …)`, which violates `not_degenerate`.  A simple sufficient
precondition is that *both* operand formats have finite exponents — this
ensures the inferred output's `exp` is finite, satisfying `not_degenerate`'s
second disjunct.  In writing this up, one would say "the equation applies
when the inferred bounding format is itself a valid `AbstractFormat`."  -/

open scoped Pointwise

/-- Coerce an `AbstractFormat` to its underlying set of representable
Dyadics.  Lets us use set-level `⊆` between abstract formats. -/
def toSet (F : AbstractFormat) : Set Dyadic := {x | x ∈ F}

@[simp] theorem mem_toSet {F : AbstractFormat} {x : Dyadic} :
    x ∈ F.toSet ↔ x ∈ F := Iff.rfl

/-- Multiplicative format inference (paper's `⊗`).  Returns the inferred
`AbstractFormat` `𝒜(p₁ + p₂, exp₁ + exp₂, b₁ × b₂)`.  Requires both inputs
to have finite exponents so the result satisfies `not_degenerate`. -/
noncomputable def opMul (F₁ F₂ : AbstractFormat)
    (h₁ : F₁.exp ≠ ⊥) (h₂ : F₂.exp ≠ ⊥) : AbstractFormat where
  p := F₁.p + F₂.p
  exp := F₁.exp + F₂.exp
  b := F₁.b * F₂.b
  p_pos := by
    -- 1 + 1 ≤ F₁.p + F₂.p, hence 1 ≤ F₁.p + F₂.p.
    calc (1 : ℕ∞) ≤ 1 + 1 := by norm_num
      _ ≤ F₁.p + F₂.p := add_le_add F₁.p_pos F₂.p_pos
  not_degenerate := by
    -- F₁.exp ≠ ⊥ and F₂.exp ≠ ⊥ ⇒ sum ≠ ⊥.  Use second disjunct.
    refine Or.inr ?_
    obtain ⟨e₁, he₁⟩ := WithBot.ne_bot_iff_exists.mp h₁
    obtain ⟨e₂, he₂⟩ := WithBot.ne_bot_iff_exists.mp h₂
    have h_sum : F₁.exp + F₂.exp = ((e₁ + e₂ : ℤ) : WithBot ℤ) := by
      rw [← he₁, ← he₂]; push_cast; rfl
    rw [h_sum]
    exact WithBot.coe_ne_bot
  b_nn := by
    -- 0 ≤ F₁.b * F₂.b.  Casework on whether each bound is ⊤.
    cases hF1_b : F₁.b with
    | top => cases hF2_b : F₂.b with
      | top => simp
      | coe d2 =>
        have hd2_nn := F₂.b_nn_of_coe hF2_b
        by_cases hd2_zero : (d2 : Dyadic) = 0
        · rw [hd2_zero, WithTop.coe_zero, mul_zero]
        · rw [WithTop.top_mul (by exact_mod_cast hd2_zero)]
          exact le_top
    | coe d1 =>
      have hd1_nn := F₁.b_nn_of_coe hF1_b
      cases hF2_b : F₂.b with
      | top =>
        by_cases hd1_zero : (d1 : Dyadic) = 0
        · rw [hd1_zero, WithTop.coe_zero, zero_mul]
        · rw [WithTop.mul_top (by exact_mod_cast hd1_zero)]
          exact le_top
      | coe d2 =>
        have hd2_nn := F₂.b_nn_of_coe hF2_b
        rw [← WithTop.coe_mul]
        refine WithTop.coe_le_coe.mpr ?_
        change (0 : ℝ) ≤ ((d1 * d2 : Dyadic) : ℝ)
        push_cast
        exact mul_nonneg hd1_nn hd2_nn

/-- Additive format inference (paper's `⊕`, with loose precision `⊤`).
Returns the inferred `AbstractFormat` `𝒜(⊤, min(exp₁, exp₂), b₁ + b₂)`.
Requires both inputs to have finite exponents so the result satisfies
`not_degenerate`.  The paper's tighter precision
`⌈log₂((b₁+b₂)/2^min(exp₁,exp₂) + 1)⌉` is deferred. -/
noncomputable def opAdd (F₁ F₂ : AbstractFormat)
    (h₁ : F₁.exp ≠ ⊥) (h₂ : F₂.exp ≠ ⊥) : AbstractFormat where
  p := ⊤
  exp := min F₁.exp F₂.exp
  b := F₁.b + F₂.b
  p_pos := le_top
  not_degenerate := by
    refine Or.inr ?_
    -- min ≠ ⊥ since both are ≠ ⊥.
    obtain ⟨e₁, he₁⟩ := WithBot.ne_bot_iff_exists.mp h₁
    obtain ⟨e₂, he₂⟩ := WithBot.ne_bot_iff_exists.mp h₂
    have h_min : min F₁.exp F₂.exp = ((min e₁ e₂ : ℤ) : WithBot ℤ) := by
      rw [← he₁, ← he₂]
      rcases le_total e₁ e₂ with hle | hle
      · rw [min_eq_left (by exact_mod_cast hle : (e₁ : WithBot ℤ) ≤ (e₂ : WithBot ℤ))]
        rw [min_eq_left hle]
      · rw [min_eq_right (by exact_mod_cast hle : (e₂ : WithBot ℤ) ≤ (e₁ : WithBot ℤ))]
        rw [min_eq_right hle]
    rw [h_min]
    exact WithBot.coe_ne_bot
  b_nn := by
    cases hF1_b : F₁.b with
    | top => rw [WithTop.top_add]; exact le_top
    | coe d1 =>
      cases hF2_b : F₂.b with
      | top => rw [WithTop.add_top]; exact le_top
      | coe d2 =>
        rw [← WithTop.coe_add]
        refine WithTop.coe_le_coe.mpr ?_
        change (0 : ℝ) ≤ ((d1 + d2 : Dyadic) : ℝ)
        have hd1_nn := F₁.b_nn_of_coe hF1_b
        have hd2_nn := F₂.b_nn_of_coe hF2_b
        push_cast
        linarith

/-- **Mul ⊆ inferred** (Section 6.1, paper's `⊗`): under the validity
precondition that both operand formats have finite exponents, the set of
products `{x · y | x ∈ F₁, y ∈ F₂}` is contained in the inferred
`AbstractFormat`. -/
theorem mul_subset (F₁ F₂ : AbstractFormat)
    (h₁ : F₁.exp ≠ ⊥) (h₂ : F₂.exp ≠ ⊥) :
    F₁.toSet * F₂.toSet ⊆ (opMul F₁ F₂ h₁ h₂).toSet := by
  rintro z ⟨x, hx, y, hy, rfl⟩
  obtain ⟨h_prec, h_quant, h_bnd⟩ :=
    mul_inferred (mem_toSet.mp hx) (mem_toSet.mp hy)
  refine ⟨h_prec, h_quant, ?_⟩
  -- boundOK: |x*y| ≤ (opMul ...).b = F₁.b * F₂.b.
  change AbstractFormat.boundOK (F₁.b * F₂.b) (x * y)
  cases hF1_b : F₁.b with
  | top => cases hF2_b : F₂.b with
    | top => simp
    | coe d2 =>
      by_cases hd2_zero : (d2 : Dyadic) = 0
      · -- F₂.b = 0 ⇒ y = 0 ⇒ x*y = 0.
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
      · rw [WithTop.top_mul (by exact_mod_cast hd2_zero)]
        trivial
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
      · rw [WithTop.mul_top (by exact_mod_cast hd1_zero)]
        trivial
    | coe d2 =>
      rw [← WithTop.coe_mul]
      exact h_bnd d1 d2 hF1_b hF2_b

/-- **Add ⊆ inferred** (Section 6.1, paper's `⊕`): under the validity
precondition that both operand formats have finite exponents, the set of
sums `{x + y | x ∈ F₁, y ∈ F₂}` is contained in the inferred
`AbstractFormat`. -/
theorem add_subset (F₁ F₂ : AbstractFormat)
    (h₁ : F₁.exp ≠ ⊥) (h₂ : F₂.exp ≠ ⊥) :
    F₁.toSet + F₂.toSet ⊆ (opAdd F₁ F₂ h₁ h₂).toSet := by
  rintro z ⟨x, hx, y, hy, rfl⟩
  obtain ⟨h_quant, h_bnd⟩ :=
    add_inferred (mem_toSet.mp hx) (mem_toSet.mp hy)
  refine ⟨trivial, h_quant, ?_⟩
  -- boundOK: |x+y| ≤ F₁.b + F₂.b.
  change AbstractFormat.boundOK (F₁.b + F₂.b) (x + y)
  cases hF1_b : F₁.b with
  | top => rw [WithTop.top_add]; trivial
  | coe d1 =>
    cases hF2_b : F₂.b with
    | top => rw [WithTop.add_top]; trivial
    | coe d2 =>
      rw [← WithTop.coe_add]
      exact h_bnd d1 d2 hF1_b hF2_b

/-- **Neg ⊆ self** (Section 6.1): set-level form of `neg_mem`. -/
theorem neg_subset (F : AbstractFormat) : -F.toSet ⊆ F.toSet := by
  intro z hz
  have h_neg_z : -z ∈ F := mem_toSet.mp hz
  have h := neg_mem h_neg_z
  rw [neg_neg] at h
  exact mem_toSet.mpr h

/-- **Abs ⊆ self** (Section 6.1): set-level form of `abs_mem`. -/
theorem abs_subset (F : AbstractFormat) :
    (Dyadic.abs '' F.toSet) ⊆ F.toSet := by
  rintro z ⟨x, hx, rfl⟩
  exact mem_toSet.mpr (abs_mem (mem_toSet.mp hx))

end AbstractFormat

end Mpfx
