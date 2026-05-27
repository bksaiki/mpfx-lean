import Mpfx2.Format
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log

/-!
# Format inference for unrounded operations (Section 6.1 of the paper)

Section 6.1 of *When Double Rounding is Correct* introduces **format
inference**: a static analysis bounding the possible values of each
subexpression by the smallest `Format` containing them.  For unrounded
operations, the paper states:

* `neg` and `abs` preserve the format.
* `mul`: `𝒜(p₁, exp₁, b₁) ⊗ 𝒜(p₂, exp₂, b₂) ⊆
          𝒜(p₁ + p₂, exp₁ + exp₂, b₁ × b₂)`.
* `add`: `𝒜(p₁, exp₁, b₁) ⊕ 𝒜(p₂, exp₂, b₂) ⊆
          𝒜(⌈log₂((b₁+b₂)/2^min(exp₁,exp₂) + 1)⌉, min(exp₁, exp₂), b₁ + b₂)`.

## Result formats are plain `Format`s

`Format` carries only the three fields `(p, exp, b)` with **no** validity
invariants (those live in `FiniteFormat`/`ParityFormat`). So `opMul`/`opAdd`
produce a plain `Format` with no proof obligations, and need no `F.exp ≠ ⊥`
preconditions.

For the `⊕`-precision we use a *slightly tighter* formula than the paper:
`opAddPrec` returns `⌈log₂(⌊(b₁+b₂)/2^min(exp₁,exp₂)⌋ + 1)⌉` (floor inside),
matching the actual integer bound on `|c|`.  The `max 1 …` keeps `p ≥ 1`.
-/

namespace Mpfx2

namespace Dyadic

/-- Absolute value of a dyadic, as a dyadic.  Equal to `x` if `0 ≤ x`,
otherwise `-x`.  Lives in `Dyadic` because the underlying subring is closed
under negation.  Computable since `ℚ` comparison is decidable. -/
def abs (x : Dyadic) : Dyadic :=
  if 0 ≤ (x : ℚ) then x else -x

@[simp] theorem coe_abs (x : Dyadic) : (Dyadic.abs x : ℝ) = |(x : ℝ)| := by
  unfold Dyadic.abs
  by_cases h : 0 ≤ (x : ℚ)
  · rw [if_pos h]
    rw [coe_real_eq_ratCast]
    have : (0 : ℝ) ≤ ((x : ℚ) : ℝ) := by exact_mod_cast h
    rw [_root_.abs_of_nonneg this]
  · rw [if_neg h]
    rw [coe_real_neg, coe_real_eq_ratCast]
    have : ((x : ℚ) : ℝ) < 0 := by
      have : (x : ℚ) < 0 := lt_of_not_ge h
      exact_mod_cast this
    rw [_root_.abs_of_neg this]

@[simp] theorem coe_rat_abs (x : Dyadic) : ((Dyadic.abs x : Dyadic) : ℚ) = |(x : ℚ)| := by
  unfold Dyadic.abs
  by_cases h : 0 ≤ (x : ℚ)
  · rw [if_pos h, _root_.abs_of_nonneg h]
  · rw [if_neg h, Subring.coe_neg, _root_.abs_of_neg (lt_of_not_ge h)]

end Dyadic

namespace Format

/-! ## `abs` preserves format -/

/-- `Dyadic.abs x ∈ F` whenever `x ∈ F`. -/
theorem abs_mem {F : Format} {x : Dyadic} (hx : x ∈ F) :
    Dyadic.abs x ∈ F := by
  unfold Dyadic.abs
  by_cases h : 0 ≤ (x : ℚ)
  · rw [if_pos h]; exact hx
  · rw [if_neg h]; exact neg_mem hx

open scoped Pointwise

/-- Coerce a `Format` to its underlying set of representable Dyadics.  Used to
express `⊆` between formats at the `Set Dyadic` level. -/
def toSet (F : Format) : Set Dyadic := {x | x ∈ F}

@[simp] theorem mem_toSet {F : Format} {x : Dyadic} :
    x ∈ F.toSet ↔ x ∈ F := Iff.rfl

/-! ## Static inference operators (paper's `⊗`/`⊕`) -/

/-- Paper's `⊗`: multiplicative format inference.  Returns
`𝒜(p₁ + p₂, exp₁ + exp₂, b₁ × b₂)`.  The bound is constructed by `match`:
when both operand bounds are finite the result is their product (non-negative
by `mul_nonneg`); otherwise `⊤`. -/
def opMul (F₁ F₂ : Format) : Format where
  p := F₁.p + F₂.p
  exp := F₁.exp + F₂.exp
  b := match F₁.b, F₂.b with
    | (b₁ : NonNegDyadic), (b₂ : NonNegDyadic) =>
        ((⟨b₁.1 * b₂.1, by
            have := mul_nonneg b₁.2 b₂.2
            push_cast at this ⊢
            exact this⟩ : NonNegDyadic) : WithTop NonNegDyadic)
    | _, _ => ⊤

/-- Tight precision bound for `⊕`:
`p = ⌈log₂(⌊(b₁+b₂)/2^min(exp₁,exp₂)⌋ + 1)⌉` (with `max 1 …` to keep `p ≥ 1`),
or `⊤` when either operand bound or exponent is infinite.  The floor ratio is
computed over `ℝ`. -/
noncomputable def opAddPrec (F₁ F₂ : Format) : WithTop ℕ+ :=
  match (F₁.b : WithTop NonNegDyadic), (F₂.b : WithTop NonNegDyadic),
        (min F₁.exp F₂.exp : WithBot ℤ) with
  | (b₁ : NonNegDyadic), (b₂ : NonNegDyadic), (m : ℤ) =>
      WithTop.some (⟨max 1 (Nat.clog 2
            (Int.toNat ⌊(((b₁.1 + b₂.1 : Dyadic) : ℝ)) / (2 : ℝ) ^ m⌋ + 1)),
          Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)⟩ : ℕ+)
  | _, _, _ => ⊤

/-- Paper's `⊕`: additive format inference.  Returns the inferred `Format`
`𝒜(opAddPrec, min(exp₁, exp₂), b₁ + b₂)`.  The bound is constructed by `match`
on both operand bounds (their sum, non-negative by `add_nonneg`), else `⊤`. -/
noncomputable def opAdd (F₁ F₂ : Format) : Format where
  p := opAddPrec F₁ F₂
  exp := min F₁.exp F₂.exp
  b := match F₁.b, F₂.b with
    | (b₁ : NonNegDyadic), (b₂ : NonNegDyadic) =>
        ((⟨b₁.1 + b₂.1, by
            have := add_nonneg b₁.2 b₂.2
            push_cast at this ⊢
            exact this⟩ : NonNegDyadic) : WithTop NonNegDyadic)
    | _, _ => ⊤

/-! ## Predicate-level helpers (private) -/

/-- For `x ∈ F₁, y ∈ F₂`, the product `x · y` satisfies the inferred
multiplicative precision and quantum parameters. -/
private theorem mul_inferred_pq {F₁ F₂ : Format} {x y : Dyadic}
    (hx : x ∈ F₁) (hy : y ∈ F₂) :
    Dyadic.precisionAtMost (F₁.p + F₂.p) (x * y) ∧
    Dyadic.quantumAtLeast (F₁.exp + F₂.exp) (x * y) := by
  obtain ⟨hpx, hqx, _⟩ := hx
  obtain ⟨hpy, hqy, _⟩ := hy
  refine ⟨?_, ?_⟩
  · -- precisionAtMost (p₁ + p₂) (x * y)
    by_cases hF1_p : F₁.p = ⊤
    · have : F₁.p + F₂.p = (⊤ : WithTop ℕ+) := by rw [hF1_p]; rfl
      rw [this]; trivial
    by_cases hF2_p : F₂.p = ⊤
    · have : F₁.p + F₂.p = (⊤ : WithTop ℕ+) := by rw [hF2_p]; cases F₁.p <;> rfl
      rw [this]; trivial
    obtain ⟨p1, hp1⟩ := WithTop.ne_top_iff_exists.mp hF1_p
    obtain ⟨p2, hp2⟩ := WithTop.ne_top_iff_exists.mp hF2_p
    rw [← hp1] at hpx
    rw [← hp2] at hpy
    rw [Dyadic.precisionAtMost_coe] at hpx hpy
    obtain ⟨c1, e1, hxeq, hc1⟩ := hpx
    obtain ⟨c2, e2, hyeq, hc2⟩ := hpy
    have h_p_eq : F₁.p + F₂.p = (((p1 + p2 : ℕ+) : ℕ+) : WithTop ℕ+) := by
      rw [← hp1, ← hp2]; rfl
    rw [h_p_eq, Dyadic.precisionAtMost_coe]
    refine ⟨c1 * c2, e1 + e2, ?_, ?_⟩
    · change ((x * y : Dyadic) : ℚ) = _
      push_cast
      rw [hxeq, hyeq, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
      ring
    · rw [PNat.add_coe, pow_add, abs_mul]
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
    rw [Dyadic.quantumAtLeast_coe] at hqx' hqy'
    obtain ⟨c1, hxeq⟩ := hqx'
    obtain ⟨c2, hyeq⟩ := hqy'
    have h_exp_eq : F₁.exp + F₂.exp = ((e1 + e2 : ℤ) : WithBot ℤ) := by
      rw [← he1, ← he2]; push_cast; rfl
    rw [h_exp_eq, Dyadic.quantumAtLeast_coe]
    refine ⟨c1 * c2, ?_⟩
    change ((x * y : Dyadic) : ℚ) = _
    push_cast
    rw [hxeq, hyeq, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
    ring

/-- For `x ∈ F₁, y ∈ F₂`, the sum `x + y` satisfies the inferred additive
quantum parameter `min(exp₁, exp₂)`. -/
private theorem add_inferred_q {F₁ F₂ : Format} {x y : Dyadic}
    (hx : x ∈ F₁) (hy : y ∈ F₂) :
    Dyadic.quantumAtLeast (min F₁.exp F₂.exp) (x + y) := by
  obtain ⟨_, hqx, _⟩ := hx
  obtain ⟨_, hqy, _⟩ := hy
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
  rw [Dyadic.quantumAtLeast_coe] at hqx' hqy'
  obtain ⟨c1, hxeq⟩ := hqx'
  obtain ⟨c2, hyeq⟩ := hqy'
  have h_min_eq : min F₁.exp F₂.exp = ((min e1 e2 : ℤ) : WithBot ℤ) := by
    rw [← he1, ← he2]
    rcases le_total e1 e2 with hle | hle
    · rw [min_eq_left (by exact_mod_cast hle : (e1 : WithBot ℤ) ≤ (e2 : WithBot ℤ))]
      rw [min_eq_left hle]
    · rw [min_eq_right (by exact_mod_cast hle : (e2 : WithBot ℤ) ≤ (e1 : WithBot ℤ))]
      rw [min_eq_right hle]
  rw [h_min_eq, Dyadic.quantumAtLeast_coe]
  set m := min e1 e2 with hm
  have he1_ge : m ≤ e1 := min_le_left _ _
  have he2_ge : m ≤ e2 := min_le_right _ _
  refine ⟨c1 * 2 ^ (e1 - m).toNat + c2 * 2 ^ (e2 - m).toNat, ?_⟩
  -- split 2^e1 = 2^(e1-m).toNat · 2^m (and likewise for e2) over ℚ.
  have hsplit1 : (2 : ℚ) ^ e1 = (2 : ℚ) ^ (e1 - m).toNat * (2 : ℚ) ^ m := by
    rw [← zpow_natCast (2 : ℚ) (e1 - m).toNat, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0),
        Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ e1 - m)]
    congr 1; ring
  have hsplit2 : (2 : ℚ) ^ e2 = (2 : ℚ) ^ (e2 - m).toNat * (2 : ℚ) ^ m := by
    rw [← zpow_natCast (2 : ℚ) (e2 - m).toNat, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0),
        Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ e2 - m)]
    congr 1; ring
  change ((x + y : Dyadic) : ℚ) = _
  push_cast
  rw [hxeq, hyeq, hsplit1, hsplit2]
  ring

/-! ## Public `⊆`-level API -/

/-- **Mul ⊆ inferred** — paper's `⊗`-containment:
`{x · y | x ∈ F₁, y ∈ F₂} ⊆ opMul F₁ F₂`. -/
theorem mul_subset (F₁ F₂ : Format) :
    F₁.toSet * F₂.toSet ⊆ (opMul F₁ F₂).toSet := by
  rintro z ⟨x, hx, y, hy, rfl⟩
  obtain ⟨h_prec, h_quant⟩ := mul_inferred_pq (mem_toSet.mp hx) (mem_toSet.mp hy)
  refine ⟨h_prec, h_quant, ?_⟩
  -- boundOK of the matched product bound
  change boundOK
      (match F₁.b, F₂.b with
        | (b₁ : NonNegDyadic), (b₂ : NonNegDyadic) => _
        | _, _ => ⊤) (x * y)
  obtain ⟨_, _, hbx⟩ := mem_toSet.mp hx
  obtain ⟨_, _, hby⟩ := mem_toSet.mp hy
  cases hF1_b : F₁.b with
  | top => trivial
  | coe b₁ =>
    cases hF2_b : F₂.b with
    | top => trivial
    | coe b₂ =>
      -- goal: |(x*y : ℚ)| ≤ ((b₁.1 * b₂.1 : Dyadic) : ℚ)
      rw [hF1_b] at hbx
      rw [hF2_b] at hby
      change |(x : ℚ)| ≤ ((b₁.1 : Dyadic) : ℚ) at hbx
      change |(y : ℚ)| ≤ ((b₂.1 : Dyadic) : ℚ) at hby
      change |((x * y : Dyadic) : ℚ)| ≤ ((b₁.1 * b₂.1 : Dyadic) : ℚ)
      push_cast
      rw [abs_mul]
      have hb1_nn : 0 ≤ ((b₁.1 : Dyadic) : ℚ) := b₁.2
      exact mul_le_mul hbx hby (abs_nonneg _) hb1_nn

/-- Precision bound for the tight `opAdd`: if both bounds and exponents are
finite, the significand of `x + y` at the finer quantum is bounded by
`⌊(b₁+b₂)/2^m⌋`, so its bit-length fits the floor-based precision formula. -/
private theorem add_prec_finite {F₁ F₂ : Format} {x y : Dyadic}
    {b1 b2 : NonNegDyadic} {e1 e2 : ℤ}
    (hF1_b : F₁.b = (b1 : WithTop NonNegDyadic)) (hF2_b : F₂.b = (b2 : WithTop NonNegDyadic))
    (hF1_exp : F₁.exp = (e1 : WithBot ℤ)) (hF2_exp : F₂.exp = (e2 : WithBot ℤ))
    (hx : x ∈ F₁) (hy : y ∈ F₂) :
    Dyadic.precisionAtMost
      (WithTop.some (⟨max 1 (Nat.clog 2
            (Int.toNat ⌊(((b1.1 + b2.1 : Dyadic) : ℝ)) / (2 : ℝ) ^ (min e1 e2)⌋ + 1)),
          Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)⟩ : ℕ+))
      (x + y) := by
  obtain ⟨_, hqx, hbx⟩ := hx
  obtain ⟨_, hqy, hby⟩ := hy
  rw [hF1_exp] at hqx
  rw [hF2_exp] at hqy
  rw [hF1_b] at hbx
  rw [hF2_b] at hby
  change |(x : ℚ)| ≤ ((b1.1 : Dyadic) : ℚ) at hbx
  change |(y : ℚ)| ≤ ((b2.1 : Dyadic) : ℚ) at hby
  rw [Dyadic.quantumAtLeast_coe] at hqx hqy
  obtain ⟨c1, hxeq⟩ := hqx
  obtain ⟨c2, hyeq⟩ := hqy
  -- bridge bounds to ℝ
  have hbxR : |(x : ℝ)| ≤ ((b1.1 : Dyadic) : ℝ) := by
    rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast, ← Rat.cast_abs]; exact_mod_cast hbx
  have hbyR : |(y : ℝ)| ≤ ((b2.1 : Dyadic) : ℝ) := by
    rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast, ← Rat.cast_abs]; exact_mod_cast hby
  have hxeqR : (x : ℝ) = (c1 : ℝ) * (2 : ℝ) ^ e1 := by
    rw [Dyadic.coe_real_eq_ratCast, hxeq]; push_cast; ring
  have hyeqR : (y : ℝ) = (c2 : ℝ) * (2 : ℝ) ^ e2 := by
    rw [Dyadic.coe_real_eq_ratCast, hyeq]; push_cast; ring
  set m := min e1 e2 with hm
  have he1_ge : m ≤ e1 := min_le_left _ _
  have he2_ge : m ≤ e2 := min_le_right _ _
  set c : ℤ := c1 * 2 ^ (e1 - m).toNat + c2 * 2 ^ (e2 - m).toNat with hc_def
  have h_xy_eqR : ((x + y : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ) ^ m := by
    rw [Dyadic.coe_real_add, hxeqR, hyeqR, hc_def]
    push_cast
    rw [two_zpow_split_toNat he1_ge, two_zpow_split_toNat he2_ge]
    ring
  have h2m_pos : (0 : ℝ) < (2 : ℝ) ^ m := zpow_pos (by norm_num) _
  have h_b1_nn : 0 ≤ ((b1.1 : Dyadic) : ℝ) := by
    rw [Dyadic.coe_real_eq_ratCast]; exact_mod_cast b1.2
  have h_b2_nn : 0 ≤ ((b2.1 : Dyadic) : ℝ) := by
    rw [Dyadic.coe_real_eq_ratCast]; exact_mod_cast b2.2
  have h_c_bound : |(c : ℝ)| * (2 : ℝ) ^ m ≤ ((b1.1 : Dyadic) : ℝ) + ((b2.1 : Dyadic) : ℝ) := by
    calc |(c : ℝ)| * (2 : ℝ) ^ m
        = |((x + y : Dyadic) : ℝ)| := by rw [h_xy_eqR, abs_mul_two_zpow]
      _ ≤ |(x : ℝ)| + |(y : ℝ)| := by rw [Dyadic.coe_real_add]; exact abs_add_le _ _
      _ ≤ ((b1.1 : Dyadic) : ℝ) + ((b2.1 : Dyadic) : ℝ) := add_le_add hbxR hbyR
  have h_c_le_ratio : |(c : ℝ)| ≤ (((b1.1 + b2.1 : Dyadic) : ℝ)) / (2 : ℝ) ^ m := by
    rw [le_div_iff₀ h2m_pos]; rw [Dyadic.coe_real_add]; linarith
  set N : ℕ := Int.toNat ⌊(((b1.1 + b2.1 : Dyadic) : ℝ)) / (2 : ℝ) ^ m⌋ with hN_def
  have h_ratio_nn : 0 ≤ (((b1.1 + b2.1 : Dyadic) : ℝ)) / (2 : ℝ) ^ m :=
    div_nonneg (by rw [Dyadic.coe_real_add]; linarith) (le_of_lt h2m_pos)
  have h_floor_nn : 0 ≤ ⌊(((b1.1 + b2.1 : Dyadic) : ℝ)) / (2 : ℝ) ^ m⌋ :=
    Int.floor_nonneg.mpr h_ratio_nn
  have hN_floor : (N : ℤ) = ⌊(((b1.1 + b2.1 : Dyadic) : ℝ)) / (2 : ℝ) ^ m⌋ := by
    rw [hN_def, Int.toNat_of_nonneg h_floor_nn]
  have h_abs_c_le : |c| ≤ (N : ℤ) := by
    rw [hN_floor]
    refine Int.le_floor.mpr ?_
    rw [Int.cast_abs]
    exact h_c_le_ratio
  -- Build the precisionAtMost witness (over ℚ).
  rw [Dyadic.precisionAtMost_coe]
  refine ⟨c, m, ?_, ?_⟩
  · -- (x+y : ℚ) = c * 2^m
    have hq : (((x + y : Dyadic) : ℚ) : ℝ) = (((c : ℚ) * (2 : ℚ) ^ m : ℚ) : ℝ) := by
      rw [← Dyadic.coe_real_eq_ratCast, h_xy_eqR]; push_cast; ring
    exact_mod_cast hq
  · -- |c| < 2 ^ (max 1 (clog 2 (N+1)))
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
    change |c| < (2 : ℤ) ^ (((⟨max 1 (Nat.clog 2 (N + 1)), _⟩ : ℕ+) : ℕ))
    rw [Int.abs_eq_natAbs]
    have h_lt : c.natAbs < 2 ^ max 1 (Nat.clog 2 (N + 1)) := by omega
    change ((c.natAbs : ℤ)) < (2 : ℤ) ^ (max 1 (Nat.clog 2 (N + 1)))
    exact_mod_cast h_lt

/-- **Add ⊆ inferred** — paper's `⊕`-containment:
`{x + y | x ∈ F₁, y ∈ F₂} ⊆ opAdd F₁ F₂`. -/
theorem add_subset (F₁ F₂ : Format) :
    F₁.toSet + F₂.toSet ⊆ (opAdd F₁ F₂).toSet := by
  rintro z ⟨x, hx, y, hy, rfl⟩
  have h_quant := add_inferred_q (mem_toSet.mp hx) (mem_toSet.mp hy)
  obtain ⟨_, _, hbx⟩ := mem_toSet.mp hx
  obtain ⟨_, _, hby⟩ := mem_toSet.mp hy
  refine ⟨?_, h_quant, ?_⟩
  · -- precisionAtMost (opAddPrec F₁ F₂) (x + y)
    change Dyadic.precisionAtMost (opAddPrec F₁ F₂) (x + y)
    unfold opAddPrec
    cases hF1_b : F₁.b with
    | top => trivial
    | coe b1 =>
      cases hF2_b : F₂.b with
      | top => trivial
      | coe b2 =>
        cases hF1_exp : F₁.exp with
        | bot =>
          -- min ≤ ⊥ ⇒ min = ⊥ ⇒ ⊤ branch
          simp only [bot_inf_eq]; trivial
        | coe e1 =>
          cases hF2_exp : F₂.exp with
          | bot =>
            simp only [inf_bot_eq]; trivial
          | coe e2 =>
            have h_min_eq : min (e1 : WithBot ℤ) (e2 : WithBot ℤ)
                = ((min e1 e2 : ℤ) : WithBot ℤ) := by
              rcases le_total e1 e2 with hle | hle
              · rw [min_eq_left (by exact_mod_cast hle : (e1 : WithBot ℤ) ≤ (e2 : WithBot ℤ)),
                    min_eq_left hle]
              · rw [min_eq_right (by exact_mod_cast hle : (e2 : WithBot ℤ) ≤ (e1 : WithBot ℤ)),
                    min_eq_right hle]
            rw [h_min_eq]
            have := add_prec_finite hF1_b hF2_b hF1_exp hF2_exp
              (mem_toSet.mp hx) (mem_toSet.mp hy)
            convert this using 3
  · -- boundOK of the matched sum bound
    change boundOK
        (match F₁.b, F₂.b with
          | (b₁ : NonNegDyadic), (b₂ : NonNegDyadic) => _
          | _, _ => ⊤) (x + y)
    cases hF1_b : F₁.b with
    | top => trivial
    | coe b1 =>
      cases hF2_b : F₂.b with
      | top => trivial
      | coe b2 =>
        rw [hF1_b] at hbx
        rw [hF2_b] at hby
        change |(x : ℚ)| ≤ ((b1.1 : Dyadic) : ℚ) at hbx
        change |(y : ℚ)| ≤ ((b2.1 : Dyadic) : ℚ) at hby
        change |((x + y : Dyadic) : ℚ)| ≤ ((b1.1 + b2.1 : Dyadic) : ℚ)
        push_cast
        calc |(x : ℚ) + (y : ℚ)|
            ≤ |(x : ℚ)| + |(y : ℚ)| := abs_add_le _ _
          _ ≤ ((b1.1 : Dyadic) : ℚ) + ((b2.1 : Dyadic) : ℚ) := add_le_add hbx hby

/-- **Neg ⊆ self** — paper: `format(neg(e)) = format(e)`. -/
theorem neg_subset (F : Format) : -F.toSet ⊆ F.toSet := by
  intro z hz
  have h_neg_z : -z ∈ F := mem_toSet.mp hz
  have h := neg_mem h_neg_z
  rw [neg_neg] at h
  exact mem_toSet.mpr h

/-- **Abs ⊆ self** — paper: `format(abs(e)) = format(e)`. -/
theorem abs_subset (F : Format) :
    (Dyadic.abs '' F.toSet) ⊆ F.toSet := by
  rintro z ⟨x, hx, rfl⟩
  exact mem_toSet.mpr (abs_mem (mem_toSet.mp hx))

end Format

end Mpfx2
