import Mpfx.Format.Defs
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

Special values follow IEEE 754 (`WithSpecial.mul`, `add`, `abs`, `neg`). The
inferred specials (`mulSpecials`, `addSpecials`, `absSpecials`, and negation
for `opNeg`) are exactly those the operation produces
(`special_mem_opMul_iff`, …), and `mul_subset`, `add_subset`, `neg_subset`,
`abs_subset` contain every result over `Format.values`. The `…_finite` forms
are the numeric containments over `Format.toSet`. With negation-closed
specials, `opNeg F = F` (`opNeg_of_negClosed`), but `|F|` can gain `+∞`.

## Result formats are plain `Format`s

`Format` carries only the three fields `(p, exp, b)` with **no** validity
invariants (those live in `FiniteFormat`/`ParityFormat`). So `opMul`/`opAdd`
produce a plain `Format` with no proof obligations, and need no `F.exp ≠ ⊥`
preconditions.

For the `⊕`-precision we use a *slightly tighter* formula than the paper:
`opAddPrec` returns `⌈log₂(⌊(b₁+b₂)/2^min(exp₁,exp₂)⌋ + 1)⌉` (floor inside),
matching the actual integer bound on `|c|`.  The `max 1 …` keeps `p ≥ 1`.
-/

namespace Mpfx

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

end Format

/-! ## IEEE 754 arithmetic on values

Exact (unrounded) `*`, `+`, `-` and `abs` on `WithSpecial Dyadic`, with the
IEEE 754 special-value rules: NaN propagates, `∞ × 0` and `∞ + (−∞)` are NaN,
an infinite product takes the XOR of the operand signs, and an infinite sum
keeps the infinity's sign. There is no signed zero, so `0` carries no sign. -/

namespace WithSpecial

/-- IEEE 754 multiplication of exact values. -/
def mul : WithSpecial Dyadic → WithSpecial Dyadic → WithSpecial Dyadic
  | .finite x, .finite y => .finite (x * y)
  | .special .nan, _ | _, .special .nan => .special .nan
  | .special (.inf a), .special (.inf b) => .special (.inf (xor a b))
  | .special (.inf a), .finite y | .finite y, .special (.inf a) =>
      if y = 0 then .special .nan else .special (.inf (xor a (decide ((y : ℚ) < 0))))

/-- IEEE 754 addition of exact values. -/
def add : WithSpecial Dyadic → WithSpecial Dyadic → WithSpecial Dyadic
  | .finite x, .finite y => .finite (x + y)
  | .special .nan, _ | _, .special .nan => .special .nan
  | .special (.inf a), .special (.inf b) => if a = b then .special (.inf a) else .special .nan
  | .special (.inf a), .finite _ | .finite _, .special (.inf a) => .special (.inf a)

/-- IEEE 754 absolute value: infinities become `+∞`, NaN stays NaN. -/
def abs : WithSpecial Dyadic → WithSpecial Dyadic
  | .finite x => .finite (Dyadic.abs x)
  | .special (.inf _) => .special (.inf false)
  | .special .nan => .special .nan

instance : Mul (WithSpecial Dyadic) := ⟨mul⟩
instance : Add (WithSpecial Dyadic) := ⟨add⟩
instance {α : Type} [Neg α] : Neg (WithSpecial α) := ⟨WithSpecial.neg⟩

@[simp] theorem finite_mul_finite (x y : Dyadic) :
    finite x * finite y = finite (x * y) := rfl

@[simp] theorem nan_mul (v : WithSpecial Dyadic) :
    (special .nan : WithSpecial Dyadic) * v = special .nan := by
  rcases v with _ | (_ | _) <;> rfl

@[simp] theorem mul_nan (u : WithSpecial Dyadic) : u * special .nan = special .nan := by
  rcases u with _ | (_ | _) <;> rfl

@[simp] theorem inf_mul_inf (a b : Bool) :
    (special (.inf a) : WithSpecial Dyadic) * special (.inf b) = special (.inf (xor a b)) :=
  rfl

@[simp] theorem inf_mul_finite (a : Bool) (y : Dyadic) :
    (special (.inf a) : WithSpecial Dyadic) * finite y =
      if y = 0 then special .nan else special (.inf (xor a (decide ((y : ℚ) < 0)))) := rfl

@[simp] theorem finite_mul_inf (x : Dyadic) (b : Bool) :
    finite x * special (.inf b) =
      if x = 0 then special .nan else special (.inf (xor b (decide ((x : ℚ) < 0)))) := rfl

@[simp] theorem finite_add_finite (x y : Dyadic) :
    finite x + finite y = finite (x + y) := rfl

@[simp] theorem nan_add (v : WithSpecial Dyadic) :
    (special .nan : WithSpecial Dyadic) + v = special .nan := by
  rcases v with _ | (_ | _) <;> rfl

@[simp] theorem add_nan (u : WithSpecial Dyadic) : u + special .nan = special .nan := by
  rcases u with _ | (_ | _) <;> rfl

@[simp] theorem inf_add_inf (a b : Bool) :
    (special (.inf a) : WithSpecial Dyadic) + special (.inf b) =
      if a = b then special (.inf a) else special .nan := rfl

@[simp] theorem inf_add_finite (a : Bool) (y : Dyadic) :
    (special (.inf a) : WithSpecial Dyadic) + finite y = special (.inf a) := rfl

@[simp] theorem finite_add_inf (x : Dyadic) (b : Bool) :
    finite x + special (.inf b) = special (.inf b) := rfl

@[simp] theorem neg_def {α : Type} [Neg α] (v : WithSpecial α) : -v = v.neg := rfl

/-- A product is finite exactly when both factors are. -/
theorem mul_eq_finite {u v : WithSpecial Dyadic} {z : Dyadic} :
    u * v = finite z ↔ ∃ x y, u = finite x ∧ v = finite y ∧ z = x * y := by
  constructor
  · intro h
    rcases u with x | (a | _) <;> rcases v with y | (b | _)
    · exact ⟨x, y, rfl, rfl, (finite.inj h).symm⟩
    all_goals
      simp only [inf_mul_finite, finite_mul_inf, inf_mul_inf,
        nan_mul, mul_nan] at h
      (try split_ifs at h) <;> cases h
  · rintro ⟨x, y, rfl, rfl, rfl⟩; rfl

/-- A sum is finite exactly when both summands are. -/
theorem add_eq_finite {u v : WithSpecial Dyadic} {z : Dyadic} :
    u + v = finite z ↔ ∃ x y, u = finite x ∧ v = finite y ∧ z = x + y := by
  constructor
  · intro h
    rcases u with x | (a | _) <;> rcases v with y | (b | _)
    · exact ⟨x, y, rfl, rfl, (finite.inj h).symm⟩
    all_goals
      simp only [inf_add_finite, finite_add_inf, inf_add_inf,
        nan_add, add_nan] at h
      (try split_ifs at h) <;> cases h
  · rintro ⟨x, y, rfl, rfl, rfl⟩; rfl

end WithSpecial

namespace Format

open scoped Pointwise

/-- A nontrivial format has a nonzero value of either sign. -/
theorem Nontrivial.exists_sign {F : Format} (h : F.Nontrivial) (b : Bool) :
    ∃ y : Dyadic, y ∈ F ∧ y ≠ 0 ∧ decide ((y : ℚ) < 0) = b := by
  obtain ⟨d, hd, hne⟩ := h
  have hne' : (d : ℚ) ≠ 0 := fun h => hne (Subtype.ext h)
  by_cases hb : decide ((d : ℚ) < 0) = b
  · exact ⟨d, hd, hne, hb⟩
  · refine ⟨-d, neg_mem hd, neg_ne_zero.mpr hne, ?_⟩
    have hneg : ((-d : Dyadic) : ℚ) = -(d : ℚ) := by push_cast; ring
    rw [hneg]
    rcases hne'.lt_or_gt with hlt | hgt
    · have h₁ : ¬ -(d : ℚ) < 0 := by linarith
      cases b <;> simp_all
    · have h₁ : -(d : ℚ) < 0 := by linarith
      have h₂ : ¬ (d : ℚ) < 0 := by linarith
      cases b <;> simp_all

/-! ## Inferred special values -/

/-- The specials of `F₁ * F₂`: NaN from a NaN operand or from `∞ × 0` (every
format holds `0`), and `±∞` from an infinity times an infinity or a nonzero
value, with the XOR of the signs. -/
def mulSpecials (F₁ F₂ : Format) : Set Special
  | .nan => .nan ∈ F₁.specials ∨ .nan ∈ F₂.specials ∨
      (∃ a, .inf a ∈ F₁.specials) ∨ (∃ b, .inf b ∈ F₂.specials)
  | .inf s => ∃ a b, xor a b = s ∧
      (.inf a ∈ F₁.specials ∧ (.inf b ∈ F₂.specials ∨ F₂.Nontrivial) ∨
        F₁.Nontrivial ∧ .inf b ∈ F₂.specials)

/-- The specials of `F₁ + F₂`: NaN from a NaN operand or from `∞ + (−∞)`, and
`±∞` from an infinity of that sign (plus `0`, or the same infinity). -/
def addSpecials (F₁ F₂ : Format) : Set Special
  | .nan => .nan ∈ F₁.specials ∨ .nan ∈ F₂.specials ∨
      ∃ a, .inf a ∈ F₁.specials ∧ .inf (!a) ∈ F₂.specials
  | .inf s => .inf s ∈ F₁.specials ∨ .inf s ∈ F₂.specials

/-- The specials of `|F|`: NaN from NaN, and `+∞` from either infinity. -/
def absSpecials (F : Format) : Set Special
  | .nan => .nan ∈ F.specials
  | .inf s => s = false ∧ ∃ a, .inf a ∈ F.specials

/-! ## Static inference operators (paper's `⊗`/`⊕`) -/

/-- Paper's `⊗`: multiplicative format inference.  Returns
`𝒜(p₁ + p₂, exp₁ + exp₂, b₁ × b₂)`.  The bound is constructed by `match`:
when both operand bounds are finite the result is their product (non-negative
by `mul_nonneg`); otherwise `⊤`. Specials by `mulSpecials`. -/
def opMul (F₁ F₂ : Format) : Format where
  p := F₁.p + F₂.p
  exp := F₁.exp + F₂.exp
  b := match F₁.b, F₂.b with
    | (b₁ : NonNegDyadic), (b₂ : NonNegDyadic) =>
        ((⟨b₁.1 * b₂.1, by
            have := mul_nonneg b₁.2 b₂.2
            push_cast at this ⊢
            exact this⟩ : NonNegDyadic) : Bound)
    | _, _ => ⊤
  specials := mulSpecials F₁ F₂

/-- Tight precision bound for `⊕`:
`p = ⌈log₂(⌊(b₁+b₂)/2^min(exp₁,exp₂)⌋ + 1)⌉`, or `⊤` when either operand bound
or exponent is infinite.  The floor ratio is computed over `ℝ`. -/
noncomputable def opAddPrec (F₁ F₂ : Format) : Prec :=
  match (F₁.b : Bound), (F₂.b : Bound),
        (min F₁.exp F₂.exp : QExp) with
  | (b₁ : NonNegDyadic), (b₂ : NonNegDyadic), (m : ℤ) =>
      (Nat.clog 2 (Int.toNat ⌊(((b₁.1 + b₂.1 : Dyadic) : ℝ)) / (2 : ℝ) ^ m⌋ + 1) : Prec)
  | _, _, _ => ⊤

/-- Paper's `⊕`: additive format inference.  Returns the inferred `Format`
`𝒜(opAddPrec, min(exp₁, exp₂), b₁ + b₂)`.  The bound is constructed by `match`
on both operand bounds (their sum, non-negative by `add_nonneg`), else `⊤`.
Specials by `addSpecials`. -/
noncomputable def opAdd (F₁ F₂ : Format) : Format where
  p := opAddPrec F₁ F₂
  exp := min F₁.exp F₂.exp
  b := match F₁.b, F₂.b with
    | (b₁ : NonNegDyadic), (b₂ : NonNegDyadic) =>
        ((⟨b₁.1 + b₂.1, by
            have := add_nonneg b₁.2 b₂.2
            push_cast at this ⊢
            exact this⟩ : NonNegDyadic) : Bound)
    | _, _ => ⊤
  specials := addSpecials F₁ F₂

/-- Negation: the numeric values are unchanged, the specials negated. -/
def opNeg (F : Format) : Format := { F with specials := {s | s.neg ∈ F.specials} }

/-- Absolute value: the numeric values are kept (`|F| ⊆ F`), the specials by
`absSpecials`. -/
def opAbs (F : Format) : Format := { F with specials := absSpecials F }

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
    · have : F₁.p + F₂.p = (⊤ : Prec) := by rw [hF1_p]; rfl
      rw [this]; trivial
    by_cases hF2_p : F₂.p = ⊤
    · have : F₁.p + F₂.p = (⊤ : Prec) := by rw [hF2_p]; cases F₁.p <;> rfl
      rw [this]; trivial
    obtain ⟨p1, hp1⟩ := WithTop.ne_top_iff_exists.mp hF1_p
    obtain ⟨p2, hp2⟩ := WithTop.ne_top_iff_exists.mp hF2_p
    simp only [Prec.some_eq_coe] at hp1 hp2
    rw [← hp1] at hpx
    rw [← hp2] at hpy
    rw [Dyadic.precisionAtMost_coe] at hpx hpy
    obtain ⟨c1, e1, hxeq, hc1⟩ := hpx
    obtain ⟨c2, e2, hyeq, hc2⟩ := hpy
    have h_p_eq : F₁.p + F₂.p = ((p1 + p2 : ℕ) : Prec) := by
      rw [← hp1, ← hp2]; rfl
    rw [h_p_eq, Dyadic.precisionAtMost_coe]
    refine ⟨c1 * c2, e1 + e2, ?_, ?_⟩
    · change ((x * y : Dyadic) : ℚ) = _
      push_cast
      rw [hxeq, hyeq, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
      ring
    · rw [pow_add, abs_mul]
      exact mul_lt_mul'' hc1 hc2 (abs_nonneg _) (abs_nonneg _)
  · -- quantumAtLeast (exp₁ + exp₂) (x * y)
    by_cases hF1_exp : F₁.exp = ⊥
    · have : F₁.exp + F₂.exp = (⊥ : QExp) := by rw [hF1_exp]; rfl
      rw [this]; trivial
    by_cases hF2_exp : F₂.exp = ⊥
    · have : F₁.exp + F₂.exp = (⊥ : QExp) := by rw [hF2_exp]; cases F₁.exp <;> rfl
      rw [this]; trivial
    obtain ⟨e1, he1⟩ := WithBot.ne_bot_iff_exists.mp hF1_exp
    obtain ⟨e2, he2⟩ := WithBot.ne_bot_iff_exists.mp hF2_exp
    have hqx' : Dyadic.quantumAtLeast (e1 : QExp) x := by rw [he1]; exact hqx
    have hqy' : Dyadic.quantumAtLeast (e2 : QExp) y := by rw [he2]; exact hqy
    rw [Dyadic.quantumAtLeast_coe] at hqx' hqy'
    obtain ⟨c1, hxeq⟩ := hqx'
    obtain ⟨c2, hyeq⟩ := hqy'
    have h_exp_eq : F₁.exp + F₂.exp = ((e1 + e2 : ℤ) : QExp) := by
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
  · have : min F₁.exp F₂.exp = (⊥ : QExp) := by
      rw [hF1_exp]; exact min_eq_left bot_le
    rw [this]; trivial
  by_cases hF2_exp : F₂.exp = ⊥
  · have : min F₁.exp F₂.exp = (⊥ : QExp) := by
      rw [hF2_exp]; exact min_eq_right bot_le
    rw [this]; trivial
  obtain ⟨e1, he1⟩ := WithBot.ne_bot_iff_exists.mp hF1_exp
  obtain ⟨e2, he2⟩ := WithBot.ne_bot_iff_exists.mp hF2_exp
  have hqx' : Dyadic.quantumAtLeast (e1 : QExp) x := by rw [he1]; exact hqx
  have hqy' : Dyadic.quantumAtLeast (e2 : QExp) y := by rw [he2]; exact hqy
  rw [Dyadic.quantumAtLeast_coe] at hqx' hqy'
  obtain ⟨c1, hxeq⟩ := hqx'
  obtain ⟨c2, hyeq⟩ := hqy'
  have h_min_eq : min F₁.exp F₂.exp = ((min e1 e2 : ℤ) : QExp) := by
    rw [← he1, ← he2, ← WithBot.coe_min]
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

/-- Finite form of `mul_subset`: `{x · y | x ∈ F₁, y ∈ F₂} ⊆ opMul F₁ F₂`. -/
theorem mul_subset_finite (F₁ F₂ : Format) :
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
  cases hF1_b : F₁.b using Bound.recTopCoe with
  | top => trivial
  | coe b₁ =>
    cases hF2_b : F₂.b using Bound.recTopCoe with
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
    (hF1_b : F₁.b = (b1 : Bound)) (hF2_b : F₂.b = (b2 : Bound))
    (hF1_exp : F₁.exp = (e1 : QExp)) (hF2_exp : F₂.exp = (e2 : QExp))
    (hx : x ∈ F₁) (hy : y ∈ F₂) :
    Dyadic.precisionAtMost
      ((Nat.clog 2
          (Int.toNat ⌊(((b1.1 + b2.1 : Dyadic) : ℝ)) / (2 : ℝ) ^ (min e1 e2)⌋ + 1) : Prec))
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
  · -- |c| < 2 ^ clog 2 (N+1)
    have h_natAbs_le : c.natAbs ≤ N := by
      have : (c.natAbs : ℤ) ≤ (N : ℤ) := by rw [Int.natCast_natAbs]; exact h_abs_c_le
      exact_mod_cast this
    have h_clog : N + 1 ≤ 2 ^ Nat.clog 2 (N + 1) :=
      Nat.le_pow_clog (by norm_num : 1 < 2) _
    rw [Int.abs_eq_natAbs]
    exact_mod_cast Nat.lt_of_lt_of_le (by omega : c.natAbs < N + 1) h_clog

/-- Finite form of `add_subset`: `{x + y | x ∈ F₁, y ∈ F₂} ⊆ opAdd F₁ F₂`. -/
theorem add_subset_finite (F₁ F₂ : Format) :
    F₁.toSet + F₂.toSet ⊆ (opAdd F₁ F₂).toSet := by
  rintro z ⟨x, hx, y, hy, rfl⟩
  have h_quant := add_inferred_q (mem_toSet.mp hx) (mem_toSet.mp hy)
  obtain ⟨_, _, hbx⟩ := mem_toSet.mp hx
  obtain ⟨_, _, hby⟩ := mem_toSet.mp hy
  refine ⟨?_, h_quant, ?_⟩
  · -- precisionAtMost (opAddPrec F₁ F₂) (x + y)
    change Dyadic.precisionAtMost (opAddPrec F₁ F₂) (x + y)
    unfold opAddPrec
    cases hF1_b : F₁.b using Bound.recTopCoe with
    | top => trivial
    | coe b1 =>
      cases hF2_b : F₂.b using Bound.recTopCoe with
      | top => trivial
      | coe b2 =>
        cases hF1_exp : F₁.exp using QExp.recBotCoe with
        | bot =>
          -- min ≤ ⊥ ⇒ min = ⊥ ⇒ ⊤ branch
          simp only [bot_inf_eq]; trivial
        | coe e1 =>
          cases hF2_exp : F₂.exp using QExp.recBotCoe with
          | bot =>
            simp only [inf_bot_eq]; trivial
          | coe e2 =>
            have h_min_eq : min (e1 : QExp) (e2 : QExp)
                = ((min e1 e2 : ℤ) : QExp) := (WithBot.coe_min e1 e2).symm
            rw [h_min_eq]
            have := add_prec_finite hF1_b hF2_b hF1_exp hF2_exp
              (mem_toSet.mp hx) (mem_toSet.mp hy)
            convert this using 3
  · -- boundOK of the matched sum bound
    change boundOK
        (match F₁.b, F₂.b with
          | (b₁ : NonNegDyadic), (b₂ : NonNegDyadic) => _
          | _, _ => ⊤) (x + y)
    cases hF1_b : F₁.b using Bound.recTopCoe with
    | top => trivial
    | coe b1 =>
      cases hF2_b : F₂.b using Bound.recTopCoe with
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

/-- Finite form of `neg_subset`: `-F ⊆ F`. -/
theorem neg_subset_finite (F : Format) : -F.toSet ⊆ F.toSet := by
  intro z hz
  have h_neg_z : -z ∈ F := mem_toSet.mp hz
  have h := neg_mem h_neg_z
  rw [neg_neg] at h
  exact mem_toSet.mpr h

/-- Finite form of `abs_subset`: `|F| ⊆ F`. -/
theorem abs_subset_finite (F : Format) :
    (Dyadic.abs '' F.toSet) ⊆ F.toSet := by
  rintro z ⟨x, hx, rfl⟩
  exact mem_toSet.mpr (abs_mem (mem_toSet.mp hx))

/-! ## Containment over values

The inferred specials are exactly those the operation produces, and the
inferred format contains every result, numeric or special. -/

/-- The specials of `opMul` are exactly the special products. -/
theorem special_mem_opMul_iff {F₁ F₂ : Format} {s : Special} :
    s ∈ (opMul F₁ F₂).specials ↔
      ∃ u ∈ F₁.values, ∃ v ∈ F₂.values, u * v = .special s := by
  constructor
  · intro h
    cases s with
    | nan =>
      rcases h with h | h | ⟨a, h⟩ | ⟨b, h⟩
      · exact ⟨.special .nan, h, .finite 0, F₂.zero_mem, WithSpecial.nan_mul _⟩
      · exact ⟨.finite 0, F₁.zero_mem, .special .nan, h, WithSpecial.mul_nan _⟩
      · exact ⟨.special (.inf a), h, .finite 0, F₂.zero_mem, by simp⟩
      · exact ⟨.finite 0, F₁.zero_mem, .special (.inf b), h, by simp⟩
    | inf s =>
      obtain ⟨a, b, rfl, ⟨ha, hb | hb⟩ | ⟨ha, hb⟩⟩ := h
      · exact ⟨.special (.inf a), ha, .special (.inf b), hb, rfl⟩
      · obtain ⟨y, hy, hy0, hsy⟩ := hb.exists_sign b
        exact ⟨.special (.inf a), ha, .finite y, hy, by simp [hy0, hsy]⟩
      · obtain ⟨x, hx, hx0, hsx⟩ := ha.exists_sign a
        exact ⟨.finite x, hx, .special (.inf b), hb, by simp [hx0, hsx, Bool.xor_comm]⟩
  · rintro ⟨u, hu, v, hv, h⟩
    rcases u with x | (a | _) <;> rcases v with y | (b | _)
    · exact absurd h (by simp)
    · by_cases hx : x = 0
      · simp only [WithSpecial.finite_mul_inf, if_pos hx, WithSpecial.special.injEq] at h
        subst h; exact Or.inr (Or.inr (Or.inr ⟨b, hv⟩))
      · simp only [WithSpecial.finite_mul_inf, if_neg hx, WithSpecial.special.injEq] at h
        subst h
        exact ⟨decide ((x : ℚ) < 0), b, Bool.xor_comm _ _, Or.inr ⟨⟨x, hu, hx⟩, hv⟩⟩
    · simp only [WithSpecial.mul_nan, WithSpecial.special.injEq] at h
      subst h; exact Or.inr (Or.inl hv)
    · by_cases hy : y = 0
      · simp only [WithSpecial.inf_mul_finite, if_pos hy, WithSpecial.special.injEq] at h
        subst h; exact Or.inr (Or.inr (Or.inl ⟨a, hu⟩))
      · simp only [WithSpecial.inf_mul_finite, if_neg hy, WithSpecial.special.injEq] at h
        subst h
        exact ⟨a, decide ((y : ℚ) < 0), rfl, Or.inl ⟨hu, Or.inr ⟨y, hv, hy⟩⟩⟩
    · simp only [WithSpecial.inf_mul_inf, WithSpecial.special.injEq] at h
      subst h; exact ⟨a, b, rfl, Or.inl ⟨hu, Or.inl hv⟩⟩
    · simp only [WithSpecial.mul_nan, WithSpecial.special.injEq] at h
      subst h; exact Or.inr (Or.inl hv)
    all_goals
      simp only [WithSpecial.nan_mul, WithSpecial.special.injEq] at h
      subst h; exact Or.inl hu

/-- **Mul ⊆ inferred** (paper's `⊗`): the inferred format contains every IEEE product,
numeric or special. -/
theorem mul_subset (F₁ F₂ : Format) :
    F₁.values * F₂.values ⊆ (opMul F₁ F₂).values := by
  rintro w ⟨u, hu, v, hv, rfl⟩
  change u * v ∈ _
  cases h : u * v with
  | finite z =>
    obtain ⟨x, y, rfl, rfl, rfl⟩ := WithSpecial.mul_eq_finite.mp h
    exact mul_subset_finite F₁ F₂ ⟨x, hu, y, hv, rfl⟩
  | special s => exact special_mem_opMul_iff.mpr ⟨u, hu, v, hv, h⟩

/-- The specials of `opAdd` are exactly the special sums. -/
theorem special_mem_opAdd_iff {F₁ F₂ : Format} {s : Special} :
    s ∈ (opAdd F₁ F₂).specials ↔
      ∃ u ∈ F₁.values, ∃ v ∈ F₂.values, u + v = .special s := by
  constructor
  · intro h
    cases s with
    | nan =>
      rcases h with h | h | ⟨a, ha, hb⟩
      · exact ⟨.special .nan, h, .finite 0, F₂.zero_mem, WithSpecial.nan_add _⟩
      · exact ⟨.finite 0, F₁.zero_mem, .special .nan, h, WithSpecial.add_nan _⟩
      · exact ⟨.special (.inf a), ha, .special (.inf !a), hb, by simp⟩
    | inf s =>
      rcases h with h | h
      · exact ⟨.special (.inf s), h, .finite 0, F₂.zero_mem, rfl⟩
      · exact ⟨.finite 0, F₁.zero_mem, .special (.inf s), h, rfl⟩
  · rintro ⟨u, hu, v, hv, h⟩
    rcases u with x | (a | _) <;> rcases v with y | (b | _)
    · exact absurd h (by simp)
    · simp only [WithSpecial.finite_add_inf, WithSpecial.special.injEq] at h
      subst h; exact Or.inr hv
    · simp only [WithSpecial.add_nan, WithSpecial.special.injEq] at h
      subst h; exact Or.inr (Or.inl hv)
    · simp only [WithSpecial.inf_add_finite, WithSpecial.special.injEq] at h
      subst h; exact Or.inl hu
    · by_cases hab : a = b
      · simp only [WithSpecial.inf_add_inf, if_pos hab, WithSpecial.special.injEq] at h
        subst h; exact Or.inl hu
      · simp only [WithSpecial.inf_add_inf, if_neg hab, WithSpecial.special.injEq] at h
        subst h
        refine Or.inr (Or.inr ⟨a, hu, ?_⟩)
        rwa [show b = !a by cases a <;> cases b <;> simp_all] at hv
    · simp only [WithSpecial.add_nan, WithSpecial.special.injEq] at h
      subst h; exact Or.inr (Or.inl hv)
    all_goals
      simp only [WithSpecial.nan_add, WithSpecial.special.injEq] at h
      subst h; exact Or.inl hu

/-- **Add ⊆ inferred** (paper's `⊕`): the inferred format contains every IEEE sum, numeric
or special. -/
theorem add_subset (F₁ F₂ : Format) :
    F₁.values + F₂.values ⊆ (opAdd F₁ F₂).values := by
  rintro w ⟨u, hu, v, hv, rfl⟩
  change u + v ∈ _
  cases h : u + v with
  | finite z =>
    obtain ⟨x, y, rfl, rfl, rfl⟩ := WithSpecial.add_eq_finite.mp h
    exact add_subset_finite F₁ F₂ ⟨x, hu, y, hv, rfl⟩
  | special s => exact special_mem_opAdd_iff.mpr ⟨u, hu, v, hv, h⟩

/-- **Neg ⊆ inferred**: the inferred format contains every negated value. -/
theorem neg_subset (F : Format) : -F.values ⊆ (opNeg F).values := by
  rintro (d | s) h
  · exact (mem_neg_iff F d).mp h
  · exact h

/-- With negation-closed specials, negation preserves the format (the paper's
`format(neg(e)) = format(e)`). -/
theorem opNeg_of_negClosed {F : Format} (hF : F.NegClosed) : opNeg F = F := by
  obtain ⟨p, e, b, S⟩ := F
  simp only [opNeg, mk.injEq, true_and]
  ext s
  exact ⟨fun h => by simpa using hF _ h, fun h => hF s h⟩

/-- The specials of `opAbs` are exactly the absolute values of specials. -/
theorem special_mem_opAbs_iff {F : Format} {s : Special} :
    s ∈ (opAbs F).specials ↔ ∃ u ∈ F.values, WithSpecial.abs u = .special s := by
  constructor
  · intro h
    cases s with
    | nan => exact ⟨.special .nan, h, rfl⟩
    | inf s =>
      obtain ⟨rfl, a, ha⟩ := h
      exact ⟨.special (.inf a), ha, rfl⟩
  · rintro ⟨u, hu, h⟩
    rcases u with x | (a | _)
    · exact absurd h (by simp [WithSpecial.abs])
    · simp only [WithSpecial.abs, WithSpecial.special.injEq] at h
      subst h; exact ⟨rfl, a, hu⟩
    · simp only [WithSpecial.abs, WithSpecial.special.injEq] at h
      subst h; exact hu

/-- **Abs ⊆ inferred**: the inferred format contains every IEEE absolute
value, numeric or special. -/
theorem abs_subset (F : Format) :
    WithSpecial.abs '' F.values ⊆ (opAbs F).values := by
  rintro w ⟨u, hu, rfl⟩
  cases h : WithSpecial.abs u with
  | finite z =>
    rcases u with x | (_ | _) <;> simp only [WithSpecial.abs, WithSpecial.finite.injEq,
      reduceCtorEq] at h
    subst h
    exact abs_mem (F := F) hu
  | special s => exact special_mem_opAbs_iff.mpr ⟨u, hu, h⟩

end Format

end Mpfx
