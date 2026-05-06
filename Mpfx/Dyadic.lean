import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Mathlib.Tactic

namespace Mpfx

/-- A real number is *dyadic* if it has the form `c · 2^e` for some integers `c, e`.
The decomposition is not unique: `c · 2^e = (2c) · 2^(e − 1)`. -/
def IsDyadic (x : ℝ) : Prop := ∃ c e : ℤ, x = (c : ℝ) * (2 : ℝ) ^ e

namespace IsDyadic

@[simp] theorem zero : IsDyadic 0 := ⟨0, 0, by simp⟩

@[simp] theorem one : IsDyadic 1 := ⟨1, 0, by simp⟩

theorem of_int (n : ℤ) : IsDyadic (n : ℝ) := ⟨n, 0, by simp⟩

theorem of_nat (n : ℕ) : IsDyadic (n : ℝ) := ⟨n, 0, by simp⟩

theorem neg {x : ℝ} (h : IsDyadic x) : IsDyadic (-x) := by
  obtain ⟨c, e, rfl⟩ := h
  exact ⟨-c, e, by push_cast; ring⟩

theorem mul {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x * y) := by
  obtain ⟨c₁, e₁, rfl⟩ := hx
  obtain ⟨c₂, e₂, rfl⟩ := hy
  refine ⟨c₁ * c₂, e₁ + e₂, ?_⟩
  rw [zpow_add₀ (two_ne_zero)]
  push_cast
  ring

private theorem add_aux (c₁ c₂ e₁ e₂ : ℤ) (h : e₁ ≤ e₂) :
    (c₁ : ℝ) * (2 : ℝ) ^ e₁ + (c₂ : ℝ) * (2 : ℝ) ^ e₂
      = ((c₁ + c₂ * 2 ^ (e₂ - e₁).toNat : ℤ) : ℝ) * (2 : ℝ) ^ e₁ := by
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  have hsub : ((e₂ - e₁).toNat : ℤ) = e₂ - e₁ := Int.toNat_of_nonneg (by omega)
  have key : (2 : ℝ) ^ e₂ = (2 : ℝ) ^ (e₂ - e₁).toNat * (2 : ℝ) ^ e₁ := by
    rw [show ((2:ℝ) ^ (e₂ - e₁).toNat : ℝ) = (2 : ℝ) ^ ((e₂ - e₁).toNat : ℤ) from
        (zpow_natCast _ _).symm, ← zpow_add₀ h2, hsub]
    congr 1; ring
  rw [key]
  push_cast
  ring

theorem add {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x + y) := by
  obtain ⟨c₁, e₁, rfl⟩ := hx
  obtain ⟨c₂, e₂, rfl⟩ := hy
  rcases le_total e₁ e₂ with h | h
  · exact ⟨c₁ + c₂ * 2 ^ (e₂ - e₁).toNat, e₁, add_aux c₁ c₂ e₁ e₂ h⟩
  · refine ⟨c₂ + c₁ * 2 ^ (e₁ - e₂).toNat, e₂, ?_⟩
    rw [add_comm]
    exact add_aux c₂ c₁ e₂ e₁ h

theorem sub {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x - y) := by
  rw [sub_eq_add_neg]
  exact add hx (neg hy)

theorem zpow_two (e : ℤ) : IsDyadic ((2 : ℝ) ^ e) := ⟨1, e, by simp⟩

end IsDyadic

/-- The subring of dyadic reals. -/
def dyadicSubring : Subring ℝ where
  carrier := { x | IsDyadic x }
  zero_mem' := IsDyadic.zero
  one_mem' := IsDyadic.one
  add_mem' := IsDyadic.add
  neg_mem' := IsDyadic.neg
  mul_mem' := IsDyadic.mul

/-- The type of dyadic numbers, as a subtype of ℝ. -/
abbrev Dyadic : Type := dyadicSubring

namespace Dyadic

@[simp] theorem coe_isDyadic (d : Dyadic) : IsDyadic (d : ℝ) := d.2

/-- Build a dyadic from `(c : ℤ)` and `(e : ℤ)`: the value `c · 2^e`. -/
noncomputable def ofIntZpow (c e : ℤ) : Dyadic :=
  ⟨(c : ℝ) * (2 : ℝ) ^ e, c, e, rfl⟩

@[simp] theorem coe_ofIntZpow (c e : ℤ) :
    ((ofIntZpow c e : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ) ^ e := rfl

/-- `x` has precision at most `p` (`⊤` = no constraint): there exist `c, e : ℤ`
with `x = c · 2^e` and `|c| < 2^p`. Matches the paper's `precisionAtMost`. -/
def precisionAtMost : ℕ∞ → Dyadic → Prop
  | ⊤, _ => True
  | (p : ℕ), x => ∃ c e : ℤ, (x : ℝ) = (c : ℝ) * (2 : ℝ) ^ e ∧ |c| < (2 : ℤ) ^ p

/-- `x` has quantum at least `2^e` (`⊥` = no constraint): there exists `c : ℤ`
with `x = c · 2^e`. Matches the paper's `quantumAtLeast`. -/
def quantumAtLeast : WithBot ℤ → Dyadic → Prop
  | ⊥, _ => True
  | (e : ℤ), x => ∃ c : ℤ, (x : ℝ) = (c : ℝ) * (2 : ℝ) ^ e

@[simp] theorem precisionAtMost_top (x : Dyadic) : precisionAtMost ⊤ x := trivial

@[simp] theorem quantumAtLeast_bot (x : Dyadic) : quantumAtLeast ⊥ x := trivial

theorem precisionAtMost_coe (p : ℕ) (x : Dyadic) :
    precisionAtMost (p : ℕ∞) x ↔
      ∃ c e : ℤ, (x : ℝ) = (c : ℝ) * (2 : ℝ) ^ e ∧ |c| < (2 : ℤ) ^ p := Iff.rfl

theorem quantumAtLeast_coe (e : ℤ) (x : Dyadic) :
    quantumAtLeast (e : WithBot ℤ) x ↔ ∃ c : ℤ, (x : ℝ) = (c : ℝ) * (2 : ℝ) ^ e := Iff.rfl

/-- Monotonicity of `precisionAtMost` in `p`. -/
theorem precisionAtMost_mono {p₁ p₂ : ℕ∞} (h : p₁ ≤ p₂) {x : Dyadic} :
    precisionAtMost p₁ x → precisionAtMost p₂ x := by
  match p₁, p₂ with
  | _, ⊤ => intro _; trivial
  | ⊤, (_ : ℕ) => simp at h
  | (n₁ : ℕ), (n₂ : ℕ) =>
    intro ⟨c, e, hx, hc⟩
    refine ⟨c, e, hx, lt_of_lt_of_le hc ?_⟩
    have hn : n₁ ≤ n₂ := WithTop.coe_le_coe.mp h
    exact pow_le_pow_right₀ (by norm_num) hn

/-- Antitonicity of `quantumAtLeast` in `e` (smaller `e` is a weaker constraint). -/
theorem quantumAtLeast_anti {e₁ e₂ : WithBot ℤ} (h : e₂ ≤ e₁) {x : Dyadic} :
    quantumAtLeast e₁ x → quantumAtLeast e₂ x := by
  match e₁, e₂ with
  | _, ⊥ => intro _; trivial
  | ⊥, (_ : ℤ) => simp at h
  | (n₁ : ℤ), (n₂ : ℤ) =>
    intro ⟨c, hx⟩
    have hn : n₂ ≤ n₁ := WithBot.coe_le_coe.mp h
    refine ⟨c * 2 ^ (n₁ - n₂).toNat, ?_⟩
    have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
    have hsub : ((n₁ - n₂).toNat : ℤ) = n₁ - n₂ := Int.toNat_of_nonneg (by omega)
    have key : (2 : ℝ) ^ n₁ = (2 : ℝ) ^ (n₁ - n₂).toNat * (2 : ℝ) ^ n₂ := by
      rw [show ((2:ℝ) ^ (n₁ - n₂).toNat : ℝ) = (2 : ℝ) ^ ((n₁ - n₂).toNat : ℤ) from
          (zpow_natCast _ _).symm, ← zpow_add₀ h2, hsub]
      congr 1; ring
    rw [hx, key]
    push_cast
    ring

end Dyadic

end Mpfx
