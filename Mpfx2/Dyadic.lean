import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Mathlib.Tactic
import Mpfx2.Utils

namespace Mpfx2

/-- A real number is *dyadic* if it has the form `c · 2^e` for some integers `c, e`.
The decomposition is not unique: `c · 2^e = (2c) · 2^(e − 1)`. -/
def IsDyadic (x : ℝ) : Prop := ∃ c e : ℤ, x = (c : ℝ) * (2 : ℝ) ^ e

namespace IsDyadic

private theorem add_aux (c₁ c₂ e₁ e₂ : ℤ) (h : e₁ ≤ e₂) :
    (c₁ : ℝ) * (2 : ℝ) ^ e₁ + (c₂ : ℝ) * (2 : ℝ) ^ e₂
      = ((c₁ + c₂ * 2 ^ (e₂ - e₁).toNat : ℤ) : ℝ) * (2 : ℝ) ^ e₁ := by
  rw [two_zpow_split_toNat h]
  push_cast; ring

theorem zero : IsDyadic 0 := ⟨0, 0, by simp⟩

theorem one : IsDyadic 1 := ⟨1, 0, by simp⟩

theorem neg {x : ℝ} (h : IsDyadic x) : IsDyadic (-x) := by
  obtain ⟨c, e, rfl⟩ := h
  exact ⟨-c, e, by push_cast; ring⟩

theorem mul {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x * y) := by
  obtain ⟨c₁, e₁, rfl⟩ := hx
  obtain ⟨c₂, e₂, rfl⟩ := hy
  refine ⟨c₁ * c₂, e₁ + e₂, ?_⟩
  rw [zpow_add₀ two_ne_zero]
  push_cast; ring

theorem add {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x + y) := by
  obtain ⟨c₁, e₁, rfl⟩ := hx
  obtain ⟨c₂, e₂, rfl⟩ := hy
  rcases le_total e₁ e₂ with h | h
  · exact ⟨c₁ + c₂ * 2 ^ (e₂ - e₁).toNat, e₁, add_aux c₁ c₂ e₁ e₂ h⟩
  · refine ⟨c₂ + c₁ * 2 ^ (e₁ - e₂).toNat, e₂, ?_⟩
    rw [add_comm]
    exact add_aux c₂ c₁ e₂ e₁ h

end IsDyadic

/-- The subring of dyadic reals. -/
def dyadicSubring : Subring ℝ where
  carrier := { x | IsDyadic x }
  zero_mem' := IsDyadic.zero
  one_mem' := IsDyadic.one
  add_mem' := IsDyadic.add
  neg_mem' := IsDyadic.neg
  mul_mem' := IsDyadic.mul

/-- The type of dyadic numbers, as a subtype of ℝ.

Defined in §3.1. -/
abbrev Dyadic : Type := dyadicSubring

namespace Dyadic

/-- Build a dyadic from `(c, e) : ℤ × ℤ`: the value `c · 2^e`. -/
noncomputable def ofIntZpow (c e : ℤ) : Dyadic :=
  ⟨(c : ℝ) * (2 : ℝ) ^ e, c, e, rfl⟩

@[simp] theorem coe_ofIntZpow (c e : ℤ) :
    ((ofIntZpow c e : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ) ^ e := rfl

/-- `x` has precision at most `p` (`⊤` = no constraint): there exist `c, e : ℤ`
with `x = c · 2^e` and `|c| < 2^p`. -/
def precisionAtMost : WithTop ℕ+ → Dyadic → Prop
  | ⊤, _ => True
  | (p : ℕ+), x => ∃ c e : ℤ, (x : ℝ) = (c : ℝ) * (2 : ℝ) ^ e ∧ |c| < (2 : ℤ) ^ (p : ℕ)

/-- `x` has quantum at least `2^e` (`⊥` = no constraint): there exists `c : ℤ`
with `x = c · 2^e`. -/
def quantumAtLeast : WithBot ℤ → Dyadic → Prop
  | ⊥, _ => True
  | (e : ℤ), x => ∃ c : ℤ, (x : ℝ) = (c : ℝ) * (2 : ℝ) ^ e

@[simp] theorem precisionAtMost_top (x : Dyadic) : precisionAtMost ⊤ x := trivial

@[simp] theorem quantumAtLeast_bot (x : Dyadic) : quantumAtLeast ⊥ x := trivial

theorem precisionAtMost_coe (p : ℕ+) (x : Dyadic) :
    precisionAtMost (p : WithTop ℕ+) x ↔
      ∃ c e : ℤ, (x : ℝ) = (c : ℝ) * (2 : ℝ) ^ e ∧ |c| < (2 : ℤ) ^ (p : ℕ) := Iff.rfl

theorem quantumAtLeast_coe (e : ℤ) (x : Dyadic) :
    quantumAtLeast (e : WithBot ℤ) x ↔
      ∃ c : ℤ, (x : ℝ) = (c : ℝ) * (2 : ℝ) ^ e := Iff.rfl

end Dyadic

/-- Non-negative dyadics: a `Dyadic` whose underlying real is `≥ 0`. Used as
the carrier of magnitude bounds in `Format`. -/
abbrev NonNegDyadic : Type := { d : Dyadic // 0 ≤ (d : ℝ) }

end Mpfx2
