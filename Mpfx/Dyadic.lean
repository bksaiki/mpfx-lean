import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Mpfx.Utils

namespace Mpfx

/-- A real number is *dyadic* if it has the form `c · 2^e` for some integers `c, e`.
The decomposition is not unique: `c · 2^e = (2c) · 2^(e − 1)`. -/
def IsDyadic (x : ℝ) : Prop := ∃ c e : ℤ, x = (c : ℝ) * (2 : ℝ) ^ e

namespace IsDyadic

@[simp] theorem zero : IsDyadic 0 := ⟨0, 0, by simp⟩

@[simp] theorem one : IsDyadic 1 := ⟨1, 0, by simp⟩

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
  rw [two_zpow_split_toNat h]
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

/-- The half-dyadic, `1/2 = 1·2^(-1)`. -/
noncomputable def half : Dyadic := ofIntZpow 1 (-1)

@[simp] theorem coe_half : (half : ℝ) = 1/2 := by
  change ((1 : ℤ) : ℝ) * (2 : ℝ) ^ (-1 : ℤ) = 1/2
  rw [zpow_neg_one]
  push_cast
  ring

/-- Midpoint of two dyadics: `(y₁ + y₂)/2`. -/
noncomputable def midpoint (y₁ y₂ : Dyadic) : Dyadic := (y₁ + y₂) * half

theorem coe_midpoint (y₁ y₂ : Dyadic) :
    ((midpoint y₁ y₂ : Dyadic) : ℝ) = ((y₁ : ℝ) + (y₂ : ℝ)) / 2 := by
  change (((y₁ + y₂) * half : Dyadic) : ℝ) = _
  push_cast
  rw [coe_half]
  ring

theorem midpoint_comm (y₁ y₂ : Dyadic) :
    midpoint y₁ y₂ = midpoint y₂ y₁ := by
  apply Subtype.ext
  rw [coe_midpoint, coe_midpoint]; ring

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

/-- If `x = c · 2^e` with `|c| ≤ 2^p`, then `precisionAtMost p x` (for `p ≥ 1`).
The boundary case `|c| = 2^p` forces `c = ±2^p`, and we can rewrite
`x = ±1 · 2^(e+p)` to recover a representation with `|c'| = 1 < 2^p`. -/
theorem precisionAtMost_of_abs_le {p : ℕ} (hp : 1 ≤ p) {x : Dyadic} (c e : ℤ)
    (hx : (x : ℝ) = (c : ℝ) * (2 : ℝ) ^ e) (hc : |c| ≤ (2 : ℤ) ^ p) :
    precisionAtMost (p : ℕ∞) x := by
  rw [precisionAtMost_coe]
  rcases lt_or_eq_of_le hc with hlt | heq
  · exact ⟨c, e, hx, hlt⟩
  · -- |c| = 2^p so c = ±2^p
    have h2p_nonneg : (0 : ℤ) ≤ (2 : ℤ) ^ p := by positivity
    have hsign : c = (2 : ℤ) ^ p ∨ c = -((2 : ℤ) ^ p) := (abs_eq h2p_nonneg).mp heq
    have hone_lt : (1 : ℤ) < (2 : ℤ) ^ p := by
      have : (2 : ℤ) ^ 0 < (2 : ℤ) ^ p := pow_lt_pow_right₀ (by norm_num) hp
      simpa using this
    have h2ne : (2 : ℝ) ≠ 0 := two_ne_zero
    rcases hsign with hpos | hneg
    · refine ⟨1, e + (p : ℤ), ?_, ?_⟩
      · rw [hx, hpos, zpow_add₀ h2ne]
        push_cast
        simp only [← zpow_natCast (2 : ℝ) p]
        ring
      · simpa using hone_lt
    · refine ⟨-1, e + (p : ℤ), ?_, ?_⟩
      · rw [hx, hneg, zpow_add₀ h2ne]
        push_cast
        simp only [← zpow_natCast (2 : ℝ) p]
        ring
      · have : |(-1 : ℤ)| = 1 := by decide
        rw [this]; exact hone_lt

/-- `(c, e)` is a representation of `y` at *exactly* `p` binary digits:
`y = c · 2^e` with `2^(p-1) ≤ |c| < 2^p` (so the significand `c` has exactly
`p` bits when `y ≠ 0`).

For nonzero `y` representable at `p` bits, the `(c, e)` pair satisfying this
predicate is unique. -/
def IsRepresentableAtP (p : ℕ) (c e : ℤ) (y : Dyadic) : Prop :=
  (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ e ∧
  (2 : ℤ) ^ (p - 1) ≤ |c| ∧ |c| < (2 : ℤ) ^ p

/-- The dyadic value `3 · 2^k` has precision at most 2 (significand `3` fits
in `|c| < 2^2 = 4`). Used as a precision-2 witness in `hp_F₂`-derivation. -/
theorem precisionAtMost_two_three_zpow (k : ℤ) :
    precisionAtMost (2 : ℕ∞) (Dyadic.ofIntZpow 3 k) := by
  change ∃ c e : ℤ, _ ∧ |c| < (2 : ℤ)^2
  refine ⟨3, k, ?_, ?_⟩
  · rw [coe_ofIntZpow]
  · decide

/-- The dyadic value `3 · 2^k` is *not* representable at precision 1. The
significand `3` has two binary digits, and no rescaling reduces it to `±1` or
`0`. Used as a precision-2 witness to force `2 ≤ F₂.p` from a containment
hypothesis. -/
theorem not_precisionAtMost_one_three_zpow (k : ℤ) :
    ¬ precisionAtMost (1 : ℕ∞) (Dyadic.ofIntZpow 3 k) := by
  intro h
  have h' : ∃ c e : ℤ,
      ((Dyadic.ofIntZpow 3 k : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ)^e ∧
      |c| < (2 : ℤ)^1 := h
  obtain ⟨c, e, h_eq, hc⟩ := h'
  rw [coe_ofIntZpow] at h_eq
  -- h_eq : ((3 : ℤ) : ℝ) * (2 : ℝ)^k = (c : ℝ) * (2 : ℝ)^e
  -- hc : |c| < 2^1 = 2.
  have hc2 : |c| < 2 := by simpa using hc
  have hc_cases : c = -1 ∨ c = 0 ∨ c = 1 := by
    have habs := abs_lt.mp hc2
    omega
  have h2k_pos : (0 : ℝ) < (2 : ℝ)^k := zpow_pos (by norm_num) _
  have h2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
  rcases hc_cases with hc_n1 | hc_0 | hc_1
  · -- c = -1: -2^e = 3·2^k. LHS < 0, RHS > 0.
    subst hc_n1
    push_cast at h_eq
    nlinarith
  · -- c = 0: 0 = 3·2^k. RHS > 0.
    subst hc_0
    push_cast at h_eq
    nlinarith
  · -- c = 1: 2^e = 3·2^k. So 2^(e-k) = 3, but no integer power of 2 equals 3.
    subst hc_1
    push_cast at h_eq
    rw [one_mul] at h_eq
    have h_pow : (2 : ℝ) ^ (e - k) = 3 := by
      have h2k_ne : (2 : ℝ)^k ≠ 0 := ne_of_gt h2k_pos
      rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
      field_simp
      linarith
    rcases lt_or_ge (e - k) 0 with h_neg | h_nn
    · -- e - k < 0: 2^(e-k) ≤ 1/2 < 3.
      have h_le_neg1 : e - k ≤ -1 := by omega
      have h_lt : (2 : ℝ) ^ (e - k) ≤ (2 : ℝ) ^ (-1 : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h_le_neg1
      rw [h_pow] at h_lt
      norm_num at h_lt
    · -- e - k ≥ 0: 2^(e-k) is a power of 2 in ℕ; never equals 3.
      lift (e - k) to ℕ using h_nn with n hn
      rw [zpow_natCast] at h_pow
      have hn_int : (2 : ℕ)^n = 3 := by exact_mod_cast h_pow
      rcases Nat.lt_or_ge n 2 with h_lt | h_ge
      · interval_cases n
        · simp at hn_int
        · simp at hn_int
      · have hge4 : (4 : ℕ) ≤ (2 : ℕ)^n := by
          calc (4 : ℕ) = 2^2 := by norm_num
            _ ≤ 2^n := Nat.pow_le_pow_right (by norm_num) h_ge
        omega

/-- Auxiliary: any nonzero integer can be factored as `c' * 2^k` with `c'` odd
and `|c'| ≤ |c|`. Strong induction on `c.natAbs`. -/
private theorem Int.exists_odd_factor_aux : ∀ (n : ℕ) (c : ℤ),
    c.natAbs ≤ n → c ≠ 0 →
    ∃ k : ℕ, ∃ c' : ℤ, Odd c' ∧ c = c' * 2^k ∧ c'.natAbs ≤ c.natAbs := by
  intro n
  induction n with
  | zero =>
    intro c hle hne
    have : c.natAbs = 0 := Nat.le_zero.mp hle
    exact absurd (Int.natAbs_eq_zero.mp this) hne
  | succ n ih =>
    intro c hle hne
    rcases Int.even_or_odd c with hev | hod
    · -- c even: c = 2 * r, r has smaller natAbs.
      obtain ⟨r, hr⟩ := hev
      have hr_eq : c = 2 * r := by linarith
      have hr_ne : r ≠ 0 := by
        intro h; rw [h, mul_zero] at hr_eq; exact hne hr_eq
      have h2r_natAbs : (2 * r).natAbs = 2 * r.natAbs := by
        rw [Int.natAbs_mul]; rfl
      have hr_natAbs_lt : r.natAbs < c.natAbs := by
        rw [hr_eq, h2r_natAbs]
        have : 0 < r.natAbs := Int.natAbs_pos.mpr hr_ne
        omega
      have hr_natAbs_le : r.natAbs ≤ n := by omega
      obtain ⟨k, c', h_odd, h_eq, h_abs⟩ := ih r hr_natAbs_le hr_ne
      refine ⟨k + 1, c', h_odd, ?_, ?_⟩
      · rw [hr_eq, h_eq]; ring
      · omega
    · -- c odd: k = 0, c' = c.
      refine ⟨0, c, hod, ?_, le_refl _⟩
      simp

/-- Any nonzero integer factors as `c' * 2^k` with `c'` odd. -/
private theorem Int.exists_odd_factor {c₀ : ℤ} (hc : c₀ ≠ 0) :
    ∃ k : ℕ, ∃ c : ℤ, Odd c ∧ c₀ = c * 2^k ∧ c.natAbs ≤ c₀.natAbs :=
  Int.exists_odd_factor_aux c₀.natAbs c₀ (le_refl _) hc

/-- For any nonzero dyadic with precision at most `p`, there's a representation
`y = c·2^e` with `c` odd and `|c| < 2^p`. -/
theorem exists_odd_canonical_of_precisionAtMost {p : ℕ} {y : Dyadic}
    (hp : precisionAtMost (p : ℕ∞) y) (hy : (y : ℝ) ≠ 0) :
    ∃ c e : ℤ, ((y : ℝ) = c * (2 : ℝ)^e) ∧ Odd c ∧ |c| < (2 : ℤ)^p := by
  rw [precisionAtMost_coe] at hp
  obtain ⟨c₀, e₀, hy_eq, hc₀_lt⟩ := hp
  have hc₀_ne : c₀ ≠ 0 := by
    intro h; rw [h] at hy_eq; push_cast at hy_eq
    rw [zero_mul] at hy_eq; exact hy hy_eq
  obtain ⟨k, c, h_odd, hc_eq, h_natAbs⟩ := Int.exists_odd_factor hc₀_ne
  refine ⟨c, e₀ + k, ?_, h_odd, ?_⟩
  · rw [hy_eq, hc_eq]
    push_cast
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
    ring
  · -- |c| ≤ |c₀| < 2^p.
    have hc_le : |c| ≤ |c₀| := by
      rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]
      exact_mod_cast h_natAbs
    linarith

/-- A nonzero dyadic with `quantumAtLeast e` has absolute value at least `2^e`.
The smallest nonzero significand `c` is `±1`, giving `|c·2^e| = 2^e`. -/
theorem abs_ge_two_zpow_of_quantum {e : ℤ} {d : Dyadic}
    (hq : quantumAtLeast (e : WithBot ℤ) d) (hne : (d : ℝ) ≠ 0) :
    (2 : ℝ)^e ≤ |(d : ℝ)| := by
  rw [quantumAtLeast_coe] at hq
  obtain ⟨c, hc_eq⟩ := hq
  have h2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
  have hc_ne : c ≠ 0 := by
    intro h
    rw [h] at hc_eq
    push_cast at hc_eq
    rw [zero_mul] at hc_eq
    exact hne hc_eq
  have hc_abs : (1 : ℤ) ≤ |c| := by
    have := abs_pos.mpr hc_ne
    omega
  have habs : (1 : ℝ) ≤ |(c : ℝ)| := by
    rw [show |(c : ℝ)| = ((|c| : ℤ) : ℝ) by push_cast; rfl]
    exact_mod_cast hc_abs
  rw [hc_eq, abs_mul, abs_of_pos h2e_pos]
  calc (2 : ℝ)^e = 1 * (2 : ℝ)^e := by ring
    _ ≤ |(c : ℝ)| * (2 : ℝ)^e :=
        mul_le_mul_of_nonneg_right habs (le_of_lt h2e_pos)

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
    rw [hx, two_zpow_split_toNat hn]
    push_cast
    ring

end Dyadic

end Mpfx
