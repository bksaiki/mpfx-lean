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

/-- `y` is *odd at p bits*: `y` admits a representation `c · 2^e` where the
significand `c` has *exactly* `p` binary digits (`2^(p-1) ≤ |c| < 2^p`) and `c`
is odd. This is the parity used by RTO and RNE rounding to a `p`-bit format.

For nonzero `y` representable at `p` bits, the `(c, e)` pair with `|c| ∈ [2^(p-1), 2^p)`
is unique, so this predicate is well-defined. For `y = 0`, the predicate is false
(0 is conventionally even). For `y` whose minimum precision exceeds `p`, the
predicate is also false (no such representation exists). -/
def IsOddAtP (p : ℕ) (y : Dyadic) : Prop :=
  ∃ c e : ℤ, (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ e ∧
             (2 : ℤ) ^ (p - 1) ≤ |c| ∧ |c| < (2 : ℤ) ^ p ∧ Odd c

/-- `y` is *even at p bits*: dual of `IsOddAtP`. Either `y = 0` (conventionally
even at any precision) or `y` admits a representation `c · 2^e` with `c` having
exactly `p` bits and `c` even. -/
def IsEvenAtP (p : ℕ) (y : Dyadic) : Prop :=
  y = 0 ∨ ∃ c e : ℤ, (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ e ∧
                     (2 : ℤ) ^ (p - 1) ≤ |c| ∧ |c| < (2 : ℤ) ^ p ∧ Even c

@[simp] theorem isEvenAtP_zero (p : ℕ) : IsEvenAtP p 0 := Or.inl rfl

/-- **Lemma 5.3 core**: If `y` is representable at precision `w`, then at any
strictly higher precision `w + k` (`k ≥ 1`), `y` cannot have an odd `(w+k)`-bit
significand. Equivalently: precision-`w`-representable values are "even at
`w + k` bits" (their canonical `c` gets multiplied by at least `2^k`).

This is the key technical fact behind Lemma 5.3 (RTO digit-padding preserves
bracketing): the precision-`w` adjacents `y₁, y₂` of `x` are even at `w + k`
bits, so RTO at `w + k` (which picks the *odd* significand) cannot land on
either of them. -/
theorem precisionAtMost_not_isOddAtP {w k : ℕ} (hk : 1 ≤ k) {y : Dyadic}
    (hprec : precisionAtMost (w : ℕ∞) y) : ¬ IsOddAtP (w + k) y := by
  intro hodd
  obtain ⟨c₁, e₁, hy_eq₁, hlow, _hhigh, hc₁_odd⟩ := hodd
  rw [precisionAtMost_coe] at hprec
  obtain ⟨c₂, e₂, hy_eq₂, hc₂_low⟩ := hprec
  have heq_real : (c₁ : ℝ) * (2 : ℝ) ^ e₁ = (c₂ : ℝ) * (2 : ℝ) ^ e₂ := by
    rw [← hy_eq₁]; exact hy_eq₂
  have h2ne : (2 : ℝ) ≠ 0 := two_ne_zero
  have h2pos : (0 : ℝ) < 2 := by norm_num
  rcases lt_or_ge e₁ e₂ with he | he
  · -- e₁ < e₂: c₁ = c₂ * 2^(e₂-e₁) in ℤ. Since e₂-e₁ ≥ 1, c₁ is even.
    have h_nat : ((e₂ - e₁).toNat : ℤ) = e₂ - e₁ := Int.toNat_of_nonneg (by omega)
    have hd_pos : 1 ≤ (e₂ - e₁).toNat := by omega
    have heq_int : c₁ = c₂ * 2 ^ (e₂ - e₁).toNat := by
      have h_real : (c₁ : ℝ) = (c₂ : ℝ) * (2 : ℝ) ^ (e₂ - e₁).toNat := by
        rw [show ((2 : ℝ) ^ (e₂ - e₁).toNat : ℝ) = (2 : ℝ) ^ ((e₂ - e₁).toNat : ℤ) from
            (zpow_natCast _ _).symm, h_nat]
        have h_step : (c₂ : ℝ) * (2 : ℝ) ^ (e₂ - e₁) * (2 : ℝ) ^ e₁
            = (c₁ : ℝ) * (2 : ℝ) ^ e₁ := by
          rw [mul_assoc, ← zpow_add₀ h2ne, show e₂ - e₁ + e₁ = e₂ from by ring]
          exact heq_real.symm
        have h2e₁_pos : (0 : ℝ) < (2 : ℝ) ^ e₁ := zpow_pos h2pos _
        exact (mul_right_cancel₀ (ne_of_gt h2e₁_pos) h_step).symm
      exact_mod_cast h_real
    have h_even : Even c₁ := by
      rw [heq_int, show (e₂ - e₁).toNat = ((e₂ - e₁).toNat - 1) + 1 from by omega, pow_succ]
      exact ⟨c₂ * 2 ^ ((e₂ - e₁).toNat - 1), by ring⟩
    exact (Int.not_even_iff_odd.mpr hc₁_odd) h_even
  · -- e₁ ≥ e₂: c₂ = c₁ * 2^(e₁-e₂) in ℤ; |c₂| ≥ |c₁| ≥ 2^(w+k-1) ≥ 2^w, contradicting |c₂| < 2^w
    have h_nat : ((e₁ - e₂).toNat : ℤ) = e₁ - e₂ := Int.toNat_of_nonneg (by omega)
    have heq_int : c₂ = c₁ * 2 ^ (e₁ - e₂).toNat := by
      have h_real : (c₂ : ℝ) = (c₁ : ℝ) * (2 : ℝ) ^ (e₁ - e₂).toNat := by
        rw [show ((2 : ℝ) ^ (e₁ - e₂).toNat : ℝ) = (2 : ℝ) ^ ((e₁ - e₂).toNat : ℤ) from
            (zpow_natCast _ _).symm, h_nat]
        have h_step : (c₁ : ℝ) * (2 : ℝ) ^ (e₁ - e₂) * (2 : ℝ) ^ e₂
            = (c₂ : ℝ) * (2 : ℝ) ^ e₂ := by
          rw [mul_assoc, ← zpow_add₀ h2ne, show e₁ - e₂ + e₂ = e₁ from by ring]
          exact heq_real
        have h2e₂_pos : (0 : ℝ) < (2 : ℝ) ^ e₂ := zpow_pos h2pos _
        exact (mul_right_cancel₀ (ne_of_gt h2e₂_pos) h_step).symm
      exact_mod_cast h_real
    have h_abs : |c₂| = |c₁| * 2 ^ (e₁ - e₂).toNat := by
      rw [heq_int, abs_mul, abs_pow]; simp
    have h_pow_ge_one : (1 : ℤ) ≤ 2 ^ (e₁ - e₂).toNat := one_le_pow₀ (by norm_num)
    have h_c₁_le_c₂ : |c₁| ≤ |c₂| := by
      rw [h_abs]
      have : 0 ≤ |c₁| := abs_nonneg _
      nlinarith
    have h_c₁_ge : (2 : ℤ) ^ w ≤ |c₁| := by
      calc (2 : ℤ) ^ w
          ≤ (2 : ℤ) ^ (w + k - 1) := by
            apply pow_le_pow_right₀ (by norm_num); omega
        _ ≤ |c₁| := hlow
    linarith

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
