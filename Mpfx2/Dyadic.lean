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

/-- `(c, e)` is a representation of `y` at *exactly* `p` binary digits:
`y = c · 2^e` with `2^(p-1) ≤ |c| < 2^p`. For nonzero `y` representable
at `p` bits, the `(c, e)` pair is unique. -/
def IsRepresentableAtP (p : ℕ) (c e : ℤ) (y : Dyadic) : Prop :=
  (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ e ∧
  (2 : ℤ) ^ (p - 1) ≤ |c| ∧ |c| < (2 : ℤ) ^ p

/-- If `y = c · 2^e` with `|c| ≤ 2^p`, then `precisionAtMost p y`. The
boundary case `|c| = 2^p` forces `c = ±2^p`; renormalize to
`y = ±1 · 2^(e+p)` to recover a strict-inequality witness. -/
theorem precisionAtMost_of_abs_le {p : ℕ+} {x : Dyadic} (c e : ℤ)
    (hx : (x : ℝ) = (c : ℝ) * (2 : ℝ) ^ e) (hc : |c| ≤ (2 : ℤ) ^ (p : ℕ)) :
    precisionAtMost ((p : ℕ+) : WithTop ℕ+) x := by
  rw [precisionAtMost_coe]
  rcases lt_or_eq_of_le hc with hlt | heq
  · exact ⟨c, e, hx, hlt⟩
  · have h2p_nonneg : (0 : ℤ) ≤ (2 : ℤ) ^ (p : ℕ) := by positivity
    have hsign : c = (2 : ℤ) ^ (p : ℕ) ∨ c = -((2 : ℤ) ^ (p : ℕ)) :=
      (abs_eq h2p_nonneg).mp heq
    have hp_pos : 1 ≤ (p : ℕ) := p.pos
    have hone_lt : (1 : ℤ) < (2 : ℤ) ^ (p : ℕ) := by
      have : (2 : ℤ) ^ 0 < (2 : ℤ) ^ (p : ℕ) := pow_lt_pow_right₀ (by norm_num) hp_pos
      simpa using this
    have h2ne : (2 : ℝ) ≠ 0 := two_ne_zero
    rcases hsign with hpos | hneg
    · refine ⟨1, e + (p : ℤ), ?_, ?_⟩
      · rw [hx, hpos, zpow_add₀ h2ne]
        push_cast
        simp only [← zpow_natCast (2 : ℝ) (p : ℕ)]
        ring
      · simpa using hone_lt
    · refine ⟨-1, e + (p : ℤ), ?_, ?_⟩
      · rw [hx, hneg, zpow_add₀ h2ne]
        push_cast
        simp only [← zpow_natCast (2 : ℝ) (p : ℕ)]
        ring
      · have habs : |(-1 : ℤ)| = 1 := by decide
        rw [habs]; exact hone_lt

/-- `IsRepresentableAtP n c e y` implies `y ≠ 0` (since `|c| ≥ 1`). -/
theorem IsRepresentableAtP.ne_zero {n : ℕ} {c e : ℤ} {y : Dyadic}
    (h : IsRepresentableAtP n c e y) : (y : ℝ) ≠ 0 := by
  obtain ⟨hyeq, hc_lo, _⟩ := h
  intro h0; rw [h0] at hyeq
  have h2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have hc_zero : (c : ℝ) = 0 := by
    rcases mul_eq_zero.mp hyeq.symm with h | h
    · exact h
    · linarith
  have hc_zero_int : c = 0 := by exact_mod_cast hc_zero
  rw [hc_zero_int, abs_zero] at hc_lo
  have hpos : (1 : ℤ) ≤ (2 : ℤ) ^ (n - 1) := one_le_pow₀ (by norm_num)
  linarith

/-- If `(c, e)` represents `y` with `|c| ∈ [2^(p-1), 2^p)`, then `(c, e)` is the
IsRepresentableAtP form for `y` at exactly `p` bits. -/
theorem isRepresentableAtP_of_bounds {p : ℕ} {c e : ℤ} {y : Dyadic}
    (hyeq : (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ e)
    (hc_lo : (2 : ℤ) ^ (p - 1) ≤ |c|) (hc_hi : |c| < (2 : ℤ) ^ p) :
    IsRepresentableAtP p c e y := ⟨hyeq, hc_lo, hc_hi⟩

/-- For `p ≥ 1`, `2^p = 2 · 2^(p-1)`. -/
theorem two_pow_succ_pred {p : ℕ} (hp : 1 ≤ p) :
    (2 : ℤ) ^ p = 2 * (2 : ℤ) ^ (p - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  rw [pow_succ, Nat.add_sub_cancel]; ring

/-- Renormalization: if `|c| = 2^p` (boundary case), then
`y = c · 2^e = (c/2) · 2^(e+1)` and `(c/2, e+1)` is the canonical
IsRepresentableAtP form at `p` bits (with `|c/2| = 2^(p-1)`). -/
theorem isRepresentableAtP_of_saturation {p : ℕ} (hp : 1 ≤ p)
    {c e : ℤ} {y : Dyadic}
    (hyeq : (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ e)
    (hc_eq : |c| = (2 : ℤ) ^ p) :
    IsRepresentableAtP p (c / 2) (e + 1) y := by
  have h2p_nonneg : (0 : ℤ) ≤ (2 : ℤ) ^ p := by positivity
  -- c is even: c = ±2^p, both divisible by 2 (since p ≥ 1).
  have hc_even : 2 ∣ c := by
    rcases (abs_eq h2p_nonneg).mp hc_eq with hc | hc
    · rw [hc, two_pow_succ_pred hp]; exact ⟨_, rfl⟩
    · rw [hc, two_pow_succ_pred hp]; exact ⟨-(2 ^ (p - 1)), by ring⟩
  have h_div_eq : 2 * (c / 2) = c := Int.mul_ediv_cancel' hc_even
  -- |c/2| = 2^(p-1).
  have h_div_abs : |c / 2| = (2 : ℤ) ^ (p - 1) := by
    have h1 : 2 * |c / 2| = (2 : ℤ) ^ p := by
      calc 2 * |c / 2|
          = |2 * (c / 2)| := by rw [abs_mul]; simp
        _ = |c| := by rw [h_div_eq]
        _ = (2 : ℤ) ^ p := hc_eq
    have h2 : (2 : ℤ) ^ p = 2 * (2 : ℤ) ^ (p - 1) := two_pow_succ_pred hp
    linarith
  -- y = (c/2) · 2^(e+1).
  have h_y_real : (y : ℝ) = ((c / 2 : ℤ) : ℝ) * (2 : ℝ) ^ (e + 1) := by
    rw [hyeq]
    have h_real_eq : (c : ℝ) = 2 * ((c / 2 : ℤ) : ℝ) := by
      have : ((2 * (c / 2) : ℤ) : ℝ) = (c : ℝ) := by exact_mod_cast h_div_eq
      push_cast at this
      linarith
    rw [h_real_eq]
    rw [show (2 : ℝ) ^ (e + 1) = (2 : ℝ) ^ e * 2 by
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; ring]
    ring
  refine ⟨h_y_real, ?_, ?_⟩
  · rw [h_div_abs]
  · rw [h_div_abs, two_pow_succ_pred hp]
    have : (0 : ℤ) < (2 : ℤ) ^ (p - 1) := by positivity
    linarith

/-- `IsRepresentableAtP p` pins down a unique `(c, e)` representation
(for `p ≥ 1`). The exponent is determined by `|y|` (via `Int.log`),
and the significand follows. -/
theorem IsRepresentableAtP.unique {p : ℕ} {y : Dyadic}
    {c₁ e₁ c₂ e₂ : ℤ}
    (h₁ : IsRepresentableAtP p c₁ e₁ y) (h₂ : IsRepresentableAtP p c₂ e₂ y) :
    c₁ = c₂ ∧ e₁ = e₂ := by
  obtain ⟨hy₁, hc₁_lo, hc₁_hi⟩ := h₁
  obtain ⟨hy₂, hc₂_lo, hc₂_hi⟩ := h₂
  have h_2_ne : (2 : ℝ) ≠ 0 := by norm_num
  -- |y| determines e uniquely: |c| ∈ [2^(p-1), 2^p) ⟹ |y| ∈ [2^(p-1+e), 2^(p+e)).
  -- Step 1: derive that |c_i| ≥ 1, so c_i ≠ 0, so y ≠ 0.
  have hone_le_2pow : ∀ n : ℕ, (1 : ℤ) ≤ (2 : ℤ) ^ n := fun n => one_le_pow₀ (by norm_num)
  have hc₁_abs_ge_1 : (1 : ℤ) ≤ |c₁| := le_trans (hone_le_2pow _) hc₁_lo
  have hc₂_abs_ge_1 : (1 : ℤ) ≤ |c₂| := le_trans (hone_le_2pow _) hc₂_lo
  have hc₁_ne : c₁ ≠ 0 := fun h => by rw [h, abs_zero] at hc₁_abs_ge_1; omega
  have hc₂_ne : c₂ ≠ 0 := fun h => by rw [h, abs_zero] at hc₂_abs_ge_1; omega
  -- Real-valued bounds.
  have h_2e1_pos : (0 : ℝ) < (2 : ℝ) ^ e₁ := zpow_pos (by norm_num) _
  have h_2e2_pos : (0 : ℝ) < (2 : ℝ) ^ e₂ := zpow_pos (by norm_num) _
  have h_eq : (c₁ : ℝ) * (2 : ℝ) ^ e₁ = (c₂ : ℝ) * (2 : ℝ) ^ e₂ := by
    rw [← hy₁, ← hy₂]
  -- The exponent: show e₁ = e₂.
  have h_e_eq : e₁ = e₂ := by
    -- By symmetry, we show ¬(e₁ < e₂) and ¬(e₂ < e₁).
    have aux : ∀ {a₁ e₁ a₂ e₂ : ℤ},
        (1 : ℤ) ≤ |a₁| → |a₁| < (2 : ℤ) ^ p →
        (2 : ℤ) ^ (p - 1) ≤ |a₂| → |a₂| < (2 : ℤ) ^ p →
        (a₁ : ℝ) * (2 : ℝ) ^ e₁ = (a₂ : ℝ) * (2 : ℝ) ^ e₂ →
        ¬ (e₁ < e₂) := by
      intro a₁ d₁ a₂ d₂ ha₁_ge ha₁_lt ha₂_lo ha₂_hi h_eq h_lt
      -- d₁ < d₂. a₁ · 2^d₁ = a₂ · 2^d₂ ⟹ a₁ = a₂ · 2^(d₂ - d₁) (in ℝ then in ℤ).
      have h_diff_pos : 0 < d₂ - d₁ := by omega
      have h_pow_eq : (2 : ℝ) ^ d₂ = (2 : ℝ) ^ (d₂ - d₁).toNat * (2 : ℝ) ^ d₁ := by
        rw [show ((2 : ℝ) ^ (d₂ - d₁).toNat : ℝ) = (2 : ℝ) ^ ((d₂ - d₁).toNat : ℤ)
            from (zpow_natCast _ _).symm,
            ← zpow_add₀ h_2_ne, Int.toNat_of_nonneg (by omega)]
        congr 1; ring
      have h_a1_eq_real : (a₁ : ℝ) = (a₂ : ℝ) * (2 : ℝ) ^ (d₂ - d₁).toNat := by
        have h2d1_pos : (0 : ℝ) < (2 : ℝ) ^ d₁ := zpow_pos (by norm_num) _
        have : (a₁ : ℝ) * (2 : ℝ) ^ d₁ =
            (a₂ : ℝ) * ((2 : ℝ) ^ (d₂ - d₁).toNat * (2 : ℝ) ^ d₁) := by
          rw [← h_pow_eq]; exact h_eq
        have := mul_right_cancel₀ (ne_of_gt h2d1_pos)
          (by linarith [this] : (a₁ : ℝ) * (2 : ℝ) ^ d₁ =
            (a₂ : ℝ) * (2 : ℝ) ^ (d₂ - d₁).toNat * (2 : ℝ) ^ d₁)
        exact this
      have h_a1_int : a₁ = a₂ * 2 ^ (d₂ - d₁).toNat := by
        have : ((a₂ * 2 ^ (d₂ - d₁).toNat : ℤ) : ℝ) = (a₁ : ℝ) := by
          push_cast; rw [h_a1_eq_real]
        exact_mod_cast this.symm
      have h_abs_eq : |a₁| = |a₂| * 2 ^ (d₂ - d₁).toNat := by
        rw [h_a1_int, abs_mul]
        congr 1
        exact abs_of_nonneg (by positivity)
      -- |a₁| = |a₂| · 2^(d₂-d₁). With |a₂| ≥ 2^(p-1) and 2^(d₂-d₁) ≥ 2:
      have h_pow_ge_2 : (2 : ℤ) ≤ (2 : ℤ) ^ (d₂ - d₁).toNat := by
        have h_toNat_pos : 1 ≤ (d₂ - d₁).toNat := by
          have : ((d₂ - d₁).toNat : ℤ) = d₂ - d₁ := Int.toNat_of_nonneg (by omega)
          omega
        calc (2 : ℤ) = (2 : ℤ) ^ 1 := by ring
          _ ≤ (2 : ℤ) ^ (d₂ - d₁).toNat := pow_le_pow_right₀ (by norm_num) h_toNat_pos
      have h_abs_ge_2p : (2 : ℤ) ^ p ≤ |a₁| := by
        rw [h_abs_eq]
        rcases p with _ | k
        · -- p = 0: |a₁| < 1 contradicts |a₁| ≥ 1.
          exfalso; simp at ha₁_lt; omega
        · -- p = k + 1: 2^(k+1) ≤ |a₂| · 2^(d₂-d₁)
          have h2k : (2 : ℤ) ^ k ≤ |a₂| := by
            have : (2 : ℤ) ^ ((k + 1) - 1) ≤ |a₂| := ha₂_lo
            simpa using this
          calc (2 : ℤ) ^ (k + 1)
              = 2 * (2 : ℤ) ^ k := by rw [pow_succ]; ring
            _ ≤ 2 * |a₂| := by linarith
            _ ≤ |a₂| * 2 ^ (d₂ - d₁).toNat := by
                rw [mul_comm 2 |a₂|]
                exact mul_le_mul_of_nonneg_left h_pow_ge_2 (abs_nonneg _)
      linarith
    -- Apply aux symmetrically.
    have h_no_lt_12 : ¬ (e₁ < e₂) := aux hc₁_abs_ge_1 hc₁_hi hc₂_lo hc₂_hi h_eq
    have h_no_lt_21 : ¬ (e₂ < e₁) := aux hc₂_abs_ge_1 hc₂_hi hc₁_lo hc₁_hi h_eq.symm
    omega
  refine ⟨?_, h_e_eq⟩
  rw [h_e_eq] at h_eq
  have : (c₁ : ℝ) = (c₂ : ℝ) := mul_right_cancel₀ (ne_of_gt h_2e2_pos) h_eq
  exact_mod_cast this

end Dyadic

/-- Non-negative dyadics: a `Dyadic` whose underlying real is `≥ 0`. Used as
the carrier of magnitude bounds in `Format`. -/
abbrev NonNegDyadic : Type := { d : Dyadic // 0 ≤ (d : ℝ) }

end Mpfx2
