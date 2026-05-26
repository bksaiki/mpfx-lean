import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Mathlib.Tactic
import Mpfx2.Utils

namespace Mpfx2

/-- A rational number is *dyadic* if it has the form `c · 2^e` for some integers `c, e`.
The decomposition is not unique: `c · 2^e = (2c) · 2^(e − 1)`. -/
def IsDyadic (x : ℚ) : Prop := ∃ c e : ℤ, x = (c : ℚ) * (2 : ℚ) ^ e

namespace IsDyadic

private theorem add_aux (c₁ c₂ e₁ e₂ : ℤ) (h : e₁ ≤ e₂) :
    (c₁ : ℚ) * (2 : ℚ) ^ e₁ + (c₂ : ℚ) * (2 : ℚ) ^ e₂
      = ((c₁ + c₂ * 2 ^ (e₂ - e₁).toNat : ℤ) : ℚ) * (2 : ℚ) ^ e₁ := by
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  have hsub : ((e₂ - e₁).toNat : ℤ) = e₂ - e₁ := Int.toNat_of_nonneg (by omega)
  have hpow : (2 : ℚ) ^ e₂ = (2 : ℚ) ^ (e₂ - e₁).toNat * (2 : ℚ) ^ e₁ := by
    rw [show ((2 : ℚ) ^ (e₂ - e₁).toNat : ℚ) = (2 : ℚ) ^ ((e₂ - e₁).toNat : ℤ) from
        (zpow_natCast _ _).symm, ← zpow_add₀ h2, hsub]
    congr 1; ring
  rw [hpow]; push_cast; ring

theorem zero : IsDyadic 0 := ⟨0, 0, by simp⟩

theorem one : IsDyadic 1 := ⟨1, 0, by simp⟩

theorem neg {x : ℚ} (h : IsDyadic x) : IsDyadic (-x) := by
  obtain ⟨c, e, rfl⟩ := h
  exact ⟨-c, e, by push_cast; ring⟩

theorem mul {x y : ℚ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x * y) := by
  obtain ⟨c₁, e₁, rfl⟩ := hx
  obtain ⟨c₂, e₂, rfl⟩ := hy
  refine ⟨c₁ * c₂, e₁ + e₂, ?_⟩
  rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  push_cast; ring

theorem add {x y : ℚ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x + y) := by
  obtain ⟨c₁, e₁, rfl⟩ := hx
  obtain ⟨c₂, e₂, rfl⟩ := hy
  rcases le_total e₁ e₂ with h | h
  · exact ⟨c₁ + c₂ * 2 ^ (e₂ - e₁).toNat, e₁, add_aux c₁ c₂ e₁ e₂ h⟩
  · refine ⟨c₂ + c₁ * 2 ^ (e₁ - e₂).toNat, e₂, ?_⟩
    rw [add_comm]
    exact add_aux c₂ c₁ e₂ e₁ h

end IsDyadic

/-- The subring of dyadic rationals. -/
def dyadicSubring : Subring ℚ where
  carrier := { x | IsDyadic x }
  zero_mem' := IsDyadic.zero
  one_mem' := IsDyadic.one
  add_mem' := IsDyadic.add
  neg_mem' := IsDyadic.neg
  mul_mem' := IsDyadic.mul

/-- The type of dyadic numbers, as a subtype of ℚ.

Defined in §3.1. -/
abbrev Dyadic : Type := dyadicSubring

namespace Dyadic

/-- The composite coercion `Dyadic → ℚ → ℝ` is just `((d : ℚ) : ℝ)`. -/
theorem coe_real_eq_ratCast (d : Dyadic) :
    ((d : Dyadic) : ℝ) = ((d : ℚ) : ℝ) := rfl

/-- Extensionality through the real coercion: equal reals ⟹ equal dyadics. -/
theorem ext_real {a b : Dyadic} (h : ((a : Dyadic) : ℝ) = ((b : Dyadic) : ℝ)) : a = b := by
  apply Subtype.ext
  exact_mod_cast h

/-- The composite coercion `Dyadic → ℚ → ℝ` is injective. -/
theorem coe_real_injective : Function.Injective (fun d : Dyadic => ((d : Dyadic) : ℝ)) :=
  fun _ _ h => ext_real h

@[simp, norm_cast] theorem coe_real_inj (a b : Dyadic) :
    ((a : Dyadic) : ℝ) = ((b : Dyadic) : ℝ) ↔ a = b :=
  ⟨ext_real, fun h => by rw [h]⟩

/-- Coercion of negation, all the way to ℝ. -/
@[simp, norm_cast] theorem coe_real_neg (d : Dyadic) :
    ((-d : Dyadic) : ℝ) = -((d : Dyadic) : ℝ) := by
  push_cast; ring

/-- Coercion of zero, all the way to ℝ. -/
@[simp, norm_cast] theorem coe_real_zero :
    ((0 : Dyadic) : ℝ) = 0 := by push_cast; ring

/-- Coercion of addition, all the way to ℝ. -/
@[simp, norm_cast] theorem coe_real_add (d₁ d₂ : Dyadic) :
    ((d₁ + d₂ : Dyadic) : ℝ) = ((d₁ : Dyadic) : ℝ) + ((d₂ : Dyadic) : ℝ) := by
  push_cast; ring

/-- Coercion of subtraction, all the way to ℝ. -/
@[simp, norm_cast] theorem coe_real_sub (d₁ d₂ : Dyadic) :
    ((d₁ - d₂ : Dyadic) : ℝ) = ((d₁ : Dyadic) : ℝ) - ((d₂ : Dyadic) : ℝ) := by
  push_cast; ring

/-- Coercion of multiplication, all the way to ℝ. -/
@[simp, norm_cast] theorem coe_real_mul (d₁ d₂ : Dyadic) :
    ((d₁ * d₂ : Dyadic) : ℝ) = ((d₁ : Dyadic) : ℝ) * ((d₂ : Dyadic) : ℝ) := by
  push_cast; ring

/-- Build a dyadic from `(c, e) : ℤ × ℤ`: the value `c · 2^e`. -/
def ofIntZpow (c e : ℤ) : Dyadic :=
  ⟨(c : ℚ) * (2 : ℚ) ^ e, c, e, rfl⟩

@[simp] theorem coe_rat_ofIntZpow (c e : ℤ) :
    ((ofIntZpow c e : Dyadic) : ℚ) = (c : ℚ) * (2 : ℚ) ^ e := rfl

@[simp] theorem coe_ofIntZpow (c e : ℤ) :
    ((ofIntZpow c e : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ) ^ e := by
  change ((((c : ℚ) * (2 : ℚ) ^ e : ℚ) : ℝ)) = (c : ℝ) * (2 : ℝ) ^ e
  push_cast; ring

/-- `x` has precision at most `p` (`⊤` = no constraint): there exist `c, e : ℤ`
with `x = c · 2^e` and `|c| < 2^p`. -/
def precisionAtMost : WithTop ℕ+ → Dyadic → Prop
  | ⊤, _ => True
  | (p : ℕ+), x => ∃ c e : ℤ, (x : ℚ) = (c : ℚ) * (2 : ℚ) ^ e ∧ |c| < (2 : ℤ) ^ (p : ℕ)

/-- `x` has quantum at least `2^e` (`⊥` = no constraint): there exists `c : ℤ`
with `x = c · 2^e`. -/
def quantumAtLeast : WithBot ℤ → Dyadic → Prop
  | ⊥, _ => True
  | (e : ℤ), x => ∃ c : ℤ, (x : ℚ) = (c : ℚ) * (2 : ℚ) ^ e

@[simp] theorem precisionAtMost_top (x : Dyadic) : precisionAtMost ⊤ x := trivial

@[simp] theorem quantumAtLeast_bot (x : Dyadic) : quantumAtLeast ⊥ x := trivial

theorem precisionAtMost_coe (p : ℕ+) (x : Dyadic) :
    precisionAtMost (p : WithTop ℕ+) x ↔
      ∃ c e : ℤ, (x : ℚ) = (c : ℚ) * (2 : ℚ) ^ e ∧ |c| < (2 : ℤ) ^ (p : ℕ) := Iff.rfl

theorem quantumAtLeast_coe (e : ℤ) (x : Dyadic) :
    quantumAtLeast (e : WithBot ℤ) x ↔
      ∃ c : ℤ, (x : ℚ) = (c : ℚ) * (2 : ℚ) ^ e := Iff.rfl

/-- `ℝ`-stated companion to `precisionAtMost_coe`. The substrate predicate is
`ℚ`-valued; this bridges to `ℝ` for the `Int.log`/`Int.floor` rounding proofs. -/
theorem precisionAtMost_coe_real (p : ℕ+) (x : Dyadic) :
    precisionAtMost (p : WithTop ℕ+) x ↔
      ∃ c e : ℤ, (x : ℝ) = (c : ℝ) * (2 : ℝ) ^ e ∧ |c| < (2 : ℤ) ^ (p : ℕ) := by
  rw [precisionAtMost_coe]
  refine ⟨fun ⟨c, e, hc, hb⟩ => ⟨c, e, ?_, hb⟩, fun ⟨c, e, hc, hb⟩ => ⟨c, e, ?_, hb⟩⟩
  · rw [coe_real_eq_ratCast, hc]; push_cast; ring
  · have h : ((x : ℚ) : ℝ) = (((c : ℚ) * (2 : ℚ) ^ e : ℚ) : ℝ) := by
      rw [← coe_real_eq_ratCast, hc]; push_cast; ring
    exact_mod_cast h

/-- `ℝ`-stated companion to `quantumAtLeast_coe`. -/
theorem quantumAtLeast_coe_real (e : ℤ) (x : Dyadic) :
    quantumAtLeast (e : WithBot ℤ) x ↔
      ∃ c : ℤ, (x : ℝ) = (c : ℝ) * (2 : ℝ) ^ e := by
  rw [quantumAtLeast_coe]
  refine ⟨fun ⟨c, hc⟩ => ⟨c, ?_⟩, fun ⟨c, hc⟩ => ⟨c, ?_⟩⟩
  · rw [coe_real_eq_ratCast, hc]; push_cast; ring
  · have h : ((x : ℚ) : ℝ) = (((c : ℚ) * (2 : ℚ) ^ e : ℚ) : ℝ) := by
      rw [← coe_real_eq_ratCast, hc]; push_cast; ring
    exact_mod_cast h

/-- `precisionAtMost` is monotone in the precision bound: more precision
allowed means the constraint is weaker. -/
theorem precisionAtMost_mono {p₁ p₂ : WithTop ℕ+} (h : p₁ ≤ p₂) {x : Dyadic}
    (hx : precisionAtMost p₁ x) : precisionAtMost p₂ x := by
  cases p₂ with
  | top => trivial
  | coe p₂ =>
    cases p₁ with
    | top => exact absurd (top_le_iff.mp h) (WithTop.coe_ne_top)
    | coe p₁ =>
      obtain ⟨c, e, hc, hb⟩ := hx
      refine ⟨c, e, hc, ?_⟩
      have hp_le : (p₁ : ℕ) ≤ (p₂ : ℕ) := by exact_mod_cast WithTop.coe_le_coe.mp h
      exact lt_of_lt_of_le hb (pow_le_pow_right₀ (by norm_num) hp_le)

/-- `quantumAtLeast` is antitone in the exponent bound: a smaller minimum
quantum (smaller `exp`) is a weaker constraint. -/
theorem quantumAtLeast_anti {e₁ e₂ : WithBot ℤ} (h : e₂ ≤ e₁) {x : Dyadic}
    (hx : quantumAtLeast e₁ x) : quantumAtLeast e₂ x := by
  cases e₂ with
  | bot => trivial
  | coe e₂ =>
    cases e₁ with
    | bot => exact absurd (le_bot_iff.mp h) (WithBot.coe_ne_bot)
    | coe e₁ =>
      obtain ⟨c, hc⟩ := hx
      have he_le : e₂ ≤ e₁ := by exact_mod_cast WithBot.coe_le_coe.mp h
      refine ⟨c * 2 ^ (e₁ - e₂).toNat, ?_⟩
      rw [hc]
      push_cast
      rw [show ((2 : ℚ) ^ (e₁ - e₂).toNat : ℚ) = (2 : ℚ) ^ ((e₁ - e₂).toNat : ℤ)
          from (zpow_natCast _ _).symm,
          mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0),
          Int.toNat_of_nonneg (by omega)]
      congr 2; omega

theorem precisionAtMost_neg {p : WithTop ℕ+} {x : Dyadic} (h : precisionAtMost p x) :
    precisionAtMost p (-x) := by
  cases p with
  | top => trivial
  | coe p =>
    obtain ⟨c, e, hx, hc⟩ := h
    refine ⟨-c, e, ?_, ?_⟩
    · push_cast [Subring.coe_neg, hx]; ring
    · simpa [abs_neg] using hc

@[simp] theorem precisionAtMost_neg_iff (p : WithTop ℕ+) (x : Dyadic) :
    precisionAtMost p (-x) ↔ precisionAtMost p x :=
  ⟨fun h => by simpa using precisionAtMost_neg h, precisionAtMost_neg⟩

theorem quantumAtLeast_neg {e : WithBot ℤ} {x : Dyadic} (h : quantumAtLeast e x) :
    quantumAtLeast e (-x) := by
  cases e with
  | bot => trivial
  | coe e =>
    obtain ⟨c, hx⟩ := h
    refine ⟨-c, ?_⟩
    push_cast [Subring.coe_neg, hx]; ring

@[simp] theorem quantumAtLeast_neg_iff (e : WithBot ℤ) (x : Dyadic) :
    quantumAtLeast e (-x) ↔ quantumAtLeast e x :=
  ⟨fun h => by simpa using quantumAtLeast_neg h, quantumAtLeast_neg⟩

/-- `(c, e)` is a representation of `y` at *exactly* `p` binary digits:
`y = c · 2^e` with `2^(p-1) ≤ |c| < 2^p`. For nonzero `y` representable
at `p` bits, the `(c, e)` pair is unique. -/
def IsRepresentableAtP (p : ℕ) (c e : ℤ) (y : Dyadic) : Prop :=
  (y : ℚ) = (c : ℚ) * (2 : ℚ) ^ e ∧
  (2 : ℤ) ^ (p - 1) ≤ |c| ∧ |c| < (2 : ℤ) ^ p

/-- If `y = c · 2^e` with `|c| ≤ 2^p`, then `precisionAtMost p y`. The
boundary case `|c| = 2^p` forces `c = ±2^p`; renormalize to
`y = ±1 · 2^(e+p)` to recover a strict-inequality witness. -/
theorem precisionAtMost_of_abs_le {p : ℕ+} {x : Dyadic} (c e : ℤ)
    (hx : (x : ℚ) = (c : ℚ) * (2 : ℚ) ^ e) (hc : |c| ≤ (2 : ℤ) ^ (p : ℕ)) :
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
    have h2ne : (2 : ℚ) ≠ 0 := two_ne_zero
    rcases hsign with hpos | hneg
    · refine ⟨1, e + (p : ℤ), ?_, ?_⟩
      · rw [hx, hpos, zpow_add₀ h2ne]
        push_cast
        simp only [← zpow_natCast (2 : ℚ) (p : ℕ)]
        ring
      · simpa using hone_lt
    · refine ⟨-1, e + (p : ℤ), ?_, ?_⟩
      · rw [hx, hneg, zpow_add₀ h2ne]
        push_cast
        simp only [← zpow_natCast (2 : ℚ) (p : ℕ)]
        ring
      · have habs : |(-1 : ℤ)| = 1 := by decide
        rw [habs]; exact hone_lt

/-- `IsRepresentableAtP n c e y` implies `y ≠ 0` (since `|c| ≥ 1`). -/
theorem IsRepresentableAtP.ne_zero {n : ℕ} {c e : ℤ} {y : Dyadic}
    (h : IsRepresentableAtP n c e y) : (y : ℚ) ≠ 0 := by
  obtain ⟨hyeq, hc_lo, _⟩ := h
  intro h0; rw [h0] at hyeq
  have h2e_pos : (0 : ℚ) < (2 : ℚ) ^ e := zpow_pos (by norm_num) _
  have hc_zero : (c : ℚ) = 0 := by
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
    (hyeq : (y : ℚ) = (c : ℚ) * (2 : ℚ) ^ e)
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
    (hyeq : (y : ℚ) = (c : ℚ) * (2 : ℚ) ^ e)
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
  have h_y_real : (y : ℚ) = ((c / 2 : ℤ) : ℚ) * (2 : ℚ) ^ (e + 1) := by
    rw [hyeq]
    have h_real_eq : (c : ℚ) = 2 * ((c / 2 : ℤ) : ℚ) := by
      have : ((2 * (c / 2) : ℤ) : ℚ) = (c : ℚ) := by exact_mod_cast h_div_eq
      push_cast at this
      linarith
    rw [h_real_eq]
    rw [show (2 : ℚ) ^ (e + 1) = (2 : ℚ) ^ e * 2 by
      rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]; ring]
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
  have h_2_ne : (2 : ℚ) ≠ 0 := by norm_num
  -- |y| determines e uniquely: |c| ∈ [2^(p-1), 2^p) ⟹ |y| ∈ [2^(p-1+e), 2^(p+e)).
  -- Step 1: derive that |c_i| ≥ 1, so c_i ≠ 0, so y ≠ 0.
  have hone_le_2pow : ∀ n : ℕ, (1 : ℤ) ≤ (2 : ℤ) ^ n := fun n => one_le_pow₀ (by norm_num)
  have hc₁_abs_ge_1 : (1 : ℤ) ≤ |c₁| := le_trans (hone_le_2pow _) hc₁_lo
  have hc₂_abs_ge_1 : (1 : ℤ) ≤ |c₂| := le_trans (hone_le_2pow _) hc₂_lo
  have hc₁_ne : c₁ ≠ 0 := fun h => by rw [h, abs_zero] at hc₁_abs_ge_1; omega
  have hc₂_ne : c₂ ≠ 0 := fun h => by rw [h, abs_zero] at hc₂_abs_ge_1; omega
  -- Rational-valued bounds.
  have h_2e1_pos : (0 : ℚ) < (2 : ℚ) ^ e₁ := zpow_pos (by norm_num) _
  have h_2e2_pos : (0 : ℚ) < (2 : ℚ) ^ e₂ := zpow_pos (by norm_num) _
  have h_eq : (c₁ : ℚ) * (2 : ℚ) ^ e₁ = (c₂ : ℚ) * (2 : ℚ) ^ e₂ := by
    rw [← hy₁, ← hy₂]
  -- The exponent: show e₁ = e₂.
  have h_e_eq : e₁ = e₂ := by
    -- By symmetry, we show ¬(e₁ < e₂) and ¬(e₂ < e₁).
    have aux : ∀ {a₁ e₁ a₂ e₂ : ℤ},
        (1 : ℤ) ≤ |a₁| → |a₁| < (2 : ℤ) ^ p →
        (2 : ℤ) ^ (p - 1) ≤ |a₂| → |a₂| < (2 : ℤ) ^ p →
        (a₁ : ℚ) * (2 : ℚ) ^ e₁ = (a₂ : ℚ) * (2 : ℚ) ^ e₂ →
        ¬ (e₁ < e₂) := by
      intro a₁ d₁ a₂ d₂ ha₁_ge ha₁_lt ha₂_lo ha₂_hi h_eq h_lt
      -- d₁ < d₂. a₁ · 2^d₁ = a₂ · 2^d₂ ⟹ a₁ = a₂ · 2^(d₂ - d₁) (in ℚ then in ℤ).
      have h_diff_pos : 0 < d₂ - d₁ := by omega
      have h_pow_eq : (2 : ℚ) ^ d₂ = (2 : ℚ) ^ (d₂ - d₁).toNat * (2 : ℚ) ^ d₁ := by
        rw [show ((2 : ℚ) ^ (d₂ - d₁).toNat : ℚ) = (2 : ℚ) ^ ((d₂ - d₁).toNat : ℤ)
            from (zpow_natCast _ _).symm,
            ← zpow_add₀ h_2_ne, Int.toNat_of_nonneg (by omega)]
        congr 1; ring
      have h_a1_eq_real : (a₁ : ℚ) = (a₂ : ℚ) * (2 : ℚ) ^ (d₂ - d₁).toNat := by
        have h2d1_pos : (0 : ℚ) < (2 : ℚ) ^ d₁ := zpow_pos (by norm_num) _
        have : (a₁ : ℚ) * (2 : ℚ) ^ d₁ =
            (a₂ : ℚ) * ((2 : ℚ) ^ (d₂ - d₁).toNat * (2 : ℚ) ^ d₁) := by
          rw [← h_pow_eq]; exact h_eq
        have := mul_right_cancel₀ (ne_of_gt h2d1_pos)
          (by linarith [this] : (a₁ : ℚ) * (2 : ℚ) ^ d₁ =
            (a₂ : ℚ) * (2 : ℚ) ^ (d₂ - d₁).toNat * (2 : ℚ) ^ d₁)
        exact this
      have h_a1_int : a₁ = a₂ * 2 ^ (d₂ - d₁).toNat := by
        have : ((a₂ * 2 ^ (d₂ - d₁).toNat : ℤ) : ℚ) = (a₁ : ℚ) := by
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
  have : (c₁ : ℚ) = (c₂ : ℚ) := mul_right_cancel₀ (ne_of_gt h_2e2_pos) h_eq
  exact_mod_cast this

/-- Dyadics have decidable equality (inherited from `ℚ`) — a payoff of the
rational substrate. -/
instance : DecidableEq Dyadic := Subtype.instDecidableEq

end Dyadic

/-- Non-negative dyadics: a `Dyadic` whose underlying rational is `≥ 0`. Used as
the carrier of magnitude bounds in `Format`. -/
abbrev NonNegDyadic : Type := { d : Dyadic // 0 ≤ (d : ℚ) }

end Mpfx2
