import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Mpfx.Utils
import Mathlib.Tactic
import Mpfx.Utils

/-!
# Dyadic numbers and format parameters

`Dyadic`, the subring of `ℚ` of numbers `c · 2^e`; the precision and quantum
predicates `precisionAtMost` / `quantumAtLeast`; and the format parameter
types `Prec`, `QExp`, `Bound`.
-/

namespace Mpfx

/-- A precision bound: a finite number of binary digits, or `⊤` for
"no precision constraint". -/
abbrev Prec := ℕ∞

/-- `WithTop.some` and the `↑ : ℕ → Prec` coercion are definitionally but not
syntactically equal. Mathlib's `ENat.some_eq_coe` states this between the
functions, which `simp` will not use to rewrite an application; this is the
pointwise form. -/
@[simp] theorem Prec.some_eq_coe p : (WithTop.some p : Prec) = (p : Prec) := rfl

/-- A minimum-quantum exponent: the format's values are multiples of `2^exp`,
or `⊥` for "no quantum constraint". -/
abbrev QExp := WithBot ℤ

/-- Eliminator for `QExp` stating its `coe` case with the `↑ : ℤ → QExp`
coercion. `QExp` is reducible, so a bare `cases` unfolds past `WithBot` to
`Option`; split with this instead. -/
@[elab_as_elim] def QExp.recBotCoe {C : QExp → Sort*} (bot : C ⊥)
    (coe : ∀ e : ℤ, C (e : QExp)) : ∀ e : QExp, C e
  | ⊥ => bot
  | (e : ℤ) => coe e

/-- A rational number is *dyadic* if it has the form `c · 2^e` for some integers `c, e`.
The decomposition is not unique: `c · 2^e = (2c) · 2^(e − 1)`. -/
def IsDyadic (x : ℚ) : Prop := ∃ c e : ℤ, x = (c : ℚ) * (2 : ℚ) ^ e

namespace IsDyadic

private theorem add_aux (c₁ c₂ e₁ e₂ : ℤ) (h : e₁ ≤ e₂) :
    (c₁ : ℚ) * (2 : ℚ) ^ e₁ + (c₂ : ℚ) * (2 : ℚ) ^ e₂
      = ((c₁ + c₂ * 2 ^ (e₂ - e₁).toNat : ℤ) : ℚ) * (2 : ℚ) ^ e₁ := by
  rw [Mpfx.two_zpow_split_toNat (K := ℚ) h]; push_cast; ring

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

theorem coe_real_lt_zero_iff (d : Dyadic) : (d : ℝ) < 0 ↔ (d : ℚ) < 0 := by
  rw [coe_real_eq_ratCast, Rat.cast_lt_zero]

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

/-- Build a dyadic from `(c, e) : ℤ × ℤ`: the value `c · 2^e`. -/
def ofIntZpow (c e : ℤ) : Dyadic :=
  ⟨(c : ℚ) * (2 : ℚ) ^ e, c, e, rfl⟩

@[simp] theorem coe_rat_ofIntZpow (c e : ℤ) :
    ((ofIntZpow c e : Dyadic) : ℚ) = (c : ℚ) * (2 : ℚ) ^ e := rfl

@[simp] theorem coe_ofIntZpow (c e : ℤ) :
    ((ofIntZpow c e : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ) ^ e := by
  change ((((c : ℚ) * (2 : ℚ) ^ e : ℚ) : ℝ)) = (c : ℝ) * (2 : ℝ) ^ e
  push_cast; ring

/-- The half-dyadic, `1/2 = 1·2^(-1)`. -/
def half : Dyadic := ofIntZpow 1 (-1)

@[simp] theorem coe_half : ((half : Dyadic) : ℝ) = 1 / 2 := by
  change ((ofIntZpow 1 (-1) : Dyadic) : ℝ) = 1 / 2
  rw [coe_ofIntZpow, zpow_neg_one]; push_cast; ring

@[simp] theorem coe_rat_half : ((half : Dyadic) : ℚ) = 1 / 2 := by
  change ((ofIntZpow 1 (-1) : Dyadic) : ℚ) = 1 / 2
  rw [coe_rat_ofIntZpow, zpow_neg_one]; push_cast; ring

/-- Midpoint of two dyadics: `(y₁ + y₂)/2`. -/
def midpoint (y₁ y₂ : Dyadic) : Dyadic := (y₁ + y₂) * half

theorem coe_midpoint (y₁ y₂ : Dyadic) :
    ((midpoint y₁ y₂ : Dyadic) : ℝ) = ((y₁ : ℝ) + (y₂ : ℝ)) / 2 := by
  change (((y₁ + y₂) * half : Dyadic) : ℝ) = _
  rw [coe_real_mul, coe_real_add, coe_half]; ring

theorem coe_rat_midpoint (y₁ y₂ : Dyadic) :
    ((midpoint y₁ y₂ : Dyadic) : ℚ) = (((y₁ : ℚ) + (y₂ : ℚ)) / 2) := by
  change (((y₁ + y₂) * half : Dyadic) : ℚ) = _
  push_cast [coe_rat_half]; ring

theorem midpoint_comm (y₁ y₂ : Dyadic) :
    midpoint y₁ y₂ = midpoint y₂ y₁ := by
  apply ext_real
  rw [coe_midpoint, coe_midpoint]; ring

/-- `x` has precision at most `p` (`⊤` = no constraint): there exist `c, e : ℤ`
with `x = c · 2^e` and `|c| < 2^p`. -/
def precisionAtMost : Prec → Dyadic → Prop
  | ⊤, _ => True
  | (p : ℕ), x => ∃ c e : ℤ, (x : ℚ) = (c : ℚ) * (2 : ℚ) ^ e ∧ |c| < (2 : ℤ) ^ p

/-- `x` has quantum at least `2^e` (`⊥` = no constraint): there exists `c : ℤ`
with `x = c · 2^e`. -/
def quantumAtLeast : QExp → Dyadic → Prop
  | ⊥, _ => True
  | (e : ℤ), x => ∃ c : ℤ, (x : ℚ) = (c : ℚ) * (2 : ℚ) ^ e

@[simp] theorem precisionAtMost_top (x : Dyadic) : precisionAtMost ⊤ x := trivial

@[simp] theorem quantumAtLeast_bot (x : Dyadic) : quantumAtLeast ⊥ x := trivial

theorem precisionAtMost_coe (p : ℕ) (x : Dyadic) :
    precisionAtMost (p : Prec) x ↔
      ∃ c e : ℤ, (x : ℚ) = (c : ℚ) * (2 : ℚ) ^ e ∧ |c| < (2 : ℤ) ^ p := Iff.rfl

theorem quantumAtLeast_coe (e : ℤ) (x : Dyadic) :
    quantumAtLeast (e : QExp) x ↔
      ∃ c : ℤ, (x : ℚ) = (c : ℚ) * (2 : ℚ) ^ e := Iff.rfl

/-- `ℝ`-stated companion to `precisionAtMost_coe`. The substrate predicate is
`ℚ`-valued; this bridges to `ℝ` for the `Int.log`/`Int.floor` rounding proofs. -/
theorem precisionAtMost_coe_real (p : ℕ) (x : Dyadic) :
    precisionAtMost (p : Prec) x ↔
      ∃ c e : ℤ, (x : ℝ) = (c : ℝ) * (2 : ℝ) ^ e ∧ |c| < (2 : ℤ) ^ p := by
  rw [precisionAtMost_coe]
  refine ⟨fun ⟨c, e, hc, hb⟩ => ⟨c, e, ?_, hb⟩, fun ⟨c, e, hc, hb⟩ => ⟨c, e, ?_, hb⟩⟩
  · rw [coe_real_eq_ratCast, hc]; push_cast; ring
  · have h : ((x : ℚ) : ℝ) = (((c : ℚ) * (2 : ℚ) ^ e : ℚ) : ℝ) := by
      rw [← coe_real_eq_ratCast, hc]; push_cast; ring
    exact_mod_cast h

/-- `ℝ`-stated companion to `quantumAtLeast_coe`. -/
theorem quantumAtLeast_coe_real (e : ℤ) (x : Dyadic) :
    quantumAtLeast (e : QExp) x ↔
      ∃ c : ℤ, (x : ℝ) = (c : ℝ) * (2 : ℝ) ^ e := by
  rw [quantumAtLeast_coe]
  refine ⟨fun ⟨c, hc⟩ => ⟨c, ?_⟩, fun ⟨c, hc⟩ => ⟨c, ?_⟩⟩
  · rw [coe_real_eq_ratCast, hc]; push_cast; ring
  · have h : ((x : ℚ) : ℝ) = (((c : ℚ) * (2 : ℚ) ^ e : ℚ) : ℝ) := by
      rw [← coe_real_eq_ratCast, hc]; push_cast; ring
    exact_mod_cast h

/-- Precision `0` is the trivial format: `|c| < 2^0 = 1` forces `c = 0`. -/
theorem precisionAtMost_zero_iff_eq_zero {x : Dyadic} :
    precisionAtMost (0 : Prec) x ↔ x = 0 := by
  rw [show (0 : Prec) = ((0 : ℕ) : Prec) from rfl, precisionAtMost_coe]
  refine ⟨fun ⟨c, e, hx, hc⟩ => ?_, fun hx => ⟨0, 0, by rw [hx]; simp, by norm_num⟩⟩
  have : c = 0 := by simpa using hc
  exact Subtype.ext (by rw [hx, this]; simp)

/-- `precisionAtMost` is monotone in the precision bound: more precision
allowed means the constraint is weaker. -/
theorem precisionAtMost_mono {p₁ p₂ : Prec} (h : p₁ ≤ p₂) {x : Dyadic}
    (hx : precisionAtMost p₁ x) : precisionAtMost p₂ x := by
  cases p₂ using ENat.recTopCoe with
  | top => trivial
  | coe p₂ =>
    cases p₁ using ENat.recTopCoe with
    | top => exact absurd (top_le_iff.mp h) (WithTop.coe_ne_top)
    | coe p₁ =>
      obtain ⟨c, e, hc, hb⟩ := hx
      refine ⟨c, e, hc, ?_⟩
      have hp_le : p₁ ≤ p₂ := by exact_mod_cast WithTop.coe_le_coe.mp h
      exact lt_of_lt_of_le hb (pow_le_pow_right₀ (by norm_num) hp_le)

/-- `quantumAtLeast` is antitone in the exponent bound: a smaller minimum
quantum (smaller `exp`) is a weaker constraint. -/
theorem quantumAtLeast_anti {e₁ e₂ : QExp} (h : e₂ ≤ e₁) {x : Dyadic}
    (hx : quantumAtLeast e₁ x) : quantumAtLeast e₂ x := by
  cases e₂ using QExp.recBotCoe with
  | bot => trivial
  | coe e₂ =>
    cases e₁ using QExp.recBotCoe with
    | bot => exact absurd (le_bot_iff.mp h) (WithBot.coe_ne_bot)
    | coe e₁ =>
      obtain ⟨c, hc⟩ := hx
      exact ⟨_, hc.trans (Mpfx.two_zpow_shift c (WithBot.coe_le_coe.mp h))⟩

/-- `c · 2^k` has quantum at least `2^e` for every `e ≤ k`. -/
theorem quantumAtLeast_ofIntZpow {e : QExp} {c k : ℤ} (he : e ≤ (k : QExp)) :
    quantumAtLeast e (ofIntZpow c k) :=
  quantumAtLeast_anti he ⟨c, by rw [coe_rat_ofIntZpow]⟩

theorem precisionAtMost_neg {p : Prec} {x : Dyadic} (h : precisionAtMost p x) :
    precisionAtMost p (-x) := by
  cases p using ENat.recTopCoe with
  | top => trivial
  | coe p =>
    obtain ⟨c, e, hx, hc⟩ := h
    refine ⟨-c, e, ?_, ?_⟩
    · push_cast [Subring.coe_neg, hx]; ring
    · simpa [abs_neg] using hc

@[simp] theorem precisionAtMost_neg_iff (p : Prec) (x : Dyadic) :
    precisionAtMost p (-x) ↔ precisionAtMost p x :=
  ⟨fun h => by simpa using precisionAtMost_neg h, precisionAtMost_neg⟩

theorem quantumAtLeast_neg {e : QExp} {x : Dyadic} (h : quantumAtLeast e x) :
    quantumAtLeast e (-x) := by
  cases e using QExp.recBotCoe with
  | bot => trivial
  | coe e =>
    obtain ⟨c, hx⟩ := h
    refine ⟨-c, ?_⟩
    push_cast [Subring.coe_neg, hx]; ring

@[simp] theorem quantumAtLeast_neg_iff (e : QExp) (x : Dyadic) :
    quantumAtLeast e (-x) ↔ quantumAtLeast e x :=
  ⟨fun h => by simpa using quantumAtLeast_neg h, quantumAtLeast_neg⟩

/-! ### Quantum alignment under arithmetic

A value's quantum is preserved under `±` and combined under `×`. -/

/-- A sum of two quantum-aligned dyadics stays quantum-aligned. -/
theorem quantumAtLeast_add {e : QExp} {a b : Dyadic}
    (ha : Dyadic.quantumAtLeast e a) (hb : Dyadic.quantumAtLeast e b) :
    Dyadic.quantumAtLeast e (a + b) := by
  cases e using QExp.recBotCoe with
  | bot => trivial
  | coe e =>
    obtain ⟨ca, hca⟩ := (Dyadic.quantumAtLeast_coe_real e a).mp ha
    obtain ⟨cb, hcb⟩ := (Dyadic.quantumAtLeast_coe_real e b).mp hb
    refine (Dyadic.quantumAtLeast_coe_real e (a + b)).mpr ⟨ca + cb, ?_⟩
    rw [show ((a + b : Dyadic) : ℝ) = (a : ℝ) + (b : ℝ) from by push_cast; ring, hca, hcb]
    push_cast; ring

/-- A difference of two quantum-aligned dyadics stays quantum-aligned. -/
theorem quantumAtLeast_sub {e : QExp} {a b : Dyadic}
    (ha : Dyadic.quantumAtLeast e a) (hb : Dyadic.quantumAtLeast e b) :
    Dyadic.quantumAtLeast e (a - b) := by
  rw [sub_eq_add_neg]; exact quantumAtLeast_add ha (Dyadic.quantumAtLeast_neg hb)

/-- A product is quantum-aligned at the *sum* of the operands' quanta. -/
theorem quantumAtLeast_mul {e₁ e₂ : QExp} {x y : Dyadic}
    (hx : Dyadic.quantumAtLeast e₁ x) (hy : Dyadic.quantumAtLeast e₂ y) :
    Dyadic.quantumAtLeast (e₁ + e₂) (x * y) := by
  cases e₁ using QExp.recBotCoe with
  | bot => rw [show (⊥ + e₂ : QExp) = ⊥ from by simp]; trivial
  | coe a =>
    cases e₂ using QExp.recBotCoe with
    | bot => rw [show ((a : QExp) + ⊥) = ⊥ from by simp]; trivial
    | coe b =>
      obtain ⟨cx, hcx⟩ := (Dyadic.quantumAtLeast_coe_real a x).mp hx
      obtain ⟨cy, hcy⟩ := (Dyadic.quantumAtLeast_coe_real b y).mp hy
      rw [← WithBot.coe_add]
      refine (Dyadic.quantumAtLeast_coe_real (a + b) (x * y)).mpr ⟨cx * cy, ?_⟩
      rw [show ((x * y : Dyadic) : ℝ) = (x : ℝ) * (y : ℝ) from by push_cast; ring, hcx, hcy,
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; push_cast; ring

/-- A product needs at most the sum of the operands' precisions. -/
theorem precisionAtMost_mul {p₁ p₂ : Prec} {x y : Dyadic}
    (hx : precisionAtMost p₁ x) (hy : precisionAtMost p₂ y) :
    precisionAtMost (p₁ + p₂) (x * y) := by
  cases p₁ using ENat.recTopCoe with
  | top => rw [top_add]; trivial
  | coe a =>
    cases p₂ using ENat.recTopCoe with
    | top => rw [add_top]; trivial
    | coe b =>
      rw [precisionAtMost_coe] at hx hy
      obtain ⟨c1, e1, hxeq, hc1⟩ := hx
      obtain ⟨c2, e2, hyeq, hc2⟩ := hy
      rw [← Nat.cast_add, precisionAtMost_coe]
      refine ⟨c1 * c2, e1 + e2, ?_, ?_⟩
      · change ((x * y : Dyadic) : ℚ) = _
        push_cast
        rw [hxeq, hyeq, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
        ring
      · rw [pow_add, abs_mul]
        exact mul_lt_mul'' hc1 hc2 (abs_nonneg _) (abs_nonneg _)

/-- The dyadic value `3 · 2^k` has precision at most 2 (significand `3` fits
in `|c| < 2^2 = 4`). Used as a precision-2 witness in `hp_F₂`-derivation. -/
theorem precisionAtMost_two_three_zpow (k : ℤ) :
    precisionAtMost ((2 : ℕ) : Prec) (Dyadic.ofIntZpow 3 k) := by
  rw [precisionAtMost_coe]
  refine ⟨3, k, ?_, ?_⟩
  · rw [coe_rat_ofIntZpow]
  · decide

/-- A nonzero dyadic with `quantumAtLeast e` has absolute value at least `2^e`.
The smallest nonzero significand `c` is `±1`, giving `|c·2^e| = 2^e`. -/
theorem abs_ge_two_zpow_of_quantum {e : ℤ} {d : Dyadic}
    (hq : quantumAtLeast (e : QExp) d) (hne : (d : ℝ) ≠ 0) :
    (2 : ℝ)^e ≤ |(d : ℝ)| := by
  rw [quantumAtLeast_coe_real] at hq
  obtain ⟨c, hc_eq⟩ := hq
  have hc_ne : c ≠ 0 := by rintro rfl; simp [hc_eq] at hne
  have habs : (1 : ℝ) ≤ |(c : ℝ)| := by exact_mod_cast Int.one_le_abs hc_ne
  rw [hc_eq, abs_mul, abs_of_pos (zpow_pos two_pos e : (0 : ℝ) < 2 ^ e)]
  exact le_mul_of_one_le_left (zpow_pos two_pos e).le habs

/-- A nonzero dyadic with `quantumAtLeast e` lies at or above binade `e`. -/
theorem le_log_of_quantum {e : ℤ} {d : Dyadic}
    (hq : quantumAtLeast (e : QExp) d) (hne : (d : ℝ) ≠ 0) :
    e ≤ Int.log 2 |(d : ℝ)| :=
  (Int.zpow_le_iff_le_log (by norm_num) (abs_pos.mpr hne)).mp
    (by exact_mod_cast abs_ge_two_zpow_of_quantum hq hne)

/-- `(c, e)` is a representation of `y` at *exactly* `p` binary digits:
`y = c · 2^e` with `2^(p-1) ≤ |c| < 2^p`. For nonzero `y` representable
at `p` bits, the `(c, e)` pair is unique. -/
def IsRepresentableAtP (p : ℕ) (c e : ℤ) (y : Dyadic) : Prop :=
  (y : ℚ) = (c : ℚ) * (2 : ℚ) ^ e ∧
  (2 : ℤ) ^ (p - 1) ≤ |c| ∧ |c| < (2 : ℤ) ^ p

/-- If `y = c · 2^e` with `|c| ≤ 2^p`, then `precisionAtMost p y`. The
boundary case `|c| = 2^p` forces `c = ±2^p`; renormalize to
`y = ±1 · 2^(e+p)` to recover a strict-inequality witness. -/
theorem precisionAtMost_of_abs_le {p : ℕ} (hp : 0 < p) {x : Dyadic} (c e : ℤ)
    (hx : (x : ℚ) = (c : ℚ) * (2 : ℚ) ^ e) (hc : |c| ≤ (2 : ℤ) ^ p) :
    precisionAtMost (p : Prec) x := by
  rw [precisionAtMost_coe]
  rcases lt_or_eq_of_le hc with hlt | heq
  · exact ⟨c, e, hx, hlt⟩
  · have h2p_nonneg : (0 : ℤ) ≤ (2 : ℤ) ^ p := by positivity
    have hsign : c = (2 : ℤ) ^ p ∨ c = -((2 : ℤ) ^ p) :=
      (abs_eq h2p_nonneg).mp heq
    have hone_lt : (1 : ℤ) < (2 : ℤ) ^ p := by
      have : (2 : ℤ) ^ 0 < (2 : ℤ) ^ p := pow_lt_pow_right₀ (by norm_num) hp
      simpa using this
    -- `c = ±2^p` renormalises to `±1 · 2^(e+p)`.
    obtain ⟨s, hs, hcs⟩ : ∃ s : ℤ, |s| = 1 ∧ c = s * 2 ^ p := by
      rcases hsign with h | h
      exacts [⟨1, by simp, by simp [h]⟩, ⟨-1, by simp, by simp [h]⟩]
    refine ⟨s, e + (p : ℤ), ?_, by rw [hs]; exact hone_lt⟩
    rw [hx, hcs, zpow_add₀ two_ne_zero]
    push_cast
    simp only [← zpow_natCast (2 : ℚ) p]
    ring

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
    · rw [hc, Int.two_pow_succ_pred hp]; exact ⟨_, rfl⟩
    · rw [hc, Int.two_pow_succ_pred hp]; exact ⟨-(2 ^ (p - 1)), by ring⟩
  have h_div_eq : 2 * (c / 2) = c := Int.mul_ediv_cancel' hc_even
  -- |c/2| = 2^(p-1).
  have h_div_abs : |c / 2| = (2 : ℤ) ^ (p - 1) := by
    have h1 : 2 * |c / 2| = (2 : ℤ) ^ p := by
      calc 2 * |c / 2|
          = |2 * (c / 2)| := by rw [abs_mul]; simp
        _ = |c| := by rw [h_div_eq]
        _ = (2 : ℤ) ^ p := hc_eq
    have h2 : (2 : ℤ) ^ p = 2 * (2 : ℤ) ^ (p - 1) := Int.two_pow_succ_pred hp
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
  · rw [h_div_abs, Int.two_pow_succ_pred hp]
    have : (0 : ℤ) < (2 : ℤ) ^ (p - 1) := by positivity
    linarith

/-- `((ofIntZpow k e : Dyadic) : ℝ) ≠ 0` whenever `k ≠ 0`. Packages the
recurring `mul_ne_zero (cast) (zpow_pos)` idiom. -/
theorem coe_ofIntZpow_ne_zero {k : ℤ} (hk : k ≠ 0) (e : ℤ) :
    ((ofIntZpow k e : Dyadic) : ℝ) ≠ 0 := by
  rw [coe_ofIntZpow]
  exact mul_ne_zero (Int.cast_ne_zero.mpr hk) (ne_of_gt (zpow_pos (by norm_num) _))

/-- The `Int.log`-based bounds core: for `k ≠ 0` and `y = k · 2^e'`, the pair
`(k, e')` is the canonical representation of `y` at `log₂|k| + 1` bits. This
captures the `2^(nd-1) ≤ |k| < 2^nd` derivation (via `Int.zpow_log_le_self` /
`Int.lt_zpow_succ_log_self`) once, so the case-specific `numDigits` helpers can
route through it. -/
theorem isRepresentableAtP_of_log {k e' : ℤ} (hk : k ≠ 0) {y : Dyadic}
    (hy : (y : ℚ) = (k : ℚ) * (2 : ℚ) ^ e') :
    IsRepresentableAtP ((Int.log 2 (|k| : ℝ)).toNat + 1) k e' y := by
  have h_one_le : (1 : ℝ) ≤ (|k| : ℝ) := by
    have h1 : (1 : ℤ) ≤ |k| := Int.one_le_abs hk
    exact_mod_cast h1
  have h_abs_pos : (0 : ℝ) < (|k| : ℝ) := by linarith
  have h_log_nn : 0 ≤ Int.log 2 (|k| : ℝ) := by
    rw [show (0 : ℤ) = Int.log 2 (1 : ℝ) by simp [Int.log_one_right]]
    exact Int.log_mono_right (by norm_num) h_one_le
  refine ⟨hy, ?_, ?_⟩
  · have h_simp : (Int.log 2 (|k| : ℝ)).toNat + 1 - 1 = (Int.log 2 (|k| : ℝ)).toNat := by
      omega
    rw [h_simp]
    have h_2pow_le : (2 : ℝ) ^ (Int.log 2 (|k| : ℝ)) ≤ (|k| : ℝ) :=
      Int.zpow_log_le_self (by norm_num : (1 : ℕ) < 2) h_abs_pos
    have h_nat : ((Int.log 2 (|k| : ℝ)).toNat : ℤ) = Int.log 2 (|k| : ℝ) :=
      Int.toNat_of_nonneg h_log_nn
    have h_cast : ((2 : ℤ) ^ (Int.log 2 (|k| : ℝ)).toNat : ℝ) =
        (2 : ℝ) ^ (Int.log 2 (|k| : ℝ)) := by
      rw [show (Int.log 2 (|k| : ℝ)) = ((Int.log 2 (|k| : ℝ)).toNat : ℤ) from
        h_nat.symm, zpow_natCast]
      push_cast; rfl
    have h_real_le : ((2 : ℤ) ^ (Int.log 2 (|k| : ℝ)).toNat : ℝ) ≤ (|k| : ℝ) := by
      rw [h_cast]; exact h_2pow_le
    exact_mod_cast h_real_le
  · have h_2pow_gt : (|k| : ℝ) < (2 : ℝ) ^ (Int.log 2 (|k| : ℝ) + 1) :=
      Int.lt_zpow_succ_log_self (by norm_num : (1 : ℕ) < 2) _
    have h_cast : ((2 : ℤ) ^ ((Int.log 2 (|k| : ℝ)).toNat + 1) : ℝ) =
        (2 : ℝ) ^ (Int.log 2 (|k| : ℝ) + 1) := by
      push_cast
      rw [← zpow_natCast (2 : ℝ) ((Int.log 2 (|k| : ℝ)).toNat + 1)]
      congr 1; push_cast; omega
    have h_real_lt : (|k| : ℝ) <
        ((2 : ℤ) ^ ((Int.log 2 (|k| : ℝ)).toNat + 1) : ℝ) := by
      rw [h_cast]; exact h_2pow_gt
    exact_mod_cast h_real_lt

/-- `IsRepresentableAtP p` pins down a unique `(c, e)` representation
(for `p ≥ 1`). The exponent is determined by `|y|` (via `Int.log`),
and the significand follows. -/
theorem IsRepresentableAtP.unique {p : ℕ} {y : Dyadic}
    {c₁ e₁ c₂ e₂ : ℤ}
    (h₁ : IsRepresentableAtP p c₁ e₁ y) (h₂ : IsRepresentableAtP p c₂ e₂ y) :
    c₁ = c₂ ∧ e₁ = e₂ := by
  obtain ⟨hy₁, hc₁_lo, hc₁_hi⟩ := h₁
  obtain ⟨hy₂, hc₂_lo, hc₂_hi⟩ := h₂
  have h_eq : (c₁ : ℚ) * (2 : ℚ) ^ e₁ = (c₂ : ℚ) * (2 : ℚ) ^ e₂ := by rw [← hy₁, ← hy₂]
  -- A representation at a strictly smaller exponent has a coefficient at least `2^p`.
  have aux : ∀ {a₁ d₁ a₂ d₂ : ℤ}, |a₁| < (2 : ℤ) ^ p → (2 : ℤ) ^ (p - 1) ≤ |a₂| →
      (a₁ : ℚ) * (2 : ℚ) ^ d₁ = (a₂ : ℚ) * (2 : ℚ) ^ d₂ → ¬ d₁ < d₂ := by
    intro a₁ d₁ a₂ d₂ ha₁_lt ha₂_lo h_eq h_lt
    have h_pow : (2 : ℤ) ≤ (2 : ℤ) ^ (d₂ - d₁).toNat := le_self_pow₀ (by norm_num) (by omega)
    rw [Mpfx.coeff_eq_of_shift h_lt.le h_eq, abs_mul,
      abs_of_pos (by positivity : (0 : ℤ) < 2 ^ (d₂ - d₁).toNat)] at ha₁_lt
    rcases p with _ | k
    · simp at ha₂_lo ha₁_lt; nlinarith [abs_nonneg a₂]
    · have h2k : (2 : ℤ) ^ k ≤ |a₂| := by simpa using ha₂_lo
      have : (2 : ℤ) ^ (k + 1) ≤ |a₂| * 2 ^ (d₂ - d₁).toNat := by
        rw [pow_succ]; exact mul_le_mul h2k h_pow (by norm_num) (abs_nonneg _)
      omega
  have h_e_eq : e₁ = e₂ := by
    have := aux hc₁_hi hc₂_lo h_eq
    have := aux hc₂_hi hc₁_lo h_eq.symm
    omega
  subst h_e_eq
  exact ⟨by exact_mod_cast mul_right_cancel₀ (zpow_ne_zero _ two_ne_zero) h_eq, rfl⟩

/-- Any nonzero integer factors as `c' * 2^k` with `c'` odd. -/
private theorem Int.exists_odd_factor {c₀ : ℤ} (hc : c₀ ≠ 0) :
    ∃ k : ℕ, ∃ c : ℤ, Odd c ∧ c₀ = c * 2^k ∧ c.natAbs ≤ c₀.natAbs := by
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (Int.natAbs_ne_zero.mpr hc)
  have hm_le : m ≤ c₀.natAbs := hn ▸ Nat.le_mul_of_pos_left m (by positivity)
  rcases Int.natAbs_eq c₀ with h | h
  · exact ⟨k, m, (Int.odd_coe_nat m).mpr hm, by rw [h, hn]; push_cast; ring, by simpa using hm_le⟩
  · exact ⟨k, -m, ((Int.odd_coe_nat m).mpr hm).neg, by rw [h, hn]; push_cast; ring,
      by simpa using hm_le⟩

/-- For any nonzero dyadic with precision at most `p`, there's a representation
`y = c·2^e` with `c` odd and `|c| < 2^p`. -/
theorem exists_odd_canonical_of_precisionAtMost {p : ℕ} {y : Dyadic}
    (hp : precisionAtMost (p : Prec) y) (hy : (y : ℝ) ≠ 0) :
    ∃ c e : ℤ, ((y : ℝ) = c * (2 : ℝ)^e) ∧ Odd c ∧ |c| < (2 : ℤ)^p := by
  rw [precisionAtMost_coe_real] at hp
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

/-- Dyadics have decidable equality (inherited from `ℚ`) — a payoff of the
rational substrate. -/
instance : DecidableEq Dyadic := Subtype.instDecidableEq

end Dyadic

/-- Non-negative dyadics: a `Dyadic` whose underlying rational is `≥ 0`. Used as
the carrier of magnitude bounds in `Format`. -/
abbrev NonNegDyadic : Type := { d : Dyadic // 0 ≤ (d : ℚ) }

/-- A magnitude bound on a format's values, or `⊤` for "unbounded". -/
abbrev Bound := WithTop NonNegDyadic

/-- Eliminator for `Bound` stating its `coe` case with the
`↑ : NonNegDyadic → Bound` coercion; see `QExp.recBotCoe`. -/
@[elab_as_elim] def Bound.recTopCoe {C : Bound → Sort*} (top : C ⊤)
    (coe : ∀ b : NonNegDyadic, C (b : Bound)) : ∀ b : Bound, C b
  | ⊤ => top
  | (b : NonNegDyadic) => coe b


/-! ### Canonical representations and casts (used by the grid lemmas) -/

/-- `ofIntZpow 1 k` is `2^k` over `ℝ` (coefficient-free form). -/
theorem coe_real_ofIntZpow_one (k : ℤ) :
    ((Dyadic.ofIntZpow 1 k : Dyadic) : ℝ) = (2 : ℝ) ^ k := by
  rw [Dyadic.coe_ofIntZpow]; push_cast; ring

/-- A dyadic that is zero over `ℝ` is zero. -/
theorem eq_zero_of_coe_real_zero {z : Dyadic} (h : (z : ℝ) = 0) : z = 0 :=
  (Dyadic.coe_real_inj z 0).mp (by rw [h, Dyadic.coe_real_zero])

/-- `2^k` (any `k`) has precision 1, hence fits any precision bound. -/
theorem precisionAtMost_one_zpow {p : Prec} (hp : p ≠ 0) (k : ℤ) :
    Dyadic.precisionAtMost p (Dyadic.ofIntZpow 1 k) := by
  cases p using ENat.recTopCoe with
  | top => trivial
  | coe p =>
    rw [Dyadic.precisionAtMost_coe]
    refine ⟨1, k, by rw [Dyadic.coe_rat_ofIntZpow], ?_⟩
    exact abs_one_lt_two_pow (Nat.pos_of_ne_zero (by simpa using hp))

/-- An odd-significand representation cannot sit below the quantum: if
`x = c·2^q` with `c` odd and `x` has quantum at least `e`, then `e ≤ q`. -/
theorem quantum_le_of_odd_rep {e : ℤ} {x : Dyadic}
    (hq : Dyadic.quantumAtLeast (e : QExp) x) {c q : ℤ}
    (hodd : Odd c) (heq : ((x : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ) ^ q) :
    e ≤ q := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, ((x : Dyadic) : ℝ) = (m : ℝ) * (2 : ℝ) ^ e := by
    rw [← Dyadic.quantumAtLeast_coe_real]; exact hq
  by_contra hlt; push Not at hlt
  have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ q := zpow_pos (by norm_num) _
  have h1 : (c : ℝ) * (2 : ℝ) ^ q = (m : ℝ) * (2 : ℝ) ^ e := by rw [← heq, hm]
  have h2 : (m : ℝ) * (2 : ℝ) ^ (e - q) * (2 : ℝ) ^ q = (m : ℝ) * (2 : ℝ) ^ e := by
    rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), sub_add_cancel]
  have hce : (c : ℝ) = (m : ℝ) * (2 : ℝ) ^ (e - q) :=
    mul_right_cancel₀ (ne_of_gt h2q_pos) (h1.trans h2.symm)
  have hcast : ((m * 2 ^ (e - q).toNat : ℤ) : ℝ) = (m : ℝ) * (2 : ℝ) ^ (e - q) := by
    push_cast
    rw [← zpow_natCast (2 : ℝ) ((e - q).toNat), Int.toNat_of_nonneg (by omega)]
  have hc_int : c = m * 2 ^ (e - q).toNat := by
    exact_mod_cast hce.trans hcast.symm
  have h2dvd : (2 : ℤ) ∣ c := by
    rw [hc_int]
    exact dvd_mul_of_dvd_right (dvd_pow_self 2 (by omega)) m
  rcases hodd with ⟨t, ht⟩
  omega

namespace Dyadic

/-- Odd-significand representations are unique: `quantum_le_of_odd_rep` in both
directions pins the exponent, and cancellation the significand. -/
private theorem odd_rep_unique {x : Dyadic} {c q c' q' : ℤ} (hc : Odd c) (hc' : Odd c')
    (h : (x : ℝ) = (c : ℝ) * (2 : ℝ) ^ q) (h' : (x : ℝ) = (c' : ℝ) * (2 : ℝ) ^ q') :
    c = c' ∧ q = q' := by
  have hq : quantumAtLeast (q : QExp) x := (quantumAtLeast_coe_real q x).mpr ⟨c, h⟩
  have hq' : quantumAtLeast (q' : QExp) x := (quantumAtLeast_coe_real q' x).mpr ⟨c', h'⟩
  obtain rfl : q = q' :=
    le_antisymm (quantum_le_of_odd_rep hq hc' h') (quantum_le_of_odd_rep hq' hc h)
  refine ⟨?_, rfl⟩
  have h2q : (0 : ℝ) < (2 : ℝ) ^ q := zpow_pos (by norm_num) _
  exact_mod_cast mul_right_cancel₀ (ne_of_gt h2q) (h.symm.trans h')

/-- The odd canonical representation is the narrowest one: if `x = c · 2^q` with
`c` odd and `|c| ≥ 2^p`, then `x` does not fit in `p` digits. -/
theorem not_precisionAtMost_of_odd {p : ℕ} {x : Dyadic} {c q : ℤ}
    (hc : Odd c) (h : (x : ℝ) = (c : ℝ) * (2 : ℝ) ^ q) (hge : (2 : ℤ) ^ p ≤ |c|) :
    ¬ precisionAtMost (p : Prec) x := by
  intro hp
  have hc_ne : c ≠ 0 := by
    have : (0 : ℤ) < 2 ^ p := by positivity
    intro h0; rw [h0, abs_zero] at hge; omega
  have hx_ne : (x : ℝ) ≠ 0 := by
    rw [h]
    exact mul_ne_zero (Int.cast_ne_zero.mpr hc_ne) (ne_of_gt (zpow_pos (by norm_num) _))
  obtain ⟨c', q', h', hc'_odd, hc'_lt⟩ := exists_odd_canonical_of_precisionAtMost hp hx_ne
  obtain ⟨rfl, -⟩ := odd_rep_unique hc hc'_odd h h'
  omega

/-- The dyadic value `3 · 2^k` is *not* representable at precision 1: `3` is odd
and two digits wide. Used as a precision-2 witness to force `2 ≤ F₂.p` from a
containment hypothesis. -/
theorem not_precisionAtMost_one_three_zpow (k : ℤ) :
    ¬ precisionAtMost ((1 : ℕ) : Prec) (Dyadic.ofIntZpow 3 k) :=
  not_precisionAtMost_of_odd (by norm_num : Odd (3 : ℤ)) (by rw [coe_ofIntZpow]) (by norm_num)

end Dyadic

/-- Odd canonical representation of a positive dyadic at precision `p`,
packaged with positivity and binade bounds: `b = c·2^q` with `c` odd and
positive, `2^q ≤ b`, and `q ≤ ⌊log₂ b⌋ < q + p`. -/
theorem exists_odd_canonical_pos {p : ℕ} {b : Dyadic}
    (hb_p : Dyadic.precisionAtMost (p : Prec) b)
    (hb_pos : 0 < ((b : Dyadic) : ℝ)) :
    ∃ c q : ℤ, ((b : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ) ^ q ∧ Odd c ∧ 0 < c ∧
      (2 : ℝ) ^ q ≤ ((b : Dyadic) : ℝ) ∧
      q ≤ Int.log 2 ((b : Dyadic) : ℝ) ∧
      Int.log 2 ((b : Dyadic) : ℝ) < q + (p : ℤ) := by
  obtain ⟨c, q, hc_eq, hc_odd, hc_lt⟩ :=
    Dyadic.exists_odd_canonical_of_precisionAtMost hb_p (ne_of_gt hb_pos)
  have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ q := zpow_pos (by norm_num) _
  have hc_pos : 0 < c := by
    by_contra h; push Not at h
    have hcr : (c : ℝ) ≤ 0 := by exact_mod_cast h
    nlinarith
  have hc1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc_pos
  have h_lb : (2 : ℝ) ^ q ≤ ((b : Dyadic) : ℝ) := by rw [hc_eq]; nlinarith
  have hcp : (c : ℝ) < (2 : ℝ) ^ (p : ℤ) := by
    rw [zpow_natCast]
    have h1 : (c : ℝ) < ((2 ^ p : ℤ) : ℝ) := by
      exact_mod_cast lt_of_abs_lt hc_lt
    push_cast at h1; exact h1
  have h_ub : ((b : Dyadic) : ℝ) < (2 : ℝ) ^ (q + (p : ℤ)) := by
    rw [hc_eq, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    calc (c : ℝ) * (2 : ℝ) ^ q < (2 : ℝ) ^ (p : ℤ) * (2 : ℝ) ^ q := by nlinarith
      _ = (2 : ℝ) ^ q * (2 : ℝ) ^ (p : ℤ) := by ring
  exact ⟨c, q, hc_eq, hc_odd, hc_pos, h_lb,
    (Int.zpow_le_iff_le_log (by norm_num) hb_pos).mp h_lb,
    (Int.lt_zpow_iff_log_lt (by norm_num) hb_pos).mp h_ub⟩

/-- The order on `NonNegDyadic`, in terms of the underlying reals. -/
theorem NonNegDyadic.le_iff_coe_real {a b : NonNegDyadic} :
    a ≤ b ↔ ((a.val : Dyadic) : ℝ) ≤ ((b.val : Dyadic) : ℝ) := by
  rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast, Rat.cast_le]
  exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩

/-- A `NonNegDyadic` is non-negative over `ℝ`. -/
theorem nonneg_coe_real (b : NonNegDyadic) : 0 ≤ ((b.val : Dyadic) : ℝ) := by
  exact_mod_cast b.2

end Mpfx
