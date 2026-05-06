import Mpfx.Format
import Mathlib.Data.Int.Log

/-!
# Lemmas 5.1 and 5.2 — digit positions of roundings

Lemma 5.1 says the number of binary digits a rounding `rnd_{A(p,exp,b),rm}(x)`
keeps is a function of `(p, exp, x)` only — not of `b` or `rm`. In our
spec-relational setup we capture this by *defining* `numDigits` via the same
case analysis the paper's proof uses; the type signature `ℕ∞ → WithBot ℤ → ℝ → ℕ`
*is* Lemma 5.1.

Lemma 5.2 says shifting parameters by `(p, exp) ↦ (p + k, exp − k)` shifts the
digit count by `+k`. We prove this for `x ≠ 0` and non-degenerate formats
(the case `p = ⊤ ∧ exp = ⊥` is excluded — there is no quantum and no precision,
so no rounding happens).
-/

namespace Mpfx

namespace AbstractFormat

/-- Subtract a natural number from a `WithBot ℤ`. `⊥ - k = ⊥`. -/
def expSub (e : WithBot ℤ) (k : ℕ) : WithBot ℤ :=
  e.map (· - (k : ℤ))

@[simp] theorem expSub_bot (k : ℕ) : expSub ⊥ k = ⊥ := rfl

@[simp] theorem expSub_coe (e : ℤ) (k : ℕ) :
    expSub (e : WithBot ℤ) k = ((e - k : ℤ) : WithBot ℤ) := rfl

/-- **Lemma 5.1**: number of binary digits a format `(p, exp)` rounds `x` to.

Case analysis follows the paper's proof of Lemma 5.1:
- `p = ⊤, exp = ⊥`: degenerate (no rounding happens); return `0`.
- `p = ⊤, exp = e`: fixed-point with quantum `2^e`. Digits = `⌊log₂|x|⌋ - e + 1`.
- `p = n, exp = ⊥`: pure floating-point with precision `n`. Digits = `n`.
- `p = n, exp = e`: floating-point with min quantum `2^e`. Digits = `min(n, e' - e + 1)`
  where `e' = ⌊log₂|x|⌋`. The `min` captures subnormal behaviour.

The result is `ℤ`-valued: a negative or zero result indicates the rounding
underflows to `0`. For `x = 0` we return `0` by convention. -/
noncomputable def numDigits (p : ℕ∞) (exp : WithBot ℤ) (x : ℝ) : ℤ :=
  if x = 0 then 0
  else
    let e : ℤ := Int.log 2 |x|
    match p, exp with
    | ⊤, ⊥ => 0
    | ⊤, ((e' : ℤ) : WithBot ℤ) => e - e' + 1
    | ((n : ℕ) : ℕ∞), ⊥ => (n : ℤ)
    | ((n : ℕ) : ℕ∞), ((e' : ℤ) : WithBot ℤ) => min (n : ℤ) (e - e' + 1)

/-- **Lemma 5.2**: shifting `(p, exp)` by `(+k, -k)` shifts digits by `+k`.

Excludes the degenerate `p = ⊤ ∧ exp = ⊥` case where `numDigits` returns `0`
regardless. Requires `x ≠ 0`. -/
theorem numDigits_shift (p : ℕ∞) (exp : WithBot ℤ) (k : ℕ) (x : ℝ) (hx : x ≠ 0)
    (hnd : p ≠ ⊤ ∨ exp ≠ ⊥) :
    numDigits (p + k) (expSub exp k) x = numDigits p exp x + k := by
  unfold numDigits
  simp only [hx, ↓reduceIte]
  match hp : p, hexp : exp with
  | ⊤, ⊥ => simp at hnd
  | ⊤, ((e' : ℤ) : WithBot ℤ) =>
    change Int.log 2 |x| - (e' - (k : ℤ)) + 1 = Int.log 2 |x| - e' + 1 + k
    ring
  | ((n : ℕ) : ℕ∞), ⊥ =>
    change ((n + k : ℕ) : ℤ) = (n : ℤ) + k
    push_cast; ring
  | ((n : ℕ) : ℕ∞), ((e' : ℤ) : WithBot ℤ) =>
    change min ((n + k : ℕ) : ℤ) (Int.log 2 |x| - (e' - (k : ℤ)) + 1)
        = min (n : ℤ) (Int.log 2 |x| - e' + 1) + k
    have h1 : Int.log 2 |x| - (e' - (k : ℤ)) + 1 = Int.log 2 |x| - e' + 1 + k := by ring
    rw [h1]
    omega

/-- `numDigits` is invariant under negation of `x`: `|x| = |-x|`. -/
theorem numDigits_neg (p : ℕ∞) (exp : WithBot ℤ) (x : ℝ) :
    numDigits p exp (-x) = numDigits p exp x := by
  unfold numDigits
  by_cases hx : x = 0
  · subst hx; simp
  · have hxne' : -x ≠ 0 := neg_ne_zero.mpr hx
    have habs : |(-x)| = |x| := abs_neg x
    simp only [hx, hxne', ↓reduceIte, habs]

@[simp] theorem numDigits_zero (p : ℕ∞) (exp : WithBot ℤ) :
    numDigits p exp 0 = 0 := by unfold numDigits; simp

/-- If `y ∈ F`, then `y` has a representation with at most `numDigits F.p F.exp y`
binary digits. This bridges format membership to the Lemma 5.1 effective
precision: even in subnormal regimes (where `F.p > numDigits F y`), `y`'s
significand is bounded by `2^(numDigits F y)`. -/
theorem mem_imp_precisionAtMost_numDigits {F : AbstractFormat} {y : Dyadic}
    (hy : y ∈ F) :
    Dyadic.precisionAtMost ((numDigits F.p F.exp (y : ℝ)).toNat : ℕ∞) y := by
  obtain ⟨hP, hQ, _⟩ := hy
  by_cases hy0 : (y : ℝ) = 0
  · -- y = 0: numDigits = 0, precisionAtMost 0 y holds via c = 0, e = 0
    have h_nd : numDigits F.p F.exp (y : ℝ) = 0 := by unfold numDigits; simp [hy0]
    rw [h_nd]
    change Dyadic.precisionAtMost ((0 : ℕ) : ℕ∞) y
    rw [Dyadic.precisionAtMost_coe]
    refine ⟨0, 0, ?_, by norm_num⟩
    rw [hy0]; push_cast; ring
  -- y ≠ 0
  set e_y : ℤ := Int.log 2 |(y : ℝ)| with he_y_def
  have habs_pos : 0 < |(y : ℝ)| := abs_pos.mpr hy0
  have hlogN : (1 : ℕ) < 2 := by norm_num
  have hlogR : (1 : ℝ) < 2 := by norm_num
  have he_y_hi : |(y : ℝ)| < (2 : ℝ) ^ (e_y + 1) := Int.lt_zpow_succ_log_self hlogN _
  -- "Quantum" subproof: from y = c·2^e' (and e' ≤ e_y), derive precisionAtMost (e_y - e' + 1).
  have quantum_case : ∀ e' : ℤ,
      (∃ c : ℤ, (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ e') →
      e' ≤ e_y →
      Dyadic.precisionAtMost (((e_y - e' + 1).toNat : ℕ) : ℕ∞) y := by
    intro e' hQ' he_y_ge
    obtain ⟨c, hyeq⟩ := hQ'
    have h2pos : (0 : ℝ) < 2 := by norm_num
    have h2e'_pos : (0 : ℝ) < (2 : ℝ) ^ e' := zpow_pos h2pos _
    have h_real : (|c| : ℝ) < (2 : ℝ) ^ (e_y - e' + 1) := by
      have h_y_eq : |(y : ℝ)| = |(c : ℝ)| * (2 : ℝ) ^ e' := by
        rw [hyeq, abs_mul, abs_zpow, abs_of_pos h2pos]
      have hsplit : (2 : ℝ) ^ (e_y + 1) =
          (2 : ℝ) ^ (e_y - e' + 1) * (2 : ℝ) ^ e' := by
        rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        congr 1; ring
      have key : |(c : ℝ)| * (2 : ℝ) ^ e' < (2 : ℝ) ^ (e_y - e' + 1) * (2 : ℝ) ^ e' := by
        rw [← hsplit, ← h_y_eq]; exact he_y_hi
      exact lt_of_mul_lt_mul_right key (le_of_lt h2e'_pos)
    have h_nat : ((e_y - e' + 1).toNat : ℤ) = e_y - e' + 1 :=
      Int.toNat_of_nonneg (by omega)
    rw [Dyadic.precisionAtMost_coe]
    refine ⟨c, e', hyeq, ?_⟩
    have : (|c| : ℝ) < ((2 : ℤ) ^ (e_y - e' + 1).toNat : ℝ) := by
      rw [show ((2 : ℤ) ^ (e_y - e' + 1).toNat : ℝ) =
          (2 : ℝ) ^ ((e_y - e' + 1).toNat : ℤ) by push_cast; rfl, h_nat]
      exact h_real
    exact_mod_cast this
  -- e' ≤ e_y from quantum constraint when y ≠ 0
  have e'_le_e_y : ∀ e' : ℤ,
      (∃ c : ℤ, (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ e') → e' ≤ e_y := by
    intro e' ⟨c, hyeq⟩
    have hc_ne : c ≠ 0 := by
      intro hc0; rw [hc0] at hyeq; push_cast at hyeq
      rw [zero_mul] at hyeq; exact hy0 hyeq
    have hc_abs_ge : (1 : ℤ) ≤ |c| := Int.one_le_abs hc_ne
    have h2pos : (0 : ℝ) < 2 := by norm_num
    have h2e'_pos : (0 : ℝ) < (2 : ℝ) ^ e' := zpow_pos h2pos _
    have habs_lo : (2 : ℝ) ^ e' ≤ |(y : ℝ)| := by
      rw [hyeq, abs_mul, abs_zpow, abs_of_pos h2pos]
      calc (2 : ℝ) ^ e'
          = 1 * (2 : ℝ) ^ e' := (one_mul _).symm
        _ ≤ |(c : ℝ)| * (2 : ℝ) ^ e' := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt h2e'_pos)
            rw [show ((1 : ℝ) : ℝ) = ((1 : ℤ) : ℝ) from by norm_num,
                ← Int.cast_abs]
            exact_mod_cast hc_abs_ge
    -- e' ≤ e_y: suppose e_y < e', then 2^(e_y+1) ≤ 2^e' ≤ |y| < 2^(e_y+1) — contradiction
    by_contra h_lt
    push Not at h_lt
    have h_step : e_y + 1 ≤ e' := by omega
    have h_pow_le : (2 : ℝ) ^ (e_y + 1) ≤ (2 : ℝ) ^ e' :=
      zpow_le_zpow_right₀ (by norm_num) h_step
    linarith [habs_lo, he_y_hi]
  -- Main case analysis on (F.p, F.exp). Use `change` per arm to materialize
  -- the unfolded numDigits value (style mirrors `numDigits_shift`).
  unfold numDigits
  simp only [hy0, ↓reduceIte]
  match hp : F.p, hexp : F.exp with
  | ⊤, ⊥ =>
    exfalso; rcases F.not_degenerate with h | h
    · exact h hp
    · exact h hexp
  | ⊤, ((e' : ℤ) : WithBot ℤ) =>
    change Dyadic.precisionAtMost (((Int.log 2 |(y : ℝ)| - e' + 1).toNat : ℕ) : ℕ∞) y
    rw [hexp] at hQ
    exact quantum_case e' hQ (e'_le_e_y e' hQ)
  | ((n : ℕ) : ℕ∞), ⊥ =>
    change Dyadic.precisionAtMost ((((n : ℤ).toNat : ℕ) : ℕ∞)) y
    have hcast : (((n : ℤ).toNat : ℕ) : ℕ∞) = ((n : ℕ∞)) := by simp
    rw [hcast]
    rw [hp] at hP
    exact hP
  | ((n : ℕ) : ℕ∞), ((e' : ℤ) : WithBot ℤ) =>
    change Dyadic.precisionAtMost
      (((min ((n : ℤ)) (Int.log 2 |(y : ℝ)| - e' + 1)).toNat : ℕ) : ℕ∞) y
    rcases le_or_gt ((n : ℤ)) (e_y - e' + 1) with hcase | hcase
    · rw [show min ((n : ℕ) : ℤ) (Int.log 2 |(y : ℝ)| - e' + 1) = (n : ℤ) from
          min_eq_left hcase]
      have hcast : (((n : ℤ).toNat : ℕ) : ℕ∞) = ((n : ℕ∞)) := by simp
      rw [hcast]
      rw [hp] at hP
      exact hP
    · rw [show min ((n : ℕ) : ℤ) (Int.log 2 |(y : ℝ)| - e' + 1)
          = e_y - e' + 1 from min_eq_right (le_of_lt hcase)]
      rw [hexp] at hQ
      exact quantum_case e' hQ (e'_le_e_y e' hQ)

/-- Parity of `y` in format `F`. The precision used is `numDigits F.p F.exp y`
(intrinsic to `y` in `F`); the *type* of parity test depends on `F.p`:

- If `F.p = 1`: every nonzero value's significand is `±1` (always odd by integer
  convention), so parity is determined by the *exponent*.
- Otherwise (including `F.p = ⊤`): parity is determined by the *significand*.

For `y = 0`: `IsOdd F y = False` (zero is conventionally even). For `y` whose
canonical precision exceeds `numDigits F.p F.exp y`: also `False` (no
representation at the right precision). -/
def IsOdd (F : AbstractFormat) (y : Dyadic) : Prop :=
  ∃ c e : ℤ,
    Dyadic.IsRepresentableAtP (numDigits F.p F.exp (y : ℝ)).toNat c e y ∧
    (if F.p = (1 : ℕ∞) then Odd e else Odd c)

/-- Even-parity dual of `IsOdd`. Convention: `0` is even at every format. -/
def IsEven (F : AbstractFormat) (y : Dyadic) : Prop :=
  y = 0 ∨ ∃ c e : ℤ,
    Dyadic.IsRepresentableAtP (numDigits F.p F.exp (y : ℝ)).toNat c e y ∧
    (if F.p = (1 : ℕ∞) then Even e else Even c)

@[simp] theorem isEven_zero (F : AbstractFormat) : IsEven F 0 := Or.inl rfl

/-- `IsOdd` is invariant under negation. -/
theorem IsOdd.neg {F : AbstractFormat} {y : Dyadic} (h : IsOdd F y) :
    IsOdd F (-y) := by
  obtain ⟨c, e, ⟨hyeq, hlow, hhigh⟩, hp⟩ := h
  have h_nd : numDigits F.p F.exp ((-y : Dyadic) : ℝ) =
      numDigits F.p F.exp (y : ℝ) := by
    change numDigits F.p F.exp (-(y : ℝ)) = _
    exact numDigits_neg F.p F.exp (y : ℝ)
  refine ⟨-c, e, ⟨?_, ?_, ?_⟩, ?_⟩
  · change ((-y : Dyadic) : ℝ) = _
    push_cast
    rw [hyeq]; ring
  · rw [h_nd]; simpa using hlow
  · rw [h_nd]; simpa using hhigh
  · by_cases hp1 : F.p = 1
    · rw [if_pos hp1]; rw [if_pos hp1] at hp; exact hp
    · rw [if_neg hp1]; rw [if_neg hp1] at hp; exact Odd.neg hp

theorem isOdd_neg_iff (F : AbstractFormat) (y : Dyadic) :
    IsOdd F (-y) ↔ IsOdd F y :=
  ⟨fun h => by simpa using h.neg, IsOdd.neg⟩

/-- `IsOdd F y` implies `numDigits F.p F.exp y ≥ 1`. If `numDigits` were ≤ 0, the
`IsRepresentableAtP` witness would force `1 ≤ |c| < 1`, a contradiction. -/
theorem IsOdd.numDigits_pos {F : AbstractFormat} {y : Dyadic} (h : IsOdd F y) :
    0 < numDigits F.p F.exp (y : ℝ) := by
  obtain ⟨c, _, ⟨_, hlow, hhigh⟩, _⟩ := h
  by_contra h_le
  push Not at h_le
  have h_toNat : (numDigits F.p F.exp ((y : Dyadic) : ℝ)).toNat = 0 :=
    Int.toNat_of_nonpos h_le
  rw [h_toNat] at hlow hhigh
  -- hlow : 2^(0 - 1) ≤ |c| reduces to 1 ≤ |c|; hhigh : |c| < 2^0 = 1
  have h1 : (1 : ℤ) ≤ |c| := by simpa using hlow
  have h2 : |c| < (1 : ℤ) := by simpa using hhigh
  omega

/-- An `IsOdd F y` value is nonzero. -/
theorem IsOdd.ne_zero {F : AbstractFormat} {y : Dyadic} (h : IsOdd F y) :
    y ≠ 0 := by
  intro hy0
  obtain ⟨c, e, ⟨hyeq, hlow, _⟩, _⟩ := h
  rw [hy0] at hyeq
  have h2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have hc_zero : (c : ℝ) = 0 := by
    push_cast at hyeq
    rcases mul_eq_zero.mp hyeq.symm with h | h
    · exact h
    · linarith
  have hc_zero_int : c = 0 := by exact_mod_cast hc_zero
  rw [hc_zero_int, abs_zero] at hlow
  have : (1 : ℤ) ≤ (2 : ℤ) ^ ((numDigits F.p F.exp ((y : Dyadic) : ℝ)).toNat - 1) :=
    one_le_pow₀ (by norm_num)
  linarith

/-- `numDigits F.p F.exp x ≤ 1` whenever `F.p = 1`. -/
theorem numDigits_le_one_of_p_one {p : ℕ∞} (hp1 : p = 1) (exp : WithBot ℤ) (x : ℝ) :
    numDigits p exp x ≤ 1 := by
  rw [hp1]
  unfold numDigits
  by_cases hx : x = 0
  · simp [hx]
  · simp only [hx, ↓reduceIte]
    -- match on exp: ⊥ or coe e'
    cases exp with
    | bot =>
      change ((1 : ℕ) : ℤ) ≤ 1
      norm_num
    | coe e' =>
      change min ((1 : ℕ) : ℤ) (Int.log 2 |x| - e' + 1) ≤ 1
      exact min_le_left _ _

/-- **Lemma 5.3 corollary** (format-parameterized form): If `y` has precision at
most `w` and the rounding precision in `F` (= `numDigits F.p F.exp y`) strictly
exceeds `w`, then `y` cannot be `IsOdd F`. -/
theorem precisionAtMost_not_IsOdd {F : AbstractFormat} {w : ℕ} {y : Dyadic}
    (hgt : (w : ℤ) < numDigits F.p F.exp (y : ℝ))
    (hprec : Dyadic.precisionAtMost (w : ℕ∞) y) :
    ¬ IsOdd F y := by
  intro hodd
  have hy_ne_zero : y ≠ 0 := hodd.ne_zero
  -- Case w = 0: precisionAtMost 0 forces y = 0, contradicting IsOdd's nonzero
  by_cases hw0 : w = 0
  · subst hw0
    rw [Dyadic.precisionAtMost_coe] at hprec
    obtain ⟨c, e, hy_eq, hc_lt⟩ := hprec
    have habs_lt : |c| < 1 := by simpa using hc_lt
    have habs_nn : 0 ≤ |c| := abs_nonneg _
    have hc_zero : c = 0 := by
      have : |c| = 0 := by omega
      exact abs_eq_zero.mp this
    rw [hc_zero] at hy_eq
    push_cast at hy_eq
    rw [zero_mul] at hy_eq
    have : (y : ℝ) = ((0 : Dyadic) : ℝ) := by rw [hy_eq]; rfl
    exact hy_ne_zero (Subtype.ext this)
  -- Case w ≥ 1
  have hw_pos : 1 ≤ w := Nat.one_le_iff_ne_zero.mpr hw0
  obtain ⟨c₁, e₁, ⟨hy_eq₁, hlow, _hhigh⟩, hp_check⟩ := hodd
  set p_y : ℕ := (numDigits F.p F.exp (y : ℝ)).toNat with hp_y_def
  have h_nd_pos : 0 ≤ numDigits F.p F.exp (y : ℝ) := by linarith
  have h_pyZ : (p_y : ℤ) = numDigits F.p F.exp (y : ℝ) := Int.toNat_of_nonneg h_nd_pos
  have hp_y_ge : p_y ≥ w + 1 := by
    have : (p_y : ℤ) ≥ (w : ℤ) + 1 := by rw [h_pyZ]; linarith
    exact_mod_cast this
  -- Show F.p ≠ 1 (else numDigits F y ≤ 1, but we have numDigits ≥ w + 1 ≥ 2)
  have hFp_ne_1 : F.p ≠ 1 := by
    intro hFp1
    have h_le := numDigits_le_one_of_p_one hFp1 F.exp (y : ℝ)
    have : (p_y : ℤ) ≤ 1 := by rw [h_pyZ]; exact h_le
    have : p_y ≤ 1 := by exact_mod_cast this
    omega
  rw [if_neg hFp_ne_1] at hp_check
  have hc₁_odd : Odd c₁ := hp_check
  -- Inline the contradiction (formerly Dyadic.precisionAtMost_not_isOddAtP)
  set k : ℕ := p_y - w with hk_def
  have hk_pos : 1 ≤ k := by omega
  have hpyw : p_y = w + k := by omega
  rw [Dyadic.precisionAtMost_coe] at hprec
  obtain ⟨c₂, e₂, hy_eq₂, hc₂_low⟩ := hprec
  have heq_real : (c₁ : ℝ) * (2 : ℝ) ^ e₁ = (c₂ : ℝ) * (2 : ℝ) ^ e₂ := by
    rw [← hy_eq₁]; exact hy_eq₂
  have h2ne : (2 : ℝ) ≠ 0 := two_ne_zero
  have h2pos : (0 : ℝ) < 2 := by norm_num
  rcases lt_or_ge e₁ e₂ with he | he
  · -- e₁ < e₂: c₁ = c₂ * 2^(e₂-e₁), so c₁ is even, contradicting Odd c₁
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
      rw [heq_int,
          show (e₂ - e₁).toNat = ((e₂ - e₁).toNat - 1) + 1 from by omega, pow_succ]
      exact ⟨c₂ * 2 ^ ((e₂ - e₁).toNat - 1), by ring⟩
    exact (Int.not_even_iff_odd.mpr hc₁_odd) h_even
  · -- e₁ ≥ e₂: c₂ = c₁ * 2^(e₁-e₂), so |c₂| ≥ |c₁| ≥ 2^(p_y - 1) ≥ 2^w, contradicting |c₂| < 2^w
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
    -- |c₂| = |c₁| * 2^(e₁ - e₂) ≥ 2^(p_y - 1) ≥ 2^w, contradicting |c₂| < 2^w.
    have h_abs : |c₂| = |c₁| * 2 ^ (e₁ - e₂).toNat := by
      rw [heq_int, abs_mul, abs_pow]; congr 1
    -- 2^(p_y - 1) ≤ |c₁|
    have hlow' : (2 : ℤ) ^ (p_y - 1) ≤ |c₁| := hlow
    have hpow_le : (2 : ℤ) ^ w ≤ (2 : ℤ) ^ (p_y - 1) := by
      apply pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
      omega
    have h2pow_pos : (0 : ℤ) < 2 ^ (e₁ - e₂).toNat := by positivity
    have h_one_le : (1 : ℤ) ≤ 2 ^ (e₁ - e₂).toNat := h2pow_pos
    have h_chain : (2 : ℤ) ^ w ≤ |c₂| := by
      calc (2 : ℤ) ^ w
          ≤ (2 : ℤ) ^ (p_y - 1) := hpow_le
        _ ≤ |c₁| := hlow'
        _ = |c₁| * 1 := (mul_one _).symm
        _ ≤ |c₁| * 2 ^ (e₁ - e₂).toNat :=
            mul_le_mul_of_nonneg_left h_one_le (abs_nonneg _)
        _ = |c₂| := h_abs.symm
    exact absurd (lt_of_le_of_lt h_chain hc₂_low) (lt_irrefl _)

end AbstractFormat

end Mpfx
