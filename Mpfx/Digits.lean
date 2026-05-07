import Mpfx.Containment
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

/-- Specialization of `numDigits_shift` to `AbstractFormat.extend`: extending
`F` by `k` extends the digit count at every nonzero `x` by exactly `k`. -/
theorem numDigits_extend (F : AbstractFormat) (k : ℕ) {x : ℝ} (hx : x ≠ 0) :
    numDigits (F.extend k).p (F.extend k).exp x = numDigits F.p F.exp x + k := by
  change numDigits (F.p + k) (expSub F.exp k) x = numDigits F.p F.exp x + k
  exact numDigits_shift F.p F.exp k x hx F.not_doubly_unbounded

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

/-- Compute `numDigits` for each non-degenerate `(p, exp)` shape. -/
theorem numDigits_top_coe' {x : ℝ} (hx : x ≠ 0) (e' : ℤ) :
    numDigits ⊤ ((e' : ℤ) : WithBot ℤ) x = Int.log 2 |x| - e' + 1 := by
  unfold numDigits
  split_ifs with h
  · exact absurd h hx
  · rfl

theorem numDigits_coe_bot' {x : ℝ} (hx : x ≠ 0) (n : ℕ) :
    numDigits ((n : ℕ) : ℕ∞) ⊥ x = (n : ℤ) := by
  unfold numDigits
  split_ifs with h
  · exact absurd h hx
  · rfl

theorem numDigits_coe_coe' {x : ℝ} (hx : x ≠ 0) (n : ℕ) (e' : ℤ) :
    numDigits ((n : ℕ) : ℕ∞) ((e' : ℤ) : WithBot ℤ) x
      = min ((n : ℕ) : ℤ) (Int.log 2 |x| - e' + 1) := by
  unfold numDigits
  split_ifs with h
  · exact absurd h hx
  · rfl

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
    have h_real : (|c| : ℝ) < (2 : ℝ) ^ (e_y - e' + 1) := by
      have h_y_eq : |(y : ℝ)| = |(c : ℝ)| * (2 : ℝ) ^ e' := by
        rw [hyeq, abs_mul_two_zpow]
      have hsplit : (2 : ℝ) ^ (e_y + 1) =
          (2 : ℝ) ^ (e_y - e' + 1) * (2 : ℝ) ^ e' := by
        rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        congr 1; ring
      have key : |(c : ℝ)| * (2 : ℝ) ^ e' < (2 : ℝ) ^ (e_y - e' + 1) * (2 : ℝ) ^ e' := by
        rw [← hsplit, ← h_y_eq]; exact he_y_hi
      exact lt_of_mul_lt_mul_right key (le_of_lt (two_zpow_pos e'))
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
    have habs_lo : (2 : ℝ) ^ e' ≤ |(y : ℝ)| := by
      rw [hyeq, abs_mul_two_zpow]
      calc (2 : ℝ) ^ e'
          = 1 * (2 : ℝ) ^ e' := (one_mul _).symm
        _ ≤ |(c : ℝ)| * (2 : ℝ) ^ e' := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt (two_zpow_pos e'))
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
    exfalso; rcases F.not_degenerate with ⟨hp_top, _⟩ | hexp_ne
    · exact hp_top hp
    · exact hexp_ne hexp
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

- If `F.p = 1`: parity is determined by *index counting from 0*. The structural
  invariant guarantees `F.exp ≠ ⊥`, so values are `0, ±2^F.exp, ±2^(F.exp+1), …`
  with index `e − F.exp + 1`. Odd-index values (1st, 3rd, 5th, …) are "odd".
- Otherwise (including `F.p = ⊤`): parity is determined by the *significand*.

For `y = 0`: `IsOdd F y = False` (zero is conventionally even). For `y` whose
canonical precision exceeds `numDigits F.p F.exp y`: also `False` (no
representation at the right precision). -/
def IsOdd (F : AbstractFormat) (y : Dyadic) : Prop :=
  ∃ c e : ℤ,
    Dyadic.IsRepresentableAtP (numDigits F.p F.exp (y : ℝ)).toNat c e y ∧
    (if F.p = (1 : ℕ∞) then Odd (e - WithBot.unbotD 0 F.exp + 1) else Odd c)

/-- Even-parity dual of `IsOdd`. Convention: `0` is even at every format. -/
def IsEven (F : AbstractFormat) (y : Dyadic) : Prop :=
  y = 0 ∨ ∃ c e : ℤ,
    Dyadic.IsRepresentableAtP (numDigits F.p F.exp (y : ℝ)).toNat c e y ∧
    (if F.p = (1 : ℕ∞) then Even (e - WithBot.unbotD 0 F.exp + 1) else Even c)

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

/-- `IsEven` is invariant under negation. -/
theorem IsEven.neg {F : AbstractFormat} {y : Dyadic} (h : IsEven F y) :
    IsEven F (-y) := by
  rcases h with hy0 | ⟨c, e, ⟨hyeq, hlow, hhigh⟩, hp⟩
  · left; rw [hy0]; simp
  · right
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
      · rw [if_neg hp1]; rw [if_neg hp1] at hp; exact Even.neg hp

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

/-- Under `F₁ ⊆ F₂` with `F₂.p ≥ 2` and an `IsOdd F₂ y` value `y ∈ F₁`, the
effective precisions in `F₁` and `F₂` at `y` agree.

**Proof strategy:**
- `≥`: Lemma 5.3 corollary (`precisionAtMost_not_IsOdd`).
- `≤`: by contradiction. Suppose `numDigits F₁ y > numDigits F₂ y =: p₂`.
  Then `F₁.p > p₂ ∧ e > F₁.exp` where `(c, e)` is `y`'s F₂-canonical
  (`c` odd, `|c| ∈ [2^(p₂-1), 2^p₂)`).
  Construct `y'' = y - sign(c)·2^(e-1)` ("finer-grid" F₁ neighbor):
  - `y'' ∈ F₁` via (a) `|2c-sign(c)| < 2^(p₂+1) ≤ 2^F₁.p`,
    (b) `e-1 ≥ F₁.exp`, (c) `|y''| < |y| ≤ F₁.b`.
  - `y'' ∉ F₂`: integer reps have odd numerator → `|c'''| > 2^p₂` so
    precision fails when `F₂.p = p₂`; smallest `e''' = e-1 < F₂.exp` so
    quantum fails when `F₂.p > p₂` (subnormal regime).
  - `y'' ∈ F₁ ⊆ F₂` contradicts `y'' ∉ F₂`. -/
theorem numDigits_eq_of_subset_of_isOdd {F₁ F₂ : AbstractFormat}
    (hsub : F₁ ⊆ F₂)
    (hp_F₂ : 2 ≤ F₂.p)
    {y : Dyadic} (hyF₁ : y ∈ F₁) (hodd : IsOdd F₂ y) :
    numDigits F₁.p F₁.exp (y : ℝ) = numDigits F₂.p F₂.exp (y : ℝ) := by
  have h_F₂_pos : 0 < numDigits F₂.p F₂.exp ((y : Dyadic) : ℝ) := hodd.numDigits_pos
  have h_prec_F₁ : Dyadic.precisionAtMost
      (((numDigits F₁.p F₁.exp ((y : Dyadic) : ℝ)).toNat : ℕ) : ℕ∞) y :=
    mem_imp_precisionAtMost_numDigits hyF₁
  have h_ge_int : ((numDigits F₁.p F₁.exp ((y : Dyadic) : ℝ)).toNat : ℤ) ≥
      numDigits F₂.p F₂.exp ((y : Dyadic) : ℝ) := by
    by_contra h
    push Not at h
    exact precisionAtMost_not_IsOdd h h_prec_F₁ hodd
  have h_F₁_pos : 0 < numDigits F₁.p F₁.exp ((y : Dyadic) : ℝ) := by
    have h_chain : (0 : ℤ) < ((numDigits F₁.p F₁.exp ((y : Dyadic) : ℝ)).toNat : ℤ) :=
      lt_of_lt_of_le h_F₂_pos h_ge_int
    by_contra hneg
    push Not at hneg
    rw [Int.toNat_of_nonpos hneg] at h_chain
    exact absurd h_chain (by decide)
  have h_F₁_toNat : ((numDigits F₁.p F₁.exp ((y : Dyadic) : ℝ)).toNat : ℤ) =
      numDigits F₁.p F₁.exp ((y : Dyadic) : ℝ) :=
    Int.toNat_of_nonneg (le_of_lt h_F₁_pos)
  have h_ge : numDigits F₁.p F₁.exp ((y : Dyadic) : ℝ) ≥
      numDigits F₂.p F₂.exp ((y : Dyadic) : ℝ) := by
    rw [← h_F₁_toNat]; exact h_ge_int
  refine le_antisymm ?_ h_ge
  -- ≤ direction: by contradiction, construct y'' ∈ F₁ \ F₂.
  by_contra h_lt
  push Not at h_lt
  -- h_lt : numDigits F₂ y < numDigits F₁ y
  obtain ⟨c, e, ⟨hy_eq, hc_low, hc_high⟩, hp_check⟩ := hodd
  have hF₂_ne_1 : F₂.p ≠ 1 := by
    intro h; rw [h] at hp_F₂; exact absurd hp_F₂ (by decide)
  rw [if_neg hF₂_ne_1] at hp_check
  have hc_odd : Odd c := hp_check
  set p₂ : ℕ := (numDigits F₂.p F₂.exp ((y : Dyadic) : ℝ)).toNat with hp₂_def
  have hp₂_eq : (p₂ : ℤ) = numDigits F₂.p F₂.exp ((y : Dyadic) : ℝ) :=
    Int.toNat_of_nonneg (le_of_lt h_F₂_pos)
  have hp₂_pos : 1 ≤ p₂ := by
    have : (0 : ℤ) < numDigits F₂.p F₂.exp ((y : Dyadic) : ℝ) := h_F₂_pos
    rw [← hp₂_eq] at this; exact_mod_cast this
  have hc_ne : c ≠ 0 := by
    intro h; rw [h, abs_zero] at hc_low
    have : (1 : ℤ) ≤ (2 : ℤ) ^ (p₂ - 1) := one_le_pow₀ (by norm_num)
    linarith
  -- Define y'' = Dyadic.ofIntZpow c'' (e - 1) where c'' = 2c - sign(c).
  set c'' : ℤ := 2 * c - (if 0 < c then 1 else -1) with hc''_def
  have hc''_odd : Odd c'' := by
    rcases lt_or_gt_of_ne hc_ne with h | h
    · simp only [hc''_def, if_neg (not_lt.mpr h.le)]
      exact ⟨c, by ring⟩
    · simp only [hc''_def, if_pos h]
      exact ⟨c - 1, by ring⟩
  have hc''_abs : |c''| = 2 * |c| - 1 := by
    rcases lt_or_gt_of_ne hc_ne with h | h
    · simp only [hc''_def, if_neg (not_lt.mpr h.le)]
      have hc_neg : c < 0 := h
      have h1 : 2 * c + 1 < 0 := by linarith
      rw [show (2 * c - -1 : ℤ) = 2 * c + 1 from by ring,
          abs_of_neg h1, abs_of_neg hc_neg]
      linarith
    · simp only [hc''_def, if_pos h]
      have hc_pos : c > 0 := h
      have h1 : 2 * c - 1 > 0 := by linarith
      rw [abs_of_pos h1, abs_of_pos hc_pos]
  have hc''_low : (2 : ℤ) ^ p₂ - 1 ≤ |c''| := by
    rw [hc''_abs, Int.two_pow_succ_pred hp₂_pos]
    linarith
  have hc''_high : |c''| < (2 : ℤ) ^ (p₂ + 1) := by
    rw [hc''_abs, Int.two_pow_succ_pred (by omega : 1 ≤ p₂ + 1)]
    have : (p₂ + 1 - 1 : ℕ) = p₂ := by omega
    rw [this]
    linarith
  set y'' : Dyadic := Dyadic.ofIntZpow c'' (e - 1) with hy''_def
  have hy''_real : (y'' : ℝ) = (c'' : ℝ) * (2 : ℝ) ^ (e - 1) := rfl
  have h2real_pos : (0 : ℝ) < 2 := by norm_num
  have h2real_ne : (2 : ℝ) ≠ 0 := by norm_num
  have habs_y_eq : |((y : Dyadic) : ℝ)| = (|c| : ℝ) * (2 : ℝ) ^ e := by
    rw [hy_eq, abs_mul_two_zpow]
  have habs_y''_eq : |((y'' : Dyadic) : ℝ)| = (|c''| : ℝ) * (2 : ℝ) ^ (e - 1) := by
    rw [hy''_real, abs_mul_two_zpow]
  have habs_y''_lt_y : |((y'' : Dyadic) : ℝ)| < |((y : Dyadic) : ℝ)| := by
    rw [habs_y_eq, habs_y''_eq]
    have h2e_pos : (0 : ℝ) < (2 : ℝ) ^ (e - 1) := zpow_pos h2real_pos _
    have habs_split : (2 : ℝ) ^ e = 2 * (2 : ℝ) ^ (e - 1) := by
      conv_lhs => rw [show e = (e - 1) + 1 from by ring]
      rw [zpow_add₀ h2real_ne, zpow_one]; ring
    rw [habs_split]
    have h_cabs_pos : (0 : ℝ) < (|c| : ℝ) := by exact_mod_cast (abs_pos.mpr hc_ne)
    have : (|c''| : ℝ) = 2 * (|c| : ℝ) - 1 := by
      have := hc''_abs
      have : (|c''| : ℤ) = 2 * |c| - 1 := this
      exact_mod_cast this
    rw [this]
    have h_cabs_ge : (1 : ℝ) ≤ (|c| : ℝ) := by
      have : (1 : ℤ) ≤ |c| := by
        rcases lt_or_gt_of_ne hc_ne with h | h
        · exact Int.one_le_abs (Int.ne_of_lt h)
        · exact Int.one_le_abs (Int.ne_of_gt h)
      exact_mod_cast this
    nlinarith [h2e_pos]
  have hy_ne_zero : ((y : Dyadic) : ℝ) ≠ 0 := by
    intro h
    rw [h, abs_zero] at habs_y_eq
    have hp : (0 : ℝ) < (|c| : ℝ) := by exact_mod_cast (abs_pos.mpr hc_ne)
    have h2 : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos h2real_pos _
    have h_prod : (|c| : ℝ) * (2 : ℝ) ^ e = 0 := habs_y_eq.symm
    have hp_ne : (|c| : ℝ) ≠ 0 := ne_of_gt hp
    have h2_ne : (2 : ℝ) ^ e ≠ 0 := ne_of_gt h2
    exact hp_ne ((mul_eq_zero.mp h_prod).resolve_right h2_ne)
  have habs_y_pos : 0 < |((y : Dyadic) : ℝ)| := abs_pos.mpr hy_ne_zero
  have hlog2_nat : (1 : ℕ) < 2 := by norm_num
  have h_cast_pow : ∀ k : ℕ, ((2 : ℤ) ^ k : ℝ) = (2 : ℝ) ^ (k : ℤ) := by
    intro k
    rw [zpow_natCast]
    push_cast; rfl
  have h_log_y_lo : (2 : ℝ) ^ ((p₂ - 1 : ℤ) + e) ≤ |((y : Dyadic) : ℝ)| := by
    rw [habs_y_eq, zpow_add₀ h2real_ne]
    apply mul_le_mul_of_nonneg_right _ (le_of_lt (zpow_pos h2real_pos _))
    have h_cast_low : ((2 : ℤ) ^ (p₂ - 1) : ℝ) ≤ (|c| : ℝ) := by
      exact_mod_cast hc_low
    have h_cast_low_zp : (2 : ℝ) ^ ((p₂ - 1 : ℕ) : ℤ) = ((2 : ℤ) ^ (p₂ - 1) : ℝ) :=
      (h_cast_pow (p₂ - 1)).symm
    have h_eq : (p₂ - 1 : ℤ) = ((p₂ - 1 : ℕ) : ℤ) := by omega
    rw [h_eq, h_cast_low_zp]
    exact h_cast_low
  have h_log_y_hi : |((y : Dyadic) : ℝ)| < (2 : ℝ) ^ ((p₂ : ℤ) + e) := by
    rw [habs_y_eq, zpow_add₀ h2real_ne]
    apply mul_lt_mul_of_pos_right _ (zpow_pos h2real_pos _)
    have h_cast_high : (|c| : ℝ) < ((2 : ℤ) ^ p₂ : ℝ) := by
      exact_mod_cast hc_high
    have h_cast_zp : (2 : ℝ) ^ ((p₂ : ℕ) : ℤ) = ((2 : ℤ) ^ p₂ : ℝ) :=
      (h_cast_pow p₂).symm
    have h_eq : (p₂ : ℤ) = ((p₂ : ℕ) : ℤ) := rfl
    rw [h_eq, h_cast_zp]; exact h_cast_high
  have h_log_y_eq : Int.log 2 |((y : Dyadic) : ℝ)| = (p₂ - 1 : ℤ) + e := by
    apply le_antisymm
    · have : Int.log 2 |((y : Dyadic) : ℝ)| < (p₂ - 1 : ℤ) + e + 1 :=
        (Int.lt_zpow_iff_log_lt hlog2_nat habs_y_pos).mp
          (by rw [show (p₂ - 1 : ℤ) + e + 1 = (p₂ : ℤ) + e from by omega]
              exact h_log_y_hi)
      omega
    · exact (Int.zpow_le_iff_le_log hlog2_nat habs_y_pos).mp h_log_y_lo
  -- Step 1: Show y'' ∈ F₁.
  have hy''_F₁ : y'' ∈ F₁ := by
    refine ⟨?_, ?_, ?_⟩
    · cases hp1 : F₁.p with
      | top => trivial
      | coe n =>
        rw [Dyadic.precisionAtMost_coe]
        refine ⟨c'', e - 1, hy''_real, ?_⟩
        have h_le_n : numDigits F₁.p F₁.exp ((y : Dyadic) : ℝ) ≤ (n : ℤ) := by
          rw [hp1]
          cases hexp : F₁.exp with
          | bot =>
            rw [numDigits_coe_bot' hy_ne_zero]
          | coe e' =>
            rw [numDigits_coe_coe' hy_ne_zero]
            exact min_le_left _ _
        have hp₂_lt_n : (p₂ : ℤ) < (n : ℤ) := by
          rw [hp₂_eq]; exact lt_of_lt_of_le h_lt h_le_n
        have hp₂_lt_n_nat : p₂ + 1 ≤ n := by exact_mod_cast (by omega : (p₂ : ℤ) + 1 ≤ n)
        calc |c''|
            < (2 : ℤ) ^ (p₂ + 1) := hc''_high
          _ ≤ (2 : ℤ) ^ n :=
              pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hp₂_lt_n_nat
    · cases hexp : F₁.exp with
      | bot => trivial
      | coe e₁ =>
        rw [Dyadic.quantumAtLeast_coe]
        have h_e_gt_e₁ : e₁ < e := by
          have h_inner_gt : Int.log 2 |((y : Dyadic) : ℝ)| - e₁ + 1 > (p₂ : ℤ) := by
            have h_F₁_lt : (p₂ : ℤ) < numDigits F₁.p F₁.exp ((y : Dyadic) : ℝ) := by
              rw [hp₂_eq]; exact h_lt
            rw [hexp] at h_F₁_lt
            cases hp1 : F₁.p with
            | top =>
              rw [hp1] at h_F₁_lt
              rw [numDigits_top_coe' hy_ne_zero] at h_F₁_lt
              exact h_F₁_lt
            | coe n =>
              rw [hp1] at h_F₁_lt
              rw [numDigits_coe_coe' hy_ne_zero] at h_F₁_lt
              exact lt_of_lt_of_le h_F₁_lt (min_le_right _ _)
          rw [h_log_y_eq] at h_inner_gt
          omega
        have h_diff_nn : ((e - 1 - e₁).toNat : ℤ) = e - 1 - e₁ :=
          Int.toNat_of_nonneg (by omega)
        refine ⟨c'' * 2 ^ (e - 1 - e₁).toNat, ?_⟩
        rw [hy''_real]
        have h_pow_eq : (2 : ℝ) ^ (e - 1) =
            (2 : ℝ) ^ ((e - 1 - e₁).toNat : ℤ) * (2 : ℝ) ^ e₁ := by
          rw [← zpow_add₀ h2real_ne, h_diff_nn]
          congr 1; ring
        rw [h_pow_eq]
        rw [zpow_natCast]
        push_cast
        ring
    · have hyF₁_bnd := hyF₁.2.2
      cases hb : F₁.b with
      | top => trivial
      | coe b =>
        rw [hb] at hyF₁_bnd
        change |((y'' : Dyadic) : ℝ)| ≤ (b : ℝ)
        have hyF₁_bnd' : |((y : Dyadic) : ℝ)| ≤ (b : ℝ) := hyF₁_bnd
        linarith [habs_y''_lt_y]
  -- For p₂ ≥ 2 with c odd: |c| ≥ 2^(p₂-1) + 1.
  have hc_low_strict : p₂ ≥ 2 → (2 : ℤ) ^ (p₂ - 1) + 1 ≤ |c| := by
    intro hp₂_ge_2
    have h_even : Even ((2 : ℤ) ^ (p₂ - 1)) := by
      have hp_sub_pos : p₂ - 1 ≥ 1 := by omega
      refine ⟨(2 : ℤ) ^ (p₂ - 2), ?_⟩
      rw [show (p₂ - 1 : ℕ) = (p₂ - 2) + 1 from by omega, pow_succ]; ring
    have h_abs_odd : Odd |c| := Odd.abs_int hc_odd
    by_contra h_le
    push Not at h_le
    have h_eq : |c| = (2 : ℤ) ^ (p₂ - 1) := by linarith
    rw [h_eq] at h_abs_odd
    exact (Int.not_odd_iff_even.mpr h_even) h_abs_odd
  -- Step 2: Show y'' ∉ F₂.
  -- Helper: any integer rep (c''', e''') of y'' has e''' ≤ e - 1.
  have h_int_rep_le : ∀ (c''' : ℤ) (e''' : ℤ),
      ((y'' : Dyadic) : ℝ) = (c''' : ℝ) * (2 : ℝ) ^ e''' → e''' ≤ e - 1 := by
    intro c''' e''' h_eq
    by_contra h_gt
    push Not at h_gt
    have h_diff_pos : 0 < e''' - (e - 1) := by omega
    have h_diff_nat : ((e''' - (e - 1)).toNat : ℤ) = e''' - (e - 1) :=
      Int.toNat_of_nonneg (le_of_lt h_diff_pos)
    have h_c''_eq : (c'' : ℝ) = (c''' : ℝ) * (2 : ℝ) ^ (e''' - (e - 1)) := by
      have h2eml_pos : (0 : ℝ) < (2 : ℝ) ^ (e - 1) := zpow_pos h2real_pos _
      have hsplit : (2 : ℝ) ^ e''' =
          (2 : ℝ) ^ (e''' - (e - 1)) * (2 : ℝ) ^ (e - 1) := by
        rw [← zpow_add₀ h2real_ne]; congr 1; ring
      rw [hy''_real] at h_eq
      have key : (c'' : ℝ) * (2 : ℝ) ^ (e - 1) =
          ((c''' : ℝ) * (2 : ℝ) ^ (e''' - (e - 1))) * (2 : ℝ) ^ (e - 1) := by
        rw [h_eq, hsplit]; ring
      exact mul_right_cancel₀ (ne_of_gt h2eml_pos) key
    rw [show (2 : ℝ) ^ (e''' - (e - 1)) =
        (2 : ℝ) ^ ((e''' - (e - 1)).toNat : ℤ) from by rw [h_diff_nat],
        zpow_natCast] at h_c''_eq
    have h_c''_int : c'' = c''' * 2 ^ (e''' - (e - 1)).toNat := by
      have : ((c''' * 2 ^ (e''' - (e - 1)).toNat : ℤ) : ℝ) = (c'' : ℝ) := by
        push_cast; linarith [h_c''_eq]
      exact_mod_cast this.symm
    have h_pow_ge : 1 ≤ (e''' - (e - 1)).toNat := by
      have : ((e''' - (e - 1)).toNat : ℤ) ≥ 1 := by rw [h_diff_nat]; omega
      exact_mod_cast this
    have h_pow_split : (2 : ℤ) ^ (e''' - (e - 1)).toNat =
        2 * (2 : ℤ) ^ ((e''' - (e - 1)).toNat - 1) := Int.two_pow_succ_pred h_pow_ge
    have hc''_even : Even c'' := by
      rw [h_c''_int, h_pow_split]
      exact ⟨c''' * (2 : ℤ) ^ ((e''' - (e - 1)).toNat - 1), by ring⟩
    exact (Int.not_odd_iff_even.mpr hc''_even) hc''_odd
  -- Helper: |c'''| ≥ |c''| from any integer rep.
  have h_int_rep_abs : ∀ (c''' : ℤ) (e''' : ℤ),
      ((y'' : Dyadic) : ℝ) = (c''' : ℝ) * (2 : ℝ) ^ e''' → |c''| ≤ |c'''| := by
    intro c''' e''' h_eq
    have h_e_le := h_int_rep_le c''' e''' h_eq
    have h_diff_nn : ((e - 1 - e''').toNat : ℤ) = e - 1 - e''' :=
      Int.toNat_of_nonneg (by omega)
    have h_c'''_eq : c''' = c'' * 2 ^ (e - 1 - e''').toNat := by
      have h2_pos : (0 : ℝ) < (2 : ℝ) ^ e''' := zpow_pos h2real_pos _
      rw [hy''_real] at h_eq
      have hsplit : (2 : ℝ) ^ (e - 1) =
          (2 : ℝ) ^ (e - 1 - e''') * (2 : ℝ) ^ e''' := by
        rw [← zpow_add₀ h2real_ne]; congr 1; ring
      have key : ((c'' : ℝ) * (2 : ℝ) ^ (e - 1 - e''')) * (2 : ℝ) ^ e''' =
          (c''' : ℝ) * (2 : ℝ) ^ e''' := by
        rw [show ((c'' : ℝ) * (2 : ℝ) ^ (e - 1 - e''')) * (2 : ℝ) ^ e''' =
            (c'' : ℝ) * ((2 : ℝ) ^ (e - 1 - e''') * (2 : ℝ) ^ e''') from by ring]
        rw [← hsplit]; exact h_eq
      have h_real : (c'' : ℝ) * (2 : ℝ) ^ (e - 1 - e''') = (c''' : ℝ) :=
        mul_right_cancel₀ (ne_of_gt h2_pos) key
      rw [show (2 : ℝ) ^ (e - 1 - e''') =
          (2 : ℝ) ^ ((e - 1 - e''').toNat : ℤ) from by rw [h_diff_nn],
          zpow_natCast] at h_real
      have : ((c'' * 2 ^ (e - 1 - e''').toNat : ℤ) : ℝ) = (c''' : ℝ) := by
        push_cast; linarith [h_real]
      exact_mod_cast this.symm
    rw [h_c'''_eq, abs_mul, abs_pow]
    have h2_abs : |(2 : ℤ)| = 2 := by decide
    rw [h2_abs]
    have h_pow_pos : (1 : ℤ) ≤ 2 ^ (e - 1 - e''').toNat := one_le_pow₀ (by norm_num)
    have h_abs_nn : (0 : ℤ) ≤ |c''| := abs_nonneg _
    nlinarith
  -- Combine: y'' ∉ F₂, contradicting y'' ∈ F₁ ⊆ F₂.
  have hy''_not_F₂ : y'' ∉ F₂ := by
    intro hy''_F₂
    obtain ⟨h_pre, h_qua, _⟩ := hy''_F₂
    cases hexp2 : F₂.exp with
    | bot =>
      have h_F₂_nd := F₂.not_doubly_unbounded
      rcases h_F₂_nd with hp_top_neg | hexp_bot_neg
      · cases hp2 : F₂.p with
        | top => exact absurd hp2 hp_top_neg
        | coe n =>
          have h_numD_eq_n : (p₂ : ℤ) = (n : ℤ) := by
            rw [hp₂_eq, hp2, hexp2, numDigits_coe_bot' hy_ne_zero]
          have hp₂_eq_n : p₂ = n := by exact_mod_cast h_numD_eq_n
          have hp₂_ge_2 : p₂ ≥ 2 := by
            have : (2 : ℕ∞) ≤ ((n : ℕ) : ℕ∞) := hp2 ▸ hp_F₂
            have hn_ge_2 : 2 ≤ n := by exact_mod_cast this
            omega
          have hc''_strong : (2 : ℤ) ^ p₂ + 1 ≤ |c''| := by
            rw [hc''_abs]
            have hcs := hc_low_strict hp₂_ge_2
            have h_double : 2 * ((2 : ℤ) ^ (p₂ - 1) + 1) - 1 = (2 : ℤ) ^ p₂ + 1 := by
              rw [Int.two_pow_succ_pred hp₂_pos]; ring
            linarith
          rw [hp2, Dyadic.precisionAtMost_coe] at h_pre
          obtain ⟨c''', e''', hy''_rep, hc'''_low⟩ := h_pre
          have h_abs := h_int_rep_abs c''' e''' hy''_rep
          have : (2 : ℤ) ^ n + 1 ≤ |c'''| := by
            rw [← hp₂_eq_n]; linarith
          linarith
      · exact absurd hexp2 hexp_bot_neg
    | coe e₂ =>
      cases hp2 : F₂.p with
      | top =>
        have h_numD : numDigits F₂.p F₂.exp ((y : Dyadic) : ℝ) =
            Int.log 2 |((y : Dyadic) : ℝ)| - e₂ + 1 := by
          rw [hp2, hexp2, numDigits_top_coe' hy_ne_zero]
        rw [h_log_y_eq] at h_numD
        have h_e_eq : e = e₂ := by
          have h1 : (p₂ : ℤ) = (p₂ : ℤ) - 1 + e - e₂ + 1 := by
            rw [← h_numD]; exact hp₂_eq
          omega
        rw [hexp2, Dyadic.quantumAtLeast_coe] at h_qua
        obtain ⟨c''', hy''_rep⟩ := h_qua
        have h_e_le := h_int_rep_le c''' e₂ hy''_rep
        omega
      | coe n =>
        have h_numD : numDigits F₂.p F₂.exp ((y : Dyadic) : ℝ) =
            min ((n : ℕ) : ℤ) (Int.log 2 |((y : Dyadic) : ℝ)| - e₂ + 1) := by
          rw [hp2, hexp2, numDigits_coe_coe' hy_ne_zero]
        rw [h_log_y_eq] at h_numD
        have hp₂_le_n : (p₂ : ℤ) ≤ (n : ℤ) := by
          rw [hp₂_eq, h_numD]; exact min_le_left _ _
        rcases eq_or_lt_of_le hp₂_le_n with hp₂_eq_n | hp₂_lt_n
        · have hn_eq_p₂ : n = p₂ := by exact_mod_cast hp₂_eq_n.symm
          have hp₂_ge_2 : p₂ ≥ 2 := by
            have : (2 : ℕ∞) ≤ ((n : ℕ) : ℕ∞) := hp2 ▸ hp_F₂
            have : 2 ≤ n := by exact_mod_cast this
            omega
          have hc''_strong : (2 : ℤ) ^ p₂ + 1 ≤ |c''| := by
            rw [hc''_abs]
            have hcs := hc_low_strict hp₂_ge_2
            have h_double : 2 * ((2 : ℤ) ^ (p₂ - 1) + 1) - 1 = (2 : ℤ) ^ p₂ + 1 := by
              rw [Int.two_pow_succ_pred hp₂_pos]; ring
            linarith
          rw [hp2, Dyadic.precisionAtMost_coe] at h_pre
          obtain ⟨c''', e''', hy''_rep, hc'''_low⟩ := h_pre
          have h_abs := h_int_rep_abs c''' e''' hy''_rep
          have h_chain : (2 : ℤ) ^ n + 1 ≤ |c'''| := by
            rw [hn_eq_p₂]; linarith
          linarith
        · have h_e_eq : e = e₂ := by
            have h1 : (p₂ : ℤ) = min ((n : ℕ) : ℤ) ((p₂ : ℤ) - 1 + e - e₂ + 1) := by
              rw [← h_numD]; exact hp₂_eq
            have h2 : (p₂ : ℤ) = (p₂ : ℤ) - 1 + e - e₂ + 1 := by
              rcases min_cases ((n : ℕ) : ℤ) ((p₂ : ℤ) - 1 + e - e₂ + 1) with
                ⟨hmin, _⟩ | ⟨hmin, _⟩
              · rw [hmin] at h1; omega
              · rw [hmin] at h1; exact h1
            omega
          rw [hexp2, Dyadic.quantumAtLeast_coe] at h_qua
          obtain ⟨c''', hy''_rep⟩ := h_qua
          have h_e_le := h_int_rep_le c''' e₂ hy''_rep
          omega
  exact hy''_not_F₂ (hsub _ hy''_F₁)

/-- Transfer `IsOdd` from `F₂` to a subformat `F₁` containing `y`, given that
the effective precisions agree. Handles both `F₁.p ≥ 2` (direct witness
transfer) and `F₁.p = 1` (the index-counting parity discriminator, which
forces `F₁.exp = F₂.exp = e_y` and reduces to `Odd 1`).

The `numDigits F₁ y = numDigits F₂ y` hypothesis is the conclusion of
`numDigits_eq_of_subset_of_isOdd`; together they form the standard
parity-transfer chain used by `rndRTO_RTO`. -/
theorem IsOdd.transfer_of_numDigits_eq {F₁ F₂ : AbstractFormat}
    (hsub : F₁ ⊆ F₂) (hp_F₂ : 2 ≤ F₂.p)
    {y : Dyadic} (hyF₁ : y ∈ F₁) (h_iod_F₂ : IsOdd F₂ y)
    (h_eq : numDigits F₁.p F₁.exp ((y : Dyadic) : ℝ)
            = numDigits F₂.p F₂.exp ((y : Dyadic) : ℝ)) :
    IsOdd F₁ y := by
  have h_iod_F₂' : IsOdd F₂ y := h_iod_F₂
  obtain ⟨c, e, h_rep_F₂, h_par_F₂⟩ := h_iod_F₂
  have hF₂_ne_1 : F₂.p ≠ 1 := by
    intro h; rw [h] at hp_F₂; exact absurd hp_F₂ (by decide)
  rw [if_neg hF₂_ne_1] at h_par_F₂
  have h_par_c : Odd c := h_par_F₂
  refine ⟨c, e, ?_, ?_⟩
  · rw [h_eq]; exact h_rep_F₂
  · by_cases hF₁_p_1 : F₁.p = 1
    · rw [if_pos hF₁_p_1]
      have hF₁_exp_ne : F₁.exp ≠ ⊥ := F₁.exp_finite_of_p_one hF₁_p_1
      set e₁ : ℤ := F₁.exp.unbot hF₁_exp_ne with he₁_def
      have hF₁_exp_eq : F₁.exp = (e₁ : WithBot ℤ) :=
        (WithBot.coe_unbot F₁.exp hF₁_exp_ne).symm
      have h_unbot : WithBot.unbotD 0 F₁.exp = e₁ := by
        rw [hF₁_exp_eq]; rfl
      rw [h_unbot]
      have h_F₂_pos_y : 0 < numDigits F₂.p F₂.exp ((y : Dyadic) : ℝ) :=
        h_iod_F₂'.numDigits_pos
      have h_numD_F₁_le_1 : numDigits F₁.p F₁.exp ((y : Dyadic) : ℝ) ≤ 1 :=
        numDigits_le_one_of_p_one hF₁_p_1 _ _
      have h_p₂_eq_1 : numDigits F₂.p F₂.exp ((y : Dyadic) : ℝ) = 1 := by
        rw [h_eq] at h_numD_F₁_le_1; omega
      have h_p₂_toNat_eq_1 :
          (numDigits F₂.p F₂.exp ((y : Dyadic) : ℝ)).toNat = 1 := by
        rw [h_p₂_eq_1]; rfl
      obtain ⟨h_y_eq, hc_low_y, hc_high_y⟩ := h_rep_F₂
      rw [h_p₂_toNat_eq_1] at hc_low_y hc_high_y
      have hc_abs_eq : |c| = 1 := by
        have h1 : (1 : ℤ) ≤ |c| := by simpa using hc_low_y
        have h2 : |c| < (2 : ℤ) := by simpa using hc_high_y
        omega
      have hy_ne_zero_d : y ≠ 0 := h_iod_F₂'.ne_zero
      have hy_ne_zero : ((y : Dyadic) : ℝ) ≠ 0 := by
        intro h; exact hy_ne_zero_d (Subtype.ext (by rw [h]; rfl))
      have h2real_pos : (0 : ℝ) < 2 := by norm_num
      have h2real_ne : (2 : ℝ) ≠ 0 := by norm_num
      have habs_y_eq : |((y : Dyadic) : ℝ)| = (2 : ℝ) ^ e := by
        rw [h_y_eq, abs_mul_two_zpow]
        have hc_real : (|c| : ℝ) = 1 := by exact_mod_cast hc_abs_eq
        rw [hc_real]; ring
      have h_log_y_eq : Int.log 2 |((y : Dyadic) : ℝ)| = e := by
        rw [habs_y_eq]
        exact Int.log_zpow (by norm_num : 1 < 2) e
      have hyF₁_q : Dyadic.quantumAtLeast F₁.exp y := hyF₁.2.1
      rw [hF₁_exp_eq, Dyadic.quantumAtLeast_coe] at hyF₁_q
      obtain ⟨c'_q, hc'_q_eq⟩ := hyF₁_q
      have h_e_ge_e₁ : e₁ ≤ e := by
        by_contra h_gt
        push Not at h_gt
        have h_diff : 0 < e₁ - e := by omega
        have h_diff_nat : ((e₁ - e).toNat : ℤ) = e₁ - e :=
          Int.toNat_of_nonneg (le_of_lt h_diff)
        have h_real : (c : ℝ) = (c'_q : ℝ) * (2 : ℝ) ^ (e₁ - e) := by
          have h2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos h2real_pos _
          have h_split : (2 : ℝ) ^ e₁ = (2 : ℝ) ^ (e₁ - e) * (2 : ℝ) ^ e := by
            rw [← zpow_add₀ h2real_ne]; congr 1; ring
          have key : (c : ℝ) * (2 : ℝ) ^ e =
              ((c'_q : ℝ) * (2 : ℝ) ^ (e₁ - e)) * (2 : ℝ) ^ e := by
            rw [show ((c'_q : ℝ) * (2 : ℝ) ^ (e₁ - e)) * (2 : ℝ) ^ e =
                (c'_q : ℝ) * ((2 : ℝ) ^ (e₁ - e) * (2 : ℝ) ^ e) from by ring]
            rw [← h_split, ← hc'_q_eq, h_y_eq]
          exact mul_right_cancel₀ (ne_of_gt h2e_pos) key
        rw [show (2 : ℝ) ^ (e₁ - e) = (2 : ℝ) ^ ((e₁ - e).toNat : ℤ) from by
            rw [h_diff_nat], zpow_natCast] at h_real
        have h_int_eq : c = c'_q * 2 ^ (e₁ - e).toNat := by
          have : ((c'_q * 2 ^ (e₁ - e).toNat : ℤ) : ℝ) = (c : ℝ) := by
            push_cast; linarith
          exact_mod_cast this.symm
        have h_k_ge_1 : 1 ≤ (e₁ - e).toNat := by
          have : ((e₁ - e).toNat : ℤ) ≥ 1 := by rw [h_diff_nat]; omega
          exact_mod_cast this
        have h_pow_ge_2 : (2 : ℤ) ≤ 2 ^ (e₁ - e).toNat := by
          have : (2 : ℤ) ^ 1 ≤ 2 ^ (e₁ - e).toNat :=
            pow_le_pow_right₀ (by norm_num) h_k_ge_1
          simpa using this
        have h_factor : (1 : ℤ) = |c'_q| * 2 ^ (e₁ - e).toNat := by
          have : |c| = |c'_q * 2 ^ (e₁ - e).toNat| := by rw [h_int_eq]
          rw [hc_abs_eq, abs_mul, abs_pow] at this
          have h2_abs : |(2 : ℤ)| = 2 := by decide
          rw [h2_abs] at this
          exact this
        have h_abs_pos : (1 : ℤ) ≤ |c'_q| := by
          rcases eq_or_ne c'_q 0 with hc'0 | hc'_ne
          · rw [hc'0] at h_factor; simp at h_factor
          · exact Int.one_le_abs hc'_ne
        nlinarith
      have h_e_eq_F₂_exp_or_p_eq_1 :
          (∃ e₂ : ℤ, F₂.exp = (e₂ : WithBot ℤ) ∧ e = e₂) := by
        cases hF₂_exp_cases : F₂.exp with
        | bot =>
          exfalso
          cases hF₂_p_cases : F₂.p with
          | top =>
            have := F₂.not_doubly_unbounded
            rcases this with h1 | h1
            · exact h1 hF₂_p_cases
            · exact h1 hF₂_exp_cases
          | coe n =>
            have h_n : numDigits F₂.p F₂.exp ((y : Dyadic) : ℝ) = (n : ℤ) := by
              rw [hF₂_p_cases, hF₂_exp_cases, numDigits_coe_bot' hy_ne_zero]
            rw [h_n] at h_p₂_eq_1
            have hn_eq_1 : n = 1 := by exact_mod_cast h_p₂_eq_1
            have hF₂_p_eq_1 : F₂.p = (1 : ℕ∞) := by
              rw [hF₂_p_cases]; exact_mod_cast hn_eq_1
            rw [hF₂_p_eq_1] at hp_F₂
            exact absurd hp_F₂ (by decide)
        | coe e₂ =>
          refine ⟨e₂, rfl, ?_⟩
          cases hF₂_p_cases : F₂.p with
          | top =>
            have h_n : numDigits F₂.p F₂.exp ((y : Dyadic) : ℝ) =
                Int.log 2 |((y : Dyadic) : ℝ)| - e₂ + 1 := by
              rw [hF₂_p_cases, hF₂_exp_cases, numDigits_top_coe' hy_ne_zero]
            rw [h_n, h_log_y_eq] at h_p₂_eq_1
            omega
          | coe n =>
            have h_n : numDigits F₂.p F₂.exp ((y : Dyadic) : ℝ) =
                min ((n : ℕ) : ℤ) (Int.log 2 |((y : Dyadic) : ℝ)| - e₂ + 1) := by
              rw [hF₂_p_cases, hF₂_exp_cases, numDigits_coe_coe' hy_ne_zero]
            rw [h_n, h_log_y_eq] at h_p₂_eq_1
            have hn_ge_2 : (2 : ℤ) ≤ (n : ℤ) := by
              have : (2 : ℕ∞) ≤ ((n : ℕ) : ℕ∞) := hF₂_p_cases ▸ hp_F₂
              exact_mod_cast this
            rcases min_cases ((n : ℕ) : ℤ) (e - e₂ + 1) with ⟨h1, _⟩ | ⟨h1, _⟩
            · rw [h1] at h_p₂_eq_1; omega
            · rw [h1] at h_p₂_eq_1; omega
      obtain ⟨e₂, hF₂_exp_eq, h_e_eq⟩ := h_e_eq_F₂_exp_or_p_eq_1
      have h_2e1_in_F₁ : (Dyadic.ofIntZpow 1 e₁) ∈ F₁ := by
        refine ⟨?_, ?_, ?_⟩
        · rw [hF₁_p_1]
          change Dyadic.precisionAtMost ((1 : ℕ) : ℕ∞) (Dyadic.ofIntZpow 1 e₁)
          rw [Dyadic.precisionAtMost_coe]
          refine ⟨1, e₁, ?_, ?_⟩
          · rw [Dyadic.coe_ofIntZpow]
          · decide
        · rw [hF₁_exp_eq, Dyadic.quantumAtLeast_coe]
          refine ⟨1, ?_⟩
          rw [Dyadic.coe_ofIntZpow]
        · have hyF₁_b := hyF₁.2.2
          cases hb : F₁.b with
          | top => trivial
          | coe b =>
            rw [hb] at hyF₁_b
            change |((Dyadic.ofIntZpow 1 e₁ : Dyadic) : ℝ)| ≤ (b : ℝ)
            rw [Dyadic.coe_ofIntZpow]
            have h2e₁_pos : (0 : ℝ) < (2 : ℝ) ^ e₁ := zpow_pos h2real_pos _
            have h_eq_pow : ((1 : ℤ) : ℝ) * (2 : ℝ) ^ e₁ = (2 : ℝ) ^ e₁ := by
              push_cast; ring
            rw [h_eq_pow, abs_of_pos h2e₁_pos]
            have h2e_le : (2 : ℝ) ^ e₁ ≤ (2 : ℝ) ^ e :=
              zpow_le_zpow_right₀ (by norm_num) h_e_ge_e₁
            have habs_y_le : |((y : Dyadic) : ℝ)| ≤ (b : ℝ) := hyF₁_b
            rw [habs_y_eq] at habs_y_le
            linarith
      have h_2e1_in_F₂ : (Dyadic.ofIntZpow 1 e₁) ∈ F₂ := hsub _ h_2e1_in_F₁
      have hF₂_exp_le_e₁ : e₂ ≤ e₁ := by
        obtain ⟨_, hq, _⟩ := h_2e1_in_F₂
        rw [hF₂_exp_eq, Dyadic.quantumAtLeast_coe] at hq
        obtain ⟨c''', hc'''_eq⟩ := hq
        by_contra h_gt
        push Not at h_gt
        have h_gt' : 0 < e₂ - e₁ := by omega
        have h_diff_nat : ((e₂ - e₁).toNat : ℤ) = e₂ - e₁ :=
          Int.toNat_of_nonneg (le_of_lt h_gt')
        have h_real : (1 : ℝ) = (c''' : ℝ) * (2 : ℝ) ^ (e₂ - e₁) := by
          rw [Dyadic.coe_ofIntZpow] at hc'''_eq
          have h_one : ((1 : ℤ) : ℝ) * (2 : ℝ) ^ e₁ =
              (c''' : ℝ) * (2 : ℝ) ^ e₂ := hc'''_eq
          have h2e₁_pos : (0 : ℝ) < (2 : ℝ) ^ e₁ := zpow_pos h2real_pos _
          have h_split : (2 : ℝ) ^ e₂ = (2 : ℝ) ^ (e₂ - e₁) * (2 : ℝ) ^ e₁ := by
            rw [← zpow_add₀ h2real_ne]; congr 1; ring
          have key : (1 : ℝ) * (2 : ℝ) ^ e₁ =
              ((c''' : ℝ) * (2 : ℝ) ^ (e₂ - e₁)) * (2 : ℝ) ^ e₁ := by
            rw [show ((1 : ℤ) : ℝ) = (1 : ℝ) from by push_cast; ring] at h_one
            rw [h_one, h_split]; ring
          exact mul_right_cancel₀ (ne_of_gt h2e₁_pos) key
        rw [show (2 : ℝ) ^ (e₂ - e₁) =
            (2 : ℝ) ^ ((e₂ - e₁).toNat : ℤ) from by rw [h_diff_nat],
            zpow_natCast] at h_real
        have h_k_pos : 1 ≤ (e₂ - e₁).toNat := by
          have : ((e₂ - e₁).toNat : ℤ) ≥ 1 := by rw [h_diff_nat]; omega
          exact_mod_cast this
        have h_int_eq : (1 : ℤ) = c''' * 2 ^ (e₂ - e₁).toNat := by
          have : ((1 : ℤ) : ℝ) = ((c''' * 2 ^ (e₂ - e₁).toNat : ℤ) : ℝ) := by
            push_cast; linarith
          exact_mod_cast this
        have h_2_dvd : (2 : ℤ) ∣ c''' * 2 ^ (e₂ - e₁).toNat := by
          rw [show (e₂ - e₁).toNat = ((e₂ - e₁).toNat - 1) + 1 from by omega,
              pow_succ]
          exact ⟨c''' * 2 ^ ((e₂ - e₁).toNat - 1), by ring⟩
        rw [← h_int_eq] at h_2_dvd
        exact absurd h_2_dvd (by decide)
      have h_e₁_eq_e : e₁ = e := by omega
      rw [show (e - e₁ + 1 : ℤ) = 1 from by omega]
      exact ⟨0, by ring⟩
    · rw [if_neg hF₁_p_1]; exact h_par_c

end AbstractFormat

end Mpfx
