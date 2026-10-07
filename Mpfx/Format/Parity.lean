import Mpfx.Format.Defs

/-!
# Parity formats

`ParityFormat` and the `IsOdd` / `IsEven` classification of its elements.
-/

namespace Mpfx

/-- A `FiniteFormat` where parity is well-defined: `p ≠ 1` whenever
`exp = ⊥`. Combined with `FiniteFormat.finite`, this is
`(p ≠ ⊤ ∧ p ≠ 1) ∨ exp ≠ ⊥`. Required for `IsOdd` / `IsEven`. -/
structure ParityFormat extends FiniteFormat where
  parity : toFormat.p ≠ 1 ∨ toFormat.exp ≠ ⊥

namespace ParityFormat

/-- Conjunction of `FiniteFormat.finite` and `ParityFormat.parity`,
recovering the original `non-degenerate` invariant. -/
theorem nondegenerate (F : ParityFormat) :
    (F.p ≠ ⊤ ∧ F.p ≠ 1) ∨ F.exp ≠ ⊥ := by
  rcases F.parity with hp1 | hexp
  · rcases F.finite with hpT | hexp
    · exact Or.inl ⟨hpT, hp1⟩
    · exact Or.inr hexp
  · exact Or.inr hexp

/-- A nonzero `y` is *odd* in `F` if its canonical `(c, e)` representation
at the format's rounding precision has odd significand `c`. When `F.p = 1`
the significand is constant (`±1`), and parity is read off the *exponent*
`e` instead. `ParityFormat`'s `parity` invariant ensures the exponent has
an anchor (either via a finite quantum, or via `p > 1` making the
significand case the relevant one). -/
def IsOdd (F : ParityFormat) (y : Dyadic) : Prop :=
  ∃ c e : ℤ,
    Dyadic.IsRepresentableAtP (F.toFiniteFormat.numDigits (y : ℝ)).toNat c e y ∧
    (if F.p = ((1 : ℕ) : Prec) then
        Odd (e - WithBot.unbotD 0 F.exp + 1)
      else
        Odd c)

/-- Even-parity dual of `IsOdd`. Convention: `0` is even in every format. -/
def IsEven (F : ParityFormat) (y : Dyadic) : Prop :=
  y = 0 ∨ ∃ c e : ℤ,
    Dyadic.IsRepresentableAtP (F.toFiniteFormat.numDigits (y : ℝ)).toNat c e y ∧
    (if F.p = ((1 : ℕ) : Prec) then
        Even (e - WithBot.unbotD 0 F.exp + 1)
      else
        Even c)

@[simp] theorem isEven_zero (F : ParityFormat) : IsEven F 0 := Or.inl rfl

/-- `IsOdd` is invariant under negation. -/
theorem IsOdd.neg {F : ParityFormat} {y : Dyadic} (h : IsOdd F y) :
    IsOdd F (-y) := by
  obtain ⟨c, e, ⟨hyeq, hlow, hhigh⟩, hp⟩ := h
  have h_nd : F.toFiniteFormat.numDigits ((-y : Dyadic) : ℝ) =
      F.toFiniteFormat.numDigits (y : ℝ) := by
    rw [Dyadic.coe_real_neg]
    exact F.toFiniteFormat.numDigits_neg (y : ℝ)
  refine ⟨-c, e, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [Subring.coe_neg, hyeq]; push_cast; ring
  · rw [h_nd]; simpa using hlow
  · rw [h_nd]; simpa using hhigh
  · by_cases hp1 : F.p = ((1 : ℕ) : Prec)
    · rw [if_pos hp1]; rw [if_pos hp1] at hp; exact hp
    · rw [if_neg hp1]; rw [if_neg hp1] at hp; exact Odd.neg hp

/-- Iff form of `IsOdd.neg`. -/
@[simp] theorem IsOdd.neg_iff {F : ParityFormat} (y : Dyadic) :
    IsOdd F (-y) ↔ IsOdd F y :=
  ⟨fun h => by simpa using h.neg, IsOdd.neg⟩

/-- `IsEven` is invariant under negation. -/
theorem IsEven.neg {F : ParityFormat} {y : Dyadic} (h : IsEven F y) :
    IsEven F (-y) := by
  rcases h with hy0 | ⟨c, e, ⟨hyeq, hlow, hhigh⟩, hp⟩
  · left; rw [hy0]; simp
  · right
    have h_nd : F.toFiniteFormat.numDigits ((-y : Dyadic) : ℝ) =
        F.toFiniteFormat.numDigits (y : ℝ) := by
      rw [Dyadic.coe_real_neg]
      exact F.toFiniteFormat.numDigits_neg (y : ℝ)
    refine ⟨-c, e, ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [Subring.coe_neg, hyeq]; push_cast; ring
    · rw [h_nd]; simpa using hlow
    · rw [h_nd]; simpa using hhigh
    · by_cases hp1 : F.p = ((1 : ℕ) : Prec)
      · rw [if_pos hp1]; rw [if_pos hp1] at hp; exact hp
      · rw [if_neg hp1]; rw [if_neg hp1] at hp; exact Even.neg hp

/-- Iff form of `IsEven.neg`. -/
@[simp] theorem IsEven.neg_iff {F : ParityFormat} (y : Dyadic) :
    IsEven F (-y) ↔ IsEven F y :=
  ⟨fun h => by simpa using h.neg, IsEven.neg⟩

/-- `IsOdd F y` implies `numDigits ≥ 1`. -/
theorem IsOdd.numDigits_pos {F : ParityFormat} {y : Dyadic} (h : IsOdd F y) :
    0 < F.toFiniteFormat.numDigits (y : ℝ) := by
  obtain ⟨c, _, ⟨_, hlow, hhigh⟩, _⟩ := h
  by_contra h_le
  push Not at h_le
  have h_toNat : (F.toFiniteFormat.numDigits ((y : Dyadic) : ℝ)).toNat = 0 :=
    Int.toNat_of_nonpos h_le
  rw [h_toNat] at hlow hhigh
  have h1 : (1 : ℤ) ≤ |c| := by simpa using hlow
  have h2 : |c| < (1 : ℤ) := by simpa using hhigh
  omega

/-- An `IsOdd` value is nonzero. -/
theorem IsOdd.ne_zero {F : ParityFormat} {y : Dyadic} (h : IsOdd F y) :
    y ≠ 0 := by
  intro hy0
  obtain ⟨c, e, ⟨hyeq, hlow, _⟩, _⟩ := h
  rw [hy0] at hyeq
  have h2e_pos : (0 : ℚ) < (2 : ℚ) ^ e := zpow_pos (by norm_num) _
  have hc_zero : (c : ℚ) = 0 := by
    push_cast at hyeq
    rcases mul_eq_zero.mp hyeq.symm with h | h
    · exact h
    · linarith
  have hc_zero_int : c = 0 := by exact_mod_cast hc_zero
  rw [hc_zero_int, abs_zero] at hlow
  have : (1 : ℤ) ≤ (2 : ℤ) ^ ((F.toFiniteFormat.numDigits ((y : Dyadic) : ℝ)).toNat - 1) :=
    one_le_pow₀ (by norm_num)
  linarith

/-- If `(c, e)` is a canonical-form representation at `F`'s `numDigits y`
precision and `F.p ≠ 1`, then `F.IsOdd y ↔ Odd c`. The forward direction
uses `IsRepresentableAtP.unique` to pin the canonical form, then reads off
the parity. -/
theorem isOdd_iff_odd_of_canonical {F : ParityFormat} {y : Dyadic}
    {c e : ℤ}
    (h_rep : Dyadic.IsRepresentableAtP (F.toFiniteFormat.numDigits (y : ℝ)).toNat
      c e y)
    (hp_ne_1 : F.p ≠ ((1 : ℕ) : Prec)) :
    F.IsOdd y ↔ Odd c := by
  constructor
  · rintro ⟨c', e', h_rep', h_odd⟩
    rw [if_neg hp_ne_1] at h_odd
    obtain ⟨h_c, _⟩ := h_rep'.unique h_rep
    rw [← h_c]; exact h_odd
  · intro h_odd
    exact ⟨c, e, h_rep, by rw [if_neg hp_ne_1]; exact h_odd⟩

/-- Dual of `isOdd_iff_odd_of_canonical` for `IsEven`. -/
theorem isEven_iff_even_of_canonical {F : ParityFormat} {y : Dyadic}
    {c e : ℤ}
    (h_rep : Dyadic.IsRepresentableAtP (F.toFiniteFormat.numDigits (y : ℝ)).toNat
      c e y)
    (hp_ne_1 : F.p ≠ ((1 : ℕ) : Prec)) :
    F.IsEven y ↔ Even c := by
  constructor
  · rintro (rfl | ⟨c', e', h_rep', h_even⟩)
    · -- y = 0: IsRepresentableAtP at any precision forces |c| ≥ 1,
      -- but y = 0 forces c = 0. Contradiction.
      obtain ⟨hyeq, h_lo, _⟩ := h_rep
      have h_2e_pos : (0 : ℚ) < (2 : ℚ) ^ e := zpow_pos (by norm_num) _
      have hc_zero : (c : ℚ) = 0 := by
        push_cast at hyeq
        rcases mul_eq_zero.mp hyeq.symm with h | h
        · exact h
        · linarith
      have hc_zero_int : c = 0 := by exact_mod_cast hc_zero
      rw [hc_zero_int]
      exact Even.zero
    · rw [if_neg hp_ne_1] at h_even
      obtain ⟨h_c, _⟩ := h_rep'.unique h_rep
      rw [← h_c]; exact h_even
  · intro h_even
    right; exact ⟨c, e, h_rep, by rw [if_neg hp_ne_1]; exact h_even⟩

/-- IsEven and IsOdd are mutually exclusive: no `y` is both. -/
theorem not_isEven_and_isOdd {F : ParityFormat} {y : Dyadic}
    (h_even : F.IsEven y) (h_odd : F.IsOdd y) : False := by
  have hy_ne : y ≠ 0 := IsOdd.ne_zero h_odd
  rcases h_even with h_y0 | ⟨c_e, e_e, h_rep_e, h_par_e⟩
  · exact hy_ne h_y0
  obtain ⟨c_o, e_o, h_rep_o, h_par_o⟩ := h_odd
  by_cases hp1 : F.p = ((1 : ℕ) : Prec)
  · rw [if_pos hp1] at h_par_e h_par_o
    obtain ⟨_, h_e_eq⟩ := h_rep_e.unique h_rep_o
    rw [← h_e_eq] at h_par_o
    exact (Int.not_odd_iff_even.mpr h_par_e) h_par_o
  · rw [if_neg hp1] at h_par_e h_par_o
    obtain ⟨h_c_eq, _⟩ := h_rep_e.unique h_rep_o
    rw [← h_c_eq] at h_par_o
    exact (Int.not_odd_iff_even.mpr h_par_e) h_par_o

/-- Parity dichotomy: for `y` with a canonical representation,
`IsEven y ↔ ¬ IsOdd y`. Combines the two characterizations through integer
parity, handling both `p = 1` (exponent parity) and `p ≠ 1` (significand
parity). -/
theorem isEven_iff_not_isOdd_of_canonical {F : ParityFormat} {y : Dyadic}
    {c e : ℤ}
    (h_rep : Dyadic.IsRepresentableAtP (F.toFiniteFormat.numDigits (y : ℝ)).toNat
      c e y) :
    F.IsEven y ↔ ¬ F.IsOdd y := by
  have hy_ne : (y : ℚ) ≠ 0 := h_rep.ne_zero
  by_cases hp1 : F.p = ((1 : ℕ) : Prec)
  · constructor
    · rintro (h_y0 | ⟨c', e', h_rep', h_par⟩) ⟨c'', e'', h_rep'', h_par_odd⟩
      · exact hy_ne (by rw [h_y0]; push_cast; rfl)
      · rw [if_pos hp1] at h_par h_par_odd
        obtain ⟨_, h_e_eq⟩ := h_rep'.unique h_rep''
        rw [← h_e_eq] at h_par_odd
        exact (Int.not_odd_iff_even.mpr h_par) h_par_odd
    · intro h_not_odd
      right
      refine ⟨c, e, h_rep, ?_⟩
      rw [if_pos hp1]
      by_contra h_not_even
      apply h_not_odd
      refine ⟨c, e, h_rep, ?_⟩
      rw [if_pos hp1]
      exact Int.not_even_iff_odd.mp h_not_even
  · rw [isEven_iff_even_of_canonical h_rep hp1]
    rw [isOdd_iff_odd_of_canonical h_rep hp1]
    constructor
    · exact Int.not_odd_iff_even.mpr
    · exact Int.not_odd_iff_even.mp

/-! ### Generic consequences of the alternating-parity iff

For any `dlo, dhi` related by the iff `IsOdd dhi ↔ ¬ IsOdd dlo`, we get
both *no-overlap* (`¬ (IsOdd dlo ∧ IsOdd dhi)`) and *alternation in IsEven*
(`¬ IsEven dlo → IsEven dhi`) without case-by-case reasoning. The
alternation requires canonical representations (or zero) on both sides
to invoke the dichotomy. -/

/-- From an alternating-parity iff, the two values can't both be `IsOdd`. -/
theorem not_both_isOdd_of_alternating_iff {F : ParityFormat} {dlo dhi : Dyadic}
    (h : F.IsOdd dhi ↔ ¬ F.IsOdd dlo) :
    ¬ (F.IsOdd dlo ∧ F.IsOdd dhi) := fun ⟨h1, h2⟩ => h.mp h2 h1

/-- From an alternating-parity iff plus canonical representations (or
zero) on both sides, `IsEven` alternates as well: `¬ IsEven dlo → IsEven dhi`. -/
theorem alternating_isEven_of_alternating_iff
    {F : ParityFormat} {dlo dhi : Dyadic} {c_lo e_lo c_hi e_hi : ℤ}
    (h_iff : F.IsOdd dhi ↔ ¬ F.IsOdd dlo)
    (h_rep_lo_or_zero : dlo = 0 ∨ Dyadic.IsRepresentableAtP
      (F.toFiniteFormat.numDigits (dlo : ℝ)).toNat c_lo e_lo dlo)
    (h_rep_hi_or_zero : dhi = 0 ∨ Dyadic.IsRepresentableAtP
      (F.toFiniteFormat.numDigits (dhi : ℝ)).toNat c_hi e_hi dhi) :
    ¬ F.IsEven dlo → F.IsEven dhi := by
  intro h_not_even
  rcases h_rep_hi_or_zero with hhi_z | h_rep_hi
  · rw [hhi_z]; exact isEven_zero F
  rcases h_rep_lo_or_zero with hlo_z | h_rep_lo
  · exfalso; apply h_not_even
    rw [hlo_z]; exact isEven_zero F
  have h_odd_lo : F.IsOdd dlo := by
    by_contra h_not_odd
    apply h_not_even
    rw [isEven_iff_not_isOdd_of_canonical h_rep_lo]
    exact h_not_odd
  have h_not_odd_hi : ¬ F.IsOdd dhi := fun h_odd_hi => h_iff.mp h_odd_hi h_odd_lo
  rw [isEven_iff_not_isOdd_of_canonical h_rep_hi]
  exact h_not_odd_hi

/-- `Int.log 2 |k · 2^e'| = Int.log 2 |k| + e'` for nonzero integer `k`. The
"log distributes through multiplication by powers of 2" identity. -/
theorem log_abs_mul_zpow {k : ℤ} (hk_ne : k ≠ 0) (e' : ℤ) :
    Int.log 2 |(k : ℝ) * (2 : ℝ) ^ e'| = Int.log 2 (|k| : ℝ) + e' := by
  have h_2_ne : (2 : ℝ) ≠ 0 := by norm_num
  have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e' := zpow_pos (by norm_num) _
  have h_abs_k_pos : (0 : ℝ) < (|k| : ℝ) := by
    have h1 : (1 : ℤ) ≤ |k| := Int.one_le_abs hk_ne
    have h2 : (1 : ℝ) ≤ (|k| : ℝ) := by exact_mod_cast h1
    linarith
  have h_abs_y : |(k : ℝ) * (2 : ℝ) ^ e'| = (|k| : ℝ) * (2 : ℝ) ^ e' := by
    rw [abs_mul, abs_of_pos h_2e_pos]
  rw [h_abs_y]
  have h_y_pos : (0 : ℝ) < (|k| : ℝ) * (2 : ℝ) ^ e' := mul_pos h_abs_k_pos h_2e_pos
  have h_lb_k : (2 : ℝ) ^ (Int.log 2 (|k| : ℝ)) ≤ (|k| : ℝ) :=
    Int.zpow_log_le_self (by norm_num : (1 : ℕ) < 2) h_abs_k_pos
  have h_ub_k : (|k| : ℝ) < (2 : ℝ) ^ (Int.log 2 (|k| : ℝ) + 1) :=
    Int.lt_zpow_succ_log_self (by norm_num : (1 : ℕ) < 2) _
  have h_lb : (2 : ℝ) ^ (Int.log 2 (|k| : ℝ) + e') ≤ (|k| : ℝ) * (2 : ℝ) ^ e' := by
    rw [zpow_add₀ h_2_ne]
    exact mul_le_mul_of_nonneg_right h_lb_k h_2e_pos.le
  have h_ub : (|k| : ℝ) * (2 : ℝ) ^ e' < (2 : ℝ) ^ (Int.log 2 (|k| : ℝ) + e' + 1) := by
    rw [show Int.log 2 (|k| : ℝ) + e' + 1 = (Int.log 2 (|k| : ℝ) + 1) + e' by ring,
        zpow_add₀ h_2_ne]
    exact mul_lt_mul_of_pos_right h_ub_k h_2e_pos
  have h_le : Int.log 2 (|k| : ℝ) + e' ≤ Int.log 2 ((|k| : ℝ) * (2 : ℝ) ^ e') :=
    (Int.zpow_le_iff_le_log (by norm_num : (1 : ℕ) < 2) h_y_pos).mp h_lb
  have h_lt : Int.log 2 ((|k| : ℝ) * (2 : ℝ) ^ e') < Int.log 2 (|k| : ℝ) + e' + 1 :=
    (Int.lt_zpow_iff_log_lt (by norm_num : (1 : ℕ) < 2) h_y_pos).mp h_ub
  omega

/-! ### Per-case canonical-rep helpers

For each format regime (floating, mixed-normal, mixed-subnormal, mixed-`p=1`,
fixed-point), construct the `IsRepresentableAtP` witness at `numDigits`
precision. These are the only place the case-specific `numDigits`
computation happens; characterization lemmas below are thin wrappers over
`isOdd_iff_odd_of_canonical` / `isEven_iff_even_of_canonical`. -/

/-- Canonical h_rep construction for floating-point: when `|k| ∈ [2^(p-1), 2^p)`,
the (k, e) pair is the canonical representation of `ofIntZpow k e` at
`numDigits`-precision. -/
private theorem canonical_rep_floating {F : ParityFormat}
    {p : ℕ} (hp_eq : F.p = (p : Prec))
    (hexp_bot : F.exp = ⊥) {k e : ℤ}
    (hk_lo : (2 : ℤ) ^ (p - 1) ≤ |k|)
    (hk_hi : |k| < (2 : ℤ) ^ p) :
    Dyadic.IsRepresentableAtP
      (F.toFiniteFormat.numDigits ((Dyadic.ofIntZpow k e : Dyadic) : ℝ)).toNat
      k e (Dyadic.ofIntZpow k e) := by
  set y : Dyadic := Dyadic.ofIntZpow k e
  have h_y_real : (y : ℝ) = (k : ℝ) * (2 : ℝ) ^ e := Dyadic.coe_ofIntZpow k e
  have h_y_rat : (y : ℚ) = (k : ℚ) * (2 : ℚ) ^ e := Dyadic.coe_rat_ofIntZpow k e
  have hk_ne : k ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hk_lo
    have hpos : (1 : ℤ) ≤ (2 : ℤ) ^ (p - 1) := one_le_pow₀ (by norm_num)
    linarith
  have h_y_ne : (y : ℝ) ≠ 0 := Dyadic.coe_ofIntZpow_ne_zero hk_ne e
  have h_nd_toNat : (F.toFiniteFormat.numDigits (y : ℝ)).toNat = p := by
    rw [F.toFiniteFormat.numDigits_coe_bot h_y_ne hp_eq hexp_bot]; simp
  rw [h_nd_toNat]
  exact Dyadic.isRepresentableAtP_of_bounds h_y_rat hk_lo hk_hi

/-- Canonical h_rep construction for mixed-normal (`p ≠ 1`): when
`|k| ∈ [2^(p-1), 2^p)`, the (k, e_c) pair is canonical at `numDigits` bits. -/
private theorem canonical_rep_mixed_normal_pne1 {F : ParityFormat}
    {p : ℕ} (hp_eq : F.p = (p : Prec))
    {e' : ℤ} (hexp : F.exp = (e' : QExp))
    {y : Dyadic} (hy_ne : (y : ℝ) ≠ 0)
    (h_log_y_ge : (p : ℤ) ≤ Int.log 2 |(y : ℝ)| - e' + 1)
    {k e_c : ℤ} (h_y_eq : (y : ℝ) = (k : ℝ) * (2 : ℝ) ^ e_c)
    (hk_lo : (2 : ℤ) ^ (p - 1) ≤ |k|)
    (hk_hi : |k| < (2 : ℤ) ^ p) :
    Dyadic.IsRepresentableAtP
      (F.toFiniteFormat.numDigits (y : ℝ)).toNat k e_c y := by
  have h_nd_eq : F.toFiniteFormat.numDigits (y : ℝ) = (p : ℤ) := by
    rw [F.toFiniteFormat.numDigits_coe_coe hy_ne hp_eq hexp]
    exact min_eq_left h_log_y_ge
  have h_nd_toNat : (F.toFiniteFormat.numDigits (y : ℝ)).toNat = p := by
    rw [h_nd_eq]; simp
  rw [h_nd_toNat]
  have h_y_rat : (y : ℚ) = (k : ℚ) * (2 : ℚ) ^ e_c := by
    apply (Rat.cast_injective (α := ℝ))
    rw [← Dyadic.coe_real_eq_ratCast, h_y_eq]; push_cast; ring
  exact ⟨h_y_rat, hk_lo, hk_hi⟩

/-- Canonical h_rep construction for mixed-subnormal (`p ≠ 1`): when
`log|k| + 1 ≤ p`, the (k, e') pair is canonical at `numDigits` bits. -/
private theorem canonical_rep_mixed_subnormal_pne1 {F : ParityFormat}
    {p : ℕ} (hp_eq : F.p = (p : Prec))
    {e' : ℤ} (hexp : F.exp = (e' : QExp))
    {k : ℤ} (hk_ne : k ≠ 0)
    (h_log_k_lt_p : Int.log 2 (|k| : ℝ) + 1 ≤ (p : ℤ)) :
    Dyadic.IsRepresentableAtP
      (F.toFiniteFormat.numDigits ((Dyadic.ofIntZpow k e' : Dyadic) : ℝ)).toNat
      k e' (Dyadic.ofIntZpow k e') := by
  set y : Dyadic := Dyadic.ofIntZpow k e'
  have h_y_real : (y : ℝ) = (k : ℝ) * (2 : ℝ) ^ e' := Dyadic.coe_ofIntZpow k e'
  have h_y_rat : (y : ℚ) = (k : ℚ) * (2 : ℚ) ^ e' := Dyadic.coe_rat_ofIntZpow k e'
  have h_y_ne : (y : ℝ) ≠ 0 := Dyadic.coe_ofIntZpow_ne_zero hk_ne e'
  have h_log_k_nn : 0 ≤ Int.log 2 (|k| : ℝ) := by
    have h_one_le : (1 : ℝ) ≤ (|k| : ℝ) := by
      have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk_ne
      exact_mod_cast this
    rw [show (0 : ℤ) = Int.log 2 (1 : ℝ) by simp [Int.log_one_right]]
    exact Int.log_mono_right (by linarith) h_one_le
  have h_log_eq : Int.log 2 |(y : ℝ)| = Int.log 2 (|k| : ℝ) + e' := by
    rw [h_y_real]; exact log_abs_mul_zpow hk_ne e'
  have h_nd_eq : F.toFiniteFormat.numDigits (y : ℝ) = Int.log 2 (|k| : ℝ) + 1 := by
    rw [F.toFiniteFormat.numDigits_coe_coe h_y_ne hp_eq hexp]
    have h_log_y_eq : Int.log 2 |(y : ℝ)| - e' + 1 = Int.log 2 (|k| : ℝ) + 1 := by
      linarith [h_log_eq]
    rw [h_log_y_eq]
    exact min_eq_right h_log_k_lt_p
  have h_nd_toNat : (F.toFiniteFormat.numDigits (y : ℝ)).toNat =
      (Int.log 2 (|k| : ℝ)).toNat + 1 := by
    rw [h_nd_eq]
    have h1 : ((Int.log 2 (|k| : ℝ)).toNat : ℤ) = Int.log 2 (|k| : ℝ) :=
      Int.toNat_of_nonneg h_log_k_nn
    omega
  rw [h_nd_toNat]
  exact Dyadic.isRepresentableAtP_of_log hk_ne h_y_rat

/-- Canonical h_rep construction for the mixed `p = 1` case: when `|k| = 1`
and `e_c ≥ e'`, the (k, e_c) pair is canonical at `numDigits = 1` bit. -/
private theorem canonical_rep_mixed_p1 {F : ParityFormat}
    (hp_eq : F.p = ((1 : ℕ) : Prec))
    {e' : ℤ} (hexp : F.exp = (e' : QExp))
    {k e_c : ℤ} (hk_eq : |k| = 1) (h_ec_ge : e' ≤ e_c) :
    Dyadic.IsRepresentableAtP
      (F.toFiniteFormat.numDigits ((Dyadic.ofIntZpow k e_c : Dyadic) : ℝ)).toNat
      k e_c (Dyadic.ofIntZpow k e_c) := by
  set y : Dyadic := Dyadic.ofIntZpow k e_c
  have hk_ne : k ≠ 0 := by
    intro h0; rw [h0] at hk_eq; simp at hk_eq
  have h_y_real : (y : ℝ) = (k : ℝ) * (2 : ℝ) ^ e_c := Dyadic.coe_ofIntZpow k e_c
  have h_y_rat : (y : ℚ) = (k : ℚ) * (2 : ℚ) ^ e_c := Dyadic.coe_rat_ofIntZpow k e_c
  have h_y_ne : (y : ℝ) ≠ 0 := Dyadic.coe_ofIntZpow_ne_zero hk_ne e_c
  have h_log_eq : Int.log 2 |(y : ℝ)| = e_c := by
    rw [h_y_real, log_abs_mul_zpow hk_ne e_c]
    have h_abs_k_one : (|k| : ℝ) = 1 := by exact_mod_cast hk_eq
    rw [h_abs_k_one]
    simp [Int.log_one_right]
  have h_nd_eq : F.toFiniteFormat.numDigits (y : ℝ) = 1 := by
    rw [F.toFiniteFormat.numDigits_coe_coe h_y_ne hp_eq hexp]
    rw [h_log_eq]
    have h1 : (1 : ℤ) ≤ e_c - e' + 1 := by linarith
    exact min_eq_left h1
  have h_nd_toNat : (F.toFiniteFormat.numDigits (y : ℝ)).toNat = 1 := by
    rw [h_nd_eq]; rfl
  rw [h_nd_toNat]
  refine ⟨h_y_rat, ?_, ?_⟩
  · simp only [tsub_self, pow_zero]; rw [hk_eq]
  · rw [hk_eq]; norm_num

/-- Floating-point characterization (non-saturation): when `F.p = (p:ℕ)`,
`F.p ≠ 1`, `F.exp = ⊥`, and `|k| ∈ [2^(p-1), 2^p)`, then
`F.IsOdd (Dyadic.ofIntZpow k e) ↔ Odd k`. -/
theorem isOdd_iff_odd_at_canonical_floating {F : ParityFormat}
    {p : ℕ} (hp_eq : F.p = (p : Prec))
    (hp_ne_1 : F.p ≠ ((1 : ℕ) : Prec))
    (hexp_bot : F.exp = ⊥) {k e : ℤ}
    (hk_lo : (2 : ℤ) ^ (p - 1) ≤ |k|)
    (hk_hi : |k| < (2 : ℤ) ^ p) :
    F.IsOdd (Dyadic.ofIntZpow k e) ↔ Odd k :=
  isOdd_iff_odd_of_canonical (canonical_rep_floating hp_eq hexp_bot hk_lo hk_hi) hp_ne_1

/-! ### Saturation helpers

Shared infrastructure for the four `*_at_saturation_*` lemmas:
* `two_le_p_of_pne1` — derive `2 ≤ p` from `p ≠ 1`.
* `canonical_rep_at_saturation_floating` / `canonical_rep_at_saturation_mixed_normal` —
  the saturation rep `(k/2, e+1)` at `numDigits` precision.
* `not_odd_k_div_2_at_sat` — the arithmetic fact `¬ Odd (k/2)` when `|k| = 2^p`
  and `p ≥ 2`.

With these, each of the four lemmas reduces to a 3-5 line wrapper. -/

private theorem two_le_p_of_pne1 {F : ParityFormat} {p : ℕ}
    (hp_eq : F.p = (p : Prec))
    (hp_ne_1 : F.p ≠ ((1 : ℕ) : Prec)) :
    2 ≤ p := by
  by_contra h_neg
  push Not at h_neg
  have hp_one : p = 1 := by have := F.p_pos hp_eq; omega
  exact hp_ne_1 (by rw [hp_eq, hp_one])

private theorem canonical_rep_at_saturation_floating {F : ParityFormat}
    {p : ℕ} (hp_eq : F.p = (p : Prec))
    (hexp_bot : F.exp = ⊥) {k e : ℤ}
    (hk_eq : |k| = (2 : ℤ) ^ p) :
    Dyadic.IsRepresentableAtP
      (F.toFiniteFormat.numDigits ((Dyadic.ofIntZpow k e : Dyadic) : ℝ)).toNat
      (k / 2) (e + 1) (Dyadic.ofIntZpow k e) := by
  set y : Dyadic := Dyadic.ofIntZpow k e
  have h_y_real : (y : ℝ) = (k : ℝ) * (2 : ℝ) ^ e := Dyadic.coe_ofIntZpow k e
  have h_y_rat : (y : ℚ) = (k : ℚ) * (2 : ℚ) ^ e := Dyadic.coe_rat_ofIntZpow k e
  have hk_ne : k ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hk_eq
    have hpos : (1 : ℤ) ≤ (2 : ℤ) ^ p := one_le_pow₀ (by norm_num)
    linarith
  have h_y_ne : (y : ℝ) ≠ 0 := Dyadic.coe_ofIntZpow_ne_zero hk_ne e
  have h_nd_toNat : (F.toFiniteFormat.numDigits (y : ℝ)).toNat = p := by
    rw [F.toFiniteFormat.numDigits_coe_bot h_y_ne hp_eq hexp_bot]; simp
  rw [h_nd_toNat]
  exact Dyadic.isRepresentableAtP_of_saturation (F.p_pos hp_eq) h_y_rat hk_eq

private theorem canonical_rep_at_saturation_mixed_normal {F : ParityFormat}
    {p : ℕ} (hp_eq : F.p = (p : Prec))
    {e' : ℤ} (hexp : F.exp = (e' : QExp))
    {y : Dyadic} (hy_ne : (y : ℝ) ≠ 0)
    (h_log_y_ge : (p : ℤ) ≤ Int.log 2 |(y : ℝ)| - e' + 1)
    {k e_c : ℤ} (h_y_eq : (y : ℝ) = (k : ℝ) * (2 : ℝ) ^ e_c)
    (hk_eq : |k| = (2 : ℤ) ^ p) :
    Dyadic.IsRepresentableAtP
      (F.toFiniteFormat.numDigits (y : ℝ)).toNat (k / 2) (e_c + 1) y := by
  have h_nd_eq : F.toFiniteFormat.numDigits (y : ℝ) = (p : ℤ) := by
    rw [F.toFiniteFormat.numDigits_coe_coe hy_ne hp_eq hexp]
    exact min_eq_left h_log_y_ge
  have h_nd_toNat : (F.toFiniteFormat.numDigits (y : ℝ)).toNat = p := by
    rw [h_nd_eq]; simp
  rw [h_nd_toNat]
  have h_y_rat : (y : ℚ) = (k : ℚ) * (2 : ℚ) ^ e_c := by
    apply (Rat.cast_injective (α := ℝ))
    rw [← Dyadic.coe_real_eq_ratCast, h_y_eq]; push_cast; ring
  exact Dyadic.isRepresentableAtP_of_saturation (F.p_pos hp_eq) h_y_rat hk_eq

/-- When `|k| = 2^p` and `p ≥ 2`, `k/2 = ±2^(p-1)` which is divisible by 2,
hence not odd. -/
private theorem not_odd_k_div_2_at_sat {p : ℕ} (hp_ge_2 : 2 ≤ p)
    {k : ℤ} (hk_eq : |k| = (2 : ℤ) ^ p) :
    ¬ Odd (k / 2) := by
  intro h_odd
  have h_4_dvd_k : (4 : ℤ) ∣ k := by
    have h4 : (4 : ℤ) = (2 : ℤ) ^ 2 := by norm_num
    rw [h4]
    rcases (abs_eq (by positivity : (0 : ℤ) ≤ (2 : ℤ) ^ p)).mp hk_eq
      with hk | hk
    · rw [hk]; exact pow_dvd_pow 2 hp_ge_2
    · rw [hk]; exact Dvd.dvd.neg_right (pow_dvd_pow 2 hp_ge_2)
  obtain ⟨c, hc⟩ := h_4_dvd_k
  have h_k_div_2 : k / 2 = 2 * c := by
    rw [hc, show (4 : ℤ) * c = 2 * (2 * c) by ring,
        Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]
  rw [h_k_div_2] at h_odd
  obtain ⟨m, hm⟩ := h_odd
  omega

/-- Floating-point saturation case: `|k| = 2^p` forces `F.IsOdd (k·2^e) = False`
(via renormalization, the canonical significand is `±2^(p-1)`, which is even). -/
theorem not_isOdd_at_saturation {F : ParityFormat}
    {p : ℕ} (hp_eq : F.p = (p : Prec))
    (hp_ne_1 : F.p ≠ ((1 : ℕ) : Prec))
    (hexp_bot : F.exp = ⊥) {k e : ℤ}
    (hk_eq : |k| = (2 : ℤ) ^ p) :
    ¬ F.IsOdd (Dyadic.ofIntZpow k e) := by
  rw [isOdd_iff_odd_of_canonical
        (canonical_rep_at_saturation_floating hp_eq hexp_bot hk_eq) hp_ne_1]
  exact not_odd_k_div_2_at_sat (two_le_p_of_pne1 hp_eq hp_ne_1) hk_eq

/-- Mixed normal regime characterization. `numDigits y = p` when
`log|y| - e' + 1 ≥ p` (the precision branch of min wins). Then IsOdd ↔ Odd k
via canonical IsRepresentableAtP at p bits. -/
theorem isOdd_iff_odd_at_canonical_mixed_normal {F : ParityFormat}
    {p : ℕ} (hp_eq : F.p = (p : Prec))
    (hp_ne_1 : F.p ≠ ((1 : ℕ) : Prec))
    {e' : ℤ} (hexp : F.exp = (e' : QExp))
    {y : Dyadic} (hy_ne : (y : ℝ) ≠ 0)
    (h_log_y_ge : (p : ℤ) ≤ Int.log 2 |(y : ℝ)| - e' + 1)
    {k e_c : ℤ} (h_y_eq : (y : ℝ) = (k : ℝ) * (2 : ℝ) ^ e_c)
    (hk_lo : (2 : ℤ) ^ (p - 1) ≤ |k|)
    (hk_hi : |k| < (2 : ℤ) ^ p) :
    F.IsOdd y ↔ Odd k :=
  isOdd_iff_odd_of_canonical
    (canonical_rep_mixed_normal_pne1 hp_eq hexp hy_ne h_log_y_ge h_y_eq hk_lo hk_hi) hp_ne_1

/-- Mixed subnormal regime characterization. `numDigits y = log|y| - e' + 1`
when `p > log|y| - e' + 1` (the quantum branch of min wins). For
`y = k · 2^e'` with `k ≠ 0`, IsOdd ↔ Odd k (via canonical `(k, e')` form). -/
theorem isOdd_iff_odd_at_canonical_mixed_subnormal {F : ParityFormat}
    {p : ℕ} (hp_eq : F.p = (p : Prec))
    (hp_ne_1 : F.p ≠ ((1 : ℕ) : Prec))
    {e' : ℤ} (hexp : F.exp = (e' : QExp))
    {k : ℤ} (hk_ne : k ≠ 0)
    (h_log_k_lt_p : Int.log 2 (|k| : ℝ) + 1 ≤ (p : ℤ)) :
    F.IsOdd (Dyadic.ofIntZpow k e') ↔ Odd k :=
  isOdd_iff_odd_of_canonical
    (canonical_rep_mixed_subnormal_pne1 hp_eq hexp hk_ne h_log_k_lt_p) hp_ne_1

/-- IsEven dual of `isOdd_iff_odd_at_canonical_mixed_subnormal`. -/
theorem isEven_iff_even_at_canonical_mixed_subnormal {F : ParityFormat}
    {p : ℕ} (hp_eq : F.p = (p : Prec))
    (hp_ne_1 : F.p ≠ ((1 : ℕ) : Prec))
    {e' : ℤ} (hexp : F.exp = (e' : QExp))
    {k : ℤ} (hk_ne : k ≠ 0)
    (h_log_k_lt_p : Int.log 2 (|k| : ℝ) + 1 ≤ (p : ℤ)) :
    F.IsEven (Dyadic.ofIntZpow k e') ↔ Even k :=
  isEven_iff_even_of_canonical
    (canonical_rep_mixed_subnormal_pne1 hp_eq hexp hk_ne h_log_k_lt_p) hp_ne_1

/-- Mixed-normal saturation: when `|k| = 2^p`, IsOdd is false (canonical
form renormalizes to `(k/2, e_c+1)` with `|k/2| = 2^(p-1)`, which is even
for `p ≥ 2`). -/
theorem not_isOdd_at_saturation_mixed_normal {F : ParityFormat}
    {p : ℕ} (hp_eq : F.p = (p : Prec))
    (hp_ne_1 : F.p ≠ ((1 : ℕ) : Prec))
    {e' : ℤ} (hexp : F.exp = (e' : QExp))
    {y : Dyadic} (hy_ne : (y : ℝ) ≠ 0)
    (h_log_y_ge : (p : ℤ) ≤ Int.log 2 |(y : ℝ)| - e' + 1)
    {k e_c : ℤ} (h_y_eq : (y : ℝ) = (k : ℝ) * (2 : ℝ) ^ e_c)
    (hk_eq : |k| = (2 : ℤ) ^ p) :
    ¬ F.IsOdd y := by
  rw [isOdd_iff_odd_of_canonical
        (canonical_rep_at_saturation_mixed_normal hp_eq hexp hy_ne h_log_y_ge
          h_y_eq hk_eq) hp_ne_1]
  exact not_odd_k_div_2_at_sat (two_le_p_of_pne1 hp_eq hp_ne_1) hk_eq

/-- IsEven at saturation (mixed-normal, `p ≠ 1`). Derived from
`not_isOdd_at_saturation_mixed_normal` via the dichotomy. -/
theorem isEven_at_saturation_mixed_normal {F : ParityFormat}
    {p : ℕ} (hp_eq : F.p = (p : Prec))
    (hp_ne_1 : F.p ≠ ((1 : ℕ) : Prec))
    {e' : ℤ} (hexp : F.exp = (e' : QExp))
    {y : Dyadic} (hy_ne : (y : ℝ) ≠ 0)
    (h_log_y_ge : (p : ℤ) ≤ Int.log 2 |(y : ℝ)| - e' + 1)
    {k e_c : ℤ} (h_y_eq : (y : ℝ) = (k : ℝ) * (2 : ℝ) ^ e_c)
    (hk_eq : |k| = (2 : ℤ) ^ p) :
    F.IsEven y := by
  rw [isEven_iff_not_isOdd_of_canonical
        (canonical_rep_at_saturation_mixed_normal hp_eq hexp hy_ne h_log_y_ge
          h_y_eq hk_eq)]
  exact not_isOdd_at_saturation_mixed_normal hp_eq hp_ne_1 hexp hy_ne
    h_log_y_ge h_y_eq hk_eq

/-- Mixed case characterization at `p = 1`. Given `y = k · 2^e_c` with
`|k| = 1` (so the 1-bit canonical form is `(k, e_c)`) and `e_c ≥ e'`,
`F.IsOdd y ↔ Odd (e_c - e' + 1)`. -/
theorem isOdd_p1_iff_at_canonical_mixed {F : ParityFormat}
    (hp_eq : F.p = ((1 : ℕ) : Prec))
    {e' : ℤ} (hexp : F.exp = (e' : QExp))
    {k e_c : ℤ} (hk_eq : |k| = 1) (h_ec_ge : e' ≤ e_c) :
    F.IsOdd (Dyadic.ofIntZpow k e_c) ↔ Odd (e_c - e' + 1) := by
  have h_rep := canonical_rep_mixed_p1 hp_eq hexp hk_eq h_ec_ge
  have h_unbot : WithBot.unbotD 0 F.exp = e' := by rw [hexp]; rfl
  refine ⟨?_, ?_⟩
  · rintro ⟨c', e'', h_rep', h_par⟩
    rw [if_pos hp_eq] at h_par
    obtain ⟨_, h_e_eq⟩ := h_rep'.unique h_rep
    rw [h_e_eq, h_unbot] at h_par
    exact h_par
  · intro h_odd
    refine ⟨k, e_c, h_rep, ?_⟩
    rw [if_pos hp_eq, h_unbot]; exact h_odd

/-- IsEven dual of `isOdd_p1_iff_at_canonical_mixed`. -/
theorem isEven_p1_iff_at_canonical_mixed {F : ParityFormat}
    (hp_eq : F.p = ((1 : ℕ) : Prec))
    {e' : ℤ} (hexp : F.exp = (e' : QExp))
    {k e_c : ℤ} (hk_eq : |k| = 1) (h_ec_ge : e' ≤ e_c) :
    F.IsEven (Dyadic.ofIntZpow k e_c) ↔ Even (e_c - e' + 1) := by
  have h_rep := canonical_rep_mixed_p1 hp_eq hexp hk_eq h_ec_ge
  have hk_ne : k ≠ 0 := by intro h0; rw [h0] at hk_eq; simp at hk_eq
  have h_y_ne : ((Dyadic.ofIntZpow k e_c : Dyadic) : ℝ) ≠ 0 :=
    Dyadic.coe_ofIntZpow_ne_zero hk_ne e_c
  have h_unbot : WithBot.unbotD 0 F.exp = e' := by rw [hexp]; rfl
  refine ⟨?_, ?_⟩
  · rintro (h_y0 | ⟨c', e'', h_rep', h_par⟩)
    · exact absurd (show ((Dyadic.ofIntZpow k e_c : Dyadic) : ℝ) = 0 by
        rw [h_y0]; push_cast; rfl) h_y_ne
    · rw [if_pos hp_eq] at h_par
      obtain ⟨_, h_e_eq⟩ := h_rep'.unique h_rep
      rw [h_e_eq, h_unbot] at h_par
      exact h_par
  · intro h_even
    right
    refine ⟨k, e_c, h_rep, ?_⟩
    rw [if_pos hp_eq, h_unbot]; exact h_even

/-- Alternating parity iff (mixed-subnormal, `p ≠ 1`):
`IsOdd dhi ↔ ¬ IsOdd dlo`. Bulk proof handling edge cases `lo = 0`
(dlo = 0, ¬IsOdd) and `lo = -1` (dhi = 0, ¬IsOdd), and the generic
`Odd lo ↔ ¬ Odd (lo + 1)` case via `isOdd_iff_odd_at_canonical_mixed_subnormal`. -/
theorem alternating_parity_mixed_subnormal_pne1_iff {F : ParityFormat}
    {p : ℕ} (hp_eq : F.p = (p : Prec))
    (hp_ne_1 : F.p ≠ ((1 : ℕ) : Prec))
    {e' : ℤ} (hexp : F.exp = (e' : QExp))
    {lo : ℤ} (h_lo_lt : Int.log 2 (|lo| : ℝ) + 1 ≤ (p : ℤ))
    (h_lop1_lt : Int.log 2 (|lo + 1| : ℝ) + 1 ≤ (p : ℤ)) :
    F.IsOdd (Dyadic.ofIntZpow (lo + 1) e') ↔
      ¬ F.IsOdd (Dyadic.ofIntZpow lo e') := by
  have h_lop1_lt' : Int.log 2 (|((lo + 1 : ℤ) : ℝ)|) + 1 ≤ (p : ℤ) := by
    have h_cast : ((lo + 1 : ℤ) : ℝ) = (lo : ℝ) + 1 := by push_cast; ring
    rw [h_cast]; exact h_lop1_lt
  by_cases hlo_zero : lo = 0
  · subst hlo_zero
    rw [show (0 : ℤ) + 1 = 1 by ring]
    have h_dhi_odd : F.IsOdd (Dyadic.ofIntZpow (1 : ℤ) e') := by
      rw [isOdd_iff_odd_at_canonical_mixed_subnormal hp_eq hp_ne_1 hexp
          (by norm_num : (1 : ℤ) ≠ 0) ?_]
      · exact ⟨0, by ring⟩
      · simp only [Int.cast_one, abs_one, Int.log_one_right, zero_add, Nat.one_le_cast]
        exact (F.p_pos hp_eq)
    have h_not_odd_dlo : ¬ F.IsOdd (Dyadic.ofIntZpow (0 : ℤ) e') := by
      intro h
      have h_zero : Dyadic.ofIntZpow (0 : ℤ) e' = 0 :=
        Subtype.ext (by rw [Dyadic.coe_rat_ofIntZpow]; simp)
      exact IsOdd.ne_zero h h_zero
    exact ⟨fun _ => h_not_odd_dlo, fun _ => h_dhi_odd⟩
  by_cases hlop1_zero : lo + 1 = 0
  · have hlo_neg1 : lo = -1 := by omega
    subst hlo_neg1
    rw [show (-1 : ℤ) + 1 = 0 by ring]
    have h_not_odd_dhi : ¬ F.IsOdd (Dyadic.ofIntZpow (0 : ℤ) e') := by
      intro h
      have h_zero : Dyadic.ofIntZpow (0 : ℤ) e' = 0 :=
        Subtype.ext (by rw [Dyadic.coe_rat_ofIntZpow]; simp)
      exact IsOdd.ne_zero h h_zero
    have h_odd_dlo : F.IsOdd (Dyadic.ofIntZpow (-1 : ℤ) e') := by
      rw [isOdd_iff_odd_at_canonical_mixed_subnormal hp_eq hp_ne_1 hexp
          (by norm_num : (-1 : ℤ) ≠ 0) ?_]
      · exact ⟨-1, by ring⟩
      · simp only [Int.cast_neg, Int.cast_one, abs_neg, abs_one,
          Int.log_one_right, zero_add, Nat.one_le_cast]
        exact (F.p_pos hp_eq)
    exact ⟨fun h => absurd h h_not_odd_dhi, fun h => absurd h_odd_dlo h⟩
  · rw [isOdd_iff_odd_at_canonical_mixed_subnormal hp_eq hp_ne_1 hexp
        hlop1_zero h_lop1_lt']
    rw [isOdd_iff_odd_at_canonical_mixed_subnormal hp_eq hp_ne_1 hexp
        hlo_zero h_lo_lt]
    constructor
    · rintro ⟨m₂, hm₂⟩ ⟨m₁, hm₁⟩; omega
    · intro h_not_odd_lo
      exact Even.add_one (Int.not_odd_iff_even.mp h_not_odd_lo)

theorem alternating_isEven_mixed_subnormal_pne1 {F : ParityFormat}
    {p : ℕ} (hp_eq : F.p = (p : Prec))
    (hp_ne_1 : F.p ≠ ((1 : ℕ) : Prec))
    {e' : ℤ} (hexp : F.exp = (e' : QExp))
    {lo : ℤ} (h_lo_lt : Int.log 2 (|lo| : ℝ) + 1 ≤ (p : ℤ))
    (h_lop1_lt : Int.log 2 (|lo + 1| : ℝ) + 1 ≤ (p : ℤ)) :
    ¬ F.IsEven (Dyadic.ofIntZpow lo e') →
    F.IsEven (Dyadic.ofIntZpow (lo + 1) e') := by
  -- Reduce IsEven_iff to the canonical rep at numDigits; both sides either
  -- equal 0 (and isEven trivially) or have a canonical representation.
  have h_zero_rep : ∀ k : ℤ, k = 0 → Dyadic.ofIntZpow k e' = 0 := fun k hk =>
    Subtype.ext (by rw [Dyadic.coe_rat_ofIntZpow, hk]; push_cast; ring)
  have h_lop1_lt' : Int.log 2 (|((lo + 1 : ℤ) : ℝ)|) + 1 ≤ (p : ℤ) := by
    have h_cast : ((lo + 1 : ℤ) : ℝ) = (lo : ℝ) + 1 := by push_cast; ring
    rw [h_cast]; exact h_lop1_lt
  intro h_not_even
  by_cases hlo_zero : lo = 0
  · exfalso; apply h_not_even
    rw [h_zero_rep lo hlo_zero]; exact isEven_zero F
  by_cases hlop1_zero : lo + 1 = 0
  · rw [h_zero_rep (lo + 1) hlop1_zero]; exact isEven_zero F
  · rw [isEven_iff_even_at_canonical_mixed_subnormal hp_eq hp_ne_1 hexp
        hlo_zero h_lo_lt] at h_not_even
    rw [isEven_iff_even_at_canonical_mixed_subnormal hp_eq hp_ne_1 hexp
        hlop1_zero h_lop1_lt']
    exact Odd.add_one (Int.not_even_iff_odd.mp h_not_even)

/-- Alternating parity iff (mixed-normal, `p ≠ 1`):
`IsOdd y_hi ↔ ¬ IsOdd y_lo`. Bulk proof: case-splits on saturation for
both sides, using `isOdd_iff_odd_at_canonical_mixed_normal` in the
non-sat case and `not_isOdd_at_saturation_mixed_normal` for saturated sides. -/
theorem alternating_parity_mixed_normal_pne1_iff {F : ParityFormat}
    {p : ℕ} (hp_eq : F.p = (p : Prec))
    (hp_ne_1 : F.p ≠ ((1 : ℕ) : Prec))
    {e' : ℤ} (hexp : F.exp = (e' : QExp))
    {y_lo y_hi : Dyadic} (h_y_lo_ne : (y_lo : ℝ) ≠ 0) (h_y_hi_ne : (y_hi : ℝ) ≠ 0)
    (h_log_lo : (p : ℤ) ≤ Int.log 2 |(y_lo : ℝ)| - e' + 1)
    (h_log_hi : (p : ℤ) ≤ Int.log 2 |(y_hi : ℝ)| - e' + 1)
    {lo : ℤ} {e : ℤ}
    (h_y_lo_eq : (y_lo : ℝ) = (lo : ℝ) * (2 : ℝ) ^ e)
    (h_y_hi_eq : (y_hi : ℝ) = ((lo + 1 : ℤ) : ℝ) * (2 : ℝ) ^ e)
    (hlo_lo : (2 : ℤ) ^ (p - 1) ≤ |lo|)
    (hlo_hi : |lo| ≤ (2 : ℤ) ^ p)
    (hlop1_lo : (2 : ℤ) ^ (p - 1) ≤ |lo + 1|)
    (hlop1_hi : |lo + 1| ≤ (2 : ℤ) ^ p) :
    F.IsOdd y_hi ↔ ¬ F.IsOdd y_lo := by
  have h2p_nn : (0 : ℤ) ≤ (2 : ℤ) ^ p := by positivity
  have h_2p_even : Even ((2 : ℤ) ^ p) := by
    refine ⟨(2 : ℤ) ^ (p - 1), ?_⟩
    have := Dyadic.two_pow_succ_pred (F.p_pos hp_eq); linarith
  rcases lt_or_eq_of_le hlo_hi with hlo_lt | hlo_sat
  · rw [isOdd_iff_odd_at_canonical_mixed_normal hp_eq hp_ne_1 hexp h_y_lo_ne
        h_log_lo h_y_lo_eq hlo_lo hlo_lt]
    rcases lt_or_eq_of_le hlop1_hi with hlop1_lt | hlop1_sat
    · rw [isOdd_iff_odd_at_canonical_mixed_normal hp_eq hp_ne_1 hexp h_y_hi_ne
          h_log_hi h_y_hi_eq hlop1_lo hlop1_lt]
      constructor
      · rintro ⟨m₂, hm₂⟩ ⟨m₁, hm₁⟩; omega
      · intro h; exact Even.add_one (Int.not_odd_iff_even.mp h)
    · -- dhi sat: ¬IsOdd dhi; lo+1 even, lo odd.
      have h_not_odd_dhi : ¬ F.IsOdd y_hi :=
        not_isOdd_at_saturation_mixed_normal hp_eq hp_ne_1 hexp h_y_hi_ne
          h_log_hi h_y_hi_eq hlop1_sat
      have h_even_lop1 : Even (lo + 1) := by
        rcases (abs_eq h2p_nn).mp hlop1_sat with h | h
        · rw [h]; exact h_2p_even
        · rw [h]; exact h_2p_even.neg
      have h_odd_lo : Odd lo := by
        rcases h_even_lop1 with ⟨m, hm⟩; exact ⟨m - 1, by omega⟩
      exact ⟨fun h => absurd h h_not_odd_dhi, fun h => absurd h_odd_lo h⟩
  · -- dlo sat: ¬IsOdd dlo, must show IsOdd dhi.
    have h_not_odd_dlo : ¬ F.IsOdd y_lo :=
      not_isOdd_at_saturation_mixed_normal hp_eq hp_ne_1 hexp h_y_lo_ne
        h_log_lo h_y_lo_eq hlo_sat
    rcases (abs_eq h2p_nn).mp hlo_sat with hlo_pos | hlo_neg
    · exfalso
      rw [hlo_pos] at hlop1_hi
      have : (2 : ℤ) ^ p + 1 > 0 := by positivity
      have h_abs : |(2 : ℤ) ^ p + 1| = (2 : ℤ) ^ p + 1 := abs_of_pos this
      linarith
    · have h_lop1_lt : |lo + 1| < (2 : ℤ) ^ p := by
        rw [hlo_neg]
        have h_pos_inner : (0 : ℤ) < (2 : ℤ) ^ p - 1 := by
          have h_two_le : (2 : ℤ) ≤ (2 : ℤ) ^ p := by
            calc (2 : ℤ) = (2 : ℤ) ^ 1 := by ring
              _ ≤ (2 : ℤ) ^ p := pow_le_pow_right₀ (by norm_num) (F.p_pos hp_eq)
          linarith
        have h_eq : -((2 : ℤ) ^ p) + 1 = -((2 : ℤ) ^ p - 1) := by ring
        rw [h_eq, abs_neg, abs_of_pos h_pos_inner]; linarith
      rw [isOdd_iff_odd_at_canonical_mixed_normal hp_eq hp_ne_1 hexp h_y_hi_ne
          h_log_hi h_y_hi_eq hlop1_lo h_lop1_lt]
      have h_odd_lop1 : Odd (lo + 1) := by
        rw [hlo_neg]; exact h_2p_even.neg.add_one
      exact ⟨fun _ => h_not_odd_dlo, fun _ => h_odd_lop1⟩

theorem alternating_isEven_mixed_normal_pne1 {F : ParityFormat}
    {p : ℕ} (hp_eq : F.p = (p : Prec))
    (hp_ne_1 : F.p ≠ ((1 : ℕ) : Prec))
    {e' : ℤ} (hexp : F.exp = (e' : QExp))
    {y_lo y_hi : Dyadic} (h_y_lo_ne : (y_lo : ℝ) ≠ 0) (h_y_hi_ne : (y_hi : ℝ) ≠ 0)
    (h_log_lo : (p : ℤ) ≤ Int.log 2 |(y_lo : ℝ)| - e' + 1)
    (h_log_hi : (p : ℤ) ≤ Int.log 2 |(y_hi : ℝ)| - e' + 1)
    {lo : ℤ} {e : ℤ}
    (h_y_lo_eq : (y_lo : ℝ) = (lo : ℝ) * (2 : ℝ) ^ e)
    (h_y_hi_eq : (y_hi : ℝ) = ((lo + 1 : ℤ) : ℝ) * (2 : ℝ) ^ e)
    (hlo_lo : (2 : ℤ) ^ (p - 1) ≤ |lo|)
    (hlo_hi : |lo| ≤ (2 : ℤ) ^ p)
    (hlop1_lo : (2 : ℤ) ^ (p - 1) ≤ |lo + 1|)
    (hlop1_hi : |lo + 1| ≤ (2 : ℤ) ^ p) :
    ¬ F.IsEven y_lo → F.IsEven y_hi := by
  intro h_not_even
  rcases lt_or_eq_of_le hlo_hi with hlo_lt | hlo_sat
  · rcases lt_or_eq_of_le hlop1_hi with hlop1_lt | hlop1_sat
    · exact alternating_isEven_of_alternating_iff
        (alternating_parity_mixed_normal_pne1_iff hp_eq hp_ne_1 hexp h_y_lo_ne h_y_hi_ne
          h_log_lo h_log_hi h_y_lo_eq h_y_hi_eq hlo_lo hlo_hi hlop1_lo hlop1_hi)
        (Or.inr (canonical_rep_mixed_normal_pne1 hp_eq hexp h_y_lo_ne h_log_lo
          h_y_lo_eq hlo_lo hlo_lt))
        (Or.inr (canonical_rep_mixed_normal_pne1 hp_eq hexp h_y_hi_ne h_log_hi
          h_y_hi_eq hlop1_lo hlop1_lt))
        h_not_even
    · exact isEven_at_saturation_mixed_normal hp_eq hp_ne_1 hexp h_y_hi_ne
        h_log_hi h_y_hi_eq hlop1_sat
  · exfalso; apply h_not_even
    exact isEven_at_saturation_mixed_normal hp_eq hp_ne_1 hexp h_y_lo_ne
      h_log_lo h_y_lo_eq hlo_sat

/-- Alternating parity iff (mixed-subnormal, `p = 1`):
`IsOdd dhi ↔ ¬ IsOdd dlo`. Bulk proof: `interval_cases` lo ∈ {-2, -1, 0, 1}.
Uses `isOdd_p1_iff_at_canonical_mixed` and the parity of
`e' + 1 - e' + 1 = 2` (even, so `Odd 2 = False`). -/
theorem alternating_parity_mixed_subnormal_p1_iff {F : ParityFormat}
    (hp_eq : F.p = ((1 : ℕ) : Prec))
    {e' : ℤ} (hexp : F.exp = (e' : QExp))
    {lo : ℤ} (hlo_hi : |lo| ≤ 2) (hlop1_hi : |lo + 1| ≤ 2) :
    F.IsOdd (Dyadic.ofIntZpow (lo + 1) e') ↔
      ¬ F.IsOdd (Dyadic.ofIntZpow lo e') := by
  have h_lo_ge : -2 ≤ lo := (abs_le.mp hlo_hi).1
  have h_lop1_le : lo + 1 ≤ 2 := (abs_le.mp hlop1_hi).2
  have h_lo_le_1 : lo ≤ 1 := by linarith
  have h_zero_eq : ∀ (e_c : ℤ), Dyadic.ofIntZpow (0 : ℤ) e_c = 0 := fun e_c =>
    Subtype.ext (by rw [Dyadic.coe_rat_ofIntZpow]; simp)
  have h_neg2_canon : Dyadic.ofIntZpow (-2 : ℤ) e' =
      Dyadic.ofIntZpow (-1 : ℤ) (e' + 1) := by
    apply Subtype.ext
    rw [Dyadic.coe_rat_ofIntZpow, Dyadic.coe_rat_ofIntZpow,
        zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_one]
    push_cast; ring
  have h_2_canon : Dyadic.ofIntZpow (2 : ℤ) e' =
      Dyadic.ofIntZpow (1 : ℤ) (e' + 1) := by
    apply Subtype.ext
    rw [Dyadic.coe_rat_ofIntZpow, Dyadic.coe_rat_ofIntZpow,
        zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_one]
    push_cast; ring
  have h_odd2_false : ¬ Odd ((e' + 1) - e' + 1) := by
    rw [show (e' + 1) - e' + 1 = 2 by ring]
    exact Int.not_odd_iff_even.mpr ⟨1, by ring⟩
  have h_not_odd_zero : ¬ F.IsOdd (0 : Dyadic) := fun h => IsOdd.ne_zero h rfl
  have h_odd1 : Odd (e' - e' + 1) := ⟨0, by ring⟩
  interval_cases lo
  · -- lo = -2: lo+1 = -1; dlo = -1·2^(e'+1) so ¬IsOdd dlo, dhi = -1·2^e' so IsOdd dhi.
    rw [h_neg2_canon, isOdd_p1_iff_at_canonical_mixed hp_eq hexp (k := -1)
      (e_c := e' + 1) (by decide) (by linarith)]
    rw [show ((-2 : ℤ) + 1) = (-1 : ℤ) by ring,
        isOdd_p1_iff_at_canonical_mixed hp_eq hexp (k := -1) (e_c := e')
          (by decide) (le_refl _)]
    exact ⟨fun _ h => h_odd2_false h, fun _ => h_odd1⟩
  · -- lo = -1: dlo = -1·2^e' so IsOdd, dhi = 0 so ¬IsOdd.
    rw [show ((-1 : ℤ) + 1) = (0 : ℤ) by ring, h_zero_eq,
        isOdd_p1_iff_at_canonical_mixed hp_eq hexp (k := -1) (e_c := e')
          (by decide) (le_refl _)]
    exact ⟨fun h => absurd h h_not_odd_zero, fun h => absurd h_odd1 h⟩
  · -- lo = 0: dlo = 0 (¬IsOdd), dhi = 1·2^e' (IsOdd).
    rw [show ((0 : ℤ) + 1) = (1 : ℤ) by ring, h_zero_eq,
        isOdd_p1_iff_at_canonical_mixed hp_eq hexp (k := 1) (e_c := e')
          (by decide) (le_refl _)]
    exact ⟨fun _ => h_not_odd_zero, fun _ => h_odd1⟩
  · -- lo = 1: dlo = 1·2^e' (IsOdd), dhi = 2·2^e' = 1·2^(e'+1) (¬IsOdd).
    rw [show ((1 : ℤ) + 1) = (2 : ℤ) by ring, h_2_canon,
        isOdd_p1_iff_at_canonical_mixed hp_eq hexp (k := 1) (e_c := e' + 1)
          (by decide) (by linarith),
        isOdd_p1_iff_at_canonical_mixed hp_eq hexp (k := 1) (e_c := e')
          (by decide) (le_refl _)]
    exact ⟨fun h _ => h_odd2_false h, fun h => absurd h_odd1 h⟩

theorem alternating_isEven_mixed_subnormal_p1 {F : ParityFormat}
    (hp_eq : F.p = ((1 : ℕ) : Prec))
    {e' : ℤ} (hexp : F.exp = (e' : QExp))
    {lo : ℤ} (hlo_hi : |lo| ≤ 2) (hlop1_hi : |lo + 1| ≤ 2) :
    ¬ F.IsEven (Dyadic.ofIntZpow lo e') →
    F.IsEven (Dyadic.ofIntZpow (lo + 1) e') := by
  intro h_not_even
  have h_lo_ge : -2 ≤ lo := (abs_le.mp hlo_hi).1
  have h_lop1_le : lo + 1 ≤ 2 := (abs_le.mp hlop1_hi).2
  have h_lo_le_1 : lo ≤ 1 := by linarith
  have h_zero_eq : ∀ (e_c : ℤ), Dyadic.ofIntZpow (0 : ℤ) e_c = 0 := fun e_c =>
    Subtype.ext (by rw [Dyadic.coe_rat_ofIntZpow]; simp)
  have h_neg2_canon : Dyadic.ofIntZpow (-2 : ℤ) e' =
      Dyadic.ofIntZpow (-1 : ℤ) (e' + 1) := by
    apply Subtype.ext
    rw [Dyadic.coe_rat_ofIntZpow, Dyadic.coe_rat_ofIntZpow,
        zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_one]
    push_cast; ring
  have h_2_canon : Dyadic.ofIntZpow (2 : ℤ) e' =
      Dyadic.ofIntZpow (1 : ℤ) (e' + 1) := by
    apply Subtype.ext
    rw [Dyadic.coe_rat_ofIntZpow, Dyadic.coe_rat_ofIntZpow,
        zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_one]
    push_cast; ring
  have h_even2 : Even ((e' + 1) - e' + 1) := by
    rw [show (e' + 1) - e' + 1 = 2 by ring]; exact ⟨1, by ring⟩
  interval_cases lo
  · -- lo = -2: dlo = -1·2^(e'+1), IsEven dlo (Even 2). Contradiction.
    exfalso; apply h_not_even
    rw [h_neg2_canon, isEven_p1_iff_at_canonical_mixed hp_eq hexp (k := -1)
        (e_c := e' + 1) (by decide) (by linarith)]
    exact h_even2
  · -- lo = -1: dhi = 0, IsEven dhi.
    rw [show ((-1 : ℤ) + 1) = (0 : ℤ) by ring, h_zero_eq]; exact isEven_zero F
  · -- lo = 0: dlo = 0, IsEven dlo. Contradiction.
    exfalso; apply h_not_even
    rw [h_zero_eq]; exact isEven_zero F
  · -- lo = 1: dhi = 1·2^(e'+1), IsEven dhi (Even 2).
    rw [show ((1 : ℤ) + 1) = (2 : ℤ) by ring, h_2_canon,
        isEven_p1_iff_at_canonical_mixed hp_eq hexp (k := 1) (e_c := e' + 1)
          (by decide) (by linarith)]
    exact h_even2

/-- Alternating parity iff (mixed-normal, `p = 1`):
`IsOdd dhi ↔ ¬ IsOdd dlo`. Bulk proof: `interval_cases` lo. The constraints
`1 ≤ |lo|`, `1 ≤ |lo+1|` exclude `lo = -1` and `lo = 0`, leaving only
`lo ∈ {-2, 1}`. -/
theorem alternating_parity_mixed_normal_p1_iff {F : ParityFormat}
    (hp_eq : F.p = ((1 : ℕ) : Prec))
    {e' : ℤ} (hexp : F.exp = (e' : QExp))
    {lo e : ℤ} (h_e_ge : e' ≤ e)
    (hlo_lo : 1 ≤ |lo|) (hlo_hi : |lo| ≤ 2)
    (hlop1_lo : 1 ≤ |lo + 1|) (hlop1_hi : |lo + 1| ≤ 2) :
    F.IsOdd (Dyadic.ofIntZpow (lo + 1) e) ↔
      ¬ F.IsOdd (Dyadic.ofIntZpow lo e) := by
  have h_lo_ge : -2 ≤ lo := (abs_le.mp hlo_hi).1
  have h_lop1_le : lo + 1 ≤ 2 := (abs_le.mp hlop1_hi).2
  have h_lo_le_1 : lo ≤ 1 := by linarith
  have h_lo_ne_neg1 : lo ≠ -1 := by
    intro h_eq
    rw [h_eq, show ((-1 : ℤ) + 1) = 0 by ring] at hlop1_lo
    simp at hlop1_lo
  have h_lo_ne_0 : lo ≠ 0 := by
    intro h_eq; rw [h_eq] at hlo_lo; simp at hlo_lo
  have h_neg2_canon : Dyadic.ofIntZpow (-2 : ℤ) e =
      Dyadic.ofIntZpow (-1 : ℤ) (e + 1) := by
    apply Subtype.ext
    rw [Dyadic.coe_rat_ofIntZpow, Dyadic.coe_rat_ofIntZpow,
        zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_one]
    push_cast; ring
  have h_2_canon : Dyadic.ofIntZpow (2 : ℤ) e =
      Dyadic.ofIntZpow (1 : ℤ) (e + 1) := by
    apply Subtype.ext
    rw [Dyadic.coe_rat_ofIntZpow, Dyadic.coe_rat_ofIntZpow,
        zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_one]
    push_cast; ring
  interval_cases lo
  · -- lo = -2: dlo = -1·2^(e+1), Odd(e+1-e'+1) = Odd(e-e'+2);
    -- dhi = -1·2^e, Odd(e-e'+1).
    rw [h_neg2_canon, show ((-2 : ℤ) + 1) = (-1 : ℤ) by ring,
        isOdd_p1_iff_at_canonical_mixed hp_eq hexp (k := -1) (e_c := e + 1)
          (by decide) (by linarith),
        isOdd_p1_iff_at_canonical_mixed hp_eq hexp (k := -1) (e_c := e)
          (by decide) h_e_ge]
    constructor
    · rintro ⟨m₂, hm₂⟩ ⟨m₁, hm₁⟩; omega
    · intro h
      have h_even : Even (e + 1 - e' + 1) := Int.not_odd_iff_even.mp h
      rcases h_even with ⟨m, hm⟩; exact ⟨m - 1, by omega⟩
  · exact absurd rfl h_lo_ne_neg1
  · exact absurd rfl h_lo_ne_0
  · -- lo = 1: dlo = 1·2^e, Odd(e-e'+1); dhi = 1·2^(e+1), Odd(e-e'+2).
    rw [show ((1 : ℤ) + 1) = (2 : ℤ) by ring, h_2_canon,
        isOdd_p1_iff_at_canonical_mixed hp_eq hexp (k := 1) (e_c := e + 1)
          (by decide) (by linarith),
        isOdd_p1_iff_at_canonical_mixed hp_eq hexp (k := 1) (e_c := e)
          (by decide) h_e_ge]
    constructor
    · rintro ⟨m₂, hm₂⟩ ⟨m₁, hm₁⟩; omega
    · intro h
      have h_even : Even (e - e' + 1) := Int.not_odd_iff_even.mp h
      rcases h_even with ⟨m, hm⟩; exact ⟨m, by omega⟩

theorem alternating_isEven_mixed_normal_p1 {F : ParityFormat}
    (hp_eq : F.p = ((1 : ℕ) : Prec))
    {e' : ℤ} (hexp : F.exp = (e' : QExp))
    {lo e : ℤ} (h_e_ge : e' ≤ e)
    (hlo_lo : 1 ≤ |lo|) (hlo_hi : |lo| ≤ 2)
    (hlop1_lo : 1 ≤ |lo + 1|) (hlop1_hi : |lo + 1| ≤ 2) :
    ¬ F.IsEven (Dyadic.ofIntZpow lo e) →
    F.IsEven (Dyadic.ofIntZpow (lo + 1) e) := by
  intro h_not_even
  have h_lo_ge : -2 ≤ lo := (abs_le.mp hlo_hi).1
  have h_lop1_le : lo + 1 ≤ 2 := (abs_le.mp hlop1_hi).2
  have h_lo_le_1 : lo ≤ 1 := by linarith
  have h_lo_ne_neg1 : lo ≠ -1 := by
    intro h_eq
    rw [h_eq, show ((-1 : ℤ) + 1) = 0 by ring] at hlop1_lo
    simp at hlop1_lo
  have h_lo_ne_0 : lo ≠ 0 := by
    intro h_eq; rw [h_eq] at hlo_lo; simp at hlo_lo
  have h_neg2_canon : Dyadic.ofIntZpow (-2 : ℤ) e =
      Dyadic.ofIntZpow (-1 : ℤ) (e + 1) := by
    apply Subtype.ext
    rw [Dyadic.coe_rat_ofIntZpow, Dyadic.coe_rat_ofIntZpow,
        zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_one]
    push_cast; ring
  have h_2_canon : Dyadic.ofIntZpow (2 : ℤ) e =
      Dyadic.ofIntZpow (1 : ℤ) (e + 1) := by
    apply Subtype.ext
    rw [Dyadic.coe_rat_ofIntZpow, Dyadic.coe_rat_ofIntZpow,
        zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_one]
    push_cast; ring
  interval_cases lo
  · rw [h_neg2_canon, show ((-2 : ℤ) + 1) = (-1 : ℤ) by ring] at *
    rw [isEven_p1_iff_at_canonical_mixed hp_eq hexp (k := -1) (e_c := e + 1)
        (by decide) (by linarith)] at h_not_even
    rw [isEven_p1_iff_at_canonical_mixed hp_eq hexp (k := -1) (e_c := e)
        (by decide) h_e_ge]
    rcases Int.not_even_iff_odd.mp h_not_even with ⟨m, hm⟩
    exact ⟨m, by omega⟩
  · exact absurd rfl h_lo_ne_neg1
  · exact absurd rfl h_lo_ne_0
  · rw [show ((1 : ℤ) + 1) = (2 : ℤ) by ring, h_2_canon]
    rw [isEven_p1_iff_at_canonical_mixed hp_eq hexp (k := 1) (e_c := e)
        (by decide) h_e_ge] at h_not_even
    rw [isEven_p1_iff_at_canonical_mixed hp_eq hexp (k := 1) (e_c := e + 1)
        (by decide) (by linarith)]
    rcases Int.not_even_iff_odd.mp h_not_even with ⟨m, hm⟩
    exact ⟨m + 1, by omega⟩

/-- Saturation in floating-point implies `IsEven`. Derived from
`not_isOdd_at_saturation` via the dichotomy. -/
theorem isEven_at_saturation_floating {F : ParityFormat}
    {p : ℕ} (hp_eq : F.p = (p : Prec))
    (hp_ne_1 : F.p ≠ ((1 : ℕ) : Prec))
    (hexp_bot : F.exp = ⊥) {k e : ℤ}
    (hk_eq : |k| = (2 : ℤ) ^ p) :
    F.IsEven (Dyadic.ofIntZpow k e) := by
  rw [isEven_iff_not_isOdd_of_canonical
        (canonical_rep_at_saturation_floating hp_eq hexp_bot hk_eq)]
  exact not_isOdd_at_saturation hp_eq hp_ne_1 hexp_bot hk_eq

/-- Canonical h_rep construction for fixed-point: for `k ≠ 0`,
the (k, e') pair is the canonical representation of `ofIntZpow k e'` at
`numDigits`-precision. -/
private theorem canonical_rep_fixedpoint {F : ParityFormat}
    (hp_top : F.p = ⊤) {e' : ℤ}
    (hexp : F.exp = (e' : QExp)) {k : ℤ} (hk_ne : k ≠ 0) :
    Dyadic.IsRepresentableAtP
      (F.toFiniteFormat.numDigits ((Dyadic.ofIntZpow k e' : Dyadic) : ℝ)).toNat
      k e' (Dyadic.ofIntZpow k e') := by
  set y : Dyadic := Dyadic.ofIntZpow k e'
  have h_y_real : (y : ℝ) = (k : ℝ) * (2 : ℝ) ^ e' := Dyadic.coe_ofIntZpow k e'
  have h_y_rat : (y : ℚ) = (k : ℚ) * (2 : ℚ) ^ e' := Dyadic.coe_rat_ofIntZpow k e'
  have h_y_ne : (y : ℝ) ≠ 0 := Dyadic.coe_ofIntZpow_ne_zero hk_ne e'
  have h_log_nn : 0 ≤ Int.log 2 (|k| : ℝ) := by
    have h_one_le : (1 : ℝ) ≤ (|k| : ℝ) := by
      have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk_ne
      exact_mod_cast this
    rw [show (0 : ℤ) = Int.log 2 (1 : ℝ) by simp [Int.log_one_right]]
    exact Int.log_mono_right (by linarith) h_one_le
  have h_log_eq : Int.log 2 |(y : ℝ)| = Int.log 2 (|k| : ℝ) + e' := by
    rw [h_y_real]; exact log_abs_mul_zpow hk_ne e'
  have h_nd_eq : F.toFiniteFormat.numDigits (y : ℝ) = Int.log 2 (|k| : ℝ) + 1 := by
    rw [F.toFiniteFormat.numDigits_top_coe h_y_ne hexp hp_top]
    linarith
  have h_nd_toNat : (F.toFiniteFormat.numDigits (y : ℝ)).toNat =
      (Int.log 2 (|k| : ℝ)).toNat + 1 := by
    rw [h_nd_eq]
    have h1 : ((Int.log 2 (|k| : ℝ)).toNat : ℤ) = Int.log 2 (|k| : ℝ) :=
      Int.toNat_of_nonneg h_log_nn
    omega
  rw [h_nd_toNat]
  exact Dyadic.isRepresentableAtP_of_log hk_ne h_y_rat

/-- `IsOdd` depends only on `toFormat`: two `ParityFormat`s with equal `toFormat`
agree on `IsOdd`. Uses Lean's proof irrelevance for the `finite`/`parity`
Prop fields. -/
theorem IsOdd_iff_of_toFormat_eq {F1 F2 : ParityFormat}
    (h : F1.toFormat = F2.toFormat) (y : Dyadic) :
    F1.IsOdd y ↔ F2.IsOdd y := by
  rcases F1 with ⟨⟨FF1, fin1⟩, par1⟩
  rcases F2 with ⟨⟨FF2, fin2⟩, par2⟩
  cases h
  rfl

/-- Dual of `IsOdd_iff_of_toFormat_eq` for `IsEven`. -/
theorem IsEven_iff_of_toFormat_eq {F1 F2 : ParityFormat}
    (h : F1.toFormat = F2.toFormat) (y : Dyadic) :
    F1.IsEven y ↔ F2.IsEven y := by
  rcases F1 with ⟨⟨FF1, fin1⟩, par1⟩
  rcases F2 with ⟨⟨FF2, fin2⟩, par2⟩
  cases h
  rfl

/-- Fixed-point characterization (`F.p = ⊤, F.exp = (e' : ℤ)`):
`F.IsOdd (Dyadic.ofIntZpow k e') ↔ Odd k`, for `k ≠ 0`. No saturation
since `numDigits` adapts to `log|k| + 1`. -/
theorem isOdd_iff_odd_at_canonical_fixedpoint {F : ParityFormat}
    (hp_top : F.p = ⊤) {e' : ℤ}
    (hexp : F.exp = (e' : QExp)) {k : ℤ} (hk_ne : k ≠ 0) :
    F.IsOdd (Dyadic.ofIntZpow k e') ↔ Odd k := by
  have hp_ne_1 : F.p ≠ ((1 : ℕ) : Prec) := by rw [hp_top]; decide
  exact isOdd_iff_odd_of_canonical (canonical_rep_fixedpoint hp_top hexp hk_ne) hp_ne_1

/-- Alternating parity iff (fixed-point): `IsOdd dhi ↔ ¬ IsOdd dlo` at
canonical exponent `e'`. Handles the edge cases `lo = 0` (dlo = 0,
IsOdd false) and `lo = -1` (dhi = 0, IsOdd false) directly. -/
theorem alternating_parity_fixedpoint_iff {F : ParityFormat}
    (hp_top : F.p = ⊤) {e' : ℤ}
    (hexp : F.exp = (e' : QExp)) {lo : ℤ} :
    F.IsOdd (Dyadic.ofIntZpow (lo + 1) e') ↔
      ¬ F.IsOdd (Dyadic.ofIntZpow lo e') := by
  by_cases hlo_zero : lo = 0
  · subst hlo_zero
    rw [show (0 : ℤ) + 1 = 1 by ring]
    have h_dhi_odd : F.IsOdd (Dyadic.ofIntZpow (1 : ℤ) e') := by
      rw [isOdd_iff_odd_at_canonical_fixedpoint hp_top hexp (by norm_num : (1 : ℤ) ≠ 0)]
      exact ⟨0, by ring⟩
    have h_not_odd_dlo : ¬ F.IsOdd (Dyadic.ofIntZpow (0 : ℤ) e') := by
      intro h
      have h_zero : (Dyadic.ofIntZpow (0 : ℤ) e' : ℚ) = 0 := by
        rw [Dyadic.coe_rat_ofIntZpow]; ring
      exact (IsOdd.ne_zero h) (by apply Subtype.ext; exact h_zero)
    exact ⟨fun _ => h_not_odd_dlo, fun _ => h_dhi_odd⟩
  by_cases hlop1_zero : lo + 1 = 0
  · have hlo_neg1 : lo = -1 := by omega
    subst hlo_neg1
    rw [show (-1 : ℤ) + 1 = 0 by ring]
    have h_not_odd_dhi : ¬ F.IsOdd (Dyadic.ofIntZpow (0 : ℤ) e') := by
      intro h
      have h_zero : (Dyadic.ofIntZpow (0 : ℤ) e' : ℚ) = 0 := by
        rw [Dyadic.coe_rat_ofIntZpow]; ring
      exact (IsOdd.ne_zero h) (by apply Subtype.ext; exact h_zero)
    have h_odd_dlo : F.IsOdd (Dyadic.ofIntZpow (-1 : ℤ) e') := by
      rw [isOdd_iff_odd_at_canonical_fixedpoint hp_top hexp (by norm_num : (-1 : ℤ) ≠ 0)]
      exact ⟨-1, by ring⟩
    exact ⟨fun h => absurd h h_not_odd_dhi, fun h => absurd h_odd_dlo h⟩
  · rw [isOdd_iff_odd_at_canonical_fixedpoint hp_top hexp hlo_zero]
    rw [isOdd_iff_odd_at_canonical_fixedpoint hp_top hexp hlop1_zero]
    constructor
    · rintro ⟨m₂, hm₂⟩ ⟨m₁, hm₁⟩; omega
    · intro h_not_odd_lo
      exact Even.add_one (Int.not_odd_iff_even.mp h_not_odd_lo)

theorem alternating_isEven_fixedpoint {F : ParityFormat}
    (hp_top : F.p = ⊤) {e' : ℤ}
    (hexp : F.exp = (e' : QExp)) {lo : ℤ} :
    ¬ F.IsEven (Dyadic.ofIntZpow lo e') →
    F.IsEven (Dyadic.ofIntZpow (lo + 1) e') := by
  apply alternating_isEven_of_alternating_iff
    (alternating_parity_fixedpoint_iff hp_top hexp)
  · by_cases h : lo = 0
    · left; apply Subtype.ext
      rw [Dyadic.coe_rat_ofIntZpow, h]; push_cast; ring
    · right; exact canonical_rep_fixedpoint hp_top hexp h
  · by_cases h : lo + 1 = 0
    · left; apply Subtype.ext
      rw [Dyadic.coe_rat_ofIntZpow, h]; push_cast; ring
    · right; exact canonical_rep_fixedpoint hp_top hexp h

/-- Alternating parity iff (floating-point):
`IsOdd dhi ↔ ¬ IsOdd dlo`. Bulk proof: case-splits on saturation for both
sides, using `isOdd_iff_odd_at_canonical_floating` plus integer arithmetic
in the non-sat × non-sat case, and `not_isOdd_at_saturation` for the
saturated sides. -/
theorem alternating_parity_floating_iff {F : ParityFormat}
    {p : ℕ} (hp_eq : F.p = (p : Prec))
    (hp_ne_1 : F.p ≠ ((1 : ℕ) : Prec))
    (hexp_bot : F.exp = ⊥) {lo e : ℤ}
    (hlo_lo : (2 : ℤ) ^ (p - 1) ≤ |lo|)
    (hlo_hi : |lo| ≤ (2 : ℤ) ^ p)
    (hlop1_lo : (2 : ℤ) ^ (p - 1) ≤ |lo + 1|)
    (hlop1_hi : |lo + 1| ≤ (2 : ℤ) ^ p) :
    F.IsOdd (Dyadic.ofIntZpow (lo + 1) e) ↔
      ¬ F.IsOdd (Dyadic.ofIntZpow lo e) := by
  have h2p_nn : (0 : ℤ) ≤ (2 : ℤ) ^ p := by positivity
  have h_2p_even : Even ((2 : ℤ) ^ p) := by
    refine ⟨(2 : ℤ) ^ (p - 1), ?_⟩
    have := Dyadic.two_pow_succ_pred (F.p_pos hp_eq); linarith
  rcases lt_or_eq_of_le hlo_hi with hlo_lt | hlo_sat
  · rw [isOdd_iff_odd_at_canonical_floating hp_eq hp_ne_1 hexp_bot hlo_lo hlo_lt]
    rcases lt_or_eq_of_le hlop1_hi with hlop1_lt | hlop1_sat
    · rw [isOdd_iff_odd_at_canonical_floating hp_eq hp_ne_1 hexp_bot hlop1_lo hlop1_lt]
      constructor
      · rintro ⟨m₂, hm₂⟩ ⟨m₁, hm₁⟩; omega
      · intro h; exact Even.add_one (Int.not_odd_iff_even.mp h)
    · -- dhi sat: ¬IsOdd dhi.
      have h_not_odd_dhi : ¬ F.IsOdd (Dyadic.ofIntZpow (lo + 1) e) :=
        not_isOdd_at_saturation hp_eq hp_ne_1 hexp_bot hlop1_sat
      -- |lo+1| = 2^p ⟹ lo+1 even ⟹ lo odd.
      have h_even_lop1 : Even (lo + 1) := by
        rcases (abs_eq h2p_nn).mp hlop1_sat with h | h
        · rw [h]; exact h_2p_even
        · rw [h]; exact h_2p_even.neg
      have h_odd_lo : Odd lo := by
        rcases h_even_lop1 with ⟨m, hm⟩; exact ⟨m - 1, by omega⟩
      exact ⟨fun h => absurd h h_not_odd_dhi, fun h => absurd h_odd_lo h⟩
  · -- dlo sat: ¬IsOdd dlo, so RHS is True. Show LHS (IsOdd dhi).
    have h_not_odd_dlo : ¬ F.IsOdd (Dyadic.ofIntZpow lo e) :=
      not_isOdd_at_saturation hp_eq hp_ne_1 hexp_bot hlo_sat
    rcases (abs_eq h2p_nn).mp hlo_sat with hlo_pos | hlo_neg
    · -- lo = 2^p: lo+1 = 2^p+1 with |.| = 2^p+1 > 2^p, contradiction with hlop1_hi.
      exfalso
      rw [hlo_pos] at hlop1_hi
      have : (2 : ℤ) ^ p + 1 > 0 := by positivity
      have h_abs : |(2 : ℤ) ^ p + 1| = (2 : ℤ) ^ p + 1 := abs_of_pos this
      linarith
    · -- lo = -2^p: lo+1 = -(2^p - 1), |lo+1| < 2^p so dhi non-sat with Odd (lo+1).
      have h_lop1_lt : |lo + 1| < (2 : ℤ) ^ p := by
        rw [hlo_neg]
        have h_pos_inner : (0 : ℤ) < (2 : ℤ) ^ p - 1 := by
          have h_two_le : (2 : ℤ) ≤ (2 : ℤ) ^ p := by
            calc (2 : ℤ) = (2 : ℤ) ^ 1 := by ring
              _ ≤ (2 : ℤ) ^ p := pow_le_pow_right₀ (by norm_num) (F.p_pos hp_eq)
          linarith
        have h_eq : -((2 : ℤ) ^ p) + 1 = -((2 : ℤ) ^ p - 1) := by ring
        rw [h_eq, abs_neg, abs_of_pos h_pos_inner]; linarith
      have h_odd_lop1 : Odd (lo + 1) := by
        rw [hlo_neg]; exact h_2p_even.neg.add_one
      rw [isOdd_iff_odd_at_canonical_floating hp_eq hp_ne_1 hexp_bot hlop1_lo h_lop1_lt]
      exact ⟨fun _ => h_not_odd_dlo, fun _ => h_odd_lop1⟩

theorem alternating_isEven_floating {F : ParityFormat}
    {p : ℕ} (hp_eq : F.p = (p : Prec))
    (hp_ne_1 : F.p ≠ ((1 : ℕ) : Prec))
    (hexp_bot : F.exp = ⊥) {lo e : ℤ}
    (hlo_lo : (2 : ℤ) ^ (p - 1) ≤ |lo|)
    (hlo_hi : |lo| ≤ (2 : ℤ) ^ p)
    (hlop1_lo : (2 : ℤ) ^ (p - 1) ≤ |lo + 1|)
    (hlop1_hi : |lo + 1| ≤ (2 : ℤ) ^ p) :
    ¬ F.IsEven (Dyadic.ofIntZpow lo e) →
    F.IsEven (Dyadic.ofIntZpow (lo + 1) e) := by
  intro h_not_even
  rcases lt_or_eq_of_le hlo_hi with hlo_lt | hlo_sat
  · rcases lt_or_eq_of_le hlop1_hi with hlop1_lt | hlop1_sat
    · -- Both non-sat: use generic helper.
      exact alternating_isEven_of_alternating_iff
        (alternating_parity_floating_iff hp_eq hp_ne_1 hexp_bot
          hlo_lo hlo_hi hlop1_lo hlop1_hi)
        (Or.inr (canonical_rep_floating hp_eq hexp_bot hlo_lo hlo_lt))
        (Or.inr (canonical_rep_floating hp_eq hexp_bot hlop1_lo hlop1_lt))
        h_not_even
    · exact isEven_at_saturation_floating hp_eq hp_ne_1 hexp_bot hlop1_sat
  · exfalso; apply h_not_even
    exact isEven_at_saturation_floating hp_eq hp_ne_1 hexp_bot hlo_sat

end ParityFormat

/-! ### Parity transport -/

/-- Transport a parity witness (`∃ F', F'.toFormat = _ ∧ F'.IsOdd y`) between
formats agreeing on `(p, exp)`. -/
theorem parity_witness_congr {F G : FiniteFormat} (hp : F.p = G.p)
    (he : F.exp = G.exp) {y : Dyadic}
    (h : ∃ F' : ParityFormat, F'.toFormat = F.toFormat ∧ F'.IsOdd y) :
    ∃ F'' : ParityFormat, F''.toFormat = G.toFormat ∧ F''.IsOdd y := by
  obtain ⟨F', hFeq, hodd⟩ := h
  have hp' : F'.p = G.p := by rw [congrArg Format.p hFeq]; exact hp
  have he' : F'.exp = G.exp := by rw [congrArg Format.exp hFeq]; exact he
  refine ⟨⟨G, by rw [← hp', ← he']; exact F'.parity⟩, rfl, ?_⟩
  obtain ⟨c, e, hrep, hpar⟩ := hodd
  refine ⟨c, e, ?_, ?_⟩
  · change Dyadic.IsRepresentableAtP (G.numDigits (y : ℝ)).toNat c e y
    rwa [numDigits_congr (F := G) (G := F'.toFiniteFormat) hp'.symm he'.symm (y : ℝ)]
  · change if G.p = ((1 : ℕ) : Prec) then
        Odd (e - WithBot.unbotD 0 G.exp + 1) else Odd c
    rw [← hp', ← he']
    exact hpar

/-- Transport an even-parity witness (`∃ F', F'.toFormat = _ ∧ F'.IsEven y`)
between formats agreeing on `(p, exp)`. -/
theorem parity_witness_even_congr {F G : FiniteFormat} (hp : F.p = G.p)
    (he : F.exp = G.exp) {y : Dyadic}
    (h : ∃ F' : ParityFormat, F'.toFormat = F.toFormat ∧ F'.IsEven y) :
    ∃ F'' : ParityFormat, F''.toFormat = G.toFormat ∧ F''.IsEven y := by
  obtain ⟨F', hFeq, heven⟩ := h
  have hp' : F'.p = G.p := by rw [congrArg Format.p hFeq]; exact hp
  have he' : F'.exp = G.exp := by rw [congrArg Format.exp hFeq]; exact he
  refine ⟨⟨G, by rw [← hp', ← he']; exact F'.parity⟩, rfl, ?_⟩
  rcases heven with h0 | ⟨c, e, hrep, hpar⟩
  · exact Or.inl h0
  refine Or.inr ⟨c, e, ?_, ?_⟩
  · change Dyadic.IsRepresentableAtP (G.numDigits (y : ℝ)).toNat c e y
    rwa [numDigits_congr (F := G) (G := F'.toFiniteFormat) hp'.symm he'.symm (y : ℝ)]
  · change if G.p = ((1 : ℕ) : Prec) then
        Even (e - WithBot.unbotD 0 G.exp + 1) else Even c
    rw [← hp', ← he']
    exact hpar

end Mpfx
