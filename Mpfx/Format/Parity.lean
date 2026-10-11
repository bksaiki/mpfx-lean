import Mpfx.Format.Next
import Mpfx.Format.CanonicalExp

/-!
# Parity formats

`ParityFormat`, the `IsOdd` / `IsEven` classification of its elements,
negation, exclusivity, and transport across formats with equal `toFormat` or
`(p, exp)` (`congr`).

Parity then reduces to membership in the shrink `𝒜(p − 1, exp + 1)`. For
`p ≠ 1` its values are exactly the even values of `F`
(`isEven_iff_mem_shrink`), and the odd values are those of `F` outside it
(`isOdd_iff_mem_shrink`). Hence:

* a multiple `k · 2^e` of the canonical step is even exactly when `k` is
  (`FiniteFormat.ofIntZpow_mem_shrink_iff`), which gives alternation;
* containment carries shrink membership from a subformat into a format with
  `p ≥ 2` (`Format.mem_shrink_of_subset`), which gives the RTO-padding lemma
  `IsOdd.transfer_of_subset`.

Precision `1` is the exception: its even values `{0, ±2^(exp+1+2j)}` are not a
format, and parity counts exponents (`isOdd_ofIntZpow_of_p_one`).
-/

namespace Mpfx

/-- A `FiniteFormat` where parity is well-defined: `p ≠ 1` whenever
`exp = ⊥`. Combined with `FiniteFormat.finite`, this is
`(p ≠ ⊤ ∧ p ≠ 1) ∨ exp ≠ ⊥`. Required for `IsOdd` / `IsEven`. -/
structure ParityFormat extends FiniteFormat where
  parity : toFormat.p ≠ 1 ∨ toFormat.exp ≠ ⊥

namespace ParityFormat

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

/-- An `IsOdd` value is nonzero. -/
theorem IsOdd.ne_zero {F : ParityFormat} {y : Dyadic} (h : IsOdd F y) :
    y ≠ 0 := by
  obtain ⟨c, e, hrep, _⟩ := h
  exact fun hy0 => hrep.ne_zero (by simp [hy0])

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

end ParityFormat

/-! ### Parity transport -/

namespace ParityFormat

/-- `IsOdd` depends only on `(p, exp)`. -/
theorem IsOdd.congr {F G : ParityFormat} (hp : F.p = G.p) (he : F.exp = G.exp)
    {y : Dyadic} (h : F.IsOdd y) : G.IsOdd y := by
  obtain ⟨c, e, hrep, hpar⟩ := h
  refine ⟨c, e, ?_, ?_⟩
  · change Dyadic.IsRepresentableAtP (G.numDigits (y : ℝ)).toNat c e y
    rwa [numDigits_congr (F := G.toFiniteFormat) (G := F.toFiniteFormat) hp.symm he.symm]
  · change if G.p = ((1 : ℕ) : Prec) then
        Odd (e - WithBot.unbotD 0 G.exp + 1) else Odd c
    rw [← hp, ← he]
    exact hpar

/-- `IsEven` depends only on `(p, exp)`. -/
theorem IsEven.congr {F G : ParityFormat} (hp : F.p = G.p) (he : F.exp = G.exp)
    {y : Dyadic} (h : F.IsEven y) : G.IsEven y := by
  rcases h with h0 | ⟨c, e, hrep, hpar⟩
  · exact Or.inl h0
  refine Or.inr ⟨c, e, ?_, ?_⟩
  · change Dyadic.IsRepresentableAtP (G.numDigits (y : ℝ)).toNat c e y
    rwa [numDigits_congr (F := G.toFiniteFormat) (G := F.toFiniteFormat) hp.symm he.symm]
  · change if G.p = ((1 : ℕ) : Prec) then
        Even (e - WithBot.unbotD 0 G.exp + 1) else Even c
    rw [← hp, ← he]
    exact hpar

end ParityFormat

/-- Transport a parity witness (`∃ F', F'.toFormat = _ ∧ F'.IsOdd y`) between
formats agreeing on `(p, exp)`. -/
theorem parity_witness_congr {F G : FiniteFormat} (hp : F.p = G.p)
    (he : F.exp = G.exp) {y : Dyadic}
    (h : ∃ F' : ParityFormat, F'.toFormat = F.toFormat ∧ F'.IsOdd y) :
    ∃ F'' : ParityFormat, F''.toFormat = G.toFormat ∧ F''.IsOdd y := by
  obtain ⟨F', hFeq, hodd⟩ := h
  have hp' : F'.p = G.p := by rw [congrArg Format.p hFeq]; exact hp
  have he' : F'.exp = G.exp := by rw [congrArg Format.exp hFeq]; exact he
  exact ⟨⟨G, by rw [← hp', ← he']; exact F'.parity⟩, rfl,
    hodd.congr (G := ⟨G, _⟩) hp' he'⟩

/-- Transport an even-parity witness (`∃ F', F'.toFormat = _ ∧ F'.IsEven y`)
between formats agreeing on `(p, exp)`. -/
theorem parity_witness_even_congr {F G : FiniteFormat} (hp : F.p = G.p)
    (he : F.exp = G.exp) {y : Dyadic}
    (h : ∃ F' : ParityFormat, F'.toFormat = F.toFormat ∧ F'.IsEven y) :
    ∃ F'' : ParityFormat, F''.toFormat = G.toFormat ∧ F''.IsEven y := by
  obtain ⟨F', hFeq, heven⟩ := h
  have hp' : F'.p = G.p := by rw [congrArg Format.p hFeq]; exact hp
  have he' : F'.exp = G.exp := by rw [congrArg Format.exp hFeq]; exact he
  exact ⟨⟨G, by rw [← hp', ← he']; exact F'.parity⟩, rfl,
    heven.congr (G := ⟨G, _⟩) hp' he'⟩

/-! ### The canonical significand -/

namespace FiniteFormat

/-- A representation at `y`'s digit count is the one at the canonical
exponent. -/
theorem isRepresentableAtP_numDigits_iff (F : FiniteFormat) {y : Dyadic} {c e : ℤ} :
    Dyadic.IsRepresentableAtP (F.numDigits (y : ℝ)).toNat c e y ↔
      (y : ℝ) ≠ 0 ∧ e = F.canonicalExp y ∧ (y : ℝ) = c * 2 ^ e := by
  constructor
  · rintro ⟨hyq, hlo, hhi⟩
    have hy : (y : ℝ) = c * 2 ^ e := by
      rw [Dyadic.coe_real_eq_ratCast, hyq]; push_cast; ring
    set n := (F.numDigits (y : ℝ)).toNat with hn
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · have h1 : |c| < 1 := by simpa [h0] using hhi
        have h2 : 1 ≤ |c| := by simpa [h0] using hlo
        omega
      · exact h0
    have hc0 : c ≠ 0 := by
      rintro rfl
      have := pow_pos (two_pos : (0 : ℤ) < 2) (n - 1)
      simp at hlo; omega
    have hy0 : (y : ℝ) ≠ 0 := by
      rw [hy]; exact mul_ne_zero (by exact_mod_cast hc0) (zpow_pos two_pos e).ne'
    -- `2^(n-1) ≤ |c| < 2^n` puts `|y| = |c| · 2^e` in binade `n - 1 + e`.
    have hlog : Int.log 2 |(y : ℝ)| = (n - 1 : ℕ) + e := by
      have hlo' : (2 : ℝ) ^ ((n - 1 : ℕ) : ℤ) ≤ |(c : ℝ)| := by
        rw [zpow_natCast]; exact_mod_cast hlo
      have hhi' : |(c : ℝ)| < (2 : ℝ) ^ (((n - 1 : ℕ) : ℤ) + 1) := by
        rw [show ((n - 1 : ℕ) : ℤ) + 1 = (n : ℤ) by omega, zpow_natCast]; exact_mod_cast hhi
      have h2e : (0 : ℝ) < 2 ^ e := zpow_pos two_pos e
      rw [hy, abs_mul_two_zpow]
      refine log_eq_of_zpow_bounds (mul_pos (abs_pos.mpr (by exact_mod_cast hc0)) h2e) ?_ ?_
      · rw [zpow_add₀ two_ne_zero]; exact mul_le_mul_of_nonneg_right hlo' h2e.le
      · rw [show ((n - 1 : ℕ) : ℤ) + e + 1 = (((n - 1 : ℕ) : ℤ) + 1) + e by ring,
          zpow_add₀ two_ne_zero]
        exact mul_lt_mul_of_pos_right hhi' h2e
    have hnd : (n : ℤ) = F.numDigits (y : ℝ) := Int.toNat_of_nonneg (by omega)
    rw [numDigits, if_neg hy0] at hnd
    exact ⟨hy0, by omega, hy⟩
  · rintro ⟨hy0, rfl, hy⟩
    set e := F.canonicalExp (y : ℝ)
    have hc0 : c ≠ 0 := by rintro rfl; exact hy0 (by rw [hy]; simp)
    have hL : 0 ≤ Int.log 2 |(c : ℝ)| := by
      rw [Int.log_of_one_le_right _ (by exact_mod_cast Int.one_le_abs hc0)]
      exact Nat.cast_nonneg _
    have hlog : Int.log 2 |(y : ℝ)| = Int.log 2 |(c : ℝ)| + e := by
      rw [hy, log_abs_mul_zpow hc0]
    have hnd : (F.numDigits (y : ℝ)).toNat = (Int.log 2 |(c : ℝ)|).toNat + 1 := by
      rw [numDigits, if_neg hy0, hlog]; omega
    rw [hnd]
    refine Dyadic.isRepresentableAtP_of_log hc0 ?_
    have : ((y : ℚ) : ℝ) = ((c * 2 ^ e : ℚ) : ℝ) := by
      rw [← Dyadic.coe_real_eq_ratCast, hy]; push_cast; ring
    exact_mod_cast this

end FiniteFormat

namespace ParityFormat

/-- `IsOdd` at the canonical exponent: `y ≠ 0` is `c · 2^cexp y` with `c` odd,
or, at precision `1`, its exponent has odd index above `exp`. -/
theorem isOdd_iff_canonical (F : ParityFormat) (y : Dyadic) :
    F.IsOdd y ↔ (y : ℝ) ≠ 0 ∧ ∃ c : ℤ, (y : ℝ) = c * 2 ^ F.canonicalExp y ∧
      if F.p = ((1 : ℕ) : Prec) then
        Odd (F.canonicalExp y - WithBot.unbotD 0 F.exp + 1) else Odd c := by
  constructor
  · rintro ⟨c, e, hrep, hpar⟩
    obtain ⟨hy0, rfl, hy⟩ := F.isRepresentableAtP_numDigits_iff.mp hrep
    exact ⟨hy0, c, hy, hpar⟩
  · rintro ⟨hy0, c, hy, hpar⟩
    exact ⟨c, _, F.isRepresentableAtP_numDigits_iff.mpr ⟨hy0, rfl, hy⟩, hpar⟩

/-- `IsEven` at the canonical exponent, the dual of `isOdd_iff_canonical`. -/
theorem isEven_iff_canonical (F : ParityFormat) (y : Dyadic) :
    F.IsEven y ↔ y = 0 ∨ (y : ℝ) ≠ 0 ∧ ∃ c : ℤ, (y : ℝ) = c * 2 ^ F.canonicalExp y ∧
      if F.p = ((1 : ℕ) : Prec) then
        Even (F.canonicalExp y - WithBot.unbotD 0 F.exp + 1) else Even c := by
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨c, e, hrep, hpar⟩
    obtain ⟨hy0, rfl, hy⟩ := F.isRepresentableAtP_numDigits_iff.mp hrep
    exact ⟨hy0, c, hy, hpar⟩
  · rintro ⟨hy0, c, hy, hpar⟩
    exact ⟨c, _, F.isRepresentableAtP_numDigits_iff.mpr ⟨hy0, rfl, hy⟩, hpar⟩

/-- For `p ≠ 1`, `y` is odd iff its significand at the canonical exponent is. -/
theorem isOdd_iff_odd (F : ParityFormat) (hp : F.p ≠ ((1 : ℕ) : Prec)) (y : Dyadic) :
    F.IsOdd y ↔ ∃ c : ℤ, (y : ℝ) = c * 2 ^ F.canonicalExp y ∧ Odd c := by
  simp only [isOdd_iff_canonical, if_neg hp]
  refine ⟨fun ⟨_, h⟩ => h, fun ⟨c, hy, hc⟩ => ⟨?_, c, hy, hc⟩⟩
  have hc0 : c ≠ 0 := by rintro rfl; exact Int.not_odd_iff_even.mpr Even.zero hc
  rw [hy]
  exact mul_ne_zero (by exact_mod_cast hc0) (zpow_pos two_pos _).ne'

/-- For `p ≠ 1`, `y` is even iff its significand at the canonical exponent is. -/
theorem isEven_iff_even (F : ParityFormat) (hp : F.p ≠ ((1 : ℕ) : Prec)) (y : Dyadic) :
    F.IsEven y ↔ ∃ c : ℤ, (y : ℝ) = c * 2 ^ F.canonicalExp y ∧ Even c := by
  simp only [isEven_iff_canonical, if_neg hp]
  constructor
  · rintro (rfl | ⟨_, h⟩)
    · exact ⟨0, by simp, Even.zero⟩
    · exact h
  · rintro ⟨c, hy, hc⟩
    by_cases hy0 : (y : ℝ) = 0
    · exact Or.inl (eq_zero_of_coe_real_zero hy0)
    · exact Or.inr ⟨hy0, c, hy, hc⟩

/-! ### Even values are the shrink -/

/-- **Even values are the shrink.** For `p ≠ 1`, `y` is even exactly when it
is a value of `𝒜(p − 1, exp + 1)`: an even significand at `cexp y` is a
significand at `cexp y + 1`, the shrink's canonical exponent. -/
theorem isEven_iff_mem_shrink (F : ParityFormat) (hp : F.p ≠ ((1 : ℕ) : Prec))
    (y : Dyadic) : F.IsEven y ↔ y ∈ (F.shrink hp).unbounded := by
  rw [isEven_iff_even F hp]
  by_cases hy0 : (y : ℝ) = 0
  · rw [eq_zero_of_coe_real_zero hy0]
    exact iff_of_true ⟨0, by simp, Even.zero⟩ (FiniteFormat.zero_mem _)
  have hC := FiniteFormat.canonicalExp_shrink F.toFiniteFormat hp hy0
  constructor
  · rintro ⟨c, hy, k, rfl⟩
    refine FiniteFormat.mem_unbounded_of_mul_zpow_canonicalExp _ (m := k) ?_
    rw [hC]
    refine hy.trans ?_
    rw [zpow_add_one₀ two_ne_zero]; push_cast; ring
  · intro hmem
    obtain ⟨m, hm⟩ := (F.shrink hp).exists_mul_zpow_canonicalExp hmem
    refine ⟨2 * m, hm.trans ?_, even_two_mul m⟩
    rw [hC, zpow_add_one₀ two_ne_zero]; push_cast; ring

/-- **Odd values are the rest.** For `p ≠ 1`, `y` is odd exactly when it is a
value of `F` outside the shrink. -/
theorem isOdd_iff_mem_shrink (F : ParityFormat) (hp : F.p ≠ ((1 : ℕ) : Prec))
    (y : Dyadic) :
    F.IsOdd y ↔ y ∈ F.unbounded ∧ y ∉ (F.shrink hp).unbounded := by
  constructor
  · intro h
    obtain ⟨c, hy, -⟩ := (isOdd_iff_odd F hp y).mp h
    exact ⟨F.mem_unbounded_of_mul_zpow_canonicalExp hy,
      fun hC => not_isEven_and_isOdd ((isEven_iff_mem_shrink F hp y).mpr hC) h⟩
  · rintro ⟨hmem, hC⟩
    obtain ⟨c, hc⟩ := F.exists_mul_zpow_canonicalExp hmem
    exact (isOdd_iff_odd F hp y).mpr ⟨c, hc, Int.not_even_iff_odd.mp fun he =>
      hC ((isEven_iff_mem_shrink F hp y).mp ((isEven_iff_even F hp y).mpr ⟨c, hc, he⟩))⟩

end ParityFormat

/-! ### Multiples of the canonical step -/

namespace FiniteFormat

/-- **Alternation at the canonical step.** A multiple `k · 2^e` of a step at
least the quantum, whose own canonical exponent is at least `e`, lies in the
shrink exactly when `k` is even. -/
theorem ofIntZpow_mem_shrink_iff (F : FiniteFormat) (h : F.p ≠ ((1 : ℕ) : Prec))
    {k e : ℤ} (he : F.exp ≤ (e : QExp)) (hk : ∀ p : ℕ, F.p = p → |k| ≤ 2 ^ p)
    (hce : k ≠ 0 → e ≤ F.canonicalExp (Dyadic.ofIntZpow k e)) :
    Dyadic.ofIntZpow k e ∈ (F.shrink h).unbounded ↔ Even k := by
  constructor
  · intro hmem
    by_contra hodd
    have hk0 : k ≠ 0 := by rintro rfl; exact hodd Even.zero
    have hkc := hce hk0
    obtain ⟨m, hm⟩ := (F.shrink h).exists_mul_zpow_canonicalExp hmem
    rw [canonicalExp_shrink F h (Dyadic.coe_ofIntZpow_ne_zero hk0 e)] at hm
    -- `k · 2^e = m · 2^(c + 1)` with `e < c + 1` makes `k` even.
    have hshift := coeff_eq_of_shift (K := ℝ) (by omega) ((Dyadic.coe_ofIntZpow k e).symm.trans hm)
    exact hodd (hshift ▸ (Int.even_pow.mpr ⟨even_two, by omega⟩).mul_left m)
  · rintro ⟨j, rfl⟩
    have hd : Dyadic.ofIntZpow (j + j) e = Dyadic.ofIntZpow j (e + 1) := Dyadic.ext_real (by
      simp only [Dyadic.coe_ofIntZpow]; rw [zpow_add_one₀ two_ne_zero]; push_cast; ring)
    rw [hd]
    refine ofIntZpow_mem_unbounded _ (fun {e'} he' => ?_) (fun {p} hp => ?_)
    · cases hexp : F.exp using QExp.recBotCoe with
      | bot => rw [shrink_exp_bot h hexp] at he'; exact absurd he' WithBot.bot_ne_coe
      | coe e₀ =>
        rw [shrink_exp_coe h hexp] at he'
        rw [hexp] at he
        have h1 := WithBot.coe_inj.mp he'
        have h2 := WithBot.coe_le_coe.mp he
        omega
    · change F.p - 1 = _ at hp
      cases hF : F.p using ENat.recTopCoe with
      | top => rw [hF] at hp; exact absurd hp (ENat.top_ne_coe p)
      | coe n =>
        rw [hF] at hp
        have h1 : n ≠ 1 := fun h1 => h (by rw [hF, h1])
        have hn : n = p + 1 := by
          have : n - 1 = p := by exact_mod_cast hp
          have := F.p_pos hF
          omega
        have := hk n hF
        rw [hn, pow_succ, ← two_mul, abs_mul, abs_two] at this
        linarith

/-- At precision `1`, `±2^j` above the quantum is its own canonical step. -/
theorem canonicalExp_ofIntZpow_of_p_one {F : FiniteFormat} (hp : F.p = ((1 : ℕ) : Prec))
    {e₀ : ℤ} (he : F.exp = (e₀ : QExp)) {k j : ℤ} (hk : |k| = 1) (hj : e₀ ≤ j) :
    F.canonicalExp (Dyadic.ofIntZpow k j) = j := by
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  have hk1 : |(k : ℝ)| = 1 := by exact_mod_cast hk
  rw [canonicalExp_expFinite hp he (Dyadic.coe_ofIntZpow_ne_zero hk0 j), Dyadic.coe_ofIntZpow,
    log_abs_mul_zpow hk0, hk1, Int.log_one_right]
  push_cast; omega

end FiniteFormat

namespace ParityFormat

/-- At precision `1`, `±2^j` is odd when `j` has even index above `exp`. -/
theorem isOdd_ofIntZpow_of_p_one (F : ParityFormat) (hp : F.p = ((1 : ℕ) : Prec))
    {e₀ : ℤ} (he : F.exp = (e₀ : QExp)) {k j : ℤ} (hk : |k| = 1) (hj : e₀ ≤ j) :
    F.IsOdd (Dyadic.ofIntZpow k j) ↔ Even (j - e₀) := by
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  simp only [isOdd_iff_canonical, if_pos hp]
  rw [FiniteFormat.canonicalExp_ofIntZpow_of_p_one hp he hk hj, he, WithBot.unbotD_coe,
    ← Int.not_even_iff_odd, Int.even_add_one, not_not]
  exact ⟨fun ⟨_, _, _, h⟩ => h,
    fun h => ⟨Dyadic.coe_ofIntZpow_ne_zero hk0 j, k, Dyadic.coe_ofIntZpow k j, h⟩⟩

/-- At precision `1`, `±2^j` is even when `j` has odd index above `exp`. -/
theorem isEven_ofIntZpow_of_p_one (F : ParityFormat) (hp : F.p = ((1 : ℕ) : Prec))
    {e₀ : ℤ} (he : F.exp = (e₀ : QExp)) {k j : ℤ} (hk : |k| = 1) (hj : e₀ ≤ j) :
    F.IsEven (Dyadic.ofIntZpow k j) ↔ Odd (j - e₀) := by
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  have hd0 := Dyadic.coe_ofIntZpow_ne_zero hk0 j
  simp only [isEven_iff_canonical, if_pos hp]
  rw [FiniteFormat.canonicalExp_ofIntZpow_of_p_one hp he hk hj, he, WithBot.unbotD_coe,
    Int.even_add_one, Int.not_even_iff_odd]
  refine ⟨?_, fun h => Or.inr ⟨hd0, k, Dyadic.coe_ofIntZpow k j, h⟩⟩
  rintro (h0 | ⟨_, _, _, h⟩)
  · exact absurd (by rw [h0, Dyadic.coe_real_zero]) hd0
  · exact h

/-! ### Containment -/

/-- `2 ≤ p` rules out `p = 1`. -/
theorem p_ne_one_of_two_le {F : FiniteFormat} (hp : ((2 : ℕ) : Prec) ≤ F.p) :
    F.p ≠ ((1 : ℕ) : Prec) := fun h1 => by
  rw [h1] at hp; exact absurd (by exact_mod_cast hp : (2 : ℕ) ≤ 1) (by norm_num)

/-- **Values of a subformat's shrink are even.** If `y ∈ G ⊆ F` with
`F.p ≥ 2` and `y` in `G`'s shrink, then `y` is even in `F`. -/
theorem isEven_of_subset {G : Format} {F : ParityFormat} (hsub : G ⊆ F.toFormat)
    (hp : ((2 : ℕ) : Prec) ≤ F.p) {y : Dyadic} (hyG : y ∈ G)
    (hyC : y ∈ G.shrink.unbounded) : F.IsEven y := by
  by_cases hy0 : y = 0
  · rw [hy0]; exact isEven_zero F
  -- Bound `G` by `|y|`, a value of `G`, so the completeness of containment applies.
  let b : NonNegDyadic := ⟨Dyadic.abs y, by rw [Dyadic.coe_rat_abs]; exact abs_nonneg _⟩
  have hb : ((b.val : Dyadic) : ℝ) = |(y : ℝ)| := Dyadic.coe_abs y
  have habs : Dyadic.abs y ∈ G.unbounded := by
    unfold Dyadic.abs
    split_ifs
    · exact ⟨hyG.1, hyG.2.1, trivial⟩
    · exact Format.neg_mem ⟨hyG.1, hyG.2.1, trivial⟩
  have hsub' : G.withBound (b : Bound) ⊆ F.toFormat :=
    (Format.subset_of_mem (F₁ := G.withBound (b : Bound)) (F₂ := G) subset_rfl
    fun v hv => ⟨hv.1, hv.2.1, boundOK_of_abs_le
      ((abs_coe_real_le_of_boundOK hv.2.2).trans hb.le) hyG.2.2⟩).trans hsub
  have hyb : Format.boundOK (b : Bound) y := boundOK_coe_of_abs_le hb.ge
  refine (isEven_iff_mem_shrink F (p_ne_one_of_two_le hp) y).mpr
    (Format.mem_shrink_of_subset hsub' ?_ ⟨y, ⟨hyG.1, hyG.2.1, hyb⟩, hy0⟩ hp
      ⟨hyC.1, hyC.2.1, hyb⟩)
  intro bv hbv
  rw [Format.withBound_b, WithTop.coe_inj] at hbv
  rw [← hbv]
  exact habs

/-- **Precision-`1` values odd in a wider format sit at the quantum.** If
`y ∈ F₁ ⊆ F₂` with `F₁.p = 1`, `F₂.p ≥ 2` and `y` odd in `F₂`, then `y`'s
exponent is `F₁.exp`: any higher power of two is even in `F₂`. -/
theorem exp_eq_canonicalExp_of_p_one {F₁ : FiniteFormat} {F₂ : ParityFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat) (hp : ((2 : ℕ) : Prec) ≤ F₂.p)
    (hp₁ : F₁.p = ((1 : ℕ) : Prec)) {y : Dyadic} (hy : y ∈ F₁) (hodd : F₂.IsOdd y) :
    F₁.exp = ((F₁.canonicalExp y : ℤ) : QExp) := by
  have hy0 : (y : ℝ) ≠ 0 := fun h => hodd.ne_zero (eq_zero_of_coe_real_zero h)
  obtain ⟨c, hc⟩ := F₁.exists_mul_zpow_canonicalExp (mem_unbounded_of_mem hy)
  set j := F₁.canonicalExp y
  -- The significand of a precision-`1` value is `±1`.
  have hc1 : |c| = 1 := by
    have h := floor_mantissa_lt (F := F₁) (x := y) hp₁
    change |(y : ℝ) * 2 ^ (-j)| < 2 ^ 1 at h
    rw [hc, mul_assoc, ← zpow_add₀ two_ne_zero, add_neg_cancel, zpow_zero, mul_one] at h
    have : |c| < 2 := by exact_mod_cast (show |(c : ℝ)| < 2 by simpa using h)
    have : c ≠ 0 := by rintro rfl; exact hy0 (by rw [hc]; simp)
    have := Int.one_le_abs this
    omega
  have hyc : y = Dyadic.ofIntZpow c j := Dyadic.ext_real (by rw [Dyadic.coe_ofIntZpow]; exact hc)
  have h₂₁ := Format.exp_le_of_subset ⟨y, hy, hodd.ne_zero⟩ hsub
  have h₁j := exp_le_canonicalExp_coe F₁ (y : ℝ)
  by_contra hne
  -- Otherwise `y = ±2^j` with `j` above `F₂`'s quantum lies in `F₂`'s shrink.
  have hC : y ∈ (F₂.shrink (p_ne_one_of_two_le hp)).unbounded := by
    rw [hyc]
    refine ofIntZpow_mem_unbounded _ (fun {e'} he' => ?_) (fun {q} hq => ?_)
    · cases he₂ : F₂.exp using QExp.recBotCoe with
      | bot => rw [FiniteFormat.shrink_exp_bot _ he₂] at he'; exact absurd he' WithBot.bot_ne_coe
      | coe e₂ =>
        rw [FiniteFormat.shrink_exp_coe _ he₂, WithBot.coe_inj] at he'
        cases he₁ : F₁.exp using QExp.recBotCoe with
        | bot => rw [he₁, he₂] at h₂₁; exact absurd h₂₁ (by simp)
        | coe e₁ =>
          rw [he₁, he₂, WithBot.coe_le_coe] at h₂₁
          rw [he₁, WithBot.coe_le_coe] at h₁j
          rw [he₁, WithBot.coe_inj] at hne
          omega
    · rw [hc1]; exact one_le_pow₀ (by norm_num)
  exact not_isEven_and_isOdd ((isEven_iff_mem_shrink F₂ _ y).mpr hC) hodd

end ParityFormat

open ParityFormat in
/-- **RTO-padding lemma.** If `F₁ ⊆ F₂`, `F₂.p ≥ 2`, and `y ∈ F₁` is odd in `F₂`,
then `y` is odd in `F₁`: were it even, it would be in `F₁`'s shrink, hence
even in `F₂`. -/
theorem IsOdd.transfer_of_subset {F₁ F₂ : ParityFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {y : Dyadic} (hyF₁ : y ∈ F₁.toFiniteFormat) (hodd : F₂.IsOdd y) :
    F₁.IsOdd y := by
  by_cases hp₁ : F₁.p = ((1 : ℕ) : Prec)
  · have he := exp_eq_canonicalExp_of_p_one hsub hp_F₂ hp₁ hyF₁ hodd
    obtain ⟨c, hc⟩ := F₁.exists_mul_zpow_canonicalExp (mem_unbounded_of_mem hyF₁)
    refine (isOdd_iff_canonical F₁ y).mpr
      ⟨fun h => hodd.ne_zero (eq_zero_of_coe_real_zero h), c, hc, ?_⟩
    rw [if_pos hp₁, he, WithBot.unbotD_coe, sub_self, zero_add]
    exact odd_one
  · rw [isOdd_iff_mem_shrink F₁ hp₁]
    exact ⟨mem_unbounded_of_mem hyF₁,
      fun hC => not_isEven_and_isOdd (isEven_of_subset hsub hp_F₂ hyF₁ hC) hodd⟩

end Mpfx
