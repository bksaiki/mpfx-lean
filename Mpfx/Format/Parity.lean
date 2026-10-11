import Mpfx.Format.Defs

/-!
# Parity formats

`ParityFormat`, the `IsOdd` / `IsEven` classification of its elements,
basic parity facts (negation, canonical-representation characterizations),
and transport across formats with equal `toFormat` or `(p, exp)` (`congr`).
Alternation between adjacent values is in `Format/Parity/Alternate.lean`.
-/

namespace Mpfx

/-- A `FiniteFormat` where parity is well-defined: `p ≠ 1` whenever
`exp = ⊥`. Combined with `FiniteFormat.finite`, this is
`(p ≠ ⊤ ∧ p ≠ 1) ∨ exp ≠ ⊥`. Required for `IsOdd` / `IsEven`. -/
structure ParityFormat extends FiniteFormat where
  parity : toFormat.p ≠ 1 ∨ toFormat.exp ≠ ⊥

namespace ParityFormat

/-- Conjunction of `FiniteFormat.finite` and `ParityFormat.parity`. -/
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
  obtain ⟨c, e, hrep, _⟩ := h
  exact fun hy0 => hrep.ne_zero (by simp [hy0])

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

end Mpfx
