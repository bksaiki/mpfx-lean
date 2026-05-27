import Mpfx.Rounding
import Mpfx.Grid
import Mpfx.Digits

/-!
# Counterexamples to invalid double-rounding pairings — shared infrastructure

This file ports the *shared gadget format* `F₁_g` and its support lemmas
from `Mpfx/DoubleRoundingCex.lean` to the `Mpfx` substrate. The actual
counterexample theorems (`no_rndRNE_RNE`, etc.) are built on top of this
infrastructure in later development.

`F₁_g p e = 𝒜(p, e, ⊤)` (with `p ≥ 2`) is the witness format used by all
§5.2 counterexamples. Witnesses on its grid:

* `y_lo_g = 3·2^e` (odd in F₁ at numDigits 2),
* `y_hi_g = 4·2^e = 2^(e+2)` (even in F₁),
* `two_e_g = 2^e` (smallest positive F₁-element witness),
* `m_g = 7·2^(e-1)` (midpoint of the F₁-adjacent pair `(y_lo, y_hi)`),
* `y_lo_low_g = 2·2^e` (even lower neighbor),
* `m_low_g = 5·2^(e-1)` (midpoint of `(y_lo_low, y_lo)`).

## Substrate notes

* `F₁_g` is a `ParityFormat` (Mpfx's parity tier), constructed with bound
  `⊤ : WithTop NonNegDyadic`.
* Precision/quantum predicates are `ℚ`-valued in Mpfx; membership proofs
  go through `precisionAtMost_coe` / `quantumAtLeast_coe`, but witness
  equations are stated over `ℝ` via `Dyadic.coe_ofIntZpow`, so we bridge
  with the `*_coe_real` companions or by casting.
* The RNE inner-step lemmas conclude `RoundsFinite … (.nearest .toEven) …`
  with the tie clause discharged using `F₁_g` itself as the even witness.
-/

namespace Mpfx

namespace ParityFormat

/-! ## The gadget format `F₁_g = 𝒜(p, e, ⊤)` -/

/-- The witness format `𝒜(p, e, ⊤)` with precision `p ≥ 2`, quantum `2^e`,
unbounded magnitude. Built as a `ParityFormat`: both the `finite` and
`parity` invariants hold because `exp = (e : ℤ) ≠ ⊥`. -/
def F₁_g (p : ℕ+) (_hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ) : ParityFormat where
  toFiniteFormat :=
    { toFormat := { p := ((p : ℕ+) : WithTop ℕ+), exp := (e : WithBot ℤ), b := ⊤ }
      finite := Or.inr WithBot.coe_ne_bot }
  parity := Or.inr WithBot.coe_ne_bot

@[simp] theorem F₁_g_p (p : ℕ+) (hp : 2 ≤ (p : ℕ)) (e : ℤ) :
    (F₁_g p hp e).toFormat.p = ((p : ℕ+) : WithTop ℕ+) := rfl

@[simp] theorem F₁_g_exp (p : ℕ+) (hp : 2 ≤ (p : ℕ)) (e : ℤ) :
    (F₁_g p hp e).toFormat.exp = (e : WithBot ℤ) := rfl

@[simp] theorem F₁_g_b (p : ℕ+) (hp : 2 ≤ (p : ℕ)) (e : ℤ) :
    (F₁_g p hp e).toFormat.b = ⊤ := rfl

/-! ### The grid witnesses (as `Dyadic.ofIntZpow`) -/

noncomputable def y_lo_g (e : ℤ) : Dyadic := Dyadic.ofIntZpow 3 e
noncomputable def y_hi_g (e : ℤ) : Dyadic := Dyadic.ofIntZpow 1 (e + 2)

/-- `2^e` as a Dyadic, used as the smallest positive F₁_g-element witness. -/
noncomputable def two_e_g (e : ℤ) : Dyadic := Dyadic.ofIntZpow 1 e

noncomputable def m_g (e : ℤ) : Dyadic := Dyadic.ofIntZpow 7 (e - 1)

noncomputable def y_lo_low_g (e : ℤ) : Dyadic := Dyadic.ofIntZpow 2 e

noncomputable def m_low_g (e : ℤ) : Dyadic := Dyadic.ofIntZpow 5 (e - 1)

theorem coe_y_lo_g (e : ℤ) : ((y_lo_g e : Dyadic) : ℝ) = 3 * (2 : ℝ)^e := by
  change ((Dyadic.ofIntZpow 3 e : Dyadic) : ℝ) = _
  rw [Dyadic.coe_ofIntZpow]; push_cast; ring

theorem coe_y_hi_g (e : ℤ) :
    ((y_hi_g e : Dyadic) : ℝ) = (2 : ℝ)^(e + 2) := by
  change ((Dyadic.ofIntZpow 1 (e + 2) : Dyadic) : ℝ) = _
  rw [Dyadic.coe_ofIntZpow]; push_cast; ring

theorem coe_two_e_g (e : ℤ) : ((two_e_g e : Dyadic) : ℝ) = (2 : ℝ)^e := by
  change ((Dyadic.ofIntZpow 1 e : Dyadic) : ℝ) = _
  rw [Dyadic.coe_ofIntZpow]; push_cast; ring

theorem coe_m_g (e : ℤ) : ((m_g e : Dyadic) : ℝ) = 7 * (2 : ℝ)^(e - 1) := by
  change ((Dyadic.ofIntZpow 7 (e - 1) : Dyadic) : ℝ) = _
  rw [Dyadic.coe_ofIntZpow]; push_cast; ring

theorem coe_y_lo_low_g (e : ℤ) :
    ((y_lo_low_g e : Dyadic) : ℝ) = 2 * (2 : ℝ)^e := by
  change ((Dyadic.ofIntZpow 2 e : Dyadic) : ℝ) = _
  rw [Dyadic.coe_ofIntZpow]; push_cast; ring

theorem coe_m_low_g (e : ℤ) :
    ((m_low_g e : Dyadic) : ℝ) = 5 * (2 : ℝ)^(e - 1) := by
  change ((Dyadic.ofIntZpow 5 (e - 1) : Dyadic) : ℝ) = _
  rw [Dyadic.coe_ofIntZpow]; push_cast; ring

/-! ### Membership lemmas -/

theorem y_lo_mem_F₁_g (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ) :
    y_lo_g e ∈ (F₁_g p hp_ge_2 e).toFormat := by
  refine ⟨?_, ?_, trivial⟩
  · -- precisionAtMost p: take (c=3, k=e). |3| < 2^p since p ≥ 2.
    change Dyadic.precisionAtMost ((p : ℕ+) : WithTop ℕ+) (y_lo_g e)
    rw [Dyadic.precisionAtMost_coe_real]
    refine ⟨3, e, ?_, ?_⟩
    · rw [coe_y_lo_g]; push_cast; ring
    · have h_pow : (4 : ℤ) ≤ (2 : ℤ)^(p : ℕ) :=
        calc (4 : ℤ) = (2 : ℤ)^2 := by norm_num
          _ ≤ (2 : ℤ)^(p : ℕ) := pow_le_pow_right₀ (by norm_num) hp_ge_2
      have h_abs : |(3 : ℤ)| = 3 := by decide
      omega
  · change Dyadic.quantumAtLeast ((e : ℤ) : WithBot ℤ) (y_lo_g e)
    rw [Dyadic.quantumAtLeast_coe_real]
    refine ⟨3, ?_⟩
    rw [coe_y_lo_g]; push_cast; ring

theorem two_e_mem_F₁_g (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ) :
    two_e_g e ∈ (F₁_g p hp_ge_2 e).toFormat := by
  refine ⟨?_, ?_, trivial⟩
  · change Dyadic.precisionAtMost ((p : ℕ+) : WithTop ℕ+) (two_e_g e)
    rw [Dyadic.precisionAtMost_coe_real]
    refine ⟨1, e, ?_, ?_⟩
    · rw [coe_two_e_g]; push_cast; ring
    · have h_pow : (2 : ℤ) ≤ (2 : ℤ)^(p : ℕ) :=
        calc (2 : ℤ) = (2 : ℤ)^1 := by norm_num
          _ ≤ (2 : ℤ)^(p : ℕ) := pow_le_pow_right₀ (by norm_num) (by omega)
      have : |(1 : ℤ)| = 1 := by decide
      omega
  · change Dyadic.quantumAtLeast ((e : ℤ) : WithBot ℤ) (two_e_g e)
    rw [Dyadic.quantumAtLeast_coe_real]
    exact ⟨1, by rw [coe_two_e_g]; push_cast; ring⟩

theorem y_hi_mem_F₁_g (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ) :
    y_hi_g e ∈ (F₁_g p hp_ge_2 e).toFormat := by
  refine ⟨?_, ?_, trivial⟩
  · change Dyadic.precisionAtMost ((p : ℕ+) : WithTop ℕ+) (y_hi_g e)
    rw [Dyadic.precisionAtMost_coe_real]
    refine ⟨1, e + 2, ?_, ?_⟩
    · rw [coe_y_hi_g]; push_cast; ring
    · have h_pow : (2 : ℤ) ≤ (2 : ℤ)^(p : ℕ) :=
        calc (2 : ℤ) = (2 : ℤ)^1 := by norm_num
          _ ≤ (2 : ℤ)^(p : ℕ) := pow_le_pow_right₀ (by norm_num) (by omega : 1 ≤ (p : ℕ))
      have h_abs : |(1 : ℤ)| = 1 := by decide
      omega
  · change Dyadic.quantumAtLeast ((e : ℤ) : WithBot ℤ) (y_hi_g e)
    rw [Dyadic.quantumAtLeast_coe_real]
    refine ⟨4, ?_⟩
    rw [coe_y_hi_g, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have : (2 : ℝ)^(2 : ℤ) = 4 := by norm_num
    rw [this]; push_cast; ring

theorem y_lo_low_mem_F₁_g (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ) :
    y_lo_low_g e ∈ (F₁_g p hp_ge_2 e).toFormat := by
  refine ⟨?_, ?_, trivial⟩
  · change Dyadic.precisionAtMost ((p : ℕ+) : WithTop ℕ+) (y_lo_low_g e)
    rw [Dyadic.precisionAtMost_coe_real]
    refine ⟨2, e, ?_, ?_⟩
    · rw [coe_y_lo_low_g]; push_cast; ring
    · have h_pow : (4 : ℤ) ≤ (2 : ℤ)^(p : ℕ) :=
        calc (4 : ℤ) = (2 : ℤ)^2 := by norm_num
          _ ≤ (2 : ℤ)^(p : ℕ) := pow_le_pow_right₀ (by norm_num) hp_ge_2
      have h_abs : |(2 : ℤ)| = 2 := by decide
      omega
  · change Dyadic.quantumAtLeast ((e : ℤ) : WithBot ℤ) (y_lo_low_g e)
    rw [Dyadic.quantumAtLeast_coe_real]
    refine ⟨2, ?_⟩
    rw [coe_y_lo_low_g]; push_cast; ring

/-- Quantum extraction: every `z ∈ F₁_g` is `c · 2^e` for some `c : ℤ`. -/
theorem F₁_g_quantum (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    {z : Dyadic} (hz : z ∈ (F₁_g p hp_ge_2 e).toFormat) :
    ∃ c : ℤ, (z : ℝ) = (c : ℝ) * (2 : ℝ)^e := by
  have hq : Dyadic.quantumAtLeast ((e : ℤ) : WithBot ℤ) z := hz.2.1
  rw [Dyadic.quantumAtLeast_coe_real] at hq
  exact hq

/-! ## Containment → exponent helpers -/

/-- From `F₁_g ⊆ F₂` and `F₂.exp = (f₂ : WithBot ℤ)`, we have `f₂ ≤ e`. -/
theorem f₂_le_e_of_F₁_g_subset (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    (F₂ : Format) (hsub : (F₁_g p hp_ge_2 e).toFormat ⊆ F₂)
    {f₂ : ℤ} (hF₂_exp : F₂.exp = (f₂ : WithBot ℤ)) :
    f₂ ≤ e := by
  have h_two_e_in_F₂ : two_e_g e ∈ F₂ := hsub _ (two_e_mem_F₁_g p hp_ge_2 e)
  have hq : Dyadic.quantumAtLeast F₂.exp (two_e_g e) := h_two_e_in_F₂.2.1
  rw [hF₂_exp, Dyadic.quantumAtLeast_coe_real] at hq
  obtain ⟨c, hc⟩ := hq
  rw [coe_two_e_g] at hc
  by_contra h_gt; push Not at h_gt
  have h_2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
  have h_split : (2 : ℝ)^e = (2 : ℝ)^(e - f₂) * (2 : ℝ)^f₂ := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
  rw [h_split] at hc
  have hc_real : (c : ℝ) = (2 : ℝ)^(e - f₂) :=
    (mul_right_cancel₀ (ne_of_gt h_2f_pos) hc).symm
  have h_lt_1 : (c : ℝ) < 1 := by
    rw [hc_real]
    have h_diff_neg : e - f₂ < 0 := by omega
    have : (2 : ℝ)^(e - f₂) < (2 : ℝ)^(0 : ℤ) :=
      zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) h_diff_neg
    simpa using this
  have h_pos : 0 < (c : ℝ) := by rw [hc_real]; exact zpow_pos (by norm_num) _
  have hc_int_pos : 0 < c := by exact_mod_cast h_pos
  have hc_int_lt : c < 1 := by exact_mod_cast h_lt_1
  omega

/-- If an F₂-element `y` equals `odd_c · 2^(e−1)` with `odd_c` odd, then
`F₂`'s quantum exponent `f₂` satisfies `f₂ ≤ e − 1`. -/
theorem f₂_le_e_sub_one_of_odd_in_F₂
    {F₂ : Format} {f₂ e : ℤ}
    (hF₂_exp : F₂.exp = (f₂ : WithBot ℤ))
    {y : Dyadic} (hy_in_F₂ : y ∈ F₂)
    {odd_c : ℤ} (h_odd : Odd odd_c)
    (h_y_eq : ((y : Dyadic) : ℝ) = (odd_c : ℝ) * (2 : ℝ) ^ (e - 1)) :
    f₂ ≤ e - 1 := by
  obtain ⟨_, hq, _⟩ := hy_in_F₂
  rw [hF₂_exp, Dyadic.quantumAtLeast_coe_real] at hq
  obtain ⟨c, hc⟩ := hq
  by_contra h_gt
  push Not at h_gt
  rw [h_y_eq] at hc
  set k : ℕ := (f₂ - (e - 1)).toNat with hk_def
  have h_kn : (k : ℤ) = f₂ - (e - 1) := Int.toNat_of_nonneg (by omega)
  have h_k_pos : 1 ≤ k := by
    have : (1 : ℤ) ≤ (k : ℤ) := by rw [h_kn]; omega
    exact_mod_cast this
  have h_2e1_ne : (2 : ℝ)^(e - 1) ≠ 0 := ne_of_gt (zpow_pos (by norm_num) _)
  have h_split : (2 : ℝ)^f₂ = (2 : ℝ)^(k : ℤ) * (2 : ℝ)^(e - 1) := by
    rw [show (f₂ : ℤ) = (k : ℤ) + (e - 1) from by linarith [h_kn],
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  rw [h_split, ← mul_assoc, zpow_natCast] at hc
  have h_eq : (odd_c : ℝ) = (c : ℝ) * (2 : ℝ)^k :=
    mul_right_cancel₀ h_2e1_ne hc
  have h_int : odd_c = c * (2 : ℤ)^k := by
    have h1 : ((odd_c : ℤ) : ℝ) = ((c * (2 : ℤ)^k : ℤ) : ℝ) := by
      push_cast; exact h_eq
    exact_mod_cast h1
  have h_even : Even odd_c := by
    rw [h_int, show k = (k - 1) + 1 from by omega, pow_succ]
    refine ⟨c * 2^(k - 1), ?_⟩; ring
  exact (Int.not_even_iff_odd.mpr h_odd) h_even

/-! ## Arithmetic helpers -/

/-- `(2:ℝ)^(e - f) = ((2:ℤ)^n : ℝ)` where `n = (e - f).toNat`, when `f ≤ e`. -/
theorem two_zpow_diff_eq (e f : ℤ) (h : f ≤ e) :
    (2 : ℝ)^(e - f) = ((2 : ℤ)^(e - f).toNat : ℝ) := by
  have hn_eq : ((e - f).toNat : ℤ) = e - f := Int.toNat_of_nonneg (by omega)
  rw [show (2 : ℝ)^(e - f) = (2 : ℝ)^(((e - f).toNat : ℤ) : ℤ) by rw [hn_eq],
      zpow_natCast]
  push_cast; ring

/-- `(2:ℝ)^e = ((2:ℤ)^n : ℝ) * (2:ℝ)^f` where `n = (e - f).toNat`, when `f ≤ e`. -/
theorem two_zpow_split (e f : ℤ) (h : f ≤ e) :
    (2 : ℝ)^e = ((2 : ℤ)^(e - f).toNat : ℝ) * (2 : ℝ)^f := by
  have h_split : (2 : ℝ)^e = (2 : ℝ)^(e - f) * (2 : ℝ)^f := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
  rw [h_split, two_zpow_diff_eq e f h]

/-- If `z·x ≥ 0` and `0 < x`, then `0 ≤ z`. -/
theorem nonneg_of_mul_nonneg_pos {z x : ℝ} (h_sign : z * x ≥ 0) (hx : 0 < x) :
    0 ≤ z := by
  rcases le_or_gt 0 z with h | h
  · exact h
  · exfalso; nlinarith

/-- `2^f = 4 · 2^(f − 2)`. -/
theorem two_zpow_split_minus_two (f : ℤ) :
    (2 : ℝ)^f = 4 * (2 : ℝ)^(f - 2) := by
  have h_eq : (2 : ℝ)^f = (2 : ℝ)^(f - 2) * (2 : ℝ)^(2 : ℤ) := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
  rw [h_eq, show (2 : ℝ)^(2 : ℤ) = 4 by norm_num]; ring

/-- **F₂-grid floor.** Given `target = c_target · 2^f₂` on F₂'s grid, any
`z ∈ F₂` strictly below `target + 2^f₂` is at most `target`. -/
theorem F₂_grid_floor
    {F₂ : Format} {f₂ : ℤ} (hF₂_exp : F₂.exp = (f₂ : WithBot ℤ))
    {target : ℝ} {c_target : ℤ}
    (h_target_eq : target = (c_target : ℝ) * (2 : ℝ) ^ f₂) :
    ∀ z ∈ F₂, ((z : Dyadic) : ℝ) < target + (2 : ℝ)^f₂ →
      ((z : Dyadic) : ℝ) ≤ target := by
  intro z hz hz_lt
  obtain ⟨_, hq, _⟩ := hz
  rw [hF₂_exp, Dyadic.quantumAtLeast_coe_real] at hq
  obtain ⟨c, hc⟩ := hq
  rw [hc] at hz_lt ⊢
  have h_2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
  rw [h_target_eq, show (c_target : ℝ) * (2 : ℝ)^f₂ + (2 : ℝ)^f₂
        = ((c_target + 1 : ℤ) : ℝ) * (2 : ℝ)^f₂ from by push_cast; ring] at hz_lt
  have hc_lt : (c : ℝ) < ((c_target + 1 : ℤ) : ℝ) :=
    lt_of_mul_lt_mul_right hz_lt h_2f_pos.le
  have hc_int_lt : c < c_target + 1 := by exact_mod_cast hc_lt
  have hc_int_le : c ≤ c_target := by omega
  have hc_real_le : (c : ℝ) ≤ (c_target : ℝ) := by exact_mod_cast hc_int_le
  have h_mul : (c : ℝ) * (2 : ℝ)^f₂ ≤ (c_target : ℝ) * (2 : ℝ)^f₂ :=
    mul_le_mul_of_nonneg_right hc_real_le h_2f_pos.le
  rw [h_target_eq]; exact h_mul

/-- RTO at an F-exact value is the identity (vacuous parity clause since
`x = y`). -/
theorem rounds_RTO_self {F : FiniteFormat} {y : Dyadic} (h : y ∈ F) :
    RoundsFinite F .toOdd ((y : Dyadic) : ℝ) y := by
  refine ⟨h, ?_, ?_⟩
  · left
    refine ⟨h, le_refl _, ?_⟩
    intro z _ hz_le; exact hz_le
  · intro h_ne; exfalso; exact h_ne rfl

/-! ## Parity lemmas -/

/-- `IsEven F₁ (4·2^e)` for any `p ≥ 2`. -/
theorem isEven_F₁_g_y_hi (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ) :
    (F₁_g p hp_ge_2 e).IsEven (y_hi_g e) := by
  have h_coe : ((y_hi_g e : Dyadic) : ℝ) = (2 : ℝ)^(e + 2) := coe_y_hi_g e
  have h_coe_rat : ((y_hi_g e : Dyadic) : ℚ) = (2 : ℚ)^(e + 2) := by
    change ((Dyadic.ofIntZpow 1 (e + 2) : Dyadic) : ℚ) = _
    rw [Dyadic.coe_rat_ofIntZpow]; push_cast; ring
  have h_2_pos : (0 : ℝ) < (2 : ℝ)^(e + 2) := zpow_pos (by norm_num) _
  have h_y_ne_real : ((y_hi_g e : Dyadic) : ℝ) ≠ 0 := by
    rw [h_coe]; exact ne_of_gt h_2_pos
  have h_log : Int.log 2 |((y_hi_g e : Dyadic) : ℝ)| = e + 2 := by
    rw [h_coe, abs_of_pos h_2_pos]
    rw [show (2 : ℝ)^(e + 2) = ((2 : ℕ) : ℝ)^(e + 2) by push_cast; rfl]
    exact Int.log_zpow (R := ℝ) (by omega : 1 < 2) (e + 2)
  -- Compute numDigits = min p 3.
  have h_nd : (F₁_g p hp_ge_2 e).toFiniteFormat.numDigits ((y_hi_g e : Dyadic) : ℝ)
        = min ((p : ℕ) : ℤ) 3 := by
    rw [(F₁_g p hp_ge_2 e).toFiniteFormat.numDigits_coe_coe h_y_ne_real
        (F₁_g_p p hp_ge_2 e) (F₁_g_exp p hp_ge_2 e), h_log]
    congr 1; ring
  have h_p_ne_1 : (F₁_g p hp_ge_2 e).toFormat.p ≠ ((1 : ℕ+) : WithTop ℕ+) := by
    rw [F₁_g_p]
    intro h
    have : ((p : ℕ+)) = (1 : ℕ+) := by exact_mod_cast h
    have : (p : ℕ) = 1 := by exact_mod_cast this
    omega
  right
  -- Case split on whether numDigits is 2 (p = 2) or 3 (p ≥ 3).
  rcases (lt_or_ge (p : ℕ) 3) with hp_lt | hp_ge
  · -- p = 2 (since 2 ≤ p < 3).
    have hp_eq : (p : ℕ) = 2 := by omega
    have h_nd_toNat : ((F₁_g p hp_ge_2 e).toFiniteFormat.numDigits
          ((y_hi_g e : Dyadic) : ℝ)).toNat = 2 := by
      rw [h_nd, hp_eq]; decide
    refine ⟨2, e + 1, ⟨?_, ?_, ?_⟩, ?_⟩
    · -- 4·2^e = 2·2^(e+1)
      rw [h_coe_rat, show (e + 2 : ℤ) = (e + 1) + 1 from by ring,
          zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
      have : (2 : ℚ)^(1 : ℤ) = 2 := by norm_num
      rw [this]; push_cast; ring
    · rw [h_nd_toNat]; decide
    · rw [h_nd_toNat]; decide
    · rw [if_neg h_p_ne_1]; decide
  · -- p ≥ 3.
    have h_nd_toNat : ((F₁_g p hp_ge_2 e).toFiniteFormat.numDigits
          ((y_hi_g e : Dyadic) : ℝ)).toNat = 3 := by
      rw [h_nd]
      have h_min : min ((p : ℕ) : ℤ) 3 = 3 := by
        have : ((p : ℕ) : ℤ) ≥ 3 := by exact_mod_cast hp_ge
        omega
      rw [h_min]; rfl
    refine ⟨4, e, ⟨?_, ?_, ?_⟩, ?_⟩
    · -- 4·2^e = 4·2^e
      rw [h_coe_rat, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
      have : (2 : ℚ)^(2 : ℤ) = 4 := by norm_num
      rw [this]; push_cast; ring
    · rw [h_nd_toNat]; decide
    · rw [h_nd_toNat]; decide
    · rw [if_neg h_p_ne_1]; decide

/-- `y_hi = 4·2^e` is not odd in `F₁_g`: its true precision is 1, below the
rounding precision `numDigits = min p 3 ≥ 2`. -/
theorem notIsOdd_F₁_g_y_hi (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ) :
    ¬ (F₁_g p hp_ge_2 e).IsOdd (y_hi_g e) := by
  have h_coe : ((y_hi_g e : Dyadic) : ℝ) = (2 : ℝ)^(e + 2) := coe_y_hi_g e
  have h_coe_rat : ((y_hi_g e : Dyadic) : ℚ) = (2 : ℚ)^(e + 2) := by
    change ((Dyadic.ofIntZpow 1 (e + 2) : Dyadic) : ℚ) = _
    rw [Dyadic.coe_rat_ofIntZpow]; push_cast; ring
  have h_2_pos : (0 : ℝ) < (2 : ℝ)^(e + 2) := zpow_pos (by norm_num) _
  have h_y_ne_real : ((y_hi_g e : Dyadic) : ℝ) ≠ 0 := by
    rw [h_coe]; exact ne_of_gt h_2_pos
  have h_log : Int.log 2 |((y_hi_g e : Dyadic) : ℝ)| = e + 2 := by
    rw [h_coe, abs_of_pos h_2_pos]
    rw [show (2 : ℝ)^(e + 2) = ((2 : ℕ) : ℝ)^(e + 2) by push_cast; rfl]
    exact Int.log_zpow (R := ℝ) (by omega : 1 < 2) (e + 2)
  have h_nd_eq : (F₁_g p hp_ge_2 e).toFiniteFormat.numDigits ((y_hi_g e : Dyadic) : ℝ)
        = min ((p : ℕ) : ℤ) 3 := by
    rw [(F₁_g p hp_ge_2 e).toFiniteFormat.numDigits_coe_coe h_y_ne_real
        (F₁_g_p p hp_ge_2 e) (F₁_g_exp p hp_ge_2 e), h_log]
    congr 1; ring
  have h_prec : Dyadic.precisionAtMost ((1 : ℕ+) : WithTop ℕ+) (y_hi_g e) := by
    rw [Dyadic.precisionAtMost_coe]
    refine ⟨1, e + 2, ?_, ?_⟩
    · rw [h_coe_rat]; push_cast; ring
    · decide
  have h_gt : ((1 : ℕ+) : ℤ) < (F₁_g p hp_ge_2 e).toFiniteFormat.numDigits
        ((y_hi_g e : Dyadic) : ℝ) := by
    rw [h_nd_eq]
    have : ((p : ℕ) : ℤ) ≥ 2 := by exact_mod_cast hp_ge_2
    have h1 : ((1 : ℕ+) : ℤ) = 1 := by decide
    rw [h1]; omega
  exact (F₁_g p hp_ge_2 e).precisionAtMost_not_IsOdd h_gt h_prec

/-- `IsEven F₁_g y_lo_low_g`: at numDigits = 2, canonical significand is `2`. -/
theorem isEven_F₁_g_y_lo_low (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ) :
    (F₁_g p hp_ge_2 e).IsEven (y_lo_low_g e) := by
  have h_coe : ((y_lo_low_g e : Dyadic) : ℝ) = 2 * (2 : ℝ)^e := coe_y_lo_low_g e
  have h_coe_rat : ((y_lo_low_g e : Dyadic) : ℚ) = 2 * (2 : ℚ)^e := by
    change ((Dyadic.ofIntZpow 2 e : Dyadic) : ℚ) = _
    rw [Dyadic.coe_rat_ofIntZpow]; push_cast; ring
  have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
  have h_y_pos : (0 : ℝ) < ((y_lo_low_g e : Dyadic) : ℝ) := by rw [h_coe]; nlinarith
  have h_y_ne_real : ((y_lo_low_g e : Dyadic) : ℝ) ≠ 0 := ne_of_gt h_y_pos
  have h_y_eq_2e1 : ((y_lo_low_g e : Dyadic) : ℝ) = (2 : ℝ)^(e + 1) := by
    rw [h_coe, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [show (2 : ℝ)^(1 : ℤ) = 2 by norm_num]; ring
  have h_log : Int.log 2 |((y_lo_low_g e : Dyadic) : ℝ)| = e + 1 := by
    rw [h_y_eq_2e1, abs_of_pos (by rw [← h_y_eq_2e1]; exact h_y_pos)]
    rw [show (2 : ℝ)^(e + 1) = ((2 : ℕ) : ℝ)^(e + 1) by push_cast; rfl]
    exact Int.log_zpow (R := ℝ) (by omega : 1 < 2) (e + 1)
  have h_nd_eq : (F₁_g p hp_ge_2 e).toFiniteFormat.numDigits
        ((y_lo_low_g e : Dyadic) : ℝ) = min ((p : ℕ) : ℤ) 2 := by
    rw [(F₁_g p hp_ge_2 e).toFiniteFormat.numDigits_coe_coe h_y_ne_real
        (F₁_g_p p hp_ge_2 e) (F₁_g_exp p hp_ge_2 e), h_log]
    congr 1; ring
  have h_nd_toNat : ((F₁_g p hp_ge_2 e).toFiniteFormat.numDigits
        ((y_lo_low_g e : Dyadic) : ℝ)).toNat = 2 := by
    rw [h_nd_eq]
    have hp_int : ((p : ℕ) : ℤ) ≥ 2 := by exact_mod_cast hp_ge_2
    have h_min : min ((p : ℕ) : ℤ) 2 = 2 := by omega
    rw [h_min]; rfl
  have h_p_ne_1 : (F₁_g p hp_ge_2 e).toFormat.p ≠ ((1 : ℕ+) : WithTop ℕ+) := by
    rw [F₁_g_p]
    intro h
    have h1 : ((p : ℕ+)) = (1 : ℕ+) := by exact_mod_cast h
    have h2 : (p : ℕ) = 1 := by exact_mod_cast h1
    omega
  right
  refine ⟨2, e, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [h_coe_rat]; push_cast; ring
  · rw [h_nd_toNat]; decide
  · rw [h_nd_toNat]; decide
  · rw [if_neg h_p_ne_1]; decide

/-! ## Faithful enumerations + RNE inner steps -/

/-- F₁-faithful values of `m_low = 5·2^(e-1)` enumerate to
`{y_lo_low, y_lo_g}` (= `{2·2^e, 3·2^e}`). -/
theorem F₁_faithful_m_low_eq_g (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    {z : Dyadic}
    (hf : IsFaithfulRound (F₁_g p hp_ge_2 e).toFiniteFormat ((m_low_g e : Dyadic) : ℝ) z) :
    (z : ℝ) = ((y_lo_low_g e : Dyadic) : ℝ) ∨ (z : ℝ) = ((y_lo_g e : Dyadic) : ℝ) := by
  have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
  have h_m_eq : ((m_low_g e : Dyadic) : ℝ) = (5 / 2) * (2 : ℝ)^e := by
    rw [coe_m_low_g, show (e - 1 : ℤ) = e + (-1 : ℤ) by ring,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [show (2 : ℝ)^(-1 : ℤ) = 1/2 by
      rw [show ((-1 : ℤ)) = -(1 : ℤ) by ring, zpow_neg]; norm_num]
    ring
  rcases hf with ⟨hzF, hle, hmax⟩ | ⟨hzF, hge, hmin⟩
  · left
    obtain ⟨c, hc⟩ := F₁_g_quantum p hp_ge_2 e hzF
    rw [hc, h_m_eq] at hle
    have hc_r_le : (c : ℝ) ≤ 5/2 := le_of_mul_le_mul_right hle h_2e_pos
    have hc_lt : (c : ℝ) < 3 := by linarith
    have hc_int_lt : c < 3 := by exact_mod_cast hc_lt
    have hc_int_le : c ≤ 2 := by omega
    have h_y_lo_low_le : ((y_lo_low_g e : Dyadic) : ℝ) ≤ ((m_low_g e : Dyadic) : ℝ) := by
      rw [coe_y_lo_low_g, h_m_eq]; nlinarith
    have h_ge_y_lo_low := hmax (y_lo_low_g e) (y_lo_low_mem_F₁_g p hp_ge_2 e) h_y_lo_low_le
    rw [coe_y_lo_low_g, hc] at h_ge_y_lo_low
    have hc_r_ge : (2 : ℝ) ≤ (c : ℝ) := le_of_mul_le_mul_right h_ge_y_lo_low h_2e_pos
    have hc_int_ge : 2 ≤ c := by exact_mod_cast hc_r_ge
    have hc_eq : c = 2 := by omega
    rw [hc, coe_y_lo_low_g, hc_eq]; push_cast; ring
  · right
    obtain ⟨c, hc⟩ := F₁_g_quantum p hp_ge_2 e hzF
    rw [hc, h_m_eq] at hge
    have hc_r_ge : (5/2 : ℝ) ≤ (c : ℝ) := le_of_mul_le_mul_right hge h_2e_pos
    have hc_gt : (2 : ℝ) < (c : ℝ) := by linarith
    have hc_int_gt : 2 < c := by exact_mod_cast hc_gt
    have hc_int_ge : 3 ≤ c := by omega
    have h_y_lo_ge : ((m_low_g e : Dyadic) : ℝ) ≤ ((y_lo_g e : Dyadic) : ℝ) := by
      rw [coe_y_lo_g, h_m_eq]; nlinarith
    have h_le_y_lo := hmin (y_lo_g e) (y_lo_mem_F₁_g p hp_ge_2 e) h_y_lo_ge
    rw [coe_y_lo_g, hc] at h_le_y_lo
    have hc_r_le : (c : ℝ) ≤ 3 := le_of_mul_le_mul_right h_le_y_lo h_2e_pos
    have hc_int_le : c ≤ 3 := by exact_mod_cast hc_r_le
    have hc_eq : c = 3 := by omega
    rw [hc, coe_y_lo_g, hc_eq]; push_cast; ring

/-- F₁_g-RNE at `m_low = 5·2^(e-1)` is `y_lo_low = 2·2^e` (the even lower
neighbor wins the tie). -/
theorem rounds_F₁_g_RNE_m_low_y_lo_low (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ) :
    RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat (.nearest .toEven)
      ((m_low_g e : Dyadic) : ℝ) (y_lo_low_g e) := by
  have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
  have h_m_eq : ((m_low_g e : Dyadic) : ℝ) = (5 / 2) * (2 : ℝ)^e := by
    rw [coe_m_low_g, show (e - 1 : ℤ) = e + (-1 : ℤ) by ring,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [show (2 : ℝ)^(-1 : ℤ) = 1/2 by
      rw [show ((-1 : ℤ)) = -(1 : ℤ) by ring, zpow_neg]; norm_num]
    ring
  have h_y_lo_low_eq : ((y_lo_low_g e : Dyadic) : ℝ) = 2 * (2 : ℝ)^e := coe_y_lo_low_g e
  refine ⟨y_lo_low_mem_F₁_g p hp_ge_2 e, ?_, ?_, ?_⟩
  · -- IsFaithfulRound (RoundDown y_lo_low).
    left
    refine ⟨y_lo_low_mem_F₁_g p hp_ge_2 e, ?_, ?_⟩
    · rw [h_m_eq, h_y_lo_low_eq]; nlinarith
    · intro z hz hle
      obtain ⟨c, hc⟩ := F₁_g_quantum p hp_ge_2 e hz
      rw [hc, h_m_eq] at hle
      rw [h_y_lo_low_eq, hc]
      have hc_r_le : (c : ℝ) ≤ 5/2 := le_of_mul_le_mul_right hle h_2e_pos
      have hc_lt : (c : ℝ) < 3 := by linarith
      have hc_int_lt : c < 3 := by exact_mod_cast hc_lt
      have hc_int_le : c ≤ 2 := by omega
      have : (c : ℝ) ≤ 2 := by exact_mod_cast hc_int_le
      nlinarith
  · -- Closeness: faithful z ∈ {y_lo_low, y_lo_g}, both equidistant.
    intro z hz hf
    rcases F₁_faithful_m_low_eq_g p hp_ge_2 e hf with hz_lo | hz_hi
    · rw [hz_lo]
    · rw [hz_hi, coe_y_lo_g, h_m_eq, h_y_lo_low_eq]
      have hL : |(5/2 : ℝ) * (2 : ℝ)^e - 2 * (2 : ℝ)^e| = (1/2) * (2 : ℝ)^e := by
        rw [show (5/2 : ℝ) * (2 : ℝ)^e - 2 * (2 : ℝ)^e
            = (1/2) * (2 : ℝ)^e by ring, abs_of_pos]
        nlinarith
      have hR : |(5/2 : ℝ) * (2 : ℝ)^e - 3 * (2 : ℝ)^e| = (1/2) * (2 : ℝ)^e := by
        rw [show (5/2 : ℝ) * (2 : ℝ)^e - 3 * (2 : ℝ)^e
            = -((1/2) * (2 : ℝ)^e) by ring, abs_neg, abs_of_pos]
        nlinarith
      rw [hL, hR]
  · rintro ⟨_, _, _, _, _⟩
    exact ⟨F₁_g p hp_ge_2 e, rfl, isEven_F₁_g_y_lo_low p hp_ge_2 e⟩

/-- F₁-faithful values of `m`: enumeration to `{y_lo, y_hi}`. -/
theorem F₁_faithful_m_eq_g (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    {z : Dyadic}
    (hf : IsFaithfulRound (F₁_g p hp_ge_2 e).toFiniteFormat ((m_g e : Dyadic) : ℝ) z) :
    (z : ℝ) = ((y_lo_g e : Dyadic) : ℝ) ∨ (z : ℝ) = ((y_hi_g e : Dyadic) : ℝ) := by
  have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
  have h_m_eq : ((m_g e : Dyadic) : ℝ) = (7 / 2) * (2 : ℝ)^e := by
    rw [coe_m_g, show (e - 1 : ℤ) = e + (-1 : ℤ) by ring,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have : (2 : ℝ)^(-1 : ℤ) = 1/2 := by
      rw [show ((-1 : ℤ)) = -(1 : ℤ) by ring, zpow_neg]; norm_num
    rw [this]; ring
  rcases hf with ⟨hzF, hle, hmax⟩ | ⟨hzF, hge, hmin⟩
  · -- RoundDown: z ≤ m.
    left
    obtain ⟨c, hc⟩ := F₁_g_quantum p hp_ge_2 e hzF
    rw [hc, h_m_eq] at hle
    have hc_r_le : (c : ℝ) ≤ 7/2 := le_of_mul_le_mul_right hle h_2e_pos
    have hc_lt : (c : ℝ) < 4 := by linarith
    have hc_int_lt : c < 4 := by exact_mod_cast hc_lt
    have hc_int_le : c ≤ 3 := by omega
    have h_y_lo_le : ((y_lo_g e : Dyadic) : ℝ) ≤ ((m_g e : Dyadic) : ℝ) := by
      rw [coe_y_lo_g, h_m_eq]
      have : (3 : ℝ) ≤ 7/2 := by norm_num
      nlinarith
    have h_ge_y_lo := hmax (y_lo_g e) (y_lo_mem_F₁_g p hp_ge_2 e) h_y_lo_le
    rw [coe_y_lo_g, hc] at h_ge_y_lo
    have hc_r_ge : (3 : ℝ) ≤ (c : ℝ) :=
      le_of_mul_le_mul_right h_ge_y_lo h_2e_pos
    have hc_int_ge : 3 ≤ c := by exact_mod_cast hc_r_ge
    have hc_eq : c = 3 := by omega
    rw [hc, coe_y_lo_g, hc_eq]; push_cast; ring
  · -- RoundUp: z ≥ m.
    right
    obtain ⟨c, hc⟩ := F₁_g_quantum p hp_ge_2 e hzF
    rw [hc, h_m_eq] at hge
    have hc_r_ge : (7 / 2 : ℝ) ≤ (c : ℝ) := le_of_mul_le_mul_right hge h_2e_pos
    have hc_gt : (3 : ℝ) < (c : ℝ) := by linarith
    have hc_int_gt : 3 < c := by exact_mod_cast hc_gt
    have hc_int_ge : 4 ≤ c := by omega
    have h_y_hi_ge : ((m_g e : Dyadic) : ℝ) ≤ ((y_hi_g e : Dyadic) : ℝ) := by
      rw [coe_y_hi_g, h_m_eq]
      have h_split : (2 : ℝ)^(e + 2) = 4 * (2 : ℝ)^e := by
        rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        have : (2 : ℝ)^(2 : ℤ) = 4 := by norm_num
        rw [this]; ring
      rw [h_split]
      have : (7/2 : ℝ) ≤ 4 := by norm_num
      nlinarith
    have h_le_y_hi := hmin (y_hi_g e) (y_hi_mem_F₁_g p hp_ge_2 e) h_y_hi_ge
    rw [coe_y_hi_g, hc] at h_le_y_hi
    have h_split : (2 : ℝ)^(e + 2) = 4 * (2 : ℝ)^e := by
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      have : (2 : ℝ)^(2 : ℤ) = 4 := by norm_num
      rw [this]; ring
    rw [h_split] at h_le_y_hi
    have hc_r_le : (c : ℝ) ≤ 4 := le_of_mul_le_mul_right h_le_y_hi h_2e_pos
    have hc_int_le : c ≤ 4 := by exact_mod_cast hc_r_le
    have hc_eq : c = 4 := by omega
    rw [hc, coe_y_hi_g, hc_eq, h_split]; push_cast; ring

/-- Inner step: `RoundsFinite F₁ RNE m y_hi` — at the F₁-midpoint `m`, RNE
breaks the tie between `y_lo = 3·2^e` and `y_hi = 4·2^e` toward the even
neighbor. -/
theorem rounds_F₁_g_RNE_m_y_hi (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ) :
    RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat (.nearest .toEven)
      ((m_g e : Dyadic) : ℝ) (y_hi_g e) := by
  have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
  have h_m_eq : ((m_g e : Dyadic) : ℝ) = (7 / 2) * (2 : ℝ)^e := by
    rw [coe_m_g, show (e - 1 : ℤ) = e + (-1 : ℤ) by ring,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have : (2 : ℝ)^(-1 : ℤ) = 1/2 := by
      rw [show ((-1 : ℤ)) = -(1 : ℤ) by ring, zpow_neg]; norm_num
    rw [this]; ring
  have h_y_hi_eq : ((y_hi_g e : Dyadic) : ℝ) = 4 * (2 : ℝ)^e := by
    rw [coe_y_hi_g, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have : (2 : ℝ)^(2 : ℤ) = 4 := by norm_num
    rw [this]; ring
  refine ⟨y_hi_mem_F₁_g p hp_ge_2 e, ?_, ?_, ?_⟩
  · right
    refine ⟨y_hi_mem_F₁_g p hp_ge_2 e, ?_, ?_⟩
    · rw [h_m_eq, h_y_hi_eq]; nlinarith
    · intro z hz hge
      obtain ⟨c, hc⟩ := F₁_g_quantum p hp_ge_2 e hz
      rw [hc, h_m_eq] at hge
      rw [h_y_hi_eq, hc]
      have hc_r_ge : (7/2 : ℝ) ≤ (c : ℝ) := le_of_mul_le_mul_right hge h_2e_pos
      have hc_r_3lt : (3 : ℝ) < (c : ℝ) := by linarith
      have hc_int_3lt : 3 < c := by exact_mod_cast hc_r_3lt
      have hc_int_ge : 4 ≤ c := by omega
      have hc_r_ge_4 : (4 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc_int_ge
      nlinarith
  · intro z hz hf
    rcases F₁_faithful_m_eq_g p hp_ge_2 e hf with hz_lo | hz_hi
    · rw [hz_lo, coe_y_lo_g, h_m_eq, h_y_hi_eq]
      have hL : |(7/2 : ℝ) * (2 : ℝ)^e - 4 * (2 : ℝ)^e| = (1/2) * (2 : ℝ)^e := by
        rw [show (7/2 : ℝ) * (2 : ℝ)^e - 4 * (2 : ℝ)^e
            = -((1/2) * (2 : ℝ)^e) by ring, abs_neg, abs_of_pos]
        nlinarith
      have hR : |(7/2 : ℝ) * (2 : ℝ)^e - 3 * (2 : ℝ)^e| = (1/2) * (2 : ℝ)^e := by
        rw [show (7/2 : ℝ) * (2 : ℝ)^e - 3 * (2 : ℝ)^e
            = (1/2) * (2 : ℝ)^e by ring, abs_of_pos]
        nlinarith
      rw [hL, hR]
    · rw [hz_hi]
  · rintro ⟨_, _, _, _, _⟩
    exact ⟨F₁_g p hp_ge_2 e, rfl, isEven_F₁_g_y_hi p hp_ge_2 e⟩

/-! ## Predecessor-extraction prerequisite -/

/-- For the midpoint `m = 7·2^(e-1)`, F₂'s grid representation `(c, k)` always
has `c ≥ 2` and `Int.log 2 c = Int.log 2 (c-1)`. Prerequisite for invoking
`prev_F_adjacent_of_log_eq`. -/
theorem m_g_grid_log_invariant {q₂ : ℕ} {f₂ : ℤ} {k c : ℤ} {e : ℤ}
    (hq₂ : 4 ≤ q₂) (hf₂_le : f₂ ≤ e - 2)
    (hk_max : k = max f₂ (Int.log 2 ((c : ℝ) * (2 : ℝ) ^ k) - (q₂ : ℤ) + 1))
    (hm_eq : (7 : ℝ) * (2 : ℝ) ^ (e - 1) = (c : ℝ) * (2 : ℝ) ^ k) :
    2 ≤ c ∧ Int.log 2 (((c - 1 : ℤ) : ℝ) * (2 : ℝ)^k) =
            Int.log 2 ((c : ℝ) * (2 : ℝ)^k) := by
  have h_2_pos : (0 : ℝ) < (2 : ℝ)^(e-1) := zpow_pos (by norm_num) _
  have hm_pos : (0 : ℝ) < (7 : ℝ) * (2 : ℝ)^(e - 1) := by nlinarith
  have h_log_m : Int.log 2 ((7 : ℝ) * (2 : ℝ)^(e - 1)) = e + 1 := by
    apply le_antisymm
    · have hle : (7 : ℝ) * (2 : ℝ)^(e-1) < ((2 : ℕ) : ℝ)^(e + 2) := by
        rw [show ((2 : ℕ) : ℝ) = 2 from by push_cast; rfl,
            show e + 2 = (e - 1) + 3 by ring,
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        have : (2 : ℝ)^(3 : ℤ) = 8 := by norm_num
        rw [this]; nlinarith
      have h_lt := (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) hm_pos).mp hle
      omega
    · have hge : ((2 : ℕ) : ℝ)^(e + 1) ≤ (7 : ℝ) * (2 : ℝ)^(e-1) := by
        rw [show ((2 : ℕ) : ℝ) = 2 from by push_cast; rfl,
            show e + 1 = (e - 1) + 2 by ring,
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        have : (2 : ℝ)^(2 : ℤ) = 4 := by norm_num
        rw [this]; nlinarith
      exact (Int.zpow_le_iff_le_log (by norm_num : 1 < (2 : ℕ)) hm_pos).mp hge
  have h_log_cxk : Int.log 2 ((c : ℝ) * (2 : ℝ)^k) = e + 1 := by
    rw [← hm_eq]; exact h_log_m
  rw [h_log_cxk] at hk_max
  have hk_eq : k = max f₂ (e + 2 - q₂) := by
    convert hk_max using 2; ring
  have hk_le : k ≤ e - 2 := by
    rw [hk_eq]
    have h1 : f₂ ≤ e - 2 := hf₂_le
    have h2 : e + 2 - (q₂ : ℤ) ≤ e - 2 := by
      have : (4 : ℤ) ≤ (q₂ : ℤ) := by exact_mod_cast hq₂
      omega
    exact max_le h1 h2
  have h_2k_pos : (0 : ℝ) < (2 : ℝ)^k := zpow_pos (by norm_num) _
  have hc_real : (c : ℝ) = 7 * (2 : ℝ)^(e - 1 - k) := by
    have h_split : (2 : ℝ)^(e - 1) = (2 : ℝ)^(e - 1 - k) * (2 : ℝ)^k := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
    have h1 : (7 : ℝ) * ((2 : ℝ)^(e - 1 - k) * (2 : ℝ)^k) = (c : ℝ) * (2 : ℝ)^k := by
      rw [← h_split]; exact hm_eq
    have h2 : (7 : ℝ) * (2 : ℝ)^(e - 1 - k) * (2 : ℝ)^k = (c : ℝ) * (2 : ℝ)^k := by
      rw [mul_assoc]; exact h1
    exact (mul_right_cancel₀ (ne_of_gt h_2k_pos) h2).symm
  have h_exp_ge : 1 ≤ e - 1 - k := by omega
  have hc_ge_14 : (14 : ℝ) ≤ (c : ℝ) := by
    rw [hc_real]
    have : (2 : ℝ)^(e - 1 - k) ≥ (2 : ℝ)^(1 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h_exp_ge
    nlinarith
  have hc_int_ge : 14 ≤ c := by exact_mod_cast hc_ge_14
  refine ⟨by omega, ?_⟩
  rw [h_log_cxk]
  apply le_antisymm
  · have h_c1_pos : 0 < c - 1 := by omega
    have h_c1_real_pos : (0 : ℝ) < ((c - 1 : ℤ) : ℝ) := by exact_mod_cast h_c1_pos
    have h_prod_pos : (0 : ℝ) < ((c - 1 : ℤ) : ℝ) * (2 : ℝ)^k :=
      mul_pos h_c1_real_pos h_2k_pos
    have h_c1_lt_c : ((c - 1 : ℤ) : ℝ) < (c : ℝ) := by push_cast; linarith
    have h_prod_lt_m : ((c - 1 : ℤ) : ℝ) * (2 : ℝ)^k < (c : ℝ) * (2 : ℝ)^k := by
      nlinarith
    have h_prod_lt_2 : ((c - 1 : ℤ) : ℝ) * (2 : ℝ)^k < ((2 : ℕ) : ℝ)^(e + 2) := by
      rw [show ((2 : ℕ) : ℝ) = 2 from by push_cast; rfl]
      have h_log_m_ub : (7 : ℝ) * (2 : ℝ)^(e - 1) < (2 : ℝ)^(e + 2) := by
        rw [show e + 2 = (e - 1) + 3 by ring,
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        have : (2 : ℝ)^(3 : ℤ) = 8 := by norm_num
        rw [this]; nlinarith
      have : (c : ℝ) * (2 : ℝ)^k < (2 : ℝ)^(e + 2) := by rw [← hm_eq]; exact h_log_m_ub
      linarith
    have h := (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) h_prod_pos).mp h_prod_lt_2
    omega
  · have h_c1_pos : 0 < c - 1 := by omega
    have h_prod_pos : (0 : ℝ) < ((c - 1 : ℤ) : ℝ) * (2 : ℝ)^k :=
      mul_pos (by exact_mod_cast h_c1_pos) h_2k_pos
    have h_prod_ge : ((2 : ℕ) : ℝ)^(e + 1) ≤ ((c - 1 : ℤ) : ℝ) * (2 : ℝ)^k := by
      rw [show ((2 : ℕ) : ℝ) = 2 from by push_cast; rfl,
          show e + 1 = (e - 1 - k) + k + 2 by ring,
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      have h22 : (2 : ℝ)^(2 : ℤ) = 4 := by norm_num
      rw [h22]
      have h_2e1k_pos : (0 : ℝ) < (2 : ℝ)^(e - 1 - k) := zpow_pos (by norm_num) _
      have hc_real_alt : (c : ℝ) = 7 * (2 : ℝ)^(e - 1 - k) := hc_real
      have h_c1_real : ((c - 1 : ℤ) : ℝ) = (c : ℝ) - 1 := by push_cast; ring
      rw [h_c1_real, hc_real_alt]
      have h_2e1k_ge_2 : (2 : ℝ) ≤ (2 : ℝ)^(e - 1 - k) := by
        calc (2 : ℝ) = (2 : ℝ)^(1 : ℤ) := by norm_num
          _ ≤ (2 : ℝ)^(e - 1 - k) :=
              zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h_exp_ge
      nlinarith
    exact (Int.zpow_le_iff_le_log (by norm_num : 1 < (2 : ℕ)) h_prod_pos).mp h_prod_ge

/-! ## The RNE-RNE counterexample -/

/-- **Core RNE-RNE counterexample.** Takes F₂'s structural parameters
explicitly: precision `q₂ ≥ p + 2`, finite quantum `f₂ ≤ e − 2`, and
unbounded magnitude. Witness `x = (3m + pred_{F₂}(m)) / 4` where the F₂-
predecessor of `m = 7·2^(e−1)` is extracted via `prev_F_adjacent_of_log_eq`.
The public-facing version is `no_rndRNE_RNE`, which takes only
`(F₁.extend 2) ⊆ F₂` plus finiteness and derives the remaining bounds. -/
theorem no_rndRNE_RNE_arbitrary_F₂
    (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    (F₂ : FiniteFormat)
    {q₂ : ℕ+} (hF₂_p : F₂.toFormat.p = ((q₂ : ℕ+) : WithTop ℕ+))
    (hq₂ : (p : ℕ) + 2 ≤ (q₂ : ℕ))
    {f₂ : ℤ} (hF₂_exp : F₂.toFormat.exp = (f₂ : WithBot ℤ)) (hf₂ : f₂ ≤ e - 2)
    (hF₂_b : F₂.toFormat.b = ⊤) :
    (F₁_g p hp_ge_2 e).toFormat ⊆ F₂.toFormat ∧
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ (.nearest .toEven) x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat (.nearest .toEven) (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat (.nearest .toEven) x w := by
  -- Containment F₁_g ⊆ F₂ from p/exp/b ordering.
  have hq₁_le_q₂ : (F₁_g p hp_ge_2 e).toFormat.p ≤ F₂.toFormat.p := by
    rw [F₁_g_p, hF₂_p]
    exact WithTop.coe_le_coe.mpr (by exact_mod_cast (by omega : (p : ℕ) ≤ (q₂ : ℕ)))
  have hf₂_le_e : F₂.toFormat.exp ≤ (F₁_g p hp_ge_2 e).toFormat.exp := by
    rw [F₁_g_exp, hF₂_exp]
    exact WithBot.coe_le_coe.mpr (by omega : f₂ ≤ e)
  have hb_le : (F₁_g p hp_ge_2 e).toFormat.b ≤ F₂.toFormat.b := by
    rw [F₁_g_b, hF₂_b]
  have h_F₁_sub : (F₁_g p hp_ge_2 e).toFormat ⊆ F₂.toFormat :=
    Format.containsPrec hq₁_le_q₂ hf₂_le_e hb_le
  refine ⟨h_F₁_sub, ?_⟩
  -- m, y_lo, y_hi.
  set m : Dyadic := m_g e with hm_def
  set y_lo : Dyadic := y_lo_g e with hy_lo_def
  set y_hi : Dyadic := y_hi_g e with hy_hi_def
  have h_m_coe : (m : ℝ) = 7 * (2 : ℝ)^(e - 1) := coe_m_g e
  have h_m_pos : 0 < (m : ℝ) := by
    rw [h_m_coe]
    have : (0 : ℝ) < (2 : ℝ)^(e - 1) := zpow_pos (by norm_num) _
    nlinarith
  -- m ∈ F₂.
  have h_m_mem_F₂ : m ∈ F₂ := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hF₂_p, Dyadic.precisionAtMost_coe_real]
      refine ⟨7, e - 1, by rw [h_m_coe]; push_cast; ring, ?_⟩
      · have h_pow : (8 : ℤ) ≤ (2 : ℤ)^(q₂ : ℕ) :=
          calc (8 : ℤ) = (2 : ℤ)^3 := by norm_num
            _ ≤ (2 : ℤ)^(q₂ : ℕ) := pow_le_pow_right₀ (by norm_num) (by omega : 3 ≤ (q₂ : ℕ))
        have h_abs : |(7 : ℤ)| = 7 := by decide
        omega
    · rw [hF₂_exp, Dyadic.quantumAtLeast_coe_real]
      refine ⟨7 * (2 : ℤ)^(e - 1 - f₂).toNat, ?_⟩
      rw [h_m_coe]
      have h_split : (2 : ℝ)^(e - 1) = ((2 : ℤ)^(e - 1 - f₂).toNat : ℝ) * (2 : ℝ)^f₂ :=
        two_zpow_split (e - 1) f₂ (by omega)
      rw [h_split]; push_cast; ring
    · rw [hF₂_b]; trivial
  -- Grid representation of m in F₂.
  obtain ⟨k, c, hk_ge_f₂, hc_lt_abs, hm_eq_F₂, hk_max⟩ :=
    exists_grid_rep F₂ hF₂_p hF₂_exp h_m_mem_F₂.1 h_m_mem_F₂.2.1 h_m_pos
  have hc_pos : 0 < c := grid_rep_c_pos h_m_pos hm_eq_F₂
  have hc_lt_pos : c < (2 : ℤ)^(q₂ : ℕ) := by
    have h_abs : |c| = c := abs_of_pos hc_pos
    rw [← h_abs]; exact hc_lt_abs
  have hm_eq_simple : (7 : ℝ) * (2 : ℝ)^(e - 1) = (c : ℝ) * (2 : ℝ)^k := by
    rw [← h_m_coe]; exact hm_eq_F₂
  have hk_max' : k = max f₂ (Int.log 2 ((c : ℝ) * (2 : ℝ)^k) - ((q₂ : ℕ) : ℤ) + 1) := by
    rw [← hm_eq_F₂]; exact hk_max
  obtain ⟨hc_ge_2, h_log_eq⟩ := m_g_grid_log_invariant
    (by omega : 4 ≤ (q₂ : ℕ)) hf₂ hk_max' hm_eq_simple
  -- Apply prev_F_adjacent_of_log_eq.
  obtain ⟨h_pred_mem, h_pred_lt_m, h_pred_max⟩ :=
    prev_F_adjacent_of_log_eq F₂ hF₂_p hF₂_exp h_m_mem_F₂ h_m_pos
      hk_ge_f₂ hc_ge_2 hc_lt_pos hm_eq_F₂ hk_max' h_log_eq
  set pred : Dyadic := Dyadic.ofIntZpow (c - 1) k with h_pred_def
  set x_val : ℝ := (3 * (m : ℝ) + (pred : ℝ)) / 4 with hx_def
  have h_pred_real : (pred : ℝ) = ((c - 1 : ℤ) : ℝ) * (2 : ℝ)^k := by
    rw [h_pred_def, Dyadic.coe_ofIntZpow]
  have h_m_real : (m : ℝ) = (c : ℝ) * (2 : ℝ)^k := hm_eq_F₂
  have h_m_minus_pred : (m : ℝ) - (pred : ℝ) = (2 : ℝ)^k := by
    rw [h_m_real, h_pred_real]; push_cast; ring
  have h_2k_pos : (0 : ℝ) < (2 : ℝ)^k := zpow_pos (by norm_num) _
  have h_pred_pos : (0 : ℝ) < (pred : ℝ) := by
    rw [h_pred_real]
    have h_c1_pos : (0 : ℝ) < ((c - 1 : ℤ) : ℝ) := by
      have : 0 < c - 1 := by omega
      exact_mod_cast this
    exact mul_pos h_c1_pos h_2k_pos
  have h_x_lt_m : x_val < (m : ℝ) := by rw [hx_def]; linarith
  have h_pred_lt_x : (pred : ℝ) < x_val := by rw [hx_def]; linarith
  have h_x_pos : 0 < x_val := by linarith
  have h_y_lo_coe : (y_lo : ℝ) = 3 * (2 : ℝ)^e := coe_y_lo_g e
  have h_y_hi_coe : (y_hi : ℝ) = (2 : ℝ)^(e + 2) := coe_y_hi_g e
  have h_2e1_pos : (0 : ℝ) < (2 : ℝ)^(e - 1) := zpow_pos (by norm_num) _
  have h_y_hi_eq : (y_hi : ℝ) = (m : ℝ) + (2 : ℝ)^(e - 1) := by
    rw [h_y_hi_coe, h_m_coe]
    rw [show e + 2 = (e - 1) + 3 by ring, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have : (2 : ℝ)^(3 : ℤ) = 8 := by norm_num
    rw [this]; ring
  have h_y_lo_eq : (y_lo : ℝ) = (m : ℝ) - (2 : ℝ)^(e - 1) := by
    rw [h_y_lo_coe, h_m_coe]
    have h_split : (2 : ℝ)^e = (2 : ℝ)^(e - 1) * (2 : ℝ)^(1 : ℤ) := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
    rw [h_split]
    have h_two : (2 : ℝ)^(1 : ℤ) = 2 := by norm_num
    rw [h_two]; ring
  -- k ≤ e - 2.
  have hk_le_e2 : k ≤ e - 2 := by
    have h_log_cxk : Int.log 2 ((c : ℝ) * (2 : ℝ)^k) = e + 1 := by
      have h_log_m : Int.log 2 ((m : ℝ)) = e + 1 := by
        rw [h_m_coe]
        apply le_antisymm
        · have hle : (7 : ℝ) * (2 : ℝ)^(e-1) < ((2 : ℕ) : ℝ)^(e + 2) := by
            rw [show ((2 : ℕ) : ℝ) = 2 from by push_cast; rfl,
                show e + 2 = (e - 1) + 3 by ring,
                zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
            have : (2 : ℝ)^(3 : ℤ) = 8 := by norm_num
            rw [this]; nlinarith
          have hm_pos' : (0 : ℝ) < (7 : ℝ) * (2 : ℝ)^(e - 1) := by nlinarith
          have h_log_lt : Int.log 2 ((7 : ℝ) * (2 : ℝ)^(e-1)) < e + 2 :=
            (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) hm_pos').mp hle
          omega
        · have hge : ((2 : ℕ) : ℝ)^(e + 1) ≤ (7 : ℝ) * (2 : ℝ)^(e-1) := by
            rw [show ((2 : ℕ) : ℝ) = 2 from by push_cast; rfl,
                show e + 1 = (e - 1) + 2 by ring,
                zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
            have : (2 : ℝ)^(2 : ℤ) = 4 := by norm_num
            rw [this]; nlinarith
          have hm_pos' : (0 : ℝ) < (7 : ℝ) * (2 : ℝ)^(e - 1) := by nlinarith
          exact (Int.zpow_le_iff_le_log (by norm_num : 1 < (2 : ℕ)) hm_pos').mp hge
      rw [h_m_real] at h_log_m
      exact h_log_m
    rw [h_log_cxk] at hk_max'
    have hk_eq : k = max f₂ (e + 2 - (q₂ : ℕ)) := by convert hk_max' using 2; ring
    rw [hk_eq]
    have h2 : e + 2 - ((q₂ : ℕ) : ℤ) ≤ e - 2 := by
      have : (4 : ℤ) ≤ ((q₂ : ℕ) : ℤ) := by exact_mod_cast (show 4 ≤ (q₂ : ℕ) by omega)
      omega
    exact max_le hf₂ h2
  have h_2k_le : (2 : ℝ)^k ≤ (2 : ℝ)^(e - 2) :=
    zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk_le_e2
  have h_2e2_pos : (0 : ℝ) < (2 : ℝ)^(e - 2) := zpow_pos (by norm_num) _
  have h_2k_lt_2e1 : (2 : ℝ)^k < (2 : ℝ)^(e - 1) := by
    calc (2 : ℝ)^k ≤ (2 : ℝ)^(e - 2) := h_2k_le
      _ < (2 : ℝ)^(e - 1) :=
          zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : (e - 2 : ℤ) < e - 1)
  refine ⟨x_val, m, y_hi, ?_, ?_, ?_⟩
  · -- RoundsFinite F₂ RNE x m.
    refine ⟨h_m_mem_F₂, ?_, ?_, ?_⟩
    · -- IsFaithfulRound (RoundUp).
      right
      refine ⟨h_m_mem_F₂, le_of_lt h_x_lt_m, ?_⟩
      intro z hzF₂ hx_le_z
      by_contra h_z_lt_m
      push Not at h_z_lt_m
      have h_z_le_pred := h_pred_max z hzF₂ h_z_lt_m
      linarith
    · -- Closeness.
      intro z hzF₂ hf
      rcases hf with ⟨_, hz_le, hz_max⟩ | ⟨_, hx_le_z, hz_min⟩
      · have h_z_lt_m : (z : ℝ) < (m : ℝ) := lt_of_le_of_lt hz_le h_x_lt_m
        have h_z_le_pred := h_pred_max z hzF₂ h_z_lt_m
        have h_xm : x_val - (m : ℝ) = -((2 : ℝ)^k / 4) := by rw [hx_def]; linarith
        have h_x_pred : x_val - (pred : ℝ) = 3 * (2 : ℝ)^k / 4 := by rw [hx_def]; linarith
        have hL : |x_val - (m : ℝ)| = (2 : ℝ)^k / 4 := by
          rw [h_xm, abs_neg, abs_of_pos]; linarith
        rw [hL]
        have h_x_minus_z_ge : (2 : ℝ)^k / 4 ≤ x_val - (z : ℝ) := by
          have : x_val - (pred : ℝ) ≤ x_val - (z : ℝ) := by linarith
          rw [h_x_pred] at this; linarith
        have h_abs : |x_val - (z : ℝ)| = x_val - (z : ℝ) := by
          rw [abs_of_nonneg]; linarith
        rw [h_abs]; exact h_x_minus_z_ge
      · have h_z_le_m : (z : ℝ) ≤ (m : ℝ) := hz_min m h_m_mem_F₂ (le_of_lt h_x_lt_m)
        have h_z_eq_m : (z : ℝ) = (m : ℝ) := by
          by_contra h_z_ne_m
          have h_z_lt_m : (z : ℝ) < (m : ℝ) := lt_of_le_of_ne h_z_le_m h_z_ne_m
          have h_z_le_pred := h_pred_max z hzF₂ h_z_lt_m
          linarith
        rw [h_z_eq_m]
    · -- No-tie.
      rintro ⟨z, hzF₂, hf, hne, heq⟩
      rcases hf with ⟨_, hz_le, hz_max⟩ | ⟨_, hx_le_z, hz_min⟩
      · exfalso
        have h_z_lt_m : (z : ℝ) < (m : ℝ) := lt_of_le_of_lt hz_le h_x_lt_m
        have h_z_le_pred := h_pred_max z hzF₂ h_z_lt_m
        have h_xm : x_val - (m : ℝ) = -((2 : ℝ)^k / 4) := by rw [hx_def]; linarith
        have hL : |x_val - (m : ℝ)| = (2 : ℝ)^k / 4 := by
          rw [h_xm, abs_neg, abs_of_pos]; linarith
        have h_x_pred : x_val - (pred : ℝ) = 3 * (2 : ℝ)^k / 4 := by rw [hx_def]; linarith
        have h_abs_xz : |x_val - (z : ℝ)| = x_val - (z : ℝ) := by
          rw [abs_of_nonneg]; linarith
        rw [hL, h_abs_xz] at heq
        linarith
      · exfalso
        apply hne
        rw [← Dyadic.coe_real_inj]
        have h_z_le_m : (z : ℝ) ≤ (m : ℝ) := hz_min m h_m_mem_F₂ (le_of_lt h_x_lt_m)
        by_contra h_z_ne_m
        have h_z_lt_m : (z : ℝ) < (m : ℝ) := lt_of_le_of_ne h_z_le_m h_z_ne_m
        have h_z_le_pred := h_pred_max z hzF₂ h_z_lt_m
        linarith
  · exact rounds_F₁_g_RNE_m_y_hi p hp_ge_2 e
  · -- ¬ RoundsFinite F₁ RNE x y_hi (since x is closer to y_lo).
    intro hr
    obtain ⟨_, _, h_close, _⟩ := hr
    have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
    have h_y_lo_faith : IsFaithfulRound (F₁_g p hp_ge_2 e).toFiniteFormat x_val y_lo := by
      left
      refine ⟨y_lo_mem_F₁_g p hp_ge_2 e, ?_, ?_⟩
      · rw [h_y_lo_eq]
        have hx_eq : x_val = (m : ℝ) - (2 : ℝ)^k / 4 := by rw [hx_def]; linarith
        rw [hx_eq]; linarith
      · intro z hz hz_le
        obtain ⟨c', hc'⟩ := F₁_g_quantum p hp_ge_2 e hz
        have h_z_lt_m : (z : ℝ) < (m : ℝ) := lt_of_le_of_lt hz_le h_x_lt_m
        rw [hc', h_m_coe] at h_z_lt_m
        have h_7_2 : (7 : ℝ) * (2 : ℝ)^(e-1) = (7/2) * (2 : ℝ)^e := by
          rw [show (e-1 : ℤ) = e + (-1 : ℤ) from by ring,
              zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          have : (2 : ℝ)^(-1 : ℤ) = 1/2 := by
            rw [show ((-1 : ℤ)) = -(1 : ℤ) from by ring, zpow_neg]; norm_num
          rw [this]; ring
        rw [h_7_2] at h_z_lt_m
        have hc'_r_lt : (c' : ℝ) < 7/2 := lt_of_mul_lt_mul_right h_z_lt_m h_2e_pos.le
        have hc'_lt_4 : (c' : ℝ) < 4 := by linarith
        have : c' < 4 := by exact_mod_cast hc'_lt_4
        have hc'_le_3 : c' ≤ 3 := by omega
        change (z : ℝ) ≤ (y_lo : ℝ)
        rw [hc', h_y_lo_coe]
        have : (c' : ℝ) ≤ 3 := by exact_mod_cast hc'_le_3
        nlinarith
    have h_close_lo := h_close y_lo (y_lo_mem_F₁_g p hp_ge_2 e) h_y_lo_faith
    have hx_eq : x_val = (m : ℝ) - (2 : ℝ)^k / 4 := by rw [hx_def]; linarith
    have h_x_y_hi : x_val - (y_hi : ℝ) = -((2 : ℝ)^(e-1) + (2 : ℝ)^k/4) := by
      rw [h_y_hi_eq, hx_eq]; ring
    have h_x_y_lo : x_val - (y_lo : ℝ) = (2 : ℝ)^(e-1) - (2 : ℝ)^k/4 := by
      rw [h_y_lo_eq, hx_eq]; ring
    have h_2k4_pos : (0 : ℝ) < (2 : ℝ)^k / 4 := by linarith
    have h_2k4_lt : (2 : ℝ)^k / 4 < (2 : ℝ)^(e - 1) := by linarith [h_2k_lt_2e1]
    have hL : |x_val - (y_hi : ℝ)| = (2 : ℝ)^(e-1) + (2 : ℝ)^k/4 := by
      rw [h_x_y_hi, abs_neg, abs_of_pos]; linarith
    have hR : |x_val - (y_lo : ℝ)| = (2 : ℝ)^(e-1) - (2 : ℝ)^k/4 := by
      rw [h_x_y_lo, abs_of_pos]; linarith
    rw [hL, hR] at h_close_lo
    linarith

/-- **Convenience wrapper** with the minimal user-facing hypotheses: the
paper-style containment `(F₁.extend 2) ⊆ F₂` plus the structural finiteness
of `F₂.p` and `F₂.exp`. The precision/quantum bounds and the unboundedness of
`F₂.b` are derived internally and forwarded to `no_rndRNE_RNE_arbitrary_F₂`. -/
theorem no_rndRNE_RNE
    (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    (F₂ : FiniteFormat)
    (hsub : ((F₁_g p hp_ge_2 e).toFiniteFormat.extend 2).toFormat ⊆ F₂.toFormat)
    (hF₂_p_fin : F₂.toFormat.p ≠ ⊤)
    (hF₂_exp_fin : F₂.toFormat.exp ≠ ⊥) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ (.nearest .toEven) x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat (.nearest .toEven) (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat (.nearest .toEven) x w := by
  -- Extract finite q₂ and f₂.
  obtain ⟨q₂, hq₂_eq⟩ := WithTop.ne_top_iff_exists.mp hF₂_p_fin
  obtain ⟨f₂, hf₂_eq⟩ := WithBot.ne_bot_iff_exists.mp hF₂_exp_fin
  have hF₂_p : F₂.toFormat.p = ((q₂ : ℕ+) : WithTop ℕ+) := hq₂_eq.symm
  have hF₂_exp : F₂.toFormat.exp = (f₂ : WithBot ℤ) := hf₂_eq.symm
  -- The extend-2 precision predicate: p + 2 bits.
  have h_ext_p : ((F₁_g p hp_ge_2 e).toFiniteFormat.extend 2).toFormat.p
      = (((p + 2 : ℕ+)) : WithTop ℕ+) := by
    change (F₁_g p hp_ge_2 e).toFormat.p.map (· + (2 : ℕ+)) = _
    rw [F₁_g_p, WithTop.map_coe]
  have h_pp2_cast : (((p + 2 : ℕ+)) : ℕ) = (p : ℕ) + 2 := by exact_mod_cast rfl
  -- Derive F₂.b = ⊤ from an arbitrarily large element.
  have hF₂_b : F₂.toFormat.b = ⊤ := by
    by_contra h_b_ne
    obtain ⟨b, hb_eq⟩ := WithTop.ne_top_iff_exists.mp h_b_ne
    set N : ℤ := max (e - 2) (Int.log 2 ((b.val : Dyadic) : ℝ) + 1) with hN_def
    set y_huge : Dyadic := Dyadic.ofIntZpow 1 N with hy_huge_def
    have hN_ge : e - 2 ≤ N := le_max_left _ _
    have hy_huge_real : ((y_huge : Dyadic) : ℝ) = (2 : ℝ)^N := by
      rw [hy_huge_def, Dyadic.coe_ofIntZpow]; push_cast; ring
    have hy_huge_in_ext2 : y_huge ∈ (F₁_g p hp_ge_2 e).toFiniteFormat.extend 2 := by
      refine ⟨?_, ?_, trivial⟩
      · rw [h_ext_p, Dyadic.precisionAtMost_coe_real]
        refine ⟨1, N, by rw [hy_huge_real]; push_cast; ring, ?_⟩
        rw [h_pp2_cast]
        have h_pow : (2 : ℤ) ≤ (2 : ℤ)^((p : ℕ) + 2) :=
          calc (2 : ℤ) = (2 : ℤ)^1 := by norm_num
            _ ≤ (2 : ℤ)^((p : ℕ) + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
        have h_abs : |(1 : ℤ)| = 1 := by decide
        omega
      · -- quantumAtLeast (exp − 2) = (e − 2).
        change Dyadic.quantumAtLeast ((F₁_g p hp_ge_2 e).toFormat.exp.map (· - (2 : ℤ))) y_huge
        rw [F₁_g_exp, WithBot.map_coe, Dyadic.quantumAtLeast_coe_real]
        refine ⟨(2 : ℤ)^(N - (e - 2)).toNat, ?_⟩
        rw [hy_huge_real, two_zpow_split N (e - 2) (by omega)]; push_cast; ring
    have hy_huge_in_F₂ : y_huge ∈ F₂.toFormat := hsub _ hy_huge_in_ext2
    have hb_ok : Format.boundOK F₂.toFormat.b y_huge := hy_huge_in_F₂.2.2
    rw [← hb_eq] at hb_ok
    change |((y_huge : Dyadic) : ℚ)| ≤ ((b.val : Dyadic) : ℚ) at hb_ok
    -- Move to ℝ.
    have hb_ok_real : |((y_huge : Dyadic) : ℝ)| ≤ ((b.val : Dyadic) : ℝ) := by
      rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast, ← Rat.cast_abs]
      exact_mod_cast hb_ok
    rw [hy_huge_real] at hb_ok_real
    have h_2N_pos : (0 : ℝ) < (2 : ℝ)^N := zpow_pos (by norm_num) _
    rw [abs_of_pos h_2N_pos] at hb_ok_real
    have hN_ge_log : Int.log 2 ((b.val : Dyadic) : ℝ) + 1 ≤ N := le_max_right _ _
    by_cases hb_pos : 0 < ((b.val : Dyadic) : ℝ)
    · have h_lt_log_succ :
          ((b.val : Dyadic) : ℝ) < (2 : ℝ)^(Int.log 2 ((b.val : Dyadic) : ℝ) + 1) := by
        have := Int.lt_zpow_succ_log_self (b := 2) (by norm_num : 1 < (2 : ℕ))
          ((b.val : Dyadic) : ℝ)
        rw [show ((2 : ℕ) : ℝ) = 2 from by push_cast; rfl] at this
        exact this
      have h_2N_ge : (2 : ℝ)^(Int.log 2 ((b.val : Dyadic) : ℝ) + 1) ≤ (2 : ℝ)^N :=
        zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hN_ge_log
      linarith
    · push Not at hb_pos
      linarith
  -- Derive p + 2 ≤ q₂ and f₂ ≤ e - 2 from a "tight" element.
  have hq₂_hf₂ : (p : ℕ) + 2 ≤ (q₂ : ℕ) ∧ f₂ ≤ e - 2 := by
    set c_max : ℤ := (2 : ℤ)^((p : ℕ) + 2) - 1 with hc_max_def
    have hc_max_pos : 0 < c_max := by
      have h_pow_ge : (2 : ℤ) ≤ (2 : ℤ)^((p : ℕ) + 2) :=
        calc (2 : ℤ) = (2 : ℤ)^1 := by norm_num
          _ ≤ (2 : ℤ)^((p : ℕ) + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
      omega
    have hc_max_lt : c_max < (2 : ℤ)^((p : ℕ) + 2) := by omega
    have hc_max_odd : Odd c_max := by
      refine ⟨(2 : ℤ)^((p : ℕ) + 1) - 1, ?_⟩
      rw [hc_max_def, show (p : ℕ) + 2 = ((p : ℕ) + 1) + 1 from by omega, pow_succ]
      ring
    set y_max : Dyadic := Dyadic.ofIntZpow c_max (e - 2) with hy_max_def
    have hy_max_real : ((y_max : Dyadic) : ℝ) = (c_max : ℝ) * (2 : ℝ)^(e - 2) := by
      rw [hy_max_def, Dyadic.coe_ofIntZpow]
    have h_2e2_pos : (0 : ℝ) < (2 : ℝ)^(e - 2) := zpow_pos (by norm_num) _
    have hy_max_pos : 0 < ((y_max : Dyadic) : ℝ) := by
      rw [hy_max_real]
      have : (0 : ℝ) < (c_max : ℝ) := by exact_mod_cast hc_max_pos
      exact mul_pos this h_2e2_pos
    have hy_max_in_ext2 : y_max ∈ (F₁_g p hp_ge_2 e).toFiniteFormat.extend 2 := by
      refine ⟨?_, ?_, trivial⟩
      · rw [h_ext_p, Dyadic.precisionAtMost_coe_real]
        refine ⟨c_max, e - 2, hy_max_real, ?_⟩
        rw [h_pp2_cast, abs_of_pos hc_max_pos]; exact hc_max_lt
      · change Dyadic.quantumAtLeast ((F₁_g p hp_ge_2 e).toFormat.exp.map (· - (2 : ℤ))) y_max
        rw [F₁_g_exp, WithBot.map_coe, Dyadic.quantumAtLeast_coe_real]
        exact ⟨c_max, hy_max_real⟩
    have hy_max_in_F₂ : y_max ∈ F₂.toFormat := hsub _ hy_max_in_ext2
    obtain ⟨k, c, hk_ge_f₂, hc_lt_abs, hy_eq, hk_max⟩ :=
      exists_grid_rep F₂ hF₂_p hF₂_exp hy_max_in_F₂.1 hy_max_in_F₂.2.1 hy_max_pos
    have h_eq_real : (c : ℝ) * (2 : ℝ)^k = (c_max : ℝ) * (2 : ℝ)^(e - 2) := by
      rw [← hy_max_real, ← hy_eq]
    have hk_le : k ≤ e - 2 := by
      by_contra h_gt
      push Not at h_gt
      set n : ℕ := (k - (e - 2)).toNat with hn_def
      have h_n_eq : (n : ℤ) = k - (e - 2) := Int.toNat_of_nonneg (by omega)
      have h_n_ge_1 : 1 ≤ n := by
        have : (1 : ℤ) ≤ (n : ℤ) := by rw [h_n_eq]; omega
        exact_mod_cast this
      have h_2e2_ne : (2 : ℝ)^(e - 2) ≠ 0 := ne_of_gt h_2e2_pos
      have h_real_eq2 : (c : ℝ) * (2 : ℝ)^(n : ℤ) = (c_max : ℝ) := by
        have h_split : (2 : ℝ)^k = (2 : ℝ)^(n : ℤ) * (2 : ℝ)^(e - 2) := by
          rw [show (k : ℤ) = (n : ℤ) + (e - 2) from by linarith [h_n_eq],
              zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        rw [h_split, ← mul_assoc] at h_eq_real
        exact mul_right_cancel₀ h_2e2_ne h_eq_real
      rw [zpow_natCast] at h_real_eq2
      have h_int_eq : c * (2 : ℤ)^n = c_max := by
        have h_cast : ((c * (2 : ℤ)^n : ℤ) : ℝ) = ((c_max : ℤ) : ℝ) := by
          push_cast; exact h_real_eq2
        exact_mod_cast h_cast
      have h_even : Even c_max := by
        rw [← h_int_eq, show (n : ℕ) = (n - 1) + 1 from by omega, pow_succ]
        refine ⟨c * (2 : ℤ)^(n - 1), ?_⟩; ring
      exact (Int.not_even_iff_odd.mpr hc_max_odd) h_even
    -- Compute log y_max = e + p - 1.
    have h_log_y_max : Int.log 2 ((y_max : Dyadic) : ℝ) = e + (p : ℕ) - 1 := by
      rw [hy_max_real]
      apply le_antisymm
      · have h_lt : (c_max : ℝ) * (2 : ℝ)^(e - 2) < ((2 : ℕ) : ℝ)^(e + (p : ℕ)) := by
          rw [show ((2 : ℕ) : ℝ) = 2 from by push_cast; rfl,
              show e + ((p : ℕ) : ℤ) = (e - 2) + (((p : ℕ) + 2 : ℕ)) by push_cast; ring,
              zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          have h_2p_pow : (2 : ℝ)^(((p : ℕ) + 2 : ℕ) : ℤ) = ((2 : ℤ)^((p : ℕ) + 2) : ℝ) := by
            rw [zpow_natCast]; push_cast; ring
          rw [h_2p_pow]
          have hc_max_lt_r : (c_max : ℝ) < ((2 : ℤ)^((p : ℕ) + 2) : ℝ) := by
            exact_mod_cast hc_max_lt
          nlinarith
        have hy_pos' : (0 : ℝ) < (c_max : ℝ) * (2 : ℝ)^(e - 2) := by
          rw [← hy_max_real]; exact hy_max_pos
        have := (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) hy_pos').mp h_lt
        omega
      · have h_ge : ((2 : ℕ) : ℝ)^(e + (p : ℕ) - 1) ≤ (c_max : ℝ) * (2 : ℝ)^(e - 2) := by
          rw [show ((2 : ℕ) : ℝ) = 2 from by push_cast; rfl,
              show e + ((p : ℕ) : ℤ) - 1 = (e - 2) + (((p : ℕ) + 1 : ℕ)) by push_cast; ring,
              zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          have h_2p1_pow : (2 : ℝ)^(((p : ℕ) + 1 : ℕ) : ℤ) = ((2 : ℤ)^((p : ℕ) + 1) : ℝ) := by
            rw [zpow_natCast]; push_cast; ring
          rw [h_2p1_pow]
          have hc_max_ge : ((2 : ℤ)^((p : ℕ) + 1) : ℝ) ≤ (c_max : ℝ) := by
            have h_int : (2 : ℤ)^((p : ℕ) + 1) ≤ c_max := by
              rw [hc_max_def]
              have h_two_pp2 : (2 : ℤ)^((p : ℕ) + 2) = 2 * (2 : ℤ)^((p : ℕ) + 1) := by
                rw [show (p : ℕ) + 2 = ((p : ℕ) + 1) + 1 from by omega, pow_succ]; ring
              omega
            exact_mod_cast h_int
          nlinarith
        have hy_pos' : (0 : ℝ) < (c_max : ℝ) * (2 : ℝ)^(e - 2) := by
          rw [← hy_max_real]; exact hy_max_pos
        exact (Int.zpow_le_iff_le_log (by norm_num : 1 < (2 : ℕ)) hy_pos').mp h_ge
    rw [h_log_y_max] at hk_max
    have hk_eq : k = max f₂ (e + (p : ℕ) - (q₂ : ℕ)) := by convert hk_max using 2; ring
    rw [hk_eq] at hk_le
    refine ⟨?_, ?_⟩
    · have h_part : e + ((p : ℕ) : ℤ) - ((q₂ : ℕ) : ℤ) ≤ e - 2 :=
        le_trans (le_max_right _ _) hk_le
      have hq_int : ((p : ℕ) + 2 : ℤ) ≤ ((q₂ : ℕ) : ℤ) := by push_cast at h_part ⊢; omega
      exact_mod_cast hq_int
    · exact le_trans (le_max_left _ _) hk_le
  obtain ⟨hq₂, hf₂⟩ := hq₂_hf₂
  exact (no_rndRNE_RNE_arbitrary_F₂ p hp_ge_2 e F₂ hF₂_p hq₂ hF₂_exp hf₂ hF₂_b).2

/-! ## CHUNK 3: the remaining §5.2 counterexamples -/

/-- For any `F₂` with finite quantum `f₂`, no F₂-element lies strictly in
`(0, 2^f₂)`. -/
theorem F₂_no_element_in_zero_quantum_interval
    (F₂ : Format) {f₂ : ℤ} (hF₂_exp : F₂.exp = (f₂ : WithBot ℤ))
    {z : Dyadic} (hzF : z ∈ F₂)
    (hz_pos : 0 < ((z : Dyadic) : ℝ))
    (hz_lt : ((z : Dyadic) : ℝ) < (2 : ℝ) ^ f₂) :
    False := by
  obtain ⟨_, hq, _⟩ := hzF
  rw [hF₂_exp, Dyadic.quantumAtLeast_coe_real] at hq
  obtain ⟨c, hc⟩ := hq
  rw [hc] at hz_pos hz_lt
  have h_2f_pos : (0 : ℝ) < (2 : ℝ) ^ f₂ := zpow_pos (by norm_num) _
  have hc_pos : 0 < (c : ℝ) := pos_of_mul_pos_left (by linarith) h_2f_pos.le
  have hc_lt : (c : ℝ) < 1 := by
    have h1 : (c : ℝ) * (2 : ℝ)^f₂ < 1 * (2 : ℝ)^f₂ := by linarith
    exact lt_of_mul_lt_mul_right h1 h_2f_pos.le
  have hc_int_pos : 0 < c := by exact_mod_cast hc_pos
  have hc_int_lt_1 : c < 1 := by exact_mod_cast hc_lt
  omega

/-- For any `F₂` with finite quantum `f₂` and `F₁_g ⊆ F₂`, `F₂.b` must be `⊤`. -/
theorem F₂_b_top_of_F₁_g_subset
    (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    (F₂ : Format) (hsub : (F₁_g p hp_ge_2 e).toFormat ⊆ F₂) :
    F₂.b = ⊤ := by
  by_contra h_b_ne
  obtain ⟨b, hb_eq⟩ := WithTop.ne_top_iff_exists.mp h_b_ne
  set N : ℤ := max e (Int.log 2 ((b.val : Dyadic) : ℝ) + 1) with hN_def
  set y_huge : Dyadic := Dyadic.ofIntZpow 1 N with hy_huge_def
  have hy_huge_real : ((y_huge : Dyadic) : ℝ) = (2 : ℝ)^N := by
    rw [hy_huge_def, Dyadic.coe_ofIntZpow]; push_cast; ring
  have hN_ge : e ≤ N := le_max_left _ _
  have hy_huge_in_F₁ : y_huge ∈ (F₁_g p hp_ge_2 e).toFormat := by
    refine ⟨?_, ?_, trivial⟩
    · change Dyadic.precisionAtMost ((p : ℕ+) : WithTop ℕ+) y_huge
      rw [Dyadic.precisionAtMost_coe_real]
      refine ⟨1, N, ?_, ?_⟩
      · rw [hy_huge_real]; push_cast; ring
      · have h_pow : (2 : ℤ) ≤ (2 : ℤ)^(p : ℕ) :=
          calc (2 : ℤ) = (2 : ℤ)^1 := by norm_num
            _ ≤ (2 : ℤ)^(p : ℕ) := pow_le_pow_right₀ (by norm_num) (by omega)
        have h_abs : |(1 : ℤ)| = 1 := by decide
        omega
    · change Dyadic.quantumAtLeast (((e : ℤ)) : WithBot ℤ) y_huge
      rw [Dyadic.quantumAtLeast_coe_real]
      refine ⟨(2 : ℤ)^(N - e).toNat, ?_⟩
      rw [hy_huge_real, two_zpow_split N e (by omega)]
      push_cast; ring
  have hy_huge_in_F₂ : y_huge ∈ F₂ := hsub _ hy_huge_in_F₁
  have hb_ok : Format.boundOK F₂.b y_huge := hy_huge_in_F₂.2.2
  rw [← hb_eq] at hb_ok
  change |((y_huge : Dyadic) : ℚ)| ≤ ((b.val : Dyadic) : ℚ) at hb_ok
  have hb_ok_real : |((y_huge : Dyadic) : ℝ)| ≤ ((b.val : Dyadic) : ℝ) := by
    rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast, ← Rat.cast_abs]
    exact_mod_cast hb_ok
  rw [hy_huge_real] at hb_ok_real
  have h_2N_pos : (0 : ℝ) < (2 : ℝ)^N := zpow_pos (by norm_num) _
  rw [abs_of_pos h_2N_pos] at hb_ok_real
  have hN_ge_log : Int.log 2 ((b.val : Dyadic) : ℝ) + 1 ≤ N := le_max_right _ _
  by_cases hb_pos : 0 < ((b.val : Dyadic) : ℝ)
  · have h_lt_log_succ :
        ((b.val : Dyadic) : ℝ) < (2 : ℝ)^(Int.log 2 ((b.val : Dyadic) : ℝ) + 1) := by
      have := Int.lt_zpow_succ_log_self (b := 2)
        (by norm_num : 1 < (2 : ℕ)) ((b.val : Dyadic) : ℝ)
      rw [show ((2 : ℕ) : ℝ) = 2 from by push_cast; rfl] at this
      exact this
    have h_2N_ge : (2 : ℝ)^(Int.log 2 ((b.val : Dyadic) : ℝ) + 1) ≤ (2 : ℝ)^N :=
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hN_ge_log
    linarith
  · push Not at hb_pos; linarith

/-- `IsOdd` depends only on `toFormat`: transfer along `F'.toFormat = F.toFormat`. -/
theorem isOdd_transfer_toFormat {F F' : ParityFormat} {y : Dyadic}
    (hF'_eq : F'.toFormat = F.toFormat) (h : F'.IsOdd y) : F.IsOdd y := by
  have h_nd : F.toFiniteFormat.numDigits ((y : Dyadic) : ℝ)
      = F'.toFiniteFormat.numDigits ((y : Dyadic) : ℝ) := by
    unfold FiniteFormat.numDigits; rw [hF'_eq]
  obtain ⟨c, e', hrep, hpar⟩ := h
  refine ⟨c, e', ?_, ?_⟩
  · rw [h_nd]; exact hrep
  · rw [show F.toFormat = F'.toFormat from hF'_eq.symm]; exact hpar

/-- **Counterexample to `rndRNE_RAZ`.** -/
theorem no_rndRNE_RAZ
    (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    (F₂ : FiniteFormat) (hF₂_exp_fin : F₂.toFormat.exp ≠ ⊥) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ (.nearest .toEven) x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .awayZero (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .awayZero x w := by
  obtain ⟨f₂, hf₂_eq⟩ := WithBot.ne_bot_iff_exists.mp hF₂_exp_fin
  have hF₂_exp : F₂.toFormat.exp = (f₂ : WithBot ℤ) := hf₂_eq.symm
  set x_val : ℝ := (2 : ℝ)^(f₂ - 2) with hx_def
  have h_2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
  have h_2f2_pos : (0 : ℝ) < (2 : ℝ)^(f₂ - 2) := zpow_pos (by norm_num) _
  have h_x_pos : 0 < x_val := h_2f2_pos
  have h_2f_split : (2 : ℝ)^f₂ = 4 * (2 : ℝ)^(f₂ - 2) := by
    have h_eq : (2 : ℝ)^f₂ = (2 : ℝ)^(f₂ - 2) * (2 : ℝ)^(2 : ℤ) := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
    have h2 : (2 : ℝ)^(2 : ℤ) = 4 := by norm_num
    rw [h_eq, h2]; ring
  have h_x_lt_2f : x_val < (2 : ℝ)^f₂ := by rw [h_2f_split]; linarith
  have h_F₂_le_x_to_le_0 : ∀ z ∈ F₂.toFormat, ((z : Dyadic) : ℝ) ≤ x_val →
      ((z : Dyadic) : ℝ) ≤ 0 := by
    intro z hz hz_le
    obtain ⟨_, hq, _⟩ := hz
    rw [hF₂_exp, Dyadic.quantumAtLeast_coe_real] at hq
    obtain ⟨c, hc⟩ := hq
    rw [hc] at hz_le
    have hc_le_quart : (c : ℝ) ≤ 1/4 := by
      have hxv : x_val = (1/4 : ℝ) * (2 : ℝ)^f₂ := by
        rw [hx_def, h_2f_split]; ring
      rw [hxv] at hz_le
      exact le_of_mul_le_mul_right hz_le h_2f_pos
    have hc_lt_1 : (c : ℝ) < 1 := by linarith
    have hc_int_lt : c < 1 := by exact_mod_cast hc_lt_1
    have hc_le_0 : c ≤ 0 := by omega
    rw [hc]
    have h_cr : (c : ℝ) ≤ 0 := by exact_mod_cast hc_le_0
    nlinarith
  have h_F₂_ge_x_to_ge_2f : ∀ z ∈ F₂.toFormat, x_val ≤ ((z : Dyadic) : ℝ) →
      (2 : ℝ)^f₂ ≤ ((z : Dyadic) : ℝ) := by
    intro z hz hz_ge
    obtain ⟨_, hq, _⟩ := hz
    rw [hF₂_exp, Dyadic.quantumAtLeast_coe_real] at hq
    obtain ⟨c, hc⟩ := hq
    rw [hc] at hz_ge
    have hc_ge_quart : (1/4 : ℝ) ≤ (c : ℝ) := by
      have hxv : x_val = (1/4 : ℝ) * (2 : ℝ)^f₂ := by
        rw [hx_def, h_2f_split]; ring
      rw [hxv] at hz_ge
      exact le_of_mul_le_mul_right hz_ge h_2f_pos
    have hc_gt_0 : (0 : ℝ) < (c : ℝ) := by linarith
    have hc_int_pos : 0 < c := by exact_mod_cast hc_gt_0
    have hc_ge_1 : 1 ≤ c := hc_int_pos
    rw [hc]
    have h_cr : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc_ge_1
    nlinarith
  refine ⟨x_val, 0, 0, ?_, ?_, ?_⟩
  · refine ⟨FiniteFormat.zero_mem F₂, ?_, ?_, ?_⟩
    · left
      refine ⟨FiniteFormat.zero_mem F₂, ?_, ?_⟩
      · change ((0 : Dyadic) : ℝ) ≤ x_val
        push_cast; linarith
      · intro z hz hz_le
        have := h_F₂_le_x_to_le_0 z hz hz_le
        change ((z : Dyadic) : ℝ) ≤ ((0 : Dyadic) : ℝ)
        push_cast; linarith
    · intro z hz hf
      push_cast
      rcases hf with ⟨_, hz_le, _⟩ | ⟨_, hz_ge, _⟩
      · have h_z_le_0 := h_F₂_le_x_to_le_0 z hz hz_le
        rw [show x_val - 0 = x_val from by ring, abs_of_pos h_x_pos]
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x_val - (z : ℝ))]
        linarith
      · have h_z_ge_2f := h_F₂_ge_x_to_ge_2f z hz hz_ge
        rw [show x_val - 0 = x_val from by ring, abs_of_pos h_x_pos]
        rw [abs_of_nonpos (by linarith : x_val - (z : ℝ) ≤ 0), neg_sub]
        linarith
    · rintro ⟨z, hzF, hf, hne, heq⟩
      change |x_val - ((0 : Dyadic) : ℝ)| = |x_val - ((z : Dyadic) : ℝ)| at heq
      push_cast at heq
      rcases hf with ⟨_, hz_le, _⟩ | ⟨_, hz_ge, _⟩
      · have h_z_le_0 := h_F₂_le_x_to_le_0 z hzF hz_le
        have h_z_lt_0 : ((z : Dyadic) : ℝ) < 0 := by
          rcases lt_or_eq_of_le h_z_le_0 with h | h_eq
          · exact h
          · exfalso; apply hne; rw [← Dyadic.coe_real_inj]; push_cast; exact h_eq
        rw [show x_val - 0 = x_val from by ring, abs_of_pos h_x_pos] at heq
        rw [abs_of_pos (by linarith : 0 < x_val - (z : ℝ))] at heq
        linarith
      · have h_z_ge_2f := h_F₂_ge_x_to_ge_2f z hzF hz_ge
        rw [show x_val - 0 = x_val from by ring, abs_of_pos h_x_pos] at heq
        rw [abs_of_nonpos (by linarith : x_val - (z : ℝ) ≤ 0), neg_sub] at heq
        linarith
  · refine ⟨FiniteFormat.zero_mem _, ?_, ?_, ?_⟩
    · change |((0 : Dyadic) : ℝ)| ≤ |((0 : Dyadic) : ℝ)|; rfl
    · change ((0 : Dyadic) : ℝ) * ((0 : Dyadic) : ℝ) ≥ 0
      push_cast; linarith
    · intro v _ _ _
      push_cast
      rw [abs_zero]
      exact abs_nonneg _
  · intro hr
    obtain ⟨_, h_bnd, _, _⟩ := hr
    change |x_val| ≤ |((0 : Dyadic) : ℝ)| at h_bnd
    push_cast at h_bnd
    rw [abs_of_pos h_x_pos, abs_zero] at h_bnd
    linarith

/-- **Counterexample to `rndRNE_RTZ`.** -/
theorem no_rndRNE_RTZ
    (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    (F₂ : FiniteFormat) (hsub : (F₁_g p hp_ge_2 e).toFormat ⊆ F₂.toFormat)
    (hF₂_exp_fin : F₂.toFormat.exp ≠ ⊥) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ (.nearest .toEven) x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .toZero (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .toZero x w := by
  obtain ⟨f₂, hf₂_eq⟩ := WithBot.ne_bot_iff_exists.mp hF₂_exp_fin
  have hF₂_exp : F₂.toFormat.exp = (f₂ : WithBot ℤ) := hf₂_eq.symm
  have h_two_e_in_F₁ := two_e_mem_F₁_g p hp_ge_2 e
  have h_two_e_in_F₂ : two_e_g e ∈ F₂.toFormat := hsub _ h_two_e_in_F₁
  have hf₂_le_e : f₂ ≤ e := f₂_le_e_of_F₁_g_subset p hp_ge_2 e F₂.toFormat hsub hF₂_exp
  set x_val : ℝ := (2 : ℝ)^e - (2 : ℝ)^(f₂ - 2) with hx_def
  have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
  have h_2f2_pos : (0 : ℝ) < (2 : ℝ)^(f₂ - 2) := zpow_pos (by norm_num) _
  have h_2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
  have h_2f2_lt_2e : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^e :=
    zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < e)
  have h_x_pos : 0 < x_val := by rw [hx_def]; linarith
  have h_x_lt_2e : x_val < (2 : ℝ)^e := by rw [hx_def]; linarith
  have h_two_e_coe := coe_two_e_g e
  set n : ℕ := (e - f₂).toNat with hn_def
  have h_2e_eq : (2 : ℝ)^e = ((2 : ℤ)^n : ℝ) * (2 : ℝ)^f₂ := two_zpow_split e f₂ hf₂_le_e
  have h_2f_split : (2 : ℝ)^f₂ = 4 * (2 : ℝ)^(f₂ - 2) := two_zpow_split_minus_two f₂
  have h_F₂_lt_2e_bound : ∀ z ∈ F₂.toFormat, ((z : Dyadic) : ℝ) < (2 : ℝ)^e →
      ((z : Dyadic) : ℝ) ≤ (2 : ℝ)^e - (2 : ℝ)^f₂ := by
    have h_target_eq : (2 : ℝ)^e - (2 : ℝ)^f₂ = (((2 : ℤ)^n - 1 : ℤ) : ℝ) * (2 : ℝ) ^ f₂ := by
      push_cast; rw [h_2e_eq]; ring
    intro z hz hz_lt
    apply F₂_grid_floor hF₂_exp h_target_eq z hz
    linarith
  have h_F₂_ge_x_to_ge_2e : ∀ z ∈ F₂.toFormat, x_val ≤ ((z : Dyadic) : ℝ) →
      (2 : ℝ)^e ≤ ((z : Dyadic) : ℝ) := by
    intro z hz hz_ge
    by_contra h_lt
    push Not at h_lt
    have h_z_bnd := h_F₂_lt_2e_bound z hz h_lt
    have h_2f2_lt_2f : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^f₂ := by
      have : f₂ - 2 < f₂ := by omega
      exact zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) this
    linarith
  refine ⟨x_val, two_e_g e, two_e_g e, ?_, ?_, ?_⟩
  · refine ⟨h_two_e_in_F₂, ?_, ?_, ?_⟩
    · right
      refine ⟨h_two_e_in_F₂, ?_, ?_⟩
      · rw [h_two_e_coe]; linarith
      · intro z hz hz_ge
        rw [h_two_e_coe]
        exact h_F₂_ge_x_to_ge_2e z hz hz_ge
    · intro z hz hf
      rw [h_two_e_coe]
      rcases hf with ⟨_, hz_le, _⟩ | ⟨_, hz_ge, _⟩
      · have h_z_lt_2e : (z : ℝ) < (2 : ℝ)^e := lt_of_le_of_lt hz_le h_x_lt_2e
        have h_z_bnd := h_F₂_lt_2e_bound z hz h_z_lt_2e
        rw [abs_of_neg (by rw [hx_def]; linarith : x_val - (2 : ℝ)^e < 0), neg_sub]
        rw [abs_of_nonneg (by rw [hx_def]; linarith : (0 : ℝ) ≤ x_val - (z : ℝ))]
        rw [h_2f_split] at h_z_bnd
        rw [hx_def]; linarith
      · have h_z_ge_2e := h_F₂_ge_x_to_ge_2e z hz hz_ge
        rw [abs_of_neg (by rw [hx_def]; linarith : x_val - (2 : ℝ)^e < 0), neg_sub]
        rw [abs_of_nonpos (by linarith : x_val - (z : ℝ) ≤ 0), neg_sub]
        linarith
    · rintro ⟨z, hzF₂, hf, hne, heq⟩
      rw [h_two_e_coe] at heq
      rcases hf with ⟨_, hz_le, _⟩ | ⟨_, hz_ge, _⟩
      · exfalso
        have h_z_lt_2e : (z : ℝ) < (2 : ℝ)^e := lt_of_le_of_lt hz_le h_x_lt_2e
        have h_z_bnd := h_F₂_lt_2e_bound z hzF₂ h_z_lt_2e
        rw [abs_of_neg (by rw [hx_def]; linarith : x_val - (2 : ℝ)^e < 0), neg_sub] at heq
        rw [abs_of_nonneg (by rw [hx_def]; linarith : (0 : ℝ) ≤ x_val - (z : ℝ))] at heq
        rw [h_2f_split] at h_z_bnd
        rw [hx_def] at heq
        linarith
      · exfalso
        have h_z_ge_2e := h_F₂_ge_x_to_ge_2e z hzF₂ hz_ge
        have h_z_ne_2e : (z : ℝ) ≠ (2 : ℝ)^e := by
          intro h_eq
          apply hne
          rw [← Dyadic.coe_real_inj, h_two_e_coe]; exact h_eq
        have h_z_gt_2e : (2 : ℝ)^e < (z : ℝ) := lt_of_le_of_ne h_z_ge_2e (Ne.symm h_z_ne_2e)
        have h_z_ge_2e_plus : (2 : ℝ)^e + (2 : ℝ)^f₂ ≤ (z : ℝ) := by
          obtain ⟨_, hq, _⟩ := hzF₂
          rw [hF₂_exp, Dyadic.quantumAtLeast_coe_real] at hq
          obtain ⟨c, hc⟩ := hq
          rw [hc] at h_z_gt_2e ⊢
          rw [h_2e_eq] at h_z_gt_2e
          have hc_gt : ((2 : ℤ)^n : ℝ) < (c : ℝ) :=
            lt_of_mul_lt_mul_right h_z_gt_2e h_2f_pos.le
          have hc_int_gt : (2 : ℤ)^n < c := by exact_mod_cast hc_gt
          have hc_int_ge : (2 : ℤ)^n + 1 ≤ c := by omega
          have hc_real_ge : ((2 : ℤ)^n : ℝ) + 1 ≤ (c : ℝ) := by
            have h1 : (((2 : ℤ)^n + 1 : ℤ) : ℝ) ≤ ((c : ℤ) : ℝ) := by exact_mod_cast hc_int_ge
            push_cast at h1; exact h1
          have h_mul : (((2 : ℤ)^n : ℝ) + 1) * (2 : ℝ)^f₂ ≤ (c : ℝ) * (2 : ℝ)^f₂ :=
            mul_le_mul_of_nonneg_right hc_real_ge h_2f_pos.le
          rw [h_2e_eq]
          linarith
        rw [abs_of_neg (by rw [hx_def]; linarith : x_val - (2 : ℝ)^e < 0), neg_sub] at heq
        rw [abs_of_nonpos (by linarith : x_val - (z : ℝ) ≤ 0), neg_sub] at heq
        rw [hx_def] at heq; linarith
  · refine ⟨h_two_e_in_F₁, ?_, ?_, ?_⟩
    · rfl
    · exact mul_self_nonneg _
    · intro v _ hv_bnd _
      exact hv_bnd
  · intro hr
    obtain ⟨_, h_bnd, _, _⟩ := hr
    rw [h_two_e_coe] at h_bnd
    rw [abs_of_pos h_x_pos, abs_of_pos h_2e_pos] at h_bnd
    linarith

/-- **Counterexample to `rndRTZ_RAZ`.** -/
theorem no_rndRTZ_RAZ
    (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    (F₂ : FiniteFormat) (hsub : (F₁_g p hp_ge_2 e).toFormat ⊆ F₂.toFormat)
    (hF₂_exp_fin : F₂.toFormat.exp ≠ ⊥) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .toZero x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .awayZero (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .awayZero x w := by
  obtain ⟨f₂, hf₂_eq⟩ := WithBot.ne_bot_iff_exists.mp hF₂_exp_fin
  have hF₂_exp : F₂.toFormat.exp = (f₂ : WithBot ℤ) := hf₂_eq.symm
  have h_two_e_in_F₁ := two_e_mem_F₁_g p hp_ge_2 e
  have h_two_e_in_F₂ : two_e_g e ∈ F₂.toFormat := hsub _ h_two_e_in_F₁
  have hf₂_le_e : f₂ ≤ e := f₂_le_e_of_F₁_g_subset p hp_ge_2 e F₂.toFormat hsub hF₂_exp
  set x_val : ℝ := (2 : ℝ)^e + (2 : ℝ)^(f₂ - 2) with hx_def
  have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
  have h_2f2_pos : (0 : ℝ) < (2 : ℝ)^(f₂ - 2) := zpow_pos (by norm_num) _
  have h_2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
  have h_x_pos : 0 < x_val := by rw [hx_def]; linarith
  have h_x_gt_2e : (2 : ℝ)^e < x_val := by rw [hx_def]; linarith
  have h_two_e_coe := coe_two_e_g e
  set n : ℕ := (e - f₂).toNat with hn_def
  have h_2e_eq : (2 : ℝ)^e = ((2 : ℤ)^n : ℝ) * (2 : ℝ)^f₂ := two_zpow_split e f₂ hf₂_le_e
  have h_F₂_le_x_to_le_2e : ∀ z ∈ F₂.toFormat, ((z : Dyadic) : ℝ) ≤ x_val →
      ((z : Dyadic) : ℝ) ≤ (2 : ℝ)^e := by
    intro z hz hz_le
    obtain ⟨_, hq, _⟩ := hz
    rw [hF₂_exp, Dyadic.quantumAtLeast_coe_real] at hq
    obtain ⟨c, hc⟩ := hq
    rw [hc] at hz_le ⊢
    by_contra h_gt
    push Not at h_gt
    rw [h_2e_eq] at h_gt
    have hc_gt : ((2 : ℤ)^n : ℝ) < (c : ℝ) := lt_of_mul_lt_mul_right h_gt h_2f_pos.le
    have hc_int_gt : (2 : ℤ)^n < c := by exact_mod_cast hc_gt
    have hc_int_ge : (2 : ℤ)^n + 1 ≤ c := by omega
    have hc_real_ge : ((2 : ℤ)^n : ℝ) + 1 ≤ (c : ℝ) := by
      have h1 : (((2 : ℤ)^n + 1 : ℤ) : ℝ) ≤ ((c : ℤ) : ℝ) := by exact_mod_cast hc_int_ge
      push_cast at h1; exact h1
    have h_mul : ((2 : ℤ)^n : ℝ) * (2 : ℝ)^f₂ + (2 : ℝ)^f₂ ≤ (c : ℝ) * (2 : ℝ)^f₂ := by
      have h := mul_le_mul_of_nonneg_right hc_real_ge h_2f_pos.le
      linarith [h, show (((2 : ℤ)^n : ℝ) + 1) * (2 : ℝ)^f₂
        = ((2 : ℤ)^n : ℝ) * (2 : ℝ)^f₂ + (2 : ℝ)^f₂ from by ring]
    have h_2f_gt_2f2 : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^f₂ :=
      zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < f₂)
    rw [hx_def] at hz_le
    rw [h_2e_eq] at hz_le
    linarith
  refine ⟨x_val, two_e_g e, two_e_g e, ?_, ?_, ?_⟩
  · refine ⟨h_two_e_in_F₂, ?_, ?_, ?_⟩
    · rw [h_two_e_coe, abs_of_pos h_2e_pos, abs_of_pos h_x_pos]; linarith
    · rw [h_two_e_coe]; positivity
    · intro z hz hz_bnd hz_sign
      have h_z_nn : 0 ≤ ((z : Dyadic) : ℝ) := nonneg_of_mul_nonneg_pos hz_sign h_x_pos
      rw [abs_of_nonneg h_z_nn, abs_of_pos h_x_pos] at hz_bnd
      rw [h_two_e_coe, abs_of_pos h_2e_pos, abs_of_nonneg h_z_nn]
      exact h_F₂_le_x_to_le_2e z hz hz_bnd
  · refine ⟨h_two_e_in_F₁, ?_, ?_, ?_⟩
    · rfl
    · change ((two_e_g e : Dyadic) : ℝ) * ((two_e_g e : Dyadic) : ℝ) ≥ 0
      rw [h_two_e_coe]; positivity
    · intro v _ hv_bnd _
      exact hv_bnd
  · intro hr
    obtain ⟨_, h_bnd, _, _⟩ := hr
    rw [h_two_e_coe, abs_of_pos h_x_pos, abs_of_pos h_2e_pos] at h_bnd
    linarith

/-- **Counterexample to `rndRAZ_RTZ`.** -/
theorem no_rndRAZ_RTZ
    (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    (F₂ : FiniteFormat) (hsub : (F₁_g p hp_ge_2 e).toFormat ⊆ F₂.toFormat)
    (hF₂_exp_fin : F₂.toFormat.exp ≠ ⊥) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .awayZero x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .toZero (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .toZero x w := by
  obtain ⟨f₂, hf₂_eq⟩ := WithBot.ne_bot_iff_exists.mp hF₂_exp_fin
  have hF₂_exp : F₂.toFormat.exp = (f₂ : WithBot ℤ) := hf₂_eq.symm
  have h_two_e_in_F₁ := two_e_mem_F₁_g p hp_ge_2 e
  have h_two_e_in_F₂ : two_e_g e ∈ F₂.toFormat := hsub _ h_two_e_in_F₁
  have hf₂_le_e : f₂ ≤ e := f₂_le_e_of_F₁_g_subset p hp_ge_2 e F₂.toFormat hsub hF₂_exp
  set x_val : ℝ := (2 : ℝ)^e - (2 : ℝ)^(f₂ - 2) with hx_def
  have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
  have h_2f2_pos : (0 : ℝ) < (2 : ℝ)^(f₂ - 2) := zpow_pos (by norm_num) _
  have h_2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
  have h_2f2_lt_2e : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^e :=
    zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < e)
  have h_x_pos : 0 < x_val := by rw [hx_def]; linarith
  have h_x_lt_2e : x_val < (2 : ℝ)^e := by rw [hx_def]; linarith
  have h_two_e_coe := coe_two_e_g e
  set n : ℕ := (e - f₂).toNat with hn_def
  have h_2e_eq : (2 : ℝ)^e = ((2 : ℤ)^n : ℝ) * (2 : ℝ)^f₂ := two_zpow_split e f₂ hf₂_le_e
  have h_F₂_lt_2e_bound : ∀ z ∈ F₂.toFormat, ((z : Dyadic) : ℝ) < (2 : ℝ)^e →
      ((z : Dyadic) : ℝ) ≤ (2 : ℝ)^e - (2 : ℝ)^f₂ := by
    intro z hz hz_lt
    obtain ⟨_, hq, _⟩ := hz
    rw [hF₂_exp, Dyadic.quantumAtLeast_coe_real] at hq
    obtain ⟨c, hc⟩ := hq
    rw [hc] at hz_lt ⊢
    have h_mul_bnd : ((c : ℝ) + 1) * (2 : ℝ)^f₂ ≤ (2 : ℝ)^e := by
      rw [h_2e_eq] at hz_lt
      have hc_lt : (c : ℝ) < ((2 : ℤ)^n : ℝ) :=
        lt_of_mul_lt_mul_right hz_lt h_2f_pos.le
      have hc_int_lt : c < (2 : ℤ)^n := by exact_mod_cast hc_lt
      have hc_int_le : c + 1 ≤ (2 : ℤ)^n := by omega
      have hc_real_le : (c : ℝ) + 1 ≤ ((2 : ℤ)^n : ℝ) := by exact_mod_cast hc_int_le
      have h_mul : ((c : ℝ) + 1) * (2 : ℝ)^f₂ ≤ ((2 : ℤ)^n : ℝ) * (2 : ℝ)^f₂ :=
        mul_le_mul_of_nonneg_right hc_real_le h_2f_pos.le
      rw [← h_2e_eq] at h_mul; exact h_mul
    linarith
  refine ⟨x_val, two_e_g e, two_e_g e, ?_, ?_, ?_⟩
  · refine ⟨h_two_e_in_F₂, ?_, ?_, ?_⟩
    · rw [h_two_e_coe, abs_of_pos h_2e_pos, abs_of_pos h_x_pos]; linarith
    · rw [h_two_e_coe]; positivity
    · intro z hz hz_bnd hz_sign
      have h_z_nn : 0 ≤ ((z : Dyadic) : ℝ) := nonneg_of_mul_nonneg_pos hz_sign h_x_pos
      rw [abs_of_nonneg h_z_nn, abs_of_pos h_x_pos] at hz_bnd
      rw [h_two_e_coe, abs_of_pos h_2e_pos, abs_of_nonneg h_z_nn]
      by_contra h_lt
      push Not at h_lt
      have h_z_pred := h_F₂_lt_2e_bound z hz h_lt
      have h_2f2_lt_2f : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^f₂ :=
        zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < f₂)
      rw [hx_def] at hz_bnd
      linarith
  · refine ⟨h_two_e_in_F₁, ?_, ?_, ?_⟩
    · rfl
    · exact mul_self_nonneg _
    · intro v _ hv_bnd _
      exact hv_bnd
  · intro hr
    obtain ⟨_, h_bnd, _, _⟩ := hr
    rw [h_two_e_coe, abs_of_pos h_2e_pos, abs_of_pos h_x_pos] at h_bnd
    linarith

/-- **Counterexample to `rndRAZ_RTO`.** -/
theorem no_rndRAZ_RTO
    (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    (F₂ : FiniteFormat) (hsub : (F₁_g p hp_ge_2 e).toFormat ⊆ F₂.toFormat)
    (hF₂_exp_fin : F₂.toFormat.exp ≠ ⊥) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .awayZero x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .toOdd (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .toOdd x w := by
  obtain ⟨f₂, hf₂_eq⟩ := WithBot.ne_bot_iff_exists.mp hF₂_exp_fin
  have hF₂_exp : F₂.toFormat.exp = (f₂ : WithBot ℤ) := hf₂_eq.symm
  have h_y_hi_in_F₁ := y_hi_mem_F₁_g p hp_ge_2 e
  have h_y_hi_in_F₂ : y_hi_g e ∈ F₂.toFormat := hsub _ h_y_hi_in_F₁
  have hf₂_le_e : f₂ ≤ e := f₂_le_e_of_F₁_g_subset p hp_ge_2 e F₂.toFormat hsub hF₂_exp
  have hf₂_le_e2 : f₂ ≤ e + 2 := by omega
  set x_val : ℝ := (2 : ℝ)^(e + 2) - (2 : ℝ)^(f₂ - 2) with hx_def
  have h_2e2_pos : (0 : ℝ) < (2 : ℝ)^(e + 2) := zpow_pos (by norm_num) _
  have h_2f2_pos : (0 : ℝ) < (2 : ℝ)^(f₂ - 2) := zpow_pos (by norm_num) _
  have h_2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
  have h_2f2_lt_2e2 : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^(e + 2) :=
    zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < e + 2)
  have h_x_pos : 0 < x_val := by rw [hx_def]; linarith
  have h_x_lt_y_hi : x_val < (2 : ℝ)^(e + 2) := by rw [hx_def]; linarith
  have h_y_hi_coe : ((y_hi_g e : Dyadic) : ℝ) = (2 : ℝ)^(e + 2) := coe_y_hi_g e
  set n : ℕ := (e + 2 - f₂).toNat with hn_def
  have h_2e2_eq : (2 : ℝ)^(e + 2) = ((2 : ℤ)^n : ℝ) * (2 : ℝ)^f₂ :=
    two_zpow_split (e + 2) f₂ hf₂_le_e2
  have h_F₂_lt_y_hi_bound : ∀ z ∈ F₂.toFormat, ((z : Dyadic) : ℝ) < (2 : ℝ)^(e + 2) →
      ((z : Dyadic) : ℝ) ≤ (2 : ℝ)^(e + 2) - (2 : ℝ)^f₂ := by
    have h_target_eq : (2 : ℝ)^(e + 2) - (2 : ℝ)^f₂
        = (((2 : ℤ)^n - 1 : ℤ) : ℝ) * (2 : ℝ) ^ f₂ := by
      push_cast; rw [h_2e2_eq]; ring
    intro z hz hz_lt
    apply F₂_grid_floor hF₂_exp h_target_eq z hz
    linarith
  refine ⟨x_val, y_hi_g e, y_hi_g e, ?_, ?_, ?_⟩
  · refine ⟨h_y_hi_in_F₂, ?_, ?_, ?_⟩
    · rw [h_y_hi_coe, abs_of_pos h_2e2_pos, abs_of_pos h_x_pos]; linarith
    · rw [h_y_hi_coe]; positivity
    · intro z hz hz_bnd hz_sign
      have h_z_nn : 0 ≤ ((z : Dyadic) : ℝ) := nonneg_of_mul_nonneg_pos hz_sign h_x_pos
      rw [abs_of_nonneg h_z_nn, abs_of_pos h_x_pos] at hz_bnd
      rw [h_y_hi_coe, abs_of_pos h_2e2_pos, abs_of_nonneg h_z_nn]
      by_contra h_lt
      push Not at h_lt
      have h_z_pred := h_F₂_lt_y_hi_bound z hz h_lt
      have h_2f2_lt_2f : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^f₂ :=
        zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < f₂)
      rw [hx_def] at hz_bnd
      linarith
  · exact rounds_RTO_self h_y_hi_in_F₁
  · intro hr
    obtain ⟨_, _, h_parity⟩ := hr
    have h_x_ne_y_hi : x_val ≠ ((y_hi_g e : Dyadic) : ℝ) := by
      rw [h_y_hi_coe, hx_def]; linarith
    obtain ⟨F', hF'_eq, hF'_odd⟩ := h_parity h_x_ne_y_hi
    have : (F₁_g p hp_ge_2 e).IsOdd (y_hi_g e) :=
      isOdd_transfer_toFormat hF'_eq hF'_odd
    exact notIsOdd_F₁_g_y_hi p hp_ge_2 e this

/-- **Counterexample to `rndRNE_RTO`.** -/
theorem no_rndRNE_RTO
    (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    (F₂ : FiniteFormat) (hsub : (F₁_g p hp_ge_2 e).toFormat ⊆ F₂.toFormat)
    (hF₂_exp_fin : F₂.toFormat.exp ≠ ⊥) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ (.nearest .toEven) x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .toOdd (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .toOdd x w := by
  obtain ⟨f₂, hf₂_eq⟩ := WithBot.ne_bot_iff_exists.mp hF₂_exp_fin
  have hF₂_exp : F₂.toFormat.exp = (f₂ : WithBot ℤ) := hf₂_eq.symm
  have h_y_hi_in_F₁ := y_hi_mem_F₁_g p hp_ge_2 e
  have h_y_hi_in_F₂ : y_hi_g e ∈ F₂.toFormat := hsub _ h_y_hi_in_F₁
  have hf₂_le_e : f₂ ≤ e := f₂_le_e_of_F₁_g_subset p hp_ge_2 e F₂.toFormat hsub hF₂_exp
  have hf₂_le_e2 : f₂ ≤ e + 2 := by omega
  set x_val : ℝ := (2 : ℝ)^(e + 2) - (2 : ℝ)^(f₂ - 2) with hx_def
  have h_2e2_pos : (0 : ℝ) < (2 : ℝ)^(e + 2) := zpow_pos (by norm_num) _
  have h_2f2_pos : (0 : ℝ) < (2 : ℝ)^(f₂ - 2) := zpow_pos (by norm_num) _
  have h_2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
  have h_2f2_lt_2e2 : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^(e + 2) :=
    zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < e + 2)
  have h_x_pos : 0 < x_val := by rw [hx_def]; linarith
  have h_x_lt_y_hi : x_val < (2 : ℝ)^(e + 2) := by rw [hx_def]; linarith
  have h_y_hi_coe : ((y_hi_g e : Dyadic) : ℝ) = (2 : ℝ)^(e + 2) := coe_y_hi_g e
  set n : ℕ := (e + 2 - f₂).toNat with hn_def
  have h_2e2_eq : (2 : ℝ)^(e + 2) = ((2 : ℤ)^n : ℝ) * (2 : ℝ)^f₂ :=
    two_zpow_split (e + 2) f₂ hf₂_le_e2
  have h_2f_split : (2 : ℝ)^f₂ = 4 * (2 : ℝ)^(f₂ - 2) := two_zpow_split_minus_two f₂
  have h_F₂_lt_y_hi_bound : ∀ z ∈ F₂.toFormat, ((z : Dyadic) : ℝ) < (2 : ℝ)^(e + 2) →
      ((z : Dyadic) : ℝ) ≤ (2 : ℝ)^(e + 2) - (2 : ℝ)^f₂ := by
    have h_target_eq : (2 : ℝ)^(e + 2) - (2 : ℝ)^f₂
        = (((2 : ℤ)^n - 1 : ℤ) : ℝ) * (2 : ℝ) ^ f₂ := by
      push_cast; rw [h_2e2_eq]; ring
    intro z hz hz_lt
    apply F₂_grid_floor hF₂_exp h_target_eq z hz
    linarith
  have h_F₂_ge_x_to_ge_y_hi : ∀ z ∈ F₂.toFormat, x_val ≤ ((z : Dyadic) : ℝ) →
      (2 : ℝ)^(e + 2) ≤ ((z : Dyadic) : ℝ) := by
    intro z hz hz_ge
    by_contra h_lt
    push Not at h_lt
    have h_z_bnd := h_F₂_lt_y_hi_bound z hz h_lt
    have h_2f2_lt_2f : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^f₂ :=
      zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < f₂)
    linarith
  refine ⟨x_val, y_hi_g e, y_hi_g e, ?_, ?_, ?_⟩
  · refine ⟨h_y_hi_in_F₂, ?_, ?_, ?_⟩
    · right
      refine ⟨h_y_hi_in_F₂, ?_, ?_⟩
      · rw [h_y_hi_coe]; linarith
      · intro z hz hz_ge
        rw [h_y_hi_coe]
        exact h_F₂_ge_x_to_ge_y_hi z hz hz_ge
    · intro z hz hf
      rw [h_y_hi_coe]
      rcases hf with ⟨_, hz_le, _⟩ | ⟨_, hz_ge, _⟩
      · have h_z_lt_y_hi : (z : ℝ) < (2 : ℝ)^(e + 2) := lt_of_le_of_lt hz_le h_x_lt_y_hi
        have h_z_bnd := h_F₂_lt_y_hi_bound z hz h_z_lt_y_hi
        rw [abs_of_neg (by rw [hx_def]; linarith : x_val - (2 : ℝ)^(e + 2) < 0), neg_sub]
        rw [abs_of_nonneg (by rw [hx_def]; linarith : (0 : ℝ) ≤ x_val - (z : ℝ))]
        rw [h_2f_split] at h_z_bnd
        rw [hx_def]; linarith
      · have h_z_ge_y_hi := h_F₂_ge_x_to_ge_y_hi z hz hz_ge
        rw [abs_of_neg (by rw [hx_def]; linarith : x_val - (2 : ℝ)^(e + 2) < 0), neg_sub]
        rw [abs_of_nonpos (by linarith : x_val - (z : ℝ) ≤ 0), neg_sub]
        linarith
    · rintro ⟨z, hzF₂, hf, hne, heq⟩
      rw [h_y_hi_coe] at heq
      rcases hf with ⟨_, hz_le, _⟩ | ⟨_, hz_ge, _⟩
      · exfalso
        have h_z_lt_y_hi : (z : ℝ) < (2 : ℝ)^(e + 2) := lt_of_le_of_lt hz_le h_x_lt_y_hi
        have h_z_bnd := h_F₂_lt_y_hi_bound z hzF₂ h_z_lt_y_hi
        rw [abs_of_neg (by rw [hx_def]; linarith : x_val - (2 : ℝ)^(e + 2) < 0), neg_sub] at heq
        rw [abs_of_nonneg (by rw [hx_def]; linarith : (0 : ℝ) ≤ x_val - (z : ℝ))] at heq
        rw [h_2f_split] at h_z_bnd
        rw [hx_def] at heq
        linarith
      · exfalso
        have h_z_ge_y_hi := h_F₂_ge_x_to_ge_y_hi z hzF₂ hz_ge
        have h_z_ne_y_hi : (z : ℝ) ≠ (2 : ℝ)^(e + 2) := by
          intro h_eq
          apply hne
          rw [← Dyadic.coe_real_inj, h_y_hi_coe]; exact h_eq
        have h_z_gt_y_hi : (2 : ℝ)^(e + 2) < (z : ℝ) :=
          lt_of_le_of_ne h_z_ge_y_hi (Ne.symm h_z_ne_y_hi)
        have h_z_ge_y_hi_plus : (2 : ℝ)^(e + 2) + (2 : ℝ)^f₂ ≤ (z : ℝ) := by
          obtain ⟨_, hq, _⟩ := hzF₂
          rw [hF₂_exp, Dyadic.quantumAtLeast_coe_real] at hq
          obtain ⟨c, hc⟩ := hq
          rw [hc] at h_z_gt_y_hi ⊢
          rw [h_2e2_eq] at h_z_gt_y_hi
          have hc_gt : ((2 : ℤ)^n : ℝ) < (c : ℝ) :=
            lt_of_mul_lt_mul_right h_z_gt_y_hi h_2f_pos.le
          have hc_int_gt : (2 : ℤ)^n < c := by exact_mod_cast hc_gt
          have hc_int_ge : (2 : ℤ)^n + 1 ≤ c := by omega
          have hc_real_ge : ((2 : ℤ)^n : ℝ) + 1 ≤ (c : ℝ) := by
            have h1 : (((2 : ℤ)^n + 1 : ℤ) : ℝ) ≤ ((c : ℤ) : ℝ) := by exact_mod_cast hc_int_ge
            push_cast at h1; exact h1
          have h_mul : (((2 : ℤ)^n : ℝ) + 1) * (2 : ℝ)^f₂ ≤ (c : ℝ) * (2 : ℝ)^f₂ :=
            mul_le_mul_of_nonneg_right hc_real_ge h_2f_pos.le
          rw [h_2e2_eq]
          linarith
        rw [abs_of_neg (by rw [hx_def]; linarith : x_val - (2 : ℝ)^(e + 2) < 0), neg_sub] at heq
        rw [abs_of_nonpos (by linarith : x_val - (z : ℝ) ≤ 0), neg_sub] at heq
        rw [hx_def] at heq; linarith
  · exact rounds_RTO_self h_y_hi_in_F₁
  · intro hr
    obtain ⟨_, _, h_parity⟩ := hr
    have h_x_ne_y_hi : x_val ≠ ((y_hi_g e : Dyadic) : ℝ) := by
      rw [h_y_hi_coe, hx_def]; linarith
    obtain ⟨F', hF'_eq, hF'_odd⟩ := h_parity h_x_ne_y_hi
    have : (F₁_g p hp_ge_2 e).IsOdd (y_hi_g e) :=
      isOdd_transfer_toFormat hF'_eq hF'_odd
    exact notIsOdd_F₁_g_y_hi p hp_ge_2 e this

/-- **Counterexample to `rndRTZ_RTO`.** -/
theorem no_rndRTZ_RTO
    (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    (F₂ : FiniteFormat) (hsub : (F₁_g p hp_ge_2 e).toFormat ⊆ F₂.toFormat)
    (hF₂_exp_fin : F₂.toFormat.exp ≠ ⊥) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .toZero x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .toOdd (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .toOdd x w := by
  obtain ⟨f₂, hf₂_eq⟩ := WithBot.ne_bot_iff_exists.mp hF₂_exp_fin
  have hF₂_exp : F₂.toFormat.exp = (f₂ : WithBot ℤ) := hf₂_eq.symm
  have h_y_hi_in_F₁ := y_hi_mem_F₁_g p hp_ge_2 e
  have h_y_hi_in_F₂ : y_hi_g e ∈ F₂.toFormat := hsub _ h_y_hi_in_F₁
  have hf₂_le_e : f₂ ≤ e := f₂_le_e_of_F₁_g_subset p hp_ge_2 e F₂.toFormat hsub hF₂_exp
  have hf₂_le_e2 : f₂ ≤ e + 2 := by omega
  set x_val : ℝ := (2 : ℝ)^(e + 2) + (2 : ℝ)^(f₂ - 2) with hx_def
  have h_2e2_pos : (0 : ℝ) < (2 : ℝ)^(e + 2) := zpow_pos (by norm_num) _
  have h_2f2_pos : (0 : ℝ) < (2 : ℝ)^(f₂ - 2) := zpow_pos (by norm_num) _
  have h_2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
  have h_x_pos : 0 < x_val := by rw [hx_def]; linarith
  have h_x_gt_y_hi : (2 : ℝ)^(e + 2) < x_val := by rw [hx_def]; linarith
  have h_y_hi_coe : ((y_hi_g e : Dyadic) : ℝ) = (2 : ℝ)^(e + 2) := coe_y_hi_g e
  set n : ℕ := (e + 2 - f₂).toNat with hn_def
  have h_2e2_eq : (2 : ℝ)^(e + 2) = ((2 : ℤ)^n : ℝ) * (2 : ℝ)^f₂ :=
    two_zpow_split (e + 2) f₂ hf₂_le_e2
  have h_F₂_le_x_to_le_y_hi : ∀ z ∈ F₂.toFormat, ((z : Dyadic) : ℝ) ≤ x_val →
      ((z : Dyadic) : ℝ) ≤ (2 : ℝ)^(e + 2) := by
    have h_2f2_lt_2f : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^f₂ :=
      zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < f₂)
    have h_target_eq : (2 : ℝ)^(e + 2) = (((2 : ℤ)^n : ℤ) : ℝ) * (2 : ℝ) ^ f₂ := by
      push_cast; exact h_2e2_eq
    intro z hz hz_le
    apply F₂_grid_floor hF₂_exp h_target_eq z hz
    rw [hx_def] at hz_le; linarith
  refine ⟨x_val, y_hi_g e, y_hi_g e, ?_, ?_, ?_⟩
  · refine ⟨h_y_hi_in_F₂, ?_, ?_, ?_⟩
    · rw [h_y_hi_coe, abs_of_pos h_2e2_pos, abs_of_pos h_x_pos]; linarith
    · rw [h_y_hi_coe]; positivity
    · intro z hz hz_bnd hz_sign
      have h_z_nn : 0 ≤ ((z : Dyadic) : ℝ) := nonneg_of_mul_nonneg_pos hz_sign h_x_pos
      rw [abs_of_nonneg h_z_nn, abs_of_pos h_x_pos] at hz_bnd
      rw [h_y_hi_coe, abs_of_pos h_2e2_pos, abs_of_nonneg h_z_nn]
      exact h_F₂_le_x_to_le_y_hi z hz hz_bnd
  · exact rounds_RTO_self h_y_hi_in_F₁
  · intro hr
    obtain ⟨_, _, h_parity⟩ := hr
    have h_x_ne_y_hi : x_val ≠ ((y_hi_g e : Dyadic) : ℝ) := by
      rw [h_y_hi_coe, hx_def]; linarith
    obtain ⟨F', hF'_eq, hF'_odd⟩ := h_parity h_x_ne_y_hi
    have : (F₁_g p hp_ge_2 e).IsOdd (y_hi_g e) :=
      isOdd_transfer_toFormat hF'_eq hF'_odd
    exact notIsOdd_F₁_g_y_hi p hp_ge_2 e this

/-- **Counterexample to `rndRAZ_RNE`.** -/
theorem no_rndRAZ_RNE
    (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    (F₂ : FiniteFormat) (hm_in_F₂ : m_g e ∈ F₂.toFormat)
    (hF₂_exp_fin : F₂.toFormat.exp ≠ ⊥) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .awayZero x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat (.nearest .toEven) (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat (.nearest .toEven) x w := by
  obtain ⟨f₂, hf₂_eq⟩ := WithBot.ne_bot_iff_exists.mp hF₂_exp_fin
  have hF₂_exp : F₂.toFormat.exp = (f₂ : WithBot ℤ) := hf₂_eq.symm
  have hf₂_le_e1 : f₂ ≤ e - 1 :=
    f₂_le_e_sub_one_of_odd_in_F₂ hF₂_exp hm_in_F₂ (by decide : Odd (7 : ℤ))
      (by rw [coe_m_g]; push_cast; ring)
  have h_y_lo_in_F₁ := y_lo_mem_F₁_g p hp_ge_2 e
  have h_y_hi_in_F₁ := y_hi_mem_F₁_g p hp_ge_2 e
  set m : Dyadic := m_g e with hm_def
  have h_m_in_F₂ : m ∈ F₂.toFormat := hm_in_F₂
  have h_m_coe : (m : ℝ) = 7 * (2 : ℝ)^(e - 1) := coe_m_g e
  have h_2e1_pos : (0 : ℝ) < (2 : ℝ)^(e - 1) := zpow_pos (by norm_num) _
  have h_m_pos : 0 < (m : ℝ) := by rw [h_m_coe]; nlinarith
  set x_val : ℝ := (m : ℝ) - (2 : ℝ)^(f₂ - 2) with hx_def
  have h_2f2_pos : (0 : ℝ) < (2 : ℝ)^(f₂ - 2) := zpow_pos (by norm_num) _
  have h_2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
  have h_2f2_lt_2e1 : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^(e - 1) :=
    zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < e - 1)
  have h_2f2_lt_2f : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^f₂ :=
    zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < f₂)
  have h_x_lt_m : x_val < (m : ℝ) := by rw [hx_def]; linarith
  have h_x_pos : 0 < x_val := by
    rw [hx_def, h_m_coe]; nlinarith
  set n : ℕ := (e - 1 - f₂).toNat with hn_def
  have h_m_grid : (m : ℝ) = ((7 * (2 : ℤ)^n : ℤ) : ℝ) * (2 : ℝ)^f₂ := by
    have h_split : (2 : ℝ)^(e - 1) = ((2 : ℤ)^n : ℝ) * (2 : ℝ)^f₂ :=
      two_zpow_split (e - 1) f₂ hf₂_le_e1
    rw [h_m_coe, h_split]; push_cast; ring
  have h_F₂_lt_m_bound : ∀ z ∈ F₂.toFormat, ((z : Dyadic) : ℝ) < (m : ℝ) →
      ((z : Dyadic) : ℝ) ≤ (m : ℝ) - (2 : ℝ)^f₂ := by
    have h_target_eq : (m : ℝ) - (2 : ℝ)^f₂
        = (((7 * (2 : ℤ)^n - 1 : ℤ) : ℤ) : ℝ) * (2 : ℝ) ^ f₂ := by
      push_cast; rw [h_m_grid]; push_cast; ring
    intro z hz hz_lt
    apply F₂_grid_floor hF₂_exp h_target_eq z hz
    linarith
  have h_y_lo_coe : ((y_lo_g e : Dyadic) : ℝ) = 3 * (2 : ℝ)^e := coe_y_lo_g e
  have h_y_hi_coe : ((y_hi_g e : Dyadic) : ℝ) = (2 : ℝ)^(e + 2) := coe_y_hi_g e
  have h_y_lo_eq : ((y_lo_g e : Dyadic) : ℝ) = (m : ℝ) - (2 : ℝ)^(e - 1) := by
    rw [h_y_lo_coe, h_m_coe]
    have h_split : (2 : ℝ)^e = (2 : ℝ)^(e - 1) * (2 : ℝ)^(1 : ℤ) := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
    rw [h_split, show (2 : ℝ)^(1 : ℤ) = 2 by norm_num]; ring
  have h_y_hi_eq : ((y_hi_g e : Dyadic) : ℝ) = (m : ℝ) + (2 : ℝ)^(e - 1) := by
    rw [h_y_hi_coe, h_m_coe]
    rw [show e + 2 = (e - 1) + 3 by ring, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [show (2 : ℝ)^(3 : ℤ) = 8 by norm_num]; ring
  refine ⟨x_val, m, y_hi_g e, ?_, ?_, ?_⟩
  · refine ⟨h_m_in_F₂, ?_, ?_, ?_⟩
    · rw [abs_of_pos h_m_pos, abs_of_pos h_x_pos]; linarith
    · positivity
    · intro z hz hz_bnd hz_sign
      have h_z_nn : 0 ≤ ((z : Dyadic) : ℝ) := nonneg_of_mul_nonneg_pos hz_sign h_x_pos
      rw [abs_of_nonneg h_z_nn, abs_of_pos h_x_pos] at hz_bnd
      rw [abs_of_pos h_m_pos, abs_of_nonneg h_z_nn]
      by_contra h_lt
      push Not at h_lt
      have h_z_pred := h_F₂_lt_m_bound z hz h_lt
      rw [hx_def] at hz_bnd
      linarith
  · exact rounds_F₁_g_RNE_m_y_hi p hp_ge_2 e
  · intro hr
    obtain ⟨_, _, h_close, _⟩ := hr
    have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
    have h_y_lo_faith : IsFaithfulRound (F₁_g p hp_ge_2 e).toFiniteFormat x_val (y_lo_g e) := by
      left
      refine ⟨h_y_lo_in_F₁, ?_, ?_⟩
      · rw [h_y_lo_eq, hx_def]; linarith
      · intro z hz hz_le
        obtain ⟨c', hc'⟩ := F₁_g_quantum p hp_ge_2 e hz
        have h_z_lt_m : (z : ℝ) < (m : ℝ) := lt_of_le_of_lt hz_le h_x_lt_m
        rw [hc', h_m_coe] at h_z_lt_m
        have h_7_2 : (7 : ℝ) * (2 : ℝ)^(e-1) = (7/2) * (2 : ℝ)^e := by
          rw [show (e-1 : ℤ) = e + (-1 : ℤ) from by ring,
              zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          rw [show (2 : ℝ)^(-1 : ℤ) = 1/2 by
            rw [show ((-1 : ℤ)) = -(1 : ℤ) from by ring, zpow_neg]; norm_num]
          ring
        rw [h_7_2] at h_z_lt_m
        have hc'_r_lt : (c' : ℝ) < 7/2 := lt_of_mul_lt_mul_right h_z_lt_m h_2e_pos.le
        have hc'_lt_4 : (c' : ℝ) < 4 := by linarith
        have : c' < 4 := by exact_mod_cast hc'_lt_4
        have hc'_le_3 : c' ≤ 3 := by omega
        change (z : ℝ) ≤ ((y_lo_g e : Dyadic) : ℝ)
        rw [hc', h_y_lo_coe]
        have : (c' : ℝ) ≤ 3 := by exact_mod_cast hc'_le_3
        nlinarith
    have h_close_lo := h_close (y_lo_g e) h_y_lo_in_F₁ h_y_lo_faith
    rw [h_y_hi_eq, h_y_lo_eq, hx_def] at h_close_lo
    have h_abs_hi : |((m : ℝ) - (2 : ℝ)^(f₂ - 2)) - ((m : ℝ) + (2 : ℝ)^(e - 1))| =
        (2 : ℝ)^(e - 1) + (2 : ℝ)^(f₂ - 2) := by
      rw [show (m : ℝ) - (2 : ℝ)^(f₂ - 2) - ((m : ℝ) + (2 : ℝ)^(e - 1)) =
          -((2 : ℝ)^(e - 1) + (2 : ℝ)^(f₂ - 2)) from by ring]
      rw [abs_neg, abs_of_pos (by linarith : 0 < (2 : ℝ)^(e - 1) + (2 : ℝ)^(f₂ - 2))]
    have h_abs_lo : |((m : ℝ) - (2 : ℝ)^(f₂ - 2)) - ((m : ℝ) - (2 : ℝ)^(e - 1))| =
        (2 : ℝ)^(e - 1) - (2 : ℝ)^(f₂ - 2) := by
      rw [show (m : ℝ) - (2 : ℝ)^(f₂ - 2) - ((m : ℝ) - (2 : ℝ)^(e - 1)) =
          (2 : ℝ)^(e - 1) - (2 : ℝ)^(f₂ - 2) from by ring]
      exact abs_of_pos (by linarith)
    rw [h_abs_hi, h_abs_lo] at h_close_lo
    linarith

/-- **Counterexample to `rndRTZ_RNE`.** -/
theorem no_rndRTZ_RNE
    (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    (F₂ : FiniteFormat) (hm_low_in_F₂ : m_low_g e ∈ F₂.toFormat)
    (hF₂_exp_fin : F₂.toFormat.exp ≠ ⊥) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .toZero x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat (.nearest .toEven) (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat (.nearest .toEven) x w := by
  obtain ⟨f₂, hf₂_eq⟩ := WithBot.ne_bot_iff_exists.mp hF₂_exp_fin
  have hF₂_exp : F₂.toFormat.exp = (f₂ : WithBot ℤ) := hf₂_eq.symm
  have hf₂_le_e1 : f₂ ≤ e - 1 :=
    f₂_le_e_sub_one_of_odd_in_F₂ hF₂_exp hm_low_in_F₂ (by decide : Odd (5 : ℤ))
      (by rw [coe_m_low_g]; push_cast; ring)
  have h_y_lo_low_in_F₁ := y_lo_low_mem_F₁_g p hp_ge_2 e
  have h_y_lo_in_F₁ := y_lo_mem_F₁_g p hp_ge_2 e
  set m_low : Dyadic := m_low_g e with hm_low_def
  have h_m_low_in_F₂ : m_low ∈ F₂.toFormat := hm_low_in_F₂
  have h_m_low_coe : (m_low : ℝ) = 5 * (2 : ℝ)^(e - 1) := coe_m_low_g e
  have h_2e1_pos : (0 : ℝ) < (2 : ℝ)^(e - 1) := zpow_pos (by norm_num) _
  have h_m_low_pos : 0 < (m_low : ℝ) := by rw [h_m_low_coe]; nlinarith
  set x_val : ℝ := (m_low : ℝ) + (2 : ℝ)^(f₂ - 2) with hx_def
  have h_2f2_pos : (0 : ℝ) < (2 : ℝ)^(f₂ - 2) := zpow_pos (by norm_num) _
  have h_2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
  have h_2f2_lt_2e1 : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^(e - 1) :=
    zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < e - 1)
  have h_2f2_lt_2f : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^f₂ :=
    zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < f₂)
  have h_x_gt_m_low : (m_low : ℝ) < x_val := by rw [hx_def]; linarith
  have h_x_pos : 0 < x_val := by linarith
  set n : ℕ := (e - 1 - f₂).toNat with hn_def
  have h_m_low_grid : (m_low : ℝ) = ((5 * (2 : ℤ)^n : ℤ) : ℝ) * (2 : ℝ)^f₂ := by
    have h_split : (2 : ℝ)^(e - 1) = ((2 : ℤ)^n : ℝ) * (2 : ℝ)^f₂ :=
      two_zpow_split (e - 1) f₂ hf₂_le_e1
    rw [h_m_low_coe, h_split]; push_cast; ring
  have h_F₂_le_x_to_le_m_low : ∀ z ∈ F₂.toFormat, ((z : Dyadic) : ℝ) ≤ x_val →
      ((z : Dyadic) : ℝ) ≤ (m_low : ℝ) := by
    have h_target_eq : (m_low : ℝ) = ((5 * (2 : ℤ)^n : ℤ) : ℝ) * (2 : ℝ) ^ f₂ :=
      h_m_low_grid
    intro z hz hz_le
    apply F₂_grid_floor hF₂_exp h_target_eq z hz
    rw [hx_def] at hz_le; linarith
  have h_y_lo_low_coe : ((y_lo_low_g e : Dyadic) : ℝ) = 2 * (2 : ℝ)^e := coe_y_lo_low_g e
  have h_y_lo_coe : ((y_lo_g e : Dyadic) : ℝ) = 3 * (2 : ℝ)^e := coe_y_lo_g e
  have h_y_lo_low_eq : ((y_lo_low_g e : Dyadic) : ℝ) = (m_low : ℝ) - (2 : ℝ)^(e - 1) := by
    rw [h_y_lo_low_coe, h_m_low_coe]
    have h_split : (2 : ℝ)^e = (2 : ℝ)^(e - 1) * (2 : ℝ)^(1 : ℤ) := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
    rw [h_split, show (2 : ℝ)^(1 : ℤ) = 2 by norm_num]; ring
  have h_y_lo_eq : ((y_lo_g e : Dyadic) : ℝ) = (m_low : ℝ) + (2 : ℝ)^(e - 1) := by
    rw [h_y_lo_coe, h_m_low_coe]
    have h_split : (2 : ℝ)^e = (2 : ℝ)^(e - 1) * (2 : ℝ)^(1 : ℤ) := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
    rw [h_split, show (2 : ℝ)^(1 : ℤ) = 2 by norm_num]; ring
  refine ⟨x_val, m_low, y_lo_low_g e, ?_, ?_, ?_⟩
  · refine ⟨h_m_low_in_F₂, ?_, ?_, ?_⟩
    · rw [abs_of_pos h_m_low_pos, abs_of_pos h_x_pos]; linarith
    · positivity
    · intro z hz hz_bnd hz_sign
      have h_z_nn : 0 ≤ ((z : Dyadic) : ℝ) := nonneg_of_mul_nonneg_pos hz_sign h_x_pos
      rw [abs_of_nonneg h_z_nn, abs_of_pos h_x_pos] at hz_bnd
      rw [abs_of_pos h_m_low_pos, abs_of_nonneg h_z_nn]
      exact h_F₂_le_x_to_le_m_low z hz hz_bnd
  · exact rounds_F₁_g_RNE_m_low_y_lo_low p hp_ge_2 e
  · intro hr
    obtain ⟨_, _, h_close, _⟩ := hr
    have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
    have h_y_lo_faith : IsFaithfulRound (F₁_g p hp_ge_2 e).toFiniteFormat x_val (y_lo_g e) := by
      right
      refine ⟨h_y_lo_in_F₁, ?_, ?_⟩
      · rw [h_y_lo_eq, hx_def]; linarith
      · intro z hz hz_ge
        obtain ⟨c', hc'⟩ := F₁_g_quantum p hp_ge_2 e hz
        have h_z_gt_m_low : (m_low : ℝ) < (z : ℝ) := lt_of_lt_of_le h_x_gt_m_low hz_ge
        rw [hc', h_m_low_coe] at h_z_gt_m_low
        have h_5_2 : (5 : ℝ) * (2 : ℝ)^(e-1) = (5/2) * (2 : ℝ)^e := by
          rw [show (e-1 : ℤ) = e + (-1 : ℤ) from by ring,
              zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          rw [show (2 : ℝ)^(-1 : ℤ) = 1/2 by
            rw [show ((-1 : ℤ)) = -(1 : ℤ) from by ring, zpow_neg]; norm_num]
          ring
        rw [h_5_2] at h_z_gt_m_low
        have hc'_r_gt : (5/2 : ℝ) < (c' : ℝ) := lt_of_mul_lt_mul_right h_z_gt_m_low h_2e_pos.le
        have hc'_gt_2 : (2 : ℝ) < (c' : ℝ) := by linarith
        have : 2 < c' := by exact_mod_cast hc'_gt_2
        have hc'_ge_3 : 3 ≤ c' := by omega
        change ((y_lo_g e : Dyadic) : ℝ) ≤ (z : ℝ)
        rw [hc', h_y_lo_coe]
        have : (3 : ℝ) ≤ (c' : ℝ) := by exact_mod_cast hc'_ge_3
        nlinarith
    have h_close_lo := h_close (y_lo_g e) h_y_lo_in_F₁ h_y_lo_faith
    rw [h_y_lo_low_eq, h_y_lo_eq, hx_def] at h_close_lo
    have h_abs_low : |((m_low : ℝ) + (2 : ℝ)^(f₂ - 2)) - ((m_low : ℝ) - (2 : ℝ)^(e - 1))| =
        (2 : ℝ)^(e - 1) + (2 : ℝ)^(f₂ - 2) := by
      rw [show (m_low : ℝ) + (2 : ℝ)^(f₂ - 2) - ((m_low : ℝ) - (2 : ℝ)^(e - 1)) =
          (2 : ℝ)^(e - 1) + (2 : ℝ)^(f₂ - 2) from by ring]
      exact abs_of_pos (by linarith)
    have h_abs_hi : |((m_low : ℝ) + (2 : ℝ)^(f₂ - 2)) - ((m_low : ℝ) + (2 : ℝ)^(e - 1))| =
        (2 : ℝ)^(e - 1) - (2 : ℝ)^(f₂ - 2) := by
      rw [show (m_low : ℝ) + (2 : ℝ)^(f₂ - 2) - ((m_low : ℝ) + (2 : ℝ)^(e - 1)) =
          -((2 : ℝ)^(e - 1) - (2 : ℝ)^(f₂ - 2)) from by ring]
      rw [abs_neg]; exact abs_of_pos (by linarith)
    rw [h_abs_low, h_abs_hi] at h_close_lo
    linarith

end ParityFormat

end Mpfx
