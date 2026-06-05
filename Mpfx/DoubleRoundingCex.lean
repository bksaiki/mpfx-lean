import Mpfx.Rounding
import Mpfx.Grid
import Mpfx.Digits
import Mpfx.RoundOp

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

namespace Cex

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
    (F₁_g p hp e).p = ((p : ℕ+) : WithTop ℕ+) := rfl

@[simp] theorem F₁_g_exp (p : ℕ+) (hp : 2 ≤ (p : ℕ)) (e : ℤ) :
    (F₁_g p hp e).exp = (e : WithBot ℤ) := rfl

@[simp] theorem F₁_g_b (p : ℕ+) (hp : 2 ≤ (p : ℕ)) (e : ℤ) :
    (F₁_g p hp e).b = ⊤ := rfl

/-! ### The grid witnesses (as `Dyadic.ofIntZpow`) -/

private noncomputable def y_lo_g (e : ℤ) : Dyadic := Dyadic.ofIntZpow 3 e
private noncomputable def y_hi_g (e : ℤ) : Dyadic := Dyadic.ofIntZpow 1 (e + 2)

/-- `2^e` as a Dyadic, used as the smallest positive F₁_g-element witness. -/
private noncomputable def two_e_g (e : ℤ) : Dyadic := Dyadic.ofIntZpow 1 e

private noncomputable def m_g (e : ℤ) : Dyadic := Dyadic.ofIntZpow 7 (e - 1)

private noncomputable def y_lo_low_g (e : ℤ) : Dyadic := Dyadic.ofIntZpow 2 e

private noncomputable def m_low_g (e : ℤ) : Dyadic := Dyadic.ofIntZpow 5 (e - 1)

private theorem coe_y_lo_g (e : ℤ) : ((y_lo_g e : Dyadic) : ℝ) = 3 * (2 : ℝ)^e := by
  change ((Dyadic.ofIntZpow 3 e : Dyadic) : ℝ) = _
  rw [Dyadic.coe_ofIntZpow]; push_cast; ring

private theorem coe_y_hi_g (e : ℤ) :
    ((y_hi_g e : Dyadic) : ℝ) = (2 : ℝ)^(e + 2) := by
  change ((Dyadic.ofIntZpow 1 (e + 2) : Dyadic) : ℝ) = _
  rw [Dyadic.coe_ofIntZpow]; push_cast; ring

private theorem coe_two_e_g (e : ℤ) : ((two_e_g e : Dyadic) : ℝ) = (2 : ℝ)^e := by
  change ((Dyadic.ofIntZpow 1 e : Dyadic) : ℝ) = _
  rw [Dyadic.coe_ofIntZpow]; push_cast; ring

private theorem coe_m_g (e : ℤ) : ((m_g e : Dyadic) : ℝ) = 7 * (2 : ℝ)^(e - 1) := by
  change ((Dyadic.ofIntZpow 7 (e - 1) : Dyadic) : ℝ) = _
  rw [Dyadic.coe_ofIntZpow]; push_cast; ring

private theorem coe_y_lo_low_g (e : ℤ) :
    ((y_lo_low_g e : Dyadic) : ℝ) = 2 * (2 : ℝ)^e := by
  change ((Dyadic.ofIntZpow 2 e : Dyadic) : ℝ) = _
  rw [Dyadic.coe_ofIntZpow]; push_cast; ring

private theorem coe_m_low_g (e : ℤ) :
    ((m_low_g e : Dyadic) : ℝ) = 5 * (2 : ℝ)^(e - 1) := by
  change ((Dyadic.ofIntZpow 5 (e - 1) : Dyadic) : ℝ) = _
  rw [Dyadic.coe_ofIntZpow]; push_cast; ring

/-! ### Membership lemmas -/

private theorem y_lo_mem_F₁_g (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ) :
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

private theorem two_e_mem_F₁_g (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ) :
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

/-- `2^N ∈ F₁_g` for any `N ≥ e`: precision `1 ≤ p`, quantum `N ≥ e`. The
gadget therefore contains arbitrarily large elements. -/
private theorem zpow_mem_F₁_g (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    {N : ℤ} (hN : e ≤ N) :
    Dyadic.ofIntZpow 1 N ∈ (F₁_g p hp_ge_2 e).toFormat := by
  have h_real : ((Dyadic.ofIntZpow 1 N : Dyadic) : ℝ) = (2 : ℝ)^N := by
    rw [Dyadic.coe_ofIntZpow]; push_cast; ring
  refine ⟨?_, ?_, trivial⟩
  · change Dyadic.precisionAtMost ((p : ℕ+) : WithTop ℕ+) _
    rw [Dyadic.precisionAtMost_coe_real]
    refine ⟨1, N, by rw [h_real]; push_cast; ring, ?_⟩
    have h_pow : (2 : ℤ) ≤ (2 : ℤ)^(p : ℕ) :=
      calc (2 : ℤ) = (2 : ℤ)^1 := by norm_num
        _ ≤ (2 : ℤ)^(p : ℕ) := pow_le_pow_right₀ (by norm_num) (by omega)
    have : |(1 : ℤ)| = 1 := by decide
    omega
  · change Dyadic.quantumAtLeast ((e : ℤ) : WithBot ℤ) _
    rw [Dyadic.quantumAtLeast_coe_real]
    refine ⟨(2 : ℤ)^(N - e).toNat, ?_⟩
    rw [h_real, two_zpow_split N e hN]
    push_cast; ring

private theorem y_hi_mem_F₁_g (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ) :
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

private theorem y_lo_low_mem_F₁_g (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ) :
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
private theorem F₁_g_quantum (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    {z : Dyadic} (hz : z ∈ (F₁_g p hp_ge_2 e).toFormat) :
    ∃ c : ℤ, (z : ℝ) = (c : ℝ) * (2 : ℝ)^e := by
  have hq : Dyadic.quantumAtLeast ((e : ℤ) : WithBot ℤ) z := hz.2.1
  rw [Dyadic.quantumAtLeast_coe_real] at hq
  exact hq

/-! ## Containment → exponent helpers -/

/-- From `F₁_g ⊆ F₂` and `F₂.exp = (f₂ : WithBot ℤ)`, we have `f₂ ≤ e`. -/
private theorem f₂_le_e_of_F₁_g_subset (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
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

/-- `F₁_g ⊆ F₂` forces `F₂.b = ⊤`: the gadget contains the arbitrarily large
elements `2^N` (`zpow_mem_F₁_g`), so any finite bound on `F₂` is exceeded. -/
private theorem F₂_bound_top_of_F₁_g_subset (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    (F₂ : FiniteFormat) (hsub : (F₁_g p hp_ge_2 e).toFormat ⊆ F₂.toFormat) :
    F₂.b = ⊤ := by
  by_contra h_b_ne
  obtain ⟨b, hb_eq⟩ := WithTop.ne_top_iff_exists.mp h_b_ne
  set N : ℤ := max e (Int.log 2 ((b.val : Dyadic) : ℝ) + 1) with hN_def
  set y_huge : Dyadic := Dyadic.ofIntZpow 1 N with hy_huge_def
  have hN_ge : e ≤ N := le_max_left _ _
  have hy_huge_real : ((y_huge : Dyadic) : ℝ) = (2 : ℝ)^N := by
    rw [hy_huge_def, Dyadic.coe_ofIntZpow]; push_cast; ring
  have hy_huge_in_F₂ : y_huge ∈ F₂.toFormat :=
    hsub _ (zpow_mem_F₁_g p hp_ge_2 e hN_ge)
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
      have := Int.lt_zpow_succ_log_self (b := 2) (by norm_num : 1 < (2 : ℕ))
        ((b.val : Dyadic) : ℝ)
      rw [show ((2 : ℕ) : ℝ) = 2 from by push_cast; rfl] at this
      exact this
    have h_2N_ge : (2 : ℝ)^(Int.log 2 ((b.val : Dyadic) : ℝ) + 1) ≤ (2 : ℝ)^N :=
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hN_ge_log
    linarith
  · push Not at hb_pos
    linarith

/-- A `FiniteFormat` whose bound is already `⊤` equals its own unbounded
relaxation. Lets `rndUnbounded_satisfies` produce roundings directly against
`F₂` once `F₂_bound_top_of_F₁_g_subset` applies. -/
private theorem unbounded_eq_self {F : FiniteFormat} (hb : F.b = ⊤) :
    F.unbounded = F := by
  obtain ⟨⟨q, f, b⟩, fin⟩ := F
  have hb' : b = ⊤ := hb
  subst hb'
  rfl

/-- If an F₂-element `y` equals `odd_c · 2^(e−1)` with `odd_c` odd, then
`F₂`'s quantum exponent `f₂` satisfies `f₂ ≤ e − 1`. -/
private theorem f₂_le_e_sub_one_of_odd_in_F₂
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

/-- **F₂-grid floor.** Given `target = c_target · 2^f₂` on F₂'s grid, any
`z ∈ F₂` strictly below `target + 2^f₂` is at most `target`. -/
private theorem F₂_grid_floor
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

/-- **F₂-grid ceiling** (dual of `F₂_grid_floor`). Given
`target = c_target · 2^f₂` on F₂'s grid, any `z ∈ F₂` strictly above
`target − 2^f₂` is at least `target`. -/
private theorem F₂_grid_ceil
    {F₂ : Format} {f₂ : ℤ} (hF₂_exp : F₂.exp = (f₂ : WithBot ℤ))
    {target : ℝ} {c_target : ℤ}
    (h_target_eq : target = (c_target : ℝ) * (2 : ℝ) ^ f₂) :
    ∀ z ∈ F₂, target - (2 : ℝ)^f₂ < ((z : Dyadic) : ℝ) →
      target ≤ ((z : Dyadic) : ℝ) := by
  intro z hz hz_gt
  obtain ⟨_, hq, _⟩ := hz
  rw [hF₂_exp, Dyadic.quantumAtLeast_coe_real] at hq
  obtain ⟨c, hc⟩ := hq
  rw [hc] at hz_gt ⊢
  have h_2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
  rw [h_target_eq, show (c_target : ℝ) * (2 : ℝ)^f₂ - (2 : ℝ)^f₂
        = ((c_target - 1 : ℤ) : ℝ) * (2 : ℝ)^f₂ from by push_cast; ring] at hz_gt
  have hc_gt : ((c_target - 1 : ℤ) : ℝ) < (c : ℝ) :=
    lt_of_mul_lt_mul_right hz_gt h_2f_pos.le
  have hc_int_gt : c_target - 1 < c := by exact_mod_cast hc_gt
  have hc_int_ge : c_target ≤ c := by omega
  have hc_real_ge : (c_target : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc_int_ge
  rw [h_target_eq]
  exact mul_le_mul_of_nonneg_right hc_real_ge h_2f_pos.le

/-- RTO at an F-exact value is the identity (vacuous parity clause since
`x = y`). -/
private theorem rounds_RTO_self {F : FiniteFormat} {y : Dyadic} (h : y ∈ F) :
    RoundsFinite F .toOdd ((y : Dyadic) : ℝ) y := by
  refine ⟨h, ?_, ?_⟩
  · left
    refine ⟨h, le_refl _, ?_⟩
    intro z _ hz_le; exact hz_le
  · intro h_ne; exfalso; exact h_ne rfl

/-! ## Parity lemmas -/

/-- `IsEven F₁ (4·2^e)` for any `p ≥ 2`. -/
private theorem isEven_F₁_g_y_hi (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ) :
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
  have h_p_ne_1 : (F₁_g p hp_ge_2 e).p ≠ ((1 : ℕ+) : WithTop ℕ+) := by
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
private theorem notIsOdd_F₁_g_y_hi (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ) :
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
private theorem isEven_F₁_g_y_lo_low (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ) :
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
  have h_p_ne_1 : (F₁_g p hp_ge_2 e).p ≠ ((1 : ℕ+) : WithTop ℕ+) := by
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

/-- F₁-faithful values of any `t ∈ [2·2^e, 5·2^(e−1)]` enumerate to
`{y_lo_low, y_lo}` (= `{2·2^e, 3·2^e}`). -/
private theorem F₁_faithful_interval_lo_g (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    {t : ℝ} (h_lo : 2 * (2 : ℝ) ^ e ≤ t) (h_hi : t ≤ (5 / 2) * (2 : ℝ) ^ e)
    {z : Dyadic}
    (hf : IsFaithfulRound (F₁_g p hp_ge_2 e).toFiniteFormat t z) :
    (z : ℝ) = ((y_lo_low_g e : Dyadic) : ℝ) ∨ (z : ℝ) = ((y_lo_g e : Dyadic) : ℝ) := by
  have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
  rcases hf with ⟨hzF, hle, hmax⟩ | ⟨hzF, hge, hmin⟩
  · -- RoundDown: z is the F₁-floor of t, namely 2·2^e.
    left
    obtain ⟨c, hc⟩ := F₁_g_quantum p hp_ge_2 e hzF
    rw [hc] at hle
    have hc_r_le : (c : ℝ) ≤ 5/2 :=
      le_of_mul_le_mul_right (le_trans hle h_hi) h_2e_pos
    have hc_int_le : c ≤ 2 := by
      have h3 : (c : ℝ) < 3 := by linarith
      have : c < 3 := by exact_mod_cast h3
      omega
    have h_y_lo_low_le : ((y_lo_low_g e : Dyadic) : ℝ) ≤ t := by
      rw [coe_y_lo_low_g]; linarith
    have h_ge := hmax (y_lo_low_g e) (y_lo_low_mem_F₁_g p hp_ge_2 e) h_y_lo_low_le
    rw [coe_y_lo_low_g, hc] at h_ge
    have hc_r_ge : (2 : ℝ) ≤ (c : ℝ) := le_of_mul_le_mul_right h_ge h_2e_pos
    have hc_int_ge : 2 ≤ c := by exact_mod_cast hc_r_ge
    have hc_eq : c = 2 := by omega
    rw [hc, coe_y_lo_low_g, hc_eq]; push_cast; ring
  · -- RoundUp: z is the F₁-ceiling of t, namely 2·2^e or 3·2^e.
    obtain ⟨c, hc⟩ := F₁_g_quantum p hp_ge_2 e hzF
    rw [hc] at hge
    have hc_r_ge : (2 : ℝ) ≤ (c : ℝ) :=
      le_of_mul_le_mul_right (le_trans h_lo hge) h_2e_pos
    have hc_int_ge : 2 ≤ c := by exact_mod_cast hc_r_ge
    have h_y_lo_ge : t ≤ ((y_lo_g e : Dyadic) : ℝ) := by
      rw [coe_y_lo_g]; linarith
    have h_le := hmin (y_lo_g e) (y_lo_mem_F₁_g p hp_ge_2 e) h_y_lo_ge
    rw [coe_y_lo_g, hc] at h_le
    have hc_r_le : (c : ℝ) ≤ 3 := le_of_mul_le_mul_right h_le h_2e_pos
    have hc_int_le : c ≤ 3 := by exact_mod_cast hc_r_le
    rcases (by omega : c = 2 ∨ c = 3) with hc_eq | hc_eq
    · left; rw [hc, coe_y_lo_low_g, hc_eq]; push_cast; ring
    · right; rw [hc, coe_y_lo_g, hc_eq]; push_cast; ring

/-- F₁_g-RNE at any `t ∈ [2·2^e, 5·2^(e−1)]` admits `y_lo_low = 2·2^e`:
in the interior `y_lo_low` is the strictly nearest element; at the right
endpoint (the midpoint `m_low`) it wins the tie as the even neighbor. -/
private theorem rounds_F₁_g_RNE_interval_y_lo_low (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    {t : ℝ} (h_lo : 2 * (2 : ℝ) ^ e ≤ t) (h_hi : t ≤ (5 / 2) * (2 : ℝ) ^ e) :
    RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat (.nearest .toEven) t
      (y_lo_low_g e) := by
  have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
  have h_y_lo_low_eq : ((y_lo_low_g e : Dyadic) : ℝ) = 2 * (2 : ℝ)^e := coe_y_lo_low_g e
  refine ⟨y_lo_low_mem_F₁_g p hp_ge_2 e, ?_, ?_, ?_⟩
  · -- IsFaithfulRound (RoundDown y_lo_low).
    left
    refine ⟨y_lo_low_mem_F₁_g p hp_ge_2 e, ?_, ?_⟩
    · rw [h_y_lo_low_eq]; exact h_lo
    · intro z hz hle
      obtain ⟨c, hc⟩ := F₁_g_quantum p hp_ge_2 e hz
      rw [hc] at hle
      rw [h_y_lo_low_eq, hc]
      have hc_r_le : (c : ℝ) ≤ 5/2 :=
        le_of_mul_le_mul_right (le_trans hle h_hi) h_2e_pos
      have hc_int_le : c ≤ 2 := by
        have h3 : (c : ℝ) < 3 := by linarith
        have : c < 3 := by exact_mod_cast h3
        omega
      have : (c : ℝ) ≤ 2 := by exact_mod_cast hc_int_le
      nlinarith
  · -- Closeness: faithful z ∈ {y_lo_low, y_lo}; y_lo_low is no farther.
    intro z hz hf
    rcases F₁_faithful_interval_lo_g p hp_ge_2 e h_lo h_hi hf with hz_lo | hz_hi
    · rw [hz_lo]
    · rw [hz_hi, coe_y_lo_g, h_y_lo_low_eq]
      have hL : |t - 2 * (2 : ℝ)^e| = t - 2 * (2 : ℝ)^e :=
        abs_of_nonneg (by linarith)
      have hR : |t - 3 * (2 : ℝ)^e| = 3 * (2 : ℝ)^e - t := by
        rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
      rw [hL, hR]; linarith
  · rintro ⟨_, _, _, _, _⟩
    exact ⟨F₁_g p hp_ge_2 e, rfl, isEven_F₁_g_y_lo_low p hp_ge_2 e⟩

/-- F₁-faithful values of `m`: enumeration to `{y_lo, y_hi}`. -/
private theorem F₁_faithful_m_eq_g (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
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
private theorem rounds_F₁_g_RNE_m_y_hi (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ) :
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

/-- F₁-faithful values of any `t ∈ [7·2^(e−1), 4·2^e]` enumerate to
`{y_lo, y_hi}` (= `{3·2^e, 4·2^e}`). Generalizes `F₁_faithful_m_eq_g`
from the midpoint `m` to the whole right half-interval. -/
private theorem F₁_faithful_interval_hi_g (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    {t : ℝ} (h_lo : (7 / 2) * (2 : ℝ) ^ e ≤ t) (h_hi : t ≤ 4 * (2 : ℝ) ^ e)
    {z : Dyadic}
    (hf : IsFaithfulRound (F₁_g p hp_ge_2 e).toFiniteFormat t z) :
    (z : ℝ) = ((y_lo_g e : Dyadic) : ℝ) ∨ (z : ℝ) = ((y_hi_g e : Dyadic) : ℝ) := by
  have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
  have h_y_hi_eq : ((y_hi_g e : Dyadic) : ℝ) = 4 * (2 : ℝ)^e := by
    rw [coe_y_hi_g, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [show (2 : ℝ)^(2 : ℤ) = 4 by norm_num]; ring
  rcases hf with ⟨hzF, hle, hmax⟩ | ⟨hzF, hge, hmin⟩
  · -- RoundDown: z is the F₁-floor of t, namely 3·2^e or 4·2^e.
    obtain ⟨c, hc⟩ := F₁_g_quantum p hp_ge_2 e hzF
    rw [hc] at hle
    have hc_r_le : (c : ℝ) ≤ 4 :=
      le_of_mul_le_mul_right (le_trans hle h_hi) h_2e_pos
    have hc_int_le : c ≤ 4 := by exact_mod_cast hc_r_le
    have h_y_lo_le : ((y_lo_g e : Dyadic) : ℝ) ≤ t := by
      rw [coe_y_lo_g]; linarith
    have h_ge := hmax (y_lo_g e) (y_lo_mem_F₁_g p hp_ge_2 e) h_y_lo_le
    rw [coe_y_lo_g, hc] at h_ge
    have hc_r_ge : (3 : ℝ) ≤ (c : ℝ) := le_of_mul_le_mul_right h_ge h_2e_pos
    have hc_int_ge : 3 ≤ c := by exact_mod_cast hc_r_ge
    rcases (by omega : c = 3 ∨ c = 4) with hc_eq | hc_eq
    · left; rw [hc, coe_y_lo_g, hc_eq]; push_cast; ring
    · right; rw [hc, h_y_hi_eq, hc_eq]; push_cast; ring
  · -- RoundUp: z is the F₁-ceiling of t, namely 4·2^e.
    right
    obtain ⟨c, hc⟩ := F₁_g_quantum p hp_ge_2 e hzF
    rw [hc] at hge
    have hc_r_ge : (7/2 : ℝ) ≤ (c : ℝ) :=
      le_of_mul_le_mul_right (le_trans h_lo hge) h_2e_pos
    have hc_int_ge : 4 ≤ c := by
      have h3 : (3 : ℝ) < (c : ℝ) := by linarith
      have : 3 < c := by exact_mod_cast h3
      omega
    have h_y_hi_ge : t ≤ ((y_hi_g e : Dyadic) : ℝ) := by
      rw [h_y_hi_eq]; linarith
    have h_le := hmin (y_hi_g e) (y_hi_mem_F₁_g p hp_ge_2 e) h_y_hi_ge
    rw [h_y_hi_eq, hc] at h_le
    have hc_r_le : (c : ℝ) ≤ 4 := le_of_mul_le_mul_right h_le h_2e_pos
    have hc_int_le : c ≤ 4 := by exact_mod_cast hc_r_le
    have hc_eq : c = 4 := by omega
    rw [hc, h_y_hi_eq, hc_eq]; push_cast; ring

/-- F₁_g-RNE at any `t ∈ [7·2^(e−1), 4·2^e]` admits `y_hi = 4·2^e`:
in the interior `y_hi` is the strictly nearest element; at the left
endpoint (the midpoint `m`) it wins the tie as the even neighbor.
Generalizes `rounds_F₁_g_RNE_m_y_hi`. -/
private theorem rounds_F₁_g_RNE_interval_y_hi (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    {t : ℝ} (h_lo : (7 / 2) * (2 : ℝ) ^ e ≤ t) (h_hi : t ≤ 4 * (2 : ℝ) ^ e) :
    RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat (.nearest .toEven) t
      (y_hi_g e) := by
  have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
  have h_y_hi_eq : ((y_hi_g e : Dyadic) : ℝ) = 4 * (2 : ℝ)^e := by
    rw [coe_y_hi_g, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [show (2 : ℝ)^(2 : ℤ) = 4 by norm_num]; ring
  refine ⟨y_hi_mem_F₁_g p hp_ge_2 e, ?_, ?_, ?_⟩
  · -- IsFaithfulRound (RoundUp y_hi).
    right
    refine ⟨y_hi_mem_F₁_g p hp_ge_2 e, ?_, ?_⟩
    · rw [h_y_hi_eq]; exact h_hi
    · intro z hz hge
      obtain ⟨c, hc⟩ := F₁_g_quantum p hp_ge_2 e hz
      rw [hc] at hge
      rw [h_y_hi_eq, hc]
      have hc_r_ge : (7/2 : ℝ) ≤ (c : ℝ) :=
        le_of_mul_le_mul_right (le_trans h_lo hge) h_2e_pos
      have hc_int_ge : 4 ≤ c := by
        have h3 : (3 : ℝ) < (c : ℝ) := by linarith
        have : 3 < c := by exact_mod_cast h3
        omega
      have : (4 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc_int_ge
      nlinarith
  · -- Closeness: faithful z ∈ {y_lo, y_hi}; y_hi is no farther.
    intro z hz hf
    rcases F₁_faithful_interval_hi_g p hp_ge_2 e h_lo h_hi hf with hz_lo | hz_hi
    · rw [hz_lo, coe_y_lo_g, h_y_hi_eq]
      have hL : |t - 4 * (2 : ℝ)^e| = 4 * (2 : ℝ)^e - t := by
        rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
      have hR : |t - 3 * (2 : ℝ)^e| = t - 3 * (2 : ℝ)^e :=
        abs_of_nonneg (by linarith)
      rw [hL, hR]; linarith
    · rw [hz_hi]
  · rintro ⟨_, _, _, _, _⟩
    exact ⟨F₁_g p hp_ge_2 e, rfl, isEven_F₁_g_y_hi p hp_ge_2 e⟩

/-! ## The RNE-RNE counterexample -/

/-- **Core RNE-RNE counterexample via midpoint membership.** If the
`F₁`-midpoint `m = 7·2^(e−1)` is representable in `F₂` and `F₂` has finite
quantum `f₂ ≤ e − 1`, then the quarter-quantum witness `x = m − 2^(f₂−2)`
defeats RNE-RNE double rounding — for *any* precision (including `F₂.p = ⊤`)
and any bound on `F₂`. Every `F₂`-element is a multiple of `2^f₂` while `m`
lies on that grid, so `m` is the strictly nearest `F₂`-element to `x`
(`z = m`); the `F₁`-tie at `m` then breaks to the even `y_hi = 4·2^e`,
while the direct RNE of `x` is `y_lo = 3·2^e`. -/
private theorem no_rndRNE_RNE_of_m_mem
    (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    (F₂ : FiniteFormat) (hm_in_F₂ : m_g e ∈ F₂.toFormat)
    {f₂ : ℤ} (hF₂_exp : F₂.exp = (f₂ : WithBot ℤ)) (hf₂ : f₂ ≤ e - 1) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ (.nearest .toEven) x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat (.nearest .toEven) (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat (.nearest .toEven) x w := by
  have h_y_lo_in_F₁ := y_lo_mem_F₁_g p hp_ge_2 e
  -- Numeric facts.
  have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
  have h_2f2_pos : (0 : ℝ) < (2 : ℝ)^(f₂ - 2) := zpow_pos (by norm_num) _
  have h_2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
  have h_2f2_lt_2f : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^f₂ :=
    zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < f₂)
  have h_2e2_eq : (2 : ℝ)^(e - 2) = (1/4) * (2 : ℝ)^e := by
    rw [show (e - 2 : ℤ) = e + (-2 : ℤ) by ring,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
        show (2 : ℝ)^(-2 : ℤ) = 1/4 by
          rw [show ((-2 : ℤ)) = -(2 : ℤ) by ring, zpow_neg]; norm_num]
    ring
  have h_2f2_le_quarter : (2 : ℝ)^(f₂ - 2) ≤ (1/4) * (2 : ℝ)^e := by
    rw [← h_2e2_eq]
    exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : f₂ - 2 ≤ e - 2)
  have h_2f_4 : (2 : ℝ)^f₂ = 4 * (2 : ℝ)^(f₂ - 2) := two_zpow_split_minus_two f₂
  have h_m_eq : ((m_g e : Dyadic) : ℝ) = (7/2) * (2 : ℝ)^e := by
    rw [coe_m_g, show (e - 1 : ℤ) = e + (-1 : ℤ) by ring,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
        show (2 : ℝ)^(-1 : ℤ) = 1/2 by
          rw [show ((-1 : ℤ)) = -(1 : ℤ) by ring, zpow_neg]; norm_num]
    ring
  set x_val : ℝ := (7/2) * (2 : ℝ)^e - (2 : ℝ)^(f₂ - 2) with hx_def
  have h_x_le_m : x_val ≤ ((m_g e : Dyadic) : ℝ) := by
    rw [h_m_eq, hx_def]; linarith
  -- `m` is on `F₂`'s quantum grid: `m = (7·2^n) · 2^f₂`.
  set n : ℕ := (e - 1 - f₂).toNat with hn_def
  have h_m_grid : (7/2) * (2 : ℝ)^e = ((7 * (2 : ℤ)^n : ℤ) : ℝ) * (2 : ℝ)^f₂ := by
    have h_split : (2 : ℝ)^(e - 1) = ((2 : ℤ)^n : ℝ) * (2 : ℝ)^f₂ :=
      two_zpow_split (e - 1) f₂ hf₂
    have h72 : (7 : ℝ) * (2 : ℝ)^(e - 1) = (7/2) * (2 : ℝ)^e := by
      rw [show (e - 1 : ℤ) = e + (-1 : ℤ) by ring,
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
          show (2 : ℝ)^(-1 : ℤ) = 1/2 by
            rw [show ((-1 : ℤ)) = -(1 : ℤ) by ring, zpow_neg]; norm_num]
      ring
    rw [← h72, h_split]; push_cast; ring
  -- Grid dichotomy around `x`: every `F₂`-element is a multiple of `2^f₂`,
  -- so it sits at or below `m − 2^f₂`, or at or above `m`.
  have h_floor : ∀ z' ∈ F₂.toFormat, ((z' : Dyadic) : ℝ) ≤ x_val →
      ((z' : Dyadic) : ℝ) ≤ (7/2) * (2 : ℝ)^e - (2 : ℝ)^f₂ := by
    have h_target : (7/2) * (2 : ℝ)^e - (2 : ℝ)^f₂
        = ((7 * (2 : ℤ)^n - 1 : ℤ) : ℝ) * (2 : ℝ)^f₂ := by
      rw [h_m_grid]; push_cast; ring
    intro z' hz' hz'_le
    apply F₂_grid_floor hF₂_exp h_target z' hz'
    rw [hx_def] at hz'_le
    linarith
  have h_ceil : ∀ z' ∈ F₂.toFormat, x_val ≤ ((z' : Dyadic) : ℝ) →
      (7/2) * (2 : ℝ)^e ≤ ((z' : Dyadic) : ℝ) := by
    intro z' hz' hz'_ge
    apply F₂_grid_ceil hF₂_exp h_m_grid z' hz'
    rw [hx_def] at hz'_ge
    linarith
  have h_abs_m : |x_val - ((m_g e : Dyadic) : ℝ)| = (2 : ℝ)^(f₂ - 2) := by
    rw [h_m_eq, hx_def,
        show (7/2) * (2 : ℝ)^e - (2 : ℝ)^(f₂ - 2) - (7/2) * (2 : ℝ)^e
          = -((2 : ℝ)^(f₂ - 2)) by ring, abs_neg]
    exact abs_of_pos h_2f2_pos
  refine ⟨x_val, m_g e, y_hi_g e, ?_, rounds_F₁_g_RNE_m_y_hi p hp_ge_2 e, ?_⟩
  · -- `z = m`: RNE in `F₂` rounds `x` up onto the midpoint.
    refine ⟨hm_in_F₂, ?_, ?_, ?_⟩
    · -- Faithful: `m` is the `F₂`-ceiling of `x`.
      right
      refine ⟨hm_in_F₂, h_x_le_m, ?_⟩
      intro z' hz' hz'_ge
      rw [h_m_eq]
      exact h_ceil z' hz' hz'_ge
    · -- Strictly nearest among all `F₂`-elements.
      intro z' hz' _
      rw [h_abs_m]
      rcases le_or_gt ((z' : Dyadic) : ℝ) x_val with hle | hgt
      · have hz'_le_grid := h_floor z' hz' hle
        have h_nn : (0 : ℝ) ≤ x_val - ((z' : Dyadic) : ℝ) := by linarith
        rw [abs_of_nonneg h_nn, hx_def]
        linarith
      · have hz'_ge_grid := h_ceil z' hz' hgt.le
        have h_nn : (0 : ℝ) ≤ ((z' : Dyadic) : ℝ) - x_val := by linarith
        rw [abs_sub_comm, abs_of_nonneg h_nn, hx_def]
        linarith
    · -- No tie: `m` is *strictly* nearest, so the premise is contradictory.
      rintro ⟨z', hz'_mem, _, hz'_ne, hz'_eq⟩
      exfalso
      rw [h_abs_m] at hz'_eq
      rcases le_or_gt ((z' : Dyadic) : ℝ) x_val with hle | hgt
      · have hz'_le_grid := h_floor z' hz'_mem hle
        have h_nn : (0 : ℝ) ≤ x_val - ((z' : Dyadic) : ℝ) := by linarith
        rw [abs_of_nonneg h_nn, hx_def] at hz'_eq
        linarith
      · have hz'_ge_grid := h_ceil z' hz'_mem hgt.le
        have h_nn : (0 : ℝ) ≤ ((z' : Dyadic) : ℝ) - x_val := by linarith
        rw [abs_sub_comm, abs_of_nonneg h_nn] at hz'_eq
        have h_z'_eq_m : ((z' : Dyadic) : ℝ) = ((m_g e : Dyadic) : ℝ) := by
          rw [h_m_eq]; rw [hx_def] at hz'_eq; linarith
        exact hz'_ne ((Dyadic.coe_real_inj z' (m_g e)).mp h_z'_eq_m)
  · -- The direct RNE of `x` cannot be `y_hi`: `y_lo = 3·2^e` is faithful and
    -- strictly closer.
    intro hr
    obtain ⟨_, _, h_close, _⟩ := hr
    have h_2f2_lt_half : (2 : ℝ)^(f₂ - 2) < (1/2) * (2 : ℝ)^e := by nlinarith
    have h_y_hi_eq : ((y_hi_g e : Dyadic) : ℝ) = 4 * (2 : ℝ)^e := by
      rw [coe_y_hi_g, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      rw [show (2 : ℝ)^(2 : ℤ) = 4 by norm_num]; ring
    have h_y_lo_faith :
        IsFaithfulRound (F₁_g p hp_ge_2 e).toFiniteFormat x_val (y_lo_g e) := by
      left
      refine ⟨h_y_lo_in_F₁, ?_, ?_⟩
      · rw [coe_y_lo_g, hx_def]; linarith
      · intro z' hz' hz'_le
        obtain ⟨c', hc'⟩ := F₁_g_quantum p hp_ge_2 e hz'
        have h_lt : (z' : ℝ) < (7/2) * (2 : ℝ)^e := by
          have hx_lt : x_val < (7/2) * (2 : ℝ)^e := by rw [hx_def]; linarith
          linarith
        rw [hc'] at h_lt
        have hc'_lt : (c' : ℝ) < 7/2 := lt_of_mul_lt_mul_right h_lt h_2e_pos.le
        have hc'_le3 : c' ≤ 3 := by
          have h4 : (c' : ℝ) < 4 := by linarith
          have h4' : c' < 4 := by exact_mod_cast h4
          omega
        change (z' : ℝ) ≤ ((y_lo_g e : Dyadic) : ℝ)
        rw [hc', coe_y_lo_g]
        have : (c' : ℝ) ≤ 3 := by exact_mod_cast hc'_le3
        nlinarith
    have h_close_lo := h_close (y_lo_g e) h_y_lo_in_F₁ h_y_lo_faith
    rw [h_y_hi_eq, coe_y_lo_g] at h_close_lo
    have h_absL : |x_val - 4 * (2 : ℝ)^e|
        = (1/2) * (2 : ℝ)^e + (2 : ℝ)^(f₂ - 2) := by
      rw [hx_def, show (7/2) * (2 : ℝ)^e - (2 : ℝ)^(f₂ - 2) - 4 * (2 : ℝ)^e
          = -((1/2) * (2 : ℝ)^e + (2 : ℝ)^(f₂ - 2)) by ring, abs_neg]
      exact abs_of_pos (by nlinarith)
    have h_absR : |x_val - 3 * (2 : ℝ)^e|
        = (1/2) * (2 : ℝ)^e - (2 : ℝ)^(f₂ - 2) := by
      rw [hx_def, show (7/2) * (2 : ℝ)^e - (2 : ℝ)^(f₂ - 2) - 3 * (2 : ℝ)^e
          = (1/2) * (2 : ℝ)^e - (2 : ℝ)^(f₂ - 2) by ring]
      exact abs_of_pos (by linarith)
    rw [h_absL, h_absR] at h_close_lo
    linarith

/-- **Convenience wrapper** with the minimal user-facing hypotheses: the
paper-style containment `(F₁.extend 2) ⊆ F₂` plus finiteness of `F₂.exp`.
`F₂.p` may be `⊤` (fixed-point `F₂`) or any finite precision — the
containment places the midpoint `m = 14·2^(e−2)` in `F₂` and forces
`f₂ ≤ e − 1`, which is all `no_rndRNE_RNE_of_m_mem` needs. -/
theorem no_rndRNE_RNE
    (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    (F₂ : FiniteFormat)
    (hsub : ((F₁_g p hp_ge_2 e).toFiniteFormat.extend 2).toFormat ⊆ F₂.toFormat)
    (hF₂_exp_fin : F₂.exp ≠ ⊥) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ (.nearest .toEven) x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat (.nearest .toEven) (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat (.nearest .toEven) x w := by
  obtain ⟨f₂, hf₂_eq⟩ := WithBot.ne_bot_iff_exists.mp hF₂_exp_fin
  have hF₂_exp : F₂.exp = (f₂ : WithBot ℤ) := hf₂_eq.symm
  -- `m = 7·2^(e−1) = 14·2^(e−2)` is in the extend-2 format, hence in `F₂`.
  have h_ext_p : ((F₁_g p hp_ge_2 e).toFiniteFormat.extend 2).p
      = (((p + 2 : ℕ+)) : WithTop ℕ+) := by
    change (F₁_g p hp_ge_2 e).p.map (· + (2 : ℕ+)) = _
    rw [F₁_g_p, WithTop.map_coe]
  have h_pp2_cast : (((p + 2 : ℕ+)) : ℕ) = (p : ℕ) + 2 := by exact_mod_cast rfl
  have hm_in_ext2 :
      m_g e ∈ ((F₁_g p hp_ge_2 e).toFiniteFormat.extend 2).toFormat := by
    refine ⟨?_, ?_, trivial⟩
    · rw [h_ext_p, Dyadic.precisionAtMost_coe_real]
      refine ⟨14, e - 2, ?_, ?_⟩
      · rw [coe_m_g, show (e - 1 : ℤ) = (e - 2) + 1 by ring,
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
            show (2 : ℝ)^(1 : ℤ) = 2 by norm_num]
        push_cast; ring
      · rw [h_pp2_cast]
        have h_pow : (16 : ℤ) ≤ (2 : ℤ)^((p : ℕ) + 2) :=
          calc (16 : ℤ) = (2 : ℤ)^4 := by norm_num
            _ ≤ (2 : ℤ)^((p : ℕ) + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
        have h_abs : |(14 : ℤ)| = 14 := by decide
        omega
    · change Dyadic.quantumAtLeast ((F₁_g p hp_ge_2 e).exp.map (· - (2 : ℤ))) (m_g e)
      rw [F₁_g_exp, WithBot.map_coe, Dyadic.quantumAtLeast_coe_real]
      refine ⟨14, ?_⟩
      rw [coe_m_g, show (e - 1 : ℤ) = (e - 2) + 1 by ring,
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
          show (2 : ℝ)^(1 : ℤ) = 2 by norm_num]
      push_cast; ring
  have hm_in_F₂ : m_g e ∈ F₂.toFormat := hsub _ hm_in_ext2
  -- `m = 7·2^(e−1)` with `7` odd forces `f₂ ≤ e − 1`.
  have hf₂_le : f₂ ≤ e - 1 :=
    f₂_le_e_sub_one_of_odd_in_F₂ hF₂_exp hm_in_F₂ (by decide : Odd (7 : ℤ))
      (by rw [coe_m_g]; push_cast; ring)
  exact no_rndRNE_RNE_of_m_mem p hp_ge_2 e F₂ hm_in_F₂ hF₂_exp hf₂_le

/-! ## CHUNK 3: the remaining §5.2 counterexamples -/

/-- `IsOdd` depends only on `toFormat`: transfer along `F'.toFormat = F.toFormat`. -/
private theorem isOdd_transfer_toFormat {F F' : ParityFormat} {y : Dyadic}
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
    (F₂ : FiniteFormat) (hF₂_exp_fin : F₂.exp ≠ ⊥) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ (.nearest .toEven) x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .awayZero (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .awayZero x w := by
  obtain ⟨f₂, hf₂_eq⟩ := WithBot.ne_bot_iff_exists.mp hF₂_exp_fin
  have hF₂_exp : F₂.exp = (f₂ : WithBot ℤ) := hf₂_eq.symm
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
    (hF₂_exp_fin : F₂.exp ≠ ⊥) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ (.nearest .toEven) x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .toZero (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .toZero x w := by
  obtain ⟨f₂, hf₂_eq⟩ := WithBot.ne_bot_iff_exists.mp hF₂_exp_fin
  have hF₂_exp : F₂.exp = (f₂ : WithBot ℤ) := hf₂_eq.symm
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
    (hF₂_exp_fin : F₂.exp ≠ ⊥) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .toZero x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .awayZero (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .awayZero x w := by
  obtain ⟨f₂, hf₂_eq⟩ := WithBot.ne_bot_iff_exists.mp hF₂_exp_fin
  have hF₂_exp : F₂.exp = (f₂ : WithBot ℤ) := hf₂_eq.symm
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
    (hF₂_exp_fin : F₂.exp ≠ ⊥) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .awayZero x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .toZero (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .toZero x w := by
  obtain ⟨f₂, hf₂_eq⟩ := WithBot.ne_bot_iff_exists.mp hF₂_exp_fin
  have hF₂_exp : F₂.exp = (f₂ : WithBot ℤ) := hf₂_eq.symm
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
    (hF₂_exp_fin : F₂.exp ≠ ⊥) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .awayZero x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .toOdd (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .toOdd x w := by
  obtain ⟨f₂, hf₂_eq⟩ := WithBot.ne_bot_iff_exists.mp hF₂_exp_fin
  have hF₂_exp : F₂.exp = (f₂ : WithBot ℤ) := hf₂_eq.symm
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
    (hF₂_exp_fin : F₂.exp ≠ ⊥) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ (.nearest .toEven) x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .toOdd (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .toOdd x w := by
  obtain ⟨f₂, hf₂_eq⟩ := WithBot.ne_bot_iff_exists.mp hF₂_exp_fin
  have hF₂_exp : F₂.exp = (f₂ : WithBot ℤ) := hf₂_eq.symm
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
    (hF₂_exp_fin : F₂.exp ≠ ⊥) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .toZero x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .toOdd (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .toOdd x w := by
  obtain ⟨f₂, hf₂_eq⟩ := WithBot.ne_bot_iff_exists.mp hF₂_exp_fin
  have hF₂_exp : F₂.exp = (f₂ : WithBot ℤ) := hf₂_eq.symm
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

/-- **Counterexample to `rndRAZ_RNE`.** Requires only the containment
`F₁_g ⊆ F₂` — no midpoint representability. With
`x = 7·2^(e−1) − 2^(f₂−2)`, the intermediate RAZ either lands on the
midpoint `m = 7·2^(e−1)` (when `F₂` resolves it, manufacturing a spurious
tie that RNE breaks toward the even `4·2^e`) or lands strictly above it
(crossing RNE's decision boundary undetected). Either way the chained
result is `4·2^e`, while the direct RNE of `x` is `3·2^e`. -/
theorem no_rndRAZ_RNE
    (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    (F₂ : FiniteFormat) (hsub : (F₁_g p hp_ge_2 e).toFormat ⊆ F₂.toFormat)
    (hF₂_exp_fin : F₂.exp ≠ ⊥) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .awayZero x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat (.nearest .toEven) (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat (.nearest .toEven) x w := by
  obtain ⟨f₂, hf₂_eq⟩ := WithBot.ne_bot_iff_exists.mp hF₂_exp_fin
  have hF₂_exp : F₂.exp = (f₂ : WithBot ℤ) := hf₂_eq.symm
  have hf₂_le_e : f₂ ≤ e := f₂_le_e_of_F₁_g_subset p hp_ge_2 e F₂.toFormat hsub hF₂_exp
  have h_y_lo_in_F₁ := y_lo_mem_F₁_g p hp_ge_2 e
  have h_y_hi_in_F₁ := y_hi_mem_F₁_g p hp_ge_2 e
  have h_y_hi_in_F₂ : y_hi_g e ∈ F₂.toFormat := hsub _ h_y_hi_in_F₁
  -- Numeric facts.
  have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
  have h_2f2_pos : (0 : ℝ) < (2 : ℝ)^(f₂ - 2) := zpow_pos (by norm_num) _
  have h_2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
  have h_2f2_lt_2f : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^f₂ :=
    zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < f₂)
  have h_2e2_eq : (2 : ℝ)^(e - 2) = (1/4) * (2 : ℝ)^e := by
    rw [show (e - 2 : ℤ) = e + (-2 : ℤ) by ring,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
        show (2 : ℝ)^(-2 : ℤ) = 1/4 by
          rw [show ((-2 : ℤ)) = -(2 : ℤ) by ring, zpow_neg]; norm_num]
    ring
  have h_2f2_le_quarter : (2 : ℝ)^(f₂ - 2) ≤ (1/4) * (2 : ℝ)^e := by
    rw [← h_2e2_eq]
    exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : f₂ - 2 ≤ e - 2)
  have h_y_hi_eq : ((y_hi_g e : Dyadic) : ℝ) = 4 * (2 : ℝ)^e := by
    rw [coe_y_hi_g, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [show (2 : ℝ)^(2 : ℤ) = 4 by norm_num]; ring
  set x_val : ℝ := (7/2) * (2 : ℝ)^e - (2 : ℝ)^(f₂ - 2) with hx_def
  have h_x_pos : 0 < x_val := by rw [hx_def]; nlinarith
  -- The intermediate rounding exists: `F₂.b = ⊤`, so the unbounded RAZ
  -- rounding of `x` is the bounded one.
  have hb_top : F₂.b = ⊤ := F₂_bound_top_of_F₁_g_subset p hp_ge_2 e F₂ hsub
  set z : Dyadic := rndUnbounded F₂ .awayZero x_val (not_isUndefined_awayZero F₂)
    with hz_def
  have hz_rounds : RoundsFinite F₂ .awayZero x_val z := by
    have h := rndUnbounded_satisfies F₂ .awayZero x_val (not_isUndefined_awayZero F₂)
    rwa [unbounded_eq_self hb_top] at h
  obtain ⟨hz_mem, hz_abs, hz_sign, hz_min⟩ := hz_rounds
  -- Bracket the intermediate: `7·2^(e−1) ≤ z ≤ 4·2^e`.
  have h_z_nn : 0 ≤ (z : ℝ) := nonneg_of_mul_nonneg_pos hz_sign h_x_pos
  have h_z_ge_x : x_val ≤ (z : ℝ) := by
    have h := hz_abs
    rwa [abs_of_nonneg h_z_nn, abs_of_pos h_x_pos] at h
  have h_z_le : (z : ℝ) ≤ 4 * (2 : ℝ)^e := by
    have h4e_nn : (0 : ℝ) ≤ 4 * (2 : ℝ)^e := by nlinarith
    have h_ge_abs : |x_val| ≤ |((y_hi_g e : Dyadic) : ℝ)| := by
      rw [h_y_hi_eq, abs_of_nonneg h4e_nn, abs_of_pos h_x_pos, hx_def]
      linarith
    have h_sign : ((y_hi_g e : Dyadic) : ℝ) * x_val ≥ 0 := by
      rw [h_y_hi_eq]; nlinarith
    have h := hz_min (y_hi_g e) h_y_hi_in_F₂ h_ge_abs h_sign
    rwa [h_y_hi_eq, abs_of_nonneg h4e_nn, abs_of_nonneg h_z_nn] at h
  have h_z_ge_m : (7/2) * (2 : ℝ)^e ≤ (z : ℝ) := by
    rcases lt_or_eq_of_le hf₂_le_e with hf₂_lt | hf₂_eq_e
    · -- `f₂ ≤ e − 1`: the midpoint value `7·2^(e−1)` is on F₂'s quantum grid.
      set n : ℕ := (e - 1 - f₂).toNat with hn_def
      have h_target : (7/2) * (2 : ℝ)^e
          = ((7 * (2 : ℤ)^n : ℤ) : ℝ) * (2 : ℝ)^f₂ := by
        have h_split : (2 : ℝ)^(e - 1) = ((2 : ℤ)^n : ℝ) * (2 : ℝ)^f₂ :=
          two_zpow_split (e - 1) f₂ (by omega)
        have h72 : (7 : ℝ) * (2 : ℝ)^(e - 1) = (7/2) * (2 : ℝ)^e := by
          rw [show (e - 1 : ℤ) = e + (-1 : ℤ) by ring,
              zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
              show (2 : ℝ)^(-1 : ℤ) = 1/2 by
                rw [show ((-1 : ℤ)) = -(1 : ℤ) by ring, zpow_neg]; norm_num]
          ring
        rw [← h72, h_split]; push_cast; ring
      exact F₂_grid_ceil hF₂_exp h_target z hz_mem
        (by rw [hx_def] at h_z_ge_x; linarith)
    · -- `f₂ = e`: F₂'s quantum grid steps by `2^e`; the ceiling above `x` is
      -- at least `4·2^e`.
      have h_target : 4 * (2 : ℝ)^e = ((4 : ℤ) : ℝ) * (2 : ℝ)^f₂ := by
        rw [hf₂_eq_e]; push_cast; ring
      have h_2f2_eq : (2 : ℝ)^(f₂ - 2) = (1/4) * (2 : ℝ)^e := by
        rw [hf₂_eq_e]; exact h_2e2_eq
      have h_2f_eq : (2 : ℝ)^f₂ = (2 : ℝ)^e := by rw [hf₂_eq_e]
      have h_ceil := F₂_grid_ceil hF₂_exp h_target z hz_mem (by
        rw [hx_def] at h_z_ge_x
        rw [h_2f_eq]
        linarith [h_2f2_eq])
      linarith
  refine ⟨x_val, z, y_hi_g e, ⟨hz_mem, hz_abs, hz_sign, hz_min⟩,
    rounds_F₁_g_RNE_interval_y_hi p hp_ge_2 e h_z_ge_m h_z_le, ?_⟩
  -- The direct RNE of `x` cannot be `y_hi`: `y_lo = 3·2^e` is faithful and
  -- strictly closer.
  intro hr
  obtain ⟨_, _, h_close, _⟩ := hr
  have h_2f2_lt_half : (2 : ℝ)^(f₂ - 2) < (1/2) * (2 : ℝ)^e := by nlinarith
  have h_y_lo_faith :
      IsFaithfulRound (F₁_g p hp_ge_2 e).toFiniteFormat x_val (y_lo_g e) := by
    left
    refine ⟨h_y_lo_in_F₁, ?_, ?_⟩
    · rw [coe_y_lo_g, hx_def]; linarith
    · intro z' hz' hz'_le
      obtain ⟨c', hc'⟩ := F₁_g_quantum p hp_ge_2 e hz'
      have h_lt : (z' : ℝ) < (7/2) * (2 : ℝ)^e := by
        have hx_lt : x_val < (7/2) * (2 : ℝ)^e := by rw [hx_def]; linarith
        linarith
      rw [hc'] at h_lt
      have hc'_lt : (c' : ℝ) < 7/2 := lt_of_mul_lt_mul_right h_lt h_2e_pos.le
      have hc'_le3 : c' ≤ 3 := by
        have h4 : (c' : ℝ) < 4 := by linarith
        have h4' : c' < 4 := by exact_mod_cast h4
        omega
      change (z' : ℝ) ≤ ((y_lo_g e : Dyadic) : ℝ)
      rw [hc', coe_y_lo_g]
      have : (c' : ℝ) ≤ 3 := by exact_mod_cast hc'_le3
      nlinarith
  have h_close_lo := h_close (y_lo_g e) h_y_lo_in_F₁ h_y_lo_faith
  rw [h_y_hi_eq, coe_y_lo_g] at h_close_lo
  have h_absL : |x_val - 4 * (2 : ℝ)^e|
      = (1/2) * (2 : ℝ)^e + (2 : ℝ)^(f₂ - 2) := by
    rw [hx_def, show (7/2) * (2 : ℝ)^e - (2 : ℝ)^(f₂ - 2) - 4 * (2 : ℝ)^e
        = -((1/2) * (2 : ℝ)^e + (2 : ℝ)^(f₂ - 2)) by ring, abs_neg]
    exact abs_of_pos (by nlinarith)
  have h_absR : |x_val - 3 * (2 : ℝ)^e|
      = (1/2) * (2 : ℝ)^e - (2 : ℝ)^(f₂ - 2) := by
    rw [hx_def, show (7/2) * (2 : ℝ)^e - (2 : ℝ)^(f₂ - 2) - 3 * (2 : ℝ)^e
        = (1/2) * (2 : ℝ)^e - (2 : ℝ)^(f₂ - 2) by ring]
    exact abs_of_pos (by linarith)
  rw [h_absL, h_absR] at h_close_lo
  linarith

/-- **Counterexample to `rndRTZ_RNE`.** Requires only the containment
`F₁_g ⊆ F₂` — no midpoint representability. With
`x = 5·2^(e−1) + 2^(f₂−2)`, the intermediate RTZ either lands on the
midpoint `m_low = 5·2^(e−1)` (when `F₂` resolves it, manufacturing a
spurious tie that RNE breaks toward the even `2·2^e`) or lands strictly
below it (crossing RNE's decision boundary undetected). Either way the
chained result is `2·2^e`, while the direct RNE of `x` is `3·2^e`. -/
theorem no_rndRTZ_RNE
    (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    (F₂ : FiniteFormat) (hsub : (F₁_g p hp_ge_2 e).toFormat ⊆ F₂.toFormat)
    (hF₂_exp_fin : F₂.exp ≠ ⊥) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .toZero x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat (.nearest .toEven) (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat (.nearest .toEven) x w := by
  obtain ⟨f₂, hf₂_eq⟩ := WithBot.ne_bot_iff_exists.mp hF₂_exp_fin
  have hF₂_exp : F₂.exp = (f₂ : WithBot ℤ) := hf₂_eq.symm
  have hf₂_le_e : f₂ ≤ e := f₂_le_e_of_F₁_g_subset p hp_ge_2 e F₂.toFormat hsub hF₂_exp
  have h_y_lo_low_in_F₁ := y_lo_low_mem_F₁_g p hp_ge_2 e
  have h_y_lo_in_F₁ := y_lo_mem_F₁_g p hp_ge_2 e
  have h_y_lo_low_in_F₂ : y_lo_low_g e ∈ F₂.toFormat := hsub _ h_y_lo_low_in_F₁
  -- Numeric facts.
  have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
  have h_2f2_pos : (0 : ℝ) < (2 : ℝ)^(f₂ - 2) := zpow_pos (by norm_num) _
  have h_2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
  have h_2f2_lt_2f : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^f₂ :=
    zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < f₂)
  have h_2e2_eq : (2 : ℝ)^(e - 2) = (1/4) * (2 : ℝ)^e := by
    rw [show (e - 2 : ℤ) = e + (-2 : ℤ) by ring,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
        show (2 : ℝ)^(-2 : ℤ) = 1/4 by
          rw [show ((-2 : ℤ)) = -(2 : ℤ) by ring, zpow_neg]; norm_num]
    ring
  have h_2f2_le_quarter : (2 : ℝ)^(f₂ - 2) ≤ (1/4) * (2 : ℝ)^e := by
    rw [← h_2e2_eq]
    exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : f₂ - 2 ≤ e - 2)
  set x_val : ℝ := (5/2) * (2 : ℝ)^e + (2 : ℝ)^(f₂ - 2) with hx_def
  have h_x_pos : 0 < x_val := by rw [hx_def]; nlinarith
  -- The intermediate rounding exists: `F₂.b = ⊤`, so the unbounded RTZ
  -- rounding of `x` is the bounded one.
  have hb_top : F₂.b = ⊤ := F₂_bound_top_of_F₁_g_subset p hp_ge_2 e F₂ hsub
  set z : Dyadic := rndUnbounded F₂ .toZero x_val (not_isUndefined_toZero F₂)
    with hz_def
  have hz_rounds : RoundsFinite F₂ .toZero x_val z := by
    have h := rndUnbounded_satisfies F₂ .toZero x_val (not_isUndefined_toZero F₂)
    rwa [unbounded_eq_self hb_top] at h
  obtain ⟨hz_mem, hz_abs, hz_sign, hz_max⟩ := hz_rounds
  -- Bracket the intermediate: `2·2^e ≤ z ≤ 5·2^(e−1)`.
  have h_z_nn : 0 ≤ (z : ℝ) := nonneg_of_mul_nonneg_pos hz_sign h_x_pos
  have h_z_le_x : (z : ℝ) ≤ x_val := by
    have h := hz_abs
    rwa [abs_of_nonneg h_z_nn, abs_of_pos h_x_pos] at h
  have h_z_ge : 2 * (2 : ℝ)^e ≤ (z : ℝ) := by
    have h2e_nn : (0 : ℝ) ≤ 2 * (2 : ℝ)^e := by nlinarith
    have h_le_abs : |((y_lo_low_g e : Dyadic) : ℝ)| ≤ |x_val| := by
      rw [coe_y_lo_low_g, abs_of_nonneg h2e_nn, abs_of_pos h_x_pos, hx_def]
      linarith
    have h_sign : ((y_lo_low_g e : Dyadic) : ℝ) * x_val ≥ 0 := by
      rw [coe_y_lo_low_g]; nlinarith
    have h := hz_max (y_lo_low_g e) h_y_lo_low_in_F₂ h_le_abs h_sign
    rwa [coe_y_lo_low_g, abs_of_nonneg h2e_nn, abs_of_nonneg h_z_nn] at h
  have h_z_le_m : (z : ℝ) ≤ (5/2) * (2 : ℝ)^e := by
    rcases lt_or_eq_of_le hf₂_le_e with hf₂_lt | hf₂_eq_e
    · -- `f₂ ≤ e − 1`: the midpoint value `5·2^(e−1)` is on F₂'s quantum grid.
      set n : ℕ := (e - 1 - f₂).toNat with hn_def
      have h_target : (5/2) * (2 : ℝ)^e
          = ((5 * (2 : ℤ)^n : ℤ) : ℝ) * (2 : ℝ)^f₂ := by
        have h_split : (2 : ℝ)^(e - 1) = ((2 : ℤ)^n : ℝ) * (2 : ℝ)^f₂ :=
          two_zpow_split (e - 1) f₂ (by omega)
        have h52 : (5 : ℝ) * (2 : ℝ)^(e - 1) = (5/2) * (2 : ℝ)^e := by
          rw [show (e - 1 : ℤ) = e + (-1 : ℤ) by ring,
              zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
              show (2 : ℝ)^(-1 : ℤ) = 1/2 by
                rw [show ((-1 : ℤ)) = -(1 : ℤ) by ring, zpow_neg]; norm_num]
          ring
        rw [← h52, h_split]; push_cast; ring
      exact F₂_grid_floor hF₂_exp h_target z hz_mem
        (by rw [hx_def] at h_z_le_x; linarith)
    · -- `f₂ = e`: F₂'s quantum grid steps by `2^e`; the floor below `x` is
      -- at most `2·2^e`.
      have h_target : 2 * (2 : ℝ)^e = ((2 : ℤ) : ℝ) * (2 : ℝ)^f₂ := by
        rw [hf₂_eq_e]; push_cast; ring
      have h_2f2_eq : (2 : ℝ)^(f₂ - 2) = (1/4) * (2 : ℝ)^e := by
        rw [hf₂_eq_e]; exact h_2e2_eq
      have h_2f_eq : (2 : ℝ)^f₂ = (2 : ℝ)^e := by rw [hf₂_eq_e]
      have h_floor := F₂_grid_floor hF₂_exp h_target z hz_mem (by
        rw [hx_def] at h_z_le_x
        rw [h_2f_eq]
        linarith [h_2f2_eq])
      linarith
  refine ⟨x_val, z, y_lo_low_g e, ⟨hz_mem, hz_abs, hz_sign, hz_max⟩,
    rounds_F₁_g_RNE_interval_y_lo_low p hp_ge_2 e h_z_ge h_z_le_m, ?_⟩
  -- The direct RNE of `x` cannot be `y_lo_low`: `y_lo = 3·2^e` is faithful
  -- and strictly closer.
  intro hr
  obtain ⟨_, _, h_close, _⟩ := hr
  have h_2f2_lt_half : (2 : ℝ)^(f₂ - 2) < (1/2) * (2 : ℝ)^e := by nlinarith
  have h_y_lo_faith :
      IsFaithfulRound (F₁_g p hp_ge_2 e).toFiniteFormat x_val (y_lo_g e) := by
    right
    refine ⟨h_y_lo_in_F₁, ?_, ?_⟩
    · rw [coe_y_lo_g, hx_def]; linarith
    · intro z' hz' hz'_ge
      obtain ⟨c', hc'⟩ := F₁_g_quantum p hp_ge_2 e hz'
      have h_gt : (5/2) * (2 : ℝ)^e < (z' : ℝ) := by
        have hx_gt : (5/2) * (2 : ℝ)^e < x_val := by rw [hx_def]; linarith
        linarith
      rw [hc'] at h_gt
      have hc'_gt : (5/2 : ℝ) < (c' : ℝ) := lt_of_mul_lt_mul_right h_gt h_2e_pos.le
      have hc'_ge3 : 3 ≤ c' := by
        have h2 : (2 : ℝ) < (c' : ℝ) := by linarith
        have h2' : 2 < c' := by exact_mod_cast h2
        omega
      change ((y_lo_g e : Dyadic) : ℝ) ≤ (z' : ℝ)
      rw [hc', coe_y_lo_g]
      have : (3 : ℝ) ≤ (c' : ℝ) := by exact_mod_cast hc'_ge3
      nlinarith
  have h_close_lo := h_close (y_lo_g e) h_y_lo_in_F₁ h_y_lo_faith
  rw [coe_y_lo_low_g, coe_y_lo_g] at h_close_lo
  have h_absL : |x_val - 2 * (2 : ℝ)^e|
      = (1/2) * (2 : ℝ)^e + (2 : ℝ)^(f₂ - 2) := by
    rw [hx_def, show (5/2) * (2 : ℝ)^e + (2 : ℝ)^(f₂ - 2) - 2 * (2 : ℝ)^e
        = (1/2) * (2 : ℝ)^e + (2 : ℝ)^(f₂ - 2) by ring]
    exact abs_of_pos (by nlinarith)
  have h_absR : |x_val - 3 * (2 : ℝ)^e|
      = (1/2) * (2 : ℝ)^e - (2 : ℝ)^(f₂ - 2) := by
    rw [hx_def, show (5/2) * (2 : ℝ)^e + (2 : ℝ)^(f₂ - 2) - 3 * (2 : ℝ)^e
        = -((1/2) * (2 : ℝ)^e - (2 : ℝ)^(f₂ - 2)) by ring, abs_neg]
    exact abs_of_pos (by linarith)
  rw [h_absL, h_absR] at h_close_lo
  linarith

end Cex

end Mpfx
