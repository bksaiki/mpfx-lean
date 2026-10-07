import Mpfx.Rounding.Defs
import Mpfx.Format.Discrete
import Mpfx.Format.Digits
import Mpfx.Rounding.Restrict

/-!
# Double-rounding counterexamples: shared lemmas

The quantum target format, its anchors, containment → exponent helpers,
the `F₂`-side local-grid interface, and parity lemmas.
-/

namespace Mpfx

namespace Cex

/-! ## The quantum target format `F₁_g = 𝒜(p, e, ⊤)` -/

/-- The quantum target format `𝒜(p, e, ⊤)` with precision `p ≥ 2`, quantum `2^e`,
unbounded magnitude. Built as a `ParityFormat`: both the `finite` and
`parity` invariants hold because `exp = (e : ℤ) ≠ ⊥`. -/
def F₁_g (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ) : ParityFormat where
  toFiniteFormat :=
    { toFormat := { p := (p : Prec), exp := (e : QExp), b := ⊤ }
      finite := Or.inr WithBot.coe_ne_bot
      pos := by simp; omega }
  parity := Or.inr WithBot.coe_ne_bot

@[simp] theorem F₁_g_p p (hp : 2 ≤ p) (e : ℤ) :
    (F₁_g p hp e).p = (p : Prec) := rfl

@[simp] theorem F₁_g_exp p (hp : 2 ≤ p) (e : ℤ) :
    (F₁_g p hp e).exp = (e : QExp) := rfl

@[simp] private theorem F₁_g_b p (hp : 2 ≤ p) (e : ℤ) :
    (F₁_g p hp e).b = ⊤ := rfl

/-! ### The grid anchors (as `Dyadic.ofIntZpow`) -/

noncomputable def y_lo_g (e : ℤ) : Dyadic := Dyadic.ofIntZpow 3 e
noncomputable def y_hi_g (e : ℤ) : Dyadic := Dyadic.ofIntZpow 1 (e + 2)

/-- `2^e` as a Dyadic, used as the smallest positive F₁_g-element witness. -/
noncomputable def two_e_g (e : ℤ) : Dyadic := Dyadic.ofIntZpow 1 e

noncomputable def m_g (e : ℤ) : Dyadic := Dyadic.ofIntZpow 7 (e - 1)

noncomputable def y_lo_low_g (e : ℤ) : Dyadic := Dyadic.ofIntZpow 2 e

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

/-! ### Membership lemmas -/

theorem y_lo_mem_F₁_g (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ) :
    y_lo_g e ∈ (F₁_g p hp_ge_2 e).toFormat := by
  refine ⟨?_, ?_, trivial⟩
  · -- precisionAtMost p: take (c=3, k=e). |3| < 2^p since p ≥ 2.
    change Dyadic.precisionAtMost (p : Prec) (y_lo_g e)
    rw [Dyadic.precisionAtMost_coe_real]
    refine ⟨3, e, ?_, ?_⟩
    · rw [coe_y_lo_g]; push_cast; ring
    · have h_pow : (4 : ℤ) ≤ (2 : ℤ)^p :=
        calc (4 : ℤ) = (2 : ℤ)^2 := by norm_num
          _ ≤ (2 : ℤ)^p := pow_le_pow_right₀ (by norm_num) hp_ge_2
      have h_abs : |(3 : ℤ)| = 3 := by decide
      omega
  · change Dyadic.quantumAtLeast (e : QExp) (y_lo_g e)
    rw [Dyadic.quantumAtLeast_coe_real]
    refine ⟨3, ?_⟩
    rw [coe_y_lo_g]; push_cast; ring

theorem two_e_mem_F₁_g (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ) :
    two_e_g e ∈ (F₁_g p hp_ge_2 e).toFormat := by
  refine ⟨?_, ?_, trivial⟩
  · change Dyadic.precisionAtMost (p : Prec) (two_e_g e)
    rw [Dyadic.precisionAtMost_coe_real]
    refine ⟨1, e, ?_, ?_⟩
    · rw [coe_two_e_g]; push_cast; ring
    · have h_pow : (2 : ℤ) ≤ (2 : ℤ)^p :=
        calc (2 : ℤ) = (2 : ℤ)^1 := by norm_num
          _ ≤ (2 : ℤ)^p := pow_le_pow_right₀ (by norm_num) (by omega)
      have : |(1 : ℤ)| = 1 := by decide
      omega
  · change Dyadic.quantumAtLeast (e : QExp) (two_e_g e)
    rw [Dyadic.quantumAtLeast_coe_real]
    exact ⟨1, by rw [coe_two_e_g]; push_cast; ring⟩

theorem y_hi_mem_F₁_g (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ) :
    y_hi_g e ∈ (F₁_g p hp_ge_2 e).toFormat := by
  refine ⟨?_, ?_, trivial⟩
  · change Dyadic.precisionAtMost (p : Prec) (y_hi_g e)
    rw [Dyadic.precisionAtMost_coe_real]
    refine ⟨1, e + 2, ?_, ?_⟩
    · rw [coe_y_hi_g]; push_cast; ring
    · have h_pow : (2 : ℤ) ≤ (2 : ℤ)^p :=
        calc (2 : ℤ) = (2 : ℤ)^1 := by norm_num
          _ ≤ (2 : ℤ)^p := pow_le_pow_right₀ (by norm_num) (by omega : 1 ≤ p)
      have h_abs : |(1 : ℤ)| = 1 := by decide
      omega
  · change Dyadic.quantumAtLeast (e : QExp) (y_hi_g e)
    rw [Dyadic.quantumAtLeast_coe_real]
    refine ⟨4, ?_⟩
    rw [coe_y_hi_g, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have : (2 : ℝ)^(2 : ℤ) = 4 := by norm_num
    rw [this]; push_cast; ring

theorem y_lo_low_mem_F₁_g (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ) :
    y_lo_low_g e ∈ (F₁_g p hp_ge_2 e).toFormat := by
  refine ⟨?_, ?_, trivial⟩
  · change Dyadic.precisionAtMost (p : Prec) (y_lo_low_g e)
    rw [Dyadic.precisionAtMost_coe_real]
    refine ⟨2, e, ?_, ?_⟩
    · rw [coe_y_lo_low_g]; push_cast; ring
    · have h_pow : (4 : ℤ) ≤ (2 : ℤ)^p :=
        calc (4 : ℤ) = (2 : ℤ)^2 := by norm_num
          _ ≤ (2 : ℤ)^p := pow_le_pow_right₀ (by norm_num) hp_ge_2
      have h_abs : |(2 : ℤ)| = 2 := by decide
      omega
  · change Dyadic.quantumAtLeast (e : QExp) (y_lo_low_g e)
    rw [Dyadic.quantumAtLeast_coe_real]
    refine ⟨2, ?_⟩
    rw [coe_y_lo_low_g]; push_cast; ring

/-- Quantum extraction: every `z ∈ F₁_g` is `c · 2^e` for some `c : ℤ`. -/
theorem F₁_g_quantum (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ)
    {z : Dyadic} (hz : z ∈ (F₁_g p hp_ge_2 e).toFormat) :
    ∃ c : ℤ, (z : ℝ) = (c : ℝ) * (2 : ℝ)^e := by
  have hq : Dyadic.quantumAtLeast (e : QExp) z := hz.2.1
  rw [Dyadic.quantumAtLeast_coe_real] at hq
  exact hq

/-! ## Containment → exponent helpers -/

/-- If `2^e ∈ F₂` and `F₂.exp = (f₂ : QExp)`, then `f₂ ≤ e`. -/
theorem f₂_le_e_of_two_e_mem {e : ℤ} {F₂ : Format}
    (h_two_e_in_F₂ : two_e_g e ∈ F₂)
    {f₂ : ℤ} (hF₂_exp : F₂.exp = (f₂ : QExp)) :
    f₂ ≤ e := by
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
    (hF₂_exp : F₂.exp = (f₂ : QExp))
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
theorem F₂_quantum_floor
    {F₂ : Format} {f₂ : ℤ} (hF₂_exp : F₂.exp = (f₂ : QExp))
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

/-- **F₂-grid ceiling** (dual of `F₂_quantum_floor`). Given
`target = c_target · 2^f₂` on F₂'s grid, any `z ∈ F₂` strictly above
`target − 2^f₂` is at least `target`. -/
theorem F₂_quantum_ceil
    {F₂ : Format} {f₂ : ℤ} (hF₂_exp : F₂.exp = (f₂ : QExp))
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

/-! ### Shape-generic local-grid interface

Near any anchor, every `F₂`-element is an integer multiple of a local
step `2^K`: the global quantum `2^f₂` when `F₂.exp = f₂` is finite, and
the binade step `2^(E−q₂+1)` when `F₂.exp = ⊥` (`binade_quantum`). The
dispatch lemmas below package the resulting gap bounds uniformly, so the
counterexamples never case-split on `F₂`'s shape. -/

private theorem two_zpow_add_three (t : ℤ) : (2 : ℝ)^(t + 3) = 8 * (2 : ℝ)^t := by
  rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
      show (2 : ℝ)^(3 : ℤ) = 8 from by norm_num]
  ring

/-- Two distinct multiples of `2^K` and `2^E` (`K ≤ E`) differ by at least
`2^K`. -/
private theorem gap_of_ne_aligned {c a K E : ℤ} (hK : K ≤ E)
    (hne : (c : ℝ) * (2 : ℝ) ^ K ≠ (a : ℝ) * (2 : ℝ) ^ E) :
    (2 : ℝ)^K ≤ |(c : ℝ) * (2 : ℝ)^K - (a : ℝ) * (2 : ℝ)^E| := by
  set j : ℕ := (E - K).toNat with hj
  have h_split : (2 : ℝ)^E = ((2 : ℤ)^j : ℝ) * (2 : ℝ)^K := two_zpow_split E K hK
  set m : ℤ := c - a * 2^j with hm
  have h_eq : (c : ℝ) * (2 : ℝ)^K - (a : ℝ) * (2 : ℝ)^E
      = (m : ℝ) * (2 : ℝ)^K := by
    rw [h_split, hm]; push_cast; ring
  have h2K_pos : (0 : ℝ) < (2 : ℝ)^K := zpow_pos (by norm_num) _
  have hm_ne : m ≠ 0 := by
    intro h0
    apply hne
    have hdiff : (c : ℝ) * (2 : ℝ)^K - (a : ℝ) * (2 : ℝ)^E = 0 := by
      rw [h_eq, h0]; norm_num
    linarith
  have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
    have h0 : (1 : ℤ) ≤ |m| := Int.one_le_abs hm_ne
    calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ ((|m| : ℤ) : ℝ) := by exact_mod_cast h0
      _ = |(m : ℝ)| := by rw [Int.cast_abs]
  rw [h_eq, abs_mul, abs_of_pos h2K_pos]
  nlinarith

/-- Two distinct multiples of `2^K` and `2^E` with the weaker alignment
`K ≤ E + 1` differ by at least `2^(K−1)`. -/
private theorem gap_of_ne_half_aligned {c a K E : ℤ} (hK : K ≤ E + 1)
    (hne : (c : ℝ) * (2 : ℝ) ^ K ≠ (a : ℝ) * (2 : ℝ) ^ E) :
    (2 : ℝ)^(K - 1) ≤ |(c : ℝ) * (2 : ℝ)^K - (a : ℝ) * (2 : ℝ)^E| := by
  have h2 : (2 : ℝ)^K = 2 * (2 : ℝ)^(K - 1) := by
    have h := two_zpow_succ (K - 1)
    rwa [show K - 1 + 1 = K by ring] at h
  have h_resc : ((2 * c : ℤ) : ℝ) * (2 : ℝ)^(K - 1) = (c : ℝ) * (2 : ℝ)^K := by
    rw [h2]; push_cast; ring
  have hne' : ((2 * c : ℤ) : ℝ) * (2 : ℝ)^(K - 1) ≠ (a : ℝ) * (2 : ℝ)^E := by
    rw [h_resc]; exact hne
  have h := gap_of_ne_aligned (c := 2 * c) (a := a) (K := K - 1) (E := E)
    (by omega) hne'
  rwa [h_resc] at h

/-- Package a two-sided distance bound `g ≤ |z − A|` into the below-side gap
`z ≤ A − g` (given `z < A`). Shared tail of the `gap_*` dispatch helpers,
absorbing the repeated `abs_sub_comm` / `abs_of_nonneg` / `linarith` step. -/
private theorem gap_bound_below {z A g : ℝ} (hz_lt : z < A) (h_gap : g ≤ |z - A|) :
    z ≤ A - g := by
  rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ A - z)] at h_gap
  linarith

/-- Dual of `gap_bound_below`: `g ≤ |z − A|` with `A < z` gives `A + g ≤ z`. -/
private theorem gap_bound_above {z A g : ℝ} (hz_gt : A < z) (h_gap : g ≤ |z - A|) :
    A + g ≤ z := by
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ z - A)] at h_gap
  linarith

/-- **Binade quantization.** In a format with finite precision `q₂`, every
element of the binade `[2^E, 2^(E+1))` is an integer multiple of the local
step `2^(E − q₂ + 1)`. -/
theorem binade_quantum {F₂ : FiniteFormat} {q₂ : ℕ}
    (hp : F₂.p = (q₂ : Prec)) {E : ℤ} {y : Dyadic}
    (hy : y ∈ F₂.toFormat)
    (h_lo : (2 : ℝ) ^ E ≤ ((y : Dyadic) : ℝ))
    (_h_hi : ((y : Dyadic) : ℝ) < (2 : ℝ) ^ (E + 1)) :
    ∃ c : ℤ, ((y : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ)^(E - q₂ + 1) := by
  have hprec : Dyadic.precisionAtMost F₂.p y := hy.1
  rw [hp, Dyadic.precisionAtMost_coe_real] at hprec
  obtain ⟨c, k, hck, hc_lt⟩ := hprec
  have h2E_pos : (0 : ℝ) < (2 : ℝ)^E := zpow_pos (by norm_num) _
  have h2k_pos : (0 : ℝ) < (2 : ℝ)^k := zpow_pos (by norm_num) _
  have hc_real_lt : (c : ℝ) < (2 : ℝ)^(q₂ : ℤ) := by
    have h1 : (c : ℝ) ≤ ((|c| : ℤ) : ℝ) := by
      rw [Int.cast_abs]; exact le_abs_self _
    have h2 : ((|c| : ℤ) : ℝ) < (((2 : ℤ)^q₂ : ℤ) : ℝ) := by
      exact_mod_cast hc_lt
    have h3 : (((2 : ℤ)^q₂ : ℤ) : ℝ) = (2 : ℝ)^(q₂ : ℤ) := by
      push_cast
      rw [← zpow_natCast (2 : ℝ) q₂]
    linarith
  have hk_ge : E - q₂ + 1 ≤ k := by
    by_contra h
    push Not at h
    have h_y_lt : ((y : Dyadic) : ℝ) < (2 : ℝ)^E := by
      rw [hck]
      calc (c : ℝ) * (2 : ℝ)^k
          < (2 : ℝ)^(q₂ : ℤ) * (2 : ℝ)^k := by nlinarith
        _ = (2 : ℝ)^((q₂ : ℤ) + k) := by
            rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        _ ≤ (2 : ℝ)^E := zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith
  refine ⟨c * 2^((k - (E - q₂ + 1)).toNat), ?_⟩
  rw [hck, two_zpow_split k (E - q₂ + 1) hk_ge]
  push_cast; ring

/-- An odd positive coefficient is visible to the precision: if
`y = a·2^e' ∈ F₂` with `a` odd and positive and `F₂.p = q₂`, then
`a < 2^q₂`. -/
theorem coeff_lt_of_odd_mem {F₂ : FiniteFormat} {q₂ : ℕ}
    (hp : F₂.p = (q₂ : Prec)) {a e' : ℤ}
    (ha_odd : Odd a) (ha_pos : 0 < a) {y : Dyadic} (hy : y ∈ F₂.toFormat)
    (hy_eq : ((y : Dyadic) : ℝ) = (a : ℝ) * (2 : ℝ) ^ e') :
    a < 2^q₂ := by
  have hprec : Dyadic.precisionAtMost F₂.p y := hy.1
  rw [hp, Dyadic.precisionAtMost_coe_real] at hprec
  obtain ⟨c, k, hck, hc_lt⟩ := hprec
  have h_eq : (c : ℝ) * (2 : ℝ)^k = (a : ℝ) * (2 : ℝ)^e' := by
    rw [← hck, hy_eq]
  rcases le_or_gt k e' with hk | hk
  · -- `c = a·2^(e'−k)`, so `a ≤ |c| < 2^q₂`.
    have h_split : (2 : ℝ)^e' = ((2 : ℤ)^(e' - k).toNat : ℝ) * (2 : ℝ)^k :=
      two_zpow_split e' k hk
    have h2k_pos : (0 : ℝ) < (2 : ℝ)^k := zpow_pos (by norm_num) _
    have hc_eq : (c : ℝ) = ((a * 2^(e' - k).toNat : ℤ) : ℝ) := by
      have h : (c : ℝ) * (2 : ℝ)^k
          = ((a * 2^(e' - k).toNat : ℤ) : ℝ) * (2 : ℝ)^k := by
        rw [h_eq, h_split]; push_cast; ring
      exact mul_right_cancel₀ (ne_of_gt h2k_pos) h
    have hc_int : c = a * 2^(e' - k).toNat := by exact_mod_cast hc_eq
    have h_pow_pos : (0 : ℤ) < 2^(e' - k).toNat := pow_pos (by norm_num) _
    have h_a_le : a ≤ |c| := by
      have h1 : a ≤ a * 2^(e' - k).toNat :=
        le_mul_of_one_le_right ha_pos.le (by omega)
      have h2 : |c| = c := abs_of_pos (by rw [hc_int]; positivity)
      omega
    omega
  · -- `k > e'`: then `a = c·2^(k−e')` is even, contradicting oddness.
    have h_split : (2 : ℝ)^k = ((2 : ℤ)^(k - e').toNat : ℝ) * (2 : ℝ)^e' :=
      two_zpow_split k e' hk.le
    have h2e_pos : (0 : ℝ) < (2 : ℝ)^e' := zpow_pos (by norm_num) _
    have ha_eq : (a : ℝ) = ((c * 2^(k - e').toNat : ℤ) : ℝ) := by
      have h : (a : ℝ) * (2 : ℝ)^e'
          = ((c * 2^(k - e').toNat : ℤ) : ℝ) * (2 : ℝ)^e' := by
        rw [← h_eq, h_split]; push_cast; ring
      exact mul_right_cancel₀ (ne_of_gt h2e_pos) h
    have ha_int : a = c * 2^(k - e').toNat := by exact_mod_cast ha_eq
    have h_even : Even a := by
      rw [ha_int, show (k - e').toNat = ((k - e').toNat - 1) + 1 from by omega,
          pow_succ]
      exact ⟨c * 2^((k - e').toNat - 1), by ring⟩
    rcases ha_odd with ⟨t, ht⟩
    rcases h_even with ⟨s, hs⟩
    omega

/-- `y_lo = 3·2^e ∈ F₂` forces at least 2 bits of precision. -/
theorem p_ge2_of_y_lo_mem {F₂ : FiniteFormat} {e : ℤ}
    (h3 : y_lo_g e ∈ F₂.toFormat) :
    ∀ q₂ : ℕ, F₂.p = (q₂ : Prec) → 2 ≤ q₂ := by
  intro q₂ hp
  have h := coeff_lt_of_odd_mem hp (by decide : Odd (3 : ℤ)) (by norm_num) h3
    (by rw [coe_y_lo_g]; push_cast; ring)
  by_contra hq
  push Not at hq
  have h1 : q₂ = 1 := by
    have h2 : 1 ≤ q₂ := F₂.p_pos hp
    omega
  rw [h1] at h
  norm_num at h

/-- **Shape dispatch: gap below `2^E`.** There is a local step `2^K`
(`K ≤ E`) such that every nonnegative `F₂`-element strictly below `2^E` is
at most `2^E − 2^K`. Needs `f₂ ≤ E` only when `F₂.exp = f₂` is finite. -/
theorem gap_below_pow (F₂ : FiniteFormat) {E : ℤ}
    (h_exp_le : ∀ f₂ : ℤ, F₂.exp = (f₂ : QExp) → f₂ ≤ E) :
    ∃ K : ℤ, K ≤ E ∧
      ∀ z ∈ F₂.toFormat, ((z : Dyadic) : ℝ) < (2 : ℝ)^E →
        ((z : Dyadic) : ℝ) ≤ (2 : ℝ)^E - (2 : ℝ)^K := by
  have h_one : ((1 : ℤ) : ℝ) * (2 : ℝ)^E = (2 : ℝ)^E := by push_cast; ring
  rcases hexp : F₂.exp with _ | f₂
  · -- `exp = ⊥`: finite precision `q₂`; the binade-(E−1) step.
    have hp_ne : F₂.p ≠ ⊤ := by
      rcases F₂.finite with h | h
      · exact h
      · exact absurd hexp h
    obtain ⟨q₂, hq₂_eq⟩ := WithTop.ne_top_iff_exists.mp hp_ne
    have hp : F₂.p = (q₂ : Prec) := hq₂_eq.symm
    have hq₂_one : 1 ≤ q₂ := F₂.p_pos hp
    refine ⟨E - q₂, by omega, ?_⟩
    intro z hz hz_lt
    have h2K_le : (2 : ℝ)^(E - q₂) ≤ (2 : ℝ)^(E - 1) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h_half : (2 : ℝ)^(E - 1) + (2 : ℝ)^(E - 1) = (2 : ℝ)^E := by
      have h := two_zpow_succ (E - 1)
      rw [show E - 1 + 1 = E by ring] at h
      linarith
    rcases lt_or_ge ((z : Dyadic) : ℝ) ((2 : ℝ)^(E - 1)) with h_below | h_in
    · -- Below the binade: `z < 2^(E−1) ≤ 2^E − 2^K`.
      linarith
    · -- In binade `E−1`: a multiple of `2^(E−q₂)` strictly below `2^E`.
      obtain ⟨c, hc⟩ := binade_quantum hp hz h_in
        (by rw [show E - 1 + 1 = E by ring]; exact hz_lt)
      rw [show E - 1 - (q₂ : ℤ) + 1 = E - q₂ by omega] at hc
      have hne : (c : ℝ) * (2 : ℝ)^(E - q₂) ≠ ((1 : ℤ) : ℝ) * (2 : ℝ)^E := by
        rw [h_one, ← hc]
        exact ne_of_lt hz_lt
      have h_gap := gap_of_ne_aligned (c := c) (a := 1)
        (K := E - q₂) (E := E) (by omega) hne
      rw [h_one, ← hc] at h_gap
      exact gap_bound_below hz_lt h_gap
  · -- `exp = f₂` finite: the global quantum grid.
    have hf₂E : f₂ ≤ E := h_exp_le f₂ hexp
    refine ⟨f₂, hf₂E, ?_⟩
    intro z hz hz_lt
    set n : ℕ := (E - f₂).toNat with hn
    have h2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
    have h_target : (2 : ℝ)^E - (2 : ℝ)^f₂
        = (((2 : ℤ)^n - 1 : ℤ) : ℝ) * (2 : ℝ)^f₂ := by
      have h_split : (2 : ℝ)^E = ((2 : ℤ)^n : ℝ) * (2 : ℝ)^f₂ :=
        two_zpow_split E f₂ hf₂E
      rw [h_split]; push_cast; ring
    apply F₂_quantum_floor hexp h_target z hz
    linarith

/-- **Shape dispatch: gap above `2^E`.** There is a local step `2^K`
(`K ≤ E`) such that every `F₂`-element strictly above `2^E` is at least
`2^E + 2^K`. Needs `f₂ ≤ E` only when `F₂.exp = f₂` is finite. -/
theorem gap_above_pow (F₂ : FiniteFormat) {E : ℤ}
    (h_exp_le : ∀ f₂ : ℤ, F₂.exp = (f₂ : QExp) → f₂ ≤ E) :
    ∃ K : ℤ, K ≤ E ∧
      ∀ z ∈ F₂.toFormat, (2 : ℝ)^E < ((z : Dyadic) : ℝ) →
        (2 : ℝ)^E + (2 : ℝ)^K ≤ ((z : Dyadic) : ℝ) := by
  have h_one : ((1 : ℤ) : ℝ) * (2 : ℝ)^E = (2 : ℝ)^E := by push_cast; ring
  have h2E_pos : (0 : ℝ) < (2 : ℝ)^E := zpow_pos (by norm_num) _
  have h_double : (2 : ℝ)^(E + 1) = (2 : ℝ)^E + (2 : ℝ)^E := by
    have h := two_zpow_succ E
    linarith
  rcases hexp : F₂.exp with _ | f₂
  · -- `exp = ⊥`: finite precision `q₂`; the binade-E step.
    have hp_ne : F₂.p ≠ ⊤ := by
      rcases F₂.finite with h | h
      · exact h
      · exact absurd hexp h
    obtain ⟨q₂, hq₂_eq⟩ := WithTop.ne_top_iff_exists.mp hp_ne
    have hp : F₂.p = (q₂ : Prec) := hq₂_eq.symm
    have hq₂_one : 1 ≤ q₂ := F₂.p_pos hp
    refine ⟨E - q₂ + 1, by omega, ?_⟩
    intro z hz hz_gt
    have h2K_le : (2 : ℝ)^(E - q₂ + 1) ≤ (2 : ℝ)^E :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    rcases lt_or_ge ((z : Dyadic) : ℝ) ((2 : ℝ)^(E + 1)) with h_in | h_above
    · -- In binade `E`: a multiple of `2^(E−q₂+1)` strictly above `2^E`.
      obtain ⟨c, hc⟩ := binade_quantum hp hz (by linarith) h_in
      have hne : (c : ℝ) * (2 : ℝ)^(E - q₂ + 1)
          ≠ ((1 : ℤ) : ℝ) * (2 : ℝ)^E := by
        rw [h_one, ← hc]
        exact (ne_of_lt hz_gt).symm
      have h_gap := gap_of_ne_aligned (c := c) (a := 1)
        (K := E - q₂ + 1) (E := E) (by omega) hne
      rw [h_one, ← hc] at h_gap
      exact gap_bound_above hz_gt h_gap
    · -- At or above the binade top: `z ≥ 2^(E+1) = 2^E + 2^E ≥ 2^E + 2^K`.
      linarith
  · -- `exp = f₂` finite: the global quantum grid.
    have hf₂E : f₂ ≤ E := h_exp_le f₂ hexp
    refine ⟨f₂, hf₂E, ?_⟩
    intro z hz hz_gt
    set n : ℕ := (E - f₂).toNat with hn
    have h2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
    have h_target : (2 : ℝ)^E + (2 : ℝ)^f₂
        = (((2 : ℤ)^n + 1 : ℤ) : ℝ) * (2 : ℝ)^f₂ := by
      have h_split : (2 : ℝ)^E = ((2 : ℤ)^n : ℝ) * (2 : ℝ)^f₂ :=
        two_zpow_split E f₂ hf₂E
      rw [h_split]; push_cast; ring
    apply F₂_quantum_ceil hexp h_target z hz
    linarith

/-- Rebase a two-sided gap of half-width `D` from anchor `A` to an equal
anchor `B`. Used to turn the gap lemmas' anchor-in-`a·2^k` form into the
neighborhood fields' anchor-in-grid-coordinates form once `h_A : A = B`. -/
theorem rebase_gap {F₂ : FiniteFormat} {A B D : ℝ} (h_A : A = B)
    (h_below : ∀ z ∈ F₂.toFormat, ((z : Dyadic) : ℝ) < A →
      ((z : Dyadic) : ℝ) ≤ A - D)
    (h_above : ∀ z ∈ F₂.toFormat, A < ((z : Dyadic) : ℝ) →
      A + D ≤ ((z : Dyadic) : ℝ)) :
    (∀ z ∈ F₂.toFormat, ((z : Dyadic) : ℝ) < B →
        ((z : Dyadic) : ℝ) ≤ B - D) ∧
    (∀ z ∈ F₂.toFormat, B < ((z : Dyadic) : ℝ) →
        B + D ≤ ((z : Dyadic) : ℝ)) := by
  subst h_A; exact ⟨h_below, h_above⟩

/-- **Shape dispatch: gaps around an off-grid midpoint** `A = a·2^(e−1)`,
`5 ≤ a ≤ 7`. There is a local step `2^K` (`K ≤ e`) such that `F₂`-elements
keep distance `2^(K−1)` from `A` on both sides. Needs `f₂ ≤ e` when
`F₂.exp = f₂` is finite, and (when `F₂.exp = ⊥`) at least two bits of
precision, provided by `h_p_ge2`. -/
theorem gap_around_mid (F₂ : FiniteFormat) {e a : ℤ}
    (ha_lo : 5 ≤ a) (ha_hi : a ≤ 7)
    (h_exp_le : ∀ f₂ : ℤ, F₂.exp = (f₂ : QExp) → f₂ ≤ e)
    (h_p_ge2 : ∀ q₂ : ℕ, F₂.p = (q₂ : Prec) → 2 ≤ q₂) :
    ∃ K : ℤ, K ≤ e ∧
      (∀ z ∈ F₂.toFormat, ((z : Dyadic) : ℝ) < (a : ℝ) * (2 : ℝ)^(e - 1) →
        ((z : Dyadic) : ℝ) ≤ (a : ℝ) * (2 : ℝ)^(e - 1) - (2 : ℝ)^(K - 1)) ∧
      (∀ z ∈ F₂.toFormat, (a : ℝ) * (2 : ℝ)^(e - 1) < ((z : Dyadic) : ℝ) →
        (a : ℝ) * (2 : ℝ)^(e - 1) + (2 : ℝ)^(K - 1) ≤ ((z : Dyadic) : ℝ)) := by
  have h2e1_pos : (0 : ℝ) < (2 : ℝ)^(e - 1) := zpow_pos (by norm_num) _
  have ha_lo_r : (5 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha_lo
  have ha_hi_r : (a : ℝ) ≤ (7 : ℝ) := by exact_mod_cast ha_hi
  have h_A_lo : (5 : ℝ) * (2 : ℝ)^(e - 1) ≤ (a : ℝ) * (2 : ℝ)^(e - 1) := by
    nlinarith
  have h_A_hi : (a : ℝ) * (2 : ℝ)^(e - 1) ≤ (7 : ℝ) * (2 : ℝ)^(e - 1) := by
    nlinarith
  have h_e1_split : (2 : ℝ)^(e + 1) = (4 : ℝ) * (2 : ℝ)^(e - 1) := by
    have h := two_zpow_add_two (e - 1)
    rwa [show e - 1 + 2 = e + 1 by ring] at h
  have h_e2_split : (2 : ℝ)^(e + 2) = (8 : ℝ) * (2 : ℝ)^(e - 1) := by
    have h := two_zpow_add_three (e - 1)
    rwa [show e - 1 + 3 = e + 2 by ring] at h
  rcases hexp : F₂.exp with _ | f₂
  · -- `exp = ⊥`: finite precision `q₂ ≥ 2`; the binade-(e+1) step.
    have hp_ne : F₂.p ≠ ⊤ := by
      rcases F₂.finite with h | h
      · exact h
      · exact absurd hexp h
    obtain ⟨q₂, hq₂_eq⟩ := WithTop.ne_top_iff_exists.mp hp_ne
    have hp : F₂.p = (q₂ : Prec) := hq₂_eq.symm
    have hq₂_two : 2 ≤ q₂ := h_p_ge2 q₂ hp
    refine ⟨e - q₂ + 2, by omega, ?_, ?_⟩
    all_goals
      have h2K1_le : (2 : ℝ)^(e - q₂ + 2 - 1) ≤ (2 : ℝ)^(e - 1) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
    · intro z hz hz_lt
      rcases lt_or_ge ((z : Dyadic) : ℝ) ((2 : ℝ)^(e + 1)) with h_below | h_in
      · -- Below the binade: `z < 4·2^(e−1) ≤ A − 2^(K−1)`.
        rw [h_e1_split] at h_below
        linarith
      · -- In binade `e+1`: a multiple of `2^K` distinct from `A`.
        have h_in_hi : ((z : Dyadic) : ℝ) < (2 : ℝ)^(e + 1 + 1) := by
          rw [show e + 1 + 1 = e + 2 by ring, h_e2_split]
          linarith
        obtain ⟨c, hc⟩ := binade_quantum hp hz h_in h_in_hi
        rw [show e + 1 - (q₂ : ℤ) + 1 = e - q₂ + 2 by omega] at hc
        have hne : (c : ℝ) * (2 : ℝ)^(e - q₂ + 2)
            ≠ (a : ℝ) * (2 : ℝ)^(e - 1) := by
          rw [← hc]
          exact ne_of_lt hz_lt
        have h_gap := gap_of_ne_half_aligned (c := c) (a := a)
          (K := e - q₂ + 2) (E := e - 1) (by omega) hne
        rw [← hc] at h_gap
        exact gap_bound_below hz_lt h_gap
    · intro z hz hz_gt
      rcases lt_or_ge ((z : Dyadic) : ℝ) ((2 : ℝ)^(e + 2)) with h_in | h_above
      · -- In binade `e+1` (since `z > A ≥ 5·2^(e−1) > 2^(e+1)`).
        have h_in_lo : (2 : ℝ)^(e + 1) ≤ ((z : Dyadic) : ℝ) := by
          rw [h_e1_split]
          linarith
        have h_in_hi : ((z : Dyadic) : ℝ) < (2 : ℝ)^(e + 1 + 1) := by
          rw [show e + 1 + 1 = e + 2 by ring]
          exact h_in
        obtain ⟨c, hc⟩ := binade_quantum hp hz h_in_lo h_in_hi
        rw [show e + 1 - (q₂ : ℤ) + 1 = e - q₂ + 2 by omega] at hc
        have hne : (c : ℝ) * (2 : ℝ)^(e - q₂ + 2)
            ≠ (a : ℝ) * (2 : ℝ)^(e - 1) := by
          rw [← hc]
          exact (ne_of_lt hz_gt).symm
        have h_gap := gap_of_ne_half_aligned (c := c) (a := a)
          (K := e - q₂ + 2) (E := e - 1) (by omega) hne
        rw [← hc] at h_gap
        exact gap_bound_above hz_gt h_gap
      · -- At or above the binade top: `z ≥ 8·2^(e−1) ≥ A + 2^(K−1)`.
        rw [h_e2_split] at h_above
        linarith
  · -- `exp = f₂` finite: the global quantum grid; `K = f₂ ≤ e`.
    have hexpc : F₂.exp = (f₂ : QExp) := hexp
    have hf₂e : f₂ ≤ e := h_exp_le f₂ hexpc
    refine ⟨f₂, hf₂e, ?_, ?_⟩
    all_goals
      have h2f1_le : (2 : ℝ)^(f₂ - 1) ≤ (2 : ℝ)^(e - 1) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
    · intro z hz hz_lt
      obtain ⟨_, hq, _⟩ := hz
      rw [hexpc, Dyadic.quantumAtLeast_coe_real] at hq
      obtain ⟨c, hc⟩ := hq
      have hne : (c : ℝ) * (2 : ℝ)^f₂ ≠ (a : ℝ) * (2 : ℝ)^(e - 1) := by
        rw [← hc]
        exact ne_of_lt hz_lt
      have h_gap := gap_of_ne_half_aligned (c := c) (a := a)
        (K := f₂) (E := e - 1) (by omega) hne
      rw [← hc] at h_gap
      exact gap_bound_below hz_lt h_gap
    · intro z hz hz_gt
      obtain ⟨_, hq, _⟩ := hz
      rw [hexpc, Dyadic.quantumAtLeast_coe_real] at hq
      obtain ⟨c, hc⟩ := hq
      have hne : (c : ℝ) * (2 : ℝ)^f₂ ≠ (a : ℝ) * (2 : ℝ)^(e - 1) := by
        rw [← hc]
        exact (ne_of_lt hz_gt).symm
      have h_gap := gap_of_ne_half_aligned (c := c) (a := a)
        (K := f₂) (E := e - 1) (by omega) hne
      rw [← hc] at h_gap
      exact gap_bound_above hz_gt h_gap

/-- **Full-step gaps around a representable odd multiple.** For odd `c` with
`2^j < c < 2^(j+1)`, if `c·2^(e−1) ∈ F₂` then there is a local step `2^K`
(`K ≤ e − 1`) with every other `F₂`-element at distance at least `2^K` from
`c·2^(e−1)` on both sides.

`j` is where the constant enters: it places `c·2^(e−1)` in the binade
`[2^(e−1+j), 2^(e−1+j+1))`. -/
private theorem gap_around_odd_mem (F₂ : FiniteFormat) {c : ℤ} {j : ℕ} {e : ℤ}
    (hc_odd : Odd c) (hc_lo : (2 : ℤ) ^ j < c) (hc_hi : c < (2 : ℤ) ^ (j + 1))
    (hm : Dyadic.ofIntZpow c (e - 1) ∈ F₂.toFormat) :
    ∃ K : ℤ, K ≤ e - 1 ∧
      (∀ z ∈ F₂.toFormat, ((z : Dyadic) : ℝ) < (c : ℝ) * (2 : ℝ) ^ (e - 1) →
        ((z : Dyadic) : ℝ) ≤ (c : ℝ) * (2 : ℝ) ^ (e - 1) - (2 : ℝ) ^ K) ∧
      (∀ z ∈ F₂.toFormat, (c : ℝ) * (2 : ℝ) ^ (e - 1) < ((z : Dyadic) : ℝ) →
        (c : ℝ) * (2 : ℝ) ^ (e - 1) + (2 : ℝ) ^ K ≤ ((z : Dyadic) : ℝ)) := by
  have hc_pos : 0 < c := lt_trans (by positivity) hc_lo
  have hm_eq : ((Dyadic.ofIntZpow c (e - 1) : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ) ^ (e - 1) :=
    Dyadic.coe_ofIntZpow _ _
  have h2e1_pos : (0 : ℝ) < (2 : ℝ) ^ (e - 1) := zpow_pos (by norm_num) _
  -- the two binade walls, as multiples of `2 ^ (e − 1)`
  have hsplit : ∀ n : ℕ, (2 : ℝ) ^ (e - 1 + (n : ℤ)) = (2 : ℝ) ^ n * (2 : ℝ) ^ (e - 1) := by
    intro n; rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]; ring
  have hcR_lo : (2 : ℝ) ^ j + 1 ≤ (c : ℝ) := by
    exact_mod_cast Int.add_one_le_iff.mpr hc_lo
  have hcR_hi : (c : ℝ) + 1 ≤ (2 : ℝ) ^ (j + 1) := by
    exact_mod_cast Int.add_one_le_iff.mpr hc_hi
  rcases hexp : F₂.exp with _ | f₂
  · -- `exp = ⊥`: membership bounds the coefficient, giving a binade-wide step
    have hp_ne : F₂.p ≠ ⊤ := by
      rcases F₂.finite with h | h
      · exact h
      · exact absurd hexp h
    obtain ⟨q₂, hq₂_eq⟩ := WithTop.ne_top_iff_exists.mp hp_ne
    have hp : F₂.p = (q₂ : Prec) := hq₂_eq.symm
    have hcq := coeff_lt_of_odd_mem hp hc_odd hc_pos hm hm_eq
    have hq₂_ge : (j : ℤ) + 1 ≤ (q₂ : ℤ) := by
      have h : (2 : ℤ) ^ j < 2 ^ q₂ := lt_trans hc_lo hcq
      have : j < q₂ := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℤ) < 2)).mp h
      omega
    refine ⟨e - 1 + (j : ℤ) - (q₂ : ℤ) + 1, by omega, ?_, ?_⟩ <;>
      set K : ℤ := e - 1 + (j : ℤ) - (q₂ : ℤ) + 1 with hK_def <;>
      have hK_le : (2 : ℝ) ^ K ≤ (2 : ℝ) ^ (e - 1) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega) <;>
      have h_m_rep : (c : ℝ) * (2 : ℝ) ^ (e - 1)
          = ((c * (2 : ℤ) ^ ((e - 1) - K).toNat : ℤ) : ℝ) * (2 : ℝ) ^ K := by
        rw [two_zpow_split (e - 1) K (by omega)]; push_cast; ring
    · intro z hz hz_lt
      rcases lt_or_ge ((z : Dyadic) : ℝ) ((2 : ℝ) ^ (e - 1 + (j : ℤ))) with h_below | h_in
      · rw [hsplit] at h_below; nlinarith
      · have h_in_hi : ((z : Dyadic) : ℝ) < (2 : ℝ) ^ (e - 1 + (j : ℤ) + 1) := by
          rw [show e - 1 + (j : ℤ) + 1 = e - 1 + ((j + 1 : ℕ) : ℤ) by push_cast; ring, hsplit]
          nlinarith
        obtain ⟨c', hc'⟩ := binade_quantum hp hz h_in h_in_hi
        rw [show e - 1 + (j : ℤ) - (q₂ : ℤ) + 1 = K from hK_def.symm] at hc'
        have h_gap := gap_of_ne_aligned (c := c')
          (a := c * (2 : ℤ) ^ ((e - 1) - K).toNat) (K := K) (E := K) le_rfl
          (by rw [← hc', ← h_m_rep]; exact ne_of_lt hz_lt)
        rw [← hc', ← h_m_rep] at h_gap
        exact gap_bound_below hz_lt h_gap
    · intro z hz hz_gt
      rcases lt_or_ge ((z : Dyadic) : ℝ) ((2 : ℝ) ^ (e - 1 + ((j + 1 : ℕ) : ℤ))) with h_in | h_above
      · have h_in_lo : (2 : ℝ) ^ (e - 1 + (j : ℤ)) ≤ ((z : Dyadic) : ℝ) := by
          rw [hsplit]; nlinarith
        have h_in_hi : ((z : Dyadic) : ℝ) < (2 : ℝ) ^ (e - 1 + (j : ℤ) + 1) := by
          rw [show e - 1 + (j : ℤ) + 1 = e - 1 + ((j + 1 : ℕ) : ℤ) by push_cast; ring]; exact h_in
        obtain ⟨c', hc'⟩ := binade_quantum hp hz h_in_lo h_in_hi
        rw [show e - 1 + (j : ℤ) - (q₂ : ℤ) + 1 = K from hK_def.symm] at hc'
        have h_gap := gap_of_ne_aligned (c := c')
          (a := c * (2 : ℤ) ^ ((e - 1) - K).toNat) (K := K) (E := K) le_rfl
          (by rw [← hc', ← h_m_rep]; exact (ne_of_lt hz_gt).symm)
        rw [← hc', ← h_m_rep] at h_gap
        exact gap_bound_above hz_gt h_gap
      · rw [hsplit] at h_above; nlinarith
  · -- `exp = f₂`: every element sits on the quantum grid `2 ^ f₂`, and `f₂ ≤ e − 1`
    have hexpc : F₂.exp = (f₂ : QExp) := hexp
    have hf₂_le : f₂ ≤ e - 1 := f₂_le_e_sub_one_of_odd_in_F₂ hexpc hm hc_odd hm_eq
    have h_m_rep : (c : ℝ) * (2 : ℝ) ^ (e - 1)
        = ((c * (2 : ℤ) ^ ((e - 1) - f₂).toNat : ℤ) : ℝ) * (2 : ℝ) ^ f₂ := by
      rw [two_zpow_split (e - 1) f₂ hf₂_le]; push_cast; ring
    refine ⟨f₂, hf₂_le, ?_, ?_⟩ <;> intro z hz hz_cmp <;>
      obtain ⟨_, hq, _⟩ := hz <;>
      rw [hexpc, Dyadic.quantumAtLeast_coe_real] at hq <;>
      obtain ⟨c', hc'⟩ := hq
    · have h_gap := gap_of_ne_aligned (c := c')
        (a := c * (2 : ℤ) ^ ((e - 1) - f₂).toNat) (K := f₂) (E := f₂) le_rfl
        (by rw [← hc', ← h_m_rep]; exact ne_of_lt hz_cmp)
      rw [← hc', ← h_m_rep] at h_gap
      exact gap_bound_below hz_cmp h_gap
    · have h_gap := gap_of_ne_aligned (c := c')
        (a := c * (2 : ℤ) ^ ((e - 1) - f₂).toNat) (K := f₂) (E := f₂) le_rfl
        (by rw [← hc', ← h_m_rep]; exact (ne_of_lt hz_cmp).symm)
      rw [← hc', ← h_m_rep] at h_gap
      exact gap_bound_above hz_cmp h_gap

/-- **Full-step gaps around `m = 7·2^(e−1)` when `m ∈ F₂`.** -/
theorem gap_around_m_mem (F₂ : FiniteFormat) {e : ℤ}
    (hm : m_g e ∈ F₂.toFormat) :
    ∃ K : ℤ, K ≤ e - 1 ∧
      (∀ z ∈ F₂.toFormat, ((z : Dyadic) : ℝ) < (7 : ℝ) * (2 : ℝ)^(e - 1) →
        ((z : Dyadic) : ℝ) ≤ (7 : ℝ) * (2 : ℝ)^(e - 1) - (2 : ℝ)^K) ∧
      (∀ z ∈ F₂.toFormat, (7 : ℝ) * (2 : ℝ)^(e - 1) < ((z : Dyadic) : ℝ) →
        (7 : ℝ) * (2 : ℝ)^(e - 1) + (2 : ℝ)^K ≤ ((z : Dyadic) : ℝ)) := by
  simpa using gap_around_odd_mem F₂ (c := 7) (j := 2) (by decide) (by norm_num) (by norm_num) hm

/-- **Shape dispatch for `a = 3`: half-step gaps around `A = 3·2^(E−1)`.**
The midpoints of the power-of-two neighborhood are odd multiples `3·2^k`,
which sit in the binade `[2^E, 2^(E+1))` (`E = k + 1`) rather than the
`a ∈ [5,7]` binade. Here `q₂ ≥ 1` suffices (no two-bit hypothesis). -/
theorem gap_around_mid3 (F₂ : FiniteFormat) {E : ℤ}
    (h_exp_le : ∀ f₂ : ℤ, F₂.exp = (f₂ : QExp) → f₂ ≤ E) :
    ∃ K : ℤ, K ≤ E ∧
      (∀ z ∈ F₂.toFormat, ((z : Dyadic) : ℝ) < (3 : ℝ) * (2 : ℝ)^(E - 1) →
        ((z : Dyadic) : ℝ) ≤ (3 : ℝ) * (2 : ℝ)^(E - 1) - (2 : ℝ)^(K - 1)) ∧
      (∀ z ∈ F₂.toFormat, (3 : ℝ) * (2 : ℝ)^(E - 1) < ((z : Dyadic) : ℝ) →
        (3 : ℝ) * (2 : ℝ)^(E - 1) + (2 : ℝ)^(K - 1) ≤ ((z : Dyadic) : ℝ)) := by
  have h2E1_pos : (0 : ℝ) < (2 : ℝ)^(E - 1) := zpow_pos (by norm_num) _
  have h_lo_split : (2 : ℝ)^E = (2 : ℝ) * (2 : ℝ)^(E - 1) := by
    have h := two_zpow_succ (E - 1)
    rwa [show E - 1 + 1 = E by ring] at h
  have h_hi_split : (2 : ℝ)^(E + 1) = (4 : ℝ) * (2 : ℝ)^(E - 1) := by
    have h := two_zpow_add_two (E - 1)
    rwa [show E - 1 + 2 = E + 1 by ring] at h
  rcases hexp : F₂.exp with _ | f₂
  · -- `exp = ⊥`: finite precision `q₂ ≥ 1`; the binade-`E` step.
    have hp_ne : F₂.p ≠ ⊤ := by
      rcases F₂.finite with h | h
      · exact h
      · exact absurd hexp h
    obtain ⟨q₂, hq₂_eq⟩ := WithTop.ne_top_iff_exists.mp hp_ne
    have hp : F₂.p = (q₂ : Prec) := hq₂_eq.symm
    have hq₂_one : 1 ≤ q₂ := F₂.p_pos hp
    refine ⟨E - q₂ + 1, by omega, ?_, ?_⟩
    all_goals
      have h2K1_le : (2 : ℝ)^(E - q₂ + 1 - 1) ≤ (2 : ℝ)^(E - 1) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
    · intro z hz hz_lt
      rcases lt_or_ge ((z : Dyadic) : ℝ) ((2 : ℝ)^E) with h_below | h_in
      · rw [h_lo_split] at h_below
        linarith
      · have h_in_hi : ((z : Dyadic) : ℝ) < (2 : ℝ)^(E + 1) := by
          rw [h_hi_split]; linarith
        obtain ⟨c, hc⟩ := binade_quantum hp hz h_in h_in_hi
        rw [show E - (q₂ : ℤ) + 1 = E - q₂ + 1 by ring] at hc
        have hne : (c : ℝ) * (2 : ℝ)^(E - q₂ + 1)
            ≠ (3 : ℝ) * (2 : ℝ)^(E - 1) := by
          rw [← hc]; exact ne_of_lt hz_lt
        have h_gap := gap_of_ne_half_aligned (c := c) (a := 3)
          (K := E - q₂ + 1) (E := E - 1) (by omega) hne
        push_cast at h_gap
        rw [← hc] at h_gap
        exact gap_bound_below hz_lt h_gap
    · intro z hz hz_gt
      rcases lt_or_ge ((z : Dyadic) : ℝ) ((2 : ℝ)^(E + 1)) with h_in | h_above
      · have h_in_lo : (2 : ℝ)^E ≤ ((z : Dyadic) : ℝ) := by
          rw [h_lo_split]; linarith
        obtain ⟨c, hc⟩ := binade_quantum hp hz h_in_lo h_in
        rw [show E - (q₂ : ℤ) + 1 = E - q₂ + 1 by ring] at hc
        have hne : (c : ℝ) * (2 : ℝ)^(E - q₂ + 1)
            ≠ (3 : ℝ) * (2 : ℝ)^(E - 1) := by
          rw [← hc]; exact (ne_of_lt hz_gt).symm
        have h_gap := gap_of_ne_half_aligned (c := c) (a := 3)
          (K := E - q₂ + 1) (E := E - 1) (by omega) hne
        push_cast at h_gap
        rw [← hc] at h_gap
        exact gap_bound_above hz_gt h_gap
      · rw [h_hi_split] at h_above
        linarith
  · -- `exp = f₂` finite: the global quantum grid; `K = f₂ ≤ E`.
    have hexpc : F₂.exp = (f₂ : QExp) := hexp
    have hf₂e : f₂ ≤ E := h_exp_le f₂ hexpc
    refine ⟨f₂, hf₂e, ?_, ?_⟩
    · intro z hz hz_lt
      obtain ⟨_, hq, _⟩ := hz
      rw [hexpc, Dyadic.quantumAtLeast_coe_real] at hq
      obtain ⟨c, hc⟩ := hq
      have hne : (c : ℝ) * (2 : ℝ)^f₂ ≠ (3 : ℝ) * (2 : ℝ)^(E - 1) := by
        rw [← hc]; exact ne_of_lt hz_lt
      have h_gap := gap_of_ne_half_aligned (c := c) (a := 3)
        (K := f₂) (E := E - 1) (by omega) hne
      push_cast at h_gap
      rw [← hc] at h_gap
      exact gap_bound_below hz_lt h_gap
    · intro z hz hz_gt
      obtain ⟨_, hq, _⟩ := hz
      rw [hexpc, Dyadic.quantumAtLeast_coe_real] at hq
      obtain ⟨c, hc⟩ := hq
      have hne : (c : ℝ) * (2 : ℝ)^f₂ ≠ (3 : ℝ) * (2 : ℝ)^(E - 1) := by
        rw [← hc]; exact (ne_of_lt hz_gt).symm
      have h_gap := gap_of_ne_half_aligned (c := c) (a := 3)
        (K := f₂) (E := E - 1) (by omega) hne
      push_cast at h_gap
      rw [← hc] at h_gap
      exact gap_bound_above hz_gt h_gap

/-- **Full-step gaps around `A = 3·2^(E−1)` when `A ∈ F₂`.** -/
theorem gap_around_mid3_mem (F₂ : FiniteFormat) {E : ℤ}
    (hm : Dyadic.ofIntZpow 3 (E - 1) ∈ F₂.toFormat) :
    ∃ K : ℤ, K ≤ E - 1 ∧
      (∀ z ∈ F₂.toFormat, ((z : Dyadic) : ℝ) < (3 : ℝ) * (2 : ℝ)^(E - 1) →
        ((z : Dyadic) : ℝ) ≤ (3 : ℝ) * (2 : ℝ)^(E - 1) - (2 : ℝ)^K) ∧
      (∀ z ∈ F₂.toFormat, (3 : ℝ) * (2 : ℝ)^(E - 1) < ((z : Dyadic) : ℝ) →
        (3 : ℝ) * (2 : ℝ)^(E - 1) + (2 : ℝ)^K ≤ ((z : Dyadic) : ℝ)) := by
  simpa using gap_around_odd_mem F₂ (c := 3) (j := 1) (by decide) (by norm_num) (by norm_num) hm

/-! ## Parity lemmas -/

/-- `numDigits` of an anchor `x = 2^N` in the quantum grid `F₁_g` is
`min p (N − e + 1)`. -/
private theorem F₁_g_numDigits (p : ℕ) (hp : 2 ≤ p) (e : ℤ) {x : ℝ} {N : ℤ}
    (hx : x = (2 : ℝ) ^ N) :
    (F₁_g p hp e).toFiniteFormat.numDigits x = min (p : ℤ) (N - e + 1) := by
  have h_pos : (0 : ℝ) < (2 : ℝ) ^ N := zpow_pos (by norm_num) _
  have h_ne : x ≠ 0 := by rw [hx]; exact ne_of_gt h_pos
  rw [(F₁_g p hp e).toFiniteFormat.numDigits_coe_coe h_ne
    (F₁_g_p p hp e) (F₁_g_exp p hp e), hx, abs_of_pos h_pos, log_two_zpow]

/-- `IsEven F₁ (4·2^e)` for any `p ≥ 2`. -/
theorem isEven_F₁_g_y_hi (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ) :
    (F₁_g p hp_ge_2 e).IsEven (y_hi_g e) := by
  have h_coe_rat : ((y_hi_g e : Dyadic) : ℚ) = (2 : ℚ)^(e + 2) := by
    change ((Dyadic.ofIntZpow 1 (e + 2) : Dyadic) : ℚ) = _
    rw [Dyadic.coe_rat_ofIntZpow]; push_cast; ring
  -- Compute numDigits = min p 3.
  have h_nd : (F₁_g p hp_ge_2 e).toFiniteFormat.numDigits ((y_hi_g e : Dyadic) : ℝ)
        = min (p : ℤ) 3 := by
    rw [F₁_g_numDigits p hp_ge_2 e (coe_y_hi_g e), show e + 2 - e + 1 = 3 from by ring]
  have h_p_ne_1 : (F₁_g p hp_ge_2 e).p ≠ ((1 : ℕ) : Prec) := by
    rw [F₁_g_p]
    intro h
    have : (p) = (1 : ℕ) := by exact_mod_cast h
    have : p = 1 := by exact_mod_cast this
    omega
  right
  -- Case split on whether numDigits is 2 (p = 2) or 3 (p ≥ 3).
  rcases (lt_or_ge p 3) with hp_lt | hp_ge
  · -- p = 2 (since 2 ≤ p < 3).
    have hp_eq : p = 2 := by omega
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
      have h_min : min (p : ℤ) 3 = 3 := by
        have : (p : ℤ) ≥ 3 := by exact_mod_cast hp_ge
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
theorem notIsOdd_F₁_g_y_hi (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ) :
    ¬ (F₁_g p hp_ge_2 e).IsOdd (y_hi_g e) := by
  have h_coe_rat : ((y_hi_g e : Dyadic) : ℚ) = (2 : ℚ)^(e + 2) := by
    change ((Dyadic.ofIntZpow 1 (e + 2) : Dyadic) : ℚ) = _
    rw [Dyadic.coe_rat_ofIntZpow]; push_cast; ring
  have h_nd_eq : (F₁_g p hp_ge_2 e).toFiniteFormat.numDigits ((y_hi_g e : Dyadic) : ℝ)
        = min (p : ℤ) 3 := by
    rw [F₁_g_numDigits p hp_ge_2 e (coe_y_hi_g e), show e + 2 - e + 1 = 3 from by ring]
  have h_prec : Dyadic.precisionAtMost ((1 : ℕ) : Prec) (y_hi_g e) := by
    rw [Dyadic.precisionAtMost_coe]
    refine ⟨1, e + 2, ?_, ?_⟩
    · rw [h_coe_rat]; push_cast; ring
    · decide
  have h_gt : ((1 : ℕ) : ℤ) < (F₁_g p hp_ge_2 e).toFiniteFormat.numDigits
        ((y_hi_g e : Dyadic) : ℝ) := by
    rw [h_nd_eq]
    have : (p : ℤ) ≥ 2 := by exact_mod_cast hp_ge_2
    have h1 : ((1 : ℕ) : ℤ) = 1 := by decide
    rw [h1]; omega
  exact (F₁_g p hp_ge_2 e).precisionAtMost_not_IsOdd Nat.one_pos h_gt h_prec

/-- `IsEven F₁_g y_lo_low_g`: at numDigits = 2, canonical significand is `2`. -/
theorem isEven_F₁_g_y_lo_low (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ) :
    (F₁_g p hp_ge_2 e).IsEven (y_lo_low_g e) := by
  have h_coe_rat : ((y_lo_low_g e : Dyadic) : ℚ) = 2 * (2 : ℚ)^e := by
    change ((Dyadic.ofIntZpow 2 e : Dyadic) : ℚ) = _
    rw [Dyadic.coe_rat_ofIntZpow]; push_cast; ring
  have h_y_eq_2e1 : ((y_lo_low_g e : Dyadic) : ℝ) = (2 : ℝ)^(e + 1) := by
    rw [coe_y_lo_low_g, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [show (2 : ℝ)^(1 : ℤ) = 2 by norm_num]; ring
  have h_nd_toNat : ((F₁_g p hp_ge_2 e).toFiniteFormat.numDigits
        ((y_lo_low_g e : Dyadic) : ℝ)).toNat = 2 := by
    rw [F₁_g_numDigits p hp_ge_2 e h_y_eq_2e1]
    have hp_int : (p : ℤ) ≥ 2 := by exact_mod_cast hp_ge_2
    have h_min : min (p : ℤ) (e + 1 - e + 1) = 2 := by omega
    rw [h_min]; rfl
  have h_p_ne_1 : (F₁_g p hp_ge_2 e).p ≠ ((1 : ℕ) : Prec) := by
    rw [F₁_g_p]
    intro h
    have h1 : (p) = (1 : ℕ) := by exact_mod_cast h
    omega
  right
  refine ⟨2, e, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [h_coe_rat]; push_cast; ring
  · rw [h_nd_toNat]; decide
  · rw [h_nd_toNat]; decide
  · rw [if_neg h_p_ne_1]; decide

end Cex

end Mpfx
