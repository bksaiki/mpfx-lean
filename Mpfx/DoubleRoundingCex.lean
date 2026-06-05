import Mpfx.Rounding
import Mpfx.Grid
import Mpfx.Digits
import Mpfx.RoundOp

/-!
# Counterexamples to the invalid double-rounding pairings (§5.2)

The ten `no_rnd<rm₂>_<rm₁>` theorems refute every mode pairing absent
from Fig. 9: rounding `x` first in `F₂` under `rm₂` and then in `F₁`
under `rm₁` can disagree with rounding `x` directly in `F₁` under `rm₁`.
Each takes an arbitrary inner format `F₁ = 𝒜(p₁, exp₁, ⊤)` with
`p₁ ≠ 1` — both the precision `p₁` and the quantum `exp₁` may be finite
or infinite — and holds for **every** `F₂` satisfying the stated
containment, so no side condition on `(p₁, exp₁, p₂, exp₂, b₂)` can
validate these pairings.

All ten are proven once against `AnchorNeighborhood F₁`: three
consecutive `F₁`-elements `lo2 < lo < hi` spaced `2^t` (`lo2`, `hi` even,
`hi` not odd), their `F₁`-adjacency facts, and `F₂`-side local-step gap
bounds. `neighborhoodOf` instantiates it per shape of `F₁.exp`:

* `quantumNeighborhood` (`p₁` finite, `exp₁ = e`): anchors
  `2·2^e < 3·2^e < 4·2^e`;
* `topNeighborhood` (`p₁ = ⊤`, so `exp₁ = e` by the format invariant):
  the same anchors on the full integer grid of step `2^e`;
* `floatingNeighborhood` (`exp₁ = ⊥`, so `p₁` finite): anchors
  `s·2^t < (s+1)·2^t < (s+2)·2^t`, `s = 2^(p₁−1)`, inside the binade
  `[2^(t+p₁−1), 2^(t+p₁))`.

Every witness is `anchor ± δ` with `δ = 2^(K−2)` a quarter of `F₂`'s
*local step* at the anchor: the global quantum `2^f₂` when `F₂.exp = f₂`
is finite, and the binade step `2^(E−q₂+1)` when `F₂.exp = ⊥` (where the
`FiniteFormat` invariant forces `F₂.p = q₂` finite). Only the ten
counterexamples are public; everything else is `private`.
-/

namespace Mpfx

namespace Cex

/-! ## The quantum target format `F₁_g = 𝒜(p, e, ⊤)` -/

/-- The quantum target format `𝒜(p, e, ⊤)` with precision `p ≥ 2`, quantum `2^e`,
unbounded magnitude. Built as a `ParityFormat`: both the `finite` and
`parity` invariants hold because `exp = (e : ℤ) ≠ ⊥`. -/
private def F₁_g (p : ℕ+) (_hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ) : ParityFormat where
  toFiniteFormat :=
    { toFormat := { p := ((p : ℕ+) : WithTop ℕ+), exp := (e : WithBot ℤ), b := ⊤ }
      finite := Or.inr WithBot.coe_ne_bot }
  parity := Or.inr WithBot.coe_ne_bot

@[simp] private theorem F₁_g_p (p : ℕ+) (hp : 2 ≤ (p : ℕ)) (e : ℤ) :
    (F₁_g p hp e).p = ((p : ℕ+) : WithTop ℕ+) := rfl

@[simp] private theorem F₁_g_exp (p : ℕ+) (hp : 2 ≤ (p : ℕ)) (e : ℤ) :
    (F₁_g p hp e).exp = (e : WithBot ℤ) := rfl

@[simp] private theorem F₁_g_b (p : ℕ+) (hp : 2 ≤ (p : ℕ)) (e : ℤ) :
    (F₁_g p hp e).b = ⊤ := rfl

/-! ### The grid anchors (as `Dyadic.ofIntZpow`) -/

private noncomputable def y_lo_g (e : ℤ) : Dyadic := Dyadic.ofIntZpow 3 e
private noncomputable def y_hi_g (e : ℤ) : Dyadic := Dyadic.ofIntZpow 1 (e + 2)

/-- `2^e` as a Dyadic, used as the smallest positive F₁_g-element witness. -/
private noncomputable def two_e_g (e : ℤ) : Dyadic := Dyadic.ofIntZpow 1 e

private noncomputable def m_g (e : ℤ) : Dyadic := Dyadic.ofIntZpow 7 (e - 1)

private noncomputable def y_lo_low_g (e : ℤ) : Dyadic := Dyadic.ofIntZpow 2 e

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
target format therefore contains arbitrarily large elements. -/
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

/-- If `2^e ∈ F₂` and `F₂.exp = (f₂ : WithBot ℤ)`, then `f₂ ≤ e`. -/
private theorem f₂_le_e_of_two_e_mem {e : ℤ} {F₂ : Format}
    (h_two_e_in_F₂ : two_e_g e ∈ F₂)
    {f₂ : ℤ} (hF₂_exp : F₂.exp = (f₂ : WithBot ℤ)) :
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

/-- A format containing `2^N` for every `N ≥ e` has no finite bound. -/
private theorem F₂_bound_top_of_zpow_mem {e : ℤ} (F₂ : FiniteFormat)
    (h_zpow : ∀ N : ℤ, e ≤ N → Dyadic.ofIntZpow 1 N ∈ F₂.toFormat) :
    F₂.b = ⊤ := by
  by_contra h_b_ne
  obtain ⟨b, hb_eq⟩ := WithTop.ne_top_iff_exists.mp h_b_ne
  set N : ℤ := max e (Int.log 2 ((b.val : Dyadic) : ℝ) + 1) with hN_def
  set y_huge : Dyadic := Dyadic.ofIntZpow 1 N with hy_huge_def
  have hN_ge : e ≤ N := le_max_left _ _
  have hy_huge_real : ((y_huge : Dyadic) : ℝ) = (2 : ℝ)^N := by
    rw [hy_huge_def, Dyadic.coe_ofIntZpow]; push_cast; ring
  have hy_huge_in_F₂ : y_huge ∈ F₂.toFormat := h_zpow N hN_ge
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
`F₂` once `F₂_bound_top_of_zpow_mem` applies. -/
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

/-! ### Shape-generic local-grid interface

Near any anchor, every `F₂`-element is an integer multiple of a local
step `2^K`: the global quantum `2^f₂` when `F₂.exp = f₂` is finite, and
the binade step `2^(E−q₂+1)` when `F₂.exp = ⊥` (`binade_quantum`). The
dispatch lemmas below package the resulting gap bounds uniformly, so the
counterexamples never case-split on `F₂`'s shape. -/

private theorem two_zpow_succ (t : ℤ) : (2 : ℝ)^(t + 1) = 2 * (2 : ℝ)^t := by
  rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
      show (2 : ℝ)^(1 : ℤ) = 2 from by norm_num]
  ring

private theorem two_zpow_add_two (t : ℤ) : (2 : ℝ)^(t + 2) = 4 * (2 : ℝ)^t := by
  rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
      show (2 : ℝ)^(2 : ℤ) = 4 from by norm_num]
  ring

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

/-- **Binade quantization.** In a format with finite precision `q₂`, every
element of the binade `[2^E, 2^(E+1))` is an integer multiple of the local
step `2^(E − q₂ + 1)`. -/
private theorem binade_quantum {F₂ : FiniteFormat} {q₂ : ℕ+}
    (hp : F₂.p = ((q₂ : ℕ+) : WithTop ℕ+)) {E : ℤ} {y : Dyadic}
    (hy : y ∈ F₂.toFormat)
    (h_lo : (2 : ℝ) ^ E ≤ ((y : Dyadic) : ℝ))
    (_h_hi : ((y : Dyadic) : ℝ) < (2 : ℝ) ^ (E + 1)) :
    ∃ c : ℤ, ((y : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ)^(E - (q₂ : ℕ) + 1) := by
  have hprec : Dyadic.precisionAtMost F₂.p y := hy.1
  rw [hp, Dyadic.precisionAtMost_coe_real] at hprec
  obtain ⟨c, k, hck, hc_lt⟩ := hprec
  have h2E_pos : (0 : ℝ) < (2 : ℝ)^E := zpow_pos (by norm_num) _
  have h2k_pos : (0 : ℝ) < (2 : ℝ)^k := zpow_pos (by norm_num) _
  have hc_real_lt : (c : ℝ) < (2 : ℝ)^((q₂ : ℕ) : ℤ) := by
    have h1 : (c : ℝ) ≤ ((|c| : ℤ) : ℝ) := by
      rw [Int.cast_abs]; exact le_abs_self _
    have h2 : ((|c| : ℤ) : ℝ) < (((2 : ℤ)^(q₂ : ℕ) : ℤ) : ℝ) := by
      exact_mod_cast hc_lt
    have h3 : (((2 : ℤ)^(q₂ : ℕ) : ℤ) : ℝ) = (2 : ℝ)^((q₂ : ℕ) : ℤ) := by
      push_cast
      rw [← zpow_natCast (2 : ℝ) (q₂ : ℕ)]
    linarith
  have hk_ge : E - (q₂ : ℕ) + 1 ≤ k := by
    by_contra h
    push Not at h
    have h_y_lt : ((y : Dyadic) : ℝ) < (2 : ℝ)^E := by
      rw [hck]
      calc (c : ℝ) * (2 : ℝ)^k
          < (2 : ℝ)^((q₂ : ℕ) : ℤ) * (2 : ℝ)^k := by nlinarith
        _ = (2 : ℝ)^(((q₂ : ℕ) : ℤ) + k) := by
            rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        _ ≤ (2 : ℝ)^E := zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith
  refine ⟨c * 2^((k - (E - (q₂ : ℕ) + 1)).toNat), ?_⟩
  rw [hck, two_zpow_split k (E - (q₂ : ℕ) + 1) hk_ge]
  push_cast; ring

/-- An odd positive coefficient is visible to the precision: if
`y = a·2^e' ∈ F₂` with `a` odd and positive and `F₂.p = q₂`, then
`a < 2^q₂`. -/
private theorem coeff_lt_of_odd_mem {F₂ : FiniteFormat} {q₂ : ℕ+}
    (hp : F₂.p = ((q₂ : ℕ+) : WithTop ℕ+)) {a e' : ℤ}
    (ha_odd : Odd a) (ha_pos : 0 < a) {y : Dyadic} (hy : y ∈ F₂.toFormat)
    (hy_eq : ((y : Dyadic) : ℝ) = (a : ℝ) * (2 : ℝ) ^ e') :
    a < 2^(q₂ : ℕ) := by
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
private theorem p_ge2_of_y_lo_mem {F₂ : FiniteFormat} {e : ℤ}
    (h3 : y_lo_g e ∈ F₂.toFormat) :
    ∀ q₂ : ℕ+, F₂.p = ((q₂ : ℕ+) : WithTop ℕ+) → 2 ≤ (q₂ : ℕ) := by
  intro q₂ hp
  have h := coeff_lt_of_odd_mem hp (by decide : Odd (3 : ℤ)) (by norm_num) h3
    (by rw [coe_y_lo_g]; push_cast; ring)
  by_contra hq
  push Not at hq
  have h1 : (q₂ : ℕ) = 1 := by
    have h2 : 1 ≤ (q₂ : ℕ) := q₂.one_le
    omega
  rw [h1] at h
  norm_num at h

/-- **Shape dispatch: gap below `2^E`.** There is a local step `2^K`
(`K ≤ E`) such that every nonnegative `F₂`-element strictly below `2^E` is
at most `2^E − 2^K`. Needs `f₂ ≤ E` only when `F₂.exp = f₂` is finite. -/
private theorem gap_below_pow (F₂ : FiniteFormat) {E : ℤ}
    (h_exp_le : ∀ f₂ : ℤ, F₂.exp = (f₂ : WithBot ℤ) → f₂ ≤ E) :
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
    have hp : F₂.p = ((q₂ : ℕ+) : WithTop ℕ+) := hq₂_eq.symm
    have hq₂_one : 1 ≤ (q₂ : ℕ) := q₂.one_le
    refine ⟨E - (q₂ : ℕ), by omega, ?_⟩
    intro z hz hz_lt
    have h2K_le : (2 : ℝ)^(E - (q₂ : ℕ)) ≤ (2 : ℝ)^(E - 1) :=
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
      rw [show E - 1 - ((q₂ : ℕ) : ℤ) + 1 = E - (q₂ : ℕ) by omega] at hc
      have hne : (c : ℝ) * (2 : ℝ)^(E - (q₂ : ℕ)) ≠ ((1 : ℤ) : ℝ) * (2 : ℝ)^E := by
        rw [h_one, ← hc]
        exact ne_of_lt hz_lt
      have h_gap := gap_of_ne_aligned (c := c) (a := 1)
        (K := E - (q₂ : ℕ)) (E := E) (by omega) hne
      rw [h_one, ← hc, abs_sub_comm,
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ (2 : ℝ)^E - ((z : Dyadic) : ℝ))]
        at h_gap
      linarith
  · -- `exp = f₂` finite: the global quantum grid.
    have hexpc : F₂.exp = (f₂ : WithBot ℤ) := hexp
    have hf₂E : f₂ ≤ E := h_exp_le f₂ hexpc
    refine ⟨f₂, hf₂E, ?_⟩
    intro z hz hz_lt
    set n : ℕ := (E - f₂).toNat with hn
    have h2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
    have h_target : (2 : ℝ)^E - (2 : ℝ)^f₂
        = (((2 : ℤ)^n - 1 : ℤ) : ℝ) * (2 : ℝ)^f₂ := by
      have h_split : (2 : ℝ)^E = ((2 : ℤ)^n : ℝ) * (2 : ℝ)^f₂ :=
        two_zpow_split E f₂ hf₂E
      rw [h_split]; push_cast; ring
    apply F₂_grid_floor hexpc h_target z hz
    linarith

/-- **Shape dispatch: gap above `2^E`.** There is a local step `2^K`
(`K ≤ E`) such that every `F₂`-element strictly above `2^E` is at least
`2^E + 2^K`. Needs `f₂ ≤ E` only when `F₂.exp = f₂` is finite. -/
private theorem gap_above_pow (F₂ : FiniteFormat) {E : ℤ}
    (h_exp_le : ∀ f₂ : ℤ, F₂.exp = (f₂ : WithBot ℤ) → f₂ ≤ E) :
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
    have hp : F₂.p = ((q₂ : ℕ+) : WithTop ℕ+) := hq₂_eq.symm
    have hq₂_one : 1 ≤ (q₂ : ℕ) := q₂.one_le
    refine ⟨E - (q₂ : ℕ) + 1, by omega, ?_⟩
    intro z hz hz_gt
    have h2K_le : (2 : ℝ)^(E - (q₂ : ℕ) + 1) ≤ (2 : ℝ)^E :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    rcases lt_or_ge ((z : Dyadic) : ℝ) ((2 : ℝ)^(E + 1)) with h_in | h_above
    · -- In binade `E`: a multiple of `2^(E−q₂+1)` strictly above `2^E`.
      obtain ⟨c, hc⟩ := binade_quantum hp hz (by linarith) h_in
      have hne : (c : ℝ) * (2 : ℝ)^(E - (q₂ : ℕ) + 1)
          ≠ ((1 : ℤ) : ℝ) * (2 : ℝ)^E := by
        rw [h_one, ← hc]
        exact (ne_of_lt hz_gt).symm
      have h_gap := gap_of_ne_aligned (c := c) (a := 1)
        (K := E - (q₂ : ℕ) + 1) (E := E) (by omega) hne
      rw [h_one, ← hc,
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ ((z : Dyadic) : ℝ) - (2 : ℝ)^E)]
        at h_gap
      linarith
    · -- At or above the binade top: `z ≥ 2^(E+1) = 2^E + 2^E ≥ 2^E + 2^K`.
      linarith
  · -- `exp = f₂` finite: the global quantum grid.
    have hexpc : F₂.exp = (f₂ : WithBot ℤ) := hexp
    have hf₂E : f₂ ≤ E := h_exp_le f₂ hexpc
    refine ⟨f₂, hf₂E, ?_⟩
    intro z hz hz_gt
    set n : ℕ := (E - f₂).toNat with hn
    have h2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
    have h_target : (2 : ℝ)^E + (2 : ℝ)^f₂
        = (((2 : ℤ)^n + 1 : ℤ) : ℝ) * (2 : ℝ)^f₂ := by
      have h_split : (2 : ℝ)^E = ((2 : ℤ)^n : ℝ) * (2 : ℝ)^f₂ :=
        two_zpow_split E f₂ hf₂E
      rw [h_split]; push_cast; ring
    apply F₂_grid_ceil hexpc h_target z hz
    linarith

/-- **Shape dispatch: gaps around an off-grid midpoint** `A = a·2^(e−1)`,
`5 ≤ a ≤ 7`. There is a local step `2^K` (`K ≤ e`) such that `F₂`-elements
keep distance `2^(K−1)` from `A` on both sides. Needs `f₂ ≤ e` when
`F₂.exp = f₂` is finite, and (when `F₂.exp = ⊥`) at least two bits of
precision, provided by `h_p_ge2`. -/
private theorem gap_around_mid (F₂ : FiniteFormat) {e a : ℤ}
    (ha_lo : 5 ≤ a) (ha_hi : a ≤ 7)
    (h_exp_le : ∀ f₂ : ℤ, F₂.exp = (f₂ : WithBot ℤ) → f₂ ≤ e)
    (h_p_ge2 : ∀ q₂ : ℕ+, F₂.p = ((q₂ : ℕ+) : WithTop ℕ+) → 2 ≤ (q₂ : ℕ)) :
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
    have hp : F₂.p = ((q₂ : ℕ+) : WithTop ℕ+) := hq₂_eq.symm
    have hq₂_two : 2 ≤ (q₂ : ℕ) := h_p_ge2 q₂ hp
    refine ⟨e - (q₂ : ℕ) + 2, by omega, ?_, ?_⟩
    all_goals
      have h2K1_le : (2 : ℝ)^(e - (q₂ : ℕ) + 2 - 1) ≤ (2 : ℝ)^(e - 1) :=
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
        rw [show e + 1 - ((q₂ : ℕ) : ℤ) + 1 = e - (q₂ : ℕ) + 2 by omega] at hc
        have hne : (c : ℝ) * (2 : ℝ)^(e - (q₂ : ℕ) + 2)
            ≠ (a : ℝ) * (2 : ℝ)^(e - 1) := by
          rw [← hc]
          exact ne_of_lt hz_lt
        have h_gap := gap_of_ne_half_aligned (c := c) (a := a)
          (K := e - (q₂ : ℕ) + 2) (E := e - 1) (by omega) hne
        rw [← hc, abs_sub_comm, abs_of_nonneg (by linarith :
            (0 : ℝ) ≤ (a : ℝ) * (2 : ℝ)^(e - 1) - ((z : Dyadic) : ℝ))] at h_gap
        linarith
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
        rw [show e + 1 - ((q₂ : ℕ) : ℤ) + 1 = e - (q₂ : ℕ) + 2 by omega] at hc
        have hne : (c : ℝ) * (2 : ℝ)^(e - (q₂ : ℕ) + 2)
            ≠ (a : ℝ) * (2 : ℝ)^(e - 1) := by
          rw [← hc]
          exact (ne_of_lt hz_gt).symm
        have h_gap := gap_of_ne_half_aligned (c := c) (a := a)
          (K := e - (q₂ : ℕ) + 2) (E := e - 1) (by omega) hne
        rw [← hc, abs_of_nonneg (by linarith :
            (0 : ℝ) ≤ ((z : Dyadic) : ℝ) - (a : ℝ) * (2 : ℝ)^(e - 1))] at h_gap
        linarith
      · -- At or above the binade top: `z ≥ 8·2^(e−1) ≥ A + 2^(K−1)`.
        rw [h_e2_split] at h_above
        linarith
  · -- `exp = f₂` finite: the global quantum grid; `K = f₂ ≤ e`.
    have hexpc : F₂.exp = (f₂ : WithBot ℤ) := hexp
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
      rw [← hc, abs_sub_comm, abs_of_nonneg (by linarith :
          (0 : ℝ) ≤ (a : ℝ) * (2 : ℝ)^(e - 1) - ((z : Dyadic) : ℝ))] at h_gap
      linarith
    · intro z hz hz_gt
      obtain ⟨_, hq, _⟩ := hz
      rw [hexpc, Dyadic.quantumAtLeast_coe_real] at hq
      obtain ⟨c, hc⟩ := hq
      have hne : (c : ℝ) * (2 : ℝ)^f₂ ≠ (a : ℝ) * (2 : ℝ)^(e - 1) := by
        rw [← hc]
        exact (ne_of_lt hz_gt).symm
      have h_gap := gap_of_ne_half_aligned (c := c) (a := a)
        (K := f₂) (E := e - 1) (by omega) hne
      rw [← hc, abs_of_nonneg (by linarith :
          (0 : ℝ) ≤ ((z : Dyadic) : ℝ) - (a : ℝ) * (2 : ℝ)^(e - 1))] at h_gap
      linarith

/-- **Shape dispatch: full-step gaps around the representable midpoint**
`m = 7·2^(e−1)` when `m ∈ F₂`: there is a local step `2^K` (`K ≤ e − 1`)
with `m` on the step grid and `F₂`-elements keeping the full distance `2^K`
from `m` on both sides. -/
private theorem gap_around_m_mem (F₂ : FiniteFormat) {e : ℤ}
    (hm : m_g e ∈ F₂.toFormat) :
    ∃ K : ℤ, K ≤ e - 1 ∧
      (∀ z ∈ F₂.toFormat, ((z : Dyadic) : ℝ) < (7 : ℝ) * (2 : ℝ)^(e - 1) →
        ((z : Dyadic) : ℝ) ≤ (7 : ℝ) * (2 : ℝ)^(e - 1) - (2 : ℝ)^K) ∧
      (∀ z ∈ F₂.toFormat, (7 : ℝ) * (2 : ℝ)^(e - 1) < ((z : Dyadic) : ℝ) →
        (7 : ℝ) * (2 : ℝ)^(e - 1) + (2 : ℝ)^K ≤ ((z : Dyadic) : ℝ)) := by
  have h2e1_pos : (0 : ℝ) < (2 : ℝ)^(e - 1) := zpow_pos (by norm_num) _
  have h_e1_split : (2 : ℝ)^(e + 1) = (4 : ℝ) * (2 : ℝ)^(e - 1) := by
    have h := two_zpow_add_two (e - 1)
    rwa [show e - 1 + 2 = e + 1 by ring] at h
  have h_e2_split : (2 : ℝ)^(e + 2) = (8 : ℝ) * (2 : ℝ)^(e - 1) := by
    have h := two_zpow_add_three (e - 1)
    rwa [show e - 1 + 3 = e + 2 by ring] at h
  rcases hexp : F₂.exp with _ | f₂
  · -- `exp = ⊥`: `m ∈ F₂` forces `q₂ ≥ 3`; the binade-(e+1) step,
    -- on which `m` lies.
    have hp_ne : F₂.p ≠ ⊤ := by
      rcases F₂.finite with h | h
      · exact h
      · exact absurd hexp h
    obtain ⟨q₂, hq₂_eq⟩ := WithTop.ne_top_iff_exists.mp hp_ne
    have hp : F₂.p = ((q₂ : ℕ+) : WithTop ℕ+) := hq₂_eq.symm
    have h7 := coeff_lt_of_odd_mem hp (by decide : Odd (7 : ℤ)) (by norm_num) hm
      (by rw [coe_m_g]; push_cast; ring)
    have hq₂_three : 3 ≤ (q₂ : ℕ) := by
      by_contra hq
      push Not at hq
      have h_le : (2 : ℤ)^(q₂ : ℕ) ≤ 2^2 :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      norm_num at h_le
      omega
    set K : ℤ := e - (q₂ : ℕ) + 2 with hK_def
    have hK_le : K ≤ e - 1 := by omega
    have h2K_le : (2 : ℝ)^K ≤ (2 : ℝ)^(e - 1) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h_m_grid : (7 : ℝ) * (2 : ℝ)^(e - 1)
        = ((7 * (2 : ℤ)^((e - 1) - K).toNat : ℤ) : ℝ) * (2 : ℝ)^K := by
      have h_split : (2 : ℝ)^(e - 1) = ((2 : ℤ)^((e - 1) - K).toNat : ℝ) * (2 : ℝ)^K :=
        two_zpow_split (e - 1) K (by omega)
      rw [h_split]; push_cast; ring
    refine ⟨K, hK_le, ?_, ?_⟩
    · intro z hz hz_lt
      rcases lt_or_ge ((z : Dyadic) : ℝ) ((2 : ℝ)^(e + 1)) with h_below | h_in
      · rw [h_e1_split] at h_below
        linarith
      · have h_in_hi : ((z : Dyadic) : ℝ) < (2 : ℝ)^(e + 1 + 1) := by
          rw [show e + 1 + 1 = e + 2 by ring, h_e2_split]
          linarith
        obtain ⟨c, hc⟩ := binade_quantum hp hz h_in h_in_hi
        rw [show e + 1 - ((q₂ : ℕ) : ℤ) + 1 = K by omega] at hc
        have hne : (c : ℝ) * (2 : ℝ)^K
            ≠ ((7 * (2 : ℤ)^((e - 1) - K).toNat : ℤ) : ℝ) * (2 : ℝ)^K := by
          rw [← hc, ← h_m_grid]
          exact ne_of_lt hz_lt
        have h_gap := gap_of_ne_aligned (c := c)
          (a := 7 * (2 : ℤ)^((e - 1) - K).toNat) (K := K) (E := K) le_rfl hne
        rw [← hc, ← h_m_grid, abs_sub_comm, abs_of_nonneg (by linarith :
            (0 : ℝ) ≤ (7 : ℝ) * (2 : ℝ)^(e - 1) - ((z : Dyadic) : ℝ))] at h_gap
        linarith
    · intro z hz hz_gt
      rcases lt_or_ge ((z : Dyadic) : ℝ) ((2 : ℝ)^(e + 2)) with h_in | h_above
      · have h_in_lo : (2 : ℝ)^(e + 1) ≤ ((z : Dyadic) : ℝ) := by
          rw [h_e1_split]
          linarith
        have h_in_hi : ((z : Dyadic) : ℝ) < (2 : ℝ)^(e + 1 + 1) := by
          rw [show e + 1 + 1 = e + 2 by ring]
          exact h_in
        obtain ⟨c, hc⟩ := binade_quantum hp hz h_in_lo h_in_hi
        rw [show e + 1 - ((q₂ : ℕ) : ℤ) + 1 = K by omega] at hc
        have hne : (c : ℝ) * (2 : ℝ)^K
            ≠ ((7 * (2 : ℤ)^((e - 1) - K).toNat : ℤ) : ℝ) * (2 : ℝ)^K := by
          rw [← hc, ← h_m_grid]
          exact (ne_of_lt hz_gt).symm
        have h_gap := gap_of_ne_aligned (c := c)
          (a := 7 * (2 : ℤ)^((e - 1) - K).toNat) (K := K) (E := K) le_rfl hne
        rw [← hc, ← h_m_grid, abs_of_nonneg (by linarith :
            (0 : ℝ) ≤ ((z : Dyadic) : ℝ) - (7 : ℝ) * (2 : ℝ)^(e - 1))] at h_gap
        linarith
      · rw [h_e2_split] at h_above
        linarith
  · -- `exp = f₂` finite: `m ∈ F₂` forces `f₂ ≤ e − 1`; the quantum grid,
    -- on which `m` lies.
    have hexpc : F₂.exp = (f₂ : WithBot ℤ) := hexp
    have hf₂_le : f₂ ≤ e - 1 :=
      f₂_le_e_sub_one_of_odd_in_F₂ hexpc hm (by decide : Odd (7 : ℤ))
        (by rw [coe_m_g]; push_cast; ring)
    have h_m_grid : (7 : ℝ) * (2 : ℝ)^(e - 1)
        = ((7 * (2 : ℤ)^((e - 1) - f₂).toNat : ℤ) : ℝ) * (2 : ℝ)^f₂ := by
      have h_split : (2 : ℝ)^(e - 1) = ((2 : ℤ)^((e - 1) - f₂).toNat : ℝ) * (2 : ℝ)^f₂ :=
        two_zpow_split (e - 1) f₂ hf₂_le
      rw [h_split]; push_cast; ring
    refine ⟨f₂, hf₂_le, ?_, ?_⟩
    · intro z hz hz_lt
      obtain ⟨_, hq, _⟩ := hz
      rw [hexpc, Dyadic.quantumAtLeast_coe_real] at hq
      obtain ⟨c, hc⟩ := hq
      have hne : (c : ℝ) * (2 : ℝ)^f₂
          ≠ ((7 * (2 : ℤ)^((e - 1) - f₂).toNat : ℤ) : ℝ) * (2 : ℝ)^f₂ := by
        rw [← hc, ← h_m_grid]
        exact ne_of_lt hz_lt
      have h_gap := gap_of_ne_aligned (c := c)
        (a := 7 * (2 : ℤ)^((e - 1) - f₂).toNat) (K := f₂) (E := f₂) le_rfl hne
      rw [← hc, ← h_m_grid, abs_sub_comm, abs_of_nonneg (by linarith :
          (0 : ℝ) ≤ (7 : ℝ) * (2 : ℝ)^(e - 1) - ((z : Dyadic) : ℝ))] at h_gap
      linarith
    · intro z hz hz_gt
      obtain ⟨_, hq, _⟩ := hz
      rw [hexpc, Dyadic.quantumAtLeast_coe_real] at hq
      obtain ⟨c, hc⟩ := hq
      have hne : (c : ℝ) * (2 : ℝ)^f₂
          ≠ ((7 * (2 : ℤ)^((e - 1) - f₂).toNat : ℤ) : ℝ) * (2 : ℝ)^f₂ := by
        rw [← hc, ← h_m_grid]
        exact (ne_of_lt hz_gt).symm
      have h_gap := gap_of_ne_aligned (c := c)
        (a := 7 * (2 : ℤ)^((e - 1) - f₂).toNat) (K := f₂) (E := f₂) le_rfl hne
      rw [← hc, ← h_m_grid, abs_of_nonneg (by linarith :
          (0 : ℝ) ≤ ((z : Dyadic) : ℝ) - (7 : ℝ) * (2 : ℝ)^(e - 1))] at h_gap
      linarith

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

/-! ## The anchor-neighborhood interface

Everything the ten counterexamples use about the *inner* format `F₁` and its
interaction with an arbitrary `F₂ ⊇ F₁`, bundled as data: three consecutive
`F₁`-elements `lo2 < lo < hi` spaced by a local step `2^t` (`lo2`, `hi`
even, `hi` not odd), the `F₁`-adjacency facts, and — quantified over every
`F₂` containing `F₁` — the local-step gap bounds around the anchors and the
two midpoints. The counterexample cores are proven once against this
interface; it is instantiated for the quantum target format `F₁_g = 𝒜(p, e, ⊤)`
and for the floating target format `F₁f_g = 𝒜(q, ⊥, ⊤)`. -/

private structure AnchorNeighborhood (F₁ : ParityFormat) where
  /-- Local step exponent: the anchors are spaced `2^t` apart. -/
  t : ℤ
  /-- The even lower anchor. -/
  lo2 : Dyadic
  /-- The odd middle anchor `lo2 + 2^t`. -/
  lo : Dyadic
  /-- The even upper anchor `lo2 + 2·2^t`. -/
  hi : Dyadic
  /-- The midpoint of `(lo, hi)`, as a Dyadic for the `extend 1` membership. -/
  mid : Dyadic
  lo2_pos : (0 : ℝ) < ((lo2 : Dyadic) : ℝ)
  coe_lo : ((lo : Dyadic) : ℝ) = ((lo2 : Dyadic) : ℝ) + (2 : ℝ) ^ t
  coe_hi : ((hi : Dyadic) : ℝ) = ((lo2 : Dyadic) : ℝ) + 2 * (2 : ℝ) ^ t
  coe_mid : ((mid : Dyadic) : ℝ) = ((lo : Dyadic) : ℝ) + (2 : ℝ) ^ (t - 1)
  mem_lo2 : lo2 ∈ F₁.toFormat
  mem_lo : lo ∈ F₁.toFormat
  mem_hi : hi ∈ F₁.toFormat
  even_lo2 : F₁.IsEven lo2
  even_hi : F₁.IsEven hi
  not_odd_hi : ¬ F₁.IsOdd hi
  /-- `F₁`-adjacency: no element strictly between `lo2` and `lo`. -/
  f1_floor_lo : ∀ v ∈ F₁.toFormat, ((v : Dyadic) : ℝ) < ((lo : Dyadic) : ℝ) →
    ((v : Dyadic) : ℝ) ≤ ((lo2 : Dyadic) : ℝ)
  f1_ceil_lo2 : ∀ v ∈ F₁.toFormat, ((lo2 : Dyadic) : ℝ) < ((v : Dyadic) : ℝ) →
    ((lo : Dyadic) : ℝ) ≤ ((v : Dyadic) : ℝ)
  /-- `F₁`-adjacency: no element strictly between `lo` and `hi`. -/
  f1_floor_hi : ∀ v ∈ F₁.toFormat, ((v : Dyadic) : ℝ) < ((hi : Dyadic) : ℝ) →
    ((v : Dyadic) : ℝ) ≤ ((lo : Dyadic) : ℝ)
  f1_ceil_hi : ∀ v ∈ F₁.toFormat, ((lo : Dyadic) : ℝ) < ((v : Dyadic) : ℝ) →
    ((hi : Dyadic) : ℝ) ≤ ((v : Dyadic) : ℝ)
  /-- The midpoint of `(lo, hi)` is representable with one extra digit. -/
  mid_mem_ext1 : mid ∈ ((F₁.toFiniteFormat.extend 1).toFormat)
  /-- Containing `F₁` forces an unbounded `F₂`. -/
  f2_b_top : ∀ F₂ : FiniteFormat, F₁.toFormat ⊆ F₂.toFormat → F₂.b = ⊤
  /-- `F₂`-local gap below `hi`. -/
  f2_below_hi : ∀ F₂ : FiniteFormat, F₁.toFormat ⊆ F₂.toFormat →
    ∃ K : ℤ, K ≤ t ∧ ∀ z ∈ F₂.toFormat,
      ((z : Dyadic) : ℝ) < ((hi : Dyadic) : ℝ) →
      ((z : Dyadic) : ℝ) ≤ ((hi : Dyadic) : ℝ) - (2 : ℝ) ^ K
  /-- `F₂`-local gap above `hi`. -/
  f2_above_hi : ∀ F₂ : FiniteFormat, F₁.toFormat ⊆ F₂.toFormat →
    ∃ K : ℤ, K ≤ t ∧ ∀ z ∈ F₂.toFormat,
      ((hi : Dyadic) : ℝ) < ((z : Dyadic) : ℝ) →
      ((hi : Dyadic) : ℝ) + (2 : ℝ) ^ K ≤ ((z : Dyadic) : ℝ)
  /-- `F₂`-local half-step gaps around the lower midpoint `lo2 + 2^(t−1)`. -/
  f2_mid_lo : ∀ F₂ : FiniteFormat, F₁.toFormat ⊆ F₂.toFormat →
    ∃ K : ℤ, K ≤ t ∧
      (∀ z ∈ F₂.toFormat,
        ((z : Dyadic) : ℝ) < ((lo2 : Dyadic) : ℝ) + (2 : ℝ) ^ (t - 1) →
        ((z : Dyadic) : ℝ) ≤
          ((lo2 : Dyadic) : ℝ) + (2 : ℝ) ^ (t - 1) - (2 : ℝ) ^ (K - 1)) ∧
      (∀ z ∈ F₂.toFormat,
        ((lo2 : Dyadic) : ℝ) + (2 : ℝ) ^ (t - 1) < ((z : Dyadic) : ℝ) →
        ((lo2 : Dyadic) : ℝ) + (2 : ℝ) ^ (t - 1) + (2 : ℝ) ^ (K - 1) ≤
          ((z : Dyadic) : ℝ))
  /-- `F₂`-local half-step gaps around the upper midpoint `lo + 2^(t−1)`. -/
  f2_mid_hi : ∀ F₂ : FiniteFormat, F₁.toFormat ⊆ F₂.toFormat →
    ∃ K : ℤ, K ≤ t ∧
      (∀ z ∈ F₂.toFormat,
        ((z : Dyadic) : ℝ) < ((lo : Dyadic) : ℝ) + (2 : ℝ) ^ (t - 1) →
        ((z : Dyadic) : ℝ) ≤
          ((lo : Dyadic) : ℝ) + (2 : ℝ) ^ (t - 1) - (2 : ℝ) ^ (K - 1)) ∧
      (∀ z ∈ F₂.toFormat,
        ((lo : Dyadic) : ℝ) + (2 : ℝ) ^ (t - 1) < ((z : Dyadic) : ℝ) →
        ((lo : Dyadic) : ℝ) + (2 : ℝ) ^ (t - 1) + (2 : ℝ) ^ (K - 1) ≤
          ((z : Dyadic) : ℝ))
  /-- `F₂`-local full-step gaps around the upper midpoint when it is
  `F₂`-representable. -/
  f2_mem_mid : ∀ F₂ : FiniteFormat, mid ∈ F₂.toFormat →
    ∃ K : ℤ, K ≤ t - 1 ∧
      (∀ z ∈ F₂.toFormat, ((z : Dyadic) : ℝ) < ((mid : Dyadic) : ℝ) →
        ((z : Dyadic) : ℝ) ≤ ((mid : Dyadic) : ℝ) - (2 : ℝ) ^ K) ∧
      (∀ z ∈ F₂.toFormat, ((mid : Dyadic) : ℝ) < ((z : Dyadic) : ℝ) →
        ((mid : Dyadic) : ℝ) + (2 : ℝ) ^ K ≤ ((z : Dyadic) : ℝ))

namespace AnchorNeighborhood

variable {F₁ : ParityFormat} (P : AnchorNeighborhood F₁)

/-- `F₁`-faithful values of any `s ∈ [lo2, lo2 + 2^(t−1)]` enumerate to
`{lo2, lo}`. -/
private theorem faithful_lo {s : ℝ}
    (h_lo : ((P.lo2 : Dyadic) : ℝ) ≤ s)
    (h_hi : s ≤ ((P.lo2 : Dyadic) : ℝ) + (2 : ℝ) ^ (P.t - 1))
    {v : Dyadic} (hf : IsFaithfulRound F₁.toFiniteFormat s v) :
    ((v : Dyadic) : ℝ) = ((P.lo2 : Dyadic) : ℝ) ∨
    ((v : Dyadic) : ℝ) = ((P.lo : Dyadic) : ℝ) := by
  have h_half_pos : (0 : ℝ) < (2 : ℝ) ^ (P.t - 1) := zpow_pos (by norm_num) _
  have h_half_lt : (2 : ℝ) ^ (P.t - 1) < (2 : ℝ) ^ P.t :=
    zpow_lt_zpow_right₀ (by norm_num) (by omega)
  have h_s_lt_lo : s < ((P.lo : Dyadic) : ℝ) := by
    rw [P.coe_lo]; linarith
  rcases hf with ⟨hvF, hle, hmax⟩ | ⟨hvF, hge, hmin⟩
  · left
    have h1 : ((v : Dyadic) : ℝ) ≤ ((P.lo2 : Dyadic) : ℝ) :=
      P.f1_floor_lo v hvF (lt_of_le_of_lt hle h_s_lt_lo)
    have h2 := hmax P.lo2 P.mem_lo2 h_lo
    linarith
  · rcases le_or_gt ((v : Dyadic) : ℝ) ((P.lo2 : Dyadic) : ℝ) with h1 | h1
    · left; linarith
    · right
      have h2 := P.f1_ceil_lo2 v hvF h1
      have h3 := hmin P.lo P.mem_lo (le_of_lt h_s_lt_lo)
      linarith

/-- RNE in `F₁` at any `s ∈ [lo2, lo2 + 2^(t−1)]` admits `lo2`: strictly
nearest in the interior, even tie-winner at the midpoint. -/
private theorem rounds_RNE_lo2 {s : ℝ}
    (h_lo : ((P.lo2 : Dyadic) : ℝ) ≤ s)
    (h_hi : s ≤ ((P.lo2 : Dyadic) : ℝ) + (2 : ℝ) ^ (P.t - 1)) :
    RoundsFinite F₁.toFiniteFormat (.nearest .toEven) s P.lo2 := by
  have h_half_pos : (0 : ℝ) < (2 : ℝ) ^ (P.t - 1) := zpow_pos (by norm_num) _
  have h_two_half : (2 : ℝ) ^ P.t = 2 * (2 : ℝ) ^ (P.t - 1) := by
    have h := two_zpow_succ (P.t - 1)
    rwa [show P.t - 1 + 1 = P.t by ring] at h
  have h_s_lt_lo : s < ((P.lo : Dyadic) : ℝ) := by
    rw [P.coe_lo]; linarith
  refine ⟨P.mem_lo2, ?_, ?_, ?_⟩
  · left
    refine ⟨P.mem_lo2, h_lo, ?_⟩
    intro v hv hv_le
    exact P.f1_floor_lo v hv (lt_of_le_of_lt hv_le h_s_lt_lo)
  · intro v hv hf
    rcases P.faithful_lo h_lo h_hi hf with h | h
    · rw [h]
    · rw [h, P.coe_lo]
      have hL : |s - ((P.lo2 : Dyadic) : ℝ)| = s - ((P.lo2 : Dyadic) : ℝ) :=
        abs_of_nonneg (by linarith)
      have hR : |s - (((P.lo2 : Dyadic) : ℝ) + (2 : ℝ) ^ P.t)|
          = ((P.lo2 : Dyadic) : ℝ) + (2 : ℝ) ^ P.t - s := by
        rw [abs_sub_comm]
        exact abs_of_nonneg (by linarith)
      rw [hL, hR]
      linarith
  · rintro ⟨_, _, _, _, _⟩
    exact ⟨F₁, rfl, P.even_lo2⟩

/-- `F₁`-faithful values of any `s ∈ [lo + 2^(t−1), hi]` enumerate to
`{lo, hi}`. -/
private theorem faithful_hi {s : ℝ}
    (h_lo : ((P.lo : Dyadic) : ℝ) + (2 : ℝ) ^ (P.t - 1) ≤ s)
    (h_hi : s ≤ ((P.hi : Dyadic) : ℝ))
    {v : Dyadic} (hf : IsFaithfulRound F₁.toFiniteFormat s v) :
    ((v : Dyadic) : ℝ) = ((P.lo : Dyadic) : ℝ) ∨
    ((v : Dyadic) : ℝ) = ((P.hi : Dyadic) : ℝ) := by
  have h_half_pos : (0 : ℝ) < (2 : ℝ) ^ (P.t - 1) := zpow_pos (by norm_num) _
  have h_lo_lt_s : ((P.lo : Dyadic) : ℝ) < s := by linarith
  rcases hf with ⟨hvF, hle, hmax⟩ | ⟨hvF, hge, hmin⟩
  · rcases le_or_gt ((P.hi : Dyadic) : ℝ) ((v : Dyadic) : ℝ) with h1 | h1
    · right; linarith
    · left
      have h2 := P.f1_floor_hi v hvF h1
      have h3 := hmax P.lo P.mem_lo (le_of_lt h_lo_lt_s)
      linarith
  · right
    have h1 := P.f1_ceil_hi v hvF (lt_of_lt_of_le h_lo_lt_s hge)
    have h2 := hmin P.hi P.mem_hi h_hi
    linarith

/-- RNE in `F₁` at any `s ∈ [lo + 2^(t−1), hi]` admits `hi`: strictly
nearest in the interior, even tie-winner at the midpoint. -/
private theorem rounds_RNE_hi {s : ℝ}
    (h_lo : ((P.lo : Dyadic) : ℝ) + (2 : ℝ) ^ (P.t - 1) ≤ s)
    (h_hi : s ≤ ((P.hi : Dyadic) : ℝ)) :
    RoundsFinite F₁.toFiniteFormat (.nearest .toEven) s P.hi := by
  have h_half_pos : (0 : ℝ) < (2 : ℝ) ^ (P.t - 1) := zpow_pos (by norm_num) _
  have h_two_half : (2 : ℝ) ^ P.t = 2 * (2 : ℝ) ^ (P.t - 1) := by
    have h := two_zpow_succ (P.t - 1)
    rwa [show P.t - 1 + 1 = P.t by ring] at h
  have h_hi_lo : ((P.hi : Dyadic) : ℝ) = ((P.lo : Dyadic) : ℝ) + (2 : ℝ) ^ P.t := by
    rw [P.coe_hi, P.coe_lo]; ring
  have h_lo_lt_s : ((P.lo : Dyadic) : ℝ) < s := by linarith
  refine ⟨P.mem_hi, ?_, ?_, ?_⟩
  · right
    refine ⟨P.mem_hi, h_hi, ?_⟩
    intro v hv hv_ge
    exact P.f1_ceil_hi v hv (lt_of_lt_of_le h_lo_lt_s hv_ge)
  · intro v hv hf
    rcases P.faithful_hi h_lo h_hi hf with h | h
    · rw [h]
      have hL : |s - ((P.hi : Dyadic) : ℝ)| = ((P.hi : Dyadic) : ℝ) - s := by
        rw [abs_sub_comm]
        exact abs_of_nonneg (by linarith)
      have hR : |s - ((P.lo : Dyadic) : ℝ)| = s - ((P.lo : Dyadic) : ℝ) :=
        abs_of_nonneg (by linarith)
      rw [hL, hR, h_hi_lo]
      linarith
    · rw [h]
  · rintro ⟨_, _, _, _, _⟩
    exact ⟨F₁, rfl, P.even_hi⟩

end AnchorNeighborhood

/-! ## Neighborhood-generic counterexample cores

The ten counterexamples, proven once against `AnchorNeighborhood`. Throughout,
`δ = 2^(K−2)` is a quarter of `F₂`'s local step `2^K` at the anchor. -/

namespace AnchorNeighborhood

variable {F₁ : ParityFormat} (P : AnchorNeighborhood F₁)

/-- RTZ in `F₁` fixes any representable value. -/
private theorem rounds_RTZ_self {y : Dyadic} (hy : y ∈ F₁.toFormat) :
    RoundsFinite F₁.toFiniteFormat .toZero ((y : Dyadic) : ℝ) y :=
  ⟨hy, le_refl _, mul_self_nonneg _, fun _ _ hv_bnd _ => hv_bnd⟩

/-- RAZ in `F₁` fixes any representable value. -/
private theorem rounds_RAZ_self {y : Dyadic} (hy : y ∈ F₁.toFormat) :
    RoundsFinite F₁.toFiniteFormat .awayZero ((y : Dyadic) : ℝ) y :=
  ⟨hy, le_refl _, mul_self_nonneg _, fun _ _ hv_bnd _ => hv_bnd⟩

include P

private theorem hi_pos : (0 : ℝ) < ((P.hi : Dyadic) : ℝ) := by
  have h_step_pos : (0 : ℝ) < (2 : ℝ) ^ P.t := zpow_pos (by norm_num) _
  rw [P.coe_hi]
  linarith [P.lo2_pos]

/-- `¬ RoundsFinite F₁ RTZ x hi` for `x < hi`. -/
private theorem not_rounds_RTZ_hi {x : ℝ} (hx_pos : 0 < x)
    (hx_lt : x < ((P.hi : Dyadic) : ℝ)) :
    ¬ RoundsFinite F₁.toFiniteFormat .toZero x P.hi := by
  intro hr
  obtain ⟨_, h_bnd, _, _⟩ := hr
  rw [abs_of_pos hx_pos, abs_of_pos P.hi_pos] at h_bnd
  linarith

/-- `¬ RoundsFinite F₁ RAZ x hi` for `x > hi`. -/
private theorem not_rounds_RAZ_hi {x : ℝ}
    (hx_gt : ((P.hi : Dyadic) : ℝ) < x) :
    ¬ RoundsFinite F₁.toFiniteFormat .awayZero x P.hi := by
  intro hr
  obtain ⟨_, h_bnd, _, _⟩ := hr
  rw [abs_of_pos (lt_trans P.hi_pos hx_gt), abs_of_pos P.hi_pos] at h_bnd
  linarith

/-- `¬ RoundsFinite F₁ RTO x hi` for `x ≠ hi`: `hi` is not odd in `F₁`. -/
private theorem not_rounds_RTO_hi {x : ℝ}
    (hx_ne : x ≠ ((P.hi : Dyadic) : ℝ)) :
    ¬ RoundsFinite F₁.toFiniteFormat .toOdd x P.hi := by
  intro hr
  obtain ⟨_, _, h_parity⟩ := hr
  obtain ⟨F', hF'_eq, hF'_odd⟩ := h_parity hx_ne
  exact P.not_odd_hi (isOdd_transfer_toFormat hF'_eq hF'_odd)

/-- Positivity of `x = hi − 2^(K−2)` for `K ≤ t`. -/
private theorem x_below_pos {K : ℤ} (hK_le : K ≤ P.t) :
    0 < ((P.hi : Dyadic) : ℝ) - (2 : ℝ) ^ (K - 2) := by
  have h_step_pos : (0 : ℝ) < (2 : ℝ) ^ P.t := zpow_pos (by norm_num) _
  have h_2K2_lt_step : (2 : ℝ) ^ (K - 2) < (2 : ℝ) ^ P.t :=
    zpow_lt_zpow_right₀ (by norm_num) (by omega)
  rw [P.coe_hi]
  linarith [P.lo2_pos]

/-- RNE in `F₂` carries `hi − δ` up onto `hi`. -/
private theorem f₂_RNE_up (F₂ : FiniteFormat) {K : ℤ}
    (h_hi_in_F₂ : P.hi ∈ F₂.toFormat)
    (h_below : ∀ z ∈ F₂.toFormat,
      ((z : Dyadic) : ℝ) < ((P.hi : Dyadic) : ℝ) →
      ((z : Dyadic) : ℝ) ≤ ((P.hi : Dyadic) : ℝ) - (2 : ℝ) ^ K) :
    RoundsFinite F₂ (.nearest .toEven)
      (((P.hi : Dyadic) : ℝ) - (2 : ℝ) ^ (K - 2)) P.hi := by
  have h_2K2_pos : (0 : ℝ) < (2 : ℝ) ^ (K - 2) := zpow_pos (by norm_num) _
  have h_2K_split : (2 : ℝ) ^ K = 4 * (2 : ℝ) ^ (K - 2) := two_zpow_split_minus_two K
  set x_val : ℝ := ((P.hi : Dyadic) : ℝ) - (2 : ℝ) ^ (K - 2) with hx_def
  have h_x_lt_hi : x_val < ((P.hi : Dyadic) : ℝ) := by rw [hx_def]; linarith
  have h_ge_x_to_ge_hi : ∀ z ∈ F₂.toFormat, x_val ≤ ((z : Dyadic) : ℝ) →
      ((P.hi : Dyadic) : ℝ) ≤ ((z : Dyadic) : ℝ) := by
    intro z hz hz_ge
    by_contra h_lt
    push Not at h_lt
    have h := h_below z hz h_lt
    rw [hx_def] at hz_ge
    linarith
  refine ⟨h_hi_in_F₂, ?_, ?_, ?_⟩
  · right
    exact ⟨h_hi_in_F₂, le_of_lt h_x_lt_hi, h_ge_x_to_ge_hi⟩
  · intro z hz _
    rcases le_or_gt ((z : Dyadic) : ℝ) x_val with h_le | h_gt
    · have h := h_below z hz (lt_of_le_of_lt h_le h_x_lt_hi)
      rw [abs_of_neg (by linarith : x_val - ((P.hi : Dyadic) : ℝ) < 0), neg_sub,
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ x_val - ((z : Dyadic) : ℝ)),
          hx_def]
      linarith
    · have h_z_ge_hi := h_ge_x_to_ge_hi z hz (le_of_lt h_gt)
      rw [abs_of_neg (by linarith : x_val - ((P.hi : Dyadic) : ℝ) < 0), neg_sub,
          abs_of_nonpos (by linarith : x_val - ((z : Dyadic) : ℝ) ≤ 0), neg_sub]
      linarith
  · rintro ⟨z, hzF₂, _, hne, heq⟩
    exfalso
    rcases le_or_gt ((z : Dyadic) : ℝ) x_val with h_le | h_gt
    · have h := h_below z hzF₂ (lt_of_le_of_lt h_le h_x_lt_hi)
      rw [abs_of_neg (by linarith : x_val - ((P.hi : Dyadic) : ℝ) < 0), neg_sub,
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ x_val - ((z : Dyadic) : ℝ)),
          hx_def] at heq
      linarith
    · have h_z_ge_hi := h_ge_x_to_ge_hi z hzF₂ (le_of_lt h_gt)
      have h_z_ne : ((z : Dyadic) : ℝ) ≠ ((P.hi : Dyadic) : ℝ) := fun h_eq =>
        hne ((Dyadic.coe_real_inj z P.hi).mp h_eq)
      rw [abs_of_neg (by linarith : x_val - ((P.hi : Dyadic) : ℝ) < 0), neg_sub,
          abs_of_nonpos (by linarith : x_val - ((z : Dyadic) : ℝ) ≤ 0), neg_sub]
        at heq
      exact h_z_ne (by linarith)

/-- RAZ in `F₂` carries `hi − δ` up onto `hi`. -/
private theorem f₂_RAZ_up (F₂ : FiniteFormat) {K : ℤ} (hK_le : K ≤ P.t)
    (h_hi_in_F₂ : P.hi ∈ F₂.toFormat)
    (h_below : ∀ z ∈ F₂.toFormat,
      ((z : Dyadic) : ℝ) < ((P.hi : Dyadic) : ℝ) →
      ((z : Dyadic) : ℝ) ≤ ((P.hi : Dyadic) : ℝ) - (2 : ℝ) ^ K) :
    RoundsFinite F₂ .awayZero
      (((P.hi : Dyadic) : ℝ) - (2 : ℝ) ^ (K - 2)) P.hi := by
  have h_2K2_pos : (0 : ℝ) < (2 : ℝ) ^ (K - 2) := zpow_pos (by norm_num) _
  have h_2K_split : (2 : ℝ) ^ K = 4 * (2 : ℝ) ^ (K - 2) := two_zpow_split_minus_two K
  set x_val : ℝ := ((P.hi : Dyadic) : ℝ) - (2 : ℝ) ^ (K - 2) with hx_def
  have h_x_pos : 0 < x_val := P.x_below_pos hK_le
  have h_x_lt_hi : x_val < ((P.hi : Dyadic) : ℝ) := by rw [hx_def]; linarith
  refine ⟨h_hi_in_F₂, ?_, ?_, ?_⟩
  · rw [abs_of_pos h_x_pos, abs_of_pos P.hi_pos]; linarith
  · exact le_of_lt (mul_pos P.hi_pos h_x_pos)
  · intro z hz hz_bnd hz_sign
    have h_z_nn : 0 ≤ ((z : Dyadic) : ℝ) := nonneg_of_mul_nonneg_pos hz_sign h_x_pos
    rw [abs_of_pos h_x_pos, abs_of_nonneg h_z_nn] at hz_bnd
    rw [abs_of_pos P.hi_pos, abs_of_nonneg h_z_nn]
    by_contra h_lt
    push Not at h_lt
    have h := h_below z hz h_lt
    rw [hx_def] at hz_bnd
    linarith

/-- RTZ in `F₂` carries `hi + δ` down onto `hi`. -/
private theorem f₂_RTZ_down (F₂ : FiniteFormat) {K : ℤ}
    (h_hi_in_F₂ : P.hi ∈ F₂.toFormat)
    (h_above : ∀ z ∈ F₂.toFormat,
      ((P.hi : Dyadic) : ℝ) < ((z : Dyadic) : ℝ) →
      ((P.hi : Dyadic) : ℝ) + (2 : ℝ) ^ K ≤ ((z : Dyadic) : ℝ)) :
    RoundsFinite F₂ .toZero
      (((P.hi : Dyadic) : ℝ) + (2 : ℝ) ^ (K - 2)) P.hi := by
  have h_2K2_pos : (0 : ℝ) < (2 : ℝ) ^ (K - 2) := zpow_pos (by norm_num) _
  have h_2K_split : (2 : ℝ) ^ K = 4 * (2 : ℝ) ^ (K - 2) := two_zpow_split_minus_two K
  set x_val : ℝ := ((P.hi : Dyadic) : ℝ) + (2 : ℝ) ^ (K - 2) with hx_def
  have h_x_pos : 0 < x_val := by linarith [P.hi_pos]
  refine ⟨h_hi_in_F₂, ?_, ?_, ?_⟩
  · rw [abs_of_pos P.hi_pos, abs_of_pos h_x_pos]; linarith
  · exact le_of_lt (mul_pos P.hi_pos h_x_pos)
  · intro z hz hz_bnd hz_sign
    have h_z_nn : 0 ≤ ((z : Dyadic) : ℝ) := nonneg_of_mul_nonneg_pos hz_sign h_x_pos
    rw [abs_of_nonneg h_z_nn, abs_of_pos h_x_pos] at hz_bnd
    rw [abs_of_pos P.hi_pos, abs_of_nonneg h_z_nn]
    by_contra h_gt
    push Not at h_gt
    have h := h_above z hz h_gt
    rw [hx_def] at hz_bnd
    linarith

/-- RNE in `F₂` carries `hi + δ` down onto `hi`. -/
private theorem f₂_RNE_down (F₂ : FiniteFormat) {K : ℤ}
    (h_hi_in_F₂ : P.hi ∈ F₂.toFormat)
    (h_above : ∀ z ∈ F₂.toFormat,
      ((P.hi : Dyadic) : ℝ) < ((z : Dyadic) : ℝ) →
      ((P.hi : Dyadic) : ℝ) + (2 : ℝ) ^ K ≤ ((z : Dyadic) : ℝ)) :
    RoundsFinite F₂ (.nearest .toEven)
      (((P.hi : Dyadic) : ℝ) + (2 : ℝ) ^ (K - 2)) P.hi := by
  have h_2K2_pos : (0 : ℝ) < (2 : ℝ) ^ (K - 2) := zpow_pos (by norm_num) _
  have h_2K_split : (2 : ℝ) ^ K = 4 * (2 : ℝ) ^ (K - 2) := two_zpow_split_minus_two K
  set x_val : ℝ := ((P.hi : Dyadic) : ℝ) + (2 : ℝ) ^ (K - 2) with hx_def
  have h_x_gt_hi : ((P.hi : Dyadic) : ℝ) < x_val := by rw [hx_def]; linarith
  have h_le_x_to_le_hi : ∀ z ∈ F₂.toFormat, ((z : Dyadic) : ℝ) ≤ x_val →
      ((z : Dyadic) : ℝ) ≤ ((P.hi : Dyadic) : ℝ) := by
    intro z hz hz_le
    by_contra h_gt
    push Not at h_gt
    have h := h_above z hz h_gt
    rw [hx_def] at hz_le
    linarith
  refine ⟨h_hi_in_F₂, ?_, ?_, ?_⟩
  · left
    exact ⟨h_hi_in_F₂, le_of_lt h_x_gt_hi, h_le_x_to_le_hi⟩
  · intro z hz _
    rcases le_or_gt ((z : Dyadic) : ℝ) x_val with h_le | h_gt
    · have h := h_le_x_to_le_hi z hz h_le
      rw [abs_of_pos (by linarith : (0 : ℝ) < x_val - ((P.hi : Dyadic) : ℝ)),
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ x_val - ((z : Dyadic) : ℝ))]
      linarith
    · have h_z_gt_hi : ((P.hi : Dyadic) : ℝ) < ((z : Dyadic) : ℝ) := by
        by_contra h_le'
        push Not at h_le'
        linarith
      have h := h_above z hz h_z_gt_hi
      rw [abs_of_pos (by linarith : (0 : ℝ) < x_val - ((P.hi : Dyadic) : ℝ)),
          abs_of_nonpos (by linarith : x_val - ((z : Dyadic) : ℝ) ≤ 0), neg_sub,
          hx_def]
      linarith
  · rintro ⟨z, hzF₂, _, hne, heq⟩
    exfalso
    rcases le_or_gt ((z : Dyadic) : ℝ) x_val with h_le | h_gt
    · have h := h_le_x_to_le_hi z hzF₂ h_le
      have h_z_ne : ((z : Dyadic) : ℝ) ≠ ((P.hi : Dyadic) : ℝ) := fun h_eq =>
        hne ((Dyadic.coe_real_inj z P.hi).mp h_eq)
      rw [abs_of_pos (by linarith : (0 : ℝ) < x_val - ((P.hi : Dyadic) : ℝ)),
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ x_val - ((z : Dyadic) : ℝ))]
        at heq
      exact h_z_ne (by linarith)
    · have h_z_gt_hi : ((P.hi : Dyadic) : ℝ) < ((z : Dyadic) : ℝ) := by linarith
      have h := h_above z hzF₂ h_z_gt_hi
      rw [abs_of_pos (by linarith : (0 : ℝ) < x_val - ((P.hi : Dyadic) : ℝ)),
          abs_of_nonpos (by linarith : x_val - ((z : Dyadic) : ℝ) ≤ 0), neg_sub,
          hx_def] at heq
      linarith

/-- **RNE → RTZ.** -/
private theorem no_rndRNE_RTZ (F₂ : FiniteFormat)
    (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ (.nearest .toEven) x z ∧
      RoundsFinite F₁.toFiniteFormat .toZero (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat .toZero x w := by
  obtain ⟨K, hK_le, h_below⟩ := P.f2_below_hi F₂ hsub
  have h_2K2_pos : (0 : ℝ) < (2 : ℝ) ^ (K - 2) := zpow_pos (by norm_num) _
  exact ⟨((P.hi : Dyadic) : ℝ) - (2 : ℝ) ^ (K - 2), P.hi, P.hi,
    P.f₂_RNE_up F₂ (hsub _ P.mem_hi) h_below,
    rounds_RTZ_self P.mem_hi,
    P.not_rounds_RTZ_hi (P.x_below_pos hK_le) (by linarith)⟩

/-- **RAZ → RTZ.** -/
private theorem no_rndRAZ_RTZ (F₂ : FiniteFormat)
    (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .awayZero x z ∧
      RoundsFinite F₁.toFiniteFormat .toZero (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat .toZero x w := by
  obtain ⟨K, hK_le, h_below⟩ := P.f2_below_hi F₂ hsub
  have h_2K2_pos : (0 : ℝ) < (2 : ℝ) ^ (K - 2) := zpow_pos (by norm_num) _
  exact ⟨((P.hi : Dyadic) : ℝ) - (2 : ℝ) ^ (K - 2), P.hi, P.hi,
    P.f₂_RAZ_up F₂ hK_le (hsub _ P.mem_hi) h_below,
    rounds_RTZ_self P.mem_hi,
    P.not_rounds_RTZ_hi (P.x_below_pos hK_le) (by linarith)⟩

/-- **RTZ → RAZ.** -/
private theorem no_rndRTZ_RAZ (F₂ : FiniteFormat)
    (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .toZero x z ∧
      RoundsFinite F₁.toFiniteFormat .awayZero (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat .awayZero x w := by
  obtain ⟨K, hK_le, h_above⟩ := P.f2_above_hi F₂ hsub
  have h_2K2_pos : (0 : ℝ) < (2 : ℝ) ^ (K - 2) := zpow_pos (by norm_num) _
  exact ⟨((P.hi : Dyadic) : ℝ) + (2 : ℝ) ^ (K - 2), P.hi, P.hi,
    P.f₂_RTZ_down F₂ (hsub _ P.mem_hi) h_above,
    rounds_RAZ_self P.mem_hi,
    P.not_rounds_RAZ_hi (by linarith)⟩

/-- **RNE → RAZ.** -/
private theorem no_rndRNE_RAZ (F₂ : FiniteFormat)
    (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ (.nearest .toEven) x z ∧
      RoundsFinite F₁.toFiniteFormat .awayZero (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat .awayZero x w := by
  obtain ⟨K, hK_le, h_above⟩ := P.f2_above_hi F₂ hsub
  have h_2K2_pos : (0 : ℝ) < (2 : ℝ) ^ (K - 2) := zpow_pos (by norm_num) _
  exact ⟨((P.hi : Dyadic) : ℝ) + (2 : ℝ) ^ (K - 2), P.hi, P.hi,
    P.f₂_RNE_down F₂ (hsub _ P.mem_hi) h_above,
    rounds_RAZ_self P.mem_hi,
    P.not_rounds_RAZ_hi (by linarith)⟩

/-- **RAZ → RTO.** -/
private theorem no_rndRAZ_RTO (F₂ : FiniteFormat)
    (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .awayZero x z ∧
      RoundsFinite F₁.toFiniteFormat .toOdd (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat .toOdd x w := by
  obtain ⟨K, hK_le, h_below⟩ := P.f2_below_hi F₂ hsub
  have h_2K2_pos : (0 : ℝ) < (2 : ℝ) ^ (K - 2) := zpow_pos (by norm_num) _
  exact ⟨((P.hi : Dyadic) : ℝ) - (2 : ℝ) ^ (K - 2), P.hi, P.hi,
    P.f₂_RAZ_up F₂ hK_le (hsub _ P.mem_hi) h_below,
    rounds_RTO_self P.mem_hi,
    P.not_rounds_RTO_hi (by intro h; nlinarith)⟩

/-- **RNE → RTO.** -/
private theorem no_rndRNE_RTO (F₂ : FiniteFormat)
    (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ (.nearest .toEven) x z ∧
      RoundsFinite F₁.toFiniteFormat .toOdd (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat .toOdd x w := by
  obtain ⟨K, hK_le, h_below⟩ := P.f2_below_hi F₂ hsub
  have h_2K2_pos : (0 : ℝ) < (2 : ℝ) ^ (K - 2) := zpow_pos (by norm_num) _
  exact ⟨((P.hi : Dyadic) : ℝ) - (2 : ℝ) ^ (K - 2), P.hi, P.hi,
    P.f₂_RNE_up F₂ (hsub _ P.mem_hi) h_below,
    rounds_RTO_self P.mem_hi,
    P.not_rounds_RTO_hi (by intro h; nlinarith)⟩

/-- **RTZ → RTO.** -/
private theorem no_rndRTZ_RTO (F₂ : FiniteFormat)
    (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .toZero x z ∧
      RoundsFinite F₁.toFiniteFormat .toOdd (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat .toOdd x w := by
  obtain ⟨K, hK_le, h_above⟩ := P.f2_above_hi F₂ hsub
  have h_2K2_pos : (0 : ℝ) < (2 : ℝ) ^ (K - 2) := zpow_pos (by norm_num) _
  exact ⟨((P.hi : Dyadic) : ℝ) + (2 : ℝ) ^ (K - 2), P.hi, P.hi,
    P.f₂_RTZ_down F₂ (hsub _ P.mem_hi) h_above,
    rounds_RTO_self P.mem_hi,
    P.not_rounds_RTO_hi (by intro h; nlinarith)⟩

/-- **RTZ → RNE.** `x = (lo2 + 2^(t−1)) + δ`, just above the lower midpoint:
RTZ in `F₂` lands at or below the midpoint, RNE then returns the even `lo2`;
the direct RNE of `x` is the strictly nearer `lo`. -/
private theorem no_rndRTZ_RNE (F₂ : FiniteFormat)
    (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .toZero x z ∧
      RoundsFinite F₁.toFiniteFormat (.nearest .toEven) (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat (.nearest .toEven) x w := by
  obtain ⟨K, hK_le, h_mid_below, h_mid_above⟩ := P.f2_mid_lo F₂ hsub
  have hb_top := P.f2_b_top F₂ hsub
  have h_half_pos : (0 : ℝ) < (2 : ℝ) ^ (P.t - 1) := zpow_pos (by norm_num) _
  have h_2K1_pos : (0 : ℝ) < (2 : ℝ) ^ (K - 1) := zpow_pos (by norm_num) _
  have h_2K2_pos : (0 : ℝ) < (2 : ℝ) ^ (K - 2) := zpow_pos (by norm_num) _
  have h_2K2_lt_2K1 : (2 : ℝ) ^ (K - 2) < (2 : ℝ) ^ (K - 1) :=
    zpow_lt_zpow_right₀ (by norm_num) (by omega)
  have h_2K1_le_half : (2 : ℝ) ^ (K - 1) ≤ (2 : ℝ) ^ (P.t - 1) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have h_two_half : (2 : ℝ) ^ P.t = 2 * (2 : ℝ) ^ (P.t - 1) := by
    have h := two_zpow_succ (P.t - 1)
    rwa [show P.t - 1 + 1 = P.t by ring] at h
  set x_val : ℝ := ((P.lo2 : Dyadic) : ℝ) + (2 : ℝ) ^ (P.t - 1) + (2 : ℝ) ^ (K - 2)
    with hx_def
  have h_x_pos : 0 < x_val := by rw [hx_def]; linarith [P.lo2_pos]
  set z : Dyadic := rndUnbounded F₂ .toZero x_val (not_isUndefined_toZero F₂)
    with hz_def
  have hz_rounds : RoundsFinite F₂ .toZero x_val z := by
    have h := rndUnbounded_satisfies F₂ .toZero x_val (not_isUndefined_toZero F₂)
    rwa [unbounded_eq_self hb_top] at h
  obtain ⟨hz_mem, hz_abs, hz_sign, hz_max⟩ := hz_rounds
  have h_z_nn : 0 ≤ ((z : Dyadic) : ℝ) := nonneg_of_mul_nonneg_pos hz_sign h_x_pos
  have h_z_le_x : ((z : Dyadic) : ℝ) ≤ x_val := by
    have h := hz_abs
    rwa [abs_of_nonneg h_z_nn, abs_of_pos h_x_pos] at h
  have h_lo2_in_F₂ : P.lo2 ∈ F₂.toFormat := hsub _ P.mem_lo2
  have h_z_ge : ((P.lo2 : Dyadic) : ℝ) ≤ ((z : Dyadic) : ℝ) := by
    have h_le_abs : |((P.lo2 : Dyadic) : ℝ)| ≤ |x_val| := by
      rw [abs_of_pos P.lo2_pos, abs_of_pos h_x_pos, hx_def]
      linarith
    have h_sign : ((P.lo2 : Dyadic) : ℝ) * x_val ≥ 0 :=
      le_of_lt (mul_pos P.lo2_pos h_x_pos)
    have h := hz_max P.lo2 h_lo2_in_F₂ h_le_abs h_sign
    rwa [abs_of_pos P.lo2_pos, abs_of_nonneg h_z_nn] at h
  have h_z_le_M : ((z : Dyadic) : ℝ)
      ≤ ((P.lo2 : Dyadic) : ℝ) + (2 : ℝ) ^ (P.t - 1) := by
    by_contra h_gt
    push Not at h_gt
    have h := h_mid_above z hz_mem h_gt
    rw [hx_def] at h_z_le_x
    linarith
  refine ⟨x_val, z, P.lo2, ⟨hz_mem, hz_abs, hz_sign, hz_max⟩,
    P.rounds_RNE_lo2 h_z_ge h_z_le_M, ?_⟩
  intro hr
  obtain ⟨_, _, h_close, _⟩ := hr
  have h_x_lt_lo : x_val < ((P.lo : Dyadic) : ℝ) := by
    rw [P.coe_lo, hx_def]
    linarith
  have h_lo_faith : IsFaithfulRound F₁.toFiniteFormat x_val P.lo := by
    right
    refine ⟨P.mem_lo, le_of_lt h_x_lt_lo, ?_⟩
    intro v hv hv_ge
    refine P.f1_ceil_lo2 v hv ?_
    rw [hx_def] at hv_ge
    linarith
  have h := h_close P.lo P.mem_lo h_lo_faith
  rw [P.coe_lo,
      abs_of_nonneg (by rw [hx_def]; linarith :
        (0 : ℝ) ≤ x_val - ((P.lo2 : Dyadic) : ℝ)),
      abs_of_nonpos (by rw [hx_def]; linarith :
        x_val - (((P.lo2 : Dyadic) : ℝ) + (2 : ℝ) ^ P.t) ≤ 0), neg_sub,
      hx_def] at h
  linarith

/-- **RAZ → RNE.** `x = (lo + 2^(t−1)) − δ`, just below the upper midpoint:
RAZ in `F₂` lands at or above the midpoint, RNE then returns the even `hi`;
the direct RNE of `x` is the strictly nearer `lo`. -/
private theorem no_rndRAZ_RNE (F₂ : FiniteFormat)
    (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .awayZero x z ∧
      RoundsFinite F₁.toFiniteFormat (.nearest .toEven) (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat (.nearest .toEven) x w := by
  obtain ⟨K, hK_le, h_mid_below, h_mid_above⟩ := P.f2_mid_hi F₂ hsub
  have hb_top := P.f2_b_top F₂ hsub
  have h_half_pos : (0 : ℝ) < (2 : ℝ) ^ (P.t - 1) := zpow_pos (by norm_num) _
  have h_2K1_pos : (0 : ℝ) < (2 : ℝ) ^ (K - 1) := zpow_pos (by norm_num) _
  have h_2K2_pos : (0 : ℝ) < (2 : ℝ) ^ (K - 2) := zpow_pos (by norm_num) _
  have h_2K2_lt_2K1 : (2 : ℝ) ^ (K - 2) < (2 : ℝ) ^ (K - 1) :=
    zpow_lt_zpow_right₀ (by norm_num) (by omega)
  have h_2K1_le_half : (2 : ℝ) ^ (K - 1) ≤ (2 : ℝ) ^ (P.t - 1) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have h_two_half : (2 : ℝ) ^ P.t = 2 * (2 : ℝ) ^ (P.t - 1) := by
    have h := two_zpow_succ (P.t - 1)
    rwa [show P.t - 1 + 1 = P.t by ring] at h
  have h_lo_pos : (0 : ℝ) < ((P.lo : Dyadic) : ℝ) := by
    have h_step_pos : (0 : ℝ) < (2 : ℝ) ^ P.t := zpow_pos (by norm_num) _
    rw [P.coe_lo]
    linarith [P.lo2_pos]
  set x_val : ℝ := ((P.lo : Dyadic) : ℝ) + (2 : ℝ) ^ (P.t - 1) - (2 : ℝ) ^ (K - 2)
    with hx_def
  have h_x_pos : 0 < x_val := by rw [hx_def]; linarith
  set z : Dyadic := rndUnbounded F₂ .awayZero x_val (not_isUndefined_awayZero F₂)
    with hz_def
  have hz_rounds : RoundsFinite F₂ .awayZero x_val z := by
    have h := rndUnbounded_satisfies F₂ .awayZero x_val (not_isUndefined_awayZero F₂)
    rwa [unbounded_eq_self hb_top] at h
  obtain ⟨hz_mem, hz_abs, hz_sign, hz_min⟩ := hz_rounds
  have h_z_nn : 0 ≤ ((z : Dyadic) : ℝ) := nonneg_of_mul_nonneg_pos hz_sign h_x_pos
  have h_z_ge_x : x_val ≤ ((z : Dyadic) : ℝ) := by
    have h := hz_abs
    rwa [abs_of_pos h_x_pos, abs_of_nonneg h_z_nn] at h
  have h_hi_in_F₂ : P.hi ∈ F₂.toFormat := hsub _ P.mem_hi
  have h_x_lt_hi : x_val < ((P.hi : Dyadic) : ℝ) := by
    rw [hx_def, P.coe_hi, P.coe_lo]
    linarith
  have h_z_le_hi : ((z : Dyadic) : ℝ) ≤ ((P.hi : Dyadic) : ℝ) := by
    have h_ge_abs : |x_val| ≤ |((P.hi : Dyadic) : ℝ)| := by
      rw [abs_of_pos h_x_pos, abs_of_pos P.hi_pos]
      linarith
    have h_sign : ((P.hi : Dyadic) : ℝ) * x_val ≥ 0 :=
      le_of_lt (mul_pos P.hi_pos h_x_pos)
    have h := hz_min P.hi h_hi_in_F₂ h_ge_abs h_sign
    rwa [abs_of_pos P.hi_pos, abs_of_nonneg h_z_nn] at h
  have h_z_ge_M : ((P.lo : Dyadic) : ℝ) + (2 : ℝ) ^ (P.t - 1)
      ≤ ((z : Dyadic) : ℝ) := by
    by_contra h_lt
    push Not at h_lt
    have h := h_mid_below z hz_mem h_lt
    rw [hx_def] at h_z_ge_x
    linarith
  refine ⟨x_val, z, P.hi, ⟨hz_mem, hz_abs, hz_sign, hz_min⟩,
    P.rounds_RNE_hi h_z_ge_M h_z_le_hi, ?_⟩
  intro hr
  obtain ⟨_, _, h_close, _⟩ := hr
  have h_x_gt_lo : ((P.lo : Dyadic) : ℝ) < x_val := by
    rw [hx_def]
    linarith
  have h_lo_faith : IsFaithfulRound F₁.toFiniteFormat x_val P.lo := by
    left
    refine ⟨P.mem_lo, le_of_lt h_x_gt_lo, ?_⟩
    intro v hv hv_le
    refine P.f1_floor_hi v hv ?_
    rw [hx_def] at hv_le
    rw [P.coe_lo] at hv_le
    rw [P.coe_hi]
    linarith
  have h := h_close P.lo P.mem_lo h_lo_faith
  have h_hi_lo : ((P.hi : Dyadic) : ℝ) = ((P.lo : Dyadic) : ℝ) + (2 : ℝ) ^ P.t := by
    rw [P.coe_hi, P.coe_lo]; ring
  rw [h_hi_lo,
      abs_of_nonpos (by rw [hx_def]; linarith :
        x_val - (((P.lo : Dyadic) : ℝ) + (2 : ℝ) ^ P.t) ≤ 0), neg_sub,
      abs_of_nonneg (by rw [hx_def]; linarith :
        (0 : ℝ) ≤ x_val - ((P.lo : Dyadic) : ℝ)),
      hx_def] at h
  linarith

/-- **RNE → RNE.** Needs one extra digit of containment: with
`mid = lo + 2^(t−1) ∈ F₂`, the witness `x = mid − δ` rounds (RNE, `F₂`) up
onto `mid`, whose `F₁`-tie breaks to the even `hi`; the direct RNE of `x`
is the strictly nearer `lo`. -/
private theorem no_rndRNE_RNE (F₂ : FiniteFormat)
    (hsub : (F₁.toFiniteFormat.extend 1).toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ (.nearest .toEven) x z ∧
      RoundsFinite F₁.toFiniteFormat (.nearest .toEven) (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat (.nearest .toEven) x w := by
  have h_mid_in_F₂ : P.mid ∈ F₂.toFormat := hsub _ P.mid_mem_ext1
  obtain ⟨K, hK_le, h_below, h_above⟩ := P.f2_mem_mid F₂ h_mid_in_F₂
  have h_half_pos : (0 : ℝ) < (2 : ℝ) ^ (P.t - 1) := zpow_pos (by norm_num) _
  have h_2K_pos : (0 : ℝ) < (2 : ℝ) ^ K := zpow_pos (by norm_num) _
  have h_2K2_pos : (0 : ℝ) < (2 : ℝ) ^ (K - 2) := zpow_pos (by norm_num) _
  have h_2K_split : (2 : ℝ) ^ K = 4 * (2 : ℝ) ^ (K - 2) := two_zpow_split_minus_two K
  have h_2K_le_half : (2 : ℝ) ^ K ≤ (2 : ℝ) ^ (P.t - 1) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have h_two_half : (2 : ℝ) ^ P.t = 2 * (2 : ℝ) ^ (P.t - 1) := by
    have h := two_zpow_succ (P.t - 1)
    rwa [show P.t - 1 + 1 = P.t by ring] at h
  set x_val : ℝ := ((P.mid : Dyadic) : ℝ) - (2 : ℝ) ^ (K - 2) with hx_def
  have h_x_lt_mid : x_val < ((P.mid : Dyadic) : ℝ) := by rw [hx_def]; linarith
  refine ⟨x_val, P.mid, P.hi, ?_, ?_, ?_⟩
  · -- RNE in F₂ rounds x up onto mid.
    have h_ge_x_to_ge_mid : ∀ z ∈ F₂.toFormat, x_val ≤ ((z : Dyadic) : ℝ) →
        ((P.mid : Dyadic) : ℝ) ≤ ((z : Dyadic) : ℝ) := by
      intro z hz hz_ge
      by_contra h_lt
      push Not at h_lt
      have h := h_below z hz h_lt
      rw [hx_def] at hz_ge
      linarith
    refine ⟨h_mid_in_F₂, ?_, ?_, ?_⟩
    · right
      exact ⟨h_mid_in_F₂, le_of_lt h_x_lt_mid, h_ge_x_to_ge_mid⟩
    · intro z hz _
      rcases le_or_gt ((z : Dyadic) : ℝ) x_val with h_le | h_gt
      · have h := h_below z hz (lt_of_le_of_lt h_le h_x_lt_mid)
        rw [abs_of_neg (by linarith : x_val - ((P.mid : Dyadic) : ℝ) < 0), neg_sub,
            abs_of_nonneg (by linarith : (0 : ℝ) ≤ x_val - ((z : Dyadic) : ℝ)),
            hx_def]
        linarith
      · have h_z_ge_mid := h_ge_x_to_ge_mid z hz (le_of_lt h_gt)
        rw [abs_of_neg (by linarith : x_val - ((P.mid : Dyadic) : ℝ) < 0), neg_sub,
            abs_of_nonpos (by linarith : x_val - ((z : Dyadic) : ℝ) ≤ 0), neg_sub]
        linarith
    · rintro ⟨z, hzF₂, _, hne, heq⟩
      exfalso
      rcases le_or_gt ((z : Dyadic) : ℝ) x_val with h_le | h_gt
      · have h := h_below z hzF₂ (lt_of_le_of_lt h_le h_x_lt_mid)
        rw [abs_of_neg (by linarith : x_val - ((P.mid : Dyadic) : ℝ) < 0), neg_sub,
            abs_of_nonneg (by linarith : (0 : ℝ) ≤ x_val - ((z : Dyadic) : ℝ)),
            hx_def] at heq
        linarith
      · have h_z_ge_mid := h_ge_x_to_ge_mid z hzF₂ (le_of_lt h_gt)
        have h_z_ne : ((z : Dyadic) : ℝ) ≠ ((P.mid : Dyadic) : ℝ) := fun h_eq =>
          hne ((Dyadic.coe_real_inj z P.mid).mp h_eq)
        have h_z_gt_mid : ((P.mid : Dyadic) : ℝ) < ((z : Dyadic) : ℝ) :=
          lt_of_le_of_ne h_z_ge_mid (Ne.symm h_z_ne)
        have h := h_above z hzF₂ h_z_gt_mid
        rw [abs_of_neg (by linarith : x_val - ((P.mid : Dyadic) : ℝ) < 0), neg_sub,
            abs_of_nonpos (by linarith : x_val - ((z : Dyadic) : ℝ) ≤ 0), neg_sub,
            hx_def] at heq
        linarith
  · -- The F₁-tie at mid breaks to the even hi.
    refine P.rounds_RNE_hi (le_of_eq P.coe_mid.symm) ?_
    rw [P.coe_mid, P.coe_hi, P.coe_lo]
    linarith
  · -- The direct RNE of x is lo.
    intro hr
    obtain ⟨_, _, h_close, _⟩ := hr
    have h_x_gt_lo : ((P.lo : Dyadic) : ℝ) < x_val := by
      rw [hx_def, P.coe_mid]
      linarith
    have h_x_lt_hi : x_val < ((P.hi : Dyadic) : ℝ) := by
      rw [hx_def, P.coe_mid, P.coe_hi, P.coe_lo]
      linarith
    have h_lo_faith : IsFaithfulRound F₁.toFiniteFormat x_val P.lo := by
      left
      refine ⟨P.mem_lo, le_of_lt h_x_gt_lo, ?_⟩
      intro v hv hv_le
      exact P.f1_floor_hi v hv (lt_of_le_of_lt hv_le h_x_lt_hi)
    have h := h_close P.lo P.mem_lo h_lo_faith
    have h_hi_lo : ((P.hi : Dyadic) : ℝ)
        = ((P.lo : Dyadic) : ℝ) + (2 : ℝ) ^ P.t := by
      rw [P.coe_hi, P.coe_lo]; ring
    rw [h_hi_lo,
        abs_of_nonpos (by
          rw [hx_def, P.coe_mid]
          linarith :
          x_val - (((P.lo : Dyadic) : ℝ) + (2 : ℝ) ^ P.t) ≤ 0), neg_sub,
        abs_of_nonneg (by
          rw [hx_def, P.coe_mid]
          linarith :
          (0 : ℝ) ≤ x_val - ((P.lo : Dyadic) : ℝ)),
        hx_def, P.coe_mid] at h
    linarith

end AnchorNeighborhood

/-! ## The quantum-format neighborhood

`AnchorNeighborhood` for `F₁_g p e = 𝒜(p, e, ⊤)`: step `2^e`, anchors
`(2·2^e, 3·2^e, 4·2^e)`, midpoint `7·2^(e−1)`. -/

private noncomputable def quantumNeighborhood (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ) :
    AnchorNeighborhood (F₁_g p hp_ge_2 e) where
  t := e
  lo2 := y_lo_low_g e
  lo := y_lo_g e
  hi := y_hi_g e
  mid := m_g e
  lo2_pos := by
    rw [coe_y_lo_low_g]
    have : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
    linarith
  coe_lo := by rw [coe_y_lo_g, coe_y_lo_low_g]; ring
  coe_hi := by
    rw [coe_y_hi_g, coe_y_lo_low_g]
    have h := two_zpow_add_two e
    linarith
  coe_mid := by
    rw [coe_m_g, coe_y_lo_g]
    have h := two_zpow_succ (e - 1)
    rw [show e - 1 + 1 = e by ring] at h
    linarith
  mem_lo2 := y_lo_low_mem_F₁_g p hp_ge_2 e
  mem_lo := y_lo_mem_F₁_g p hp_ge_2 e
  mem_hi := y_hi_mem_F₁_g p hp_ge_2 e
  even_lo2 := isEven_F₁_g_y_lo_low p hp_ge_2 e
  even_hi := isEven_F₁_g_y_hi p hp_ge_2 e
  not_odd_hi := notIsOdd_F₁_g_y_hi p hp_ge_2 e
  f1_floor_lo := by
    intro v hv hv_lt
    obtain ⟨c, hc⟩ := F₁_g_quantum p hp_ge_2 e hv
    have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
    rw [hc, coe_y_lo_g] at hv_lt
    rw [hc, coe_y_lo_low_g]
    have hc_lt : (c : ℝ) < 3 := lt_of_mul_lt_mul_right hv_lt h_2e_pos.le
    have hc_int : c < 3 := by exact_mod_cast hc_lt
    have hc_le : (c : ℝ) ≤ 2 := by exact_mod_cast (by omega : c ≤ 2)
    nlinarith
  f1_ceil_lo2 := by
    intro v hv hv_gt
    obtain ⟨c, hc⟩ := F₁_g_quantum p hp_ge_2 e hv
    have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
    rw [hc, coe_y_lo_low_g] at hv_gt
    rw [hc, coe_y_lo_g]
    have hc_gt : (2 : ℝ) < (c : ℝ) := lt_of_mul_lt_mul_right hv_gt h_2e_pos.le
    have hc_int : 2 < c := by exact_mod_cast hc_gt
    have hc_ge : (3 : ℝ) ≤ (c : ℝ) := by exact_mod_cast (by omega : 3 ≤ c)
    nlinarith
  f1_floor_hi := by
    intro v hv hv_lt
    obtain ⟨c, hc⟩ := F₁_g_quantum p hp_ge_2 e hv
    have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
    have h4 := two_zpow_add_two e
    rw [hc, coe_y_hi_g] at hv_lt
    rw [h4] at hv_lt
    rw [hc, coe_y_lo_g]
    have hc_lt : (c : ℝ) < 4 := lt_of_mul_lt_mul_right hv_lt h_2e_pos.le
    have hc_int : c < 4 := by exact_mod_cast hc_lt
    have hc_le : (c : ℝ) ≤ 3 := by exact_mod_cast (by omega : c ≤ 3)
    nlinarith
  f1_ceil_hi := by
    intro v hv hv_gt
    obtain ⟨c, hc⟩ := F₁_g_quantum p hp_ge_2 e hv
    have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
    have h4 := two_zpow_add_two e
    rw [hc, coe_y_lo_g] at hv_gt
    rw [hc, coe_y_hi_g, h4]
    have hc_gt : (3 : ℝ) < (c : ℝ) := lt_of_mul_lt_mul_right hv_gt h_2e_pos.le
    have hc_int : 3 < c := by exact_mod_cast hc_gt
    have hc_ge : (4 : ℝ) ≤ (c : ℝ) := by exact_mod_cast (by omega : 4 ≤ c)
    nlinarith
  mid_mem_ext1 := by
    have h_ext_p : ((F₁_g p hp_ge_2 e).toFiniteFormat.extend 1).p
        = (((p + 1 : ℕ+)) : WithTop ℕ+) := by
      change (F₁_g p hp_ge_2 e).p.map (· + (1 : ℕ+)) = _
      rw [F₁_g_p, WithTop.map_coe]
    have h_pp1_cast : (((p + 1 : ℕ+)) : ℕ) = (p : ℕ) + 1 := by exact_mod_cast rfl
    refine ⟨?_, ?_, trivial⟩
    · rw [h_ext_p, Dyadic.precisionAtMost_coe_real]
      refine ⟨7, e - 1, ?_, ?_⟩
      · rw [coe_m_g]; push_cast; ring
      · rw [h_pp1_cast]
        have h_pow : (8 : ℤ) ≤ (2 : ℤ) ^ ((p : ℕ) + 1) :=
          calc (8 : ℤ) = (2 : ℤ) ^ 3 := by norm_num
            _ ≤ (2 : ℤ) ^ ((p : ℕ) + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        have h_abs : |(7 : ℤ)| = 7 := by decide
        omega
    · change Dyadic.quantumAtLeast ((F₁_g p hp_ge_2 e).exp.map (· - (1 : ℤ))) (m_g e)
      rw [F₁_g_exp, WithBot.map_coe, Dyadic.quantumAtLeast_coe_real]
      exact ⟨7, by rw [coe_m_g]; push_cast; ring⟩
  f2_b_top := fun F₂ hsub =>
    F₂_bound_top_of_zpow_mem F₂ (fun N hN => hsub _ (zpow_mem_F₁_g p hp_ge_2 e hN))
  f2_below_hi := by
    intro F₂ hsub
    obtain ⟨K', hK'_le, h⟩ := gap_below_pow F₂ (E := e + 2)
      (fun g hg => by
        have hb := f₂_le_e_of_two_e_mem (hsub _ (two_e_mem_F₁_g p hp_ge_2 e)) hg
        omega)
    refine ⟨min K' e, min_le_right _ _, ?_⟩
    intro z hz hz_lt
    rw [coe_y_hi_g] at hz_lt
    have h1 := h z hz hz_lt
    have h_mono : (2 : ℝ) ^ (min K' e) ≤ (2 : ℝ) ^ K' :=
      zpow_le_zpow_right₀ (by norm_num) (min_le_left _ _)
    rw [coe_y_hi_g]
    linarith
  f2_above_hi := by
    intro F₂ hsub
    obtain ⟨K', hK'_le, h⟩ := gap_above_pow F₂ (E := e + 2)
      (fun g hg => by
        have hb := f₂_le_e_of_two_e_mem (hsub _ (two_e_mem_F₁_g p hp_ge_2 e)) hg
        omega)
    refine ⟨min K' e, min_le_right _ _, ?_⟩
    intro z hz hz_gt
    rw [coe_y_hi_g] at hz_gt
    have h1 := h z hz hz_gt
    have h_mono : (2 : ℝ) ^ (min K' e) ≤ (2 : ℝ) ^ K' :=
      zpow_le_zpow_right₀ (by norm_num) (min_le_left _ _)
    rw [coe_y_hi_g]
    linarith
  f2_mid_lo := by
    intro F₂ hsub
    obtain ⟨K, hK_le, h_below, h_above⟩ :=
      gap_around_mid F₂ (a := 5) (by norm_num) (by norm_num)
        (fun g hg => f₂_le_e_of_two_e_mem (hsub _ (two_e_mem_F₁_g p hp_ge_2 e)) hg)
        (p_ge2_of_y_lo_mem (hsub _ (y_lo_mem_F₁_g p hp_ge_2 e)))
    have h_A : ((5 : ℤ) : ℝ) * (2 : ℝ) ^ (e - 1)
        = ((y_lo_low_g e : Dyadic) : ℝ) + (2 : ℝ) ^ (e - 1) := by
      rw [coe_y_lo_low_g]
      have h := two_zpow_succ (e - 1)
      rw [show e - 1 + 1 = e by ring] at h
      push_cast
      linarith
    refine ⟨K, hK_le, ?_, ?_⟩
    · intro z hz hz_lt
      have h1 := h_below z hz (by rw [h_A]; exact hz_lt)
      rw [h_A] at h1
      exact h1
    · intro z hz hz_gt
      have h1 := h_above z hz (by rw [h_A]; exact hz_gt)
      rw [h_A] at h1
      exact h1
  f2_mid_hi := by
    intro F₂ hsub
    obtain ⟨K, hK_le, h_below, h_above⟩ :=
      gap_around_mid F₂ (a := 7) (by norm_num) (by norm_num)
        (fun g hg => f₂_le_e_of_two_e_mem (hsub _ (two_e_mem_F₁_g p hp_ge_2 e)) hg)
        (p_ge2_of_y_lo_mem (hsub _ (y_lo_mem_F₁_g p hp_ge_2 e)))
    have h_A : ((7 : ℤ) : ℝ) * (2 : ℝ) ^ (e - 1)
        = ((y_lo_g e : Dyadic) : ℝ) + (2 : ℝ) ^ (e - 1) := by
      rw [coe_y_lo_g]
      have h := two_zpow_succ (e - 1)
      rw [show e - 1 + 1 = e by ring] at h
      push_cast
      linarith
    refine ⟨K, hK_le, ?_, ?_⟩
    · intro z hz hz_lt
      have h1 := h_below z hz (by rw [h_A]; exact hz_lt)
      rw [h_A] at h1
      exact h1
    · intro z hz hz_gt
      have h1 := h_above z hz (by rw [h_A]; exact hz_gt)
      rw [h_A] at h1
      exact h1
  f2_mem_mid := by
    intro F₂ hm
    obtain ⟨K, hK_le, h_below, h_above⟩ := gap_around_m_mem F₂ hm
    have h_A : (7 : ℝ) * (2 : ℝ) ^ (e - 1) = ((m_g e : Dyadic) : ℝ) :=
      (coe_m_g e).symm
    refine ⟨K, hK_le, ?_, ?_⟩
    · intro z hz hz_lt
      have h1 := h_below z hz (by rw [h_A]; exact hz_lt)
      rw [h_A] at h1
      exact h1
    · intro z hz hz_gt
      have h1 := h_above z hz (by rw [h_A]; exact hz_gt)
      rw [h_A] at h1
      exact h1

/-! ## The full-precision target format `F₁t_g = 𝒜(⊤, e, ⊤)`

When `F₁.p = ⊤` the `FiniteFormat` invariant forces a finite quantum, and
`F₁` is the full integer grid of step `2^e`. The quantum-format anchors
`2·2^e < 3·2^e < 4·2^e` work verbatim: the precision constraint is
trivial, and parity reads the full integer coefficient
(`numDigits = log₂|x| − e + 1`). -/

private def F₁t_g (e : ℤ) : ParityFormat where
  toFiniteFormat :=
    { toFormat := { p := ⊤, exp := ((e : ℤ) : WithBot ℤ), b := ⊤ }
      finite := Or.inr WithBot.coe_ne_bot }
  parity := Or.inr WithBot.coe_ne_bot

@[simp] private theorem F₁t_g_p (e : ℤ) : (F₁t_g e).p = ⊤ := rfl

@[simp] private theorem F₁t_g_exp (e : ℤ) :
    (F₁t_g e).exp = (e : WithBot ℤ) := rfl

@[simp] private theorem F₁t_g_b (e : ℤ) : (F₁t_g e).b = ⊤ := rfl

/-- Membership in the integer-grid format: only the quantum matters. -/
private theorem mem_F₁t_g (e : ℤ) {v : Dyadic} (c : ℤ)
    (hv : ((v : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ) ^ e) :
    v ∈ (F₁t_g e).toFormat := by
  refine ⟨trivial, ?_, trivial⟩
  change Dyadic.quantumAtLeast ((e : ℤ) : WithBot ℤ) v
  rw [Dyadic.quantumAtLeast_coe_real]
  exact ⟨c, hv⟩

private theorem y_lo_mem_F₁t_g (e : ℤ) : y_lo_g e ∈ (F₁t_g e).toFormat :=
  mem_F₁t_g e 3 (by rw [coe_y_lo_g]; push_cast; ring)

private theorem y_lo_low_mem_F₁t_g (e : ℤ) :
    y_lo_low_g e ∈ (F₁t_g e).toFormat :=
  mem_F₁t_g e 2 (by rw [coe_y_lo_low_g]; push_cast; ring)

private theorem y_hi_mem_F₁t_g (e : ℤ) : y_hi_g e ∈ (F₁t_g e).toFormat :=
  mem_F₁t_g e 4 (by
    rw [coe_y_hi_g, two_zpow_add_two]
    push_cast
    ring)

private theorem two_e_mem_F₁t_g (e : ℤ) : two_e_g e ∈ (F₁t_g e).toFormat :=
  mem_F₁t_g e 1 (by rw [coe_two_e_g]; push_cast; ring)

private theorem zpow_mem_F₁t_g (e : ℤ) {N : ℤ} (hN : e ≤ N) :
    Dyadic.ofIntZpow 1 N ∈ (F₁t_g e).toFormat :=
  mem_F₁t_g e ((2 : ℤ) ^ (N - e).toNat) (by
    rw [Dyadic.coe_ofIntZpow, two_zpow_split N e hN]
    push_cast
    ring)

/-- Quantum extraction: every `z ∈ F₁t_g` is `c · 2^e` for some `c : ℤ`. -/
private theorem F₁t_g_quantum (e : ℤ) {z : Dyadic}
    (hz : z ∈ (F₁t_g e).toFormat) :
    ∃ c : ℤ, (z : ℝ) = (c : ℝ) * (2 : ℝ) ^ e := by
  have hq : Dyadic.quantumAtLeast ((e : ℤ) : WithBot ℤ) z := hz.2.1
  rw [Dyadic.quantumAtLeast_coe_real] at hq
  exact hq

private theorem F₁t_g_p_ne_1 (e : ℤ) :
    (F₁t_g e).p ≠ ((1 : ℕ+) : WithTop ℕ+) := by
  rw [F₁t_g_p]
  exact WithTop.top_ne_coe

/-- `IsEven F₁t_g (4·2^e)`: at `numDigits = 3`, the canonical significand
is `4`. -/
private theorem isEven_F₁t_g_y_hi (e : ℤ) : (F₁t_g e).IsEven (y_hi_g e) := by
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
  have h_nd_toNat : ((F₁t_g e).toFiniteFormat.numDigits
      ((y_hi_g e : Dyadic) : ℝ)).toNat = 3 := by
    rw [(F₁t_g e).toFiniteFormat.numDigits_top_coe h_y_ne_real
        (F₁t_g_exp e) (F₁t_g_p e), h_log]
    omega
  right
  refine ⟨4, e, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [h_coe_rat, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
    rw [show (2 : ℚ)^(2 : ℤ) = 4 by norm_num]
    push_cast; ring
  · rw [h_nd_toNat]; decide
  · rw [h_nd_toNat]; decide
  · rw [if_neg (F₁t_g_p_ne_1 e)]; decide

/-- `IsEven F₁t_g (2·2^e)`: at `numDigits = 2`, the canonical significand
is `2`. -/
private theorem isEven_F₁t_g_y_lo_low (e : ℤ) :
    (F₁t_g e).IsEven (y_lo_low_g e) := by
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
  have h_nd_toNat : ((F₁t_g e).toFiniteFormat.numDigits
      ((y_lo_low_g e : Dyadic) : ℝ)).toNat = 2 := by
    rw [(F₁t_g e).toFiniteFormat.numDigits_top_coe h_y_ne_real
        (F₁t_g_exp e) (F₁t_g_p e), h_log]
    omega
  right
  refine ⟨2, e, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [h_coe_rat]; push_cast; ring
  · rw [h_nd_toNat]; decide
  · rw [h_nd_toNat]; decide
  · rw [if_neg (F₁t_g_p_ne_1 e)]; decide

/-- `y_hi = 4·2^e` is not odd in `F₁t_g`: its true precision is 1, below
`numDigits = 3`. -/
private theorem notIsOdd_F₁t_g_y_hi (e : ℤ) : ¬ (F₁t_g e).IsOdd (y_hi_g e) := by
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
  have h_prec : Dyadic.precisionAtMost ((1 : ℕ+) : WithTop ℕ+) (y_hi_g e) := by
    rw [Dyadic.precisionAtMost_coe]
    refine ⟨1, e + 2, ?_, ?_⟩
    · rw [h_coe_rat]; push_cast; ring
    · decide
  have h_gt : ((1 : ℕ+) : ℤ) < (F₁t_g e).toFiniteFormat.numDigits
      ((y_hi_g e : Dyadic) : ℝ) := by
    rw [(F₁t_g e).toFiniteFormat.numDigits_top_coe h_y_ne_real
        (F₁t_g_exp e) (F₁t_g_p e), h_log]
    have h1 : ((1 : ℕ+) : ℤ) = 1 := by decide
    rw [h1]; omega
  exact (F₁t_g e).precisionAtMost_not_IsOdd h_gt h_prec

/-! ## The full-precision neighborhood

The same anchors as the quantum case, on the integer grid `F₁t_g e`. -/

private noncomputable def topNeighborhood (e : ℤ) :
    AnchorNeighborhood (F₁t_g e) where
  t := e
  lo2 := y_lo_low_g e
  lo := y_lo_g e
  hi := y_hi_g e
  mid := m_g e
  lo2_pos := by
    rw [coe_y_lo_low_g]
    have : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
    linarith
  coe_lo := by rw [coe_y_lo_g, coe_y_lo_low_g]; ring
  coe_hi := by
    rw [coe_y_hi_g, coe_y_lo_low_g]
    have h := two_zpow_add_two e
    linarith
  coe_mid := by
    rw [coe_m_g, coe_y_lo_g]
    have h := two_zpow_succ (e - 1)
    rw [show e - 1 + 1 = e by ring] at h
    linarith
  mem_lo2 := y_lo_low_mem_F₁t_g e
  mem_lo := y_lo_mem_F₁t_g e
  mem_hi := y_hi_mem_F₁t_g e
  even_lo2 := isEven_F₁t_g_y_lo_low e
  even_hi := isEven_F₁t_g_y_hi e
  not_odd_hi := notIsOdd_F₁t_g_y_hi e
  f1_floor_lo := by
    intro v hv hv_lt
    obtain ⟨c, hc⟩ := F₁t_g_quantum e hv
    have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
    rw [hc, coe_y_lo_g] at hv_lt
    rw [hc, coe_y_lo_low_g]
    have hc_lt : (c : ℝ) < 3 := lt_of_mul_lt_mul_right hv_lt h_2e_pos.le
    have hc_int : c < 3 := by exact_mod_cast hc_lt
    have hc_le : (c : ℝ) ≤ 2 := by exact_mod_cast (by omega : c ≤ 2)
    nlinarith
  f1_ceil_lo2 := by
    intro v hv hv_gt
    obtain ⟨c, hc⟩ := F₁t_g_quantum e hv
    have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
    rw [hc, coe_y_lo_low_g] at hv_gt
    rw [hc, coe_y_lo_g]
    have hc_gt : (2 : ℝ) < (c : ℝ) := lt_of_mul_lt_mul_right hv_gt h_2e_pos.le
    have hc_int : 2 < c := by exact_mod_cast hc_gt
    have hc_ge : (3 : ℝ) ≤ (c : ℝ) := by exact_mod_cast (by omega : 3 ≤ c)
    nlinarith
  f1_floor_hi := by
    intro v hv hv_lt
    obtain ⟨c, hc⟩ := F₁t_g_quantum e hv
    have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
    have h4 := two_zpow_add_two e
    rw [hc, coe_y_hi_g] at hv_lt
    rw [h4] at hv_lt
    rw [hc, coe_y_lo_g]
    have hc_lt : (c : ℝ) < 4 := lt_of_mul_lt_mul_right hv_lt h_2e_pos.le
    have hc_int : c < 4 := by exact_mod_cast hc_lt
    have hc_le : (c : ℝ) ≤ 3 := by exact_mod_cast (by omega : c ≤ 3)
    nlinarith
  f1_ceil_hi := by
    intro v hv hv_gt
    obtain ⟨c, hc⟩ := F₁t_g_quantum e hv
    have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
    have h4 := two_zpow_add_two e
    rw [hc, coe_y_lo_g] at hv_gt
    rw [hc, coe_y_hi_g, h4]
    have hc_gt : (3 : ℝ) < (c : ℝ) := lt_of_mul_lt_mul_right hv_gt h_2e_pos.le
    have hc_int : 3 < c := by exact_mod_cast hc_gt
    have hc_ge : (4 : ℝ) ≤ (c : ℝ) := by exact_mod_cast (by omega : 4 ≤ c)
    nlinarith
  mid_mem_ext1 := by
    refine ⟨trivial, ?_, trivial⟩
    change Dyadic.quantumAtLeast ((F₁t_g e).exp.map (· - (1 : ℤ))) (m_g e)
    rw [F₁t_g_exp, WithBot.map_coe, Dyadic.quantumAtLeast_coe_real]
    exact ⟨7, by rw [coe_m_g]; push_cast; ring⟩
  f2_b_top := fun F₂ hsub =>
    F₂_bound_top_of_zpow_mem F₂ (fun N hN => hsub _ (zpow_mem_F₁t_g e hN))
  f2_below_hi := by
    intro F₂ hsub
    obtain ⟨K', hK'_le, h⟩ := gap_below_pow F₂ (E := e + 2)
      (fun g hg => by
        have hb := f₂_le_e_of_two_e_mem (hsub _ (two_e_mem_F₁t_g e)) hg
        omega)
    refine ⟨min K' e, min_le_right _ _, ?_⟩
    intro z hz hz_lt
    rw [coe_y_hi_g] at hz_lt
    have h1 := h z hz hz_lt
    have h_mono : (2 : ℝ) ^ (min K' e) ≤ (2 : ℝ) ^ K' :=
      zpow_le_zpow_right₀ (by norm_num) (min_le_left _ _)
    rw [coe_y_hi_g]
    linarith
  f2_above_hi := by
    intro F₂ hsub
    obtain ⟨K', hK'_le, h⟩ := gap_above_pow F₂ (E := e + 2)
      (fun g hg => by
        have hb := f₂_le_e_of_two_e_mem (hsub _ (two_e_mem_F₁t_g e)) hg
        omega)
    refine ⟨min K' e, min_le_right _ _, ?_⟩
    intro z hz hz_gt
    rw [coe_y_hi_g] at hz_gt
    have h1 := h z hz hz_gt
    have h_mono : (2 : ℝ) ^ (min K' e) ≤ (2 : ℝ) ^ K' :=
      zpow_le_zpow_right₀ (by norm_num) (min_le_left _ _)
    rw [coe_y_hi_g]
    linarith
  f2_mid_lo := by
    intro F₂ hsub
    obtain ⟨K, hK_le, h_below, h_above⟩ :=
      gap_around_mid F₂ (a := 5) (by norm_num) (by norm_num)
        (fun g hg => f₂_le_e_of_two_e_mem (hsub _ (two_e_mem_F₁t_g e)) hg)
        (p_ge2_of_y_lo_mem (hsub _ (y_lo_mem_F₁t_g e)))
    have h_A : ((5 : ℤ) : ℝ) * (2 : ℝ) ^ (e - 1)
        = ((y_lo_low_g e : Dyadic) : ℝ) + (2 : ℝ) ^ (e - 1) := by
      rw [coe_y_lo_low_g]
      have h := two_zpow_succ (e - 1)
      rw [show e - 1 + 1 = e by ring] at h
      push_cast
      linarith
    refine ⟨K, hK_le, ?_, ?_⟩
    · intro z hz hz_lt
      have h1 := h_below z hz (by rw [h_A]; exact hz_lt)
      rw [h_A] at h1
      exact h1
    · intro z hz hz_gt
      have h1 := h_above z hz (by rw [h_A]; exact hz_gt)
      rw [h_A] at h1
      exact h1
  f2_mid_hi := by
    intro F₂ hsub
    obtain ⟨K, hK_le, h_below, h_above⟩ :=
      gap_around_mid F₂ (a := 7) (by norm_num) (by norm_num)
        (fun g hg => f₂_le_e_of_two_e_mem (hsub _ (two_e_mem_F₁t_g e)) hg)
        (p_ge2_of_y_lo_mem (hsub _ (y_lo_mem_F₁t_g e)))
    have h_A : ((7 : ℤ) : ℝ) * (2 : ℝ) ^ (e - 1)
        = ((y_lo_g e : Dyadic) : ℝ) + (2 : ℝ) ^ (e - 1) := by
      rw [coe_y_lo_g]
      have h := two_zpow_succ (e - 1)
      rw [show e - 1 + 1 = e by ring] at h
      push_cast
      linarith
    refine ⟨K, hK_le, ?_, ?_⟩
    · intro z hz hz_lt
      have h1 := h_below z hz (by rw [h_A]; exact hz_lt)
      rw [h_A] at h1
      exact h1
    · intro z hz hz_gt
      have h1 := h_above z hz (by rw [h_A]; exact hz_gt)
      rw [h_A] at h1
      exact h1
  f2_mem_mid := by
    intro F₂ hm
    obtain ⟨K, hK_le, h_below, h_above⟩ := gap_around_m_mem F₂ hm
    have h_A : (7 : ℝ) * (2 : ℝ) ^ (e - 1) = ((m_g e : Dyadic) : ℝ) :=
      (coe_m_g e).symm
    refine ⟨K, hK_le, ?_, ?_⟩
    · intro z hz hz_lt
      have h1 := h_below z hz (by rw [h_A]; exact hz_lt)
      rw [h_A] at h1
      exact h1
    · intro z hz hz_gt
      have h1 := h_above z hz (by rw [h_A]; exact hz_gt)
      rw [h_A] at h1
      exact h1


/-! ## The floating target format `F₁f_g = 𝒜(q, ⊥, ⊤)`

Finite precision `q ≥ 2`, *no minimum quantum*, unbounded magnitude.
Containing it forces `F₂.exp = ⊥` (it has elements of arbitrarily fine
quantum) and hence a finite `F₂.p = q₂ ≥ q`, so the `F₂`-side gap
dispatch reduces to binade quantization at precision `q₂`. -/

/-- The floating target format `𝒜(q, ⊥, ⊤)` with precision `q ≥ 2`. -/
private def F₁f_g (q : ℕ+) (hq_ge_2 : 2 ≤ (q : ℕ)) : ParityFormat where
  toFiniteFormat :=
    { toFormat := { p := ((q : ℕ+) : WithTop ℕ+), exp := ⊥, b := ⊤ }
      finite := Or.inl WithTop.coe_ne_top }
  parity := Or.inl (by
    intro h
    have h' : ((q : ℕ+) : WithTop ℕ+) = ((1 : ℕ+) : WithTop ℕ+) := h
    have h1 : q = (1 : ℕ+) := by exact_mod_cast h'
    have h2 : (q : ℕ) = 1 := by exact_mod_cast h1
    omega)

@[simp] private theorem F₁f_g_p (q : ℕ+) (hq : 2 ≤ (q : ℕ)) :
    (F₁f_g q hq).p = ((q : ℕ+) : WithTop ℕ+) := rfl

@[simp] private theorem F₁f_g_exp (q : ℕ+) (hq : 2 ≤ (q : ℕ)) :
    (F₁f_g q hq).exp = ⊥ := rfl

@[simp] private theorem F₁f_g_b (q : ℕ+) (hq : 2 ≤ (q : ℕ)) :
    (F₁f_g q hq).b = ⊤ := rfl

/-- Membership in the floating format: only the precision matters (the
quantum constraint is `⊥` and the bound is `⊤`). -/
private theorem mem_F₁f_g (q : ℕ+) (hq : 2 ≤ (q : ℕ)) {v : Dyadic} (c k : ℤ)
    (hv : (v : ℚ) = (c : ℚ) * (2 : ℚ) ^ k) (hc : |c| ≤ 2 ^ (q : ℕ)) :
    v ∈ (F₁f_g q hq).toFormat := by
  refine ⟨?_, trivial, trivial⟩
  exact Dyadic.precisionAtMost_of_abs_le c k hv hc

/-- `numDigits` of the floating format is constantly `q` on nonzero reals. -/
private theorem F₁f_g_numDigits (q : ℕ+) (hq : 2 ≤ (q : ℕ)) {x : ℝ}
    (hx : x ≠ 0) :
    (F₁f_g q hq).toFiniteFormat.numDigits x = ((q : ℕ) : ℤ) := by
  rw [(F₁f_g q hq).toFiniteFormat.numDigits_coe_bot hx rfl rfl]

/-- `F₁f_g.p ≠ 1`, the precision branch of the parity invariant. -/
private theorem F₁f_g_p_ne_1 (q : ℕ+) (hq : 2 ≤ (q : ℕ)) :
    (F₁f_g q hq).p ≠ ((1 : ℕ+) : WithTop ℕ+) := by
  rw [F₁f_g_p]
  intro h
  have h1 : q = (1 : ℕ+) := by exact_mod_cast h
  have h2 : (q : ℕ) = 1 := by exact_mod_cast h1
  omega

/-- `2^N ∈ F₁f_g` for **any** `N`: the format has no minimum quantum, so it
contains arbitrarily small and arbitrarily large powers of two. -/
private theorem zpow_mem_F₁f_g (q : ℕ+) (hq : 2 ≤ (q : ℕ)) (N : ℤ) :
    Dyadic.ofIntZpow 1 N ∈ (F₁f_g q hq).toFormat :=
  mem_F₁f_g q hq 1 N (Dyadic.coe_rat_ofIntZpow 1 N) (by
    have h_pow : (2 : ℤ) ≤ (2 : ℤ) ^ (q : ℕ) :=
      calc (2 : ℤ) = (2 : ℤ) ^ 1 := by norm_num
        _ ≤ (2 : ℤ) ^ (q : ℕ) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h_abs : |(1 : ℤ)| = 1 := by decide
    omega)

/-! ### Anchors of the floating neighborhood

Significand base `s := 2^(q−1)`: the smallest significand of the binade.
The anchors are `lo2 = s·2^t < lo = (s+1)·2^t < hi = (s+2)·2^t`, with
midpoint `mid = (2s+3)·2^(t−1)` of `(lo, hi)`. -/

/-- Significand base `s = 2^(q−1)`. -/
private def fs (q : ℕ+) : ℤ := 2 ^ ((q : ℕ) - 1)

private theorem fs_pos (q : ℕ+) : 0 < fs q := pow_pos (by norm_num) _

private theorem fs_ge_2 (q : ℕ+) (hq : 2 ≤ (q : ℕ)) : 2 ≤ fs q := by
  have h : (2 : ℤ) ^ 1 ≤ 2 ^ ((q : ℕ) - 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hfs : fs q = 2 ^ ((q : ℕ) - 1) := rfl
  norm_num at h
  omega

/-- `2s = 2^q`: the binade's upper significand boundary. -/
private theorem two_fs (q : ℕ+) : 2 * fs q = 2 ^ (q : ℕ) := by
  have h1 : 1 ≤ (q : ℕ) := q.one_le
  have h : (2 : ℤ) ^ (((q : ℕ) - 1) + 1) = 2 ^ ((q : ℕ) - 1) * 2 := pow_succ 2 _
  rw [show ((q : ℕ) - 1) + 1 = (q : ℕ) by omega] at h
  have hfs : fs q = 2 ^ ((q : ℕ) - 1) := rfl
  omega

private theorem fs_even (q : ℕ+) (hq : 2 ≤ (q : ℕ)) : Even (fs q) := by
  have hfs : fs q = 2 ^ ((q : ℕ) - 1) := rfl
  rw [hfs]
  exact (Int.even_pow).mpr ⟨even_two, by omega⟩

private theorem fs_lt (q : ℕ+) : fs q < 2 ^ (q : ℕ) := by
  have h1 := two_fs q
  have h2 := fs_pos q
  omega

/-- The four anchors at step exponent `t`. -/
private noncomputable def flo2 (q : ℕ+) (t : ℤ) : Dyadic :=
  Dyadic.ofIntZpow (fs q) t
private noncomputable def flo (q : ℕ+) (t : ℤ) : Dyadic :=
  Dyadic.ofIntZpow (fs q + 1) t
private noncomputable def fhi (q : ℕ+) (t : ℤ) : Dyadic :=
  Dyadic.ofIntZpow (fs q + 2) t
private noncomputable def fmid (q : ℕ+) (t : ℤ) : Dyadic :=
  Dyadic.ofIntZpow (2 * fs q + 3) (t - 1)

private theorem coe_flo2 (q : ℕ+) (t : ℤ) :
    ((flo2 q t : Dyadic) : ℝ) = (fs q : ℝ) * (2 : ℝ) ^ t := by
  rw [flo2, Dyadic.coe_ofIntZpow]

private theorem coe_flo (q : ℕ+) (t : ℤ) :
    ((flo q t : Dyadic) : ℝ) = ((fs q : ℝ) + 1) * (2 : ℝ) ^ t := by
  rw [flo, Dyadic.coe_ofIntZpow]; push_cast; ring

private theorem coe_fhi (q : ℕ+) (t : ℤ) :
    ((fhi q t : Dyadic) : ℝ) = ((fs q : ℝ) + 2) * (2 : ℝ) ^ t := by
  rw [fhi, Dyadic.coe_ofIntZpow]; push_cast; ring

private theorem coe_fmid (q : ℕ+) (t : ℤ) :
    ((fmid q t : Dyadic) : ℝ) = (2 * (fs q : ℝ) + 3) * (2 : ℝ) ^ (t - 1) := by
  rw [fmid, Dyadic.coe_ofIntZpow]; push_cast; ring

private theorem mem_flo2 (q : ℕ+) (hq : 2 ≤ (q : ℕ)) (t : ℤ) :
    flo2 q t ∈ (F₁f_g q hq).toFormat :=
  mem_F₁f_g q hq (fs q) t (Dyadic.coe_rat_ofIntZpow (fs q) t) (by
    have h1 := fs_pos q
    have h2 := two_fs q
    rw [abs_of_pos h1]
    omega)

private theorem mem_flo (q : ℕ+) (hq : 2 ≤ (q : ℕ)) (t : ℤ) :
    flo q t ∈ (F₁f_g q hq).toFormat :=
  mem_F₁f_g q hq (fs q + 1) t (Dyadic.coe_rat_ofIntZpow (fs q + 1) t) (by
    have h1 := fs_ge_2 q hq
    have h2 := two_fs q
    rw [abs_of_pos (by omega)]
    omega)

private theorem mem_fhi (q : ℕ+) (hq : 2 ≤ (q : ℕ)) (t : ℤ) :
    fhi q t ∈ (F₁f_g q hq).toFormat :=
  mem_F₁f_g q hq (fs q + 2) t (Dyadic.coe_rat_ofIntZpow (fs q + 2) t) (by
    have h1 := fs_ge_2 q hq
    have h2 := two_fs q
    rw [abs_of_pos (by omega)]
    omega)

private theorem flo2_pos_real (q : ℕ+) (t : ℤ) :
    (0 : ℝ) < ((flo2 q t : Dyadic) : ℝ) := by
  rw [coe_flo2]
  have h1 : (0 : ℝ) < (fs q : ℝ) := by exact_mod_cast fs_pos q
  have h2 : (0 : ℝ) < (2 : ℝ) ^ t := zpow_pos (by norm_num) _
  exact mul_pos h1 h2

private theorem fhi_pos_real (q : ℕ+) (t : ℤ) :
    (0 : ℝ) < ((fhi q t : Dyadic) : ℝ) := by
  rw [coe_fhi]
  have h1 : (0 : ℝ) < (fs q : ℝ) := by exact_mod_cast fs_pos q
  have h2 : (0 : ℝ) < (2 : ℝ) ^ t := zpow_pos (by norm_num) _
  nlinarith

/-! ### Parity of the floating anchors -/

/-- `IsEven` of `lo2 = 2^(q−1)·2^t`: the canonical significand at
`numDigits = q` is `2^(q−1)`, even since `q ≥ 2`. -/
private theorem even_flo2 (q : ℕ+) (hq : 2 ≤ (q : ℕ)) (t : ℤ) :
    (F₁f_g q hq).IsEven (flo2 q t) := by
  have h_ne : ((flo2 q t : Dyadic) : ℝ) ≠ 0 := ne_of_gt (flo2_pos_real q t)
  have h_nd_toNat : ((F₁f_g q hq).toFiniteFormat.numDigits
      ((flo2 q t : Dyadic) : ℝ)).toNat = (q : ℕ) := by
    rw [F₁f_g_numDigits q hq h_ne]
    omega
  right
  refine ⟨fs q, t, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact Dyadic.coe_rat_ofIntZpow (fs q) t
  · rw [h_nd_toNat, abs_of_pos (fs_pos q)]
    exact le_refl _
  · rw [h_nd_toNat, abs_of_pos (fs_pos q)]
    exact fs_lt q
  · rw [if_neg (F₁f_g_p_ne_1 q hq)]
    exact fs_even q hq

/-- `IsEven` of `hi = (2^(q−1)+2)·2^t`. For `q = 2` the value renormalizes
to `2·2^(t+1)` (significand `2`); for `q ≥ 3` the canonical significand is
`2^(q−1)+2` itself, even. -/
private theorem even_fhi (q : ℕ+) (hq : 2 ≤ (q : ℕ)) (t : ℤ) :
    (F₁f_g q hq).IsEven (fhi q t) := by
  have h_ne : ((fhi q t : Dyadic) : ℝ) ≠ 0 := ne_of_gt (fhi_pos_real q t)
  have h_nd_toNat : ((F₁f_g q hq).toFiniteFormat.numDigits
      ((fhi q t : Dyadic) : ℝ)).toNat = (q : ℕ) := by
    rw [F₁f_g_numDigits q hq h_ne]
    omega
  right
  rcases eq_or_lt_of_le hq with hq2 | hq3
  · -- `q = 2`: `hi = 4·2^t = 2·2^(t+1)`, canonical significand `2`.
    have h_fs2 : fs q = 2 := by
      change (2 : ℤ) ^ ((q : ℕ) - 1) = 2
      rw [show (q : ℕ) - 1 = 1 by omega]
      norm_num
    refine ⟨2, t + 1, ⟨?_, ?_, ?_⟩, ?_⟩
    · change ((Dyadic.ofIntZpow (fs q + 2) t : Dyadic) : ℚ) = _
      rw [Dyadic.coe_rat_ofIntZpow, h_fs2,
          show (2 : ℚ) ^ (t + 1) = 2 * (2 : ℚ) ^ t from by
            rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_one]; ring]
      push_cast
      ring
    · rw [h_nd_toNat, ← hq2]; decide
    · rw [h_nd_toNat, ← hq2]; decide
    · rw [if_neg (F₁f_g_p_ne_1 q hq)]; decide
  · -- `q ≥ 3`: canonical significand `2^(q−1)+2` directly.
    have hfs : fs q = 2 ^ ((q : ℕ) - 1) := rfl
    have h2fs := two_fs q
    have h4fs : 4 ≤ fs q := by
      have h4 : (2 : ℤ) ^ 2 ≤ 2 ^ ((q : ℕ) - 1) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      norm_num at h4
      omega
    refine ⟨fs q + 2, t, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact Dyadic.coe_rat_ofIntZpow (fs q + 2) t
    · rw [h_nd_toNat, abs_of_pos (by omega : (0 : ℤ) < fs q + 2)]
      omega
    · rw [h_nd_toNat, abs_of_pos (by omega : (0 : ℤ) < fs q + 2)]
      omega
    · rw [if_neg (F₁f_g_p_ne_1 q hq)]
      exact (fs_even q hq).add even_two

/-- `hi = (2^(q−1)+2)·2^t = (2^(q−2)+1)·2^(t+1)` has true precision at most
`q − 1 < q = numDigits`, so it is not odd in the floating format. -/
private theorem not_odd_fhi (q : ℕ+) (hq : 2 ≤ (q : ℕ)) (t : ℤ) :
    ¬ (F₁f_g q hq).IsOdd (fhi q t) := by
  have h_ne : ((fhi q t : Dyadic) : ℝ) ≠ 0 := ne_of_gt (fhi_pos_real q t)
  have h_w_pos : 0 < (q : ℕ) - 1 := by omega
  have hcoef : fs q + 2 = 2 * (2 ^ ((q : ℕ) - 2) + 1) := by
    have h : fs q = 2 * 2 ^ ((q : ℕ) - 2) := by
      change (2 : ℤ) ^ ((q : ℕ) - 1) = 2 * 2 ^ ((q : ℕ) - 2)
      rw [show (q : ℕ) - 1 = ((q : ℕ) - 2) + 1 by omega, pow_succ]
      ring
    omega
  have h_gt : (((⟨(q : ℕ) - 1, h_w_pos⟩ : ℕ+) : ℕ) : ℤ)
      < (F₁f_g q hq).toFiniteFormat.numDigits ((fhi q t : Dyadic) : ℝ) := by
    rw [F₁f_g_numDigits q hq h_ne]
    have hw : ((⟨(q : ℕ) - 1, h_w_pos⟩ : ℕ+) : ℕ) = (q : ℕ) - 1 := rfl
    omega
  refine (F₁f_g q hq).precisionAtMost_not_IsOdd h_gt ?_
  refine Dyadic.precisionAtMost_of_abs_le (2 ^ ((q : ℕ) - 2) + 1) (t + 1) ?_ ?_
  · change ((Dyadic.ofIntZpow (fs q + 2) t : Dyadic) : ℚ) = _
    rw [Dyadic.coe_rat_ofIntZpow, hcoef,
        show (2 : ℚ) ^ (t + 1) = 2 * (2 : ℚ) ^ t from by
          rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_one]; ring]
    push_cast
    ring
  · have h_pow_pos : (0 : ℤ) < 2 ^ ((q : ℕ) - 2) := pow_pos (by norm_num) _
    change |2 ^ ((q : ℕ) - 2) + 1| ≤ (2 : ℤ) ^ ((q : ℕ) - 1)
    rw [abs_of_pos (by omega)]
    have h_split : (2 : ℤ) ^ ((q : ℕ) - 1) = 2 * 2 ^ ((q : ℕ) - 2) := by
      rw [show (q : ℕ) - 1 = ((q : ℕ) - 2) + 1 by omega, pow_succ]
      ring
    omega

/-! ### `F₁f_g`-adjacency -/

/-- Every floating-format element in the window `[s·2^t, 2s·2^t)` is an
integer multiple of `2^t` (binade quantization at precision `q`). -/
private theorem F₁f_window_quantum (q : ℕ+) (hq : 2 ≤ (q : ℕ)) (t : ℤ)
    {v : Dyadic} (hv : v ∈ (F₁f_g q hq).toFormat)
    (h_lo : (fs q : ℝ) * (2 : ℝ) ^ t ≤ ((v : Dyadic) : ℝ))
    (h_hi : ((v : Dyadic) : ℝ) < 2 * (fs q : ℝ) * (2 : ℝ) ^ t) :
    ∃ c : ℤ, ((v : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ) ^ t := by
  have h_2E : (2 : ℝ) ^ (t + ((q : ℕ) : ℤ) - 1) = (fs q : ℝ) * (2 : ℝ) ^ t := by
    have h := two_zpow_split (t + ((q : ℕ) : ℤ) - 1) t (by omega)
    rw [show (t + ((q : ℕ) : ℤ) - 1 - t).toNat = (q : ℕ) - 1 by omega] at h
    rw [h]
    have hfs : fs q = 2 ^ ((q : ℕ) - 1) := rfl
    rw [hfs]
    push_cast
    ring
  have h_2E1 : (2 : ℝ) ^ (t + ((q : ℕ) : ℤ) - 1 + 1)
      = 2 * (fs q : ℝ) * (2 : ℝ) ^ t := by
    have h := two_zpow_succ (t + ((q : ℕ) : ℤ) - 1)
    rw [h, h_2E]
    ring
  obtain ⟨c, hc⟩ := binade_quantum (F₂ := (F₁f_g q hq).toFiniteFormat)
    (q₂ := q) rfl hv (by rw [h_2E]; exact h_lo) (by rw [h_2E1]; exact h_hi)
  rw [show t + ((q : ℕ) : ℤ) - 1 - ((q : ℕ) : ℤ) + 1 = t by ring] at hc
  exact ⟨c, hc⟩

/-- No floating-format element lies strictly between consecutive multiples
`d·2^t < (d+1)·2^t` inside the binade window. -/
private theorem no_F₁f_between (q : ℕ+) (hq : 2 ≤ (q : ℕ)) (t : ℤ)
    {d : ℤ} (hd_lo : fs q ≤ d) (hd_hi : d + 1 ≤ 2 * fs q)
    {v : Dyadic} (hv : v ∈ (F₁f_g q hq).toFormat)
    (h_above : (d : ℝ) * (2 : ℝ) ^ t < ((v : Dyadic) : ℝ))
    (h_below : ((v : Dyadic) : ℝ) < ((d : ℝ) + 1) * (2 : ℝ) ^ t) : False := by
  have h2t_pos : (0 : ℝ) < (2 : ℝ) ^ t := zpow_pos (by norm_num) _
  have hd_lo_r : (fs q : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd_lo
  have hd_hi_r : (d : ℝ) + 1 ≤ 2 * (fs q : ℝ) := by
    have h : ((d + 1 : ℤ) : ℝ) ≤ ((2 * fs q : ℤ) : ℝ) := by exact_mod_cast hd_hi
    push_cast at h
    linarith
  obtain ⟨c, hc⟩ := F₁f_window_quantum q hq t hv
    (by nlinarith) (by nlinarith)
  rw [hc] at h_above h_below
  have h1 : (d : ℝ) < (c : ℝ) := lt_of_mul_lt_mul_right h_above h2t_pos.le
  have h2 : (c : ℝ) < (d : ℝ) + 1 := lt_of_mul_lt_mul_right h_below h2t_pos.le
  have h1' : d < c := by exact_mod_cast h1
  have h2' : c < d + 1 := by
    have h : (c : ℝ) < ((d + 1 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast h
  omega

/-! ### Containment data and the floating `F₂`-side dispatch -/

/-- Containing the floating format pins down `F₂`'s shape: `F₂.exp = ⊥`
(else `2^(f₂−1) ∈ F₂` fails the quantum), hence `F₂.p = q₂` finite (by the
`FiniteFormat` invariant) with `q₂ ≥ q` (an odd coefficient of size
`2^(q−1)+1` is visible to the precision). -/
private theorem float_sub_data (q : ℕ+) (hq : 2 ≤ (q : ℕ))
    (F₂ : FiniteFormat) (hsub : (F₁f_g q hq).toFormat ⊆ F₂.toFormat) :
    ∃ q₂ : ℕ+, F₂.p = ((q₂ : ℕ+) : WithTop ℕ+) ∧ (q : ℕ) ≤ (q₂ : ℕ)
      ∧ F₂.exp = ⊥ := by
  have h_exp_bot : F₂.exp = ⊥ := by
    by_contra h_ne
    obtain ⟨f₂, hf₂⟩ := WithBot.ne_bot_iff_exists.mp h_ne
    have h_mem : Dyadic.ofIntZpow 1 (f₂ - 1) ∈ F₂.toFormat :=
      hsub _ (zpow_mem_F₁f_g q hq (f₂ - 1))
    have hquant : Dyadic.quantumAtLeast F₂.exp (Dyadic.ofIntZpow 1 (f₂ - 1)) :=
      h_mem.2.1
    rw [← hf₂, Dyadic.quantumAtLeast_coe_real] at hquant
    obtain ⟨c, hc⟩ := hquant
    rw [Dyadic.coe_ofIntZpow] at hc
    have h_step : (2 : ℝ) ^ f₂ = 2 * (2 : ℝ) ^ (f₂ - 1) := by
      have h := two_zpow_succ (f₂ - 1)
      rwa [show f₂ - 1 + 1 = f₂ by ring] at h
    rw [h_step] at hc
    have h2_pos : (0 : ℝ) < (2 : ℝ) ^ (f₂ - 1) := zpow_pos (by norm_num) _
    have h_eq : ((1 : ℤ) : ℝ) = ((2 * c : ℤ) : ℝ) := by
      apply mul_right_cancel₀ (ne_of_gt h2_pos)
      push_cast
      push_cast at hc
      linarith
    have h_int : (1 : ℤ) = 2 * c := by exact_mod_cast h_eq
    omega
  have hp_ne : F₂.p ≠ ⊤ := by
    rcases F₂.finite with h | h
    · exact h
    · exact absurd h_exp_bot h
  obtain ⟨q₂, hq₂⟩ := WithTop.ne_top_iff_exists.mp hp_ne
  refine ⟨q₂, hq₂.symm, ?_, h_exp_bot⟩
  have h_flo_mem : flo q 0 ∈ F₂.toFormat := hsub _ (mem_flo q hq 0)
  have h_even := fs_even q hq
  have h_odd : Odd (fs q + 1) := by
    obtain ⟨r, hr⟩ := h_even
    exact ⟨r, by omega⟩
  have h_fs_pos := fs_pos q
  have h_flo_eq : ((flo q 0 : Dyadic) : ℝ)
      = ((fs q + 1 : ℤ) : ℝ) * (2 : ℝ) ^ (0 : ℤ) := by
    rw [coe_flo]
    push_cast
    ring
  have h_lt := coeff_lt_of_odd_mem hq₂.symm h_odd (by omega) h_flo_mem h_flo_eq
  by_contra h_gt
  push Not at h_gt
  have h_le : (2 : ℤ) ^ (q₂ : ℕ) ≤ 2 ^ ((q : ℕ) - 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hfs : fs q = 2 ^ ((q : ℕ) - 1) := rfl
  omega

/-- Containing the floating format forces an unbounded `F₂` (it contains
arbitrarily large powers of two). -/
private theorem float_b_top (q : ℕ+) (hq : 2 ≤ (q : ℕ))
    (F₂ : FiniteFormat) (hsub : (F₁f_g q hq).toFormat ⊆ F₂.toFormat) :
    F₂.b = ⊤ := by
  by_contra h_b_ne
  obtain ⟨b, hb_eq⟩ := WithTop.ne_top_iff_exists.mp h_b_ne
  set N : ℤ := Int.log 2 ((b.val : Dyadic) : ℝ) + 1 with hN_def
  set y_huge : Dyadic := Dyadic.ofIntZpow 1 N with hy_huge_def
  have hy_huge_real : ((y_huge : Dyadic) : ℝ) = (2 : ℝ) ^ N := by
    rw [hy_huge_def, Dyadic.coe_ofIntZpow]; push_cast; ring
  have hy_huge_in_F₂ : y_huge ∈ F₂.toFormat := hsub _ (zpow_mem_F₁f_g q hq N)
  have hb_ok : Format.boundOK F₂.b y_huge := hy_huge_in_F₂.2.2
  rw [← hb_eq] at hb_ok
  change |((y_huge : Dyadic) : ℚ)| ≤ ((b.val : Dyadic) : ℚ) at hb_ok
  have hb_ok_real : |((y_huge : Dyadic) : ℝ)| ≤ ((b.val : Dyadic) : ℝ) := by
    rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast, ← Rat.cast_abs]
    exact_mod_cast hb_ok
  rw [hy_huge_real] at hb_ok_real
  have h_2N_pos : (0 : ℝ) < (2 : ℝ) ^ N := zpow_pos (by norm_num) _
  rw [abs_of_pos h_2N_pos] at hb_ok_real
  by_cases hb_pos : 0 < ((b.val : Dyadic) : ℝ)
  · have h_lt_log_succ : ((b.val : Dyadic) : ℝ)
        < (2 : ℝ) ^ (Int.log 2 ((b.val : Dyadic) : ℝ) + 1) := by
      have := Int.lt_zpow_succ_log_self (b := 2) (by norm_num : 1 < (2 : ℕ))
        ((b.val : Dyadic) : ℝ)
      rw [show ((2 : ℕ) : ℝ) = 2 from by push_cast; rfl] at this
      exact this
    rw [hN_def] at hb_ok_real
    linarith
  · push Not at hb_pos
    linarith

/-- Shift an integer power-of-two factor into the exponent. -/
private theorem int_mul_pow_shift (b : ℤ) (m : ℕ) (J : ℤ) :
    ((b * 2 ^ m : ℤ) : ℝ) * (2 : ℝ) ^ J = (b : ℝ) * (2 : ℝ) ^ (J + m) := by
  have h := two_zpow_split (J + m) J (by omega)
  rw [show (J + (m : ℤ) - J).toNat = m by omega] at h
  rw [h]
  push_cast
  ring

/-- Every `F₂`-element in the three-binade window
`[2^(E−1), 2^(E+2))` around `E := J + q₂` is an integer multiple of `2^J`
(by binade quantization in each of the three binades). -/
private theorem float_window_step (F₂ : FiniteFormat) {q₂ : ℕ+}
    (hp : F₂.p = ((q₂ : ℕ+) : WithTop ℕ+)) {J : ℤ} {z : Dyadic}
    (hz : z ∈ F₂.toFormat)
    (h_lo : (2 : ℝ) ^ (J + ((q₂ : ℕ) : ℤ) - 1) ≤ ((z : Dyadic) : ℝ))
    (h_hi : ((z : Dyadic) : ℝ) < (2 : ℝ) ^ (J + ((q₂ : ℕ) : ℤ) + 2)) :
    ∃ m : ℤ, ((z : Dyadic) : ℝ) = (m : ℝ) * (2 : ℝ) ^ J := by
  rcases lt_or_ge ((z : Dyadic) : ℝ) ((2 : ℝ) ^ (J + ((q₂ : ℕ) : ℤ))) with h1 | h1
  · -- binade `[2^(E−1), 2^E)`: step `2^J` exactly.
    obtain ⟨c, hc⟩ := binade_quantum (E := J + ((q₂ : ℕ) : ℤ) - 1) hp hz h_lo
      (by rw [show J + ((q₂ : ℕ) : ℤ) - 1 + 1 = J + ((q₂ : ℕ) : ℤ) by ring]
          exact h1)
    rw [show J + ((q₂ : ℕ) : ℤ) - 1 - ((q₂ : ℕ) : ℤ) + 1 = J by ring] at hc
    exact ⟨c, hc⟩
  · rcases lt_or_ge ((z : Dyadic) : ℝ) ((2 : ℝ) ^ (J + ((q₂ : ℕ) : ℤ) + 1))
      with h2 | h2
    · -- binade `[2^E, 2^(E+1))`: step `2^(J+1)`.
      obtain ⟨c, hc⟩ := binade_quantum (E := J + ((q₂ : ℕ) : ℤ)) hp hz h1 h2
      rw [show J + ((q₂ : ℕ) : ℤ) - ((q₂ : ℕ) : ℤ) + 1 = J + 1 by ring,
          two_zpow_succ J] at hc
      exact ⟨2 * c, by rw [hc]; push_cast; ring⟩
    · -- binade `[2^(E+1), 2^(E+2))`: step `2^(J+2)`.
      obtain ⟨c, hc⟩ := binade_quantum (E := J + ((q₂ : ℕ) : ℤ) + 1) hp hz h2
        (by rw [show J + ((q₂ : ℕ) : ℤ) + 1 + 1 = J + ((q₂ : ℕ) : ℤ) + 2 by ring]
            exact h_hi)
      rw [show J + ((q₂ : ℕ) : ℤ) + 1 - ((q₂ : ℕ) : ℤ) + 1 = J + 2 by ring,
          two_zpow_add_two J] at hc
      exact ⟨4 * c, by rw [hc]; push_cast; ring⟩

/-- **Floating local-grid gap.** In a format with finite precision `q₂`,
every element on either side of an anchor `a·2^J` with
`2^q₂ ≤ a ≤ 2^(q₂+1)` is at least the local step `2^J` away. -/
private theorem float_gap (F₂ : FiniteFormat) {q₂ : ℕ+}
    (hp : F₂.p = ((q₂ : ℕ+) : WithTop ℕ+)) {J a : ℤ}
    (ha_lo : 2 ^ (q₂ : ℕ) ≤ a) (ha_hi : a ≤ 2 ^ ((q₂ : ℕ) + 1)) :
    (∀ z ∈ F₂.toFormat, ((z : Dyadic) : ℝ) < (a : ℝ) * (2 : ℝ) ^ J →
      ((z : Dyadic) : ℝ) ≤ (a : ℝ) * (2 : ℝ) ^ J - (2 : ℝ) ^ J) ∧
    (∀ z ∈ F₂.toFormat, (a : ℝ) * (2 : ℝ) ^ J < ((z : Dyadic) : ℝ) →
      (a : ℝ) * (2 : ℝ) ^ J + (2 : ℝ) ^ J ≤ ((z : Dyadic) : ℝ)) := by
  have h2J_pos : (0 : ℝ) < (2 : ℝ) ^ J := zpow_pos (by norm_num) _
  have hq2_1 : 1 ≤ (q₂ : ℕ) := q₂.one_le
  have hE : (2 : ℝ) ^ (J + ((q₂ : ℕ) : ℤ))
      = (((2 : ℤ) ^ (q₂ : ℕ) : ℤ) : ℝ) * (2 : ℝ) ^ J := by
    have h := two_zpow_split (J + ((q₂ : ℕ) : ℤ)) J (by omega)
    rw [show (J + ((q₂ : ℕ) : ℤ) - J).toNat = (q₂ : ℕ) by omega] at h
    rw [h]
    push_cast
    ring
  have hE1 : (2 : ℝ) ^ (J + ((q₂ : ℕ) : ℤ) + 1)
      = (((2 : ℤ) ^ ((q₂ : ℕ) + 1) : ℤ) : ℝ) * (2 : ℝ) ^ J := by
    have h := two_zpow_split (J + ((q₂ : ℕ) : ℤ) + 1) J (by omega)
    rw [show (J + ((q₂ : ℕ) : ℤ) + 1 - J).toNat = (q₂ : ℕ) + 1 by omega] at h
    rw [h]
    push_cast
    ring
  have ha_lo_r : (((2 : ℤ) ^ (q₂ : ℕ) : ℤ) : ℝ) ≤ (a : ℝ) := by
    exact_mod_cast ha_lo
  have ha_hi_r : (a : ℝ) ≤ (((2 : ℤ) ^ ((q₂ : ℕ) + 1) : ℤ) : ℝ) := by
    exact_mod_cast ha_hi
  have hA_ge : (2 : ℝ) ^ (J + ((q₂ : ℕ) : ℤ)) ≤ (a : ℝ) * (2 : ℝ) ^ J := by
    rw [hE]
    exact mul_le_mul_of_nonneg_right ha_lo_r h2J_pos.le
  have hA_le : (a : ℝ) * (2 : ℝ) ^ J ≤ (2 : ℝ) ^ (J + ((q₂ : ℕ) : ℤ) + 1) := by
    rw [hE1]
    exact mul_le_mul_of_nonneg_right ha_hi_r h2J_pos.le
  have h_pow_lo : (2 : ℝ) ^ J ≤ (2 : ℝ) ^ (J + ((q₂ : ℕ) : ℤ) - 1) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have h_sum_lo : (2 : ℝ) ^ (J + ((q₂ : ℕ) : ℤ) - 1)
        + (2 : ℝ) ^ (J + ((q₂ : ℕ) : ℤ) - 1)
      = (2 : ℝ) ^ (J + ((q₂ : ℕ) : ℤ)) := by
    have h := two_zpow_succ (J + ((q₂ : ℕ) : ℤ) - 1)
    rw [show J + ((q₂ : ℕ) : ℤ) - 1 + 1 = J + ((q₂ : ℕ) : ℤ) by ring] at h
    linarith
  have h_pow_hi : (2 : ℝ) ^ J ≤ (2 : ℝ) ^ (J + ((q₂ : ℕ) : ℤ) + 1) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have h_sum_hi : (2 : ℝ) ^ (J + ((q₂ : ℕ) : ℤ) + 1)
        + (2 : ℝ) ^ (J + ((q₂ : ℕ) : ℤ) + 1)
      = (2 : ℝ) ^ (J + ((q₂ : ℕ) : ℤ) + 2) := by
    have h := two_zpow_succ (J + ((q₂ : ℕ) : ℤ) + 1)
    rw [show J + ((q₂ : ℕ) : ℤ) + 1 + 1 = J + ((q₂ : ℕ) : ℤ) + 2 by ring] at h
    linarith
  constructor
  · intro z hz hz_lt
    rcases lt_or_ge ((z : Dyadic) : ℝ) ((2 : ℝ) ^ (J + ((q₂ : ℕ) : ℤ) - 1))
      with hcase | hcase
    · -- Far below the binade: the anchor is at least `2^(E−1)` higher.
      linarith
    · -- On the local grid: integer-coefficient floor.
      obtain ⟨m, hm⟩ := float_window_step F₂ hp hz hcase (by
        have h12 : (2 : ℝ) ^ (J + ((q₂ : ℕ) : ℤ) + 1)
            ≤ (2 : ℝ) ^ (J + ((q₂ : ℕ) : ℤ) + 2) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
        linarith)
      rw [hm] at hz_lt ⊢
      have hm_lt : (m : ℝ) < (a : ℝ) := lt_of_mul_lt_mul_right hz_lt h2J_pos.le
      have hm_int : m < a := by exact_mod_cast hm_lt
      have hm_le : (m : ℝ) ≤ (a : ℝ) - 1 := by
        have h : (m : ℝ) ≤ ((a - 1 : ℤ) : ℝ) := by
          exact_mod_cast (by omega : m ≤ a - 1)
        push_cast at h
        linarith
      have h_mul := mul_le_mul_of_nonneg_right hm_le h2J_pos.le
      have h_ring : ((a : ℝ) - 1) * (2 : ℝ) ^ J
          = (a : ℝ) * (2 : ℝ) ^ J - (2 : ℝ) ^ J := by ring
      linarith
  · intro z hz hz_gt
    rcases lt_or_ge ((z : Dyadic) : ℝ) ((2 : ℝ) ^ (J + ((q₂ : ℕ) : ℤ) + 2))
      with hcase | hcase
    · -- On the local grid: integer-coefficient ceiling.
      obtain ⟨m, hm⟩ := float_window_step F₂ hp hz (by
        have h01 : (2 : ℝ) ^ (J + ((q₂ : ℕ) : ℤ) - 1)
            ≤ (2 : ℝ) ^ (J + ((q₂ : ℕ) : ℤ)) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
        linarith) hcase
      rw [hm] at hz_gt ⊢
      have hm_gt : (a : ℝ) < (m : ℝ) := lt_of_mul_lt_mul_right hz_gt h2J_pos.le
      have hm_int : a < m := by exact_mod_cast hm_gt
      have hm_ge : (a : ℝ) + 1 ≤ (m : ℝ) := by
        have h : ((a + 1 : ℤ) : ℝ) ≤ (m : ℝ) := by
          exact_mod_cast (by omega : a + 1 ≤ m)
        push_cast at h
        linarith
      have h_mul := mul_le_mul_of_nonneg_right hm_ge h2J_pos.le
      have h_ring : ((a : ℝ) + 1) * (2 : ℝ) ^ J
          = (a : ℝ) * (2 : ℝ) ^ J + (2 : ℝ) ^ J := by ring
      linarith
    · -- Far above: `z ≥ 2^(E+2) ≥ A + 2^J`.
      linarith

/-- Anchor-friendly wrapper for `float_gap`: an anchor `b·2^t'` with
`2^n ≤ b ≤ 2^(n+1)` (`n ≤ q₂`) rescales to coefficient `b·2^(q₂−n)` at the
local step `2^K`, `K = t' + n − q₂`. -/
private theorem float_anchor_gap (F₂ : FiniteFormat) {q₂ : ℕ+}
    (hp : F₂.p = ((q₂ : ℕ+) : WithTop ℕ+)) {b t' : ℤ} {n : ℕ}
    (hn_le : n ≤ (q₂ : ℕ))
    (hb_lo : 2 ^ n ≤ b) (hb_hi : b ≤ 2 ^ (n + 1)) :
    ∃ K : ℤ, K ≤ t' + (n : ℤ) - ((q₂ : ℕ) : ℤ) ∧
      (∀ z ∈ F₂.toFormat, ((z : Dyadic) : ℝ) < (b : ℝ) * (2 : ℝ) ^ t' →
        ((z : Dyadic) : ℝ) ≤ (b : ℝ) * (2 : ℝ) ^ t' - (2 : ℝ) ^ K) ∧
      (∀ z ∈ F₂.toFormat, (b : ℝ) * (2 : ℝ) ^ t' < ((z : Dyadic) : ℝ) →
        (b : ℝ) * (2 : ℝ) ^ t' + (2 : ℝ) ^ K ≤ ((z : Dyadic) : ℝ)) := by
  have h_pow_pos : (0 : ℤ) < 2 ^ ((q₂ : ℕ) - n) := pow_pos (by norm_num) _
  have ha_lo' : (2 : ℤ) ^ (q₂ : ℕ) ≤ b * 2 ^ ((q₂ : ℕ) - n) := by
    have h : (2 : ℤ) ^ (q₂ : ℕ) = 2 ^ n * 2 ^ ((q₂ : ℕ) - n) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h]
    exact mul_le_mul_of_nonneg_right hb_lo h_pow_pos.le
  have ha_hi' : b * 2 ^ ((q₂ : ℕ) - n) ≤ (2 : ℤ) ^ ((q₂ : ℕ) + 1) := by
    have h : (2 : ℤ) ^ ((q₂ : ℕ) + 1) = 2 ^ (n + 1) * 2 ^ ((q₂ : ℕ) - n) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h]
    exact mul_le_mul_of_nonneg_right hb_hi h_pow_pos.le
  obtain ⟨h_below, h_above⟩ :=
    float_gap F₂ hp (J := t' - (((q₂ : ℕ) - n : ℕ) : ℤ)) ha_lo' ha_hi'
  have h_anchor : ((b * 2 ^ ((q₂ : ℕ) - n) : ℤ) : ℝ)
        * (2 : ℝ) ^ (t' - (((q₂ : ℕ) - n : ℕ) : ℤ))
      = (b : ℝ) * (2 : ℝ) ^ t' := by
    rw [int_mul_pow_shift,
        show t' - (((q₂ : ℕ) - n : ℕ) : ℤ) + (((q₂ : ℕ) - n : ℕ) : ℤ) = t'
          by ring]
  refine ⟨t' - (((q₂ : ℕ) - n : ℕ) : ℤ), by omega, ?_, ?_⟩
  · intro z hz hz_lt
    have h := h_below z hz (by rw [h_anchor]; exact hz_lt)
    rw [h_anchor] at h
    exact h
  · intro z hz hz_gt
    have h := h_above z hz (by rw [h_anchor]; exact hz_gt)
    rw [h_anchor] at h
    exact h

/-- The floating-format anchor neighborhood: anchors `2^(q−1)·2^t`,
`(2^(q−1)+1)·2^t`, `(2^(q−1)+2)·2^t` at an arbitrary step exponent `t`. -/
private noncomputable def floatingNeighborhood (q : ℕ+) (hq : 2 ≤ (q : ℕ)) (t : ℤ) :
    AnchorNeighborhood (F₁f_g q hq) where
  t := t
  lo2 := flo2 q t
  lo := flo q t
  hi := fhi q t
  mid := fmid q t
  lo2_pos := flo2_pos_real q t
  coe_lo := by rw [coe_flo, coe_flo2]; ring
  coe_hi := by rw [coe_fhi, coe_flo2]; ring
  coe_mid := by
    have h_step : (2 : ℝ) ^ t = 2 * (2 : ℝ) ^ (t - 1) := by
      have h := two_zpow_succ (t - 1)
      rwa [show t - 1 + 1 = t by ring] at h
    rw [coe_fmid, coe_flo, h_step]
    ring
  mem_lo2 := mem_flo2 q hq t
  mem_lo := mem_flo q hq t
  mem_hi := mem_fhi q hq t
  even_lo2 := even_flo2 q hq t
  even_hi := even_fhi q hq t
  not_odd_hi := not_odd_fhi q hq t
  f1_floor_lo := by
    intro v hv hv_lt
    rcases le_or_gt ((v : Dyadic) : ℝ) ((flo2 q t : Dyadic) : ℝ) with h | h
    · exact h
    · exfalso
      have hfs2 := fs_ge_2 q hq
      refine no_F₁f_between q hq t (d := fs q) le_rfl (by omega) hv ?_ ?_
      · rw [coe_flo2] at h; exact h
      · rw [coe_flo] at hv_lt; exact hv_lt
  f1_ceil_lo2 := by
    intro v hv hv_gt
    rcases le_or_gt ((flo q t : Dyadic) : ℝ) ((v : Dyadic) : ℝ) with h | h
    · exact h
    · exfalso
      have hfs2 := fs_ge_2 q hq
      refine no_F₁f_between q hq t (d := fs q) le_rfl (by omega) hv ?_ ?_
      · rw [coe_flo2] at hv_gt; exact hv_gt
      · rw [coe_flo] at h; exact h
  f1_floor_hi := by
    intro v hv hv_lt
    rcases le_or_gt ((v : Dyadic) : ℝ) ((flo q t : Dyadic) : ℝ) with h | h
    · exact h
    · exfalso
      have hfs2 := fs_ge_2 q hq
      refine no_F₁f_between q hq t (d := fs q + 1) (by omega) (by omega) hv ?_ ?_
      · rw [coe_flo] at h; push_cast; linarith
      · rw [coe_fhi] at hv_lt; push_cast; linarith
  f1_ceil_hi := by
    intro v hv hv_gt
    rcases le_or_gt ((fhi q t : Dyadic) : ℝ) ((v : Dyadic) : ℝ) with h | h
    · exact h
    · exfalso
      have hfs2 := fs_ge_2 q hq
      refine no_F₁f_between q hq t (d := fs q + 1) (by omega) (by omega) hv ?_ ?_
      · rw [coe_flo] at hv_gt; push_cast; linarith
      · rw [coe_fhi] at h; push_cast; linarith
  mid_mem_ext1 := by
    have h_qq1_cast : (((q + 1 : ℕ+)) : ℕ) = (q : ℕ) + 1 := by exact_mod_cast rfl
    have h_ext_p : ((F₁f_g q hq).toFiniteFormat.extend 1).p
        = (((q + 1 : ℕ+)) : WithTop ℕ+) := by
      change (F₁f_g q hq).p.map (· + (1 : ℕ+)) = _
      rw [F₁f_g_p, WithTop.map_coe]
    refine ⟨?_, ?_, trivial⟩
    · rw [h_ext_p, Dyadic.precisionAtMost_coe_real]
      refine ⟨2 * fs q + 3, t - 1, ?_, ?_⟩
      · rw [coe_fmid]; push_cast; ring
      · rw [h_qq1_cast]
        have h2fs := two_fs q
        have hfs2 := fs_ge_2 q hq
        have hpow1 : (2 : ℤ) ^ ((q : ℕ) + 1) = 2 * 2 ^ (q : ℕ) := by
          rw [pow_succ]; ring
        rw [abs_of_pos (by omega)]
        omega
    · change Dyadic.quantumAtLeast ((F₁f_g q hq).exp.map (· - (1 : ℤ))) (fmid q t)
      exact trivial
  f2_b_top := float_b_top q hq
  f2_below_hi := by
    intro F₂ hsub
    obtain ⟨q₂, hp, hq_le, _⟩ := float_sub_data q hq F₂ hsub
    have hfs : fs q = 2 ^ ((q : ℕ) - 1) := rfl
    have h2fs := two_fs q
    have hfs2 := fs_ge_2 q hq
    have hpow : (2 : ℤ) ^ (((q : ℕ) - 1) + 1) = 2 ^ (q : ℕ) := by
      rw [show ((q : ℕ) - 1) + 1 = (q : ℕ) by omega]
    obtain ⟨K, hK_le, h_below, _⟩ := float_anchor_gap F₂ hp (b := fs q + 2)
      (t' := t) (n := (q : ℕ) - 1) (by omega) (by omega) (by omega)
    refine ⟨K, by omega, ?_⟩
    intro z hz hz_lt
    rw [coe_fhi] at hz_lt
    have h := h_below z hz (by push_cast; linarith)
    rw [coe_fhi]
    push_cast at h
    linarith
  f2_above_hi := by
    intro F₂ hsub
    obtain ⟨q₂, hp, hq_le, _⟩ := float_sub_data q hq F₂ hsub
    have hfs : fs q = 2 ^ ((q : ℕ) - 1) := rfl
    have h2fs := two_fs q
    have hfs2 := fs_ge_2 q hq
    have hpow : (2 : ℤ) ^ (((q : ℕ) - 1) + 1) = 2 ^ (q : ℕ) := by
      rw [show ((q : ℕ) - 1) + 1 = (q : ℕ) by omega]
    obtain ⟨K, hK_le, _, h_above⟩ := float_anchor_gap F₂ hp (b := fs q + 2)
      (t' := t) (n := (q : ℕ) - 1) (by omega) (by omega) (by omega)
    refine ⟨K, by omega, ?_⟩
    intro z hz hz_gt
    rw [coe_fhi] at hz_gt
    have h := h_above z hz (by push_cast; linarith)
    rw [coe_fhi]
    push_cast at h
    linarith
  f2_mid_lo := by
    intro F₂ hsub
    obtain ⟨q₂, hp, hq_le, _⟩ := float_sub_data q hq F₂ hsub
    have h2fs := two_fs q
    have hfs2 := fs_ge_2 q hq
    have hpow1 : (2 : ℤ) ^ ((q : ℕ) + 1) = 2 * 2 ^ (q : ℕ) := by
      rw [pow_succ]; ring
    obtain ⟨K, hK_le, h_below, h_above⟩ := float_anchor_gap F₂ hp
      (b := 2 * fs q + 1) (t' := t - 1) (n := (q : ℕ)) hq_le
      (by omega) (by omega)
    have h_step : (2 : ℝ) ^ t = 2 * (2 : ℝ) ^ (t - 1) := by
      have h := two_zpow_succ (t - 1)
      rwa [show t - 1 + 1 = t by ring] at h
    have h_A : ((2 * fs q + 1 : ℤ) : ℝ) * (2 : ℝ) ^ (t - 1)
        = ((flo2 q t : Dyadic) : ℝ) + (2 : ℝ) ^ (t - 1) := by
      rw [coe_flo2, h_step]
      push_cast
      ring
    refine ⟨K + 1, by omega, ?_, ?_⟩
    · intro z hz hz_lt
      rw [← h_A] at hz_lt
      have h := h_below z hz hz_lt
      rw [show K + 1 - 1 = K by ring, ← h_A]
      exact h
    · intro z hz hz_gt
      rw [← h_A] at hz_gt
      have h := h_above z hz hz_gt
      rw [show K + 1 - 1 = K by ring, ← h_A]
      exact h
  f2_mid_hi := by
    intro F₂ hsub
    obtain ⟨q₂, hp, hq_le, _⟩ := float_sub_data q hq F₂ hsub
    have h2fs := two_fs q
    have hfs2 := fs_ge_2 q hq
    have hpow1 : (2 : ℤ) ^ ((q : ℕ) + 1) = 2 * 2 ^ (q : ℕ) := by
      rw [pow_succ]; ring
    obtain ⟨K, hK_le, h_below, h_above⟩ := float_anchor_gap F₂ hp
      (b := 2 * fs q + 3) (t' := t - 1) (n := (q : ℕ)) hq_le
      (by omega) (by omega)
    have h_step : (2 : ℝ) ^ t = 2 * (2 : ℝ) ^ (t - 1) := by
      have h := two_zpow_succ (t - 1)
      rwa [show t - 1 + 1 = t by ring] at h
    have h_A : ((2 * fs q + 3 : ℤ) : ℝ) * (2 : ℝ) ^ (t - 1)
        = ((flo q t : Dyadic) : ℝ) + (2 : ℝ) ^ (t - 1) := by
      rw [coe_flo, h_step]
      push_cast
      ring
    refine ⟨K + 1, by omega, ?_, ?_⟩
    · intro z hz hz_lt
      rw [← h_A] at hz_lt
      have h := h_below z hz hz_lt
      rw [show K + 1 - 1 = K by ring, ← h_A]
      exact h
    · intro z hz hz_gt
      rw [← h_A] at hz_gt
      have h := h_above z hz hz_gt
      rw [show K + 1 - 1 = K by ring, ← h_A]
      exact h
  f2_mem_mid := by
    intro F₂ hmem
    have h_even := fs_even q hq
    have h_odd : Odd (2 * fs q + 3) := ⟨fs q + 1, by ring⟩
    have h_mid_real : ((fmid q t : Dyadic) : ℝ)
        = ((2 * fs q + 3 : ℤ) : ℝ) * (2 : ℝ) ^ (t - 1) := by
      rw [coe_fmid]
      push_cast
      ring
    rcases hexp_eq : F₂.exp with _ | f₂
    · -- `F₂.exp = ⊥`: finite precision `q₂ > q` is forced, and the mid sits
      -- on the binade grid of step `2^(t−1+q−q₂)`.
      have hexp_bot : F₂.exp = ⊥ := hexp_eq
      have hp_ne : F₂.p ≠ ⊤ := by
        rcases F₂.finite with h | h
        · exact h
        · exact absurd hexp_bot h
      obtain ⟨q₂, hq₂⟩ := WithTop.ne_top_iff_exists.mp hp_ne
      have hp : F₂.p = ((q₂ : ℕ+) : WithTop ℕ+) := hq₂.symm
      have h2fs := two_fs q
      have hfs2 := fs_ge_2 q hq
      have h_lt := coeff_lt_of_odd_mem hp h_odd (by omega) hmem h_mid_real
      have hq_lt : (q : ℕ) < (q₂ : ℕ) := by
        by_contra h_ge
        push Not at h_ge
        have h_le : (2 : ℤ) ^ (q₂ : ℕ) ≤ 2 ^ (q : ℕ) :=
          pow_le_pow_right₀ (by norm_num) h_ge
        omega
      have hpow1 : (2 : ℤ) ^ ((q : ℕ) + 1) = 2 * 2 ^ (q : ℕ) := by
        rw [pow_succ]; ring
      obtain ⟨K, hK_le, h_below, h_above⟩ := float_anchor_gap F₂ hp
        (b := 2 * fs q + 3) (t' := t - 1) (n := (q : ℕ)) (by omega)
        (by omega) (by omega)
      refine ⟨K, by omega, ?_, ?_⟩
      · intro z hz hz_lt
        rw [h_mid_real] at hz_lt ⊢
        exact h_below z hz hz_lt
      · intro z hz hz_gt
        rw [h_mid_real] at hz_gt ⊢
        exact h_above z hz hz_gt
    · -- `F₂.exp = f₂` finite: the mid is on the global grid, `f₂ ≤ t − 1`.
      have hexpc : F₂.exp = (f₂ : WithBot ℤ) := hexp_eq
      have h_f₂_le : f₂ ≤ t - 1 :=
        f₂_le_e_sub_one_of_odd_in_F₂ (e := t) hexpc hmem h_odd h_mid_real
      have hquant : Dyadic.quantumAtLeast F₂.exp (fmid q t) := hmem.2.1
      rw [hexpc, Dyadic.quantumAtLeast_coe_real] at hquant
      obtain ⟨c_t, hc_t⟩ := hquant
      have h2f₂_pos : (0 : ℝ) < (2 : ℝ) ^ f₂ := zpow_pos (by norm_num) _
      have h_target_lo : ((fmid q t : Dyadic) : ℝ) - (2 : ℝ) ^ f₂
          = ((c_t - 1 : ℤ) : ℝ) * (2 : ℝ) ^ f₂ := by
        rw [hc_t]
        push_cast
        ring
      have h_target_hi : ((fmid q t : Dyadic) : ℝ) + (2 : ℝ) ^ f₂
          = ((c_t + 1 : ℤ) : ℝ) * (2 : ℝ) ^ f₂ := by
        rw [hc_t]
        push_cast
        ring
      refine ⟨f₂, by omega, ?_, ?_⟩
      · intro z hz hz_lt
        have h := F₂_grid_floor hexpc h_target_lo z hz (by linarith)
        linarith
      · intro z hz hz_gt
        have h := F₂_grid_ceil hexpc h_target_hi z hz (by linarith)
        linarith

/-! ## The unified counterexamples

One theorem per invalid pairing, over an arbitrary `F₁ : ParityFormat`
with `p ≠ 1` and `b = ⊤`. In the doc comments,
`lo2 < lo < hi` are the neighborhood anchors (`lo` odd, `lo2`/`hi` even)
and `δ` is a quarter of `F₂`'s local step at the anchor. -/

/-- A `ParityFormat` is determined by its three data fields: with
`p = p₁`, `exp = e`, `b = ⊤` it *is* the quantum target format. -/
private theorem eq_F₁_g {F₁ : ParityFormat} {p₁ : ℕ+} {e : ℤ}
    (hp_ge_2 : 2 ≤ (p₁ : ℕ))
    (hp : F₁.p = ((p₁ : ℕ+) : WithTop ℕ+))
    (hexp : F₁.exp = ((e : ℤ) : WithBot ℤ))
    (hb : F₁.b = ⊤) :
    F₁ = F₁_g p₁ hp_ge_2 e := by
  obtain ⟨⟨⟨pp, ee, bb⟩, fin⟩, par⟩ := F₁
  have hp' : pp = ((p₁ : ℕ+) : WithTop ℕ+) := hp
  have hexp' : ee = ((e : ℤ) : WithBot ℤ) := hexp
  have hb' : bb = ⊤ := hb
  subst hp' hexp' hb'
  rfl

/-- With `p = p₁`, `exp = ⊥`, `b = ⊤` it *is* the floating target format. -/
private theorem eq_F₁f_g {F₁ : ParityFormat} {p₁ : ℕ+}
    (hp_ge_2 : 2 ≤ (p₁ : ℕ))
    (hp : F₁.p = ((p₁ : ℕ+) : WithTop ℕ+))
    (hexp : F₁.exp = ⊥)
    (hb : F₁.b = ⊤) :
    F₁ = F₁f_g p₁ hp_ge_2 := by
  obtain ⟨⟨⟨pp, ee, bb⟩, fin⟩, par⟩ := F₁
  have hp' : pp = ((p₁ : ℕ+) : WithTop ℕ+) := hp
  have hexp' : ee = ⊥ := hexp
  have hb' : bb = ⊤ := hb
  subst hp' hexp' hb'
  rfl

/-- With `p = ⊤`, `exp = e`, `b = ⊤` it *is* the full-precision target
format. -/
private theorem eq_F₁t_g {F₁ : ParityFormat} {e : ℤ}
    (hp : F₁.p = ⊤) (hexp : F₁.exp = ((e : ℤ) : WithBot ℤ))
    (hb : F₁.b = ⊤) :
    F₁ = F₁t_g e := by
  obtain ⟨⟨⟨pp, ee, bb⟩, fin⟩, par⟩ := F₁
  have hp' : pp = ⊤ := hp
  have hexp' : ee = ((e : ℤ) : WithBot ℤ) := hexp
  have hb' : bb = ⊤ := hb
  subst hp' hexp' hb'
  rfl

/-- Every unbounded `ParityFormat` with `p ≠ 1` carries an anchor
neighborhood, whatever its precision and quantum: dispatch on `F₁.p`,
then on `F₁.exp`. -/
private noncomputable def neighborhoodOf (F₁ : ParityFormat)
    (hp1 : F₁.p ≠ ((1 : ℕ+) : WithTop ℕ+)) (hb : F₁.b = ⊤) :
    AnchorNeighborhood F₁ :=
  match hP : F₁.p with
  | none =>
    -- `p = ⊤`: the `FiniteFormat` invariant forces a finite quantum.
    match hexp : F₁.exp with
    | none => False.elim (F₁.finite.elim (fun h => h hP) (fun h => h hexp))
    | some e => by
        rw [eq_F₁t_g (e := e) hP hexp hb]
        exact topNeighborhood e
  | some p₁ =>
    have hp_ge_2 : 2 ≤ (p₁ : ℕ) := by
      have h2 : (p₁ : ℕ) ≠ 1 := by
        intro h
        have h4 : p₁ = (1 : ℕ+) := by
          apply PNat.coe_injective
          simpa using h
        exact hp1 (by rw [hP, h4]; rfl)
      have h3 : 1 ≤ (p₁ : ℕ) := p₁.one_le
      omega
    match hexp : F₁.exp with
    | none => by
        rw [eq_F₁f_g hp_ge_2 hP hexp hb]
        exact floatingNeighborhood p₁ hp_ge_2 0
    | some e => by
        rw [eq_F₁_g (e := e) hp_ge_2 hP hexp hb]
        exact quantumNeighborhood p₁ hp_ge_2 e

/-- **RNE → RNE.** One extra digit makes the midpoint of `(lo, hi)`
`F₂`-representable: the intermediate RNE lands exactly on it,
manufacturing a tie that breaks to the even `hi`, while the direct RNE
returns the strictly nearer `lo`. (Tight: with `F₂ = F₁`,
RNE ∘ RNE = RNE by idempotence.) -/
theorem no_rndRNE_RNE
    (F₁ : ParityFormat)
    (hp1 : F₁.p ≠ ((1 : ℕ+) : WithTop ℕ+)) (hb : F₁.b = ⊤)
    (F₂ : FiniteFormat)
    (hsub : (F₁.toFiniteFormat.extend 1).toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ (.nearest .toEven) x z ∧
      RoundsFinite F₁.toFiniteFormat (.nearest .toEven) (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat (.nearest .toEven) x w :=
  (neighborhoodOf F₁ hp1 hb).no_rndRNE_RNE F₂ hsub

/-- **RNE → RAZ.** `x = hi + δ`: the intermediate RNE rounds down onto
`hi`, which RAZ fixes — but the direct RAZ must be at least `x > hi`. -/
theorem no_rndRNE_RAZ
    (F₁ : ParityFormat)
    (hp1 : F₁.p ≠ ((1 : ℕ+) : WithTop ℕ+)) (hb : F₁.b = ⊤)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ (.nearest .toEven) x z ∧
      RoundsFinite F₁.toFiniteFormat .awayZero (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat .awayZero x w :=
  (neighborhoodOf F₁ hp1 hb).no_rndRNE_RAZ F₂ hsub

/-- **RNE → RTZ.** `x = hi − δ`: the intermediate RNE carries `x` up onto
`hi`, which RTZ fixes — but the direct RTZ truncates to `lo` or below. -/
theorem no_rndRNE_RTZ
    (F₁ : ParityFormat)
    (hp1 : F₁.p ≠ ((1 : ℕ+) : WithTop ℕ+)) (hb : F₁.b = ⊤)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ (.nearest .toEven) x z ∧
      RoundsFinite F₁.toFiniteFormat .toZero (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat .toZero x w :=
  (neighborhoodOf F₁ hp1 hb).no_rndRNE_RTZ F₂ hsub

/-- **RTZ → RAZ.** `x = hi + δ`: the intermediate RTZ truncates onto `hi`,
which RAZ fixes — but the direct RAZ must reach the next `F₁`-element. -/
theorem no_rndRTZ_RAZ
    (F₁ : ParityFormat)
    (hp1 : F₁.p ≠ ((1 : ℕ+) : WithTop ℕ+)) (hb : F₁.b = ⊤)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .toZero x z ∧
      RoundsFinite F₁.toFiniteFormat .awayZero (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat .awayZero x w :=
  (neighborhoodOf F₁ hp1 hb).no_rndRTZ_RAZ F₂ hsub

/-- **RAZ → RTZ.** `x = hi − δ`: the intermediate RAZ pushes `x` up onto
`hi`, which RTZ fixes — but the direct RTZ truncates to `lo` or below. -/
theorem no_rndRAZ_RTZ
    (F₁ : ParityFormat)
    (hp1 : F₁.p ≠ ((1 : ℕ+) : WithTop ℕ+)) (hb : F₁.b = ⊤)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .awayZero x z ∧
      RoundsFinite F₁.toFiniteFormat .toZero (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat .toZero x w :=
  (neighborhoodOf F₁ hp1 hb).no_rndRAZ_RTZ F₂ hsub

/-- **RAZ → RTO.** `x = hi − δ`: the intermediate RAZ lands exactly on the
even `hi`, which RTO fixes — but the direct RTO selects the odd `lo`. -/
theorem no_rndRAZ_RTO
    (F₁ : ParityFormat)
    (hp1 : F₁.p ≠ ((1 : ℕ+) : WithTop ℕ+)) (hb : F₁.b = ⊤)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .awayZero x z ∧
      RoundsFinite F₁.toFiniteFormat .toOdd (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat .toOdd x w :=
  (neighborhoodOf F₁ hp1 hb).no_rndRAZ_RTO F₂ hsub

/-- **RNE → RTO.** `x = hi − δ`: the intermediate RNE lands exactly on the
even `hi`, which RTO fixes — but the direct RTO selects the odd `lo`. -/
theorem no_rndRNE_RTO
    (F₁ : ParityFormat)
    (hp1 : F₁.p ≠ ((1 : ℕ+) : WithTop ℕ+)) (hb : F₁.b = ⊤)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ (.nearest .toEven) x z ∧
      RoundsFinite F₁.toFiniteFormat .toOdd (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat .toOdd x w :=
  (neighborhoodOf F₁ hp1 hb).no_rndRNE_RTO F₂ hsub

/-- **RTZ → RTO.** `x = hi + δ`: the intermediate RTZ truncates onto the
even `hi`, which RTO fixes — but the direct RTO selects the odd element
above. -/
theorem no_rndRTZ_RTO
    (F₁ : ParityFormat)
    (hp1 : F₁.p ≠ ((1 : ℕ+) : WithTop ℕ+)) (hb : F₁.b = ⊤)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .toZero x z ∧
      RoundsFinite F₁.toFiniteFormat .toOdd (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat .toOdd x w :=
  (neighborhoodOf F₁ hp1 hb).no_rndRTZ_RTO F₂ hsub

/-- **RAZ → RNE.** `x = m − δ` for `m` the midpoint of `(lo, hi)`: the
intermediate RAZ lands on or above `m` (a spurious tie, or past the
boundary), so the inner RNE returns the even `hi` — but the direct RNE
returns the strictly nearer odd `lo`. -/
theorem no_rndRAZ_RNE
    (F₁ : ParityFormat)
    (hp1 : F₁.p ≠ ((1 : ℕ+) : WithTop ℕ+)) (hb : F₁.b = ⊤)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .awayZero x z ∧
      RoundsFinite F₁.toFiniteFormat (.nearest .toEven) (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat (.nearest .toEven) x w :=
  (neighborhoodOf F₁ hp1 hb).no_rndRAZ_RNE F₂ hsub

/-- **RTZ → RNE.** `x = m + δ` for `m` the midpoint of `(lo2, lo)`: the
intermediate RTZ lands on or below `m` (a spurious tie, or past the
boundary), so the inner RNE returns the even `lo2` — but the direct RNE
returns the strictly nearer odd `lo`. -/
theorem no_rndRTZ_RNE
    (F₁ : ParityFormat)
    (hp1 : F₁.p ≠ ((1 : ℕ+) : WithTop ℕ+)) (hb : F₁.b = ⊤)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .toZero x z ∧
      RoundsFinite F₁.toFiniteFormat (.nearest .toEven) (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat (.nearest .toEven) x w :=
  (neighborhoodOf F₁ hp1 hb).no_rndRTZ_RNE F₂ hsub

end Cex

end Mpfx
