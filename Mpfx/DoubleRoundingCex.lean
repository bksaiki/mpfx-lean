import Mpfx.Rounding
import Mpfx.Grid
import Mpfx.Digits
import Mpfx.RoundOp

/-!
# Counterexamples to the invalid double-rounding pairings (§5.2)

The ten `no_rnd<rm₂>_<rm₁>` theorems at the end of this file refute every
mode pairing absent from Fig. 9: rounding `x` first in `F₂` under `rm₂` and
then in `F₁` under `rm₁` can disagree with rounding `x` directly in `F₁`
under `rm₁`. Each theorem is *universal over `F₂`*: for **every** `F₂`
satisfying the stated containment, a witness `x` exists, so no side
condition on `(p₂, exp₂, b₂)` can validate these pairings.

## The gadget format and its anchors

`F₁_g p e = 𝒜(p, e, ⊤)` (with `p ≥ 2`) is the inner format used by all
counterexamples: finite precision, finite quantum, unbounded magnitude.
The anchors on its grid:

* `two_e_g = 2^e` (smallest positive anchor),
* `y_lo_low_g = 2·2^e` (even), `y_lo_g = 3·2^e` (odd),
* `y_hi_g = 4·2^e = 2^(e+2)` (even),
* `m_low_g = 5·2^(e-1)` (midpoint of `(y_lo_low, y_lo)`),
* `m_g = 7·2^(e-1)` (midpoint of `(y_lo, y_hi)`).

## The witness recipe and the local-step interface

Every witness is `anchor ± 2^(K−2)`: a quarter of `F₂`'s *local step* at
the anchor, placed on the side of the `rm₁`-decision boundary that `rm₂`
erases. The local step `2^K` is produced by the shape-dispatch lemmas
(`gap_below_pow`, `gap_above_pow`, `gap_around_mid`, `gap_around_m_mem`):
when `F₂.exp = f₂` is finite, `K = f₂` (the global quantum, any precision);
when `F₂.exp = ⊥`, the `FiniteFormat` invariant forces a finite precision
`q₂`, and within the binade `[2^E, 2^(E+1))` the format is a uniform grid
of step `2^(E−q₂+1)` (`binade_quantum`). Consequently **no restriction on
`F₂.exp` is needed anywhere**: the only `F₂` escaping all ten theorems
would be `𝒜(⊤, ⊥, ·)` — all of the dyadics, where rounding is the
identity — and that is excluded by `FiniteFormat` itself.

## Substrate notes

* `F₁_g` is a `ParityFormat` (Mpfx's parity tier), constructed with bound
  `⊤ : WithTop NonNegDyadic`.
* Precision/quantum predicates are `ℚ`-valued in Mpfx; membership proofs
  go through `precisionAtMost_coe` / `quantumAtLeast_coe`, but witness
  equations are stated over `ℝ` via `Dyadic.coe_ofIntZpow`, so we bridge
  with the `*_coe_real` companions or by casting.
* The RNE inner-step lemmas conclude `RoundsFinite … (.nearest .toEven) …`
  with the tie clause discharged using `F₁_g` itself as the even witness.
* Only `F₁_g` (with its `simp` projections) and the ten counterexamples are
  public; all supporting lemmas are `private`.
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

/-! ### Shape-generic local-grid interface

The counterexample proofs only ever use one structural fact about `F₂`:
*every element near the anchor is an integer multiple of some local step
`2^K`*. When `F₂.exp = f₂` is finite this is the global quantum (`K = f₂`,
any precision); when `F₂.exp = ⊥` the `FiniteFormat` invariant forces a
finite precision `q₂`, and within the binade `[2^E, 2^(E+1))` the format is
a uniform grid of step `2^(E−q₂+1)`. The dispatch lemmas below package the
resulting gap bounds uniformly, so the counterexamples need no hypothesis on
`F₂.exp` and no case split in their bodies. -/

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
`F₁`-midpoint `m = 7·2^(e−1)` is representable in `F₂`, the witness
`x = m − 2^(K−2)` — a quarter of `F₂`'s local step `2^K` below `m`
(`gap_around_m_mem`) — defeats RNE-RNE double rounding, for *any* shape of
`F₂`. Near `m`, every `F₂`-element is a multiple of `2^K` while `m` lies on
that grid, so `m` is the strictly nearest `F₂`-element to `x` (`z = m`);
the `F₁`-tie at `m` then breaks to the even `y_hi = 4·2^e`, while the
direct RNE of `x` is `y_lo = 3·2^e`. -/
private theorem no_rndRNE_RNE_of_m_mem
    (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    (F₂ : FiniteFormat) (hm_in_F₂ : m_g e ∈ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ (.nearest .toEven) x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat (.nearest .toEven) (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat (.nearest .toEven) x w := by
  obtain ⟨f₂, hf₂, h_disp_below, h_disp_above⟩ := gap_around_m_mem F₂ hm_in_F₂
  have h_y_lo_in_F₁ := y_lo_mem_F₁_g p hp_ge_2 e
  have h7_eq : (7 : ℝ) * (2 : ℝ)^(e - 1) = (7/2) * (2 : ℝ)^e := by
    have h := two_zpow_succ (e - 1)
    rw [show e - 1 + 1 = e by ring] at h
    linarith
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
  -- Grid dichotomy around `x`, from `gap_around_m_mem`.
  have h_floor : ∀ z' ∈ F₂.toFormat, ((z' : Dyadic) : ℝ) ≤ x_val →
      ((z' : Dyadic) : ℝ) ≤ (7/2) * (2 : ℝ)^e - (2 : ℝ)^f₂ := by
    intro z' hz' hz'_le
    have h_lt_m : ((z' : Dyadic) : ℝ) < (7 : ℝ) * (2 : ℝ)^(e - 1) := by
      rw [h7_eq]
      rw [hx_def] at hz'_le
      linarith
    have h := h_disp_below z' hz' h_lt_m
    rw [h7_eq] at h
    linarith
  have h_ceil : ∀ z' ∈ F₂.toFormat, x_val ≤ ((z' : Dyadic) : ℝ) →
      (7/2) * (2 : ℝ)^e ≤ ((z' : Dyadic) : ℝ) := by
    intro z' hz' hz'_ge
    by_contra h_lt
    push Not at h_lt
    have h := h_disp_below z' hz' (by rw [h7_eq]; exact h_lt)
    rw [h7_eq] at h
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

/-- **Counterexample to `rndRNE_RNE`.** A single extra digit — just enough
to make the `F₁`-midpoints representable in `F₂` — already defeats RNE-RNE:
the containment `(F₁.extend 1) ⊆ F₂` places the midpoint `m = 7·2^(e−1)`
in `F₂`, which is all `no_rndRNE_RNE_of_m_mem` needs. (The containment
cannot be weakened to `F₁ ⊆ F₂`: with `F₂ = F₁`, RNE ∘ RNE = RNE by
idempotence.) -/
theorem no_rndRNE_RNE
    (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    (F₂ : FiniteFormat)
    (hsub : ((F₁_g p hp_ge_2 e).toFiniteFormat.extend 1).toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ (.nearest .toEven) x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat (.nearest .toEven) (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat (.nearest .toEven) x w := by
  -- `m = 7·2^(e−1)` is in the extend-1 format (3 significant bits ≤ p + 1,
  -- quantum exactly e − 1), hence in `F₂`.
  have h_ext_p : ((F₁_g p hp_ge_2 e).toFiniteFormat.extend 1).p
      = (((p + 1 : ℕ+)) : WithTop ℕ+) := by
    change (F₁_g p hp_ge_2 e).p.map (· + (1 : ℕ+)) = _
    rw [F₁_g_p, WithTop.map_coe]
  have h_pp1_cast : (((p + 1 : ℕ+)) : ℕ) = (p : ℕ) + 1 := by exact_mod_cast rfl
  have hm_in_ext1 :
      m_g e ∈ ((F₁_g p hp_ge_2 e).toFiniteFormat.extend 1).toFormat := by
    refine ⟨?_, ?_, trivial⟩
    · rw [h_ext_p, Dyadic.precisionAtMost_coe_real]
      refine ⟨7, e - 1, ?_, ?_⟩
      · rw [coe_m_g]; push_cast; ring
      · rw [h_pp1_cast]
        have h_pow : (8 : ℤ) ≤ (2 : ℤ)^((p : ℕ) + 1) :=
          calc (8 : ℤ) = (2 : ℤ)^3 := by norm_num
            _ ≤ (2 : ℤ)^((p : ℕ) + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        have h_abs : |(7 : ℤ)| = 7 := by decide
        omega
    · change Dyadic.quantumAtLeast ((F₁_g p hp_ge_2 e).exp.map (· - (1 : ℤ))) (m_g e)
      rw [F₁_g_exp, WithBot.map_coe, Dyadic.quantumAtLeast_coe_real]
      exact ⟨7, by rw [coe_m_g]; push_cast; ring⟩
  have hm_in_F₂ : m_g e ∈ F₂.toFormat := hsub _ hm_in_ext1
  exact no_rndRNE_RNE_of_m_mem p hp_ge_2 e F₂ hm_in_F₂

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

/-- **Counterexample to `rndRNE_RAZ`.** With `x = 2^e + δ` for `δ` a quarter
of `F₂`'s local step above `2^e`, the intermediate RNE rounds `x` *down*
onto `2^e` (its strictly nearest `F₂`-element), and RAZ then fixes the
representable `2^e` — but the direct RAZ of `x` must be at least `x`,
which exceeds `2^e`. The intermediate rounding erases the away-from-zero
obligation. -/
theorem no_rndRNE_RAZ
    (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    (F₂ : FiniteFormat)
    (hsub : (F₁_g p hp_ge_2 e).toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ (.nearest .toEven) x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .awayZero (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .awayZero x w := by
  obtain ⟨f₂, hf₂_le_e, h_above⟩ := gap_above_pow F₂ (E := e)
    (fun g hg => f₂_le_e_of_F₁_g_subset p hp_ge_2 e F₂.toFormat hsub hg)
  have h_two_e_in_F₁ := two_e_mem_F₁_g p hp_ge_2 e
  have h_two_e_in_F₂ : two_e_g e ∈ F₂.toFormat := hsub _ h_two_e_in_F₁
  set x_val : ℝ := (2 : ℝ)^e + (2 : ℝ)^(f₂ - 2) with hx_def
  have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
  have h_2f2_pos : (0 : ℝ) < (2 : ℝ)^(f₂ - 2) := zpow_pos (by norm_num) _
  have h_2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
  have h_2f_split : (2 : ℝ)^f₂ = 4 * (2 : ℝ)^(f₂ - 2) := two_zpow_split_minus_two f₂
  have h_x_pos : 0 < x_val := by rw [hx_def]; linarith
  have h_x_gt_2e : (2 : ℝ)^e < x_val := by rw [hx_def]; linarith
  have h_two_e_coe := coe_two_e_g e
  -- No `F₂`-element lies in `(2^e, x]`.
  have h_F₂_le_x_to_le_2e : ∀ z ∈ F₂.toFormat, ((z : Dyadic) : ℝ) ≤ x_val →
      ((z : Dyadic) : ℝ) ≤ (2 : ℝ)^e := by
    intro z hz hz_le
    by_contra h_gt
    push Not at h_gt
    have h_z_ge := h_above z hz h_gt
    rw [hx_def] at hz_le
    linarith
  refine ⟨x_val, two_e_g e, two_e_g e, ?_, ?_, ?_⟩
  · -- RNE in `F₂` rounds `x` down onto `2^e`.
    refine ⟨h_two_e_in_F₂, ?_, ?_, ?_⟩
    · -- Faithful: `2^e` is the `F₂`-floor of `x`.
      left
      refine ⟨h_two_e_in_F₂, ?_, ?_⟩
      · rw [h_two_e_coe]; linarith
      · intro z hz hz_le
        rw [h_two_e_coe]
        exact h_F₂_le_x_to_le_2e z hz hz_le
    · -- Strictly nearest among all `F₂`-elements.
      intro z hz _
      rw [h_two_e_coe]
      rcases lt_or_ge ((2 : ℝ)^e) ((z : Dyadic) : ℝ) with h_gt | h_le
      · have h_z_ge := h_above z hz h_gt
        rw [abs_of_pos (by rw [hx_def]; linarith : (0 : ℝ) < x_val - (2 : ℝ)^e)]
        rw [abs_of_nonpos (by rw [hx_def]; linarith : x_val - (z : ℝ) ≤ 0)]
        rw [hx_def]
        linarith
      · rw [abs_of_pos (by rw [hx_def]; linarith : (0 : ℝ) < x_val - (2 : ℝ)^e)]
        rw [abs_of_nonneg (by rw [hx_def]; linarith : (0 : ℝ) ≤ x_val - (z : ℝ))]
        linarith
    · -- No tie: every other element is strictly farther.
      rintro ⟨z, hzF₂, _, hne, heq⟩
      exfalso
      rw [h_two_e_coe] at heq
      rcases lt_or_ge ((2 : ℝ)^e) ((z : Dyadic) : ℝ) with h_gt | h_le
      · have h_z_ge := h_above z hzF₂ h_gt
        rw [abs_of_pos (by rw [hx_def]; linarith : (0 : ℝ) < x_val - (2 : ℝ)^e)] at heq
        rw [abs_of_nonpos (by rw [hx_def]; linarith : x_val - (z : ℝ) ≤ 0)] at heq
        rw [hx_def] at heq
        linarith
      · have h_z_ne_2e : (z : ℝ) ≠ (2 : ℝ)^e := by
          intro h_eq
          apply hne
          rw [← Dyadic.coe_real_inj, h_two_e_coe]; exact h_eq
        have h_z_lt_2e : (z : ℝ) < (2 : ℝ)^e := lt_of_le_of_ne h_le h_z_ne_2e
        rw [abs_of_pos (by rw [hx_def]; linarith : (0 : ℝ) < x_val - (2 : ℝ)^e)] at heq
        rw [abs_of_nonneg (by rw [hx_def]; linarith : (0 : ℝ) ≤ x_val - (z : ℝ))] at heq
        linarith
  · -- RAZ in `F₁` fixes the representable `2^e`.
    refine ⟨h_two_e_in_F₁, ?_, ?_, ?_⟩
    · rfl
    · change ((two_e_g e : Dyadic) : ℝ) * ((two_e_g e : Dyadic) : ℝ) ≥ 0
      rw [h_two_e_coe]; positivity
    · intro v _ hv_bnd _
      exact hv_bnd
  · -- But the direct RAZ of `x` must reach at least `x > 2^e`.
    intro hr
    obtain ⟨_, h_bnd, _, _⟩ := hr
    rw [h_two_e_coe, abs_of_pos h_x_pos, abs_of_pos h_2e_pos] at h_bnd
    linarith

/-- **Counterexample to `rndRNE_RTZ`.** With `x = 2^e − δ` for `δ` a
quarter of `F₂`'s local step below `2^e` (`gap_below_pow`), the
intermediate RNE carries `x` *up* onto `2^e`, and RTZ then fixes it — but
the direct RTZ of `x` truncates to the `F₁`-element below (`0`). -/
theorem no_rndRNE_RTZ
    (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    (F₂ : FiniteFormat)
    (hsub : (F₁_g p hp_ge_2 e).toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ (.nearest .toEven) x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .toZero (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .toZero x w := by
  obtain ⟨f₂, hf₂_le_e, h_F₂_lt_2e_bound⟩ := gap_below_pow F₂ (E := e)
    (fun g hg => f₂_le_e_of_F₁_g_subset p hp_ge_2 e F₂.toFormat hsub hg)
  have h_two_e_in_F₁ := two_e_mem_F₁_g p hp_ge_2 e
  have h_two_e_in_F₂ : two_e_g e ∈ F₂.toFormat := hsub _ h_two_e_in_F₁
  set x_val : ℝ := (2 : ℝ)^e - (2 : ℝ)^(f₂ - 2) with hx_def
  have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
  have h_2f2_pos : (0 : ℝ) < (2 : ℝ)^(f₂ - 2) := zpow_pos (by norm_num) _
  have h_2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
  have h_2f2_lt_2e : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^e :=
    zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < e)
  have h_x_pos : 0 < x_val := by rw [hx_def]; linarith
  have h_x_lt_2e : x_val < (2 : ℝ)^e := by rw [hx_def]; linarith
  have h_two_e_coe := coe_two_e_g e
  have h_2f_split : (2 : ℝ)^f₂ = 4 * (2 : ℝ)^(f₂ - 2) := two_zpow_split_minus_two f₂
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

/-- **Counterexample to `rndRTZ_RAZ`.** With `x = 2^e + δ` for `δ` a
quarter of `F₂`'s local step above `2^e` (`gap_above_pow`), the
intermediate RTZ erases the excess above `2^e`, and RAZ then fixes `2^e` —
but the direct RAZ of `x` must reach the next `F₁`-element `2·2^e`. -/
theorem no_rndRTZ_RAZ
    (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    (F₂ : FiniteFormat)
    (hsub : (F₁_g p hp_ge_2 e).toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .toZero x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .awayZero (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .awayZero x w := by
  obtain ⟨f₂, hf₂_le_e, h_above⟩ := gap_above_pow F₂ (E := e)
    (fun g hg => f₂_le_e_of_F₁_g_subset p hp_ge_2 e F₂.toFormat hsub hg)
  have h_two_e_in_F₁ := two_e_mem_F₁_g p hp_ge_2 e
  have h_two_e_in_F₂ : two_e_g e ∈ F₂.toFormat := hsub _ h_two_e_in_F₁
  set x_val : ℝ := (2 : ℝ)^e + (2 : ℝ)^(f₂ - 2) with hx_def
  have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
  have h_2f2_pos : (0 : ℝ) < (2 : ℝ)^(f₂ - 2) := zpow_pos (by norm_num) _
  have h_2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
  have h_x_pos : 0 < x_val := by rw [hx_def]; linarith
  have h_x_gt_2e : (2 : ℝ)^e < x_val := by rw [hx_def]; linarith
  have h_two_e_coe := coe_two_e_g e
  have h_F₂_le_x_to_le_2e : ∀ z ∈ F₂.toFormat, ((z : Dyadic) : ℝ) ≤ x_val →
      ((z : Dyadic) : ℝ) ≤ (2 : ℝ)^e := by
    intro z hz hz_le
    by_contra h_gt
    push Not at h_gt
    have h_z_ge := h_above z hz h_gt
    have h_2f2_lt_2f : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^f₂ :=
      zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < f₂)
    rw [hx_def] at hz_le
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

/-- **Counterexample to `rndRAZ_RTZ`.** With `x = 2^e − δ` for `δ` a
quarter of `F₂`'s local step below `2^e` (`gap_below_pow`), the
intermediate RAZ pushes `x` *up* onto `2^e`, and RTZ then fixes it — but
the direct RTZ of `x` truncates to the `F₁`-element below (`0`). -/
theorem no_rndRAZ_RTZ
    (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    (F₂ : FiniteFormat)
    (hsub : (F₁_g p hp_ge_2 e).toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .awayZero x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .toZero (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .toZero x w := by
  obtain ⟨f₂, hf₂_le_e, h_F₂_lt_2e_bound⟩ := gap_below_pow F₂ (E := e)
    (fun g hg => f₂_le_e_of_F₁_g_subset p hp_ge_2 e F₂.toFormat hsub hg)
  have h_two_e_in_F₁ := two_e_mem_F₁_g p hp_ge_2 e
  have h_two_e_in_F₂ : two_e_g e ∈ F₂.toFormat := hsub _ h_two_e_in_F₁
  set x_val : ℝ := (2 : ℝ)^e - (2 : ℝ)^(f₂ - 2) with hx_def
  have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
  have h_2f2_pos : (0 : ℝ) < (2 : ℝ)^(f₂ - 2) := zpow_pos (by norm_num) _
  have h_2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
  have h_2f2_lt_2e : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^e :=
    zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < e)
  have h_x_pos : 0 < x_val := by rw [hx_def]; linarith
  have h_x_lt_2e : x_val < (2 : ℝ)^e := by rw [hx_def]; linarith
  have h_two_e_coe := coe_two_e_g e
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

/-- **Counterexample to `rndRAZ_RTO`.** With `x = 4·2^e − δ` for `δ` a
quarter of `F₂`'s local step below `4·2^e` (`gap_below_pow`), the
intermediate RAZ lands exactly on the *even* `F₁`-element `4·2^e`, which
RTO then fixes — but the direct RTO of `x` selects the odd neighbor
`3·2^e`. -/
theorem no_rndRAZ_RTO
    (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    (F₂ : FiniteFormat)
    (hsub : (F₁_g p hp_ge_2 e).toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .awayZero x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .toOdd (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .toOdd x w := by
  obtain ⟨f₂, hf₂_le_e2, h_F₂_lt_y_hi_bound⟩ := gap_below_pow F₂ (E := e + 2)
    (fun g hg => by
      have h := f₂_le_e_of_F₁_g_subset p hp_ge_2 e F₂.toFormat hsub hg
      omega)
  have h_y_hi_in_F₁ := y_hi_mem_F₁_g p hp_ge_2 e
  have h_y_hi_in_F₂ : y_hi_g e ∈ F₂.toFormat := hsub _ h_y_hi_in_F₁
  set x_val : ℝ := (2 : ℝ)^(e + 2) - (2 : ℝ)^(f₂ - 2) with hx_def
  have h_2e2_pos : (0 : ℝ) < (2 : ℝ)^(e + 2) := zpow_pos (by norm_num) _
  have h_2f2_pos : (0 : ℝ) < (2 : ℝ)^(f₂ - 2) := zpow_pos (by norm_num) _
  have h_2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
  have h_2f2_lt_2e2 : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^(e + 2) :=
    zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < e + 2)
  have h_x_pos : 0 < x_val := by rw [hx_def]; linarith
  have h_x_lt_y_hi : x_val < (2 : ℝ)^(e + 2) := by rw [hx_def]; linarith
  have h_y_hi_coe : ((y_hi_g e : Dyadic) : ℝ) = (2 : ℝ)^(e + 2) := coe_y_hi_g e
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

/-- **Counterexample to `rndRNE_RTO`.** With `x = 4·2^e − δ` for `δ` a
quarter of `F₂`'s local step below `4·2^e` (`gap_below_pow`), the
intermediate RNE lands exactly on the *even* `F₁`-element `4·2^e`, which
RTO then fixes — but the direct RTO of `x` selects the odd neighbor
`3·2^e`. -/
theorem no_rndRNE_RTO
    (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    (F₂ : FiniteFormat)
    (hsub : (F₁_g p hp_ge_2 e).toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ (.nearest .toEven) x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .toOdd (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .toOdd x w := by
  obtain ⟨f₂, hf₂_le_e2, h_F₂_lt_y_hi_bound⟩ := gap_below_pow F₂ (E := e + 2)
    (fun g hg => by
      have h := f₂_le_e_of_F₁_g_subset p hp_ge_2 e F₂.toFormat hsub hg
      omega)
  have h_y_hi_in_F₁ := y_hi_mem_F₁_g p hp_ge_2 e
  have h_y_hi_in_F₂ : y_hi_g e ∈ F₂.toFormat := hsub _ h_y_hi_in_F₁
  set x_val : ℝ := (2 : ℝ)^(e + 2) - (2 : ℝ)^(f₂ - 2) with hx_def
  have h_2e2_pos : (0 : ℝ) < (2 : ℝ)^(e + 2) := zpow_pos (by norm_num) _
  have h_2f2_pos : (0 : ℝ) < (2 : ℝ)^(f₂ - 2) := zpow_pos (by norm_num) _
  have h_2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
  have h_2f2_lt_2e2 : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^(e + 2) :=
    zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < e + 2)
  have h_x_pos : 0 < x_val := by rw [hx_def]; linarith
  have h_x_lt_y_hi : x_val < (2 : ℝ)^(e + 2) := by rw [hx_def]; linarith
  have h_y_hi_coe : ((y_hi_g e : Dyadic) : ℝ) = (2 : ℝ)^(e + 2) := coe_y_hi_g e
  have h_2f_split : (2 : ℝ)^f₂ = 4 * (2 : ℝ)^(f₂ - 2) := two_zpow_split_minus_two f₂
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

/-- **Counterexample to `rndRTZ_RTO`.** With `x = 4·2^e + δ` for `δ` a
quarter of `F₂`'s local step above `4·2^e` (`gap_above_pow`), the
intermediate RTZ truncates `x` onto the *even* `F₁`-element `4·2^e`, which
RTO then fixes — but the direct RTO of `x` selects the odd neighbor
`5·2^e`. -/
theorem no_rndRTZ_RTO
    (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    (F₂ : FiniteFormat)
    (hsub : (F₁_g p hp_ge_2 e).toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .toZero x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .toOdd (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat .toOdd x w := by
  obtain ⟨f₂, hf₂_le_e2, h_above⟩ := gap_above_pow F₂ (E := e + 2)
    (fun g hg => by
      have h := f₂_le_e_of_F₁_g_subset p hp_ge_2 e F₂.toFormat hsub hg
      omega)
  have h_y_hi_in_F₁ := y_hi_mem_F₁_g p hp_ge_2 e
  have h_y_hi_in_F₂ : y_hi_g e ∈ F₂.toFormat := hsub _ h_y_hi_in_F₁
  set x_val : ℝ := (2 : ℝ)^(e + 2) + (2 : ℝ)^(f₂ - 2) with hx_def
  have h_2e2_pos : (0 : ℝ) < (2 : ℝ)^(e + 2) := zpow_pos (by norm_num) _
  have h_2f2_pos : (0 : ℝ) < (2 : ℝ)^(f₂ - 2) := zpow_pos (by norm_num) _
  have h_2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
  have h_x_pos : 0 < x_val := by rw [hx_def]; linarith
  have h_x_gt_y_hi : (2 : ℝ)^(e + 2) < x_val := by rw [hx_def]; linarith
  have h_y_hi_coe : ((y_hi_g e : Dyadic) : ℝ) = (2 : ℝ)^(e + 2) := coe_y_hi_g e
  have h_F₂_le_x_to_le_y_hi : ∀ z ∈ F₂.toFormat, ((z : Dyadic) : ℝ) ≤ x_val →
      ((z : Dyadic) : ℝ) ≤ (2 : ℝ)^(e + 2) := by
    intro z hz hz_le
    by_contra h_gt
    push Not at h_gt
    have h_z_ge := h_above z hz h_gt
    have h_2f2_lt_2f : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^f₂ :=
      zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < f₂)
    rw [hx_def] at hz_le
    linarith
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
`F₁_g ⊆ F₂` — no midpoint representability. With `x = 7·2^(e−1) − δ` for
`δ` a quarter of `F₂`'s local step (`gap_around_mid`), the intermediate RAZ
either lands on the midpoint `m = 7·2^(e−1)` (when `F₂` resolves it,
manufacturing a spurious tie that RNE breaks toward the even `4·2^e`) or
lands strictly above it (crossing RNE's decision boundary undetected).
Either way the chained result is `4·2^e`, while the direct RNE of `x` is
`3·2^e`. -/
theorem no_rndRAZ_RNE
    (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    (F₂ : FiniteFormat)
    (hsub : (F₁_g p hp_ge_2 e).toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .awayZero x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat (.nearest .toEven) (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat (.nearest .toEven) x w := by
  have h_y_lo_in_F₁ := y_lo_mem_F₁_g p hp_ge_2 e
  have h_y_hi_in_F₁ := y_hi_mem_F₁_g p hp_ge_2 e
  have h_y_hi_in_F₂ : y_hi_g e ∈ F₂.toFormat := hsub _ h_y_hi_in_F₁
  obtain ⟨f₂, hf₂_le_e, h_mid_below, h_mid_above⟩ :=
    gap_around_mid F₂ (a := 7) (by norm_num) (by norm_num)
      (fun g hg => f₂_le_e_of_F₁_g_subset p hp_ge_2 e F₂.toFormat hsub hg)
      (p_ge2_of_y_lo_mem (hsub _ h_y_lo_in_F₁))
  have h_A_eq : ((7 : ℤ) : ℝ) * (2 : ℝ)^(e - 1) = (7/2) * (2 : ℝ)^e := by
    have h := two_zpow_succ (e - 1)
    rw [show e - 1 + 1 = e by ring] at h
    push_cast
    linarith
  have h_2f1_gt : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^(f₂ - 1) :=
    zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < f₂ - 1)
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
    by_contra h_lt
    push Not at h_lt
    have h := h_mid_below z hz_mem (by rw [h_A_eq]; exact h_lt)
    rw [h_A_eq] at h
    rw [hx_def] at h_z_ge_x
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
`F₁_g ⊆ F₂` — no midpoint representability. With `x = 5·2^(e−1) + δ` for
`δ` a quarter of `F₂`'s local step (`gap_around_mid`), the intermediate RTZ
either lands on the midpoint `m_low = 5·2^(e−1)` (when `F₂` resolves it,
manufacturing a spurious tie that RNE breaks toward the even `2·2^e`) or
lands strictly below it (crossing RNE's decision boundary undetected).
Either way the chained result is `2·2^e`, while the direct RNE of `x` is
`3·2^e`. -/
theorem no_rndRTZ_RNE
    (p : ℕ+) (hp_ge_2 : 2 ≤ (p : ℕ)) (e : ℤ)
    (F₂ : FiniteFormat)
    (hsub : (F₁_g p hp_ge_2 e).toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .toZero x z ∧
      RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat (.nearest .toEven) (z : ℝ) w ∧
      ¬ RoundsFinite (F₁_g p hp_ge_2 e).toFiniteFormat (.nearest .toEven) x w := by
  have h_y_lo_low_in_F₁ := y_lo_low_mem_F₁_g p hp_ge_2 e
  have h_y_lo_in_F₁ := y_lo_mem_F₁_g p hp_ge_2 e
  have h_y_lo_low_in_F₂ : y_lo_low_g e ∈ F₂.toFormat := hsub _ h_y_lo_low_in_F₁
  obtain ⟨f₂, hf₂_le_e, h_mid_below, h_mid_above⟩ :=
    gap_around_mid F₂ (a := 5) (by norm_num) (by norm_num)
      (fun g hg => f₂_le_e_of_F₁_g_subset p hp_ge_2 e F₂.toFormat hsub hg)
      (p_ge2_of_y_lo_mem (hsub _ h_y_lo_in_F₁))
  have h_A_eq : ((5 : ℤ) : ℝ) * (2 : ℝ)^(e - 1) = (5/2) * (2 : ℝ)^e := by
    have h := two_zpow_succ (e - 1)
    rw [show e - 1 + 1 = e by ring] at h
    push_cast
    linarith
  have h_2f1_gt : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^(f₂ - 1) :=
    zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < f₂ - 1)
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
    by_contra h_gt
    push Not at h_gt
    have h := h_mid_above z hz_mem (by rw [h_A_eq]; exact h_gt)
    rw [h_A_eq] at h
    rw [hx_def] at h_z_le_x
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
