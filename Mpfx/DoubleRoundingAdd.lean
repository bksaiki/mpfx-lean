import Mpfx.NearestMidpoint
import Mpfx.DoubleRoundingOps

/-!
# Operation-specific double rounding: addition (Roux 2014, §3)

Phase 3 of `docs/agents/DOUBLE_ROUNDING_OPS_PLAN.md`. Roux's Theorem 20 (radix 2,
FLX): double rounding of addition is innocuous when `p₂ ≥ 2p₁ + 1`. The proof
splits on the exponent gap between the operands:

* **Case 1** (`ln y ≥ φ₁(ln x) − 1`, operands within `p₁+1` binades): `x + y`
  fits in `2p₁ + 1` significand bits, so it is *exactly* representable in `F₂`
  and the intermediate rounding is a no-op.
* **Case 2** (`ln y ≤ φ₁(ln x) − 2`, `y` tiny): `x + y` sits just above its
  `F₁` round-down, well below the midpoint, so `rnd_lt_mid'` (Lemma 16) applies.

`rndAdd_pos` proves the result for `0 < y ≤ x` (Roux's core case); `rndAdd`
lifts it to **all same-sign operands** (`0 ≤ x·y`, any ordering) by swapping
(`add_comm`), handling zeros exactly, and joint negation for the
both-nonpositive case. Mixed signs (`x·y < 0`) are *subtraction*, a separate
result (Roux §3.1) not covered here.
-/

namespace Mpfx

/-- **Canonical grid representation.** A positive `y ∈ F` (precision `p`) is
`c · 2^(canonicalExp y)` with `|c| < 2^p`. Unifies the `exp = ⊥` and finite-`exp`
grid lemmas (both have grid step `= canonicalExp`). -/
theorem exists_canonical_rep (F : FiniteFormat) {p : ℕ+}
    (hp : F.p = ((p : ℕ+) : WithTop ℕ+))
    {y : Dyadic} (hmem : y ∈ F) (hpos : 0 < (y : ℝ)) :
    ∃ c : ℤ, |c| < (2 : ℤ) ^ (p : ℕ) ∧
      (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ (F.canonicalExp (y : ℝ)) := by
  have hy_ne : (y : ℝ) ≠ 0 := ne_of_gt hpos
  obtain ⟨hprec, hquant, _⟩ := hmem
  cases hexp : F.exp with
  | bot =>
    obtain ⟨k, c, hc, hyeq, hk⟩ := exists_grid_rep_exp_bot F hp hprec hpos
    have hcexp : F.canonicalExp (y : ℝ) = Int.log 2 (y : ℝ) + 1 - (p : ℤ) := by
      unfold FiniteFormat.canonicalExp
      simp only [hp, hexp, hy_ne, abs_of_pos hpos, if_false]
    have hkexp : k = F.canonicalExp (y : ℝ) := by rw [hcexp, hk]; omega
    exact ⟨c, hc, by rw [← hkexp]; exact hyeq⟩
  | coe e =>
    obtain ⟨k, c, _, hc, hyeq, hk⟩ :=
      exists_grid_rep F hp hexp hprec (hexp ▸ hquant) hpos
    have hcexp : F.canonicalExp (y : ℝ)
        = max (Int.log 2 (y : ℝ) + 1 - (p : ℤ)) e := by
      unfold FiniteFormat.canonicalExp
      simp only [hp, hexp, hy_ne, abs_of_pos hpos, if_false]
    have hkexp : k = F.canonicalExp (y : ℝ) := by rw [hcexp, hk]; omega
    exact ⟨c, hc, by rw [← hkexp]; exact hyeq⟩

/-- `canonicalExp` is monotone in magnitude. -/
theorem canonicalExp_mono (F : FiniteFormat) {y z : ℝ} (hy : y ≠ 0)
    (hyz : |y| ≤ |z|) : F.canonicalExp y ≤ F.canonicalExp z := by
  have hy_pos : 0 < |y| := abs_pos.mpr hy
  have hz : z ≠ 0 := by
    rintro rfl; rw [abs_zero] at hyz; exact absurd hyz (not_le.mpr hy_pos)
  have hlog : Int.log 2 |y| ≤ Int.log 2 |z| := Int.log_mono_right hy_pos hyz
  unfold FiniteFormat.canonicalExp
  cases F.p with
  | top => cases F.exp <;> simp
  | coe p =>
    cases F.exp with
    | bot => simp only [hy, hz, if_false]; omega
    | coe e => simp only [hy, hz, if_false]; omega

/-- Sign/positivity extractor: from `(x:ℝ) = c·2^e > 0` with `2^e > 0`, get `c > 0`. -/
private theorem mantissa_pos {c e : ℤ} {x : ℝ} (hxeq : x = (c : ℝ) * (2 : ℝ) ^ e)
    (hpos : 0 < x) : 0 < c := by
  have h2e : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have h : (0 : ℝ) < (c : ℝ) * (2 : ℝ) ^ e := hxeq ▸ hpos
  rcases mul_pos_iff.mp h with ⟨hc, _⟩ | ⟨_, hng⟩
  · exact_mod_cast hc
  · linarith

/-- **Case 1 precision bound** (Roux Theorem 20, the exact-intermediate case).
For `x, y ∈ F₁` with `0 < y ≤ x` and canonical-exponent gap `≤ p₁ + 1`, the sum
`x + y` fits in `2p₁ + 1` significand bits at quantum `canonicalExp y` — hence is
representable in any `F₂` with `p₂ ≥ 2p₁+1` and fine enough quantum. -/
theorem sum_precisionAtMost {F₁ : FiniteFormat} {p₁ : ℕ+}
    (hp₁ : F₁.p = ((p₁ : ℕ+) : WithTop ℕ+))
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁)
    (hxpos : 0 < (x : ℝ)) (hypos : 0 < (y : ℝ)) (hyx : (y : ℝ) ≤ (x : ℝ))
    (hgap : F₁.canonicalExp (x : ℝ) - F₁.canonicalExp (y : ℝ) ≤ (p₁ : ℤ) + 1) :
    Dyadic.precisionAtMost ((2 * p₁ + 1 : ℕ+) : WithTop ℕ+) (x + y) ∧
      Dyadic.quantumAtLeast ((F₁.canonicalExp (y : ℝ) : ℤ) : WithBot ℤ) (x + y) := by
  set ex := F₁.canonicalExp (x : ℝ) with hex
  set ey := F₁.canonicalExp (y : ℝ) with hey
  obtain ⟨cx, hcx_lt, hxeq⟩ := exists_canonical_rep F₁ hp₁ hx hxpos
  obtain ⟨cy, hcy_lt, hyeq⟩ := exists_canonical_rep F₁ hp₁ hy hypos
  rw [← hex] at hxeq; rw [← hey] at hyeq
  have hcx_pos : 0 < cx := mantissa_pos hxeq hxpos
  have hcy_pos : 0 < cy := mantissa_pos hyeq hypos
  -- ey ≤ ex
  have hey_le_ex : ey ≤ ex := by
    rw [hey, hex]
    exact canonicalExp_mono F₁ (ne_of_gt hypos)
      (by rw [abs_of_pos hypos, abs_of_pos hxpos]; exact hyx)
  set n : ℕ := (ex - ey).toNat with hn
  have hn_nat : n ≤ (p₁ : ℕ) + 1 := by
    have : (n : ℤ) = ex - ey := by rw [hn, Int.toNat_of_nonneg (by omega)]
    omega
  set C : ℤ := cx * (2 : ℤ) ^ n + cy with hC
  -- real equation `x + y = C · 2^ey`
  have hsplit : (2 : ℝ) ^ ex = (2 : ℝ) ^ n * (2 : ℝ) ^ ey := by
    rw [hn]; exact two_zpow_split_toNat hey_le_ex
  have hxy_eq : ((x + y : Dyadic) : ℝ) = (C : ℝ) * (2 : ℝ) ^ ey := by
    rw [Dyadic.coe_real_add, hxeq, hyeq, hsplit, hC]; push_cast; ring
  -- integer bound `|C| < 2^(2p₁+1)`
  set A : ℤ := (2 : ℤ) ^ (p₁ : ℕ) with hA
  have hAge : (2 : ℤ) ≤ A := by
    rw [hA]; calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (p₁ : ℕ) := pow_le_pow_right₀ (by norm_num) p₁.one_le
  have hcx_le : cx ≤ A - 1 := by rw [abs_of_pos hcx_pos] at hcx_lt; omega
  have hcy_le : cy ≤ A - 1 := by rw [abs_of_pos hcy_pos] at hcy_lt; omega
  have h2n_le : (2 : ℤ) ^ n ≤ 2 * A := by
    calc (2 : ℤ) ^ n ≤ (2 : ℤ) ^ ((p₁ : ℕ) + 1) := pow_le_pow_right₀ (by norm_num) hn_nat
      _ = 2 * A := by rw [hA, pow_succ]; ring
  have h2A2 : (2 : ℤ) ^ (2 * (p₁ : ℕ) + 1) = 2 * A * A := by
    rw [hA, show 2 * (p₁ : ℕ) + 1 = (p₁ : ℕ) + ((p₁ : ℕ) + 1) from by ring, pow_add, pow_succ]
    ring
  have hC_pos : 0 < C := by
    rw [hC]; have h1 : 0 < cx * (2 : ℤ) ^ n := mul_pos hcx_pos (by positivity); omega
  have hC_lt : C < (2 : ℤ) ^ (2 * (p₁ : ℕ) + 1) := by
    rw [h2A2, hC]
    have hprod : cx * (2 : ℤ) ^ n ≤ (A - 1) * (2 * A) :=
      mul_le_mul hcx_le h2n_le (by positivity) (by omega)
    nlinarith [hprod, hcy_le, hAge]
  have hpcast : ((2 * p₁ + 1 : ℕ+) : ℕ) = 2 * (p₁ : ℕ) + 1 := by push_cast; ring
  refine ⟨?_, ?_⟩
  · rw [Dyadic.precisionAtMost_coe_real]
    exact ⟨C, ey, hxy_eq, by rw [hpcast, abs_of_pos hC_pos]; exact hC_lt⟩
  · rw [Dyadic.quantumAtLeast_coe_real]
    exact ⟨C, hxy_eq⟩

/-- **rnd-plus, positive ordered case** (Roux Theorem 20, radix 2, FLX). For
`x, y ∈ F₁` with `0 < y ≤ x`, if `p₂ ≥ 2p₁ + 1` then double rounding of `x + y`
is innocuous. Split on the operand exponent gap: Case 1 (gap `≤ p₁+1`) makes
`x+y` exactly `F₂`-representable; Case 2 (gap `≥ p₂+2`, tiny `y`) keeps `x+y`
in `x`'s binade, well below the midpoint, so `rnd_lt_mid'` applies. -/
theorem rndAdd_pos {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ+}
    (hp₁ : F₁.p = ((p₁ : ℕ+) : WithTop ℕ+)) (hexp₁ : F₁.exp = ⊥)
    (hp₂ : F₂.p = ((p₂ : ℕ+) : WithTop ℕ+)) (hexp₂ : F₂.exp = ⊥)
    (hpp : (2 * p₁ + 1 : ℕ+) ≤ p₂)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁)
    (hxpos : 0 < (x : ℝ)) (hypos : 0 < (y : ℝ)) (hyx : (y : ℝ) ≤ (x : ℝ))
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((x + y : Dyadic) : ℝ) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((x + y : Dyadic) : ℝ) w := by
  have hxypos : 0 < ((x + y : Dyadic) : ℝ) := by rw [Dyadic.coe_real_add]; linarith
  set ex := F₁.canonicalExp (x : ℝ) with hex
  set ey := F₁.canonicalExp (y : ℝ) with hey
  have hp₁ℤ : (1 : ℤ) ≤ (p₁ : ℤ) := by exact_mod_cast p₁.one_le
  have hpp' : (2 * (p₁ : ℤ) + 1) ≤ (p₂ : ℤ) := by
    have : ((2 * p₁ + 1 : ℕ+) : ℤ) ≤ ((p₂ : ℕ+) : ℤ) := by exact_mod_cast hpp
    push_cast at this; omega
  by_cases hgap : ex - ey ≤ (p₁ : ℤ) + 1
  · -- Case 1: `x + y` is exactly representable in `F₂`.
    obtain ⟨hprec, hquant⟩ := sum_precisionAtMost hp₁ hx hy hxpos hypos hyx hgap
    have hmem : (x + y) ∈ F₂.unbounded := by
      refine ⟨?_, ?_, trivial⟩
      · refine Dyadic.precisionAtMost_mono ?_ hprec
        rw [FiniteFormat.unbounded_p, hp₂]; exact_mod_cast hpp
      · rw [FiniteFormat.unbounded_exp, hexp₂]; trivial
    exact rndExact (F₂ := F₂.unbounded) hmem hz hw
  · -- Case 2: `y` tiny, `x + y` below the midpoint.
    push Not at hgap  -- `(p₁ : ℤ) + 1 < ex - ey`
    obtain ⟨cx, hcx_lt, hxeq⟩ := exists_canonical_rep F₁ hp₁ hx hxpos
    obtain ⟨cy, hcy_lt, hyeq⟩ := exists_canonical_rep F₁ hp₁ hy hypos
    rw [← hex] at hxeq; rw [← hey] at hyeq
    have hcx_pos : 0 < cx := mantissa_pos hxeq hxpos
    have hcy_pos : 0 < cy := mantissa_pos hyeq hypos
    -- `Int.log 2 x = ex + p₁ - 1`
    have hex_val : ex = Int.log 2 (x : ℝ) + 1 - (p₁ : ℤ) := by
      rw [hex]; unfold FiniteFormat.canonicalExp
      simp only [hp₁, hexp₁, ne_of_gt hxpos, abs_of_pos hxpos, if_false]
    have hlogx : Int.log 2 (x : ℝ) = ex + (p₁ : ℤ) - 1 := by omega
    -- binade bounds on `x`
    have hx_lo : (2 : ℝ) ^ (ex + (p₁ : ℤ) - 1) ≤ (x : ℝ) := by
      have := Int.zpow_log_le_self (b := 2) (by norm_num) hxpos
      rw [hlogx] at this; exact_mod_cast this
    have hx_hi : (x : ℝ) < (2 : ℝ) ^ (ex + (p₁ : ℤ)) := by
      have := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) (x : ℝ)
      rw [hlogx] at this
      have h : (x : ℝ) < (2 : ℝ) ^ (ex + (p₁ : ℤ) - 1 + 1) := by exact_mod_cast this
      rwa [show ex + (p₁ : ℤ) - 1 + 1 = ex + (p₁ : ℤ) from by ring] at h
    -- `cx ≤ 2^p₁ - 1`, so `x ≤ 2^(ex+p₁) - 2^ex`
    have hcx_le : (cx : ℝ) ≤ (2 : ℝ) ^ (p₁ : ℕ) - 1 := by
      rw [abs_of_pos hcx_pos] at hcx_lt
      have : (cx : ℝ) < (2 : ℝ) ^ (p₁ : ℕ) := by exact_mod_cast hcx_lt
      have hcxi : cx ≤ (2 : ℤ) ^ (p₁ : ℕ) - 1 := by omega
      have : (cx : ℝ) ≤ ((2 : ℤ) ^ (p₁ : ℕ) - 1 : ℤ) := by exact_mod_cast hcxi
      push_cast at this; exact this
    have h2p1 : ((2 : ℝ) ^ (p₁ : ℕ)) = (2 : ℝ) ^ (p₁ : ℤ) := by
      rw [← zpow_natCast]
    have hx_le : (x : ℝ) ≤ (2 : ℝ) ^ (ex + (p₁ : ℤ)) - (2 : ℝ) ^ ex := by
      rw [hxeq]
      have hsplit : (2 : ℝ) ^ (ex + (p₁ : ℤ)) = (2 : ℝ) ^ (p₁ : ℤ) * (2 : ℝ) ^ ex := by
        rw [show ex + (p₁ : ℤ) = (p₁ : ℤ) + ex from by ring,
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      have h2ex : (0 : ℝ) < (2 : ℝ) ^ ex := zpow_pos (by norm_num) _
      rw [hsplit, ← h2p1]
      nlinarith [hcx_le, h2ex]
    -- `y < 2^(ex-2)`
    have hy_lt : (y : ℝ) < (2 : ℝ) ^ (ex - 2) := by
      have hcy_ltR : (cy : ℝ) < (2 : ℝ) ^ (p₁ : ℤ) := by
        rw [abs_of_pos hcy_pos] at hcy_lt
        rw [← h2p1]; exact_mod_cast hcy_lt
      have h2ey : (0 : ℝ) < (2 : ℝ) ^ ey := zpow_pos (by norm_num) _
      have h1 : (y : ℝ) < (2 : ℝ) ^ (p₁ : ℤ) * (2 : ℝ) ^ ey := by
        rw [hyeq]; exact mul_lt_mul_of_pos_right hcy_ltR h2ey
      calc (y : ℝ) < (2 : ℝ) ^ (p₁ : ℤ) * (2 : ℝ) ^ ey := h1
        _ = (2 : ℝ) ^ ((p₁ : ℤ) + ey) := by rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        _ ≤ (2 : ℝ) ^ (ex - 2) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    -- `x + y` is in `x`'s binade: `2^(ex+p₁-1) ≤ x+y < 2^(ex+p₁)`
    have h2ex : (0 : ℝ) < (2 : ℝ) ^ ex := zpow_pos (by norm_num) _
    have hxy_lo : (2 : ℝ) ^ (ex + (p₁ : ℤ) - 1) ≤ ((x + y : Dyadic) : ℝ) := by
      rw [Dyadic.coe_real_add]; linarith
    have h2ex2_lt : (2 : ℝ) ^ (ex - 2) < (2 : ℝ) ^ ex :=
      zpow_lt_zpow_right₀ (by norm_num) (by omega)
    have hxy_hi : ((x + y : Dyadic) : ℝ) < (2 : ℝ) ^ (ex + (p₁ : ℤ)) := by
      rw [Dyadic.coe_real_add]; linarith [hx_le, hy_lt, h2ex2_lt]
    have hlogxy : Int.log 2 ((x + y : Dyadic) : ℝ) = ex + (p₁ : ℤ) - 1 := by
      have h1 : ex + (p₁ : ℤ) - 1 ≤ Int.log 2 ((x + y : Dyadic) : ℝ) :=
        (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hxypos).mp (by exact_mod_cast hxy_lo)
      have h2 : Int.log 2 ((x + y : Dyadic) : ℝ) < ex + (p₁ : ℤ) :=
        (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hxypos).mp (by exact_mod_cast hxy_hi)
      omega
    -- canonicalExp of `x+y` in `F₁` and `F₂`
    have hcexp₁xy : F₁.canonicalExp ((x + y : Dyadic) : ℝ) = ex := by
      rw [hex]
      exact canonicalExp_eq_of_log_eq F₁ (ne_of_gt hxypos) (ne_of_gt hxpos)
        (by rw [abs_of_pos hxypos, abs_of_pos hxpos, hlogxy, hlogx])
    have hcexp₂xy : F₂.canonicalExp ((x + y : Dyadic) : ℝ) = ex + (p₁ : ℤ) - (p₂ : ℤ) := by
      unfold FiniteFormat.canonicalExp
      simp only [hp₂, hexp₂, ne_of_gt hxypos, abs_of_pos hxypos, if_false, hlogxy]
      ring
    -- rndDown F₁ (x+y) has real value x
    have hrdxy : (rndDown F₁ ((x + y : Dyadic) : ℝ) : ℝ) = (x : ℝ) := by
      rw [rndDown_eq, Dyadic.coe_ofIntZpow, hcexp₁xy]
      have h2negex : (0 : ℝ) < (2 : ℝ) ^ (-ex) := zpow_pos (by norm_num) _
      have hxscaled : ((cx : ℝ) * (2 : ℝ) ^ ex) * (2 : ℝ) ^ (-ex) = (cx : ℝ) := by
        rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; simp
      have hyscaled : (y : ℝ) * (2 : ℝ) ^ (-ex) < 1 := by
        have heq : (2 : ℝ) ^ (ex - 2) * (2 : ℝ) ^ (-ex) = (2 : ℝ) ^ (-2 : ℤ) := by
          rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
        have h14 : (2 : ℝ) ^ (-2 : ℤ) < 1 := by norm_num
        nlinarith [mul_lt_mul_of_pos_right hy_lt h2negex, heq, h14]
      have hfloor : ⌊((x + y : Dyadic) : ℝ) * (2 : ℝ) ^ (-ex)⌋ = cx := by
        rw [Int.floor_eq_iff]
        refine ⟨?_, ?_⟩
        · rw [Dyadic.coe_real_add, hxeq]
          nlinarith [hxscaled, mul_nonneg (le_of_lt hypos) (le_of_lt h2negex)]
        · rw [Dyadic.coe_real_add, hxeq]
          nlinarith [hyscaled, hxscaled]
      rw [hfloor, hxeq]
    -- assemble the `rnd_lt_mid'` hypotheses
    apply rnd_lt_mid' hundef₁ hxypos ?_ ?_ ?_ hz hw
    · rw [hcexp₁xy, hcexp₂xy]; omega
    · rw [hcexp₁xy, hlogxy]; omega
    · -- x+y < midp F₁ (x+y) - ulp F₂ (x+y) / 2
      have hmidp : midp F₁ ((x + y : Dyadic) : ℝ) = (x : ℝ) + (2 : ℝ) ^ ex / 2 := by
        unfold midp ulp; rw [hrdxy, hcexp₁xy]
      have hulp₂ : ulp F₂ ((x + y : Dyadic) : ℝ) = (2 : ℝ) ^ (ex + (p₁ : ℤ) - (p₂ : ℤ)) := by
        unfold ulp; rw [hcexp₂xy]
      rw [hmidp, hulp₂, Dyadic.coe_real_add]
      -- y < 2^ex/2 - 2^(ex+p₁-p₂)/2
      have hu2_le : (2 : ℝ) ^ (ex + (p₁ : ℤ) - (p₂ : ℤ)) ≤ (2 : ℝ) ^ (ex - 2) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have h2ex2 : (2 : ℝ) ^ (ex - 2) = (2 : ℝ) ^ ex / 4 := by
        rw [show ex - 2 = ex + (-2 : ℤ) from by ring, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0),
            show (2 : ℝ) ^ (-2 : ℤ) = 1 / 4 from by norm_num]
        ring
      linarith [hy_lt, hu2_le, h2ex2, h2ex]

/-- A member of `F₁` (precision `p₁`) is in `F₂.unbounded` when `p₁ ≤ p₂` and
`F₂.exp = ⊥` (quantum unconstrained). -/
private theorem mem_F₂_unbounded {F₁ F₂ : FiniteFormat} {p₁ p₂ : ℕ+}
    (hp₁ : F₁.p = ((p₁ : ℕ+) : WithTop ℕ+)) (hp₂ : F₂.p = ((p₂ : ℕ+) : WithTop ℕ+))
    (hexp₂ : F₂.exp = ⊥) (hp1p2 : p₁ ≤ p₂)
    {d : Dyadic} (hd : d ∈ F₁) : d ∈ F₂.unbounded := by
  refine ⟨?_, ?_, trivial⟩
  · refine Dyadic.precisionAtMost_mono ?_ (hp₁ ▸ hd.1)
    rw [FiniteFormat.unbounded_p, hp₂]; exact_mod_cast hp1p2
  · rw [FiniteFormat.unbounded_exp, hexp₂]; trivial

/-- Nearest rounding is invariant under joint negation (both tie-breaks). -/
private theorem RoundsFinite.neg_nearest (F : FiniteFormat) (tb : TieBreak) (a : ℝ)
    (v : Dyadic) :
    RoundsFinite F (.nearest tb) a v ↔ RoundsFinite F (.nearest tb) (-a) (-v) := by
  cases tb with
  | toEven => exact RoundsFinite.neg_nearest_toEven F a v
  | awayZero => exact RoundsFinite.neg_nearest_awayZero F a v

/-- Both operands nonnegative: reduce to `rndAdd_pos` (swap if `x < y`; a zero
operand makes the sum exactly representable). -/
theorem rndAdd_nonneg {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ+}
    (hp₁ : F₁.p = ((p₁ : ℕ+) : WithTop ℕ+)) (hexp₁ : F₁.exp = ⊥)
    (hp₂ : F₂.p = ((p₂ : ℕ+) : WithTop ℕ+)) (hexp₂ : F₂.exp = ⊥)
    (hpp : (2 * p₁ + 1 : ℕ+) ≤ p₂)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁)
    (hxnn : 0 ≤ (x : ℝ)) (hynn : 0 ≤ (y : ℝ))
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((x + y : Dyadic) : ℝ) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((x + y : Dyadic) : ℝ) w := by
  have hp1p2 : (p₁ : ℕ+) ≤ p₂ := by
    have h : 2 * (p₁ : ℕ) + 1 ≤ (p₂ : ℕ) := by exact_mod_cast hpp
    exact_mod_cast (by omega : (p₁ : ℕ) ≤ (p₂ : ℕ))
  rcases eq_or_lt_of_le hxnn with hx0 | hxp
  · -- x = 0
    have hxd : x = 0 :=
      (Dyadic.coe_real_inj x 0).mp (by rw [Dyadic.coe_real_zero]; exact hx0.symm)
    rw [hxd, zero_add] at hz ⊢
    exact rndExact (mem_F₂_unbounded hp₁ hp₂ hexp₂ hp1p2 hy) hz hw
  · rcases eq_or_lt_of_le hynn with hy0 | hyp
    · -- y = 0
      have hyd : y = 0 :=
        (Dyadic.coe_real_inj y 0).mp (by rw [Dyadic.coe_real_zero]; exact hy0.symm)
      rw [hyd, add_zero] at hz ⊢
      exact rndExact (mem_F₂_unbounded hp₁ hp₂ hexp₂ hp1p2 hx) hz hw
    · rcases le_total (y : ℝ) (x : ℝ) with hyx | hxy
      · exact rndAdd_pos hp₁ hexp₁ hp₂ hexp₂ hpp hundef₁ hx hy hxp hyp hyx hz hw
      · rw [show (x + y : Dyadic) = y + x from add_comm x y] at hz ⊢
        exact rndAdd_pos hp₁ hexp₁ hp₂ hexp₂ hpp hundef₁ hy hx hyp hxp hxy hz hw

/-- **rnd-plus, same-sign operands** (Roux Theorem 20, radix 2, FLX). For
`x, y ∈ F₁` of the same sign (`0 ≤ x·y`), if `p₂ ≥ 2p₁+1` then double rounding
of `x + y` is innocuous. The both-nonpositive case reduces to `rndAdd_nonneg`
by joint negation. (Mixed signs = subtraction, handled separately.) -/
theorem rndAdd {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ+}
    (hp₁ : F₁.p = ((p₁ : ℕ+) : WithTop ℕ+)) (hexp₁ : F₁.exp = ⊥)
    (hp₂ : F₂.p = ((p₂ : ℕ+) : WithTop ℕ+)) (hexp₂ : F₂.exp = ⊥)
    (hpp : (2 * p₁ + 1 : ℕ+) ≤ p₂)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁)
    (hsign : 0 ≤ (x : ℝ) * (y : ℝ))
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((x + y : Dyadic) : ℝ) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((x + y : Dyadic) : ℝ) w := by
  have hp1p2 : (p₁ : ℕ+) ≤ p₂ := by
    have h : 2 * (p₁ : ℕ) + 1 ≤ (p₂ : ℕ) := by exact_mod_cast hpp
    exact_mod_cast (by omega : (p₁ : ℕ) ≤ (p₂ : ℕ))
  -- a zero operand makes `x + y` exactly representable
  have exact_of_zero : ∀ {u v : Dyadic}, u ∈ F₁ → v ∈ F₁ → (u : ℝ) = 0 →
      RoundsFinite F₂.unbounded (.nearest tb₂) ((u + v : Dyadic) : ℝ) z →
      RoundsFinite F₁.unbounded (.nearest tb₁) ((u + v : Dyadic) : ℝ) w := by
    intro u v hu hv hu0 hzuv
    have hud : u = 0 := (Dyadic.coe_real_inj u 0).mp (by rw [Dyadic.coe_real_zero]; exact hu0)
    rw [hud, zero_add] at hzuv ⊢
    exact rndExact (mem_F₂_unbounded hp₁ hp₂ hexp₂ hp1p2 hv) hzuv hw
  rcases (lt_or_ge (x : ℝ) 0).symm with hxnn | hxneg
  · rcases (lt_or_ge (y : ℝ) 0).symm with hynn | hyneg
    · exact rndAdd_nonneg hp₁ hexp₁ hp₂ hexp₂ hpp hundef₁ hx hy hxnn hynn hz hw
    · -- x ≥ 0, y < 0, x·y ≥ 0 ⟹ x = 0
      exact exact_of_zero hx hy (le_antisymm (by nlinarith [hsign, hyneg]) hxnn) hz
  · rcases (lt_or_ge 0 (y : ℝ)).symm with hynp | hyp
    · -- both ≤ 0: joint negation reduces to `rndAdd_nonneg`
      have hnx : (-x) ∈ F₁ := FiniteFormat.neg_mem hx
      have hny : (-y) ∈ F₁ := FiniteFormat.neg_mem hy
      have hnxnn : 0 ≤ ((-x : Dyadic) : ℝ) := by rw [Dyadic.coe_real_neg]; linarith
      have hnynn : 0 ≤ ((-y : Dyadic) : ℝ) := by rw [Dyadic.coe_real_neg]; linarith
      have hsum_eq : ((-x) + (-y) : Dyadic) = -(x + y) := (neg_add x y).symm
      have hz' : RoundsFinite F₂.unbounded (.nearest tb₂) (((-x) + (-y) : Dyadic) : ℝ) (-z) := by
        rw [hsum_eq, Dyadic.coe_real_neg]
        exact (RoundsFinite.neg_nearest F₂.unbounded tb₂ _ z).mp hz
      have hw' : RoundsFinite F₁.unbounded (.nearest tb₁) ((-z : Dyadic) : ℝ) (-w) := by
        rw [Dyadic.coe_real_neg]
        exact (RoundsFinite.neg_nearest F₁.unbounded tb₁ _ w).mp hw
      have hresult := rndAdd_nonneg hp₁ hexp₁ hp₂ hexp₂ hpp hundef₁ hnx hny hnxnn hnynn hz' hw'
      rw [hsum_eq, Dyadic.coe_real_neg] at hresult
      exact (RoundsFinite.neg_nearest F₁.unbounded tb₁ ((x + y : Dyadic) : ℝ) w).mpr hresult
    · -- x < 0, y > 0 ⟹ x·y < 0, contradicting `hsign`
      exact absurd hsign (by nlinarith [mul_neg_of_neg_of_pos hxneg hyp])

end Mpfx
