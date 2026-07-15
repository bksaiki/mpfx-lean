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

/-- Closed form of `canonicalExp` in an FLX format (`exp = ⊥`): `log₂|v| + 1 − p`. -/
theorem canonicalExp_FLX {F : FiniteFormat} {p : ℕ+}
    (hp : F.p = ((p : ℕ+) : WithTop ℕ+)) (hexp : F.exp = ⊥)
    {v : ℝ} (hv : v ≠ 0) : F.canonicalExp v = Int.log 2 |v| + 1 - (p : ℤ) := by
  unfold FiniteFormat.canonicalExp; simp only [hp, hexp, hv, if_false]

/-- In two FLX formats with `p₁ < p₂`, the wider format's canonical exponent at
any nonzero `v` is strictly smaller (no binade computation needed). -/
theorem canonicalExp_lt_of_prec_lt {F₁ F₂ : FiniteFormat} {p₁ p₂ : ℕ+}
    (hp₁ : F₁.p = ((p₁ : ℕ+) : WithTop ℕ+)) (hexp₁ : F₁.exp = ⊥)
    (hp₂ : F₂.p = ((p₂ : ℕ+) : WithTop ℕ+)) (hexp₂ : F₂.exp = ⊥)
    (hpp : (p₁ : ℤ) < (p₂ : ℤ)) {v : ℝ} (hv : v ≠ 0) :
    F₂.canonicalExp v < F₁.canonicalExp v := by
  unfold FiniteFormat.canonicalExp
  simp only [hp₁, hexp₁, hp₂, hexp₂, hv, if_false]
  omega

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

/-- **Case 1 precision bound for subtraction.** For `x, y ∈ F₁` with `0 < y ≤ x`
and canonical-exponent gap `≤ p₁ + 1`, the difference `x − y` fits in `2p₁ + 1`
significand bits at quantum `canonicalExp y`. Mirror of `sum_precisionAtMost`. -/
theorem diff_precisionAtMost {F₁ : FiniteFormat} {p₁ : ℕ+}
    (hp₁ : F₁.p = ((p₁ : ℕ+) : WithTop ℕ+))
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁)
    (hxpos : 0 < (x : ℝ)) (hypos : 0 < (y : ℝ)) (hyx : (y : ℝ) ≤ (x : ℝ))
    (hgap : F₁.canonicalExp (x : ℝ) - F₁.canonicalExp (y : ℝ) ≤ (p₁ : ℤ) + 1) :
    Dyadic.precisionAtMost ((2 * p₁ + 1 : ℕ+) : WithTop ℕ+) (x - y) ∧
      Dyadic.quantumAtLeast ((F₁.canonicalExp (y : ℝ) : ℤ) : WithBot ℤ) (x - y) := by
  set ex := F₁.canonicalExp (x : ℝ) with hex
  set ey := F₁.canonicalExp (y : ℝ) with hey
  obtain ⟨cx, hcx_lt, hxeq⟩ := exists_canonical_rep F₁ hp₁ hx hxpos
  obtain ⟨cy, hcy_lt, hyeq⟩ := exists_canonical_rep F₁ hp₁ hy hypos
  rw [← hex] at hxeq; rw [← hey] at hyeq
  have hcx_pos : 0 < cx := mantissa_pos hxeq hxpos
  have hcy_pos : 0 < cy := mantissa_pos hyeq hypos
  have hey_le_ex : ey ≤ ex := by
    rw [hey, hex]; exact canonicalExp_mono F₁ (ne_of_gt hypos)
      (by rw [abs_of_pos hypos, abs_of_pos hxpos]; exact hyx)
  set n : ℕ := (ex - ey).toNat with hn
  have hn_nat : n ≤ (p₁ : ℕ) + 1 := by
    have : (n : ℤ) = ex - ey := by rw [hn, Int.toNat_of_nonneg (by omega)]
    omega
  set C : ℤ := cx * (2 : ℤ) ^ n - cy with hC
  have hsplit : (2 : ℝ) ^ ex = (2 : ℝ) ^ n * (2 : ℝ) ^ ey := by
    rw [hn]; exact two_zpow_split_toNat hey_le_ex
  have hxy_eq : ((x - y : Dyadic) : ℝ) = (C : ℝ) * (2 : ℝ) ^ ey := by
    have hsub : ((x - y : Dyadic) : ℝ) = (x : ℝ) - (y : ℝ) := by push_cast; ring
    rw [hsub, hxeq, hyeq, hsplit, hC]; push_cast; ring
  set A : ℤ := (2 : ℤ) ^ (p₁ : ℕ) with hA
  have hAge : (2 : ℤ) ≤ A := by
    rw [hA]; calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (p₁ : ℕ) := pow_le_pow_right₀ (by norm_num) p₁.one_le
  have hcx_le : cx ≤ A - 1 := by rw [abs_of_pos hcx_pos] at hcx_lt; omega
  have hcy_le : cy ≤ A - 1 := by rw [abs_of_pos hcy_pos] at hcy_lt; omega
  have h2n_pos : (0 : ℤ) < (2 : ℤ) ^ n := by positivity
  have h2n_le : (2 : ℤ) ^ n ≤ 2 * A := by
    calc (2 : ℤ) ^ n ≤ (2 : ℤ) ^ ((p₁ : ℕ) + 1) := pow_le_pow_right₀ (by norm_num) hn_nat
      _ = 2 * A := by rw [hA, pow_succ]; ring
  have h2A2 : (2 : ℤ) ^ (2 * (p₁ : ℕ) + 1) = 2 * A * A := by
    rw [hA, show 2 * (p₁ : ℕ) + 1 = (p₁ : ℕ) + ((p₁ : ℕ) + 1) from by ring, pow_add, pow_succ]
    ring
  have hprod : cx * (2 : ℤ) ^ n ≤ (A - 1) * (2 * A) :=
    mul_le_mul hcx_le h2n_le (le_of_lt h2n_pos) (by omega)
  have hcxn_pos : 0 < cx * (2 : ℤ) ^ n := mul_pos hcx_pos h2n_pos
  have habsC : |C| < (2 : ℤ) ^ (2 * (p₁ : ℕ) + 1) := by
    rw [h2A2, hC, abs_lt]
    exact ⟨by nlinarith [hcxn_pos, hcy_le, hAge], by nlinarith [hprod, hcy_pos, hAge]⟩
  have hpcast : ((2 * p₁ + 1 : ℕ+) : ℕ) = 2 * (p₁ : ℕ) + 1 := by push_cast; ring
  refine ⟨?_, ?_⟩
  · rw [Dyadic.precisionAtMost_coe_real]
    exact ⟨C, ey, hxy_eq, by rw [hpcast]; exact habsC⟩
  · rw [Dyadic.quantumAtLeast_coe_real]
    exact ⟨C, hxy_eq⟩

/-- **Subtraction boundary bound.** When the minuend is a binade boundary
`x = 2^k` (so `x − y` drops a binade), the intermediate rounding `z` stays
*strictly* inside `x`'s lower `F₁` rounding cell: `½·ulp₂ + y < ¼·ulp₁`, i.e.
`2^(k−p₂−1) + y < 2^(k−p₁−1)`. This strictness is exactly what stops `z` from
landing on the `F₁` midpoint (a double tie that would break innocuousness). It
holds because `y ∈ F₁` (`y ≤ 2^(ey+p₁) − 2^ey`) together with `p₂ ≥ 2p₁+1`. -/
private theorem sub_key_bound {p₁ p₂ : ℕ+} {k eb : ℤ}
    (hpp' : 2 * (p₁ : ℤ) + 1 ≤ (p₂ : ℤ))
    (hgap : eb + (p₁ : ℤ) ≤ k - (p₁ : ℤ) - 1)
    {b : ℝ} (hb_le : b ≤ (2 : ℝ) ^ (eb + (p₁ : ℤ)) - (2 : ℝ) ^ eb) :
    (2 : ℝ) ^ (k - (p₂ : ℤ) - 1) + b < (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) := by
  have hne : (2 : ℝ) ≠ 0 := by norm_num
  have h2eb : (0 : ℝ) < (2 : ℝ) ^ eb := zpow_pos (by norm_num) _
  have hp₁ℤ : (1 : ℤ) ≤ (p₁ : ℤ) := by exact_mod_cast p₁.one_le
  rcases lt_or_ge (k - (p₂ : ℤ) - 1) eb with hc | hc
  · -- `2^(k−p₂−1) < 2^eb`, so the `−2^eb` slack in `y`'s bound absorbs it.
    have h1 : (2 : ℝ) ^ (k - (p₂ : ℤ) - 1) < (2 : ℝ) ^ eb :=
      zpow_lt_zpow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ (eb + (p₁ : ℤ)) ≤ (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) :=
      zpow_le_zpow_right₀ (by norm_num) hgap
    linarith [hb_le, h1, h2]
  · -- `eb ≤ k−p₂−1`: `y < 2^(eb+p₁)` is tiny, and `2p₁+1 ≤ p₂` gives the margin.
    have hb_lt : b < (2 : ℝ) ^ (eb + (p₁ : ℤ)) := by linarith [h2eb]
    have h3 : (2 : ℝ) ^ (eb + (p₁ : ℤ)) ≤ (2 : ℝ) ^ (k - (p₂ : ℤ) - 1 + (p₁ : ℤ)) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hsplit : (2 : ℝ) ^ (k - (p₂ : ℤ) - 1 + (p₁ : ℤ))
        = (2 : ℝ) ^ (k - (p₂ : ℤ) - 1) * (2 : ℝ) ^ (p₁ : ℤ) := by rw [← zpow_add₀ hne]
    have h2p1 : (1 : ℝ) ≤ (2 : ℝ) ^ (p₁ : ℤ) := by
      rw [show (1 : ℝ) = (2 : ℝ) ^ (0 : ℤ) from (zpow_zero 2).symm]
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h6 : (1 : ℝ) + (2 : ℝ) ^ (p₁ : ℤ) ≤ (2 : ℝ) ^ ((p₁ : ℤ) + 1) := by
      rw [zpow_add₀ hne, zpow_one]; nlinarith [h2p1]
    have hfinal : (2 : ℝ) ^ (k - (p₂ : ℤ) - 1) + (2 : ℝ) ^ (k - (p₂ : ℤ) - 1 + (p₁ : ℤ))
        ≤ (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) := by
      rw [hsplit]
      calc (2 : ℝ) ^ (k - (p₂ : ℤ) - 1) + (2 : ℝ) ^ (k - (p₂ : ℤ) - 1) * (2 : ℝ) ^ (p₁ : ℤ)
          = (2 : ℝ) ^ (k - (p₂ : ℤ) - 1) * (1 + (2 : ℝ) ^ (p₁ : ℤ)) := by ring
        _ ≤ (2 : ℝ) ^ (k - (p₂ : ℤ) - 1) * (2 : ℝ) ^ ((p₁ : ℤ) + 1) :=
            mul_le_mul_of_nonneg_left h6 (le_of_lt (zpow_pos (by norm_num) _))
        _ = (2 : ℝ) ^ (k - (p₂ : ℤ) - 1 + ((p₁ : ℤ) + 1)) := by rw [← zpow_add₀ hne]
        _ ≤ (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith [hb_lt, h3, hfinal]

/-- **rnd-minus, positive ordered case** (Roux Theorem 20, radix 2, FLX,
subtraction). For `x, y ∈ F₁` with `0 < y < x`, if `p₂ ≥ 2p₁ + 1` then double
rounding of `x − y` is innocuous. Case 1 (`ex − ey ≤ p₁+1`) makes `x − y`
exactly `F₂`-representable (`diff_precisionAtMost`). Case 2 (`y` tiny) splits on
whether `x` is a binade boundary: if `x > 2^k`, `x − y` stays in `x`'s binade
and rounds directly to `x`; if `x = 2^k`, `x − y` drops a binade but
`sub_key_bound` keeps the intermediate `z` strictly inside `x`'s lower cell, so
both `◦₁(x−y)` and `◦₁(z)` equal `x`. -/
theorem rndSub_pos {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ+}
    (hp₁ : F₁.p = ((p₁ : ℕ+) : WithTop ℕ+)) (hexp₁ : F₁.exp = ⊥)
    (hp₂ : F₂.p = ((p₂ : ℕ+) : WithTop ℕ+)) (hexp₂ : F₂.exp = ⊥)
    (hpp : (2 * p₁ + 1 : ℕ+) ≤ p₂)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁)
    (hxpos : 0 < (x : ℝ)) (hypos : 0 < (y : ℝ)) (hyx : (y : ℝ) < (x : ℝ))
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((x - y : Dyadic) : ℝ) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((x - y : Dyadic) : ℝ) w := by
  have hne : (2 : ℝ) ≠ 0 := by norm_num
  have hp₁ℤ : (1 : ℤ) ≤ (p₁ : ℤ) := by exact_mod_cast p₁.one_le
  have hpp' : (2 * (p₁ : ℤ) + 1) ≤ (p₂ : ℤ) := by
    have : ((2 * p₁ + 1 : ℕ+) : ℤ) ≤ ((p₂ : ℕ+) : ℤ) := by exact_mod_cast hpp
    push_cast at this; omega
  have hr_real : ((x - y : Dyadic) : ℝ) = (x : ℝ) - (y : ℝ) := by push_cast; ring
  have hrpos : 0 < ((x - y : Dyadic) : ℝ) := by rw [hr_real]; linarith
  have hr_ne : ((x - y : Dyadic) : ℝ) ≠ 0 := ne_of_gt hrpos
  -- power helpers (avoid self-referential `rw [show var = ...]`)
  have pow_pred : ∀ a : ℤ, (2 : ℝ) ^ a = (2 : ℝ) ^ (a - 1) * 2 := fun a => by
    have h : (2 : ℝ) ^ ((a - 1) + 1) = (2 : ℝ) ^ (a - 1) * (2 : ℝ) ^ (1 : ℤ) :=
      zpow_add₀ hne (a - 1) 1
    rw [zpow_one, show (a - 1) + 1 = a from by ring] at h; exact h
  have pow_half : ∀ a : ℤ, (2 : ℝ) ^ a / 2 = (2 : ℝ) ^ (a - 1) := fun a => by
    rw [pow_pred a]; ring
  have pow_dbl : ∀ a : ℤ, (2 : ℝ) ^ a = 2 * (2 : ℝ) ^ (a - 1) := fun a => by
    rw [pow_pred a]; ring
  set ex := F₁.canonicalExp (x : ℝ) with hex
  set ey := F₁.canonicalExp (y : ℝ) with hey
  by_cases hgap : ex - ey ≤ (p₁ : ℤ) + 1
  · -- Case 1: `x − y` exactly representable in `F₂`.
    obtain ⟨hprec, hquant⟩ := diff_precisionAtMost hp₁ hx hy hxpos hypos (le_of_lt hyx) hgap
    have hmem : (x - y) ∈ F₂.unbounded := by
      refine ⟨?_, ?_, trivial⟩
      · refine Dyadic.precisionAtMost_mono ?_ hprec
        rw [FiniteFormat.unbounded_p, hp₂]; exact_mod_cast hpp
      · rw [FiniteFormat.unbounded_exp, hexp₂]; trivial
    exact rndExact (F₂ := F₂.unbounded) hmem hz hw
  · -- Case 2: `y` tiny.
    rw [not_le] at hgap
    obtain ⟨cx, hcx_lt, hxeq⟩ := exists_canonical_rep F₁ hp₁ hx hxpos
    obtain ⟨cy, hcy_lt, hyeq⟩ := exists_canonical_rep F₁ hp₁ hy hypos
    rw [← hex] at hxeq; rw [← hey] at hyeq
    have hcx_pos : 0 < cx := mantissa_pos hxeq hxpos
    have hcy_pos : 0 < cy := mantissa_pos hyeq hypos
    set k := Int.log 2 (x : ℝ) with hk
    have hex_val : ex = k + 1 - (p₁ : ℤ) := by
      rw [hex, canonicalExp_FLX hp₁ hexp₁ (ne_of_gt hxpos), abs_of_pos hxpos]
    have hey_val : ey = Int.log 2 (y : ℝ) + 1 - (p₁ : ℤ) := by
      rw [hey, canonicalExp_FLX hp₁ hexp₁ (ne_of_gt hypos), abs_of_pos hypos]
    have hgap_key : ey + (p₁ : ℤ) ≤ k - (p₁ : ℤ) - 1 := by omega
    have h2p1 : ((2 : ℝ) ^ (p₁ : ℕ)) = (2 : ℝ) ^ (p₁ : ℤ) := by rw [← zpow_natCast]
    -- binade of `x`
    have hx_lo : (2 : ℝ) ^ k ≤ (x : ℝ) := by
      have := Int.zpow_log_le_self (b := 2) (by norm_num) hxpos
      rw [← hk] at this; exact_mod_cast this
    have hx_hi : (x : ℝ) < (2 : ℝ) ^ (k + 1) := by
      have := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) (x : ℝ)
      rw [← hk] at this; exact_mod_cast this
    -- `y ≤ 2^(ey+p₁) − 2^ey` and `y < 2^(k−p₁−1)`
    have hcy_leR : (cy : ℝ) ≤ (2 : ℝ) ^ (p₁ : ℤ) - 1 := by
      rw [abs_of_pos hcy_pos] at hcy_lt
      have h : (cy : ℝ) < (2 : ℝ) ^ (p₁ : ℕ) := by exact_mod_cast hcy_lt
      have hcyi : cy ≤ (2 : ℤ) ^ (p₁ : ℕ) - 1 := by omega
      have h2 : (cy : ℝ) ≤ ((2 : ℤ) ^ (p₁ : ℕ) - 1 : ℤ) := by exact_mod_cast hcyi
      push_cast at h2; rw [← h2p1]; exact h2
    have h2ey : (0 : ℝ) < (2 : ℝ) ^ ey := zpow_pos (by norm_num) _
    have hy_le : (y : ℝ) ≤ (2 : ℝ) ^ (ey + (p₁ : ℤ)) - (2 : ℝ) ^ ey := by
      rw [hyeq]
      have hsplit : (2 : ℝ) ^ (ey + (p₁ : ℤ)) = (2 : ℝ) ^ (p₁ : ℤ) * (2 : ℝ) ^ ey := by
        rw [show ey + (p₁ : ℤ) = (p₁ : ℤ) + ey from by ring, zpow_add₀ hne]
      rw [hsplit]; nlinarith [hcy_leR, h2ey]
    have hy_lt : (y : ℝ) < (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) := by
      have h1 : (2 : ℝ) ^ (ey + (p₁ : ℤ)) ≤ (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) :=
        zpow_le_zpow_right₀ (by norm_num) hgap_key
      linarith [hy_le, h2ey]
    -- `x` is a multiple of `2^ex` and (doubling the mantissa) of `2^(ex−1)`
    have hquant_x_ex : Dyadic.quantumAtLeast ((ex : ℤ) : WithBot ℤ) x :=
      (Dyadic.quantumAtLeast_coe_real ex x).mpr ⟨cx, hxeq⟩
    have hquant_x_ex1 : Dyadic.quantumAtLeast (((ex - 1 : ℤ)) : WithBot ℤ) x :=
      (Dyadic.quantumAtLeast_coe_real (ex - 1) x).mpr ⟨2 * cx, by
        rw [hxeq, pow_pred ex]; push_cast; ring⟩
    have hu₁ : ¬ (F₁.unbounded).IsUndefined (.nearest tb₁) := by
      rw [FiniteFormat.unbounded_isUndefined]; exact hundef₁
    by_cases hbot : (x : ℝ) = (2 : ℝ) ^ k
    · -- Sub-case 2b: `x = 2^k`, `x − y` drops a binade.
      have h2ex2_le : (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) ≤ (2 : ℝ) ^ (k - 2) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have hr_lt : ((x - y : Dyadic) : ℝ) < (2 : ℝ) ^ k := by rw [hr_real, hbot]; linarith [hypos]
      have hr_gt : (2 : ℝ) ^ (k - 1) ≤ ((x - y : Dyadic) : ℝ) := by
        rw [hr_real, hbot]
        have e1 : (2 : ℝ) ^ k = 2 * (2 : ℝ) ^ (k - 1) := pow_dbl k
        have e2 : (2 : ℝ) ^ (k - 1) = 2 * (2 : ℝ) ^ (k - 2) := by
          rw [pow_dbl (k - 1), show (k - 1) - 1 = k - 2 from by ring]
        have hylt2 : (y : ℝ) < (2 : ℝ) ^ (k - 2) := lt_of_lt_of_le hy_lt h2ex2_le
        linarith [e1, e2, hylt2]
      have hlogr : Int.log 2 ((x - y : Dyadic) : ℝ) = k - 1 := by
        have h1 : k - 1 ≤ Int.log 2 ((x - y : Dyadic) : ℝ) :=
          (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hrpos).mp (by exact_mod_cast hr_gt)
        have h2 : Int.log 2 ((x - y : Dyadic) : ℝ) < k :=
          (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hrpos).mp (by exact_mod_cast hr_lt)
        omega
      have hcE2r : F₂.canonicalExp ((x - y : Dyadic) : ℝ) = k - (p₂ : ℤ) := by
        rw [canonicalExp_FLX hp₂ hexp₂ hr_ne, abs_of_pos hrpos, hlogr]; ring
      have herr : |(z : ℝ) - ((x - y : Dyadic) : ℝ)| ≤ (2 : ℝ) ^ (k - (p₂ : ℤ) - 1) := by
        have hh := nearest_error_le_half_ulp hz
        rw [ulp, hcE2r] at hh
        rwa [pow_half (k - (p₂ : ℤ))] at hh
      have hrx_abs : |((x - y : Dyadic) : ℝ) - (x : ℝ)| = (y : ℝ) := by
        rw [hr_real, abs_of_nonpos (show (x : ℝ) - (y : ℝ) - (x : ℝ) ≤ 0 by linarith)]; ring
      have hzx_close : |(z : ℝ) - (x : ℝ)| < (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) := by
        have htri := abs_sub_le (z : ℝ) ((x - y : Dyadic) : ℝ) (x : ℝ)
        rw [hrx_abs] at htri
        have hkey := sub_key_bound hpp' hgap_key hy_le
        linarith [htri, herr, hkey]
      -- `◦₁(x−y) = x`
      have hrx_round : RoundsFinite F₁.unbounded (.nearest tb₁) ((x - y : Dyadic) : ℝ) x := by
        refine nearest_eq_of_close' F₁ tb₁ _ hundef₁ ?_ ?_
        · have hcE1r : F₁.canonicalExp ((x - y : Dyadic) : ℝ) = ex - 1 := by
            rw [canonicalExp_FLX hp₁ hexp₁ hr_ne, abs_of_pos hrpos, hlogr]; omega
          rw [hcE1r]; exact hquant_x_ex1
        · have hcE1r : F₁.canonicalExp ((x - y : Dyadic) : ℝ) = ex - 1 := by
            rw [canonicalExp_FLX hp₁ hexp₁ hr_ne, abs_of_pos hrpos, hlogr]; omega
          rw [hcE1r, hrx_abs]
          have e4 : (2 : ℝ) ^ (ex - 1) / 2 = (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) := by
            rw [pow_half (ex - 1)]; congr 1; omega
          rw [e4]; exact hy_lt
      -- `◦₁(z) = x` (splitting on whether `z` is below or above `2^k`)
      have hzx_round : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) x := by
        rw [abs_lt] at hzx_close
        have hz_gt : (2 : ℝ) ^ (k - 1) < (z : ℝ) := by
          have hlow : (x : ℝ) - (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) < (z : ℝ) := by linarith [hzx_close.1]
          rw [hbot] at hlow
          have e1 : (2 : ℝ) ^ k = 2 * (2 : ℝ) ^ (k - 1) := pow_dbl k
          have e2 : (2 : ℝ) ^ (k - 1) = 2 * (2 : ℝ) ^ (k - 2) := by
            rw [pow_dbl (k - 1), show (k - 1) - 1 = k - 2 from by ring]
          linarith [hlow, h2ex2_le, e1, e2]
        have hz_pos : 0 < (z : ℝ) := lt_trans (zpow_pos (by norm_num) _) hz_gt
        rcases lt_or_ge (z : ℝ) ((2 : ℝ) ^ k) with hzlt | hzge
        · -- `z < 2^k`: binade `k−1`
          have hlogz : Int.log 2 (z : ℝ) = k - 1 := by
            have h1 : k - 1 ≤ Int.log 2 (z : ℝ) :=
              (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hz_pos).mp
                (by exact_mod_cast le_of_lt hz_gt)
            have h2 : Int.log 2 (z : ℝ) < k :=
              (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hz_pos).mp (by exact_mod_cast hzlt)
            omega
          have hcE1z : F₁.canonicalExp (z : ℝ) = ex - 1 := by
            rw [canonicalExp_FLX hp₁ hexp₁ (ne_of_gt hz_pos), abs_of_pos hz_pos, hlogz]; omega
          refine nearest_eq_of_close' F₁ tb₁ _ hundef₁ (by rw [hcE1z]; exact hquant_x_ex1) ?_
          rw [hcE1z]
          have e4 : (2 : ℝ) ^ (ex - 1) / 2 = (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) := by
            rw [pow_half (ex - 1)]; congr 1; omega
          rw [e4, abs_lt]
          exact ⟨by linarith [hzx_close.1], by linarith [hzx_close.2]⟩
        · -- `z ≥ 2^k`: binade `k`
          have hz_hi : (z : ℝ) < (2 : ℝ) ^ (k + 1) := by
            have hhigh : (z : ℝ) < (x : ℝ) + (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) := by
              linarith [hzx_close.2]
            rw [hbot] at hhigh
            have e1 : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by
              rw [zpow_add₀ hne, zpow_one]; ring
            have hb2 : (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) ≤ (2 : ℝ) ^ k :=
              zpow_le_zpow_right₀ (by norm_num) (by omega)
            linarith [hhigh, e1, hb2, zpow_pos (show (0 : ℝ) < 2 by norm_num) k]
          have hlogz : Int.log 2 (z : ℝ) = k := by
            have h1 : k ≤ Int.log 2 (z : ℝ) :=
              (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hz_pos).mp (by exact_mod_cast hzge)
            have h2 : Int.log 2 (z : ℝ) < k + 1 :=
              (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hz_pos).mp (by exact_mod_cast hz_hi)
            omega
          have hcE1z : F₁.canonicalExp (z : ℝ) = ex := by
            rw [canonicalExp_FLX hp₁ hexp₁ (ne_of_gt hz_pos), abs_of_pos hz_pos, hlogz]; omega
          refine nearest_eq_of_close' F₁ tb₁ _ hundef₁ (by rw [hcE1z]; exact hquant_x_ex) ?_
          rw [hcE1z]
          have e5 : (2 : ℝ) ^ ex / 2 = (2 : ℝ) ^ (ex - 1) := pow_half ex
          have hb3 : (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) < (2 : ℝ) ^ (ex - 1) :=
            zpow_lt_zpow_right₀ (by norm_num) (by omega)
          rw [e5, abs_lt]
          exact ⟨by linarith [hzx_close.1, hb3], by linarith [hzx_close.2, hb3]⟩
      have hw_eq : w = x := by
        rw [rndUnbounded_unique F₁.unbounded (.nearest tb₁) (z : ℝ) hu₁ hw,
            rndUnbounded_unique F₁.unbounded (.nearest tb₁) (z : ℝ) hu₁ hzx_round]
      rw [hw_eq]; exact hrx_round
    · -- Sub-case 2a: `2^k < x`, `x − y` stays in `x`'s binade.
      have hbot' : (2 : ℝ) ^ k < (x : ℝ) := lt_of_le_of_ne hx_lo (fun h => hbot h.symm)
      have hexk : ex ≤ k := by omega
      set d : ℕ := (k - ex).toNat with hd_def
      have hd : (d : ℤ) = k - ex := Int.toNat_of_nonneg (by omega)
      have hsplitk : (2 : ℝ) ^ k = (2 : ℝ) ^ (d : ℤ) * (2 : ℝ) ^ ex := by
        rw [← zpow_add₀ hne]; congr 1; omega
      have h2d_real : (2 : ℝ) ^ (d : ℤ) = ((2 : ℤ) ^ d : ℝ) := by simp [zpow_natCast]
      have hk_eq : (2 : ℝ) ^ k = ((2 : ℤ) ^ d : ℝ) * (2 : ℝ) ^ ex := by
        rw [← h2d_real]; exact hsplitk
      have h2ex : (0 : ℝ) < (2 : ℝ) ^ ex := zpow_pos (by norm_num) _
      have hcx_gt : (2 : ℤ) ^ d < cx := by
        have hltR : ((2 : ℤ) ^ d : ℝ) < (cx : ℝ) := by
          have hlt : ((2 : ℤ) ^ d : ℝ) * (2 : ℝ) ^ ex < (cx : ℝ) * (2 : ℝ) ^ ex := by
            rw [← hxeq, ← hk_eq]; exact hbot'
          exact lt_of_mul_lt_mul_right hlt (le_of_lt h2ex)
        exact_mod_cast hltR
      have hx_ge : (2 : ℝ) ^ k + (2 : ℝ) ^ ex ≤ (x : ℝ) := by
        have hcx_ge1 : ((2 : ℤ) ^ d : ℝ) + 1 ≤ (cx : ℝ) := by
          have : (2 : ℤ) ^ d + 1 ≤ cx := by omega
          exact_mod_cast this
        rw [hxeq, hk_eq]; nlinarith [hcx_ge1, h2ex]
      have hcx_le : (cx : ℝ) ≤ (2 : ℝ) ^ (p₁ : ℤ) - 1 := by
        rw [abs_of_pos hcx_pos] at hcx_lt
        have h : (cx : ℝ) < (2 : ℝ) ^ (p₁ : ℕ) := by exact_mod_cast hcx_lt
        have hcxi : cx ≤ (2 : ℤ) ^ (p₁ : ℕ) - 1 := by omega
        have h2 : (cx : ℝ) ≤ ((2 : ℤ) ^ (p₁ : ℕ) - 1 : ℤ) := by exact_mod_cast hcxi
        push_cast at h2; rw [← h2p1]; exact h2
      have hx_max : (x : ℝ) ≤ (2 : ℝ) ^ (k + 1) - (2 : ℝ) ^ ex := by
        rw [hxeq]
        have hsplit : (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ (p₁ : ℤ) * (2 : ℝ) ^ ex := by
          rw [← zpow_add₀ hne]; congr 1; omega
        rw [hsplit]; nlinarith [hcx_le, h2ex]
      have hr_lo : (2 : ℝ) ^ k < ((x - y : Dyadic) : ℝ) := by
        rw [hr_real]
        have hb1 : (y : ℝ) < (2 : ℝ) ^ ex :=
          lt_trans hy_lt (zpow_lt_zpow_right₀ (by norm_num) (by omega))
        linarith [hx_ge, hb1]
      have hr_hi : ((x - y : Dyadic) : ℝ) < (2 : ℝ) ^ (k + 1) := by
        rw [hr_real]; linarith [hx_hi, hypos]
      have hlogr : Int.log 2 ((x - y : Dyadic) : ℝ) = k := by
        have h1 : k ≤ Int.log 2 ((x - y : Dyadic) : ℝ) :=
          (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hrpos).mp
            (by exact_mod_cast le_of_lt hr_lo)
        have h2 : Int.log 2 ((x - y : Dyadic) : ℝ) < k + 1 :=
          (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hrpos).mp (by exact_mod_cast hr_hi)
        omega
      have hcE1r : F₁.canonicalExp ((x - y : Dyadic) : ℝ) = ex := by
        rw [canonicalExp_FLX hp₁ hexp₁ hr_ne, abs_of_pos hrpos, hlogr]; omega
      have hcE2r : F₂.canonicalExp ((x - y : Dyadic) : ℝ) = k + 1 - (p₂ : ℤ) := by
        rw [canonicalExp_FLX hp₂ hexp₂ hr_ne, abs_of_pos hrpos, hlogr]
      have herr : |(z : ℝ) - ((x - y : Dyadic) : ℝ)| ≤ (2 : ℝ) ^ (k - (p₂ : ℤ)) := by
        have hh := nearest_error_le_half_ulp hz
        rw [ulp, hcE2r] at hh
        have e3 : (2 : ℝ) ^ (k + 1 - (p₂ : ℤ)) / 2 = (2 : ℝ) ^ (k - (p₂ : ℤ)) := by
          rw [show k + 1 - (p₂ : ℤ) = (k - (p₂ : ℤ)) + 1 from by ring, zpow_add₀ hne, zpow_one]
          ring
        rwa [e3] at hh
      have hrx_abs : |((x - y : Dyadic) : ℝ) - (x : ℝ)| = (y : ℝ) := by
        rw [hr_real, abs_of_nonpos (show (x : ℝ) - (y : ℝ) - (x : ℝ) ≤ 0 by linarith)]; ring
      have hexm1 : (2 : ℝ) ^ (ex - 1) = (2 : ℝ) ^ (k - (p₁ : ℤ)) := by congr 1; omega
      have hzx_close : |(z : ℝ) - (x : ℝ)| < (2 : ℝ) ^ (ex - 1) := by
        have htri := abs_sub_le (z : ℝ) ((x - y : Dyadic) : ℝ) (x : ℝ)
        rw [hrx_abs] at htri
        have hb1 : (2 : ℝ) ^ (k - (p₂ : ℤ)) ≤ (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
        have hd2 : (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) + (2 : ℝ) ^ (k - (p₁ : ℤ) - 1)
            = (2 : ℝ) ^ (k - (p₁ : ℤ)) := by
          rw [pow_dbl (k - (p₁ : ℤ))]; ring
        rw [hexm1]; linarith [htri, herr, hb1, hy_lt, hd2]
      have hrx_round : RoundsFinite F₁.unbounded (.nearest tb₁) ((x - y : Dyadic) : ℝ) x := by
        refine nearest_eq_of_close' F₁ tb₁ _ hundef₁ (by rw [hcE1r]; exact hquant_x_ex) ?_
        rw [hcE1r, hrx_abs]
        have e5 : (2 : ℝ) ^ ex / 2 = (2 : ℝ) ^ (ex - 1) := pow_half ex
        rw [e5]
        calc (y : ℝ) < (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) := hy_lt
          _ < (2 : ℝ) ^ (ex - 1) := by
              rw [hexm1]; exact zpow_lt_zpow_right₀ (by norm_num) (by omega)
      have hzx_round : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) x := by
        rw [abs_lt] at hzx_close
        have e8 : (2 : ℝ) ^ ex = 2 * (2 : ℝ) ^ (ex - 1) := pow_dbl ex
        have h2ex1 : (0 : ℝ) < (2 : ℝ) ^ (ex - 1) := zpow_pos (by norm_num) _
        have hz_gt : (2 : ℝ) ^ k < (z : ℝ) := by
          have hlow : (x : ℝ) - (2 : ℝ) ^ (ex - 1) < (z : ℝ) := by linarith [hzx_close.1]
          linarith [hlow, hx_ge, e8, h2ex1]
        have hz_pos : 0 < (z : ℝ) := lt_trans (zpow_pos (by norm_num) _) hz_gt
        have hz_hi : (z : ℝ) < (2 : ℝ) ^ (k + 1) := by
          have hhigh : (z : ℝ) < (x : ℝ) + (2 : ℝ) ^ (ex - 1) := by linarith [hzx_close.2]
          linarith [hhigh, hx_max, e8]
        have hlogz : Int.log 2 (z : ℝ) = k := by
          have h1 : k ≤ Int.log 2 (z : ℝ) :=
            (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hz_pos).mp
              (by exact_mod_cast le_of_lt hz_gt)
          have h2 : Int.log 2 (z : ℝ) < k + 1 :=
            (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hz_pos).mp (by exact_mod_cast hz_hi)
          omega
        have hcE1z : F₁.canonicalExp (z : ℝ) = ex := by
          rw [canonicalExp_FLX hp₁ hexp₁ (ne_of_gt hz_pos), abs_of_pos hz_pos, hlogz]; omega
        refine nearest_eq_of_close' F₁ tb₁ _ hundef₁ (by rw [hcE1z]; exact hquant_x_ex) ?_
        rw [hcE1z]
        have e5 : (2 : ℝ) ^ ex / 2 = (2 : ℝ) ^ (ex - 1) := pow_half ex
        rw [e5, abs_lt]; exact ⟨hzx_close.1, hzx_close.2⟩
      have hw_eq : w = x := by
        rw [rndUnbounded_unique F₁.unbounded (.nearest tb₁) (z : ℝ) hu₁ hw,
            rndUnbounded_unique F₁.unbounded (.nearest tb₁) (z : ℝ) hu₁ hzx_round]
      rw [hw_eq]; exact hrx_round

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

/-- **rnd-difference, nonnegative operands** (Roux Theorem 20, radix 2, FLX,
subtraction). For `a, b ∈ F₁` with `0 ≤ a, 0 ≤ b`, if `p₂ ≥ 2p₁+1` then double
rounding of `a − b` is innocuous. Reduces to `rndSub_pos` for the ordered
positive case (`a > b` directly, `a < b` by joint negation), while a zero
operand or `a = b` makes `a − b` a member of `F₁`, hence exactly
`F₂`-representable. -/
theorem rndDiff {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ+}
    (hp₁ : F₁.p = ((p₁ : ℕ+) : WithTop ℕ+)) (hexp₁ : F₁.exp = ⊥)
    (hp₂ : F₂.p = ((p₂ : ℕ+) : WithTop ℕ+)) (hexp₂ : F₂.exp = ⊥)
    (hpp : (2 * p₁ + 1 : ℕ+) ≤ p₂)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {a b : Dyadic} (ha : a ∈ F₁) (hb : b ∈ F₁)
    (hann : 0 ≤ (a : ℝ)) (hbnn : 0 ≤ (b : ℝ))
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((a - b : Dyadic) : ℝ) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((a - b : Dyadic) : ℝ) w := by
  have hp1p2 : (p₁ : ℕ+) ≤ p₂ := by
    have h : 2 * (p₁ : ℕ) + 1 ≤ (p₂ : ℕ) := by exact_mod_cast hpp
    exact_mod_cast (by omega : (p₁ : ℕ) ≤ (p₂ : ℕ))
  by_cases hab_mem : (a - b : Dyadic) ∈ F₁
  · -- `a − b` is representable in `F₁` (a zero operand, or `a = b`): exact.
    exact rndExact (mem_F₂_unbounded hp₁ hp₂ hexp₂ hp1p2 hab_mem) hz hw
  · -- otherwise `a > 0`, `b > 0`, `a ≠ b`.
    have hane : (a : ℝ) ≠ 0 := by
      intro h; apply hab_mem
      have hd : a = 0 := (Dyadic.coe_real_inj a 0).mp (by rw [Dyadic.coe_real_zero]; exact h)
      rw [hd, show (0 - b : Dyadic) = -b from by ring]; exact FiniteFormat.neg_mem hb
    have hbne : (b : ℝ) ≠ 0 := by
      intro h; apply hab_mem
      have hd : b = 0 := (Dyadic.coe_real_inj b 0).mp (by rw [Dyadic.coe_real_zero]; exact h)
      rw [hd, show (a - 0 : Dyadic) = a from by ring]; exact ha
    have habne : (a : ℝ) ≠ (b : ℝ) := by
      intro h; apply hab_mem
      have hd : a = b := (Dyadic.coe_real_inj a b).mp h
      rw [hd, show (b - b : Dyadic) = 0 from by ring]; exact FiniteFormat.zero_mem F₁
    have hap : 0 < (a : ℝ) := lt_of_le_of_ne hann (Ne.symm hane)
    have hbp : 0 < (b : ℝ) := lt_of_le_of_ne hbnn (Ne.symm hbne)
    have hba : (a - b : Dyadic) = -(b - a) := by ring
    rcases lt_or_gt_of_ne habne with hab | hab
    · -- `a < b`: negate to `b − a > 0` and apply `rndSub_pos`.
      have hz' : RoundsFinite F₂.unbounded (.nearest tb₂) ((b - a : Dyadic) : ℝ) (-z) := by
        rw [RoundsFinite.neg_nearest F₂.unbounded tb₂ ((b - a : Dyadic) : ℝ) (-z), neg_neg,
            show -((b - a : Dyadic) : ℝ) = ((a - b : Dyadic) : ℝ) from by rw [hba]; push_cast; ring]
        exact hz
      have hw' : RoundsFinite F₁.unbounded (.nearest tb₁) ((-z : Dyadic) : ℝ) (-w) := by
        rw [Dyadic.coe_real_neg]
        exact (RoundsFinite.neg_nearest F₁.unbounded tb₁ (z : ℝ) w).mp hw
      have hres := rndSub_pos hp₁ hexp₁ hp₂ hexp₂ hpp hundef₁ hb ha hbp hap hab hz' hw'
      rw [RoundsFinite.neg_nearest F₁.unbounded tb₁ ((a - b : Dyadic) : ℝ) w,
          show -((a - b : Dyadic) : ℝ) = ((b - a : Dyadic) : ℝ) from by rw [hba]; push_cast; ring]
      exact hres
    · -- `a > b`: apply `rndSub_pos` directly.
      exact rndSub_pos hp₁ hexp₁ hp₂ hexp₂ hpp hundef₁ ha hb hap hbp hab hz hw

/-- **rnd-plus** (Roux Theorem 20, radix 2, FLX). For **arbitrary** `x, y ∈ F₁`,
if `p₂ ≥ 2p₁ + 1` then double rounding of `x + y` (round to nearest in `F₂`,
then in `F₁`) agrees with rounding `x + y` directly into `F₁`. Same-sign
operands go through `rndAdd_nonneg` (both nonpositive by joint negation); mixed
signs are a subtraction handled by `rndDiff`. This closes the sign gap with
Flocq's `round_round_plus`. -/
theorem rndAdd {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ+}
    (hp₁ : F₁.p = ((p₁ : ℕ+) : WithTop ℕ+)) (hexp₁ : F₁.exp = ⊥)
    (hp₂ : F₂.p = ((p₂ : ℕ+) : WithTop ℕ+)) (hexp₂ : F₂.exp = ⊥)
    (hpp : (2 * p₁ + 1 : ℕ+) ≤ p₂)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁)
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((x + y : Dyadic) : ℝ) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((x + y : Dyadic) : ℝ) w := by
  rcases (lt_or_ge (x : ℝ) 0).symm with hxnn | hxneg
  · rcases (lt_or_ge (y : ℝ) 0).symm with hynn | hyneg
    · -- both nonnegative
      exact rndAdd_nonneg hp₁ hexp₁ hp₂ hexp₂ hpp hundef₁ hx hy hxnn hynn hz hw
    · -- `x ≥ 0 > y`: `x + y = x − (−y)`
      have hb : (-y) ∈ F₁ := FiniteFormat.neg_mem hy
      have hbnn : 0 ≤ ((-y : Dyadic) : ℝ) := by rw [Dyadic.coe_real_neg]; linarith
      rw [show (x + y : Dyadic) = x - (-y) from by ring] at hz ⊢
      exact rndDiff hp₁ hexp₁ hp₂ hexp₂ hpp hundef₁ hx hb hxnn hbnn hz hw
  · rcases (lt_or_ge (y : ℝ) 0).symm with hynn | hyneg
    · -- `x < 0 ≤ y`: `x + y = y − (−x)`
      have hb : (-x) ∈ F₁ := FiniteFormat.neg_mem hx
      have hbnn : 0 ≤ ((-x : Dyadic) : ℝ) := by rw [Dyadic.coe_real_neg]; linarith
      rw [show (x + y : Dyadic) = y - (-x) from by ring] at hz ⊢
      exact rndDiff hp₁ hexp₁ hp₂ hexp₂ hpp hundef₁ hy hb hynn hbnn hz hw
    · -- both nonpositive: joint negation reduces to `rndAdd_nonneg`
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

end Mpfx
