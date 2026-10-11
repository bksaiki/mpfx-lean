import Mpfx.Format.CanonicalExp
import Mpfx.DoubleRounding.NearestMidpoint
import Mpfx.DoubleRounding.Basic

/-!
# Operation-specific double rounding: addition (Roux 2014, §3)

Roux's Theorem 20 (radix 2, no minimum quantum): double rounding of addition
is innocuous when `p₂ ≥ 2p₁ + 1`. The proof splits on the exponent gap between
the operands:

* **Case 1** (`ln y ≥ φ₁(ln x) − 1`, operands within `p₁+1` binades): `x + y`
  fits in `2p₁ + 1` significand bits, so it is *exactly* representable in `F₂`
  and the intermediate rounding is a no-op.
* **Case 2** (`ln y ≤ φ₁(ln x) − 2`, `y` tiny): `x + y` sits just above its
  `F₁` round-down, well below the midpoint, so `rnd_lt_mid'` (Lemma 16) applies.

`rndAdd_pos`/`rndSub_pos` prove the result for `0 < y ≤ x` (Roux's core cases);
`rndAdd` lifts them to **arbitrary operands** by swapping (`add_comm`), handling
zeros exactly, joint negation for the both-nonpositive case, and rewriting mixed
signs `x + y` as a subtraction `x − (−y)` (Roux §3.1).
-/

namespace Mpfx

/-- **Exact representability of a subnormal result** (finite `exp`). If `v` inherits `F₁`'s
quantum (`quantumAtLeast F₁.exp v`, e.g. `v = x ± y` for `x, y ∈ F₁`) and is
*subnormal* in `F₂` (`F₂.exp = ↑e₂` with `log₂|v|+1−p₂ < e₂`), then `v ∈ F₂` — a
subnormal result never needs the midpoint argument. `hexp : F₂.exp ≤ F₁.exp`
carries `v`'s quantum down to `F₂`. -/
private theorem mem_F₂_of_subnormal {F₁ F₂ : FiniteFormat} {p₂ : ℕ}
    (hp₂ : F₂.p = (p₂ : Prec)) (hexp : F₂.exp ≤ F₁.exp)
    {v : Dyadic} (hqv : Dyadic.quantumAtLeast F₁.exp v)
    {e₂ : ℤ} (he₂ : F₂.exp = (e₂ : QExp))
    (hsub : Int.log 2 |(v : ℝ)| + 1 - (p₂ : ℤ) < e₂) : v ∈ F₂.unbounded := by
  by_cases hv0 : (v : ℝ) = 0
  · rw [eq_zero_of_coe_real_zero hv0]; exact FiniteFormat.zero_mem _
  -- Subnormal: the canonical exponent is the quantum `e₂`, a step `v` inherits.
  obtain ⟨C, hC⟩ := (Dyadic.quantumAtLeast_coe_real e₂ v).mp
    (Dyadic.quantumAtLeast_anti (he₂ ▸ hexp) hqv)
  exact F₂.mem_unbounded_of_mul_zpow_canonicalExp (m := C)
    (by rw [canonicalExp_subnormal hp₂ he₂ hv0 hsub.le]; exact hC)

/-- Sign/positivity extractor: from `(x:ℝ) = c·2^e > 0` with `2^e > 0`, get `c > 0`. -/
private theorem mantissa_pos {c e : ℤ} {x : ℝ} (hxeq : x = (c : ℝ) * (2 : ℝ) ^ e)
    (hpos : 0 < x) : 0 < c := by
  have h2e : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have h : (0 : ℝ) < (c : ℝ) * (2 : ℝ) ^ e := hxeq ▸ hpos
  rcases mul_pos_iff.mp h with ⟨hc, _⟩ | ⟨_, hng⟩
  · exact_mod_cast hc
  · linarith

/-- Setup for `addSub_precisionAtMost`. For `x, y ∈ F₁`
with `0 < y ≤ x` and canonical-exponent gap `≤ p₁ + 1`, both operands are written
over the common quantum `2^(canonicalExp y)` with positive mantissas `< 2^p₁`, and
the exponent gap `n = ex − ey` satisfies `2^n ≤ 2·2^p₁`. -/
private theorem add_sub_mantissa_setup {F₁ : FiniteFormat} {p₁ : ℕ}
    (hp₁ : F₁.p = (p₁ : Prec))
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁)
    (hxpos : 0 < (x : ℝ)) (hypos : 0 < (y : ℝ)) (hyx : (y : ℝ) ≤ (x : ℝ))
    (hgap : F₁.canonicalExp (x : ℝ) - F₁.canonicalExp (y : ℝ) ≤ (p₁ : ℤ) + 1) :
    ∃ (cx cy : ℤ) (n : ℕ), 0 < cx ∧ 0 < cy ∧
      cx ≤ (2 : ℤ) ^ p₁ - 1 ∧ cy ≤ (2 : ℤ) ^ p₁ - 1 ∧
      (2 : ℤ) ^ n ≤ 2 * (2 : ℤ) ^ p₁ ∧
      (x : ℝ) = (cx : ℝ) * (2 : ℝ) ^ n * (2 : ℝ) ^ (F₁.canonicalExp (y : ℝ)) ∧
      (y : ℝ) = (cy : ℝ) * (2 : ℝ) ^ (F₁.canonicalExp (y : ℝ)) := by
  set ex := F₁.canonicalExp (x : ℝ) with hex
  set ey := F₁.canonicalExp (y : ℝ) with hey
  obtain ⟨cx, hcx_lt, hxeq⟩ := exists_canonical_rep F₁ hp₁ hx hxpos
  obtain ⟨cy, hcy_lt, hyeq⟩ := exists_canonical_rep F₁ hp₁ hy hypos
  rw [← hex] at hxeq; rw [← hey] at hyeq
  have hcx_pos : 0 < cx := mantissa_pos hxeq hxpos
  have hcy_pos : 0 < cy := mantissa_pos hyeq hypos
  have hey_le_ex : ey ≤ ex := by
    rw [hey, hex]
    exact FiniteFormat.canonicalExp_mono F₁ (ne_of_gt hypos)
      (by rw [abs_of_pos hypos, abs_of_pos hxpos]; exact hyx)
  set n : ℕ := (ex - ey).toNat with hn
  have hn_nat : n ≤ p₁ + 1 := by
    have : (n : ℤ) = ex - ey := by rw [hn, Int.toNat_of_nonneg (by omega)]
    omega
  have hsplit : (2 : ℝ) ^ ex = (2 : ℝ) ^ n * (2 : ℝ) ^ ey := by
    rw [hn]; exact two_zpow_split_toNat hey_le_ex
  have hcx_le : cx ≤ (2 : ℤ) ^ p₁ - 1 := by rw [abs_of_pos hcx_pos] at hcx_lt; omega
  have hcy_le : cy ≤ (2 : ℤ) ^ p₁ - 1 := by rw [abs_of_pos hcy_pos] at hcy_lt; omega
  have h2n_le : (2 : ℤ) ^ n ≤ 2 * (2 : ℤ) ^ p₁ := by
    calc (2 : ℤ) ^ n ≤ (2 : ℤ) ^ (p₁ + 1) := pow_le_pow_right₀ (by norm_num) hn_nat
      _ = 2 * (2 : ℤ) ^ p₁ := by rw [pow_succ]; ring
  exact ⟨cx, cy, n, hcx_pos, hcy_pos, hcx_le, hcy_le, h2n_le,
    by rw [hxeq, hsplit]; ring, hyeq⟩

/-- Common arithmetic tail: `2 ≤ A` and `2^(2p₁+1) = 2·A·A` (with `A = 2^p₁`),
used to package both precision bounds. -/
private theorem two_pow_two_p_split {p₁ : ℕ} (hp : 0 < p₁) :
    (2 : ℤ) ≤ (2 : ℤ) ^ p₁ ∧
    (2 : ℤ) ^ (2 * p₁ + 1) = 2 * (2 : ℤ) ^ p₁ * (2 : ℤ) ^ p₁ := by
  refine ⟨?_, ?_⟩
  · calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ p₁ := pow_le_pow_right₀ (by norm_num) hp
  · rw [show 2 * p₁ + 1 = p₁ + (p₁ + 1) from by ring, pow_add, pow_succ]; ring

/-- **Case 1 precision bound** (Roux Theorem 20, the exact-intermediate case).
For `x, y ∈ F₁` with `0 < y ≤ x` and canonical-exponent gap `≤ p₁ + 1`, both
`x + y` and `x − y` fit in `2p₁ + 1` significand bits at quantum `canonicalExp y`,
hence are representable in any `F₂` with `p₂ ≥ 2p₁+1` and fine enough quantum. -/
private theorem addSub_precisionAtMost {F₁ : FiniteFormat} {p₁ : ℕ}
    (hp₁ : F₁.p = (p₁ : Prec))
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁)
    (hxpos : 0 < (x : ℝ)) (hypos : 0 < (y : ℝ)) (hyx : (y : ℝ) ≤ (x : ℝ))
    (hgap : F₁.canonicalExp (x : ℝ) - F₁.canonicalExp (y : ℝ) ≤ (p₁ : ℤ) + 1) :
    Dyadic.precisionAtMost ((2 * p₁ + 1 : ℕ) : Prec) (x + y) ∧
      Dyadic.precisionAtMost ((2 * p₁ + 1 : ℕ) : Prec) (x - y) := by
  obtain ⟨cx, cy, n, hcx_pos, hcy_pos, hcx_le, hcy_le, h2n_le, hx_rep, hy_rep⟩ :=
    add_sub_mantissa_setup hp₁ hx hy hxpos hypos hyx hgap
  obtain ⟨hAge, h2A2⟩ := two_pow_two_p_split (F₁.p_pos hp₁)
  have h2n_pos : (0 : ℤ) < (2 : ℤ) ^ n := by positivity
  have hprod : cx * (2 : ℤ) ^ n ≤ ((2 : ℤ) ^ p₁ - 1) * (2 * (2 : ℤ) ^ p₁) :=
    mul_le_mul hcx_le h2n_le h2n_pos.le (by omega)
  have hcxn_pos : 0 < cx * (2 : ℤ) ^ n := mul_pos hcx_pos h2n_pos
  -- `x ± y = (cx · 2^n ± cy) · 2^ey` with the coefficient below `2^(2p₁+1)`.
  set ey := F₁.canonicalExp (y : ℝ)
  refine ⟨(Dyadic.precisionAtMost_coe_real _ _).mpr ⟨cx * 2 ^ n + cy, ey, ?_, ?_⟩,
    (Dyadic.precisionAtMost_coe_real _ _).mpr ⟨cx * 2 ^ n - cy, ey, ?_, ?_⟩⟩
  · rw [Dyadic.coe_real_add, hx_rep, hy_rep]; push_cast; ring
  · rw [h2A2, abs_of_pos (by omega)]; nlinarith [hprod, hcy_le, hAge]
  · rw [Dyadic.coe_real_sub, hx_rep, hy_rep]; push_cast; ring
  · rw [h2A2, abs_lt]
    exact ⟨by nlinarith [hcxn_pos, hcy_le, hAge], by nlinarith [hprod, hcy_pos, hAge]⟩

/-- **Setup for the midpoint cases.** For positive `x, y ∈ F₁` with a
canonical-exponent gap above `p₁ + 1`, `x` is normal in `F₁` (its canonical
exponent is `⌊log₂ x⌋ + 1 − p₁`, with the minimum quantum at most `⌊log₂ x⌋ − p₁`),
its significand is at most `2^p₁ − 1`, and `y` sits below `2^(ex − 2)`. -/
private theorem gap_setup {F₁ : FiniteFormat} {p₁ : ℕ} (hp₁ : F₁.p = (p₁ : Prec))
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁)
    (hxpos : 0 < (x : ℝ)) (hypos : 0 < (y : ℝ))
    (hgap : (p₁ : ℤ) + 1 < F₁.canonicalExp (x : ℝ) - F₁.canonicalExp (y : ℝ)) :
    ∃ cx : ℤ, (x : ℝ) = cx * 2 ^ F₁.canonicalExp (x : ℝ) ∧ 0 < cx ∧
      (cx : ℝ) ≤ 2 ^ (p₁ : ℤ) - 1 ∧
      F₁.canonicalExp (x : ℝ) = Int.log 2 (x : ℝ) + 1 - p₁ ∧
      F₁.exp ≤ ((Int.log 2 (x : ℝ) - p₁ : ℤ) : QExp) ∧
      (y : ℝ) ≤ 2 ^ (F₁.canonicalExp (y : ℝ) + p₁) - 2 ^ F₁.canonicalExp (y : ℝ) ∧
      (y : ℝ) < 2 ^ (F₁.canonicalExp (x : ℝ) - 2) := by
  set ex := F₁.canonicalExp (x : ℝ) with hex
  set ey := F₁.canonicalExp (y : ℝ) with hey
  obtain ⟨cx, hcx_lt, hxeq⟩ := exists_canonical_rep F₁ hp₁ hx hxpos
  obtain ⟨cy, hcy_lt, hyeq⟩ := exists_canonical_rep F₁ hp₁ hy hypos
  rw [← hex] at hxeq; rw [← hey] at hyeq
  have hcx_pos : 0 < cx := mantissa_pos hxeq hxpos
  have hcy_pos : 0 < cy := mantissa_pos hyeq hypos
  -- A positive significand below `2^p₁` is at most `2^p₁ − 1`.
  have hmant : ∀ {c : ℤ}, 0 < c → |c| < 2 ^ p₁ → (c : ℝ) ≤ 2 ^ (p₁ : ℤ) - 1 :=
      fun {c} hc h => by
    rw [abs_of_pos hc] at h
    have : c ≤ 2 ^ p₁ - 1 := by omega
    rw [zpow_natCast]; exact_mod_cast this
  -- `x` is normal: `2^ex ≤ x < 2^(⌊log₂ x⌋+1)` gives `ex ≤ ⌊log₂ x⌋`.
  have hex_le : ex ≤ Int.log 2 (x : ℝ) := by
    have hx_ge : (2 : ℝ) ^ ex ≤ (x : ℝ) := by
      rw [hxeq]
      have h1 : (1 : ℝ) ≤ (cx : ℝ) := by exact_mod_cast hcx_pos
      nlinarith [zpow_pos (show (0 : ℝ) < 2 by norm_num) ex]
    have hxlt : (x : ℝ) < (2 : ℝ) ^ (Int.log 2 (x : ℝ) + 1) :=
      Int.lt_zpow_succ_log_self (b := 2) (by norm_num) _
    by_contra hc
    have : (2 : ℝ) ^ (Int.log 2 (x : ℝ) + 1) ≤ (2 : ℝ) ^ ex :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith
  have hnorm : F₁.exp ≤ ((Int.log 2 (x : ℝ) - p₁ : ℤ) : QExp) :=
    le_trans (exp_le_canonicalExp_coe F₁ (y : ℝ)) (by
      rw [← hey]; exact_mod_cast (show ey ≤ Int.log 2 (x : ℝ) - p₁ by omega))
  have hex_val : ex = Int.log 2 (x : ℝ) + 1 - p₁ := by
    rw [hex, canonicalExp_closed hp₁ (ne_of_gt hxpos) (le_trans hnorm (by
      rw [abs_of_pos hxpos]; exact_mod_cast (show Int.log 2 (x : ℝ) - p₁ ≤
        Int.log 2 (x : ℝ) + 1 - p₁ by omega))), abs_of_pos hxpos]
  have h2ey : (0 : ℝ) < 2 ^ ey := zpow_pos (by norm_num) _
  have hy_le : (y : ℝ) ≤ 2 ^ (ey + p₁) - 2 ^ ey := by
    rw [hyeq, zpow_add₀ two_ne_zero, mul_comm ((2 : ℝ) ^ ey)]
    nlinarith [hmant hcy_pos hcy_lt]
  exact ⟨cx, hxeq, hcx_pos, hmant hcx_pos hcx_lt, hex_val, hnorm, hy_le,
    lt_of_lt_of_le (by linarith) (zpow_le_zpow_right₀ (by norm_num) (by omega))⟩

/-- **Subtraction boundary bound.** When the minuend is a binade boundary
`x = 2^k` (so `x − y` drops a binade), the intermediate rounding `z` stays
*strictly* inside `x`'s lower `F₁` rounding cell: `½·ulp₂ + y < ¼·ulp₁`, i.e.
`2^(k−p₂−1) + y < 2^(k−p₁−1)`. This strictness is exactly what stops `z` from
landing on the `F₁` midpoint (a double tie that would break innocuousness). It
holds because `y ∈ F₁` (`y ≤ 2^(ey+p₁) − 2^ey`) together with `p₂ ≥ 2p₁+1`. -/
private theorem sub_key_bound {p₁ p₂ : ℕ} (hp : 0 < p₁) {k eb : ℤ}
    (hpp' : 2 * (p₁ : ℤ) + 1 ≤ (p₂ : ℤ))
    (hgap : eb + (p₁ : ℤ) ≤ k - (p₁ : ℤ) - 1)
    {b : ℝ} (hb_le : b ≤ (2 : ℝ) ^ (eb + (p₁ : ℤ)) - (2 : ℝ) ^ eb) :
    (2 : ℝ) ^ (k - (p₂ : ℤ) - 1) + b < (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) := by
  have hne : (2 : ℝ) ≠ 0 := by norm_num
  have h2eb : (0 : ℝ) < (2 : ℝ) ^ eb := zpow_pos (by norm_num) _
  have hp₁ℤ : (1 : ℤ) ≤ (p₁ : ℤ) := by exact_mod_cast hp
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

/-- **rnd-minus, ordered positive, genuine-midpoint core** (radix 2, either
exponent regime).
The `x − y` case that needs Roux's midpoint argument: the operand gap exceeds
`p₁+1` (`hgap`) and `x − y` is *normal* in `F₂` (`hF2norm`) — hence normal in
`F₁` too, so `canonicalExp` takes the precision-exponent closed form
(`canonicalExp_closed`) and the proof runs identically to the `exp = ⊥` case.
Split on whether `x` is a
binade boundary: `x > 2^k` keeps `x − y` in `x`'s binade; `x = 2^k` drops a
binade but `sub_key_bound` keeps the intermediate `z` strictly inside `x`'s
lower cell. Both `◦₁(x−y)` and `◦₁(z)` equal `x`. -/
private theorem rndSub_pos_normal {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ}
    (hp₁ : F₁.p = (p₁ : Prec))
    (hp₂ : F₂.p = (p₂ : Prec))
    (hpp : 2 * p₁ + 1 ≤ p₂)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁)
    (hxpos : 0 < (x : ℝ)) (hypos : 0 < (y : ℝ)) (hyx : (y : ℝ) < (x : ℝ))
    (hgap : (p₁ : ℤ) + 1 < F₁.canonicalExp (x : ℝ) - F₁.canonicalExp (y : ℝ))
    (hF2norm : F₂.exp ≤ ((Int.log 2 |((x - y : Dyadic) : ℝ)| + 1 - (p₂ : ℤ) : ℤ) : QExp))
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((x - y : Dyadic) : ℝ) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((x - y : Dyadic) : ℝ) w := by
  have hne : (2 : ℝ) ≠ 0 := by norm_num
  have hp₁ℤ : (1 : ℤ) ≤ (p₁ : ℤ) := by exact_mod_cast F₁.p_pos hp₁
  have hpp' : (2 * (p₁ : ℤ) + 1) ≤ (p₂ : ℤ) := by omega
  have hr_real : ((x - y : Dyadic) : ℝ) = (x : ℝ) - (y : ℝ) := by push_cast; ring
  have hrpos : 0 < ((x - y : Dyadic) : ℝ) := by rw [hr_real]; linarith
  have hr_ne : ((x - y : Dyadic) : ℝ) ≠ 0 := ne_of_gt hrpos
  -- power helpers (shared `two_zpow_*` from `CanonicalExp`)
  have pow_half := two_zpow_half
  have pow_dbl := two_zpow_dbl
  set ex := F₁.canonicalExp (x : ℝ) with hex
  set ey := F₁.canonicalExp (y : ℝ) with hey
  obtain ⟨cx, hxeq, hcx_pos, hcx_le, hex_val, hnormF1, hy_le, hy_lt⟩ :=
    gap_setup hp₁ hx hy hxpos hypos hgap
  set k := Int.log 2 (x : ℝ) with hk
  rw [show ex - 2 = k - (p₁ : ℤ) - 1 by omega] at hy_lt
  have hgap_key : ey + (p₁ : ℤ) ≤ k - (p₁ : ℤ) - 1 := by omega
  -- binade of `x`
  have hx_lo : (2 : ℝ) ^ k ≤ (x : ℝ) := Int.zpow_log_le_self (b := 2) (by norm_num) hxpos
  have hx_hi : (x : ℝ) < (2 : ℝ) ^ (k + 1) := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) _
  -- precision-exponent `canonicalExp` for any `F₁`-normal value, binade `≥ k−1`
  have cE1 : ∀ v : ℝ, v ≠ 0 → k - 1 ≤ Int.log 2 |v| →
      F₁.canonicalExp v = Int.log 2 |v| + 1 - (p₁ : ℤ) := by
    intro v hv hlog
    refine canonicalExp_closed hp₁ hv (le_trans hnormF1 ?_)
    exact_mod_cast (show k - (p₁ : ℤ) ≤ Int.log 2 |v| + 1 - (p₁ : ℤ) by omega)
  -- `x` is a multiple of `2^ex` and (doubling the mantissa) of `2^(ex−1)`
  have hquant_x_ex : Dyadic.quantumAtLeast (ex : QExp) x :=
    (Dyadic.quantumAtLeast_coe_real ex x).mpr ⟨cx, hxeq⟩
  have hquant_x_ex1 : Dyadic.quantumAtLeast ((ex - 1 : ℤ) : QExp) x :=
    (Dyadic.quantumAtLeast_coe_real (ex - 1) x).mpr ⟨2 * cx, by
      rw [hxeq, pow_dbl ex]; push_cast; ring⟩
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
    have hlogr : Int.log 2 ((x - y : Dyadic) : ℝ) = k - 1 :=
      log_eq_of_zpow_bounds hrpos hr_gt (by rwa [sub_add_cancel])
    have hcE2r : F₂.canonicalExp ((x - y : Dyadic) : ℝ) = k - (p₂ : ℤ) := by
      rw [canonicalExp_closed hp₂ hr_ne hF2norm, abs_of_pos hrpos, hlogr]; ring
    have herr : |(z : ℝ) - ((x - y : Dyadic) : ℝ)| ≤ (2 : ℝ) ^ (k - (p₂ : ℤ) - 1) := by
      have hh := nearest_error_le_half_ulp hz
      rw [ulp_of_ne_zero F₂ hr_ne, hcE2r] at hh
      rwa [pow_half (k - (p₂ : ℤ))] at hh
    have hrx_abs : |((x - y : Dyadic) : ℝ) - (x : ℝ)| = (y : ℝ) := by
      rw [hr_real, abs_of_nonpos (show (x : ℝ) - (y : ℝ) - (x : ℝ) ≤ 0 by linarith)]; ring
    have hzx_close : |(z : ℝ) - (x : ℝ)| < (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) := by
      have htri := abs_sub_le (z : ℝ) ((x - y : Dyadic) : ℝ) (x : ℝ)
      rw [hrx_abs] at htri
      have hkey := sub_key_bound (F₁.p_pos hp₁) hpp' hgap_key hy_le
      linarith [htri, herr, hkey]
    -- `◦₁(x−y) = x`
    have hcE1r : F₁.canonicalExp ((x - y : Dyadic) : ℝ) = ex - 1 := by
      rw [cE1 _ hr_ne (by rw [abs_of_pos hrpos]; omega), abs_of_pos hrpos, hlogr]; omega
    have e4 : (2 : ℝ) ^ (ex - 1) / 2 = (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) := by
      rw [pow_half (ex - 1)]; congr 1; omega
    have hrx_round : RoundsFinite F₁.unbounded (.nearest tb₁) ((x - y : Dyadic) : ℝ) x := by
      refine nearest_eq_of_close' F₁ tb₁ _ hundef₁ (by rw [hcE1r]; exact hquant_x_ex1) ?_
      rw [hcE1r, hrx_abs, e4]; exact hy_lt
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
        have hlogz : Int.log 2 (z : ℝ) = k - 1 :=
          log_eq_of_zpow_bounds hz_pos hz_gt.le (by rwa [sub_add_cancel])
        have hcE1z : F₁.canonicalExp (z : ℝ) = ex - 1 := by
          rw [cE1 _ (ne_of_gt hz_pos) (by rw [abs_of_pos hz_pos]; omega),
            abs_of_pos hz_pos, hlogz]; omega
        refine nearest_eq_of_close' F₁ tb₁ _ hundef₁ (by rw [hcE1z]; exact hquant_x_ex1) ?_
        rw [hcE1z, e4, abs_lt]
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
        have hlogz : Int.log 2 (z : ℝ) = k := log_eq_of_zpow_bounds hz_pos hzge hz_hi
        have hcE1z : F₁.canonicalExp (z : ℝ) = ex := by
          rw [cE1 _ (ne_of_gt hz_pos) (by rw [abs_of_pos hz_pos]; omega),
            abs_of_pos hz_pos, hlogz]; omega
        refine nearest_eq_of_close' F₁ tb₁ _ hundef₁ (by rw [hcE1z]; exact hquant_x_ex) ?_
        rw [hcE1z]
        have e5 : (2 : ℝ) ^ ex / 2 = (2 : ℝ) ^ (ex - 1) := pow_half ex
        have hb3 : (2 : ℝ) ^ (k - (p₁ : ℤ) - 1) < (2 : ℝ) ^ (ex - 1) :=
          zpow_lt_zpow_right₀ (by norm_num) (by omega)
        rw [e5, abs_lt]
        exact ⟨by linarith [hzx_close.1, hb3], by linarith [hzx_close.2, hb3]⟩
    have hw_eq : w = x := RoundsFinite.unique hu₁ hw hzx_round
    rw [hw_eq]; exact hrx_round
  · -- Sub-case 2a: `2^k < x`, `x − y` stays in `x`'s binade.
    have hbot' : (2 : ℝ) ^ k < (x : ℝ) := lt_of_le_of_ne hx_lo (fun h => hbot h.symm)
    have hexk : ex ≤ k := by omega
    set d : ℕ := (k - ex).toNat
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
    have hlogr : Int.log 2 ((x - y : Dyadic) : ℝ) = k :=
      log_eq_of_zpow_bounds hrpos (le_of_lt hr_lo) hr_hi
    have hcE1r : F₁.canonicalExp ((x - y : Dyadic) : ℝ) = ex := by
      rw [cE1 _ hr_ne (by rw [abs_of_pos hrpos]; omega), abs_of_pos hrpos, hlogr]; omega
    have hcE2r : F₂.canonicalExp ((x - y : Dyadic) : ℝ) = k + 1 - (p₂ : ℤ) := by
      rw [canonicalExp_closed hp₂ hr_ne hF2norm, abs_of_pos hrpos, hlogr]
    have herr : |(z : ℝ) - ((x - y : Dyadic) : ℝ)| ≤ (2 : ℝ) ^ (k - (p₂ : ℤ)) := by
      have hh := nearest_error_le_half_ulp hz
      rw [ulp_of_ne_zero F₂ hr_ne, hcE2r] at hh
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
      have hlogz : Int.log 2 (z : ℝ) = k := log_eq_of_zpow_bounds hz_pos (le_of_lt hz_gt) hz_hi
      have hcE1z : F₁.canonicalExp (z : ℝ) = ex := by
        rw [cE1 _ (ne_of_gt hz_pos) (by rw [abs_of_pos hz_pos]; omega),
          abs_of_pos hz_pos, hlogz]; omega
      refine nearest_eq_of_close' F₁ tb₁ _ hundef₁ (by rw [hcE1z]; exact hquant_x_ex) ?_
      rw [hcE1z]
      have e5 : (2 : ℝ) ^ ex / 2 = (2 : ℝ) ^ (ex - 1) := pow_half ex
      rw [e5, abs_lt]; exact ⟨hzx_close.1, hzx_close.2⟩
    have hw_eq : w = x := RoundsFinite.unique hu₁ hw hzx_round
    rw [hw_eq]; exact hrx_round

/-- Small-gap / normal exact fallback: a result `r` fitting `2p₁+1` bits and
inheriting `F₁`'s quantum is exactly `F₂`-representable, so `◦₁(◦₂ r) = ◦₁ r`. -/
private theorem rndSmallGap_exact {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ}
    (hp₂ : F₂.p = (p₂ : Prec)) (hpp : 2 * p₁ + 1 ≤ p₂)
    (hexp : F₂.exp ≤ F₁.exp) {r : Dyadic}
    (hquant_r : Dyadic.quantumAtLeast F₁.exp r)
    (hprec : Dyadic.precisionAtMost ((2 * p₁ + 1 : ℕ) : Prec) r)
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) (r : ℝ) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) (r : ℝ) w := by
  refine rndExact (F₂ := F₂.unbounded)
    (Format.mem_unbounded_of_le (p := ((2 * p₁ + 1 : ℕ) : Prec)) (e := F₁.exp)
      (by rw [hp₂]; exact_mod_cast hpp) hexp hprec hquant_r) hz hw

/-- Subnormal exact fallback: a result `r` that inherits `F₁`'s quantum but is
*subnormal* in `F₂` (precision exponent below `F₂.exp`) is exactly
`F₂`-representable,
so double rounding is a no-op. -/
private theorem rndSubnormal_exact {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₂ : ℕ}
    (hp₂ : F₂.p = (p₂ : Prec)) (hexp : F₂.exp ≤ F₁.exp) {r : Dyadic}
    (hquant_r : Dyadic.quantumAtLeast F₁.exp r)
    (hF2norm : ¬ F₂.exp ≤ ((Int.log 2 |(r : ℝ)| + 1 - (p₂ : ℤ) : ℤ) : QExp))
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) (r : ℝ) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) (r : ℝ) w := by
  obtain ⟨e₂, he₂⟩ : ∃ e : ℤ, F₂.exp = (e : QExp) := by
    cases h : F₂.exp using QExp.recBotCoe with
    | bot => exact absurd (h ▸ bot_le) hF2norm
    | coe e => exact ⟨e, rfl⟩
  rw [he₂] at hF2norm
  have hsublt : Int.log 2 |(r : ℝ)| + 1 - (p₂ : ℤ) < e₂ := by
    by_contra hc; rw [not_lt] at hc; exact hF2norm (by exact_mod_cast hc)
  exact rndExact (F₂ := F₂.unbounded)
    (mem_F₂_of_subnormal hp₂ hexp hquant_r he₂ hsublt) hz hw

/-- **The three cases of Roux Theorem 20.** For a result `r` with `F₁`'s quantum:
in the small-gap case `r` fits `2p₁ + 1` bits, so it is exact in `F₂`; if `r` is
subnormal in `F₂` it is exact there too; otherwise the midpoint argument applies. -/
private theorem rnd_of_cases {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ}
    (hp₂ : F₂.p = (p₂ : Prec)) (hpp : 2 * p₁ + 1 ≤ p₂) (hexp : F₂.exp ≤ F₁.exp)
    {r : Dyadic} (hquant_r : Dyadic.quantumAtLeast F₁.exp r) {small : Prop}
    (hsmall : small → Dyadic.precisionAtMost ((2 * p₁ + 1 : ℕ) : Prec) r)
    {z w : Dyadic}
    (hmid : ¬ small → F₂.exp ≤ ((Int.log 2 |(r : ℝ)| + 1 - (p₂ : ℤ) : ℤ) : QExp) →
      RoundsFinite F₁.unbounded (.nearest tb₁) (r : ℝ) w)
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) (r : ℝ) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) (r : ℝ) w := by
  by_cases hs : small
  · exact rndSmallGap_exact hp₂ hpp hexp hquant_r (hsmall hs) hz hw
  by_cases hF2norm : F₂.exp ≤ ((Int.log 2 |(r : ℝ)| + 1 - (p₂ : ℤ) : ℤ) : QExp)
  · exact hmid hs hF2norm
  · exact rndSubnormal_exact hp₂ hexp hquant_r hF2norm hz hw

/-- **rnd-minus, positive ordered case** (Roux Theorem 20, radix 2, either exponent
regime): for `x, y ∈ F₁` with `0 < y < x`, `p₂ ≥ 2p₁+1` and `F₂.exp ≤ F₁.exp`,
double rounding of `x − y` is innocuous. -/
private theorem rndSub_pos {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ}
    (hp₁ : F₁.p = (p₁ : Prec))
    (hp₂ : F₂.p = (p₂ : Prec))
    (hpp : 2 * p₁ + 1 ≤ p₂)
    (hexp : F₂.exp ≤ F₁.exp)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁)
    (hxpos : 0 < (x : ℝ)) (hypos : 0 < (y : ℝ)) (hyx : (y : ℝ) < (x : ℝ))
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((x - y : Dyadic) : ℝ) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((x - y : Dyadic) : ℝ) w :=
  rnd_of_cases hp₂ hpp hexp (Dyadic.quantumAtLeast_sub hx.2.1 hy.2.1)
    (fun h => (addSub_precisionAtMost hp₁ hx hy hxpos hypos hyx.le h).2)
    (fun h hn => rndSub_pos_normal hp₁ hp₂ hpp hundef₁ hx hy hxpos hypos hyx
      (not_le.mp h) hn hz hw) hz hw

/-- **rnd-plus, ordered positive, genuine-midpoint core** (radix 2, either
exponent regime).
The `x + y` analog of `rndSub_pos_normal`: operand gap `> p₁+1` (`hgap`) and
`x + y` normal in `F₂` (`hF2norm`), so `canonicalExp` takes the precision-exponent
closed form
and Roux's Lemma 16 (`rnd_lt_mid'`) applies unchanged. -/
private theorem rndAdd_pos_normal {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ}
    (hp₁ : F₁.p = (p₁ : Prec))
    (hp₂ : F₂.p = (p₂ : Prec))
    (hpp : 2 * p₁ + 1 ≤ p₂)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁)
    (hxpos : 0 < (x : ℝ)) (hypos : 0 < (y : ℝ))
    (hgap : (p₁ : ℤ) + 1 < F₁.canonicalExp (x : ℝ) - F₁.canonicalExp (y : ℝ))
    (hF2norm : F₂.exp ≤ ((Int.log 2 |((x + y : Dyadic) : ℝ)| + 1 - (p₂ : ℤ) : ℤ) : QExp))
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((x + y : Dyadic) : ℝ) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((x + y : Dyadic) : ℝ) w := by
  have hxypos : 0 < ((x + y : Dyadic) : ℝ) := by rw [Dyadic.coe_real_add]; linarith
  set ex := F₁.canonicalExp (x : ℝ) with hex
  set ey := F₁.canonicalExp (y : ℝ) with hey
  have hp₁ℤ : (1 : ℤ) ≤ (p₁ : ℤ) := by exact_mod_cast F₁.p_pos hp₁
  have hpp' : (2 * (p₁ : ℤ) + 1) ≤ (p₂ : ℤ) := by omega
  obtain ⟨cx, hxeq, -, hcx_le, hex_val, -, -, hy_lt⟩ := gap_setup hp₁ hx hy hxpos hypos hgap
  have hlogx : Int.log 2 (x : ℝ) = ex + (p₁ : ℤ) - 1 := by omega
  -- binade bounds on `x`, and `x ≤ 2^(ex+p₁) − 2^ex`
  have hx_lo : (2 : ℝ) ^ (ex + (p₁ : ℤ) - 1) ≤ (x : ℝ) := by
    rw [← hlogx]; exact Int.zpow_log_le_self (b := 2) (by norm_num) hxpos
  have h2ex : (0 : ℝ) < (2 : ℝ) ^ ex := zpow_pos (by norm_num) _
  have hx_le : (x : ℝ) ≤ (2 : ℝ) ^ (ex + (p₁ : ℤ)) - (2 : ℝ) ^ ex := by
    rw [hxeq, zpow_add₀ two_ne_zero, mul_comm ((2 : ℝ) ^ ex)]
    nlinarith [hcx_le, h2ex]
  -- `x + y` is in `x`'s binade: `2^(ex+p₁-1) ≤ x+y < 2^(ex+p₁)`
  have hxy_lo : (2 : ℝ) ^ (ex + (p₁ : ℤ) - 1) ≤ ((x + y : Dyadic) : ℝ) := by
    rw [Dyadic.coe_real_add]; linarith
  have h2ex2_lt : (2 : ℝ) ^ (ex - 2) < (2 : ℝ) ^ ex :=
    zpow_lt_zpow_right₀ (by norm_num) (by omega)
  have hxy_hi : ((x + y : Dyadic) : ℝ) < (2 : ℝ) ^ (ex + (p₁ : ℤ)) := by
    rw [Dyadic.coe_real_add]; linarith [hx_le, hy_lt, h2ex2_lt]
  have hlogxy : Int.log 2 ((x + y : Dyadic) : ℝ) = ex + (p₁ : ℤ) - 1 :=
    log_eq_of_zpow_bounds hxypos hxy_lo (by rwa [sub_add_cancel])
  -- canonicalExp of `x+y` in `F₁` and `F₂`
  have hcexp₁xy : F₁.canonicalExp ((x + y : Dyadic) : ℝ) = ex := by
    rw [hex]
    exact canonicalExp_eq_of_log_eq F₁ (ne_of_gt hxypos) (ne_of_gt hxpos)
      (by rw [abs_of_pos hxypos, abs_of_pos hxpos, hlogxy, hlogx])
  have hcexp₂xy : F₂.canonicalExp ((x + y : Dyadic) : ℝ) = ex + (p₁ : ℤ) - (p₂ : ℤ) := by
    rw [canonicalExp_closed hp₂ (ne_of_gt hxypos) hF2norm, abs_of_pos hxypos, hlogxy]; ring
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
      rw [midp, ulp_of_ne_zero F₁ hxypos.ne', hrdxy, hcexp₁xy]
    have hulp₂ : ulp F₂ ((x + y : Dyadic) : ℝ) = (2 : ℝ) ^ (ex + (p₁ : ℤ) - (p₂ : ℤ)) := by
      rw [ulp_of_ne_zero F₂ hxypos.ne', hcexp₂xy]
    rw [hmidp, hulp₂, Dyadic.coe_real_add]
    -- y < 2^ex/2 - 2^(ex+p₁-p₂)/2
    have hu2_le : (2 : ℝ) ^ (ex + (p₁ : ℤ) - (p₂ : ℤ)) ≤ (2 : ℝ) ^ (ex - 2) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h2ex2 : (2 : ℝ) ^ (ex - 2) = (2 : ℝ) ^ ex / 4 := by
      rw [show ex - 2 = ex + (-2 : ℤ) from by ring, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0),
          show (2 : ℝ) ^ (-2 : ℤ) = 1 / 4 from by norm_num]
      ring
    linarith [hy_lt, hu2_le, h2ex2, h2ex]

/-- **rnd-plus, positive ordered case** (Roux Theorem 20, radix 2, either exponent
regime): for `x, y ∈ F₁` with `0 < y ≤ x`, `p₂ ≥ 2p₁+1` and `F₂.exp ≤ F₁.exp`,
double rounding of `x + y` is innocuous. -/
private theorem rndAdd_pos {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ}
    (hp₁ : F₁.p = (p₁ : Prec))
    (hp₂ : F₂.p = (p₂ : Prec))
    (hpp : 2 * p₁ + 1 ≤ p₂)
    (hexp : F₂.exp ≤ F₁.exp)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁)
    (hxpos : 0 < (x : ℝ)) (hypos : 0 < (y : ℝ)) (hyx : (y : ℝ) ≤ (x : ℝ))
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((x + y : Dyadic) : ℝ) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((x + y : Dyadic) : ℝ) w :=
  rnd_of_cases hp₂ hpp hexp (Dyadic.quantumAtLeast_add hx.2.1 hy.2.1)
    (fun h => (addSub_precisionAtMost hp₁ hx hy hxpos hypos hyx h).1)
    (fun h hn => rndAdd_pos_normal hp₁ hp₂ hpp hundef₁ hx hy hxpos hypos
      (not_le.mp h) hn hz hw) hz hw

/-- A member of `F₁` (precision `p₁`) is in `F₂.unbounded` when `p₁ ≤ p₂` and
`F₂.exp ≤ F₁.exp` (its quantum carries down). -/
private theorem mem_F₂_unbounded {F₁ F₂ : FiniteFormat} {p₁ p₂ : ℕ}
    (hp₁ : F₁.p = (p₁ : Prec)) (hp₂ : F₂.p = (p₂ : Prec))
    (hexp : F₂.exp ≤ F₁.exp) (hp1p2 : p₁ ≤ p₂)
    {d : Dyadic} (hd : d ∈ F₁) : d ∈ F₂.unbounded :=
  Format.mem_unbounded_of_le (p := F₁.p) (e := F₁.exp)
    (by rw [hp₁, hp₂]; exact_mod_cast hp1p2) hexp hd.1 hd.2.1

/-- Both operands nonnegative: reduce to `rndAdd_pos` (swap if `x < y`; a zero
operand makes the sum exactly representable). -/
private theorem rndAdd_nonneg {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ}
    (hp₁ : F₁.p = (p₁ : Prec))
    (hp₂ : F₂.p = (p₂ : Prec))
    (hpp : 2 * p₁ + 1 ≤ p₂)
    (hexp : F₂.exp ≤ F₁.exp)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁)
    (hxnn : 0 ≤ (x : ℝ)) (hynn : 0 ≤ (y : ℝ))
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((x + y : Dyadic) : ℝ) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((x + y : Dyadic) : ℝ) w := by
  have hp1p2 : p₁ ≤ p₂ := by omega
  rcases eq_or_lt_of_le hxnn with hx0 | hxp
  · -- x = 0
    have hxd : x = 0 :=
      (Dyadic.coe_real_inj x 0).mp (by rw [Dyadic.coe_real_zero]; exact hx0.symm)
    rw [hxd, zero_add] at hz ⊢
    exact rndExact (mem_F₂_unbounded hp₁ hp₂ hexp hp1p2 hy) hz hw
  · rcases eq_or_lt_of_le hynn with hy0 | hyp
    · -- y = 0
      have hyd : y = 0 :=
        (Dyadic.coe_real_inj y 0).mp (by rw [Dyadic.coe_real_zero]; exact hy0.symm)
      rw [hyd, add_zero] at hz ⊢
      exact rndExact (mem_F₂_unbounded hp₁ hp₂ hexp hp1p2 hx) hz hw
    · rcases le_total (y : ℝ) (x : ℝ) with hyx | hxy
      · exact rndAdd_pos hp₁ hp₂ hpp hexp hundef₁ hx hy hxp hyp hyx hz hw
      · rw [show (x + y : Dyadic) = y + x from add_comm x y] at hz ⊢
        exact rndAdd_pos hp₁ hp₂ hpp hexp hundef₁ hy hx hyp hxp hxy hz hw

/-- **rnd-difference, nonnegative operands** (Roux Theorem 20, radix 2). With
`F₁ = 𝒜(p₁, exp₁, b₁)` and `F₂ = 𝒜(p₂, exp₂, b₂)`, double rounding to nearest of
`a − b` (`a, b ∈ F₁`, `0 ≤ a`, `0 ≤ b`) is innocuous when

* **precision:** `p₂ ≥ 2·p₁ + 1`,
* **exponent:** `exp₂ ≤ exp₁` (covers `⊥ ≤ ⊥` and `emin₂ ≤ emin₁`),
* **bounds:** no relationship required (overflow-free `unbounded` roundings).

The exponent condition `exp₂ ≤ exp₁` is exactly the *quantum half* of `F₁ ⊆ F₂`
(`𝒜-Contains-Prec`): `F₂` is at least as fine as `F₁`. The `2p₁+1`-bit exact
difference is either `F₂`-representable (a zero operand or `a = b`, exact case)
or pinned by the midpoint argument. -/
theorem rndDiff {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ}
    (hp₁ : F₁.p = (p₁ : Prec))
    (hp₂ : F₂.p = (p₂ : Prec))
    (hpp : 2 * p₁ + 1 ≤ p₂)
    (hexp : F₂.exp ≤ F₁.exp)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {a b : Dyadic} (ha : a ∈ F₁) (hb : b ∈ F₁)
    (hann : 0 ≤ (a : ℝ)) (hbnn : 0 ≤ (b : ℝ))
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((a - b : Dyadic) : ℝ) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((a - b : Dyadic) : ℝ) w := by
  have hp1p2 : p₁ ≤ p₂ := by omega
  by_cases hab_mem : (a - b : Dyadic) ∈ F₁
  · -- `a − b` is representable in `F₁` (a zero operand, or `a = b`): exact.
    exact rndExact (mem_F₂_unbounded hp₁ hp₂ hexp hp1p2 hab_mem) hz hw
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
    have hnegval : -((a - b : Dyadic) : ℝ) = ((b - a : Dyadic) : ℝ) := by push_cast; ring
    rcases lt_or_gt_of_ne habne with hab | hab
    · -- `a < b`: negate to `b − a > 0` and apply `rndSub_pos`.
      refine rndNeg hz hw (fun z' w' hz' hw' => ?_)
      rw [hnegval] at hz' ⊢
      exact rndSub_pos hp₁ hp₂ hpp hexp hundef₁ hb ha hbp hap hab hz' hw'
    · -- `a > b`: apply `rndSub_pos` directly.
      exact rndSub_pos hp₁ hp₂ hpp hexp hundef₁ ha hb hap hbp hab hz hw

/-- **rnd-plus** (Roux Theorem 20, radix 2, **either exponent regime**). With
`F₁ = 𝒜(p₁, exp₁, b₁)` and `F₂ = 𝒜(p₂, exp₂, b₂)`, double rounding to nearest of
`x + y` for **arbitrary** `x, y ∈ F₁` is innocuous when

* **precision:** `p₂ ≥ 2·p₁ + 1`,
* **exponent:** `exp₂ ≤ exp₁` (subsumes `⊥ ≤ ⊥` and `emin₂ ≤ emin₁`),
* **bounds:** no relationship required (overflow-free `unbounded` roundings).

`exp₂ ≤ exp₁` is the *quantum half* of `F₁ ⊆ F₂` (`𝒜-Contains-Prec`): `F₂` is at
least as fine as `F₁`. Same-sign operands reduce to `rndAdd_nonneg` (both
nonpositive by joint negation); mixed signs are a subtraction handled by
`rndDiff`. Matches Flocq's `round_round_plus_FLX`/`round_round_plus_FLT`. -/
theorem rndAdd {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ}
    (hp₁ : F₁.p = (p₁ : Prec))
    (hp₂ : F₂.p = (p₂ : Prec))
    (hpp : 2 * p₁ + 1 ≤ p₂)
    (hexp : F₂.exp ≤ F₁.exp)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {x y : Dyadic} (hx : x ∈ F₁) (hy : y ∈ F₁)
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((x + y : Dyadic) : ℝ) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((x + y : Dyadic) : ℝ) w := by
  rcases (lt_or_ge (x : ℝ) 0).symm with hxnn | hxneg
  · rcases (lt_or_ge (y : ℝ) 0).symm with hynn | hyneg
    · -- both nonnegative
      exact rndAdd_nonneg hp₁ hp₂ hpp hexp hundef₁ hx hy hxnn hynn hz hw
    · -- `x ≥ 0 > y`: `x + y = x − (−y)`
      have hb : (-y) ∈ F₁ := FiniteFormat.neg_mem hy
      have hbnn : 0 ≤ ((-y : Dyadic) : ℝ) := by rw [Dyadic.coe_real_neg]; linarith
      rw [show (x + y : Dyadic) = x - (-y) from by ring] at hz ⊢
      exact rndDiff hp₁ hp₂ hpp hexp hundef₁ hx hb hxnn hbnn hz hw
  · rcases (lt_or_ge (y : ℝ) 0).symm with hynn | hyneg
    · -- `x < 0 ≤ y`: `x + y = y − (−x)`
      have hb : (-x) ∈ F₁ := FiniteFormat.neg_mem hx
      have hbnn : 0 ≤ ((-x : Dyadic) : ℝ) := by rw [Dyadic.coe_real_neg]; linarith
      rw [show (x + y : Dyadic) = y - (-x) from by ring] at hz ⊢
      exact rndDiff hp₁ hp₂ hpp hexp hundef₁ hy hb hynn hbnn hz hw
    · -- both nonpositive: joint negation reduces to `rndAdd_nonneg`
      have hnx : (-x) ∈ F₁ := FiniteFormat.neg_mem hx
      have hny : (-y) ∈ F₁ := FiniteFormat.neg_mem hy
      have hnxnn : 0 ≤ ((-x : Dyadic) : ℝ) := by rw [Dyadic.coe_real_neg]; linarith
      have hnynn : 0 ≤ ((-y : Dyadic) : ℝ) := by rw [Dyadic.coe_real_neg]; linarith
      have hnegval : -((x + y : Dyadic) : ℝ) = (((-x) + (-y) : Dyadic) : ℝ) := by push_cast; ring
      refine rndNeg hz hw (fun z' w' hz' hw' => ?_)
      rw [hnegval] at hz' ⊢
      exact rndAdd_nonneg hp₁ hp₂ hpp hexp hundef₁ hnx hny hnxnn hnynn hz' hw'

end Mpfx
