import Mpfx.CanonicalExp
import Mpfx.NearestMidpoint
import Mpfx.DoubleRoundingMul
import Mpfx.DoubleRoundingAdd

/-!
# Operation-specific double rounding: square root (Roux 2014, Theorem 25)

Roux's Theorem 25 (radix 2, FLX): double rounding of `√x` is innocuous when
`p₂ ≥ 2p₁ + 2`. Unlike `×`/`+`, the result `√x` is generally irrational — but
`RoundsFinite` rounds a *real*, so the statement simply takes `Real.sqrt x` as
the value and leans on the two-sided midpoint engine (`round_round_mid_cases`).
The new mathematical content is the *separation lemma* `round_round_sqrt_aux`:
`√x` is never within `½·ulp₂` of an `F₁`-midpoint. `rndSqrt_FLX` and `rndSqrt_FLT`
assemble it (via the shared `rndSqrt_core`) for the two format configurations.
-/

namespace Mpfx

/-- **Binade of a square root** (Flocq `mag_sqrt_disj`). For `0 < x`, writing
`L = Int.log 2 (√x)`, the binade of `x` is `2L` or `2L+1`:
`2L ≤ Int.log 2 x ≤ 2L+1`. Equivalently `Int.log 2 (√x) = ⌊(Int.log 2 x)/2⌋`.
Proof: square the defining bounds `2^L ≤ √x < 2^(L+1)` to get
`2^(2L) ≤ x < 2^(2L+2)`, then read off `Int.log 2 x`. -/
private theorem log_sqrt_bounds {x : ℝ} (hx : 0 < x) :
    2 * Int.log 2 (Real.sqrt x) ≤ Int.log 2 x ∧
      Int.log 2 x ≤ 2 * Int.log 2 (Real.sqrt x) + 1 := by
  set L := Int.log 2 (Real.sqrt x) with hL
  have hne : (2 : ℝ) ≠ 0 := by norm_num
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  -- `2^L ≤ √x < 2^(L+1)` (definition of `Int.log`)
  have hlo : (2 : ℝ) ^ L ≤ Real.sqrt x := by
    have := Int.zpow_log_le_self (b := 2) (by norm_num) hsx
    rw [← hL] at this; exact_mod_cast this
  have hhi : Real.sqrt x < (2 : ℝ) ^ (L + 1) := by
    have := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) (Real.sqrt x)
    rw [← hL] at this; exact_mod_cast this
  -- square: `2^(2L) ≤ x < 2^(2L+2)`
  have hx_lo : (2 : ℝ) ^ (2 * L) ≤ x := by
    have he : ((2 : ℝ) ^ L) ^ 2 = (2 : ℝ) ^ (2 * L) := by
      rw [pow_two, ← zpow_add₀ hne]; congr 1; ring
    have h : ((2 : ℝ) ^ L) ^ 2 ≤ (Real.sqrt x) ^ 2 := by gcongr
    rw [he, hsq] at h; exact h
  have hx_hi : x < (2 : ℝ) ^ (2 * L + 2) := by
    have he : ((2 : ℝ) ^ (L + 1)) ^ 2 = (2 : ℝ) ^ (2 * L + 2) := by
      rw [pow_two, ← zpow_add₀ hne]; congr 1; ring
    have h : (Real.sqrt x) ^ 2 < ((2 : ℝ) ^ (L + 1)) ^ 2 := by gcongr
    rw [hsq, he] at h; exact h
  -- read off `Int.log 2 x`
  have h1 : 2 * L ≤ Int.log 2 x :=
    (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hx).mp (by exact_mod_cast hx_lo)
  have h2 : Int.log 2 x < 2 * L + 2 :=
    (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hx).mp (by exact_mod_cast hx_hi)
  omega

/-- **Square-root separation lemma** (Flocq `round_round_sqrt_aux`, the Figueroa
argument). If the radicand `x` is representable in `F₁` (`hxrep`), `√x`'s binade
is not too small (`hle`), the coarse/fine precision gap is right (`hf1`, and the
quantitative `hquant` — Roux's `p₂ ≥ 2p₁+2`), then `√x` is *never* within
`½·ulp₂` of its `F₁`-midpoint.

Proof: suppose it is. With `a = rndDown₁ √x`, `u₁ = 2^e₁`, `u₂ = 2^e₂`, the
assumption puts `a + ½(u₁−u₂) ≤ √x ≤ a + ½(u₁+u₂)`. Squaring (using `x = (√x)²`)
traps `x` strictly between `A := a²+u₁a` and `A + u₁²`, where — because `a` is an
`F₁` multiple of `2^e₁` and `x` is an `F₁` multiple of `2^(canonicalExp₁ x)` with
`canonicalExp₁ x ≥ 2e₁` — both `A` and `x` are integer multiples of `M := 2^(2e₁)
= u₁²`. A multiple of `M` cannot lie strictly between `A` and `A + M`. -/
private theorem round_round_sqrt_aux {F₁ F₂ : FiniteFormat} {x : ℝ} (hx : 0 < x)
    (hxrep : ∃ mx : ℤ, x = (mx : ℝ) * (2 : ℝ) ^ (F₁.canonicalExp x))
    (hf1 : 2 * F₁.canonicalExp (Real.sqrt x) ≤ F₁.canonicalExp x)
    (hle : F₁.canonicalExp (Real.sqrt x) ≤ Int.log 2 (Real.sqrt x) + 1)
    (hquant : F₂.canonicalExp (Real.sqrt x) + Int.log 2 (Real.sqrt x) + 1
                ≤ 2 * F₁.canonicalExp (Real.sqrt x) - 2) :
    ulp F₂ (Real.sqrt x) / 2 < |Real.sqrt x - midp F₁ (Real.sqrt x)| := by
  set s := Real.sqrt x
  have hne : (2 : ℝ) ≠ 0 := by norm_num
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hx
  have hsq : s ^ 2 = x := Real.sq_sqrt hx.le
  set e₁ := F₁.canonicalExp s with he₁
  set e₂ := F₂.canonicalExp s with he₂
  set k := Int.log 2 s with hk
  have he₂_le : e₂ ≤ e₁ - 2 := by omega
  have hu1_pos : (0 : ℝ) < (2 : ℝ) ^ e₁ := zpow_pos (by norm_num) _
  have hu2_pos : (0 : ℝ) < (2 : ℝ) ^ e₂ := zpow_pos (by norm_num) _
  -- binade of `s`
  have hk_lo : (2 : ℝ) ^ k ≤ s := by
    have := Int.zpow_log_le_self (b := 2) (by norm_num) hs_pos
    rw [← hk] at this; exact_mod_cast this
  have hk_hi : s < (2 : ℝ) ^ (k + 1) := by
    have := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) s
    rw [← hk] at this; exact_mod_cast this
  -- `a = rndDown₁ s = ma · 2^e₁`
  set ma : ℤ := ⌊s * (2 : ℝ) ^ (-e₁)⌋ with hma
  set a : ℝ := (ma : ℝ) * (2 : ℝ) ^ e₁ with ha
  have ha_eq : (rndDown F₁ s : ℝ) = a := by
    rw [rndDown_eq, Dyadic.coe_ofIntZpow, ← he₁, ← hma]
  have hma_nonneg : 0 ≤ ma := Int.floor_nonneg.mpr (by positivity)
  have ha_nonneg : 0 ≤ a := by
    rw [ha]; exact mul_nonneg (by exact_mod_cast hma_nonneg) hu1_pos.le
  have ha_le : a ≤ s := ha_eq ▸ rndDown_le F₁ s
  have hk_hi_a : a < (2 : ℝ) ^ (k + 1) := lt_of_le_of_lt ha_le hk_hi
  -- make `ma`/`a` opaque so later `linarith`/`ring` don't unfold `⌊·⌋`
  clear_value ma a
  -- `a + u₁ ≤ 2^(k+1)` (the round-down plus its ulp stays under the binade top)
  have ha_top : a + (2 : ℝ) ^ e₁ ≤ (2 : ℝ) ^ (k + 1) := by
    have hd : (0 : ℤ) ≤ k + 1 - e₁ := by omega
    have hmaR : (ma : ℝ) < (2 : ℝ) ^ (k + 1 - e₁) := by
      have hlt : (ma : ℝ) * (2 : ℝ) ^ e₁ < (2 : ℝ) ^ (k + 1 - e₁) * (2 : ℝ) ^ e₁ := by
        rw [← zpow_add₀ hne, show (k + 1 - e₁) + e₁ = k + 1 from by ring, ← ha]; exact hk_hi_a
      exact lt_of_mul_lt_mul_right hlt hu1_pos.le
    have hcast : ((2 : ℤ) ^ (k + 1 - e₁).toNat : ℝ) = (2 : ℝ) ^ (k + 1 - e₁) := by
      rw [← zpow_natCast]; congr 1; rw [Int.toNat_of_nonneg hd]
    have hmaZ : ma + 1 ≤ (2 : ℤ) ^ (k + 1 - e₁).toNat := by
      have : (ma : ℝ) < ((2 : ℤ) ^ (k + 1 - e₁).toNat : ℝ) := by rw [hcast]; exact hmaR
      have : ma < (2 : ℤ) ^ (k + 1 - e₁).toNat := by exact_mod_cast this
      omega
    have hstep : ((ma : ℝ) + 1) ≤ (2 : ℝ) ^ (k + 1 - e₁) := by
      rw [← hcast]; exact_mod_cast hmaZ
    calc a + (2 : ℝ) ^ e₁ = ((ma : ℝ) + 1) * (2 : ℝ) ^ e₁ := by rw [ha]; ring
      _ ≤ (2 : ℝ) ^ (k + 1 - e₁) * (2 : ℝ) ^ e₁ :=
          mul_le_mul_of_nonneg_right hstep hu1_pos.le
      _ = (2 : ℝ) ^ (k + 1) := by rw [← zpow_add₀ hne]; congr 1; ring
  -- `u₂ ≤ u₁/2`
  have hu2_le_half : (2 : ℝ) ^ e₂ ≤ (2 : ℝ) ^ e₁ / 2 := by
    have h1 : (2 : ℝ) ^ e₂ ≤ (2 : ℝ) ^ (e₁ - 1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith [h1, two_zpow_half e₁]
  -- quantitative bound `u₂·2^(k+1) ≤ u₁²/4`
  have hqbound : (2 : ℝ) ^ e₂ * (2 : ℝ) ^ (k + 1) ≤ ((2 : ℝ) ^ e₁) ^ 2 / 4 := by
    have h1 : (2 : ℝ) ^ e₂ * (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ (e₂ + (k + 1)) := by
      rw [← zpow_add₀ hne]
    have h2 : (2 : ℝ) ^ (e₂ + (k + 1)) ≤ (2 : ℝ) ^ (2 * e₁ - 2) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h3 : (2 : ℝ) ^ (2 * e₁ - 2) = ((2 : ℝ) ^ e₁) ^ 2 / 4 := by
      rw [show (2 * e₁ - 2 : ℤ) = e₁ + e₁ + (-2) from by ring, zpow_add₀ hne, zpow_add₀ hne,
          show (2 : ℝ) ^ (-2 : ℤ) = 1 / 4 from by norm_num, pow_two]; ring
    rw [h1]; linarith [h2, h3]
  by_contra hcon
  rw [not_lt] at hcon
  have hmidp : midp F₁ s = a + (2 : ℝ) ^ e₁ / 2 := by unfold midp ulp; rw [ha_eq, ← he₁]
  rw [show ulp F₂ s = (2 : ℝ) ^ e₂ from by unfold ulp; rw [← he₂], hmidp, abs_le] at hcon
  -- `a + ½(u₁−u₂) ≤ s ≤ a + ½(u₁+u₂)`
  have hsl : a + ((2 : ℝ) ^ e₁ - (2 : ℝ) ^ e₂) / 2 ≤ s := by linarith [hcon.1]
  have hsr : s ≤ a + ((2 : ℝ) ^ e₁ + (2 : ℝ) ^ e₂) / 2 := by linarith [hcon.2]
  have hb_nonneg : 0 ≤ a + ((2 : ℝ) ^ e₁ - (2 : ℝ) ^ e₂) / 2 := by
    have : (2 : ℝ) ^ e₂ ≤ (2 : ℝ) ^ e₁ := zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith [ha_nonneg]
  -- square to bound `x`
  have hlow : (a + ((2 : ℝ) ^ e₁ - (2 : ℝ) ^ e₂) / 2) ^ 2 ≤ x := by
    rw [← hsq]; gcongr
  have hupp : x ≤ (a + ((2 : ℝ) ^ e₁ + (2 : ℝ) ^ e₂) / 2) ^ 2 := by
    rw [← hsq]; gcongr
  set A : ℝ := a ^ 2 + (2 : ℝ) ^ e₁ * a with hAdef
  set M : ℝ := (2 : ℝ) ^ (2 * e₁) with hMdef
  have hMpos : (0 : ℝ) < M := zpow_pos (by norm_num) _
  have hMu1 : M = ((2 : ℝ) ^ e₁) ^ 2 := by
    rw [hMdef, pow_two, show (2 * e₁ : ℤ) = e₁ + e₁ from by ring, zpow_add₀ hne]
  clear_value A M
  -- lower / upper separations
  have hHl' : (2 : ℝ) ^ e₂ * a < (((2 : ℝ) ^ e₁ - (2 : ℝ) ^ e₂) / 2) ^ 2 := by
    have haU : a + (2 : ℝ) ^ e₁ / 2 < (2 : ℝ) ^ (k + 1) := by linarith [ha_top, hu1_pos]
    have hbound1 : (2 : ℝ) ^ e₂ * (a + (2 : ℝ) ^ e₁ / 2) < ((2 : ℝ) ^ e₁) ^ 2 / 4 := by
      have := mul_lt_mul_of_pos_left haU hu2_pos
      linarith [this, hqbound]
    nlinarith [hbound1, sq_nonneg ((2 : ℝ) ^ e₂)]
  have hbound2 : (2 : ℝ) ^ e₂ * a < ((2 : ℝ) ^ e₁) ^ 2 / 4 := by
    have := mul_lt_mul_of_pos_left hk_hi_a hu2_pos
    linarith [this, hqbound]
  have hIII : (2 : ℝ) ^ e₂ * a + (((2 : ℝ) ^ e₁ + (2 : ℝ) ^ e₂) / 2) ^ 2 < M := by
    rw [hMu1]
    nlinarith [hbound2, hu2_le_half, hu1_pos, hu2_pos]
  -- `A < x < A + M`
  have hpos : A < x := by
    have e : (a + ((2 : ℝ) ^ e₁ - (2 : ℝ) ^ e₂) / 2) ^ 2
        = A - (2 : ℝ) ^ e₂ * a + (((2 : ℝ) ^ e₁ - (2 : ℝ) ^ e₂) / 2) ^ 2 := by rw [hAdef]; ring
    linarith [hlow, hHl', e]
  have hupp'x : x < A + M := by
    have e : (a + ((2 : ℝ) ^ e₁ + (2 : ℝ) ^ e₂) / 2) ^ 2
        = A + ((2 : ℝ) ^ e₂ * a + (((2 : ℝ) ^ e₁ + (2 : ℝ) ^ e₂) / 2) ^ 2) := by rw [hAdef]; ring
    linarith [hupp, hIII, e]
  -- divisibility: `A` and `x` are integer multiples of `M = 2^(2e₁)`
  have hAeq : A = ((ma * (ma + 1) : ℤ) : ℝ) * M := by
    rw [hAdef, ha, hMdef, show (2 * e₁ : ℤ) = e₁ + e₁ from by ring, zpow_add₀ hne]
    push_cast; ring
  have hxdvis : ∃ X : ℤ, x = (X : ℝ) * M := by
    obtain ⟨mx, hmx⟩ := hxrep
    have hd : (0 : ℤ) ≤ F₁.canonicalExp x - 2 * e₁ := by omega
    refine ⟨mx * 2 ^ (F₁.canonicalExp x - 2 * e₁).toNat, ?_⟩
    have key : ((mx * 2 ^ (F₁.canonicalExp x - 2 * e₁).toNat : ℤ) : ℝ) * M
        = (mx : ℝ) * (2 : ℝ) ^ F₁.canonicalExp x := by
      rw [hMdef]; push_cast
      rw [mul_assoc, ← zpow_natCast (2 : ℝ) (F₁.canonicalExp x - 2 * e₁).toNat,
          Int.toNat_of_nonneg hd, ← zpow_add₀ hne,
          show (F₁.canonicalExp x - 2 * e₁) + 2 * e₁ = F₁.canonicalExp x from by ring]
    rw [key]; exact hmx
  obtain ⟨X, hX⟩ := hxdvis
  rw [hAeq, hX] at hpos hupp'x
  have h1 : ma * (ma + 1) < X := by
    have := lt_of_mul_lt_mul_right hpos hMpos.le; exact_mod_cast this
  have h2 : X ≤ ma * (ma + 1) := by
    have he : ((ma * (ma + 1) : ℤ) : ℝ) * M + M = (((ma * (ma + 1) + 1 : ℤ)) : ℝ) * M := by
      push_cast; ring
    rw [he] at hupp'x
    have : X < ma * (ma + 1) + 1 := by
      have := lt_of_mul_lt_mul_right hupp'x hMpos.le; exact_mod_cast this
    omega
  omega

/-- **rnd-sqrt core.** The format-agnostic assembly: given the exact-radicand
`hxrep` and the three canonical-exponent relations at `√x`
(`hf1`, `hle`, `hquant`) that a valid precision/underflow choice supplies,
double rounding of `√x` is innocuous. `round_round_mid_cases` reduces to the
near-midpoint obligation, discharged by `round_round_sqrt_aux`; the strict
`h21` (`F₂` finer than `F₁` at `√x`) follows from `hquant` and `hle`. -/
private theorem rndSqrt_core {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {x : ℝ}
    (hx : 0 < x)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    (hxrep : ∃ mx : ℤ, x = (mx : ℝ) * (2 : ℝ) ^ (F₁.canonicalExp x))
    (hf1 : 2 * F₁.canonicalExp (Real.sqrt x) ≤ F₁.canonicalExp x)
    (hle : F₁.canonicalExp (Real.sqrt x) ≤ Int.log 2 (Real.sqrt x) + 1)
    (hquant : F₂.canonicalExp (Real.sqrt x) + Int.log 2 (Real.sqrt x) + 1
                ≤ 2 * F₁.canonicalExp (Real.sqrt x) - 2)
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) (Real.sqrt x) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) (Real.sqrt x) w :=
  round_round_mid_cases hundef₁ (Real.sqrt_pos.mpr hx) (by omega) hle hz hw
    (fun hmid => absurd hmid (not_le.mpr (round_round_sqrt_aux hx hxrep hf1 hle hquant)))

/-- Degenerate radicand `x = 0`: `√0 = 0` rounds to `0` in both formats, so double
rounding is trivially innocuous. -/
private theorem rndSqrt_zero {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {x : Dyadic}
    (hx0 : (0 : ℝ) = (x : ℝ))
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) (Real.sqrt (x : ℝ)) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) (Real.sqrt (x : ℝ)) w := by
  rw [← hx0, Real.sqrt_zero, show (0 : ℝ) = ((0 : Dyadic) : ℝ) from by simp] at hz ⊢
  exact rndExact (F₁ := F₁.unbounded) (F₂ := F₂.unbounded)
    (FiniteFormat.zero_mem F₂.unbounded) hz hw

/-- **rnd-sqrt, FLX** (Roux Theorem 25, radix 2). With FLX formats
`F₁ = 𝒜(p₁, ⊥, b₁)` and `F₂ = 𝒜(p₂, ⊥, b₂)`, double rounding to nearest of `√x`
(`x ∈ F₁`, `0 ≤ x`) is innocuous when

* **precision:** `p₂ ≥ 2·p₁ + 2`,
* **exponent:** both `⊥` (FLX),
* **bounds:** no relationship required (overflow-free `unbounded` roundings).

Unlike `×`/`+`, `√x` is generally irrational, so this is a precision *margin*
(with `2p₁+2` bits `√x` never lands near an `F₁`-midpoint), not exact containment
of a result format. -/
theorem rndSqrt_FLX {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ+}
    (hp₁ : F₁.p = ((p₁ : ℕ+) : WithTop ℕ+)) (hp₂ : F₂.p = ((p₂ : ℕ+) : WithTop ℕ+))
    (hpp : (2 * p₁ + 2 : ℕ+) ≤ p₂)
    (hexp₁ : F₁.exp = ⊥) (hexp₂ : F₂.exp = ⊥)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {x : Dyadic} (hx : x ∈ F₁) (hxpos : 0 ≤ (x : ℝ))
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) (Real.sqrt (x : ℝ)) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) (Real.sqrt (x : ℝ)) w := by
  rcases eq_or_lt_of_le hxpos with hx0 | hxpos
  · exact rndSqrt_zero hx0 hz hw
  have hs_pos : 0 < Real.sqrt (x : ℝ) := Real.sqrt_pos.mpr hxpos
  have habs : |Real.sqrt (x : ℝ)| = Real.sqrt (x : ℝ) := abs_of_pos hs_pos
  have hp₁ℤ : (1 : ℤ) ≤ (p₁ : ℤ) := by exact_mod_cast p₁.one_le
  have hpp' : 2 * (p₁ : ℤ) + 2 ≤ (p₂ : ℤ) := by
    have : ((2 * p₁ + 2 : ℕ+) : ℤ) ≤ ((p₂ : ℕ+) : ℤ) := by exact_mod_cast hpp
    push_cast at this; omega
  obtain ⟨hloglo, hloghi⟩ := log_sqrt_bounds hxpos
  have hxrep : ∃ mx : ℤ, (x : ℝ) = (mx : ℝ) * (2 : ℝ) ^ (F₁.canonicalExp (x : ℝ)) := by
    obtain ⟨c, _, hc⟩ := exists_canonical_rep F₁ hp₁ hx hxpos; exact ⟨c, hc⟩
  have hcE1s : F₁.canonicalExp (Real.sqrt (x : ℝ))
      = Int.log 2 (Real.sqrt (x : ℝ)) + 1 - (p₁ : ℤ) := by
    rw [canonicalExp_FLX hp₁ hexp₁ (ne_of_gt hs_pos), habs]
  have hcE2s : F₂.canonicalExp (Real.sqrt (x : ℝ))
      = Int.log 2 (Real.sqrt (x : ℝ)) + 1 - (p₂ : ℤ) := by
    rw [canonicalExp_FLX hp₂ hexp₂ (ne_of_gt hs_pos), habs]
  have hcE1x : F₁.canonicalExp (x : ℝ) = Int.log 2 (x : ℝ) + 1 - (p₁ : ℤ) := by
    rw [canonicalExp_FLX hp₁ hexp₁ (ne_of_gt hxpos), abs_of_pos hxpos]
  refine rndSqrt_core hxpos hundef₁ hxrep ?_ ?_ ?_ hz hw
  · rw [hcE1s, hcE1x]; omega
  · rw [hcE1s]; omega
  · rw [hcE1s, hcE2s]; omega

/-- **rnd-sqrt, FLT** (Roux Theorem 25, radix 2). With FLT formats
`F₁ = 𝒜(p₁, emin₁, b₁)` and `F₂ = 𝒜(p₂, emin₂, b₂)`, double rounding to nearest of
`√x` (`x ∈ F₁`, `0 ≤ x`) is innocuous when

* **precision:** `p₂ ≥ 2·p₁ + 2`,
* **exponent:** `emin₁ ≤ 0` and the Table-II underflow bound
  `emin₂ ≤ emin₁ − p₁ − 2  ∨  2·emin₂ ≤ emin₁ − 4·p₁ − 2`,
* **bounds:** no relationship required (overflow-free `unbounded` roundings).

A precision + underflow *margin* (not exact containment — `√x` is generally
irrational). -/
theorem rndSqrt_FLT {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ+}
    {emin₁ emin₂ : ℤ}
    (hp₁ : F₁.p = ((p₁ : ℕ+) : WithTop ℕ+)) (hp₂ : F₂.p = ((p₂ : ℕ+) : WithTop ℕ+))
    (hpp : (2 * p₁ + 2 : ℕ+) ≤ p₂)
    (hexp₁ : F₁.exp = (emin₁ : WithBot ℤ)) (hexp₂ : F₂.exp = (emin₂ : WithBot ℤ))
    (hemin1 : emin₁ ≤ 0)
    (hE : emin₂ ≤ emin₁ - (p₁ : ℤ) - 2 ∨ 2 * emin₂ ≤ emin₁ - 4 * (p₁ : ℤ) - 2)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {x : Dyadic} (hx : x ∈ F₁) (hxpos : 0 ≤ (x : ℝ))
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) (Real.sqrt (x : ℝ)) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) (Real.sqrt (x : ℝ)) w := by
  rcases eq_or_lt_of_le hxpos with hx0 | hxpos
  · exact rndSqrt_zero hx0 hz hw
  have hs_pos : 0 < Real.sqrt (x : ℝ) := Real.sqrt_pos.mpr hxpos
  have habs : |Real.sqrt (x : ℝ)| = Real.sqrt (x : ℝ) := abs_of_pos hs_pos
  have hp₁ℤ : (1 : ℤ) ≤ (p₁ : ℤ) := by exact_mod_cast p₁.one_le
  have hpp' : 2 * (p₁ : ℤ) + 2 ≤ (p₂ : ℤ) := by
    have : ((2 * p₁ + 2 : ℕ+) : ℤ) ≤ ((p₂ : ℕ+) : ℤ) := by exact_mod_cast hpp
    push_cast at this; omega
  obtain ⟨hloglo, hloghi⟩ := log_sqrt_bounds hxpos
  have hxrep : ∃ mx : ℤ, (x : ℝ) = (mx : ℝ) * (2 : ℝ) ^ (F₁.canonicalExp (x : ℝ)) := by
    obtain ⟨c, _, hc⟩ := exists_canonical_rep F₁ hp₁ hx hxpos; exact ⟨c, hc⟩
  have hx_ge : (2 : ℝ) ^ emin₁ ≤ (x : ℝ) := by
    obtain ⟨c, hc⟩ := (Dyadic.quantumAtLeast_coe_real emin₁ x).mp (hexp₁ ▸ hx.2.1)
    have h2 : (0 : ℝ) < (2 : ℝ) ^ emin₁ := zpow_pos (by norm_num) _
    have hc_pos : 0 < c := by
      rcases lt_or_ge 0 c with h | h
      · exact h
      · exfalso
        have : (x : ℝ) ≤ 0 := by
          rw [hc]; exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h) h2.le
        linarith [hxpos]
    have hc1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc_pos
    rw [hc]; nlinarith [h2, hc1]
  have hLge : emin₁ ≤ Int.log 2 (x : ℝ) :=
    (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hxpos).mp (by exact_mod_cast hx_ge)
  have hcE1s : F₁.canonicalExp (Real.sqrt (x : ℝ))
      = max (Int.log 2 (Real.sqrt (x : ℝ)) + 1 - (p₁ : ℤ)) emin₁ := by
    rw [canonicalExp_FLT hp₁ hexp₁ (ne_of_gt hs_pos), habs]
  have hcE2s : F₂.canonicalExp (Real.sqrt (x : ℝ))
      = max (Int.log 2 (Real.sqrt (x : ℝ)) + 1 - (p₂ : ℤ)) emin₂ := by
    rw [canonicalExp_FLT hp₂ hexp₂ (ne_of_gt hs_pos), habs]
  have hcE1x : F₁.canonicalExp (x : ℝ) = max (Int.log 2 (x : ℝ) + 1 - (p₁ : ℤ)) emin₁ := by
    rw [canonicalExp_FLT hp₁ hexp₁ (ne_of_gt hxpos), abs_of_pos hxpos]
  refine rndSqrt_core hxpos hundef₁ hxrep ?_ ?_ ?_ hz hw
  · rw [hcE1s, hcE1x]; omega
  · rw [hcE1s]; omega
  · rw [hcE1s, hcE2s]; rcases hE with h | h <;> omega

end Mpfx
