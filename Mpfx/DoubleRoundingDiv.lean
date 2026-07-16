import Mpfx.CanonicalExp
import Mpfx.NearestMidpoint
import Mpfx.DoubleRoundingOps
import Mpfx.DoubleRoundingAdd

/-!
# Operation-specific double rounding: division (Roux 2014, Theorem 29)

Roux's Theorem 29 (radix 2 — more generally *even* radix): double rounding of
`x / y` is innocuous when `p₂ ≥ 2p₁` (the same bound as multiplication, and
tight — Remark 30 gives a counterexample at `p₂ = 2p₁ − 1`). Odd radices need a
directed tie-break and are out of scope for this format.

Like `√`, the quotient is generally irrational, so the statement takes `x / y`
as a real and leans on the two-sided midpoint engine (`round_round_mid_cases`).
The new subtlety vs `√`: `x / y` **can** land exactly on an `F₁`-midpoint `m`.
The near-midpoint obligation therefore splits:

* `x / y ≠ m` but within `½·ulp₂` of it — *impossible*, by a separation argument
  analogous to `round_round_sqrt_aux` (`round_round_div_aux`, still to port); and
* `x / y = m` exactly — here the **even radix** makes `m ∈ F₂` (its canonical
  exponent drops by ≥ 1, absorbing the trailing `½·ulp₁`), so the intermediate
  rounding is exact (`round_round_eq_mid_beta_even`, still to port).

Status: `log_div_bounds` (binade lemma, Flocq `mag_div_disj`) is proved below;
the separation lemma, the even-radix exact-midpoint lemma, the `rndDiv` assembly
and the FLT variant remain (see `docs/agents/DOUBLE_ROUNDING_OPS_PLAN.md` §Division).
-/

namespace Mpfx

/-- **Binade of a quotient** (Flocq `mag_div_disj`). For `0 < x`, `0 < y`, the
binade of `x / y` is `Int.log 2 x − Int.log 2 y` or one less:
`Lx − Ly − 1 ≤ Int.log 2 (x / y) ≤ Lx − Ly`. Proof: divide the defining bounds
`2^Lx ≤ x < 2^(Lx+1)` and `2^Ly ≤ y < 2^(Ly+1)` to trap
`2^(Lx−Ly−1) ≤ x/y < 2^(Lx−Ly+1)`, then read off `Int.log 2 (x/y)`. -/
theorem log_div_bounds {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Int.log 2 x - Int.log 2 y - 1 ≤ Int.log 2 (x / y) ∧
      Int.log 2 (x / y) ≤ Int.log 2 x - Int.log 2 y := by
  set Lx := Int.log 2 x with hLx
  set Ly := Int.log 2 y with hLy
  have hxy : 0 < x / y := div_pos hx hy
  have hne : (2 : ℝ) ≠ 0 := by norm_num
  have hxlo : (2 : ℝ) ^ Lx ≤ x := by
    have := Int.zpow_log_le_self (b := 2) (by norm_num) hx; rw [← hLx] at this; exact_mod_cast this
  have hxhi : x < (2 : ℝ) ^ (Lx + 1) := by
    have := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) x
    rw [← hLx] at this; exact_mod_cast this
  have hylo : (2 : ℝ) ^ Ly ≤ y := by
    have := Int.zpow_log_le_self (b := 2) (by norm_num) hy; rw [← hLy] at this; exact_mod_cast this
  have hyhi : y < (2 : ℝ) ^ (Ly + 1) := by
    have := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) y
    rw [← hLy] at this; exact_mod_cast this
  have hlo : (2 : ℝ) ^ (Lx - Ly - 1) ≤ x / y := by
    rw [le_div_iff₀ hy]
    calc (2 : ℝ) ^ (Lx - Ly - 1) * y
        ≤ (2 : ℝ) ^ (Lx - Ly - 1) * (2 : ℝ) ^ (Ly + 1) :=
          mul_le_mul_of_nonneg_left hyhi.le (by positivity)
      _ = (2 : ℝ) ^ Lx := by rw [← zpow_add₀ hne]; congr 1; ring
      _ ≤ x := hxlo
  have hhi : x / y < (2 : ℝ) ^ (Lx - Ly + 1) := by
    rw [div_lt_iff₀ hy]
    calc x < (2 : ℝ) ^ (Lx + 1) := hxhi
      _ = (2 : ℝ) ^ (Lx - Ly + 1) * (2 : ℝ) ^ Ly := by rw [← zpow_add₀ hne]; congr 1; ring
      _ ≤ (2 : ℝ) ^ (Lx - Ly + 1) * y := mul_le_mul_of_nonneg_left hylo (by positivity)
  refine ⟨(Int.zpow_le_iff_le_log (b := 2) (by norm_num) hxy).mp (by exact_mod_cast hlo), ?_⟩
  have h2 : Int.log 2 (x / y) < Lx - Ly + 1 :=
    (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hxy).mp (by exact_mod_cast hhi)
  omega

/-- **Even-radix (radix 2) exact midpoint ⟹ representable in the finer format.**
If `0 < v` equals its `F₁`-midpoint and `F₂` is finer at `v`
(`F₂.canonicalExp v ≤ F₁.canonicalExp v − 1`), then the midpoint dyadic
`g = rndDown₁ v + ½·2^e₁ = (2·ma+1)·2^(e₁−1)` (`ma = ⌊v·2^(−e₁)⌋`,
`e₁ = canonicalExp₁ v`) satisfies `(g:ℝ) = v` and `g ∈ F₂`. This is where the
*even radix* enters: the trailing `½·ulp₁ = 2^(e₁−1)` is a whole `F₂`-quantum
because `e₂ ≤ e₁−1`, so the exact midpoint is on the `F₂` grid. -/
private theorem midp_mem_F₂ {F₁ F₂ : FiniteFormat} {p₂ : ℕ+}
    (hp₂ : F₂.p = ((p₂ : ℕ+) : WithTop ℕ+)) {v : ℝ} (hv : 0 < v)
    (hcexp : F₂.canonicalExp v ≤ F₁.canonicalExp v - 1)
    (hmid : v = midp F₁ v) :
    ∃ g : Dyadic, (g : ℝ) = v ∧ g ∈ F₂.unbounded := by
  set e₁ := F₁.canonicalExp v with he₁
  set e₂ := F₂.canonicalExp v with he₂
  set ma : ℤ := ⌊v * (2 : ℝ) ^ (-e₁)⌋ with hma
  have hne : (2 : ℝ) ≠ 0 := by norm_num
  -- the midpoint dyadic and its realization
  have hg_real : (Dyadic.ofIntZpow (2 * ma + 1) (e₁ - 1) : ℝ) = v := by
    have hmidp : midp F₁ v = (ma : ℝ) * (2 : ℝ) ^ e₁ + (2 : ℝ) ^ e₁ / 2 := by
      unfold midp ulp; rw [rndDown_eq, ← he₁, ← hma, Dyadic.coe_ofIntZpow]
    rw [Dyadic.coe_ofIntZpow, hmid, hmidp]
    have h2 : (2 : ℝ) ^ e₁ = 2 * (2 : ℝ) ^ (e₁ - 1) := by
      have hsplit : (2 : ℝ) ^ e₁ = (2 : ℝ) ^ (e₁ - 1) * (2 : ℝ) ^ (1 : ℤ) := by
        rw [← zpow_add₀ hne]; congr 1; ring
      rw [hsplit, zpow_one]; ring
    rw [h2]; push_cast; ring
  -- `g` is a multiple of `2^(e₁−1)`, hence at any coarser quantum
  have hq_e₁ : Dyadic.quantumAtLeast ((e₁ - 1 : ℤ) : WithBot ℤ)
      (Dyadic.ofIntZpow (2 * ma + 1) (e₁ - 1)) :=
    (Dyadic.quantumAtLeast_coe_real (e₁ - 1) _).mpr ⟨2 * ma + 1, by rw [Dyadic.coe_ofIntZpow]⟩
  have he₂le : ((e₂ : ℤ) : WithBot ℤ) ≤ ((e₁ - 1 : ℤ) : WithBot ℤ) := by
    exact_mod_cast (show e₂ ≤ e₁ - 1 from by omega)
  refine ⟨Dyadic.ofIntZpow (2 * ma + 1) (e₁ - 1), hg_real, ?_, ?_, trivial⟩
  · -- precisionAtMost p₂: mantissa at scale e₂ fits p₂ bits
    rw [FiniteFormat.unbounded_p, hp₂, Dyadic.precisionAtMost_coe_real]
    have hq_e₂ := Dyadic.quantumAtLeast_anti he₂le hq_e₁
    obtain ⟨C, hC⟩ := (Dyadic.quantumAtLeast_coe_real e₂ _).mp hq_e₂
    rw [hg_real] at hC
    refine ⟨C, e₂, by rw [hg_real]; exact hC, ?_⟩
    -- `|C| < 2^p₂` from `|v| < 2^(mag v) ≤ 2^(e₂ + p₂)`
    have h2e2 : (0 : ℝ) < (2 : ℝ) ^ e₂ := zpow_pos (by norm_num) _
    have hbound : Int.log 2 v + 1 ≤ e₂ + (p₂ : ℤ) := by
      have := log_sub_prec_le_canonicalExp hp₂ (ne_of_gt hv)
      rw [abs_of_pos hv, ← he₂] at this; omega
    have hvlt : |v| < (2 : ℝ) ^ (e₂ + (p₂ : ℤ)) := by
      rw [abs_of_pos hv]
      exact lt_of_lt_of_le (Int.lt_zpow_succ_log_self (b := 2) (by norm_num) v)
        (zpow_le_zpow_right₀ (by norm_num) hbound)
    have h2p2 : ((2 : ℝ) ^ (p₂ : ℕ)) = (2 : ℝ) ^ (p₂ : ℤ) := by rw [← zpow_natCast]
    have hsplit : (2 : ℝ) ^ (e₂ + (p₂ : ℤ)) = (2 : ℝ) ^ (p₂ : ℤ) * (2 : ℝ) ^ e₂ := by
      rw [show e₂ + (p₂ : ℤ) = (p₂ : ℤ) + e₂ from by ring, zpow_add₀ hne]
    have hCR : |(C : ℝ)| < (2 : ℝ) ^ (p₂ : ℤ) := by
      have hvC : |v| = |(C : ℝ)| * (2 : ℝ) ^ e₂ := by rw [hC, abs_mul, abs_of_pos h2e2]
      rw [hvC, hsplit] at hvlt
      exact lt_of_mul_lt_mul_right hvlt (le_of_lt h2e2)
    have hcast : (|C| : ℝ) < ((2 : ℤ) ^ (p₂ : ℕ) : ℝ) := by push_cast; rw [h2p2]; exact hCR
    exact_mod_cast hcast
  · -- quantumAtLeast F₂.exp: `g` is a multiple of `2^(e₁−1) ≥ 2^(F₂.exp)`
    rw [FiniteFormat.unbounded_exp]
    have hF₂le : F₂.exp ≤ ((e₁ - 1 : ℤ) : WithBot ℤ) := by
      refine le_trans (exp_le_canonicalExp_coe F₂ v) ?_
      rw [← he₂]; exact he₂le
    exact Dyadic.quantumAtLeast_anti hF₂le hq_e₁

/-- **Small positive values round to zero** (FLT underflow). In an FLT format
(`exp = emin`), any `0 ≤ x' < 2^(emin−1)` rounds to nearest to `0`: its scaled
mantissa is `< ½`, and the grid point selected is `0`. -/
theorem nearest_zero_of_small {F₁ : FiniteFormat} {tb₁ : TieBreak} {p₁ : ℕ+} {emin₁ : ℤ}
    (hp₁ : F₁.p = ((p₁ : ℕ+) : WithTop ℕ+)) (hexp₁ : F₁.exp = (emin₁ : WithBot ℤ))
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {x' : ℝ} (hx'0 : 0 ≤ x') (hx'lt : x' < (2 : ℝ) ^ (emin₁ - 1)) :
    RoundsFinite F₁.unbounded (.nearest tb₁) x' 0 := by
  have hz0 : ∀ e : ℤ, Dyadic.ofIntZpow 0 e = 0 := fun e =>
    (Dyadic.coe_real_inj _ _).mp (by simp)
  rcases eq_or_lt_of_le hx'0 with h0 | hpos
  · rw [← h0]
    have h := nearest_eq_of_close F₁ tb₁ 0 hundef₁ (m := 0)
      (by rw [zero_mul, Int.cast_zero, sub_zero, abs_zero]; norm_num)
    rwa [hz0] at h
  · have hcexp : F₁.canonicalExp x' = emin₁ := by
      rw [canonicalExp_FLT hp₁ hexp₁ (ne_of_gt hpos), abs_of_pos hpos]
      have hlog : Int.log 2 x' < emin₁ - 1 :=
        (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hpos).mp (by exact_mod_cast hx'lt)
      omega
    have hclose : |x' * (2 : ℝ) ^ (-(F₁.canonicalExp x')) - ((0 : ℤ) : ℝ)| < 1 / 2 := by
      rw [hcexp, Int.cast_zero, sub_zero, abs_of_nonneg (by positivity)]
      rw [show (1 : ℝ) / 2 = (2 : ℝ) ^ (emin₁ - 1) * (2 : ℝ) ^ (-emin₁) from by
            rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
                show (emin₁ - 1) + (-emin₁) = (-1 : ℤ) from by ring]; norm_num]
      exact mul_lt_mul_of_pos_right hx'lt (by positivity)
    have h := nearest_eq_of_close F₁ tb₁ x' hundef₁ hclose
    rwa [hz0] at h

/-- **Underflow double rounding to zero** (FLT, the non-sliver underflow case).
If `0 < v` is far enough below the underflow threshold `2^(emin₁−1)` (namely
`v < 2^(emin₁−1) − ½·ulp₂ v`), then both `v` and its `F₂`-rounding `z = ◦₂ v`
land in `[0, 2^(emin₁−1))`, so both round to `0` in `F₁` and double rounding is
innocuous. Covers Flocq's `round_round_really_zero` regime and the non-sliver
part of `round_round_zero`; the excluded sliver `[2^(emin₁−1) − ½ulp₂,
2^(emin₁−1))` is where `round_round_div_aux0` shows a quotient cannot land. -/
theorem round_round_div_zero {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ : ℕ+} {emin₁ : ℤ}
    (hp₁ : F₁.p = ((p₁ : ℕ+) : WithTop ℕ+)) (hexp₁ : F₁.exp = (emin₁ : WithBot ℤ))
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {v : ℝ} (hv : 0 < v)
    (hvlt : v < (2 : ℝ) ^ (emin₁ - 1) - ulp F₂ v / 2)
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) v z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) v w := by
  have hu2pos : (0 : ℝ) < ulp F₂ v := ulp_pos F₂ v
  have hv0 : RoundsFinite F₁.unbounded (.nearest tb₁) v 0 :=
    nearest_zero_of_small hp₁ hexp₁ hundef₁ hv.le (by linarith)
  have hzf : IsFaithfulRound F₂.unbounded v z := by cases tb₂ <;> exact hz.2.1
  have hznn : 0 ≤ (z : ℝ) := by
    rcases hzf with ⟨_, _, hmax⟩ | ⟨_, hxz, _⟩
    · simpa using hmax 0 (FiniteFormat.zero_mem F₂.unbounded) (by simpa using hv.le)
    · linarith [hxz, hv]
  have hzerr := abs_le.mp (nearest_error_le_half_ulp hz)
  have hzlt : (z : ℝ) < (2 : ℝ) ^ (emin₁ - 1) := by linarith [hzerr.2, hvlt]
  have hz0 : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) 0 :=
    nearest_zero_of_small hp₁ hexp₁ hundef₁ hznn hzlt
  have hw0 : w = 0 :=
    (rndUnbounded_unique F₁ (.nearest tb₁) (z : ℝ) hundef₁ hw).trans
      (rndUnbounded_unique F₁ (.nearest tb₁) (z : ℝ) hundef₁ hz0).symm
  rw [hw0]; exact hv0

/-- **Division separation lemma** (Flocq `round_round_div_aux{1,2}`, Figueroa).
For `v = x/y` with `x, y ∈ F₁` (`hxrep`, `hyrep`), the quotient is *never*
strictly within `½·ulp₂` of its `F₁`-midpoint **unless it equals it**: assuming
`v ≠ midp₁ v` gives `½·ulp₂ < |v − midp₁ v|`.

Proof: suppose `|v − m| ≤ 2^(e₂−1)` (`m = (2·ma+1)·2^(e₁−1)`). Multiply by `y`
(`x = v·y`): `x − m·y = K·2^(e₁−1+ey)` where `ey = cexp₁ y` and, because
`e₁−1+ey ≤ ex = cexp₁ x` (`hex_ge`), `K` is an *integer*. Since `v ≠ m` and
`y ≠ 0`, `K ≠ 0`, so `|x − m·y| ≥ 2^(e₁−1+ey)`. But `|x − m·y| = |v−m|·y ≤
2^(e₂−1)·y < 2^(e₂−1+ey+p₁)` (using `y < 2^(ey+p₁)`), forcing `e₁ < e₂ + p₁` —
contradicting Roux's bound `e₂ ≤ e₁ − p₁` (`hquant`, i.e. `p₂ ≥ 2p₁`). -/
theorem round_round_div_aux {F₁ F₂ : FiniteFormat} {x y v : ℝ} {p₁ : ℕ+}
    (hy : 0 < y) (hv : x = v * y)
    (hxrep : ∃ mx : ℤ, x = (mx : ℝ) * (2 : ℝ) ^ (F₁.canonicalExp x))
    (hyrep : ∃ my : ℤ, y = (my : ℝ) * (2 : ℝ) ^ (F₁.canonicalExp y))
    (hex_ge : F₁.canonicalExp v - 1 + F₁.canonicalExp y ≤ F₁.canonicalExp x)
    (hy_hi : y < (2 : ℝ) ^ (F₁.canonicalExp y + (p₁ : ℤ)))
    (hquant : F₂.canonicalExp v ≤ F₁.canonicalExp v - (p₁ : ℤ))
    (hne_mid : v ≠ midp F₁ v) :
    ulp F₂ v / 2 < |v - midp F₁ v| := by
  set e₁ := F₁.canonicalExp v with he₁
  set e₂ := F₂.canonicalExp v with he₂
  set ex := F₁.canonicalExp x with hex
  set ey := F₁.canonicalExp y with hey
  have hne : (2 : ℝ) ≠ 0 := by norm_num
  have hy_ne : y ≠ 0 := ne_of_gt hy
  set ma : ℤ := ⌊v * (2 : ℝ) ^ (-e₁)⌋ with hma
  have hmidp : midp F₁ v = ((2 * ma + 1 : ℤ) : ℝ) * (2 : ℝ) ^ (e₁ - 1) := by
    have hmv : midp F₁ v = (ma : ℝ) * (2 : ℝ) ^ e₁ + (2 : ℝ) ^ e₁ / 2 := by
      unfold midp ulp; rw [rndDown_eq, ← he₁, ← hma, Dyadic.coe_ofIntZpow]
    rw [hmv]
    have h2 : (2 : ℝ) ^ e₁ = 2 * (2 : ℝ) ^ (e₁ - 1) := by
      have hs : (2 : ℝ) ^ e₁ = (2 : ℝ) ^ (e₁ - 1) * (2 : ℝ) ^ (1 : ℤ) := by
        rw [← zpow_add₀ hne]; congr 1; ring
      rw [hs, zpow_one]; ring
    rw [h2]; push_cast; ring
  obtain ⟨mx, hmx⟩ := hxrep
  obtain ⟨my, hmy⟩ := hyrep
  -- integrality: `x − m·y = K · 2^(e₁−1+ey)`, `K` integer
  set d : ℕ := (ex - (e₁ - 1 + ey)).toNat with hd
  set K : ℤ := mx * 2 ^ d - (2 * ma + 1) * my with hK
  have hd_eq : (d : ℤ) = ex - (e₁ - 1 + ey) := by rw [hd, Int.toNat_of_nonneg (by omega)]
  have hdiff : x - midp F₁ v * y = (K : ℝ) * (2 : ℝ) ^ (e₁ - 1 + ey) := by
    rw [hmidp, hmx, hmy, hK]
    push_cast
    rw [show (2 : ℝ) ^ ex = (2 : ℝ) ^ d * (2 : ℝ) ^ (e₁ - 1) * (2 : ℝ) ^ ey from by
          rw [← zpow_natCast (2 : ℝ) d, ← zpow_add₀ hne, ← zpow_add₀ hne]; congr 1; omega,
        show (2 : ℝ) ^ (e₁ - 1 + ey) = (2 : ℝ) ^ (e₁ - 1) * (2 : ℝ) ^ ey from by
          rw [← zpow_add₀ hne]]
    ring
  have hxmy_ne : x - midp F₁ v * y ≠ 0 := by
    rw [hv, ← sub_mul]; exact mul_ne_zero (sub_ne_zero.mpr hne_mid) hy_ne
  have hK_ne : K ≠ 0 := fun h0 => hxmy_ne (by rw [hdiff, h0]; simp)
  -- lower bound `|x − m·y| ≥ 2^(e₁−1+ey)`
  have h2ey_pos : (0 : ℝ) < (2 : ℝ) ^ (e₁ - 1 + ey) := zpow_pos (by norm_num) _
  have hlow : (2 : ℝ) ^ (e₁ - 1 + ey) ≤ |x - midp F₁ v * y| := by
    rw [hdiff, abs_mul, abs_of_pos h2ey_pos]
    have hKabs : (1 : ℝ) ≤ |(K : ℝ)| := by
      have h1 : (1 : ℤ) ≤ |K| := Int.one_le_abs hK_ne
      calc (1 : ℝ) ≤ ((|K| : ℤ) : ℝ) := by exact_mod_cast h1
        _ = |(K : ℝ)| := by rw [Int.cast_abs]
    nlinarith [hKabs, h2ey_pos]
  -- upper bound (from the negated conclusion)
  by_contra hcon
  rw [not_lt, show ulp F₂ v = (2 : ℝ) ^ e₂ from by unfold ulp; rw [← he₂]] at hcon
  have h2e2half : (2 : ℝ) ^ e₂ / 2 = (2 : ℝ) ^ (e₂ - 1) := by
    rw [show (e₂ - 1 : ℤ) = e₂ + (-1) from by ring, zpow_add₀ hne,
        show (2 : ℝ) ^ (-1 : ℤ) = 1 / 2 from by norm_num]; ring
  have hupp : |x - midp F₁ v * y| < (2 : ℝ) ^ (e₂ - 1 + ey + (p₁ : ℤ)) := by
    have hxmy_eq : |x - midp F₁ v * y| = |v - midp F₁ v| * y := by
      rw [hv, ← sub_mul, abs_mul, abs_of_pos hy]
    rw [hxmy_eq]
    have hb : |v - midp F₁ v| * y ≤ ((2 : ℝ) ^ e₂ / 2) * y := mul_le_mul_of_nonneg_right hcon hy.le
    have hy2 : ((2 : ℝ) ^ e₂ / 2) * y < ((2 : ℝ) ^ e₂ / 2) * (2 : ℝ) ^ (ey + (p₁ : ℤ)) :=
      mul_lt_mul_of_pos_left hy_hi (by positivity)
    have heq : ((2 : ℝ) ^ e₂ / 2) * (2 : ℝ) ^ (ey + (p₁ : ℤ))
        = (2 : ℝ) ^ (e₂ - 1 + ey + (p₁ : ℤ)) := by
      rw [h2e2half, ← zpow_add₀ hne]; congr 1; ring
    linarith [hb, hy2, heq]
  have hmono : (2 : ℝ) ^ (e₂ - 1 + ey + (p₁ : ℤ)) ≤ (2 : ℝ) ^ (e₁ - 1 + ey) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  linarith [hlow, hupp, hmono]

/-- **rnd-div core** (format-agnostic). For a quotient `v = a / b` with `a, b ∈ F₁`
(`0 < a, b`), double rounding is innocuous once the canonical-exponent data a
valid precision/underflow choice supplies is in hand: `hex_ge` (numerator aligned
below the midpoint scale), `hb_hi` (`b`'s `F₁` bound), `hle` (`v` inside its
binade), and Roux's `hquant` (`cexp₂ v ≤ cexp₁ v − p₁`, i.e. `p₂ ≥ 2p₁`).
`round_round_mid_cases` reduces to the near-midpoint case, which splits: `v = m`
is handled exactly by `midp_mem_F₂` (even radix), and `v ≠ m` is impossible by
`round_round_div_aux`. -/
theorem rndDiv_core {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {a b v : ℝ} {p₁ p₂ : ℕ+}
    (hp₂ : F₂.p = ((p₂ : ℕ+) : WithTop ℕ+))
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    (ha : 0 < a) (hb : 0 < b) (hab : a = v * b)
    (hxrep : ∃ mx : ℤ, a = (mx : ℝ) * (2 : ℝ) ^ (F₁.canonicalExp a))
    (hyrep : ∃ my : ℤ, b = (my : ℝ) * (2 : ℝ) ^ (F₁.canonicalExp b))
    (hex_ge : F₁.canonicalExp v - 1 + F₁.canonicalExp b ≤ F₁.canonicalExp a)
    (hb_hi : b < (2 : ℝ) ^ (F₁.canonicalExp b + (p₁ : ℤ)))
    (hle : F₁.canonicalExp v ≤ Int.log 2 v + 1)
    (hquant : F₂.canonicalExp v ≤ F₁.canonicalExp v - (p₁ : ℤ))
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) v z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) v w := by
  have hv_pos : 0 < v := by
    rcases mul_pos_iff.mp (hab ▸ ha) with ⟨h, _⟩ | ⟨_, h⟩
    · exact h
    · linarith [hb]
  have hp1pos : (1 : ℤ) ≤ (p₁ : ℤ) := by exact_mod_cast p₁.one_le
  have h21 : F₂.canonicalExp v < F₁.canonicalExp v := by omega
  refine round_round_mid_cases hundef₁ hv_pos h21 hle hz hw (fun hmid_le => ?_)
  by_cases heqmid : v = midp F₁ v
  · -- exact midpoint: `v ∈ F₂`, so the intermediate rounding is a no-op
    obtain ⟨g, hgv, hgmem⟩ := midp_mem_F₂ hp₂ hv_pos (by omega) heqmid
    have hzg : z = g := RoundsFinite.eq_of_mem hgmem (by rw [hgv]; exact hz)
    have hzv : (z : ℝ) = v := by rw [hzg, hgv]
    rw [← hzv]; exact hw
  · -- otherwise the separation lemma contradicts `hmid_le`
    exact absurd hmid_le (not_le.mpr
      (round_round_div_aux hb hab hxrep hyrep hex_ge hb_hi hquant heqmid))

/-- **rnd-div, positive case** (Roux Theorem 29, radix 2, FLX). For `a, b ∈ F₁`
with `0 < a`, `0 < b` and `p₂ ≥ 2p₁`, double rounding of `a / b` is innocuous.
The `rndDiv_core` hypotheses are discharged from the FLX closed form
`canonicalExp = log₂|·| + 1 − p` and the quotient binade bounds `log_div_bounds`. -/
theorem rndDiv_pos {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ+}
    (hp₁ : F₁.p = ((p₁ : ℕ+) : WithTop ℕ+)) (hp₂ : F₂.p = ((p₂ : ℕ+) : WithTop ℕ+))
    (hpp : 2 * p₁ ≤ p₂) (hexp₁ : F₁.exp = ⊥) (hexp₂ : F₂.exp = ⊥)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {a b : Dyadic} (ha : a ∈ F₁) (hb : b ∈ F₁)
    (hapos : 0 < (a : ℝ)) (hbpos : 0 < (b : ℝ))
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((a : ℝ) / (b : ℝ)) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((a : ℝ) / (b : ℝ)) w := by
  set v := (a : ℝ) / (b : ℝ) with hv_def
  have hbne : (b : ℝ) ≠ 0 := ne_of_gt hbpos
  have hv_pos : 0 < v := div_pos hapos hbpos
  have hab : (a : ℝ) = v * (b : ℝ) := by rw [hv_def]; exact (div_mul_cancel₀ (a : ℝ) hbne).symm
  have hppZ : 2 * (p₁ : ℤ) ≤ (p₂ : ℤ) := by exact_mod_cast hpp
  have hp1pos : (1 : ℤ) ≤ (p₁ : ℤ) := by exact_mod_cast p₁.one_le
  -- FLX closed forms
  have hcv : F₁.canonicalExp v = Int.log 2 v + 1 - (p₁ : ℤ) := by
    rw [canonicalExp_FLX hp₁ hexp₁ (ne_of_gt hv_pos), abs_of_pos hv_pos]
  have hca : F₁.canonicalExp (a : ℝ) = Int.log 2 (a : ℝ) + 1 - (p₁ : ℤ) := by
    rw [canonicalExp_FLX hp₁ hexp₁ (ne_of_gt hapos), abs_of_pos hapos]
  have hcb : F₁.canonicalExp (b : ℝ) = Int.log 2 (b : ℝ) + 1 - (p₁ : ℤ) := by
    rw [canonicalExp_FLX hp₁ hexp₁ (ne_of_gt hbpos), abs_of_pos hbpos]
  have hcv2 : F₂.canonicalExp v = Int.log 2 v + 1 - (p₂ : ℤ) := by
    rw [canonicalExp_FLX hp₂ hexp₂ (ne_of_gt hv_pos), abs_of_pos hv_pos]
  have hlog := log_div_bounds hapos hbpos
  rw [← hv_def] at hlog
  refine rndDiv_core (p₁ := p₁) hp₂ hundef₁ hapos hbpos hab ?_ ?_ ?_ ?_ ?_ ?_ hz hw
  · obtain ⟨c, _, hc⟩ := exists_canonical_rep F₁ hp₁ ha hapos; exact ⟨c, hc⟩
  · obtain ⟨c, _, hc⟩ := exists_canonical_rep F₁ hp₁ hb hbpos; exact ⟨c, hc⟩
  · rw [hcv, hcb, hca]; omega
  · rw [hcb]
    have := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) (b : ℝ)
    rw [show Int.log 2 (b : ℝ) + 1 - (p₁ : ℤ) + (p₁ : ℤ) = Int.log 2 (b : ℝ) + 1 from by ring]
    exact this
  · rw [hcv]; omega
  · rw [hcv2, hcv]; omega

/-- **rnd-div, positive denominator** (FLX). Extends `rndDiv_pos` to any numerator
`a ∈ F₁` (`b > 0`): `a > 0` is `rndDiv_pos`; `a < 0` negates to `−a > 0` (the
quotient flips sign, handled by `RoundsFinite.neg_nearest`); `a = 0` gives the
exactly-representable quotient `0` (`rndExact`). -/
theorem rndDiv_posden {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ+}
    (hp₁ : F₁.p = ((p₁ : ℕ+) : WithTop ℕ+)) (hp₂ : F₂.p = ((p₂ : ℕ+) : WithTop ℕ+))
    (hpp : 2 * p₁ ≤ p₂) (hexp₁ : F₁.exp = ⊥) (hexp₂ : F₂.exp = ⊥)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {a b : Dyadic} (ha : a ∈ F₁) (hb : b ∈ F₁) (hbpos : 0 < (b : ℝ))
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((a : ℝ) / (b : ℝ)) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((a : ℝ) / (b : ℝ)) w := by
  rcases lt_trichotomy (a : ℝ) 0 with haneg | hazero | hapos
  · -- `a < 0`: negate the numerator (quotient flips sign)
    have hna : (-a) ∈ F₁ := FiniteFormat.neg_mem ha
    have hnapos : 0 < ((-a : Dyadic) : ℝ) := by rw [Dyadic.coe_real_neg]; linarith
    have hqval : ((-a : Dyadic) : ℝ) / (b : ℝ) = -((a : ℝ) / (b : ℝ)) := by
      rw [Dyadic.coe_real_neg, neg_div]
    have hz2 : RoundsFinite F₂.unbounded (.nearest tb₂) (((-a : Dyadic) : ℝ) / (b : ℝ)) (-z) := by
      rw [hqval]; exact (RoundsFinite.neg_nearest F₂.unbounded tb₂ ((a : ℝ) / (b : ℝ)) z).mp hz
    have hw2 : RoundsFinite F₁.unbounded (.nearest tb₁) ((-z : Dyadic) : ℝ) (-w) := by
      rw [Dyadic.coe_real_neg]; exact (RoundsFinite.neg_nearest F₁.unbounded tb₁ (z : ℝ) w).mp hw
    have hres := rndDiv_pos hp₁ hp₂ hpp hexp₁ hexp₂ hundef₁ hna hb hnapos hbpos hz2 hw2
    rw [hqval] at hres
    exact (RoundsFinite.neg_nearest F₁.unbounded tb₁ ((a : ℝ) / (b : ℝ)) w).mpr hres
  · -- `a = 0`: the quotient is `0`, exactly representable
    have hval : (a : ℝ) / (b : ℝ) = ((0 : Dyadic) : ℝ) := by rw [hazero, zero_div]; simp
    rw [hval] at hz ⊢
    exact rndExact (F₁ := F₁.unbounded) (F₂ := F₂.unbounded)
      (FiniteFormat.zero_mem F₂.unbounded) hz hw
  · exact rndDiv_pos hp₁ hp₂ hpp hexp₁ hexp₂ hundef₁ ha hb hapos hbpos hz hw

/-- **rnd-div** (Roux Theorem 29, radix 2, FLX). For **arbitrary** `a, b ∈ F₁`
with `b ≠ 0` and `p₂ ≥ 2p₁`, double rounding of `a / b` (round to nearest in `F₂`,
then in `F₁`) agrees with rounding `a / b` directly into `F₁`. A negative
denominator reduces to `rndDiv_posden` via `a/b = (−a)/(−b)` (same value). This
matches the generality of Flocq's `round_round_div_FLX`. -/
theorem rndDiv {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ+}
    (hp₁ : F₁.p = ((p₁ : ℕ+) : WithTop ℕ+)) (hp₂ : F₂.p = ((p₂ : ℕ+) : WithTop ℕ+))
    (hpp : 2 * p₁ ≤ p₂) (hexp₁ : F₁.exp = ⊥) (hexp₂ : F₂.exp = ⊥)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {a b : Dyadic} (ha : a ∈ F₁) (hb : b ∈ F₁) (hbne : (b : ℝ) ≠ 0)
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((a : ℝ) / (b : ℝ)) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((a : ℝ) / (b : ℝ)) w := by
  rcases lt_or_gt_of_ne hbne with hbneg | hbpos
  · -- `b < 0`: `a/b = (−a)/(−b)`, positive denominator, value unchanged
    have hna : (-a) ∈ F₁ := FiniteFormat.neg_mem ha
    have hnb : (-b) ∈ F₁ := FiniteFormat.neg_mem hb
    have hnbpos : 0 < ((-b : Dyadic) : ℝ) := by rw [Dyadic.coe_real_neg]; linarith
    have hval : (a : ℝ) / (b : ℝ) = ((-a : Dyadic) : ℝ) / ((-b : Dyadic) : ℝ) := by
      rw [Dyadic.coe_real_neg, Dyadic.coe_real_neg, neg_div_neg_eq]
    rw [hval] at hz ⊢
    exact rndDiv_posden hp₁ hp₂ hpp hexp₁ hexp₂ hundef₁ hna hnb hnbpos hz hw
  · exact rndDiv_posden hp₁ hp₂ hpp hexp₁ hexp₂ hundef₁ ha hb hbpos hz hw

end Mpfx
