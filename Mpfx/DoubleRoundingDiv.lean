import Mpfx.CanonicalExp
import Mpfx.NearestMidpoint
import Mpfx.DoubleRoundingMul
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

* `x / y ≠ m` but within `½·ulp₂` of it — *impossible*, by the separation lemma
  `round_round_div_aux` (analogue of `round_round_sqrt_aux`); and
* `x / y = m` exactly — here the **even radix** makes `m ∈ F₂` (`midp_mem_F₂`: its
  canonical exponent drops by ≥ 1, absorbing the trailing `½·ulp₁`), so the
  intermediate rounding is exact.

Top-level results: `rndDiv_FLX` and `rndDiv_FLT` (arbitrary operands, `b ≠ 0`);
the FLT underflow regimes go through `nearest_zero_of_small`/`round_round_div_zero`.
See `docs/agents/DOUBLE_ROUNDING_OPS_PLAN.md` §9.
-/

namespace Mpfx

/-- **Binade of a quotient** (Flocq `mag_div_disj`). For `0 < x`, `0 < y`, the
binade of `x / y` is `Int.log 2 x − Int.log 2 y` or one less:
`Lx − Ly − 1 ≤ Int.log 2 (x / y) ≤ Lx − Ly`. Proof: divide the defining bounds
`2^Lx ≤ x < 2^(Lx+1)` and `2^Ly ≤ y < 2^(Ly+1)` to trap
`2^(Lx−Ly−1) ≤ x/y < 2^(Lx−Ly+1)`, then read off `Int.log 2 (x/y)`. -/
private theorem log_div_bounds {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
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
    rw [Dyadic.coe_ofIntZpow, hmid, hmidp, two_zpow_dbl e₁]; push_cast; ring
  -- `g` is a multiple of `2^(e₁−1)`, hence at any coarser quantum
  have hq_e₁ : Dyadic.quantumAtLeast ((e₁ - 1 : ℤ) : WithBot ℤ)
      (Dyadic.ofIntZpow (2 * ma + 1) (e₁ - 1)) :=
    (Dyadic.quantumAtLeast_coe_real (e₁ - 1) _).mpr ⟨2 * ma + 1, by rw [Dyadic.coe_ofIntZpow]⟩
  have he₂le : ((e₂ : ℤ) : WithBot ℤ) ≤ ((e₁ - 1 : ℤ) : WithBot ℤ) := by
    exact_mod_cast (show e₂ ≤ e₁ - 1 from by omega)
  -- `g = 𝒜(p₂, e₁−1, ⊤)`-representable, and that format is contained in
  -- `F₂.unbounded` by `𝒜-Contains-Prec` (`mem_unbounded_of_le`).
  have hF₂le : F₂.exp ≤ ((e₁ - 1 : ℤ) : WithBot ℤ) :=
    le_trans (exp_le_canonicalExp_coe F₂ v) (by rw [← he₂]; exact he₂le)
  refine ⟨Dyadic.ofIntZpow (2 * ma + 1) (e₁ - 1), hg_real,
    Format.mem_unbounded_of_le (p := ((p₂ : ℕ+) : WithTop ℕ+))
      (e := ((e₁ - 1 : ℤ) : WithBot ℤ)) (le_of_eq hp₂.symm) hF₂le ?_ hq_e₁⟩
  -- precisionAtMost p₂: mantissa at scale e₂ fits p₂ bits
  rw [Dyadic.precisionAtMost_coe_real]
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

/-- **Small positive values round to zero** (FLT underflow). In an FLT format
(`exp = emin`), any `0 ≤ x' < 2^(emin−1)` rounds to nearest to `0`: its scaled
mantissa is `< ½`, and the grid point selected is `0`. -/
private theorem nearest_zero_of_small {F₁ : FiniteFormat} {tb₁ : TieBreak} {p₁ : ℕ+} {emin₁ : ℤ}
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
private theorem round_round_div_zero {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak}
    {p₁ : ℕ+} {emin₁ : ℤ}
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

/-- **Division separation lemma** (Flocq `round_round_div_aux{1,2}`, Figueroa),
format-agnostic. For `v = x/y` with `x, y ∈ F₁` (`hxrep`, `hyrep`), the quotient
is *never* strictly within `½·ulp₂` of its `F₁`-midpoint **unless it equals it**:
`v ≠ midp₁ v` gives `½·ulp₂ < |v − midp₁ v|`.

Proof: suppose `|v − m| ≤ 2^(e₂−1)` (`m = (2·ma+1)·2^(e₁−1)`). Multiply by `y`
(`x = v·y`): `x − m·y = K·2^s` where `s = min(cexp₁ x, e₁−1+cexp₁ y)` and `K` is
an *integer* (each operand is a multiple of `2^s`). Since `v ≠ m` and `y ≠ 0`,
`K ≠ 0`, so `|x − m·y| ≥ 2^s`. But `|x − m·y| = |v−m|·y ≤ 2^(e₂−1)·y <
2^(e₂+mag y)` (`y < 2^(mag y)`), forcing `s < e₂ + Int.log y` — contradicting the
two hypotheses `hA` (`e₂ + Int.log y ≤ cexp₁ x`) and `hB` (`e₂ + Int.log y ≤
e₁−1+cexp₁ y`), which together give `s ≥ e₂ + Int.log y`. The `min`-scale is what
makes this robust for FLT: unlike a fixed `cexp₁ x`-vs-`e₁−1+cexp₁ y` comparison,
it needs no ordering of the operand exponents (that ordering fails when a
subnormal operand's `cexp` is inflated to `emin₁`). -/
private theorem round_round_div_aux {F₁ F₂ : FiniteFormat} {x y v : ℝ}
    (hy : 0 < y) (hv : x = v * y)
    (hxrep : ∃ mx : ℤ, x = (mx : ℝ) * (2 : ℝ) ^ (F₁.canonicalExp x))
    (hyrep : ∃ my : ℤ, y = (my : ℝ) * (2 : ℝ) ^ (F₁.canonicalExp y))
    (hA : F₂.canonicalExp v + Int.log 2 y ≤ F₁.canonicalExp x)
    (hB : F₂.canonicalExp v + Int.log 2 y ≤ F₁.canonicalExp v - 1 + F₁.canonicalExp y)
    (hne_mid : v ≠ midp F₁ v) :
    ulp F₂ v / 2 < |v - midp F₁ v| := by
  set e₁ := F₁.canonicalExp v with he₁
  set e₂ := F₂.canonicalExp v with he₂
  set ex := F₁.canonicalExp x
  set ey := F₁.canonicalExp y
  set Ly := Int.log 2 y with hLy
  have hne : (2 : ℝ) ≠ 0 := by norm_num
  have hy_ne : y ≠ 0 := ne_of_gt hy
  set ma : ℤ := ⌊v * (2 : ℝ) ^ (-e₁)⌋ with hma
  have hmidp : midp F₁ v = ((2 * ma + 1 : ℤ) : ℝ) * (2 : ℝ) ^ (e₁ - 1) := by
    have hmv : midp F₁ v = (ma : ℝ) * (2 : ℝ) ^ e₁ + (2 : ℝ) ^ e₁ / 2 := by
      unfold midp ulp; rw [rndDown_eq, ← he₁, ← hma, Dyadic.coe_ofIntZpow]
    rw [hmv, two_zpow_dbl e₁]; push_cast; ring
  obtain ⟨mx, hmx⟩ := hxrep
  obtain ⟨my, hmy⟩ := hyrep
  -- integrality at the common scale `s = min(ex, e₁−1+ey)`
  set s : ℤ := min ex (e₁ - 1 + ey) with hs
  set dx : ℕ := (ex - s).toNat with hdx
  set dm : ℕ := (e₁ - 1 + ey - s).toNat with hdm
  have hdx_eq : (dx : ℤ) = ex - s := by rw [hdx, Int.toNat_of_nonneg (by omega)]
  have hdm_eq : (dm : ℤ) = e₁ - 1 + ey - s := by rw [hdm, Int.toNat_of_nonneg (by omega)]
  set K : ℤ := mx * 2 ^ dx - (2 * ma + 1) * my * 2 ^ dm with hK
  have e_ex : (2 : ℝ) ^ ex = (2 : ℝ) ^ dx * (2 : ℝ) ^ s := by
    rw [← zpow_natCast (2 : ℝ) dx, ← zpow_add₀ hne]; congr 1; omega
  have e_dm : (2 : ℝ) ^ (e₁ - 1) * (2 : ℝ) ^ ey = (2 : ℝ) ^ dm * (2 : ℝ) ^ s := by
    rw [← zpow_natCast (2 : ℝ) dm, ← zpow_add₀ hne, ← zpow_add₀ hne]; congr 1; omega
  have hdiff : x - midp F₁ v * y = (K : ℝ) * (2 : ℝ) ^ s := by
    rw [hmidp, hmx, hmy, hK]
    push_cast
    rw [e_ex, show (2 * (ma : ℝ) + 1) * (2 : ℝ) ^ (e₁ - 1) * ((my : ℝ) * (2 : ℝ) ^ ey)
          = (2 * (ma : ℝ) + 1) * (my : ℝ) * ((2 : ℝ) ^ (e₁ - 1) * (2 : ℝ) ^ ey) from by ring,
        e_dm]
    ring
  have hxmy_ne : x - midp F₁ v * y ≠ 0 := by
    rw [hv, ← sub_mul]; exact mul_ne_zero (sub_ne_zero.mpr hne_mid) hy_ne
  have hK_ne : K ≠ 0 := fun h0 => hxmy_ne (by rw [hdiff, h0]; simp)
  -- lower bound `|x − m·y| ≥ 2^s`
  have h2s_pos : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  have hlow : (2 : ℝ) ^ s ≤ |x - midp F₁ v * y| := by
    rw [hdiff, abs_mul, abs_of_pos h2s_pos]
    have hKabs : (1 : ℝ) ≤ |(K : ℝ)| := by
      have h1 : (1 : ℤ) ≤ |K| := Int.one_le_abs hK_ne
      calc (1 : ℝ) ≤ ((|K| : ℤ) : ℝ) := by exact_mod_cast h1
        _ = |(K : ℝ)| := by rw [Int.cast_abs]
    nlinarith [hKabs, h2s_pos]
  -- upper bound (from the negated conclusion)
  by_contra hcon
  rw [not_lt, show ulp F₂ v = (2 : ℝ) ^ e₂ from by unfold ulp; rw [← he₂]] at hcon
  have h2e2half : (2 : ℝ) ^ e₂ / 2 = (2 : ℝ) ^ (e₂ - 1) := two_zpow_half e₂
  have hupp : |x - midp F₁ v * y| < (2 : ℝ) ^ (e₂ + Ly) := by
    have hxmy_eq : |x - midp F₁ v * y| = |v - midp F₁ v| * y := by
      rw [hv, ← sub_mul, abs_mul, abs_of_pos hy]
    rw [hxmy_eq]
    have hylt : y < (2 : ℝ) ^ (Ly + 1) := by
      have := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) y
      rw [← hLy] at this; exact_mod_cast this
    have hb : |v - midp F₁ v| * y ≤ (2 : ℝ) ^ (e₂ - 1) * y := by
      rw [← h2e2half]; exact mul_le_mul_of_nonneg_right hcon hy.le
    have hy2 : (2 : ℝ) ^ (e₂ - 1) * y < (2 : ℝ) ^ (e₂ - 1) * (2 : ℝ) ^ (Ly + 1) :=
      mul_lt_mul_of_pos_left hylt (by positivity)
    have heq : (2 : ℝ) ^ (e₂ - 1) * (2 : ℝ) ^ (Ly + 1) = (2 : ℝ) ^ (e₂ + Ly) := by
      rw [← zpow_add₀ hne]; congr 1; ring
    linarith [hb, hy2, heq]
  have hmono : (2 : ℝ) ^ (e₂ + Ly) ≤ (2 : ℝ) ^ s :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  linarith [hlow, hupp, hmono]

/-- **rnd-div core** (format-agnostic). For a quotient `v = a / b` with `a, b ∈ F₁`
(`0 < a, b`), double rounding is innocuous once the canonical-exponent data a
valid precision/underflow choice supplies is in hand: `hA`/`hB` (the two
separation bounds of `round_round_div_aux`), `hle` (`v` inside its binade), and
Roux's `hquant` (`cexp₂ v ≤ cexp₁ v − p₁`, i.e. `p₂ ≥ 2p₁`). `round_round_mid_cases`
reduces to the near-midpoint case, which splits: `v = m` is handled exactly by
`midp_mem_F₂` (even radix), and `v ≠ m` is impossible by `round_round_div_aux`. -/
private theorem rndDiv_core {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {a b v : ℝ} {p₁ p₂ : ℕ+}
    (hp₂ : F₂.p = ((p₂ : ℕ+) : WithTop ℕ+))
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    (ha : 0 < a) (hb : 0 < b) (hab : a = v * b)
    (hxrep : ∃ mx : ℤ, a = (mx : ℝ) * (2 : ℝ) ^ (F₁.canonicalExp a))
    (hyrep : ∃ my : ℤ, b = (my : ℝ) * (2 : ℝ) ^ (F₁.canonicalExp b))
    (hA : F₂.canonicalExp v + Int.log 2 b ≤ F₁.canonicalExp a)
    (hB : F₂.canonicalExp v + Int.log 2 b ≤ F₁.canonicalExp v - 1 + F₁.canonicalExp b)
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
      (round_round_div_aux hb hab hxrep hyrep hA hB heqmid))

/-- **rnd-div, positive case** (Roux Theorem 29, radix 2, FLX). For `a, b ∈ F₁`
with `0 < a`, `0 < b` and `p₂ ≥ 2p₁`, double rounding of `a / b` is innocuous.
The `rndDiv_core` hypotheses are discharged from the FLX closed form
`canonicalExp = log₂|·| + 1 − p` and the quotient binade bounds `log_div_bounds`. -/
private theorem rndDiv_pos {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ+}
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
  · rw [hcv2, hca]; omega
  · rw [hcv2, hcv, hcb]; omega
  · rw [hcv]; omega
  · rw [hcv2, hcv]; omega

/-- **rnd-div, positive normal-quotient case** (Roux Theorem 29, radix 2, FLT).
For `a, b ∈ F₁` (FLT, `exp = emin`) with `0 < a, b`, `p₂ ≥ 2p₁`, Roux's underflow
bound `emin₂ ≤ emin₁ − p₁ − 2`, and the quotient in the **normal regime**
(`hle : cexp₁ (a/b) ≤ mag (a/b)`), double rounding of `a/b` is innocuous. The
reworked `round_round_div_aux` uses a `min`-scale, so its bounds `hA`/`hB` are now
`omega`-provable for FLT from `hquant`, `hle`, `log_div_bounds`, and the lower
bounds `cexp₁ = max(…) ≥ mag − p₁` — dodging the subnormal-`cexp`-inflation that
broke the FLX-style `hex_ge`. -/
private theorem rndDiv_pos_normal_FLT {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ+}
    {emin₁ emin₂ : ℤ}
    (hp₁ : F₁.p = ((p₁ : ℕ+) : WithTop ℕ+)) (hp₂ : F₂.p = ((p₂ : ℕ+) : WithTop ℕ+))
    (hpp : 2 * p₁ ≤ p₂)
    (hexp₁ : F₁.exp = (emin₁ : WithBot ℤ)) (hexp₂ : F₂.exp = (emin₂ : WithBot ℤ))
    (hemin : emin₂ ≤ emin₁ - (p₁ : ℤ) - 2)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {a b : Dyadic} (ha : a ∈ F₁) (hb : b ∈ F₁)
    (hapos : 0 < (a : ℝ)) (hbpos : 0 < (b : ℝ))
    (hle : F₁.canonicalExp ((a : ℝ) / (b : ℝ)) ≤ Int.log 2 ((a : ℝ) / (b : ℝ)) + 1)
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
  have hlogpair := log_div_bounds hapos hbpos
  rw [← hv_def] at hlogpair
  obtain ⟨hlog1, hlog2⟩ := hlogpair
  -- FLT closed form of `cexp₁ v` and lower bounds `cexp ≥ mag − p₁`
  have hcv : F₁.canonicalExp v = max (Int.log 2 v + 1 - (p₁ : ℤ)) emin₁ := by
    rw [canonicalExp_FLT hp₁ hexp₁ (ne_of_gt hv_pos), abs_of_pos hv_pos]
  have hcv2 : F₂.canonicalExp v = max (Int.log 2 v + 1 - (p₂ : ℤ)) emin₂ := by
    rw [canonicalExp_FLT hp₂ hexp₂ (ne_of_gt hv_pos), abs_of_pos hv_pos]
  have hca_lo : Int.log 2 (a : ℝ) + 1 - (p₁ : ℤ) ≤ F₁.canonicalExp (a : ℝ) := by
    rw [canonicalExp_FLT hp₁ hexp₁ (ne_of_gt hapos), abs_of_pos hapos]; exact le_max_left _ _
  have hcb_lo : Int.log 2 (b : ℝ) + 1 - (p₁ : ℤ) ≤ F₁.canonicalExp (b : ℝ) := by
    rw [canonicalExp_FLT hp₁ hexp₁ (ne_of_gt hbpos), abs_of_pos hbpos]; exact le_max_left _ _
  -- Roux's `hquant`, from the two arms of `cexp₂ v = max …`
  have h1 : emin₁ ≤ F₁.canonicalExp v := by rw [hcv]; exact le_max_right _ _
  have h2 : Int.log 2 v + 1 - (p₁ : ℤ) ≤ F₁.canonicalExp v := by rw [hcv]; exact le_max_left _ _
  have hquant : F₂.canonicalExp v ≤ F₁.canonicalExp v - (p₁ : ℤ) := by
    rw [hcv2]; exact max_le (by omega) (by omega)
  refine rndDiv_core (p₁ := p₁) hp₂ hundef₁ hapos hbpos hab ?_ ?_ ?_ ?_ hle hquant hz hw
  · obtain ⟨c, _, hc⟩ := exists_canonical_rep F₁ hp₁ ha hapos; exact ⟨c, hc⟩
  · obtain ⟨c, _, hc⟩ := exists_canonical_rep F₁ hp₁ hb hbpos; exact ⟨c, hc⟩
  · omega
  · omega

/-- **rnd-div, positive case** (Roux Theorem 29, radix 2, FLT). For `a, b ∈ F₁`
(FLT) with `0 < a, b`, `p₂ ≥ 2p₁`, and `emin₂ ≤ emin₁ − p₁ − 2`, double rounding of
`a/b` is innocuous — **all regimes**. Dispatch on `cexp₁ v` vs `mag v`:
* **normal** (`cexp₁ v ≤ mag v`): `rndDiv_pos_normal_FLT`;
* **underflow** (`cexp₁ v = emin₁ > mag v`, so `v < 2^(emin₁−1) = midp₁ v`): if `v`
  is far below the threshold (`< 2^(emin₁−1) − ½ulp₂`) it rounds to `0` in both
  (`round_round_div_zero`); otherwise `v` is in the boundary sliver, which the
  reworked `round_round_div_aux` shows is impossible (`hA`/`hB` hold there too, so
  no separate `div_aux0` port is needed). -/
private theorem rndDiv_pos_FLT {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ+}
    {emin₁ emin₂ : ℤ}
    (hp₁ : F₁.p = ((p₁ : ℕ+) : WithTop ℕ+)) (hp₂ : F₂.p = ((p₂ : ℕ+) : WithTop ℕ+))
    (hpp : 2 * p₁ ≤ p₂)
    (hexp₁ : F₁.exp = (emin₁ : WithBot ℤ)) (hexp₂ : F₂.exp = (emin₂ : WithBot ℤ))
    (hemin : emin₂ ≤ emin₁ - (p₁ : ℤ) - 2)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {a b : Dyadic} (ha : a ∈ F₁) (hb : b ∈ F₁)
    (hapos : 0 < (a : ℝ)) (hbpos : 0 < (b : ℝ))
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((a : ℝ) / (b : ℝ)) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((a : ℝ) / (b : ℝ)) w := by
  set v := (a : ℝ) / (b : ℝ) with hv_def
  have hne : (2 : ℝ) ≠ 0 := by norm_num
  have hbne : (b : ℝ) ≠ 0 := ne_of_gt hbpos
  have hv_pos : 0 < v := div_pos hapos hbpos
  have hp1pos : (1 : ℤ) ≤ (p₁ : ℤ) := by exact_mod_cast p₁.one_le
  have hppZ : 2 * (p₁ : ℤ) ≤ (p₂ : ℤ) := by exact_mod_cast hpp
  by_cases hle : F₁.canonicalExp v ≤ Int.log 2 v + 1
  · exact rndDiv_pos_normal_FLT hp₁ hp₂ hpp hexp₁ hexp₂ hemin hundef₁ ha hb hapos hbpos hle hz hw
  · -- underflow regime: `cexp₁ v = emin₁ > mag v`
    rw [not_le] at hle
    have hhalf : ∀ k : ℤ, (2 : ℝ) ^ (k - 1) = (2 : ℝ) ^ k / 2 := fun k => (two_zpow_half k).symm
    have hcvmax : F₁.canonicalExp v = max (Int.log 2 v + 1 - (p₁ : ℤ)) emin₁ := by
      rw [canonicalExp_FLT hp₁ hexp₁ (ne_of_gt hv_pos), abs_of_pos hv_pos]
    have hcv_emin : F₁.canonicalExp v = emin₁ := by rw [hcvmax] at hle ⊢; omega
    have hcv2max : F₂.canonicalExp v = max (Int.log 2 v + 1 - (p₂ : ℤ)) emin₂ := by
      rw [canonicalExp_FLT hp₂ hexp₂ (ne_of_gt hv_pos), abs_of_pos hv_pos]
    have hlogv_hi : Int.log 2 v + 1 ≤ emin₁ - 1 := by omega
    have hvhi : v < (2 : ℝ) ^ (Int.log 2 v + 1) :=
      Int.lt_zpow_succ_log_self (b := 2) (by norm_num) v
    have hvlt_thresh : v < (2 : ℝ) ^ (emin₁ - 1) :=
      lt_of_lt_of_le hvhi (zpow_le_zpow_right₀ (by norm_num) hlogv_hi)
    have hu2 : ulp F₂ v = (2 : ℝ) ^ (F₂.canonicalExp v) := rfl
    by_cases hfar : v < (2 : ℝ) ^ (emin₁ - 1) - ulp F₂ v / 2
    · exact round_round_div_zero hp₁ hexp₁ hundef₁ hv_pos hfar hz hw
    · -- boundary sliver: impossible by the separation lemma
      exfalso
      rw [not_lt] at hfar
      have hu2pos : (0 : ℝ) < ulp F₂ v := ulp_pos F₂ v
      -- `midp₁ v = 2^(emin₁−1)` (its `⌊·⌋` mantissa is `0`)
      have hma0 : ⌊v * (2 : ℝ) ^ (-(F₁.canonicalExp v))⌋ = 0 := by
        rw [hcv_emin, Int.floor_eq_zero_iff, Set.mem_Ico]
        refine ⟨by positivity, ?_⟩
        calc v * (2 : ℝ) ^ (-emin₁)
            < (2 : ℝ) ^ (emin₁ - 1) * (2 : ℝ) ^ (-emin₁) :=
              mul_lt_mul_of_pos_right hvlt_thresh (by positivity)
          _ = (2 : ℝ) ^ (-1 : ℤ) := by rw [← zpow_add₀ hne]; congr 1; ring
          _ < 1 := by norm_num
      have hmidp : midp F₁ v = (2 : ℝ) ^ (emin₁ - 1) := by
        unfold midp ulp
        rw [rndDown_eq, hcv_emin, Dyadic.coe_ofIntZpow,
            show ⌊v * (2 : ℝ) ^ (-emin₁)⌋ = 0 from by rw [← hcv_emin]; exact hma0]
        push_cast
        rw [hhalf emin₁]; ring
      have hne_mid : v ≠ midp F₁ v := by rw [hmidp]; exact ne_of_lt hvlt_thresh
      have hclose : |v - midp F₁ v| ≤ ulp F₂ v / 2 := by
        rw [hmidp, abs_of_nonpos (by linarith : v - (2 : ℝ) ^ (emin₁ - 1) ≤ 0)]; linarith
      -- bounds needed for `hA`/`hB` in the sliver: `Int.log v = emin₁ − 2`
      have hcv2_le : F₂.canonicalExp v ≤ emin₁ - (p₁ : ℤ) - 2 := by
        rw [hcv2max]; exact max_le (by omega) hemin
      have hLv_lo : emin₁ - 2 ≤ Int.log 2 v := by
        have hu2pos' := zpow_pos (show (0 : ℝ) < 2 by norm_num) (F₂.canonicalExp v)
        have h1 : ulp F₂ v / 2 ≤ (2 : ℝ) ^ (emin₁ - 2) := by
          rw [hu2]
          have hstep : (2 : ℝ) ^ (F₂.canonicalExp v) ≤ (2 : ℝ) ^ (emin₁ - 3) :=
            zpow_le_zpow_right₀ (by norm_num) (by omega)
          have hle32 : (2 : ℝ) ^ (emin₁ - 3) ≤ (2 : ℝ) ^ (emin₁ - 2) :=
            zpow_le_zpow_right₀ (by norm_num) (by omega)
          linarith [hstep, hle32, hu2pos']
        have hh : (2 : ℝ) ^ (emin₁ - 2) = (2 : ℝ) ^ (emin₁ - 1) / 2 := by
          rw [show (emin₁ - 2 : ℤ) = (emin₁ - 1) - 1 from by ring]; exact hhalf (emin₁ - 1)
        have hslv : (2 : ℝ) ^ (emin₁ - 2) ≤ v := by linarith [hfar, h1, hh]
        exact (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hv_pos).mp (by exact_mod_cast hslv)
      obtain ⟨mx, _, hmx⟩ := exists_canonical_rep F₁ hp₁ ha hapos
      obtain ⟨my, _, hmy⟩ := exists_canonical_rep F₁ hp₁ hb hbpos
      have hab : (a : ℝ) = v * (b : ℝ) := by
        rw [hv_def]; exact (div_mul_cancel₀ (a : ℝ) hbne).symm
      have hca_lo : Int.log 2 (a : ℝ) + 1 - (p₁ : ℤ) ≤ F₁.canonicalExp (a : ℝ) := by
        rw [canonicalExp_FLT hp₁ hexp₁ (ne_of_gt hapos), abs_of_pos hapos]; exact le_max_left _ _
      have hcb_lo : Int.log 2 (b : ℝ) + 1 - (p₁ : ℤ) ≤ F₁.canonicalExp (b : ℝ) := by
        rw [canonicalExp_FLT hp₁ hexp₁ (ne_of_gt hbpos), abs_of_pos hbpos]; exact le_max_left _ _
      have hlogpair := log_div_bounds hapos hbpos
      rw [← hv_def] at hlogpair
      obtain ⟨hlog1, hlog2⟩ := hlogpair
      have hA : F₂.canonicalExp v + Int.log 2 (b : ℝ) ≤ F₁.canonicalExp (a : ℝ) := by omega
      have hB : F₂.canonicalExp v + Int.log 2 (b : ℝ)
          ≤ F₁.canonicalExp v - 1 + F₁.canonicalExp (b : ℝ) := by omega
      have hsep := round_round_div_aux hbpos hab ⟨mx, hmx⟩ ⟨my, hmy⟩ hA hB hne_mid
      linarith [hsep, hclose]

/-- The both-positive division hypothesis (`0 < a, 0 < b`), shared by the FLX/FLT
sign wrappers as the base case `hpos`. -/
private abbrev DivPosCase (F₁ F₂ : FiniteFormat) (tb₁ tb₂ : TieBreak) : Prop :=
  ∀ (a b : Dyadic), a ∈ F₁ → b ∈ F₁ → 0 < (a : ℝ) → 0 < (b : ℝ) →
    ∀ (z w : Dyadic), RoundsFinite F₂.unbounded (.nearest tb₂) ((a : ℝ) / (b : ℝ)) z →
      RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w →
      RoundsFinite F₁.unbounded (.nearest tb₁) ((a : ℝ) / (b : ℝ)) w

/-- Extend a both-positive division result (`hpos`) to any numerator sign, with a
positive denominator: `a < 0` flips the quotient's sign (`RoundsFinite.neg_nearest`),
`a = 0` gives the exactly-representable quotient `0` (`rndExact`). -/
private theorem rndDiv_posden_of_pos {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak}
    (hpos : DivPosCase F₁ F₂ tb₁ tb₂)
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
    have hres := hpos (-a) b hna hb hnapos hbpos (-z) (-w) hz2 hw2
    rw [hqval] at hres
    exact (RoundsFinite.neg_nearest F₁.unbounded tb₁ ((a : ℝ) / (b : ℝ)) w).mpr hres
  · -- `a = 0`: the quotient is `0`, exactly representable
    have hval : (a : ℝ) / (b : ℝ) = ((0 : Dyadic) : ℝ) := by rw [hazero, zero_div]; simp
    rw [hval] at hz ⊢
    exact rndExact (F₁ := F₁.unbounded) (F₂ := F₂.unbounded)
      (FiniteFormat.zero_mem F₂.unbounded) hz hw
  · exact hpos a b ha hb hapos hbpos z w hz hw

/-- Extend a both-positive division result to any nonzero denominator: `b < 0`
reduces to `a/b = (−a)/(−b)` (positive denominator, same value). -/
private theorem rndDiv_of_pos {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak}
    (hpos : DivPosCase F₁ F₂ tb₁ tb₂)
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
    exact rndDiv_posden_of_pos hpos hna hnb hnbpos hz hw
  · exact rndDiv_posden_of_pos hpos ha hb hbpos hz hw

/-- **rnd-div, FLX** (Roux Theorem 29, radix 2). For **arbitrary** `a, b ∈ F₁`
with `b ≠ 0` and `p₂ ≥ 2p₁`, double rounding of `a / b` (round to nearest in `F₂`,
then in `F₁`) agrees with rounding `a / b` directly into `F₁`. Matches the
generality of Flocq's `round_round_div_FLX`. -/
theorem rndDiv_FLX {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ+}
    (hp₁ : F₁.p = ((p₁ : ℕ+) : WithTop ℕ+)) (hp₂ : F₂.p = ((p₂ : ℕ+) : WithTop ℕ+))
    (hpp : 2 * p₁ ≤ p₂) (hexp₁ : F₁.exp = ⊥) (hexp₂ : F₂.exp = ⊥)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {a b : Dyadic} (ha : a ∈ F₁) (hb : b ∈ F₁) (hbne : (b : ℝ) ≠ 0)
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((a : ℝ) / (b : ℝ)) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((a : ℝ) / (b : ℝ)) w :=
  rndDiv_of_pos (fun _ _ ha hb hapos hbpos _ _ hz hw =>
    rndDiv_pos hp₁ hp₂ hpp hexp₁ hexp₂ hundef₁ ha hb hapos hbpos hz hw) ha hb hbne hz hw

/-- **rnd-div, FLT** (Roux Theorem 29, radix 2). For **arbitrary** `a, b ∈ F₁`
(FLT) with `b ≠ 0`, `p₂ ≥ 2p₁`, and Roux's underflow bound `emin₂ ≤ emin₁ − p₁ − 2`,
double rounding of `a / b` is innocuous — including underflowing quotients. Matches
Flocq's `round_round_div_FLT`. -/
theorem rndDiv_FLT {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ+}
    {emin₁ emin₂ : ℤ}
    (hp₁ : F₁.p = ((p₁ : ℕ+) : WithTop ℕ+)) (hp₂ : F₂.p = ((p₂ : ℕ+) : WithTop ℕ+))
    (hpp : 2 * p₁ ≤ p₂)
    (hexp₁ : F₁.exp = (emin₁ : WithBot ℤ)) (hexp₂ : F₂.exp = (emin₂ : WithBot ℤ))
    (hemin : emin₂ ≤ emin₁ - (p₁ : ℤ) - 2)
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    {a b : Dyadic} (ha : a ∈ F₁) (hb : b ∈ F₁) (hbne : (b : ℝ) ≠ 0)
    {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) ((a : ℝ) / (b : ℝ)) z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) ((a : ℝ) / (b : ℝ)) w :=
  rndDiv_of_pos (fun _ _ ha hb hapos hbpos _ _ hz hw =>
    rndDiv_pos_FLT hp₁ hp₂ hpp hexp₁ hexp₂ hemin hundef₁ ha hb hapos hbpos hz hw) ha hb hbne hz hw

end Mpfx
