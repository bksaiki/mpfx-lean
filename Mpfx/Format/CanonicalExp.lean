import Mpfx.Format.Discrete

/-!
# Floor and ceiling at the canonical exponent

Values at the canonical exponent: floor and ceiling minimality
(`floor_minimality`, `ceil_minimality`), membership of `k · 2^e` once `e` is at
least the quantum (`ofIntZpow_mem_unbounded`), and the mantissa bound
`floor_mantissa_lt`. The closed forms of `canonicalExp` itself are in
`Format/Defs.lean`.
-/

namespace Mpfx

/-! ### Format-dependent scaled-mantissa facts

The companions of the `Mpfx/Utils.lean` block that mention the format. -/

/-- Generic floor-minimality: if `z ∈ F.unbounded` and `z ≤ x`, then `z` is
≤ the floor-projection of `x` at the canonical exponent. Used by `_toNegative`
(directly) and by `_toZero` (for the `0 ≤ x` branch). -/
theorem floor_minimality (F : FiniteFormat) (x : ℝ) {z : Dyadic}
    (hz_prec : Dyadic.precisionAtMost F.p z)
    (hz_quant : Dyadic.quantumAtLeast F.exp z) (hz_le_x : (z : ℝ) ≤ x) :
    (z : ℝ) ≤ (⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋ : ℝ) *
              (2 : ℝ) ^ (F.canonicalExp x) := by
  set e := F.canonicalExp x
  have h2e : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos two_pos e
  -- A multiple of `2^e` at most `x` is at most the floor projection.
  have hmul : ∀ k : ℤ, (k : ℝ) * (2 : ℝ) ^ e ≤ x →
      (k : ℝ) * (2 : ℝ) ^ e ≤ (⌊x * (2 : ℝ) ^ (-e)⌋ : ℝ) * (2 : ℝ) ^ e := fun k hk => by
    have : (k : ℝ) ≤ x * (2 : ℝ) ^ (-e) := by
      rw [zpow_neg, ← div_eq_mul_inv, le_div_iff₀ h2e]; exact hk
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Int.le_floor.mpr this) h2e.le
  have hz : z ∈ F.unbounded := ⟨hz_prec, hz_quant, trivial⟩
  -- If `z`'s own step is at least `x`'s, `z` is a multiple of `2^e`.
  by_cases hce : e ≤ F.canonicalExp (z : ℝ)
  · obtain ⟨m, hm⟩ := F.exists_mul_zpow_canonicalExp hz
    rw [hm.trans (two_zpow_shift m hce)] at hz_le_x ⊢
    exact hmul _ hz_le_x
  push Not at hce
  rcases le_or_gt (z : ℝ) 0 with hz0 | hz0
  · rcases le_or_gt 0 x with hx0 | hx0
    · -- The floor projection of a nonnegative `x` is nonnegative.
      have : (0 : ℝ) ≤ (⌊x * (2 : ℝ) ^ (-e)⌋ : ℝ) := by
        exact_mod_cast Int.floor_nonneg.mpr (mul_nonneg hx0 (zpow_pos two_pos _).le)
      nlinarith
    · -- `z ≤ x < 0` makes `|x| ≤ |z|`, so `cexp x ≤ cexp z`.
      have habs : |x| ≤ |(z : ℝ)| := by
        rw [abs_of_neg hx0, abs_of_nonpos hz0]; linarith
      exact absurd (F.canonicalExp_mono hx0.ne habs) (not_le.mpr hce)
  -- `0 < z ≤ x` with a finer step: the precision term binds at `x`, so `z` lies
  -- below `2^⌊log₂ x⌋`, a multiple of `2^e` at most `x`.
  have hx0 : 0 < x := hz0.trans_le hz_le_x
  set L := Int.log 2 x
  obtain ⟨p, hp, hpz⟩ : ∃ p : ℕ, F.p = p ∧ F.canonicalExp (z : ℝ) < Int.log 2 |x| + 1 - p := by
    by_contra h
    push Not at h
    exact absurd ((F.canonicalExp_le_iff hx0.ne').mpr ⟨h, fun e' he' =>
      F.exp_le_canonicalExp _ he'⟩) (not_le.mpr hce)
  rw [abs_of_pos hx0] at hpz
  have hzL : (z : ℝ) < (2 : ℝ) ^ L := by
    have h1 := F.log_sub_p_le_canonicalExp hz0.ne' hp
    rw [abs_of_pos hz0] at h1
    calc (z : ℝ) < (2 : ℝ) ^ (Int.log 2 (z : ℝ) + 1) := Int.lt_zpow_succ_log_self (by norm_num) _
      _ ≤ (2 : ℝ) ^ L := zpow_le_zpow_right₀ (by norm_num) (by omega)
  have heL : e ≤ L := by
    refine (F.canonicalExp_le_iff hx0.ne').mpr ⟨fun q hq => ?_, fun e' he' => ?_⟩
    · have := F.p_pos hq; rw [abs_of_pos hx0]; omega
    · have h1 := exp_le_log_of_mem F he' hz hz0
      have h2 := Int.log_mono_right (b := 2) hz0 hz_le_x
      omega
  have hLx : (2 : ℝ) ^ L ≤ x := Int.zpow_log_le_self (by norm_num) hx0
  have hpow : (((2 : ℤ) ^ (L - e).toNat : ℤ) : ℝ) * (2 : ℝ) ^ e = (2 : ℝ) ^ L := by
    rw [two_zpow_split_toNat heL]; push_cast; ring
  have h := hmul _ (by rw [hpow]; exact hLx)
  rw [hpow] at h
  linarith

/-- Mirror of `floor_minimality`: ceil-projection is the smallest F-element
≥ x. Used by `_toPositive` (directly) and by `_toZero` (`x ≤ 0` branch). -/
theorem ceil_minimality (F : FiniteFormat) (x : ℝ) {z : Dyadic}
    (hz_prec : Dyadic.precisionAtMost F.p z)
    (hz_quant : Dyadic.quantumAtLeast F.exp z) (hx_le_z : x ≤ (z : ℝ)) :
    (⌈x * (2 : ℝ) ^ (-(F.canonicalExp x))⌉ : ℝ) *
      (2 : ℝ) ^ (F.canonicalExp x) ≤ (z : ℝ) := by
  have hh := floor_minimality F (-x) (Dyadic.precisionAtMost_neg hz_prec)
    (Dyadic.quantumAtLeast_neg hz_quant) (by push_cast; linarith)
  rw [canonicalExp_neg, show (-x) * (2 : ℝ) ^ (-F.canonicalExp x)
    = -(x * (2 : ℝ) ^ (-F.canonicalExp x)) by ring, Int.floor_neg] at hh
  push_cast at hh
  linarith

/-- `Dyadic.ofIntZpow k e` is in `F.unbounded` provided `e ≥ F.exp` and (when
`F.p` is finite) `|k| ≤ 2^p`. The mantissa-bound boundary case `|k| = 2^p`
is handled by `precisionAtMost_of_abs_le`. -/
theorem ofIntZpow_mem_unbounded (F : FiniteFormat) {k e : ℤ}
    (he_ge : ∀ {e' : ℤ}, F.exp = (e' : QExp) → e' ≤ e)
    (hk_bound : ∀ {p : ℕ}, F.p = (p : Prec) →
      |k| ≤ (2 : ℤ) ^ p) :
    Dyadic.ofIntZpow k e ∈ F.unbounded := by
  refine ⟨?_, ?_, ?_⟩
  · change Dyadic.precisionAtMost F.p (Dyadic.ofIntZpow k e)
    cases hp : F.p using ENat.recTopCoe with
    | top => trivial
    | coe p =>
      exact Dyadic.precisionAtMost_of_abs_le (F.p_pos hp) k e
        (Dyadic.coe_rat_ofIntZpow k e) (hk_bound hp)
  · refine Dyadic.quantumAtLeast_ofIntZpow ?_
    cases hexp : F.unbounded.exp using QExp.recBotCoe with
    | bot => exact bot_le
    | coe e' => exact WithBot.coe_le_coe.mpr (he_ge hexp)
  · change Format.boundOK F.unbounded.b (Dyadic.ofIntZpow k e)
    rw [FiniteFormat.unbounded_b]; trivial

/-- Canonical-mantissa bound: `|x · 2^(-canonicalExp x)| < 2^p` when `F.p`
is finite. Drives the membership proofs for `floor`/`ceil`/`toZero`/`awayZero`
results across the satisfies theorems. -/
theorem floor_mantissa_lt {F : FiniteFormat} {x : ℝ}
    {p : ℕ} (hp : F.p = (p : Prec)) :
    |x * (2 : ℝ) ^ (-(F.canonicalExp x))| < (2 : ℝ) ^ p := by
  set e := F.canonicalExp x
  by_cases hx : x = 0
  · subst hx; simp
  · have h_e_ge : Int.log 2 |x| + 1 - (p : ℤ) ≤ e :=
      F.log_sub_p_le_canonicalExp hx hp
    have h_x_lt : |x| < (2 : ℝ) ^ (Int.log 2 |x| + 1) := by
      exact_mod_cast Int.lt_zpow_succ_log_self (b := 2)
        (by norm_num : (1 : ℕ) < 2) |x|
    have h_abs : |x * (2 : ℝ) ^ (-e)| = |x| * (2 : ℝ) ^ (-e) := by
      rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)]
    have hle : Int.log 2 |x| + 1 + (-e) ≤ (p : ℤ) := by
      linarith [h_e_ge]
    rw [h_abs]
    calc |x| * (2 : ℝ) ^ (-e)
        < (2 : ℝ) ^ (Int.log 2 |x| + 1) * (2 : ℝ) ^ (-e) :=
          mul_lt_mul_of_pos_right h_x_lt (zpow_pos (by norm_num) _)
      _ = (2 : ℝ) ^ (Int.log 2 |x| + 1 + (-e)) := by
          rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      _ ≤ (2 : ℝ) ^ (p : ℤ) := zpow_le_zpow_right₀ (by norm_num) hle
      _ = (2 : ℝ) ^ p := by rw [zpow_natCast]

end Mpfx
