import Mpfx.Rounding

/-!
# Constructive rounding: definitions + soundness helpers

The noncomputable layer of the rounding architecture. See
`Mpfx/Rounding.lean` for the relational spec `Rounds`; this file
provides the function `rnd` and the shared arithmetic helpers used by
the per-mode soundness/uniqueness proofs.

`rnd` is `noncomputable` because of `Int.log : ℝ → ℤ` and because the
`if`-then-else branches reduce undecidable real comparisons via
`Classical.propDecidable`. The bridge lemma `rnd_iff_rounds` connects
this to the relational layer.

Theorems about `Rounds` alone live in `Mpfx/Rounding.lean` and stay
in constructive logic; the classical commitment is isolated here.
-/

namespace Mpfx

-- FLoPS-style: noncomputable definitions rely on Mathlib's
-- `Real.decidableLT`/`decidableEq` plus the classical `propDecidable`
-- fallback for `if-then-else` on undecidable real comparisons. Marked
-- `local` so this taint is scoped per file.
attribute [local instance] Classical.propDecidable

/-- For `r` with `|r| < N`, the floor `⌊r⌋` has `|⌊r⌋| ≤ N`. The
asymmetry: negative floors can saturate (e.g. `⌊-1.5⌋ = -2` with
`|-1.5| < 2` but `|⌊-1.5⌋| = 2`). -/
theorem abs_floor_le_of_abs_lt {r : ℝ} {N : ℤ} (h : |r| < (N : ℝ)) :
    |⌊r⌋| ≤ N := by
  obtain ⟨h_neg, h_pos⟩ := abs_lt.mp h
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have h_lt : (-N - 1 : ℝ) < (⌊r⌋ : ℝ) := by
      have := Int.sub_one_lt_floor r
      linarith
    have : (-N - 1 : ℤ) < ⌊r⌋ := by exact_mod_cast h_lt
    omega
  · have h_lt : (⌊r⌋ : ℝ) < (N : ℝ) :=
      lt_of_le_of_lt (Int.floor_le r) h_pos
    exact_mod_cast h_lt.le

/-- Mirror of `abs_floor_le_of_abs_lt` for the ceiling: positive ceilings
can saturate (e.g. `⌈1.5⌉ = 2` with `|1.5| < 2` but `|⌈1.5⌉| = 2`). -/
theorem abs_ceil_le_of_abs_lt {r : ℝ} {N : ℤ} (h : |r| < (N : ℝ)) :
    |⌈r⌉| ≤ N := by
  obtain ⟨h_neg, h_pos⟩ := abs_lt.mp h
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have h_lt : (-N : ℝ) < (⌈r⌉ : ℝ) :=
      lt_of_lt_of_le h_neg (Int.le_ceil r)
    have : (-N : ℤ) < ⌈r⌉ := by exact_mod_cast h_lt
    omega
  · have h_lt : (⌈r⌉ : ℝ) < (N : ℝ) + 1 := by
      have := Int.ceil_lt_add_one r
      linarith
    have : (⌈r⌉ : ℤ) < N + 1 := by exact_mod_cast h_lt
    omega

/-- Integer-rounding step for the format-agnostic modes. Picks the
integer `c` for which `c · 2^e` is the F-grid value selected by mode
`rm` from input `x`. Parity-aware modes (`.toOdd`, `.nearest .toEven`)
are handled separately by `rndParity` since they need format info to
disambiguate. -/
noncomputable def rndInt (rm : RoundingMode) (x : ℝ) (e : ℤ) : ℤ :=
  let s := x * (2 : ℝ) ^ (-e)
  match rm with
  | .toZero    => if 0 ≤ x then ⌊s⌋ else ⌈s⌉
  | .toNegative => ⌊s⌋
  | .toPositive => ⌈s⌉
  | .awayZero   => if 0 ≤ x then ⌈s⌉ else ⌊s⌋
  | .nearest .awayZero =>
      let lo := ⌊s⌋
      let δ := s - (lo : ℝ)
      if δ < 1/2 then lo
      else if 1/2 < δ then lo + 1
      else if 0 ≤ x then lo + 1 else lo   -- tie: away from zero
  -- .toOdd and .nearest .toEven are handled by `rndParity` (need parity).
  | _ => ⌊s⌋   -- unreachable: filtered out before `rndInt` is called

/-- Parity-aware integer-rounding step. Identifies the two F-adjacents
to `x` at exponent `e` (via floor and ceiling of the scaled mantissa),
then picks the one whose parity satisfies the mode's rule. -/
noncomputable def rndParity (F : ParityFormat) (rm : RoundingMode)
    (x : ℝ) (e : ℤ) : Dyadic :=
  let s := x * (2 : ℝ) ^ (-e)
  let lo : ℤ := ⌊s⌋
  let dlo : Dyadic := Dyadic.ofIntZpow lo e
  let dhi : Dyadic := Dyadic.ofIntZpow (lo + 1) e
  match rm with
  | .toOdd =>
      if (lo : ℝ) = s then dlo                  -- x is exactly on lo
      else if F.IsOdd dlo then dlo else dhi
  | .nearest .toEven =>
      let δ := s - (lo : ℝ)
      if δ < 1/2 then dlo
      else if 1/2 < δ then dhi
      else if F.IsEven dlo then dlo else dhi    -- tie → even
  | _ => dlo   -- unreachable: `rndParity` only called for parity modes

/-- Promote `F : FiniteFormat` to `ParityFormat` from a
`¬ IsUndefined .toOdd` witness. -/
def FiniteFormat.toParityFormatOfToOdd
    (F : FiniteFormat) (h : ¬ F.IsUndefined .toOdd) : ParityFormat := by
  refine ⟨F, ?_⟩
  by_contra h_neg; push Not at h_neg
  exact h ⟨h_neg.1, h_neg.2, Or.inl rfl⟩

/-- Promote `F : FiniteFormat` to `ParityFormat` from a
`¬ IsUndefined (.nearest .toEven)` witness. -/
def FiniteFormat.toParityFormatOfNearestEven
    (F : FiniteFormat) (h : ¬ F.IsUndefined (.nearest .toEven)) : ParityFormat := by
  refine ⟨F, ?_⟩
  by_contra h_neg; push Not at h_neg
  exact h ⟨h_neg.1, h_neg.2, Or.inr rfl⟩

/-- The unbounded rounding step: produce a `Dyadic` per `rm`, *without*
checking `F.b`. Used by `rnd` as the candidate value that the bound check
filters. -/
noncomputable def rndUnbounded (F : FiniteFormat) (rm : RoundingMode) (x : ℝ)
    (h_undef : ¬ F.IsUndefined rm) : Dyadic :=
  if h1 : rm = .toOdd then
    rndParity (F.toParityFormatOfToOdd (h1 ▸ h_undef)) .toOdd x (F.canonicalExp x)
  else if h2 : rm = .nearest .toEven then
    rndParity (F.toParityFormatOfNearestEven (h2 ▸ h_undef))
      (.nearest .toEven) x (F.canonicalExp x)
  else
    Dyadic.ofIntZpow (rndInt rm x (F.canonicalExp x)) (F.canonicalExp x)

/-- The rounded value of `x` in `F` under mode `rm`, as a `RoundResult`.
Dispatches to `rndUnbounded` for the round-without-bound value, then
checks the format's magnitude bound: if the rounded result fits, return
`.finite y`; otherwise `.overflow b` where `b` records the sign of the
would-be result (`true` for positive). -/
noncomputable def rnd (F : FiniteFormat) (rm : RoundingMode) (x : ℝ) : RoundResult :=
  if h_undef : F.IsUndefined rm then
    .undefined
  else
    let y := rndUnbounded F rm x h_undef
    if Format.boundOK F.b y then .finite y
    else .overflow (if (0 : ℚ) < (y : ℚ) then true else false)

/-! ### Soundness of `rndUnbounded`

The two key obligations linking `rnd` and `Rounds`:

* `rndUnbounded_satisfies` — `rndUnbounded F rm x h` is a value
  satisfying `RoundsFinite F.unbounded rm x`.
* `rndUnbounded_unique` — uniquely so: any `y` satisfying that spec
  equals `rndUnbounded F rm x h`.

Together these say `rndUnbounded` *is* the unbounded rounding. They
are mode-specific arithmetic obligations; deferred. -/

/-! Per-mode soundness obligations for `rndUnbounded`. Each is a
mode-specific arithmetic argument over `Int.log`, `Int.floor`,
`Int.ceil`, plus the `canonicalExp`/`rndInt` definitions. -/

/-- Binade lemma for directed-mode minimality: when `z = a · 2^e_a` has
`|a| < 2^p`, `e_a < e`, and `e = log|x|+1-p` (so `e` came from the precision
side of `canonicalExp`), then `|z| < 2^(log|x|)`. Combined with `|x| ≥
2^(log|x|)` this strictly bounds `|z|` below `|x|`. -/
theorem abs_lt_two_pow_log_of_precision {p : ℕ+} {x : ℝ}
    {a e e_a : ℤ} (ha_bound : |a| < (2 : ℤ) ^ (p : ℕ))
    (h_ea_lt : e_a < e) (h_e_eq_log : e = Int.log 2 |x| + 1 - (p : ℤ)) :
    |(a : ℝ) * (2 : ℝ) ^ e_a| < (2 : ℝ) ^ (Int.log 2 |x|) := by
  have h_2ea_pos : (0 : ℝ) < (2 : ℝ) ^ e_a := zpow_pos (by norm_num) _
  have h_abs_bound : (|a| : ℝ) < (2 : ℝ) ^ (p : ℕ) := by exact_mod_cast ha_bound
  have h_pcast : ((p : ℕ+) : ℤ) = ((p : ℕ) : ℤ) := rfl
  rw [abs_mul, abs_of_pos h_2ea_pos]
  calc (|a| : ℝ) * (2 : ℝ) ^ e_a
      < (2 : ℝ) ^ (p : ℕ) * (2 : ℝ) ^ e_a :=
        mul_lt_mul_of_pos_right h_abs_bound h_2ea_pos
    _ = (2 : ℝ) ^ (((p : ℕ) : ℤ) + e_a) := by
        rw [← zpow_natCast (2 : ℝ) (p : ℕ),
            ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    _ ≤ (2 : ℝ) ^ (Int.log 2 |x|) :=
        zpow_le_zpow_right₀ (by norm_num)
          (by linarith [h_ea_lt, h_e_eq_log, h_pcast])

/-- Apply the binade argument in `_toNegative`: if `z = a · 2^e_a ≤ x` is
in the binade-clipped regime, then `z ≤ ⌊x · 2^(-e)⌋ · 2^e`. -/
theorem binade_le_floor {p : ℕ+} {x : ℝ} (hx : x ≠ 0)
    {a e e_a : ℤ} (ha_bound : |a| < (2 : ℤ) ^ (p : ℕ))
    (h_ea_lt : e_a < e) (h_e_eq_log : e = Int.log 2 |x| + 1 - (p : ℤ))
    (hz_le_x : (a : ℝ) * (2 : ℝ) ^ e_a ≤ x) :
    (a : ℝ) * (2 : ℝ) ^ e_a ≤ (⌊x * (2 : ℝ) ^ (-e)⌋ : ℝ) * (2 : ℝ) ^ e := by
  have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have h_2neg_pos : (0 : ℝ) < (2 : ℝ) ^ (-e) := zpow_pos (by norm_num) _
  have h_abs_z := abs_lt_two_pow_log_of_precision ha_bound h_ea_lt h_e_eq_log
  have h_x_ge : (2 : ℝ) ^ (Int.log 2 |x|) ≤ |x| :=
    Int.zpow_log_le_self (b := 2) (by norm_num : (1 : ℕ) < 2) (abs_pos.mpr hx)
  by_cases hx_nn : 0 ≤ x
  · -- x ≥ 0: y ≥ 2^log|x| > |z| ≥ z.
    -- c = ⌊x · 2^(-e)⌋ ≥ 2^(p-1).
    have h_pcast : ((p : ℕ+) : ℤ) = ((p : ℕ) : ℤ) := rfl
    have h_x_scaled_ge : (2 : ℝ) ^ ((p : ℕ) - 1 : ℤ) ≤ x * (2 : ℝ) ^ (-e) := by
      have h_2p_pos : (0 : ℝ) < (2 : ℝ) ^ (((p : ℕ) - 1 : ℤ)) := zpow_pos (by norm_num) _
      have h_2log_x : (2 : ℝ) ^ (Int.log 2 |x|) ≤ x := by
        have habs : |x| = x := abs_of_nonneg hx_nn
        linarith [h_x_ge, habs.symm.le]
      have h_exp_eq : Int.log 2 |x| - e = ((p : ℕ) - 1 : ℤ) := by
        linarith [h_e_eq_log, h_pcast]
      calc (2 : ℝ) ^ ((p : ℕ) - 1 : ℤ)
          = (2 : ℝ) ^ (Int.log 2 |x| - e) := by rw [h_exp_eq]
        _ = (2 : ℝ) ^ (Int.log 2 |x|) * (2 : ℝ) ^ (-e) := by
            rw [show (Int.log 2 |x| - e : ℤ) = (Int.log 2 |x|) + (-e) by ring,
                zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        _ ≤ x * (2 : ℝ) ^ (-e) :=
            mul_le_mul_of_nonneg_right h_2log_x h_2neg_pos.le
    have h_c_ge : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ ⌊x * (2 : ℝ) ^ (-e)⌋ := by
      have hp_pos : 1 ≤ (p : ℕ) := p.pos
      apply Int.le_floor.mpr
      have h_cast : (((2 : ℤ) ^ ((p : ℕ) - 1) : ℤ) : ℝ) =
          (2 : ℝ) ^ ((p : ℕ) - 1 : ℤ) := by
        rw [show ((p : ℕ) - 1 : ℤ) = (((p : ℕ) - 1 : ℕ) : ℤ) by omega,
            zpow_natCast]
        push_cast; rfl
      rw [h_cast]
      exact h_x_scaled_ge
    have h_y_ge : (2 : ℝ) ^ (Int.log 2 |x|) ≤
        (⌊x * (2 : ℝ) ^ (-e)⌋ : ℝ) * (2 : ℝ) ^ e := by
      have h_pcast : ((p : ℕ+) : ℤ) = ((p : ℕ) : ℤ) := rfl
      have h_exp_eq : (((p : ℕ) - 1 : ℤ)) + e = Int.log 2 |x| := by
        linarith [h_e_eq_log, h_pcast]
      calc (2 : ℝ) ^ (Int.log 2 |x|)
          = (2 : ℝ) ^ ((((p : ℕ) - 1 : ℤ)) + e) := by rw [h_exp_eq]
        _ = (2 : ℝ) ^ ((p : ℕ) - 1 : ℤ) * (2 : ℝ) ^ e := by
            rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        _ ≤ (⌊x * (2 : ℝ) ^ (-e)⌋ : ℝ) * (2 : ℝ) ^ e := by
            apply mul_le_mul_of_nonneg_right _ h_2e_pos.le
            have : ((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) ≤ (⌊x * (2 : ℝ) ^ (-e)⌋ : ℝ) := by
              exact_mod_cast h_c_ge
            have h_cast_eq : ((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) =
                (2 : ℝ) ^ ((p : ℕ) - 1 : ℤ) := by
              push_cast
              rw [show ((p : ℕ) - 1 : ℤ) = (((p : ℕ) - 1 : ℕ) : ℤ) by
                    have : 1 ≤ (p : ℕ) := p.pos; omega,
                  zpow_natCast]
            rw [← h_cast_eq]; exact this
    have h_z_lt : (a : ℝ) * (2 : ℝ) ^ e_a ≤ |(a : ℝ) * (2 : ℝ) ^ e_a| :=
      le_abs_self _
    linarith [h_abs_z, h_y_ge, h_z_lt]
  · -- x < 0: hypothesis z ≤ x forces |z| ≥ |x| ≥ 2^log|x|, contradicting |z| < 2^log|x|.
    push Not at hx_nn
    exfalso
    have h_z_neg : (a : ℝ) * (2 : ℝ) ^ e_a < 0 := lt_of_le_of_lt hz_le_x hx_nn
    have h_abs_z_ge : |x| ≤ |(a : ℝ) * (2 : ℝ) ^ e_a| := by
      rw [abs_of_neg hx_nn, abs_of_neg h_z_neg]; linarith
    have h_x_lt : |x| < (2 : ℝ) ^ (Int.log 2 |x|) := by
      have : |(a : ℝ) * (2 : ℝ) ^ e_a| < (2 : ℝ) ^ (Int.log 2 |x|) := h_abs_z
      linarith
    linarith [h_x_ge]

/-- Generic floor-minimality: if `z ∈ F.unbounded` and `z ≤ x`, then `z` is
≤ the floor-projection of `x` at the canonical exponent. Used by `_toNegative`
(directly) and by `_toZero` (for the `0 ≤ x` branch). -/
theorem floor_minimality (F : FiniteFormat) (x : ℝ) {z : Dyadic}
    (hz_prec : Dyadic.precisionAtMost F.p z)
    (hz_quant : Dyadic.quantumAtLeast F.exp z) (hz_le_x : (z : ℝ) ≤ x) :
    (z : ℝ) ≤ (⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋ : ℝ) *
              (2 : ℝ) ^ (F.canonicalExp x) := by
  set e := F.canonicalExp x
  set c := ⌊x * (2 : ℝ) ^ (-e)⌋
  have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  cases hp : F.p with
  | top =>
    cases hexp : F.exp with
    | bot =>
      exfalso
      rcases F.finite with h | h
      · exact h hp
      · exact h hexp
    | coe e' =>
      have h_e_eq : e = e' := by
        change F.canonicalExp x = e'
        unfold FiniteFormat.canonicalExp
        simp [hp, hexp]
      rw [hexp, Dyadic.quantumAtLeast_coe_real] at hz_quant
      obtain ⟨k, hk⟩ := hz_quant
      have h_2e'_pos : (0 : ℝ) < (2 : ℝ) ^ e' := zpow_pos (by norm_num) _
      rw [hk] at hz_le_x
      have h_k_le_x_scale : (k : ℝ) ≤ x * (2 : ℝ) ^ (-e') := by
        have h_eq : (k : ℝ) =
            (k : ℝ) * (2 : ℝ) ^ e' * (2 : ℝ) ^ (-e') := by
          rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
              add_neg_cancel, zpow_zero, mul_one]
        rw [h_eq]
        have h_2neg_pos : (0 : ℝ) < (2 : ℝ) ^ (-e') :=
          zpow_pos (by norm_num) _
        exact mul_le_mul_of_nonneg_right hz_le_x h_2neg_pos.le
      have h_k_le_floor : k ≤ ⌊x * (2 : ℝ) ^ (-e')⌋ :=
        Int.le_floor.mpr h_k_le_x_scale
      rw [hk, h_e_eq]
      have h_c_eq : (c : ℝ) = (⌊x * (2 : ℝ) ^ (-e')⌋ : ℝ) := by
        change (⌊x * (2 : ℝ) ^ (-e)⌋ : ℝ) = (⌊x * (2 : ℝ) ^ (-e')⌋ : ℝ)
        rw [h_e_eq]
      rw [h_c_eq]
      apply mul_le_mul_of_nonneg_right _ h_2e'_pos.le
      exact_mod_cast h_k_le_floor
  | coe p =>
    rw [hp, Dyadic.precisionAtMost_coe_real] at hz_prec
    obtain ⟨a, e_a, hz_repr, ha_bound⟩ := hz_prec
    by_cases h_ea_ge : e ≤ e_a
    · -- integer factor argument
      set diff := (e_a - e).toNat
      have h_diff_eq : (diff : ℤ) = e_a - e :=
        Int.toNat_of_nonneg (by omega)
      have h_factor_real : (a : ℝ) * (2 : ℝ) ^ e_a =
          ((a * 2 ^ diff : ℤ) : ℝ) * (2 : ℝ) ^ e := by
        push_cast
        rw [show ((2 : ℝ) ^ diff : ℝ) = (2 : ℝ) ^ (diff : ℤ)
            from (zpow_natCast _ _).symm]
        rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        congr 2; omega
      rw [hz_repr, h_factor_real]
      have h_le_x : ((a * 2 ^ diff : ℤ) : ℝ) * (2 : ℝ) ^ e ≤ x := by
        rw [← h_factor_real, ← hz_repr]; exact hz_le_x
      have h_factor_le_scaled : ((a * 2 ^ diff : ℤ) : ℝ) ≤
          x * (2 : ℝ) ^ (-e) := by
        have h_2neg_pos : (0 : ℝ) < (2 : ℝ) ^ (-e) :=
          zpow_pos (by norm_num) _
        have h_eq : ((a * 2 ^ diff : ℤ) : ℝ) =
            ((a * 2 ^ diff : ℤ) : ℝ) * (2 : ℝ) ^ e * (2 : ℝ) ^ (-e) := by
          rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
              add_neg_cancel, zpow_zero, mul_one]
        rw [h_eq]
        exact mul_le_mul_of_nonneg_right h_le_x h_2neg_pos.le
      have h_factor_le_c : a * 2 ^ diff ≤ c := by
        change a * 2 ^ diff ≤ ⌊x * (2 : ℝ) ^ (-e)⌋
        exact Int.le_floor.mpr h_factor_le_scaled
      apply mul_le_mul_of_nonneg_right _ h_2e_pos.le
      exact_mod_cast h_factor_le_c
    · -- e_a < e: x = 0 case or binade.
      push Not at h_ea_ge
      by_cases hx : x = 0
      · subst hx
        have hy0 : (c : ℝ) * (2 : ℝ) ^ e = 0 := by
          change (⌊(0 : ℝ) * (2 : ℝ) ^ (-e)⌋ : ℝ) * (2 : ℝ) ^ e = 0
          simp
        rw [hy0, hz_repr] at *
        exact hz_le_x
      · cases hexp : F.exp with
        | coe e' =>
          by_cases h_e'_eq : e' = e
          · rw [hexp, Dyadic.quantumAtLeast_coe_real] at hz_quant
            obtain ⟨k, hk⟩ := hz_quant
            rw [hk]
            have h_2neg_pos : (0 : ℝ) < (2 : ℝ) ^ (-e) :=
              zpow_pos (by norm_num) _
            have h_k_real_le : (k : ℝ) ≤ x * (2 : ℝ) ^ (-e) := by
              have h_le_x : (k : ℝ) * (2 : ℝ) ^ e' ≤ x := by
                rw [← hk]; exact hz_le_x
              have h_eq : (k : ℝ) =
                  (k : ℝ) * (2 : ℝ) ^ e' * (2 : ℝ) ^ (-e) := by
                rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
                    h_e'_eq, add_neg_cancel, zpow_zero, mul_one]
              rw [h_eq]
              exact mul_le_mul_of_nonneg_right h_le_x h_2neg_pos.le
            have h_k_le_c : k ≤ c := by
              change k ≤ ⌊x * (2 : ℝ) ^ (-e)⌋
              exact Int.le_floor.mpr h_k_real_le
            rw [h_e'_eq]
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast h_k_le_c)
              h_2e_pos.le
          · have h_e'_le : e' ≤ e := F.exp_le_canonicalExp x hexp
            have h_e'_lt : e' < e := lt_of_le_of_ne h_e'_le h_e'_eq
            have h_log_gt_e' : e' < Int.log 2 |x| + 1 - (p : ℤ) := by
              have h_canon_eq : e = max (Int.log 2 |x| + 1 - (p : ℤ)) e' := by
                change F.canonicalExp x = _
                unfold FiniteFormat.canonicalExp
                simp [hp, hexp, hx]
              by_contra h_neg
              push Not at h_neg
              have : e = e' := by rw [h_canon_eq]; exact max_eq_right h_neg
              exact h_e'_eq this.symm
            have h_e_eq_log : e = Int.log 2 |x| + 1 - (p : ℤ) := by
              have h_canon_eq : e = max (Int.log 2 |x| + 1 - (p : ℤ)) e' := by
                change F.canonicalExp x = _
                unfold FiniteFormat.canonicalExp
                simp [hp, hexp, hx]
              rw [h_canon_eq]
              exact max_eq_left h_log_gt_e'.le
            rw [hz_repr] at hz_le_x ⊢
            exact binade_le_floor hx ha_bound h_ea_ge h_e_eq_log hz_le_x
        | bot =>
          have h_e_eq_log : e = Int.log 2 |x| + 1 - (p : ℤ) := by
            change F.canonicalExp x = _
            unfold FiniteFormat.canonicalExp
            simp [hp, hexp, hx]
          rw [hz_repr] at hz_le_x ⊢
          exact binade_le_floor hx ha_bound h_ea_ge h_e_eq_log hz_le_x

/-- Mirror of `floor_minimality`: ceil-projection is the smallest F-element
≥ x. Used by `_toPositive` (directly) and by `_toZero` (`x ≤ 0` branch). -/
theorem ceil_minimality (F : FiniteFormat) (x : ℝ) {z : Dyadic}
    (hz_prec : Dyadic.precisionAtMost F.p z)
    (hz_quant : Dyadic.quantumAtLeast F.exp z) (hx_le_z : x ≤ (z : ℝ)) :
    (⌈x * (2 : ℝ) ^ (-(F.canonicalExp x))⌉ : ℝ) *
      (2 : ℝ) ^ (F.canonicalExp x) ≤ (z : ℝ) := by
  -- Reduce to floor_minimality via x ↦ -x, z ↦ -z.
  -- First: -z ∈ F.unbounded? Same precisionAtMost/quantumAtLeast.
  have h_neg_canon : F.canonicalExp (-x) = F.canonicalExp x := by
    unfold FiniteFormat.canonicalExp
    rcases hp : F.p with _ | p
    · rcases hexp : F.exp with _ | e' <;> simp
    · rcases hexp : F.exp with _ | e' <;> simp [abs_neg, neg_eq_zero]
  set e := F.canonicalExp x
  -- Build `(-z) ∈ F.unbounded`'s precision/quantum facts.
  have h_neg_z_prec : Dyadic.precisionAtMost F.p (-z) := by
    cases hp : F.p with
    | top => trivial
    | coe p =>
      rw [hp] at hz_prec
      rw [Dyadic.precisionAtMost_coe_real] at hz_prec
      rw [Dyadic.precisionAtMost_coe_real]
      obtain ⟨a, e_a, hz_repr, ha_bound⟩ := hz_prec
      refine ⟨-a, e_a, ?_, ?_⟩
      · push_cast; rw [hz_repr]; ring
      · rwa [abs_neg]
  have h_neg_z_quant : Dyadic.quantumAtLeast F.exp (-z) := by
    cases hexp : F.exp with
    | bot => trivial
    | coe e' =>
      rw [hexp, Dyadic.quantumAtLeast_coe_real] at hz_quant
      obtain ⟨k, hk⟩ := hz_quant
      rw [Dyadic.quantumAtLeast_coe_real]
      refine ⟨-k, ?_⟩
      push_cast; rw [hk]; ring
  have h_neg_le : ((-z : Dyadic) : ℝ) ≤ -x := by push_cast; linarith
  have hh := floor_minimality F (-x)
    h_neg_z_prec h_neg_z_quant h_neg_le
  rw [h_neg_canon] at hh
  -- hh : (-z) ≤ ⌊-x · 2^(-e)⌋ · 2^e. Now invert.
  have h_floor_eq : ⌊(-x) * (2 : ℝ) ^ (-e)⌋ = -⌈x * (2 : ℝ) ^ (-e)⌉ := by
    rw [show (-x) * (2 : ℝ) ^ (-e) = -(x * (2 : ℝ) ^ (-e)) by ring,
        Int.floor_neg]
  rw [h_floor_eq] at hh
  push_cast at hh
  linarith

/-- `Dyadic.ofIntZpow k e` is in `F.unbounded` provided `e ≥ F.exp` and (when
`F.p` is finite) `|k| ≤ 2^p`. The mantissa-bound boundary case `|k| = 2^p`
is handled by `precisionAtMost_of_abs_le`. -/
theorem ofIntZpow_mem_unbounded (F : FiniteFormat) {k e : ℤ}
    (he_ge : ∀ {e' : ℤ}, F.exp = (e' : WithBot ℤ) → e' ≤ e)
    (hk_bound : ∀ {p : ℕ+}, F.p = ((p : ℕ+) : WithTop ℕ+) →
      |k| ≤ (2 : ℤ) ^ (p : ℕ)) :
    Dyadic.ofIntZpow k e ∈ F.unbounded := by
  refine ⟨?_, ?_, ?_⟩
  · change Dyadic.precisionAtMost F.p (Dyadic.ofIntZpow k e)
    cases hp : F.p with
    | top => trivial
    | coe p =>
      exact Dyadic.precisionAtMost_of_abs_le k e (Dyadic.coe_rat_ofIntZpow k e)
        (hk_bound hp)
  · change Dyadic.quantumAtLeast F.exp (Dyadic.ofIntZpow k e)
    cases hexp : F.exp with
    | bot => trivial
    | coe e' =>
      rw [Dyadic.quantumAtLeast_coe_real]
      have h_e_ge : e' ≤ e := he_ge hexp
      have h_diff_nn : 0 ≤ e - e' := by omega
      refine ⟨k * 2 ^ (e - e').toNat, ?_⟩
      rw [Dyadic.coe_ofIntZpow]
      have h_split : (2 : ℝ) ^ e = (2 : ℝ) ^ (e - e').toNat * (2 : ℝ) ^ e' := by
        rw [show ((2 : ℝ) ^ (e - e').toNat : ℝ) = (2 : ℝ) ^ ((e - e').toNat : ℤ)
            from (zpow_natCast _ _).symm, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
            Int.toNat_of_nonneg h_diff_nn]
        congr 1; ring
      rw [h_split, ← mul_assoc]
      push_cast
      ring
  · change Format.boundOK F.unbounded.b (Dyadic.ofIntZpow k e)
    rw [FiniteFormat.unbounded_b]; trivial

/-- The "rescale back" identity: `x · 2^(-e) · 2^e = x`. Used pervasively
to lift `c ≤ x · 2^(-e)` to `c · 2^e ≤ x` (and similar). -/
theorem mul_zpow_neg_self (x : ℝ) (e : ℤ) :
    x * (2 : ℝ) ^ (-e) * (2 : ℝ) ^ e = x := by
  rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
      neg_add_cancel, zpow_zero, mul_one]

/-- `|⌊x · 2^(-e)⌋ + 1| ≤ 2^p` when `|x · 2^(-e)| < 2^p` (the canonical bound
applied to the upper-grid mantissa). Used in parity-mode proofs where `dhi`'s
mantissa is `lo + 1`. -/
theorem abs_floor_add_one_le_of_abs_lt {r : ℝ} {p : ℕ+}
    (h : |r| < (2 : ℝ) ^ (p : ℕ)) :
    |⌊r⌋ + 1| ≤ (2 : ℤ) ^ (p : ℕ) := by
  obtain ⟨h_neg_lt, h_lt⟩ := abs_lt.mp h
  have h_lo_upper : ⌊r⌋ ≤ (2 : ℤ) ^ (p : ℕ) - 1 := by
    have h1 : (⌊r⌋ : ℝ) ≤ r := Int.floor_le _
    have h2 : (⌊r⌋ : ℝ) < (2 : ℝ) ^ (p : ℕ) := lt_of_le_of_lt h1 h_lt
    have : (⌊r⌋ : ℤ) < ((2 : ℤ) ^ (p : ℕ) : ℤ) := by exact_mod_cast h2
    omega
  have h_lo_lower : -((2 : ℤ) ^ (p : ℕ)) ≤ ⌊r⌋ := by
    have h_floor_succ : r < (⌊r⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    have h_lo_lower_r : -((2 : ℝ) ^ (p : ℕ)) < (⌊r⌋ : ℝ) + 1 := by linarith
    have : -((2 : ℤ) ^ (p : ℕ)) < ⌊r⌋ + 1 := by exact_mod_cast h_lo_lower_r
    omega
  rw [abs_le]; exact ⟨by linarith, by linarith⟩

/-- Canonical-mantissa bound: `|x · 2^(-canonicalExp x)| < 2^p` when `F.p`
is finite. Drives the membership proofs for `floor`/`ceil`/`toZero`/`awayZero`
results across the satisfies theorems. -/
theorem floor_mantissa_lt {F : FiniteFormat} {x : ℝ}
    {p : ℕ+} (hp : F.p = ((p : ℕ+) : WithTop ℕ+)) :
    |x * (2 : ℝ) ^ (-(F.canonicalExp x))| < (2 : ℝ) ^ (p : ℕ) := by
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
    have h_pcast : ((p : ℕ+) : ℤ) = ((p : ℕ) : ℤ) := rfl
    have hle : Int.log 2 |x| + 1 + (-e) ≤ ((p : ℕ) : ℤ) := by
      linarith [h_e_ge, h_pcast]
    rw [h_abs]
    calc |x| * (2 : ℝ) ^ (-e)
        < (2 : ℝ) ^ (Int.log 2 |x| + 1) * (2 : ℝ) ^ (-e) :=
          mul_lt_mul_of_pos_right h_x_lt (zpow_pos (by norm_num) _)
      _ = (2 : ℝ) ^ (Int.log 2 |x| + 1 + (-e)) := by
          rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      _ ≤ (2 : ℝ) ^ ((p : ℕ) : ℤ) := zpow_le_zpow_right₀ (by norm_num) hle
      _ = (2 : ℝ) ^ (p : ℕ) := by rw [zpow_natCast]

/-- `|k| < 2^p` (integers) ⟹ `log₂|k| + 1 ≤ p`. -/
theorem log_lt_p_of_abs_lt_two_pow {p : ℕ+} {k : ℤ}
    (hk : |k| < (2 : ℤ) ^ ((p : ℕ+) : ℕ)) :
    Int.log 2 (|k| : ℝ) + 1 ≤ (((p : ℕ+) : ℕ) : ℤ) := by
  by_cases hk0 : k = 0
  · rw [hk0]
    simp only [Int.cast_zero, abs_zero, Int.log_zero_right, zero_add, Nat.one_le_cast]
    exact_mod_cast (p : ℕ+).pos
  · have h_abs_pos : (0 : ℝ) < (|k| : ℝ) := by
      have h1 : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
      have h2 : (1 : ℝ) ≤ (|k| : ℝ) := by exact_mod_cast h1
      linarith
    have h_abs_lt_zpow : (|k| : ℝ) < (2 : ℝ) ^ (((p : ℕ+) : ℕ) : ℤ) := by
      rw [zpow_natCast]
      have h1 : ((|k| : ℤ) : ℝ) < ((2 : ℤ) ^ ((p : ℕ+) : ℕ) : ℝ) := by
        exact_mod_cast hk
      have h_cast : ((2 : ℤ) ^ ((p : ℕ+) : ℕ) : ℝ) =
          (2 : ℝ) ^ ((p : ℕ+) : ℕ) := by push_cast; rfl
      rw [h_cast] at h1; push_cast at h1; exact h1
    have h_log_lt : Int.log 2 (|k| : ℝ) < (((p : ℕ+) : ℕ) : ℤ) :=
      (Int.lt_zpow_iff_log_lt (by norm_num : 1 < 2) h_abs_pos).mp h_abs_lt_zpow
    linarith

/-- `Int.log 2 ((2 : ℝ) ^ n) = n` for natural `n`. -/
theorem log_two_pow_nat (n : ℕ) : Int.log 2 ((2 : ℝ) ^ n) = (n : ℤ) := by
  rw [show ((2 : ℝ) ^ n) = ((2 : ℝ) ^ (n : ℤ)) from (zpow_natCast (2 : ℝ) n).symm]
  exact Int.log_zpow (by norm_num : 1 < 2) (n : ℤ)

/-- Cast `((2 : ℤ) ^ (p - 1) : ℝ) = (2 : ℝ) ^ (p - 1 : ℤ)`. -/
theorem cast_two_pow_pred {p : ℕ+} :
    ((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) = (2 : ℝ) ^ ((p : ℕ) - 1 : ℤ) := by
  rw [show ((p : ℕ) - 1 : ℤ) = (((p : ℕ) - 1 : ℕ) : ℤ) by
        have : 1 ≤ (p : ℕ) := p.pos; omega, zpow_natCast]
  push_cast; rfl

/-- `2^(p-1) ≤ |k|` (integers) ⟹ `p - 1 ≤ log₂|↑k|`. -/
theorem log_ge_p_pred_of_two_pow_pred_le {p : ℕ+} {k : ℤ}
    (hk : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |k|) :
    ((p : ℕ) : ℤ) - 1 ≤ Int.log 2 |(k : ℝ)| := by
  have h_2pm1_pos : (0 : ℝ) < ((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) := by
    have : (0 : ℤ) < (2 : ℤ) ^ ((p : ℕ) - 1) := by positivity
    exact_mod_cast this
  have h_le_real : ((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) ≤ |(k : ℝ)| := by
    rw [show |(k : ℝ)| = ((|k| : ℤ) : ℝ) from by push_cast; rfl]
    exact_mod_cast hk
  have h_log_mono : Int.log 2 ((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) ≤
      Int.log 2 |(k : ℝ)| :=
    Int.log_mono_right (by linarith) h_le_real
  have h_log_2pm1 : Int.log 2 ((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) =
      (((p : ℕ) - 1 : ℕ) : ℤ) := by
    have h_cast : ((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) =
        (2 : ℝ) ^ ((p : ℕ) - 1 : ℕ) := by push_cast; rfl
    rw [h_cast, log_two_pow_nat]
  rw [h_log_2pm1] at h_log_mono
  have hp_pos : 1 ≤ (p : ℕ) := p.pos
  have h_cast_eq : (((p : ℕ) - 1 : ℕ) : ℤ) = ((p : ℕ) : ℤ) - 1 := by omega
  linarith

/-- If `2^(p-1) ≤ |r|`, then `2^(p-1) ≤ |⌊r⌋|`. Sign-split argument. -/
theorem abs_floor_ge_two_pow_pred {p : ℕ+} {r : ℝ}
    (h_r : ((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) ≤ |r|) :
    (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |⌊r⌋| := by
  by_cases hr_nn : 0 ≤ r
  · have h_lo_nn : 0 ≤ ⌊r⌋ := Int.floor_nonneg.mpr hr_nn
    have h_r_ge : ((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) ≤ r := by
      rw [show |r| = r from abs_of_nonneg hr_nn] at h_r
      exact h_r
    have h_floor_ge : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ ⌊r⌋ := by
      apply Int.le_floor.mpr
      have : (((2 : ℤ) ^ ((p : ℕ) - 1) : ℤ) : ℝ) =
          ((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) := by push_cast; rfl
      rw [this]; exact h_r_ge
    rw [abs_of_nonneg h_lo_nn]; exact h_floor_ge
  · have hr_neg : r < 0 := not_le.mp hr_nn
    have h_r_le : r ≤ -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) := by
      have h_abs_eq : |r| = -r := abs_of_neg hr_neg
      linarith
    have h_floor_le : (⌊r⌋ : ℝ) ≤ r := Int.floor_le _
    have h_lo_le_r : (⌊r⌋ : ℝ) ≤ -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) := by linarith
    have h_lo_le : ⌊r⌋ ≤ -((2 : ℤ) ^ ((p : ℕ) - 1)) := by exact_mod_cast h_lo_le_r
    have h_lo_neg : ⌊r⌋ < 0 := by
      have hpos : (0 : ℤ) < (2 : ℤ) ^ ((p : ℕ) - 1) := by positivity
      linarith
    rw [abs_of_neg h_lo_neg]; linarith

/-- For `x ≠ 0` and `e = log₂|x| + 1 - p`, we have `2^(p-1) ≤ |x · 2^(-e)|`. -/
theorem two_pow_pred_le_scaled {p : ℕ+} {x : ℝ} (hx : x ≠ 0) {e : ℤ}
    (h_e_eq_log : e = Int.log 2 |x| + 1 - ((p : ℕ+) : ℤ)) :
    ((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) ≤ |x * (2 : ℝ) ^ (-e)| := by
  rw [cast_two_pow_pred (p := p)]
  have h_x_ge : (2 : ℝ) ^ (Int.log 2 |x|) ≤ |x| :=
    Int.zpow_log_le_self (b := 2) (by norm_num : (1 : ℕ) < 2) (abs_pos.mpr hx)
  have h_2neg_pos : (0 : ℝ) < (2 : ℝ) ^ (-e) := zpow_pos (by norm_num) _
  have h_abs_s : |x * (2 : ℝ) ^ (-e)| = |x| * (2 : ℝ) ^ (-e) := by
    rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)]
  rw [h_abs_s]
  have h_pcast : ((p : ℕ+) : ℤ) = ((p : ℕ) : ℤ) := rfl
  calc (2 : ℝ) ^ ((p : ℕ) - 1 : ℤ)
      = (2 : ℝ) ^ (Int.log 2 |x| + (-e)) := by
        congr 1; linarith [h_e_eq_log, h_pcast]
    _ = (2 : ℝ) ^ (Int.log 2 |x|) * (2 : ℝ) ^ (-e) := by
        rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    _ ≤ |x| * (2 : ℝ) ^ (-e) :=
        mul_le_mul_of_nonneg_right h_x_ge h_2neg_pos.le


end Mpfx
