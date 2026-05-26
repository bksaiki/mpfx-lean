import Mpfx2.Rounding

/-!
# Constructive rounding function (Mpfx2)

The noncomputable layer of the rounding architecture. See
`Mpfx2/Rounding.lean` for the relational spec `Rounds`; this file
provides the function `rnd` and bridges to the relation.

`rnd` is `noncomputable` because of `Int.log : ℝ → ℤ` and because the
`if`-then-else branches reduce undecidable real comparisons via
`Classical.propDecidable`. The bridge lemma `rnd_iff_rounds` connects
this to the relational layer.

Theorems about `Rounds` alone live in `Mpfx2/Rounding.lean` and stay
in constructive logic; the classical commitment is isolated here.
-/

namespace Mpfx2

-- FLoPS-style: noncomputable definitions rely on Mathlib's
-- `Real.decidableLT`/`decidableEq` plus the classical `propDecidable`
-- fallback for `if-then-else` on undecidable real comparisons. Marked
-- `local` so this taint is scoped to `RoundOp.lean`.
attribute [local instance] Classical.propDecidable

/-- For `r` with `|r| < N`, the floor `⌊r⌋` has `|⌊r⌋| ≤ N`. The
asymmetry: negative floors can saturate (e.g. `⌊-1.5⌋ = -2` with
`|-1.5| < 2` but `|⌊-1.5⌋| = 2`). -/
private theorem abs_floor_le_of_abs_lt {r : ℝ} {N : ℤ} (h : |r| < (N : ℝ)) :
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
private theorem abs_ceil_le_of_abs_lt {r : ℝ} {N : ℤ} (h : |r| < (N : ℝ)) :
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
private def FiniteFormat.toParityFormatOfToOdd
    (F : FiniteFormat) (h : ¬ F.IsUndefined .toOdd) : ParityFormat := by
  refine ⟨F, ?_⟩
  by_contra h_neg; push Not at h_neg
  exact h ⟨h_neg.1, h_neg.2, Or.inl rfl⟩

/-- Promote `F : FiniteFormat` to `ParityFormat` from a
`¬ IsUndefined (.nearest .toEven)` witness. -/
private def FiniteFormat.toParityFormatOfNearestEven
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
    else .overflow (if (0 : ℝ) < (y : ℝ) then true else false)

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
private theorem abs_lt_two_pow_log_of_precision {p : ℕ+} {x : ℝ}
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
private theorem binade_le_floor {p : ℕ+} {x : ℝ} (hx : x ≠ 0)
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

/-- Mirror of `binade_le_floor` for ceil/toPositive minimality. -/
private theorem ceil_le_binade {p : ℕ+} {x : ℝ} (hx : x ≠ 0)
    {a e e_a : ℤ} (ha_bound : |a| < (2 : ℤ) ^ (p : ℕ))
    (h_ea_lt : e_a < e) (h_e_eq_log : e = Int.log 2 |x| + 1 - (p : ℤ))
    (hx_le_z : x ≤ (a : ℝ) * (2 : ℝ) ^ e_a) :
    (⌈x * (2 : ℝ) ^ (-e)⌉ : ℝ) * (2 : ℝ) ^ e ≤ (a : ℝ) * (2 : ℝ) ^ e_a := by
  have hnx : -x ≠ 0 := neg_ne_zero.mpr hx
  have hna_bound : |(-a)| < (2 : ℤ) ^ (p : ℕ) := by rw [abs_neg]; exact ha_bound
  have h_e_eq_log_neg : e = Int.log 2 |-x| + 1 - (p : ℤ) := by
    rw [abs_neg]; exact h_e_eq_log
  have h_neg_z_le : ((-a : ℤ) : ℝ) * (2 : ℝ) ^ e_a ≤ -x := by push_cast; linarith
  have hh := binade_le_floor hnx hna_bound h_ea_lt h_e_eq_log_neg h_neg_z_le
  have h_floor_eq : ⌊(-x) * (2 : ℝ) ^ (-e)⌋ = -⌈x * (2 : ℝ) ^ (-e)⌉ := by
    rw [show (-x) * (2 : ℝ) ^ (-e) = -(x * (2 : ℝ) ^ (-e)) by ring,
        Int.floor_neg]
  rw [h_floor_eq] at hh
  push_cast at hh
  linarith

/-- Generic floor-minimality: if `z ∈ F.unbounded` and `z ≤ x`, then `z` is
≤ the floor-projection of `x` at the canonical exponent. Used by `_toNegative`
(directly) and by `_toZero` (for the `0 ≤ x` branch). -/
private theorem floor_minimality (F : FiniteFormat) (x : ℝ) {z : Dyadic}
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
      rw [hexp, Dyadic.quantumAtLeast_coe] at hz_quant
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
    rw [hp, Dyadic.precisionAtMost_coe] at hz_prec
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
          · rw [hexp, Dyadic.quantumAtLeast_coe] at hz_quant
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
private theorem ceil_minimality (F : FiniteFormat) (x : ℝ) {z : Dyadic}
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
      rw [Dyadic.precisionAtMost_coe] at hz_prec
      rw [Dyadic.precisionAtMost_coe]
      obtain ⟨a, e_a, hz_repr, ha_bound⟩ := hz_prec
      refine ⟨-a, e_a, ?_, ?_⟩
      · push_cast; rw [hz_repr]; ring
      · rwa [abs_neg]
  have h_neg_z_quant : Dyadic.quantumAtLeast F.exp (-z) := by
    cases hexp : F.exp with
    | bot => trivial
    | coe e' =>
      rw [hexp, Dyadic.quantumAtLeast_coe] at hz_quant
      obtain ⟨k, hk⟩ := hz_quant
      rw [Dyadic.quantumAtLeast_coe]
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
private theorem ofIntZpow_mem_unbounded (F : FiniteFormat) {k e : ℤ}
    (he_ge : ∀ {e' : ℤ}, F.exp = (e' : WithBot ℤ) → e' ≤ e)
    (hk_bound : ∀ {p : ℕ+}, F.p = ((p : ℕ+) : WithTop ℕ+) →
      |k| ≤ (2 : ℤ) ^ (p : ℕ)) :
    Dyadic.ofIntZpow k e ∈ F.unbounded := by
  refine ⟨?_, ?_, ?_⟩
  · change Dyadic.precisionAtMost F.p (Dyadic.ofIntZpow k e)
    cases hp : F.p with
    | top => trivial
    | coe p =>
      exact Dyadic.precisionAtMost_of_abs_le k e (Dyadic.coe_ofIntZpow k e)
        (hk_bound hp)
  · change Dyadic.quantumAtLeast F.exp (Dyadic.ofIntZpow k e)
    cases hexp : F.exp with
    | bot => trivial
    | coe e' =>
      rw [Dyadic.quantumAtLeast_coe]
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
private theorem mul_zpow_neg_self (x : ℝ) (e : ℤ) :
    x * (2 : ℝ) ^ (-e) * (2 : ℝ) ^ e = x := by
  rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
      neg_add_cancel, zpow_zero, mul_one]

/-- `|⌊x · 2^(-e)⌋ + 1| ≤ 2^p` when `|x · 2^(-e)| < 2^p` (the canonical bound
applied to the upper-grid mantissa). Used in parity-mode proofs where `dhi`'s
mantissa is `lo + 1`. -/
private theorem abs_floor_add_one_le_of_abs_lt {r : ℝ} {p : ℕ+}
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
private theorem floor_mantissa_lt {F : FiniteFormat} {x : ℝ}
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
private theorem log_lt_p_of_abs_lt_two_pow {p : ℕ+} {k : ℤ}
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
private theorem log_two_pow_nat (n : ℕ) : Int.log 2 ((2 : ℝ) ^ n) = (n : ℤ) := by
  rw [show ((2 : ℝ) ^ n) = ((2 : ℝ) ^ (n : ℤ)) from (zpow_natCast (2 : ℝ) n).symm]
  exact Int.log_zpow (by norm_num : 1 < 2) (n : ℤ)

/-- Cast `((2 : ℤ) ^ (p - 1) : ℝ) = (2 : ℝ) ^ (p - 1 : ℤ)`. -/
private theorem cast_two_pow_pred {p : ℕ+} :
    ((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) = (2 : ℝ) ^ ((p : ℕ) - 1 : ℤ) := by
  rw [show ((p : ℕ) - 1 : ℤ) = (((p : ℕ) - 1 : ℕ) : ℤ) by
        have : 1 ≤ (p : ℕ) := p.pos; omega, zpow_natCast]
  push_cast; rfl

/-- `2^(p-1) ≤ |k|` (integers) ⟹ `p - 1 ≤ log₂|↑k|`. -/
private theorem log_ge_p_pred_of_two_pow_pred_le {p : ℕ+} {k : ℤ}
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
private theorem abs_floor_ge_two_pow_pred {p : ℕ+} {r : ℝ}
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
private theorem two_pow_pred_le_scaled {p : ℕ+} {x : ℝ} (hx : x ≠ 0) {e : ℤ}
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

theorem rndUnbounded_satisfies_toNegative (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .toNegative) :
    RoundsFinite F.unbounded .toNegative x (rndUnbounded F .toNegative x h) := by
  have h_rnd_eq : rndUnbounded F .toNegative x h =
      Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋ (F.canonicalExp x) := by
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.toNegative : RoundingMode) ≠ .toOdd)]
    rw [dif_neg (by decide : (RoundingMode.toNegative : RoundingMode) ≠ .nearest .toEven)]
    rfl
  rw [h_rnd_eq]
  set e := F.canonicalExp x
  set c := ⌊x * (2 : ℝ) ^ (-e)⌋
  set y : Dyadic := Dyadic.ofIntZpow c e
  have h_y_real : (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ e := Dyadic.coe_ofIntZpow c e
  have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  -- Membership via `ofIntZpow_mem_unbounded`.
  have h_c_bound : ∀ {p : ℕ+}, F.p = ((p : ℕ+) : WithTop ℕ+) →
      |c| ≤ (2 : ℤ) ^ (p : ℕ) := fun hp => by
    apply abs_floor_le_of_abs_lt
    push_cast; exact floor_mantissa_lt hp
  have h_mem : y ∈ F.unbounded :=
    ofIntZpow_mem_unbounded F (fun hexp => F.exp_le_canonicalExp x hexp) h_c_bound
  obtain ⟨h_prec, h_quant, h_bnd⟩ := h_mem
  refine ⟨⟨h_prec, h_quant, h_bnd⟩, ?_, ?_⟩
  · -- (y : ℝ) ≤ x
    rw [h_y_real, ← mul_zpow_neg_self x e]
    exact mul_le_mul_of_nonneg_right (Int.floor_le _) h_2e_pos.le
  · -- minimality via `floor_minimality` helper.
    intro z hz_mem hz_le_x
    obtain ⟨hz_prec, hz_quant, _⟩ := hz_mem
    rw [h_y_real]
    exact floor_minimality F
      x hz_prec hz_quant hz_le_x

theorem rndUnbounded_satisfies_toPositive (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .toPositive) :
    RoundsFinite F.unbounded .toPositive x (rndUnbounded F .toPositive x h) := by
  have h_rnd_eq : rndUnbounded F .toPositive x h =
      Dyadic.ofIntZpow ⌈x * (2 : ℝ) ^ (-(F.canonicalExp x))⌉ (F.canonicalExp x) := by
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.toPositive : RoundingMode) ≠ .toOdd)]
    rw [dif_neg (by decide : (RoundingMode.toPositive : RoundingMode) ≠ .nearest .toEven)]
    rfl
  rw [h_rnd_eq]
  set e := F.canonicalExp x
  set c := ⌈x * (2 : ℝ) ^ (-e)⌉
  set y : Dyadic := Dyadic.ofIntZpow c e
  have h_y_real : (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ e := Dyadic.coe_ofIntZpow c e
  have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have h_c_bound : ∀ {p : ℕ+}, F.p = ((p : ℕ+) : WithTop ℕ+) →
      |c| ≤ (2 : ℤ) ^ (p : ℕ) := fun hp => by
    apply abs_ceil_le_of_abs_lt
    push_cast; exact floor_mantissa_lt hp
  have h_mem : y ∈ F.unbounded :=
    ofIntZpow_mem_unbounded F (fun hexp => F.exp_le_canonicalExp x hexp) h_c_bound
  obtain ⟨h_prec, h_quant, h_bnd⟩ := h_mem
  refine ⟨⟨h_prec, h_quant, h_bnd⟩, ?_, ?_⟩
  · -- x ≤ (y : ℝ).
    rw [h_y_real, ← mul_zpow_neg_self x e]
    exact mul_le_mul_of_nonneg_right (Int.le_ceil _) h_2e_pos.le
  · -- minimality via `ceil_minimality` helper.
    intro z hz_mem hx_le_z
    obtain ⟨hz_prec, hz_quant, _⟩ := hz_mem
    rw [h_y_real]
    exact ceil_minimality F
      x hz_prec hz_quant hx_le_z

theorem rndUnbounded_satisfies_toZero (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .toZero) :
    RoundsFinite F.unbounded .toZero x (rndUnbounded F .toZero x h) := by
  have h_rnd_eq : rndUnbounded F .toZero x h =
      Dyadic.ofIntZpow (rndInt .toZero x (F.canonicalExp x)) (F.canonicalExp x) := by
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.toZero : RoundingMode) ≠ .toOdd)]
    rw [dif_neg (by decide : (RoundingMode.toZero : RoundingMode) ≠ .nearest .toEven)]
  rw [h_rnd_eq]
  set e := F.canonicalExp x
  set c := rndInt .toZero x e
  set y : Dyadic := Dyadic.ofIntZpow c e
  have h_y_real : (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ e := Dyadic.coe_ofIntZpow c e
  have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have h_c_eq : c = if 0 ≤ x then ⌊x * (2 : ℝ) ^ (-e)⌋ else ⌈x * (2 : ℝ) ^ (-e)⌉ := by
    change rndInt .toZero x e = _
    rfl
  have h_c_bound : ∀ {p : ℕ+}, F.p = ((p : ℕ+) : WithTop ℕ+) →
      |c| ≤ (2 : ℤ) ^ (p : ℕ) := fun hp => by
    rw [h_c_eq]
    by_cases hx_nn : 0 ≤ x
    · rw [if_pos hx_nn]
      apply abs_floor_le_of_abs_lt
      push_cast; exact floor_mantissa_lt hp
    · rw [if_neg hx_nn]
      apply abs_ceil_le_of_abs_lt
      push_cast; exact floor_mantissa_lt hp
  have h_mem : y ∈ F.unbounded :=
    ofIntZpow_mem_unbounded F (fun hexp => F.exp_le_canonicalExp x hexp) h_c_bound
  obtain ⟨h_prec, h_quant, h_bnd⟩ := h_mem
  refine ⟨⟨h_prec, h_quant, h_bnd⟩, ?_, ?_, ?_⟩
  · -- |y| ≤ |x|: sign-split.
    rw [h_y_real]
    rw [show (c : ℝ) * (2 : ℝ) ^ e = (c : ℝ) * (2 : ℝ) ^ e from rfl]
    by_cases hx_nn : 0 ≤ x
    · -- x ≥ 0: c = ⌊s⌋, c · 2^e ≤ x, also c · 2^e ≥ 0.
      have h_c : c = ⌊x * (2 : ℝ) ^ (-e)⌋ := by rw [h_c_eq, if_pos hx_nn]
      have h_floor_le : (c : ℝ) ≤ x * (2 : ℝ) ^ (-e) := by rw [h_c]; exact Int.floor_le _
      have h_floor_nn : 0 ≤ c := by
        rw [h_c]; exact Int.floor_nonneg.mpr (mul_nonneg hx_nn (zpow_pos (by norm_num) _).le)
      have hy_nn : 0 ≤ (c : ℝ) * (2 : ℝ) ^ e :=
        mul_nonneg (by exact_mod_cast h_floor_nn) h_2e_pos.le
      rw [abs_of_nonneg hy_nn, abs_of_nonneg hx_nn, ← mul_zpow_neg_self x e]
      exact mul_le_mul_of_nonneg_right h_floor_le h_2e_pos.le
    · -- x < 0: c = ⌈s⌉, x ≤ c · 2^e ≤ 0.
      push Not at hx_nn
      have h_c : c = ⌈x * (2 : ℝ) ^ (-e)⌉ := by rw [h_c_eq, if_neg (not_le.mpr hx_nn)]
      have h_s_neg : x * (2 : ℝ) ^ (-e) < 0 :=
        mul_neg_of_neg_of_pos hx_nn (zpow_pos (by norm_num) _)
      have h_ceil_le : x * (2 : ℝ) ^ (-e) ≤ (c : ℝ) := by rw [h_c]; exact Int.le_ceil _
      have h_ceil_np : c ≤ 0 := by
        rw [h_c]
        exact Int.ceil_le.mpr (by push_cast; exact h_s_neg.le)
      have hy_np : (c : ℝ) * (2 : ℝ) ^ e ≤ 0 :=
        mul_nonpos_iff.mpr (Or.inr ⟨by exact_mod_cast h_ceil_np, h_2e_pos.le⟩)
      rw [abs_of_nonpos hy_np, abs_of_neg hx_nn]
      have hmul : x * (2 : ℝ) ^ (-e) * (2 : ℝ) ^ e ≤ (c : ℝ) * (2 : ℝ) ^ e :=
        mul_le_mul_of_nonneg_right h_ceil_le h_2e_pos.le
      rw [mul_zpow_neg_self] at hmul
      linarith
  · -- y · x ≥ 0: sign-split.
    rw [h_y_real]
    by_cases hx_nn : 0 ≤ x
    · -- x ≥ 0: c ≥ 0 (floor of nonneg), so c · 2^e · x ≥ 0.
      have h_c : c = ⌊x * (2 : ℝ) ^ (-e)⌋ := by rw [h_c_eq, if_pos hx_nn]
      have h_c_nn : 0 ≤ c := by
        rw [h_c]; exact Int.floor_nonneg.mpr (mul_nonneg hx_nn (zpow_pos (by norm_num) _).le)
      have h_y_nn : 0 ≤ (c : ℝ) * (2 : ℝ) ^ e :=
        mul_nonneg (by exact_mod_cast h_c_nn) h_2e_pos.le
      exact mul_nonneg h_y_nn hx_nn
    · -- x < 0: c ≤ 0 (ceil of nonpos), so c · 2^e ≤ 0 and x < 0, product ≥ 0.
      push Not at hx_nn
      have h_c : c = ⌈x * (2 : ℝ) ^ (-e)⌉ := by rw [h_c_eq, if_neg (not_le.mpr hx_nn)]
      have h_s_neg : x * (2 : ℝ) ^ (-e) < 0 :=
        mul_neg_of_neg_of_pos hx_nn (zpow_pos (by norm_num) _)
      have h_c_np : c ≤ 0 := by
        rw [h_c]
        exact Int.ceil_le.mpr (by push_cast; exact h_s_neg.le)
      have h_y_np : (c : ℝ) * (2 : ℝ) ^ e ≤ 0 :=
        mul_nonpos_iff.mpr (Or.inr ⟨by exact_mod_cast h_c_np, h_2e_pos.le⟩)
      exact mul_nonneg_iff.mpr (Or.inr ⟨h_y_np, hx_nn.le⟩)
  · -- minimality: sign-split, reduce to floor/ceil minimality.
    intro z hz_mem hz_abs_le hz_mul_x
    obtain ⟨hz_prec, hz_quant, _⟩ := hz_mem
    rw [h_y_real]
    by_cases hx_nn : 0 ≤ x
    · -- x ≥ 0: y = ⌊x · 2^(-e)⌋ · 2^e ≥ 0, z ≥ 0; reduce to `floor_minimality`.
      have h_c_int : c = ⌊x * (2 : ℝ) ^ (-e)⌋ := by
        rw [h_c_eq]; simp [if_pos hx_nn]
      have h_floor_nn : 0 ≤ ⌊x * (2 : ℝ) ^ (-e)⌋ :=
        Int.floor_nonneg.mpr (mul_nonneg hx_nn (zpow_pos (by norm_num) _).le)
      have hy_nn : 0 ≤ (c : ℝ) * (2 : ℝ) ^ e := by
        rw [show (c : ℝ) = (⌊x * (2 : ℝ) ^ (-e)⌋ : ℝ) from by exact_mod_cast h_c_int]
        exact mul_nonneg (by exact_mod_cast h_floor_nn) h_2e_pos.le
      have hz_nn : 0 ≤ (z : ℝ) := by
        rcases eq_or_lt_of_le hx_nn with hx_eq | hx_pos
        · have hx0 : x = 0 := hx_eq.symm
          rw [hx0, abs_zero] at hz_abs_le
          have : (z : ℝ) = 0 := abs_eq_zero.mp (le_antisymm hz_abs_le (abs_nonneg _))
          linarith
        · by_contra hz_neg
          push Not at hz_neg
          have : (z : ℝ) * x < 0 := mul_neg_of_neg_of_pos hz_neg hx_pos
          linarith
      have hz_le_x : (z : ℝ) ≤ x := by
        have h1 : |x| = x := abs_of_nonneg hx_nn
        have h2 : |(z : ℝ)| = z := abs_of_nonneg hz_nn
        linarith [hz_abs_le, h1, h2]
      rw [abs_of_nonneg hz_nn, abs_of_nonneg hy_nn]
      rw [show (c : ℝ) = (⌊x * (2 : ℝ) ^ (-e)⌋ : ℝ) from by exact_mod_cast h_c_int]
      exact floor_minimality F x hz_prec hz_quant hz_le_x
    · -- x < 0: y = ⌈x · 2^(-e)⌉ · 2^e ≤ 0, z ≤ 0; reduce to `ceil_minimality`.
      push Not at hx_nn
      have h_c_int : c = ⌈x * (2 : ℝ) ^ (-e)⌉ := by
        rw [h_c_eq]; simp [if_neg (not_le.mpr hx_nn)]
      have h_s_neg : x * (2 : ℝ) ^ (-e) < 0 :=
        mul_neg_of_neg_of_pos hx_nn (zpow_pos (by norm_num) _)
      have h_ceil_np : ⌈x * (2 : ℝ) ^ (-e)⌉ ≤ 0 :=
        Int.ceil_le.mpr (by push_cast; exact h_s_neg.le)
      have hy_np : (c : ℝ) * (2 : ℝ) ^ e ≤ 0 := by
        rw [show (c : ℝ) = (⌈x * (2 : ℝ) ^ (-e)⌉ : ℝ) from by exact_mod_cast h_c_int]
        exact mul_nonpos_iff.mpr (Or.inr ⟨by exact_mod_cast h_ceil_np, h_2e_pos.le⟩)
      have hz_np : (z : ℝ) ≤ 0 := by
        by_contra hz_pos
        push Not at hz_pos
        have : (z : ℝ) * x < 0 := mul_neg_of_pos_of_neg hz_pos hx_nn
        linarith
      have hx_le_z : x ≤ (z : ℝ) := by
        have h1 : |x| = -x := abs_of_neg hx_nn
        have h2 : |(z : ℝ)| = -z := abs_of_nonpos hz_np
        linarith [hz_abs_le, h1, h2]
      rw [abs_of_nonpos hz_np, abs_of_nonpos hy_np]
      rw [show (c : ℝ) = (⌈x * (2 : ℝ) ^ (-e)⌉ : ℝ) from by exact_mod_cast h_c_int]
      have := ceil_minimality F x hz_prec hz_quant hx_le_z
      linarith

theorem rndUnbounded_satisfies_awayZero (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .awayZero) :
    RoundsFinite F.unbounded .awayZero x (rndUnbounded F .awayZero x h) := by
  have h_rnd_eq : rndUnbounded F .awayZero x h =
      Dyadic.ofIntZpow (rndInt .awayZero x (F.canonicalExp x)) (F.canonicalExp x) := by
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.awayZero : RoundingMode) ≠ .toOdd)]
    rw [dif_neg (by decide : (RoundingMode.awayZero : RoundingMode) ≠ .nearest .toEven)]
  rw [h_rnd_eq]
  set e := F.canonicalExp x
  set c := rndInt .awayZero x e
  set y : Dyadic := Dyadic.ofIntZpow c e
  have h_y_real : (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ e := Dyadic.coe_ofIntZpow c e
  have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have h_c_eq : c = if 0 ≤ x then ⌈x * (2 : ℝ) ^ (-e)⌉ else ⌊x * (2 : ℝ) ^ (-e)⌋ := by
    change rndInt .awayZero x e = _
    rfl
  have h_c_bound : ∀ {p : ℕ+}, F.p = ((p : ℕ+) : WithTop ℕ+) →
      |c| ≤ (2 : ℤ) ^ (p : ℕ) := fun hp => by
    rw [h_c_eq]
    by_cases hx_nn : 0 ≤ x
    · rw [if_pos hx_nn]
      apply abs_ceil_le_of_abs_lt
      push_cast; exact floor_mantissa_lt hp
    · rw [if_neg hx_nn]
      apply abs_floor_le_of_abs_lt
      push_cast; exact floor_mantissa_lt hp
  have h_mem : y ∈ F.unbounded :=
    ofIntZpow_mem_unbounded F (fun hexp => F.exp_le_canonicalExp x hexp) h_c_bound
  obtain ⟨h_prec, h_quant, h_bnd⟩ := h_mem
  refine ⟨⟨h_prec, h_quant, h_bnd⟩, ?_, ?_, ?_⟩
  · -- |x| ≤ |y|: sign-split. RAZ rounds away from zero, so |y| ≥ |x|.
    rw [h_y_real]
    by_cases hx_nn : 0 ≤ x
    · -- x ≥ 0: c = ⌈s⌉, c · 2^e ≥ x ≥ 0.
      have h_c : c = ⌈x * (2 : ℝ) ^ (-e)⌉ := by rw [h_c_eq, if_pos hx_nn]
      have h_ceil_ge : x * (2 : ℝ) ^ (-e) ≤ (c : ℝ) := by rw [h_c]; exact Int.le_ceil _
      have h_ceil_nn : 0 ≤ c := by
        rw [h_c]; exact Int.ceil_nonneg (mul_nonneg hx_nn (zpow_pos (by norm_num) _).le)
      have hy_nn : 0 ≤ (c : ℝ) * (2 : ℝ) ^ e :=
        mul_nonneg (by exact_mod_cast h_ceil_nn) h_2e_pos.le
      rw [abs_of_nonneg hy_nn, abs_of_nonneg hx_nn, ← mul_zpow_neg_self x e]
      exact mul_le_mul_of_nonneg_right h_ceil_ge h_2e_pos.le
    · -- x < 0: c = ⌊s⌋, c · 2^e ≤ x < 0.
      push Not at hx_nn
      have h_c : c = ⌊x * (2 : ℝ) ^ (-e)⌋ := by rw [h_c_eq, if_neg (not_le.mpr hx_nn)]
      have h_s_neg : x * (2 : ℝ) ^ (-e) < 0 :=
        mul_neg_of_neg_of_pos hx_nn (zpow_pos (by norm_num) _)
      have h_floor_le : (c : ℝ) ≤ x * (2 : ℝ) ^ (-e) := by rw [h_c]; exact Int.floor_le _
      have h_c_neg : c < 0 := by
        rw [h_c]
        exact Int.floor_lt.mpr (by push_cast; exact h_s_neg)
      have hy_np : (c : ℝ) * (2 : ℝ) ^ e ≤ 0 :=
        mul_nonpos_iff.mpr (Or.inr ⟨by exact_mod_cast h_c_neg.le, h_2e_pos.le⟩)
      rw [abs_of_nonpos hy_np, abs_of_neg hx_nn]
      have hmul : (c : ℝ) * (2 : ℝ) ^ e ≤ x * (2 : ℝ) ^ (-e) * (2 : ℝ) ^ e :=
        mul_le_mul_of_nonneg_right h_floor_le h_2e_pos.le
      rw [mul_zpow_neg_self] at hmul
      linarith
  · -- y · x ≥ 0
    rw [h_y_real]
    by_cases hx_nn : 0 ≤ x
    · have h_c : c = ⌈x * (2 : ℝ) ^ (-e)⌉ := by rw [h_c_eq, if_pos hx_nn]
      have h_c_nn : 0 ≤ c := by
        rw [h_c]; exact Int.ceil_nonneg (mul_nonneg hx_nn (zpow_pos (by norm_num) _).le)
      have h_y_nn : 0 ≤ (c : ℝ) * (2 : ℝ) ^ e :=
        mul_nonneg (by exact_mod_cast h_c_nn) h_2e_pos.le
      exact mul_nonneg h_y_nn hx_nn
    · push Not at hx_nn
      have h_c : c = ⌊x * (2 : ℝ) ^ (-e)⌋ := by rw [h_c_eq, if_neg (not_le.mpr hx_nn)]
      have h_s_neg : x * (2 : ℝ) ^ (-e) < 0 :=
        mul_neg_of_neg_of_pos hx_nn (zpow_pos (by norm_num) _)
      have h_c_neg : c < 0 := by
        rw [h_c]
        exact Int.floor_lt.mpr (by push_cast; exact h_s_neg)
      have h_y_np : (c : ℝ) * (2 : ℝ) ^ e ≤ 0 :=
        mul_nonpos_iff.mpr (Or.inr ⟨by exact_mod_cast h_c_neg.le, h_2e_pos.le⟩)
      exact mul_nonneg_iff.mpr (Or.inr ⟨h_y_np, hx_nn.le⟩)
  · -- minimality: sign-split, reduce to ceil/floor minimality (mirror of `_toZero`).
    intro z hz_mem hz_abs_ge hz_mul_x
    obtain ⟨hz_prec, hz_quant, _⟩ := hz_mem
    rw [h_y_real]
    by_cases hx0 : x = 0
    · -- x = 0: c = ⌈0⌉ = 0, y = 0. Need |y| = 0 ≤ |z| (always true).
      have h_c_int : c = 0 := by
        subst hx0
        rw [h_c_eq]; simp
      rw [show (c : ℝ) = 0 from by exact_mod_cast h_c_int]
      simp [abs_nonneg]
    by_cases hx_nn : 0 ≤ x
    · -- 0 < x (since x ≠ 0): y = ⌈⌉ · 2^e ≥ 0, |x| ≤ |z| ⟹ x ≤ z; apply `ceil_minimality`.
      have hx_pos : 0 < x := lt_of_le_of_ne hx_nn (Ne.symm hx0)
      have h_c_int : c = ⌈x * (2 : ℝ) ^ (-e)⌉ := by
        rw [h_c_eq]; simp [if_pos hx_nn]
      have h_ceil_nn : 0 ≤ ⌈x * (2 : ℝ) ^ (-e)⌉ :=
        Int.ceil_nonneg (mul_nonneg hx_nn (zpow_pos (by norm_num) _).le)
      have hy_nn : 0 ≤ (c : ℝ) * (2 : ℝ) ^ e := by
        rw [show (c : ℝ) = (⌈x * (2 : ℝ) ^ (-e)⌉ : ℝ) from by exact_mod_cast h_c_int]
        exact mul_nonneg (by exact_mod_cast h_ceil_nn) h_2e_pos.le
      have hz_nn : 0 ≤ (z : ℝ) := by
        by_contra hz_neg
        push Not at hz_neg
        have : (z : ℝ) * x < 0 := mul_neg_of_neg_of_pos hz_neg hx_pos
        linarith
      have hx_le_z : x ≤ (z : ℝ) := by
        have h1 : |x| = x := abs_of_nonneg hx_nn
        have h2 : |(z : ℝ)| = z := abs_of_nonneg hz_nn
        linarith [hz_abs_ge, h1, h2]
      rw [abs_of_nonneg hy_nn, abs_of_nonneg hz_nn]
      rw [show (c : ℝ) = (⌈x * (2 : ℝ) ^ (-e)⌉ : ℝ) from by exact_mod_cast h_c_int]
      exact ceil_minimality F x hz_prec hz_quant hx_le_z
    · -- x < 0: y = ⌊⌋ · 2^e ≤ 0, |x| ≤ |z| ⟹ z ≤ x; apply `floor_minimality`.
      push Not at hx_nn
      have h_c_int : c = ⌊x * (2 : ℝ) ^ (-e)⌋ := by
        rw [h_c_eq]; simp [if_neg (not_le.mpr hx_nn)]
      have h_s_neg : x * (2 : ℝ) ^ (-e) < 0 :=
        mul_neg_of_neg_of_pos hx_nn (zpow_pos (by norm_num) _)
      have h_floor_neg : ⌊x * (2 : ℝ) ^ (-e)⌋ < 0 :=
        Int.floor_lt.mpr (by push_cast; exact h_s_neg)
      have hy_np : (c : ℝ) * (2 : ℝ) ^ e ≤ 0 := by
        rw [show (c : ℝ) = (⌊x * (2 : ℝ) ^ (-e)⌋ : ℝ) from by exact_mod_cast h_c_int]
        exact mul_nonpos_iff.mpr (Or.inr ⟨by exact_mod_cast h_floor_neg.le, h_2e_pos.le⟩)
      have hz_np : (z : ℝ) ≤ 0 := by
        by_contra hz_pos
        push Not at hz_pos
        have : (z : ℝ) * x < 0 := mul_neg_of_pos_of_neg hz_pos hx_nn
        linarith
      have hz_le_x : (z : ℝ) ≤ x := by
        have h1 : |x| = -x := abs_of_neg hx_nn
        have h2 : |(z : ℝ)| = -z := abs_of_nonpos hz_np
        linarith [hz_abs_ge, h1, h2]
      rw [abs_of_nonpos hy_np, abs_of_nonpos hz_np]
      rw [show (c : ℝ) = (⌊x * (2 : ℝ) ^ (-e)⌋ : ℝ) from by exact_mod_cast h_c_int]
      have := floor_minimality F x hz_prec hz_quant hz_le_x
      linarith

/-- `Dyadic.ofIntZpow k e` is in `F.unbounded` provided `e ≥ F.exp` and (when
`F.p` is finite) `|k| ≤ 2^p`. The mantissa-bound boundary case `|k| = 2^p`
is handled by `precisionAtMost_of_abs_le`. -/
theorem rndUnbounded_satisfies_toOdd (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .toOdd) :
    RoundsFinite F.unbounded .toOdd x (rndUnbounded F .toOdd x h) := by
  have h_unb : ¬ F.unbounded.IsUndefined .toOdd := h
  set F'' := F.toParityFormatOfToOdd h with hF''_def
  set F' := F.unbounded.toParityFormatOfToOdd h_unb with hF'_def
  have h_F'_eq : F'.toFormat = F.unbounded.toFormat := rfl
  -- IsOdd-bridge: same predicate value for F and F.unbounded
  -- since both ParityFormats share `p` and `exp` definitionally.
  have h_isOdd_bridge : ∀ (y : Dyadic), F''.IsOdd y ↔ F'.IsOdd y := fun y => Iff.rfl
  have h_rnd_eq : rndUnbounded F .toOdd x h =
      rndParity F'' .toOdd x (F.canonicalExp x) := by
    unfold rndUnbounded
    rw [dif_pos rfl]
  rw [h_rnd_eq]
  set e := F.canonicalExp x with h_e_def
  set s := x * (2 : ℝ) ^ (-e)
  set lo : ℤ := ⌊s⌋ with h_lo_def
  set dlo : Dyadic := Dyadic.ofIntZpow lo e with h_dlo_def
  set dhi : Dyadic := Dyadic.ofIntZpow (lo + 1) e with h_dhi_def
  have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  -- Mantissa bounds for dlo, dhi membership.
  have h_lo_bound : ∀ {p : ℕ+}, F.p = ((p : ℕ+) : WithTop ℕ+) →
      |lo| ≤ (2 : ℤ) ^ (p : ℕ) := fun hp => by
    apply abs_floor_le_of_abs_lt
    push_cast; exact floor_mantissa_lt hp
  have h_lop1_bound : ∀ {p : ℕ+}, F.p = ((p : ℕ+) : WithTop ℕ+) →
      |lo + 1| ≤ (2 : ℤ) ^ (p : ℕ) := fun hp =>
    abs_floor_add_one_le_of_abs_lt (floor_mantissa_lt hp)
  have h_exp_le : ∀ {e' : ℤ}, F.exp = (e' : WithBot ℤ) → e' ≤ e :=
    fun hexp => F.exp_le_canonicalExp x hexp
  have h_dlo_mem : dlo ∈ F.unbounded :=
    ofIntZpow_mem_unbounded F h_exp_le h_lo_bound
  have h_dhi_mem : dhi ∈ F.unbounded :=
    ofIntZpow_mem_unbounded F h_exp_le h_lop1_bound
  have h_dlo_real : (dlo : ℝ) = (lo : ℝ) * (2 : ℝ) ^ e :=
    Dyadic.coe_ofIntZpow _ _
  have h_dhi_real : (dhi : ℝ) = ((lo + 1 : ℤ) : ℝ) * (2 : ℝ) ^ e :=
    Dyadic.coe_ofIntZpow _ _
  have h_floor_le_s : (lo : ℝ) ≤ s := Int.floor_le _
  have h_s_lt_succ : s < (lo : ℝ) + 1 := Int.lt_floor_add_one _
  have h_s_unscale : s * (2 : ℝ) ^ e = x := mul_zpow_neg_self x e
  have h_dlo_le_x : (dlo : ℝ) ≤ x := by
    rw [h_dlo_real, ← h_s_unscale]
    exact mul_le_mul_of_nonneg_right h_floor_le_s h_2e_pos.le
  have h_x_le_dhi : x ≤ (dhi : ℝ) := by
    rw [h_dhi_real, ← h_s_unscale]
    apply mul_le_mul_of_nonneg_right _ h_2e_pos.le
    push_cast; linarith
  -- Faithfulness witnesses.
  have h_dlo_round_down : ∀ z : Dyadic, z ∈ F.unbounded → (z : ℝ) ≤ x →
      (z : ℝ) ≤ (dlo : ℝ) := by
    intro z hz hz_le_x
    obtain ⟨hz_prec, hz_quant, _⟩ := hz
    rw [h_dlo_real]
    exact floor_minimality F x hz_prec hz_quant hz_le_x
  have h_dhi_round_up : (lo : ℝ) ≠ s →
      ∀ z : Dyadic, z ∈ F.unbounded → x ≤ (z : ℝ) → (dhi : ℝ) ≤ (z : ℝ) := by
    intro hs_ne z hz hx_le_z
    obtain ⟨hz_prec, hz_quant, _⟩ := hz
    rw [h_dhi_real]
    have h_ceil_eq : (⌈s⌉ : ℤ) = lo + 1 := by
      have h_lo_lt_s : (lo : ℝ) < s := lt_of_le_of_ne h_floor_le_s hs_ne
      have h_ceil_le : ⌈s⌉ ≤ lo + 1 :=
        Int.ceil_le.mpr (by push_cast; linarith)
      have h_ceil_ge : lo + 1 ≤ ⌈s⌉ := by
        have h_lt_ceil : (lo : ℝ) < (⌈s⌉ : ℝ) :=
          lt_of_lt_of_le h_lo_lt_s (Int.le_ceil _)
        have : lo < ⌈s⌉ := by exact_mod_cast h_lt_ceil
        omega
      omega
    have hh := ceil_minimality F x hz_prec hz_quant hx_le_z
    have h_subst : ((lo + 1 : ℤ) : ℝ) = ((⌈s⌉ : ℤ) : ℝ) := by exact_mod_cast h_ceil_eq.symm
    rw [h_subst]
    convert hh using 2
  -- Main case analysis. Goal: RoundsFinite ... (if ... then ... else ...).
  by_cases hs : (lo : ℝ) = s
  · -- Exact: y = dlo, x = dlo. Parity vacuous.
    rw [show rndParity F'' .toOdd x e =
        if (lo : ℝ) = s then dlo else if F''.IsOdd dlo then dlo else dhi from rfl,
        if_pos hs]
    refine ⟨h_dlo_mem, ?_, ?_⟩
    · left; exact ⟨h_dlo_mem, h_dlo_le_x, h_dlo_round_down⟩
    · intro hne
      exfalso
      apply hne
      rw [h_dlo_real]
      -- x = lo · 2^e: from (lo : ℝ) = s = x · 2^(-e).
      have h_x_eq : x = s * (2 : ℝ) ^ e := by
        change x = x * (2 : ℝ) ^ (-e) * (2 : ℝ) ^ e
        rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
            neg_add_cancel, zpow_zero, mul_one]
      rw [h_x_eq, ← hs]
  · by_cases hodd : F''.IsOdd dlo
    · -- y = dlo, IsOdd dlo holds.
      rw [show rndParity F'' .toOdd x e =
          if (lo : ℝ) = s then dlo else if F''.IsOdd dlo then dlo else dhi from rfl,
          if_neg hs, if_pos hodd]
      refine ⟨h_dlo_mem, ?_, ?_⟩
      · left; exact ⟨h_dlo_mem, h_dlo_le_x, h_dlo_round_down⟩
      · intro _
        exact ⟨F', h_F'_eq, (h_isOdd_bridge dlo).mp hodd⟩
    · -- y = dhi, need IsOdd dhi (alternating parity).
      rw [show rndParity F'' .toOdd x e =
          if (lo : ℝ) = s then dlo else if F''.IsOdd dlo then dlo else dhi from rfl,
          if_neg hs, if_neg hodd]
      refine ⟨h_dhi_mem, ?_, ?_⟩
      · right; exact ⟨h_dhi_mem, h_x_le_dhi, h_dhi_round_up hs⟩
      · intro _
        refine ⟨F', h_F'_eq, ?_⟩
        rw [← h_isOdd_bridge dhi]
        have hx : x ≠ 0 := by
          intro h_x0
          apply hs
          subst h_x0
          have hs0 : s = 0 := by change (0 : ℝ) * (2 : ℝ) ^ (-e) = 0; ring
          rw [hs0]
          simp [h_lo_def, hs0]
        cases hp_F : F.p with
        | top =>
          cases hexp_F : F.exp with
          | bot =>
            exfalso
            rcases F.finite with hf | hf
            · exact hf hp_F
            · exact hf hexp_F
          | coe e' =>
            -- F.p = ⊤, F.exp = (e' : ℤ). canonicalExp x = e'.
            have h_e_eq : e = e' := by
              change F.canonicalExp x = _
              unfold FiniteFormat.canonicalExp
              simp [hp_F, hexp_F]
            -- Apply alternating_parity_fixedpoint to F''. Then transfer to F'.
            have h_dlo_def_e' : dlo = Dyadic.ofIntZpow lo e' := by
              rw [h_dlo_def, h_e_eq]
            have h_dhi_def_e' : dhi = Dyadic.ofIntZpow (lo + 1) e' := by
              rw [h_dhi_def, h_e_eq]
            rw [h_dhi_def_e']
            have h_F''_top : F''.toFormat.p = ⊤ := hp_F
            have h_F''_exp : F''.toFormat.exp = (e' : WithBot ℤ) := hexp_F
            have h_F''_odd_dhi : F''.IsOdd (Dyadic.ofIntZpow (lo + 1) e') := by
              apply ParityFormat.alternating_parity_fixedpoint h_F''_top h_F''_exp
              rw [← h_dlo_def_e']; exact hodd
            -- Bridge to F'.
            -- Bridge F'' to F'. Both ParityFormats have toFormat with
            -- same (p, exp) — F.unbounded inherits these from F.
            exact (show F''.IsOdd (Dyadic.ofIntZpow (lo + 1) e') =
              F'.IsOdd (Dyadic.ofIntZpow (lo + 1) e') from rfl).mp h_F''_odd_dhi
        | coe p =>
          cases hexp_F : F.exp with
          | bot =>
            have hp_eq : F''.toFormat.p = ((p : ℕ+) : WithTop ℕ+) := hp_F
            have hexp_eq : F''.toFormat.exp = ⊥ := hexp_F
            have hp_ne_1 : F''.toFormat.p ≠ ((1 : ℕ+) : WithTop ℕ+) := by
              change F.p ≠ ((1 : ℕ+) : WithTop ℕ+)
              intro h_eq
              apply h
              exact ⟨h_eq, hexp_F, Or.inl rfl⟩
            have h_e_eq_log : e = Int.log 2 |x| + 1 - (p : ℤ) := by
              change F.canonicalExp x = _
              unfold FiniteFormat.canonicalExp
              simp [hp_F, hexp_F, hx]
            have h_s_lo_real : ((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) ≤ |s| :=
              two_pow_pred_le_scaled (p := p) hx h_e_eq_log
            -- |lo| ≥ 2^(p-1).
            have h_lo_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo| :=
              abs_floor_ge_two_pow_pred (p := p) h_s_lo_real
            -- |lo + 1| ≥ 2^(p-1) (non-exact case).
            have h_lop1_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo + 1| := by
              by_cases hs_nn : 0 ≤ s
              · have h_lo_nn : 0 ≤ lo := Int.floor_nonneg.mpr hs_nn
                rw [abs_of_nonneg (by linarith : (0 : ℤ) ≤ lo + 1)]
                linarith [h_lo_lo, abs_of_nonneg h_lo_nn]
              · have hs_neg : s < 0 := not_le.mp hs_nn
                have h_lo_le_r : (lo : ℝ) ≤ -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) := by
                  have h_s_le_r : s ≤ -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) := by
                    have h_abs_eq : |s| = -s := abs_of_neg hs_neg
                    linarith [h_s_lo_real]
                  have h_floor_le : (lo : ℝ) ≤ s := Int.floor_le _
                  linarith
                have h_lo_le : lo ≤ -((2 : ℤ) ^ ((p : ℕ) - 1)) := by
                  exact_mod_cast h_lo_le_r
                have h_lo_ne : lo ≠ -((2 : ℤ) ^ ((p : ℕ) - 1)) := by
                  intro h_lo_eq
                  apply hs
                  have h_floor_le : (lo : ℝ) ≤ s := Int.floor_le _
                  have h_s_le_lo : s ≤ -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) := by
                    have h_abs_eq : |s| = -s := abs_of_neg hs_neg
                    linarith [h_s_lo_real]
                  have h_lo_r : (lo : ℝ) = -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) := by
                    exact_mod_cast h_lo_eq
                  linarith
                have h_lo_lt : lo < -((2 : ℤ) ^ ((p : ℕ) - 1)) :=
                  lt_of_le_of_ne h_lo_le h_lo_ne
                have h_lop1_le : lo + 1 ≤ -((2 : ℤ) ^ ((p : ℕ) - 1)) := by linarith
                have hp_ge_2 : 2 ≤ (p : ℕ) := by
                  by_contra h_neg
                  push Not at h_neg
                  have hp_pos : 1 ≤ (p : ℕ) := p.pos
                  have hp_one : (p : ℕ) = 1 := by omega
                  have hp_subt : p = 1 := Subtype.ext hp_one
                  apply hp_ne_1
                  change F.p = _
                  rw [hp_F, hp_subt]
                have h_2p1_ge_2 : 2 ≤ (2 : ℤ) ^ ((p : ℕ) - 1) := by
                  calc (2 : ℤ) = (2 : ℤ) ^ 1 := by ring
                    _ ≤ (2 : ℤ) ^ ((p : ℕ) - 1) :=
                        pow_le_pow_right₀ (by norm_num) (by omega)
                have h_lop1_neg : lo + 1 < 0 := by linarith
                rw [abs_of_neg h_lop1_neg]; linarith
            exact ParityFormat.alternating_parity_floating hp_eq hp_ne_1 hexp_eq
              h_lo_lo (h_lo_bound hp_F) h_lop1_lo (h_lop1_bound hp_F) hodd
          | coe e' =>
            -- F.p = (p:ℕ+), F.exp = (e':ℤ). Mixed case.
            by_cases hp_eq_1 : p = (1 : ℕ+)
            · -- p = 1: exponent-index parity branch.
              subst hp_eq_1
              have hp_eq : F''.toFormat.p = ((1 : ℕ+) : WithTop ℕ+) := hp_F
              have hexp_eq : F''.toFormat.exp = (e' : WithBot ℤ) := hexp_F
              have h_e_ge : e' ≤ e := F.exp_le_canonicalExp x hexp_F
              have h_s_lt : |x * (2 : ℝ) ^ (-e)| < (2 : ℝ) ^ ((1 : ℕ+) : ℕ) :=
                floor_mantissa_lt hp_F
              have h_s_lt_2 : |x * (2 : ℝ) ^ (-e)| < ((2 : ℤ) : ℝ) := by
                have h_cast : ((2 : ℤ) : ℝ) = (2 : ℝ) ^ ((1 : ℕ+) : ℕ) := by
                  change (2 : ℝ) = (2 : ℝ) ^ (1 : ℕ); ring
                rw [h_cast]; exact h_s_lt
              have h_lo_hi_int : |lo| ≤ 2 := abs_floor_le_of_abs_lt h_s_lt_2
              have h_lop1_hi_int : |lo + 1| ≤ 2 := by
                have := abs_floor_add_one_le_of_abs_lt (p := 1) h_s_lt
                exact this
              -- Show dlo, dhi at canonical e.
              have h_dlo_at : dlo = Dyadic.ofIntZpow lo e := h_dlo_def
              have h_dhi_at : dhi = Dyadic.ofIntZpow (lo + 1) e := h_dhi_def
              by_cases h_regime : Int.log 2 |x| + 1 - ((1 : ℕ+) : ℤ) ≤ e'
              · -- Subnormal: e = e'.
                have h_e_eq : e = e' := by
                  change F.canonicalExp x = e'
                  unfold FiniteFormat.canonicalExp
                  simp only [hp_F, hexp_F]
                  rw [if_neg hx]
                  exact max_eq_right h_regime
                rw [h_dlo_at, h_e_eq] at hodd
                rw [h_dhi_at, h_e_eq]
                exact ParityFormat.alternating_parity_mixed_subnormal_p1
                  hp_eq hexp_eq h_lo_hi_int h_lop1_hi_int hodd
              · -- Normal: e = log|x|+1-1 = log|x|. Need |lo|, |lo+1| ≥ 1.
                push Not at h_regime
                have h_pcast : ((1 : ℕ+) : ℤ) = 1 := rfl
                have h_e_eq_log : e = Int.log 2 |x| := by
                  change F.canonicalExp x = _
                  unfold FiniteFormat.canonicalExp
                  simp only [hp_F, hexp_F]
                  rw [if_neg hx]
                  rw [show (((1 : ℕ+) : ℕ) : ℤ) = 1 from rfl]
                  have h_max_eq : max (Int.log 2 |x| + 1 - 1) e' =
                      Int.log 2 |x| + 1 - 1 := by
                    apply max_eq_left
                    have := h_regime; rw [h_pcast] at this; linarith
                  rw [h_max_eq]; ring
                -- |s| ≥ 1 from |x| ≥ 2^(log|x|) = 2^e.
                have h_x_ge : (2 : ℝ) ^ (Int.log 2 |x|) ≤ |x| :=
                  Int.zpow_log_le_self (b := 2) (by norm_num : (1 : ℕ) < 2)
                    (abs_pos.mpr hx)
                have h_2neg_pos : (0 : ℝ) < (2 : ℝ) ^ (-e) :=
                  zpow_pos (by norm_num) _
                have h_abs_s : 1 ≤ |x * (2 : ℝ) ^ (-e)| := by
                  have h_abs_eq : |x * (2 : ℝ) ^ (-e)| = |x| * (2 : ℝ) ^ (-e) := by
                    rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)]
                  rw [h_abs_eq, h_e_eq_log]
                  have h_pow_eq : (2 : ℝ) ^ (Int.log 2 |x|) *
                      (2 : ℝ) ^ (-Int.log 2 |x|) = 1 := by
                    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
                        add_neg_cancel, zpow_zero]
                  have h_le := mul_le_mul_of_nonneg_right h_x_ge
                    (zpow_pos (by norm_num : (0 : ℝ) < 2) (-Int.log 2 |x|)).le
                  rw [h_pow_eq] at h_le
                  exact h_le
                -- |lo| ≥ 1.
                have h_lo_lo_int : 1 ≤ |lo| := by
                  by_cases hs_nn : 0 ≤ x * (2 : ℝ) ^ (-e)
                  · have h_s_ge : 1 ≤ x * (2 : ℝ) ^ (-e) := by
                      have h_abs_eq : |x * (2 : ℝ) ^ (-e)| = x * (2 : ℝ) ^ (-e) :=
                        abs_of_nonneg hs_nn
                      linarith [h_abs_s]
                    have h_lo_ge_1 : 1 ≤ lo := by
                      apply Int.le_floor.mpr
                      push_cast; exact h_s_ge
                    have h_lo_nn : 0 ≤ lo := by linarith
                    rw [abs_of_nonneg h_lo_nn]; exact h_lo_ge_1
                  · push Not at hs_nn
                    have h_s_le : x * (2 : ℝ) ^ (-e) ≤ -1 := by
                      have h_abs_eq : |x * (2 : ℝ) ^ (-e)| =
                          -(x * (2 : ℝ) ^ (-e)) := abs_of_neg hs_nn
                      linarith [h_abs_s]
                    have h_floor_le : (lo : ℝ) ≤ x * (2 : ℝ) ^ (-e) :=
                      Int.floor_le _
                    have h_lo_le : (lo : ℝ) ≤ -1 := le_trans h_floor_le h_s_le
                    have h_lo_le_int : lo ≤ -1 := by exact_mod_cast h_lo_le
                    have h_lo_neg : lo < 0 := by linarith
                    rw [abs_of_neg h_lo_neg]; linarith
                -- |lo+1| ≥ 1: lo ≠ -1.
                -- lo = -1 ⟹ s = -1 (boundary) since lo = ⌊s⌋ and |s| ≥ 1 in normal.
                --   x · 2^(-e) = -1, so x = -2^e = -2^(log|x|). Then dlo = x.
                --   Contradicts hs.
                have h_lo_ne_neg1 : lo ≠ -1 := by
                  intro h_eq
                  have h_lo_int : ⌊s⌋ = -1 := h_eq
                  have h_floor_le : (-1 : ℝ) ≤ s := by
                    have h_fl := Int.floor_le s
                    rw [h_lo_int] at h_fl; push_cast at h_fl; exact h_fl
                  have h_lt_succ : s < 0 := by
                    have h_lt := Int.lt_floor_add_one s
                    rw [h_lo_int] at h_lt; push_cast at h_lt; linarith
                  have h_s_le_neg1 : s ≤ -1 := by
                    have h_abs_eq : |s| = -s := abs_of_neg (by linarith : s < 0)
                    have h_abs_ge : 1 ≤ |s| := h_abs_s
                    linarith
                  have h_s_eq : s = -1 := le_antisymm h_s_le_neg1 h_floor_le
                  apply hs
                  rw [h_s_eq]
                  show (lo : ℝ) = -1
                  rw [h_eq]; push_cast; ring
                -- |lo+1| ≥ 1: from lo ∈ {-1 excluded, other values}.
                have h_lop1_lo_int : 1 ≤ |lo + 1| := by
                  have h_lop1_ne : lo + 1 ≠ 0 := by
                    intro h0; apply h_lo_ne_neg1; omega
                  exact Int.one_le_abs h_lop1_ne
                rw [h_dlo_at] at hodd
                rw [h_dhi_at]
                exact ParityFormat.alternating_parity_mixed_normal_p1
                  hp_eq hexp_eq h_e_ge h_lo_lo_int h_lo_hi_int
                  h_lop1_lo_int h_lop1_hi_int hodd
            · -- p ≠ 1.
              have hp_eq : F''.toFormat.p = ((p : ℕ+) : WithTop ℕ+) := hp_F
              have hexp_eq : F''.toFormat.exp = (e' : WithBot ℤ) := hexp_F
              have hp_ne_1 : F''.toFormat.p ≠ ((1 : ℕ+) : WithTop ℕ+) := by
                change F.p ≠ _
                rw [hp_F]
                intro h
                apply hp_eq_1
                exact_mod_cast h
              by_cases h_regime : Int.log 2 |x| + 1 - ((p : ℕ+) : ℤ) ≤ e'
              · -- Subnormal regime: e = e'.
                have h_e_eq : e = e' := by
                  change F.canonicalExp x = e'
                  unfold FiniteFormat.canonicalExp
                  simp only [hp_F, hexp_F]
                  rw [if_neg hx]
                  exact max_eq_right h_regime
                -- |x| < 2^(e' + p) from h_regime.
                have h_x_lt : |x| < (2 : ℝ) ^ (e' + (p : ℤ)) := by
                  have h_log_le : Int.log 2 |x| ≤ e' + (p : ℤ) - 1 := by
                    have : Int.log 2 |x| + 1 - ((p : ℕ+) : ℤ) ≤ e' := h_regime
                    have h_pcast : ((p : ℕ+) : ℤ) = (p : ℤ) := rfl
                    linarith
                  have h_lt := Int.lt_zpow_succ_log_self
                    (by norm_num : (1 : ℕ) < 2) |x|
                  have : Int.log 2 |x| + 1 ≤ e' + (p : ℤ) := by linarith
                  exact lt_of_lt_of_le h_lt
                    (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) this)
                -- |s| = |x| * 2^(-e') < 2^p strict.
                have h_s_lt : |x * (2 : ℝ) ^ (-e)| < (2 : ℝ) ^ ((p : ℕ+) : ℕ) := by
                  rw [h_e_eq]
                  have h_abs : |x * (2 : ℝ) ^ (-e')| = |x| * (2 : ℝ) ^ (-e') := by
                    rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)]
                  rw [h_abs]
                  have h_2neg_pos : (0 : ℝ) < (2 : ℝ) ^ (-e') := zpow_pos (by norm_num) _
                  have h_eq_split : (2 : ℝ) ^ (e' + (p : ℤ)) =
                      (2 : ℝ) ^ e' * (2 : ℝ) ^ ((p : ℕ+) : ℕ) := by
                    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
                    have h_pcast : ((p : ℕ+) : ℤ) = (((p : ℕ+) : ℕ) : ℤ) := rfl
                    rw [h_pcast, zpow_natCast]
                  have h_x2neg : |x| * (2 : ℝ) ^ (-e') <
                      (2 : ℝ) ^ (e' + (p : ℤ)) * (2 : ℝ) ^ (-e') :=
                    mul_lt_mul_of_pos_right h_x_lt h_2neg_pos
                  rw [h_eq_split] at h_x2neg
                  have h_cancel : (2 : ℝ) ^ e' * (2 : ℝ) ^ ((p : ℕ+) : ℕ) *
                      (2 : ℝ) ^ (-e') = (2 : ℝ) ^ ((p : ℕ+) : ℕ) := by
                    rw [mul_right_comm, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
                        add_neg_cancel, zpow_zero, one_mul]
                  rw [h_cancel] at h_x2neg
                  exact h_x2neg
                -- |lo| ≤ 2^p, |lo+1| ≤ 2^p.
                have h_lo_le : |lo| ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by
                  apply abs_floor_le_of_abs_lt
                  push_cast; exact h_s_lt
                have h_lop1_le : |lo + 1| ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) :=
                  abs_floor_add_one_le_of_abs_lt h_s_lt
                    -- Case split: |lo| < 2^p (non-saturation) or |lo| = 2^p.
                rcases lt_or_eq_of_le h_lo_le with h_lo_lt | h_lo_sat
                · -- Non-saturation: also |lo+1| ≤ 2^p but may saturate.
                  rcases lt_or_eq_of_le h_lop1_le with h_lop1_lt | h_lop1_sat
                  · -- Both strict. Apply lemma.
                    have h_log_lo' := log_lt_p_of_abs_lt_two_pow h_lo_lt
                    have h_log_lop1_raw := log_lt_p_of_abs_lt_two_pow h_lop1_lt
                    -- Bridge for lo+1: lemma's `|lo + 1| : ℝ` elaborates as
                    -- `|↑lo + 1|`, but helper gives `|↑(lo + 1)|`.
                    have h_log_lop1' : Int.log 2 |((lo : ℝ) + 1)| + 1 ≤
                        (((p : ℕ+) : ℕ) : ℤ) := by
                      have h_eq : |((lo : ℝ) + 1)| = |((lo + 1 : ℤ) : ℝ)| := by
                        push_cast; rfl
                      rw [h_eq]; exact h_log_lop1_raw
                    have h_dlo_at_e' : dlo = Dyadic.ofIntZpow lo e' := by
                      rw [h_dlo_def, h_e_eq]
                    have h_dhi_at_e' : dhi = Dyadic.ofIntZpow (lo + 1) e' := by
                      rw [h_dhi_def, h_e_eq]
                    rw [h_dhi_at_e']
                    apply ParityFormat.alternating_parity_mixed_subnormal_pne1
                      hp_eq hp_ne_1 hexp_eq h_log_lo' h_log_lop1'
                    rw [← h_dlo_at_e']; exact hodd
                  · -- |lo+1| = 2^p saturation. Must be lo+1 = 2^p (positive
                    -- sat); lo+1 = -2^p would force |lo| = 2^p+1 > 2^p.
                    exfalso
                    have h2p_nn : (0 : ℤ) ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by positivity
                    have h_pos_lop1 : lo + 1 = (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by
                      rcases (abs_eq h2p_nn).mp h_lop1_sat with h | h
                      · exact h
                      · -- lo + 1 = -2^p ⟹ lo = -2^p - 1 ⟹ |lo| ≥ 2^p + 1.
                        exfalso
                        have h_lo_eq : lo = -((2 : ℤ) ^ ((p : ℕ+) : ℕ)) - 1 := by omega
                        have h_abs_lo : |lo| = (2 : ℤ) ^ ((p : ℕ+) : ℕ) + 1 := by
                          rw [h_lo_eq]
                          rw [show -((2 : ℤ) ^ ((p : ℕ+) : ℕ)) - 1 =
                              -((2 : ℤ) ^ ((p : ℕ+) : ℕ) + 1) by ring]
                          rw [abs_neg]
                          exact abs_of_nonneg (by linarith)
                        linarith [h_lo_lt, h_abs_lo]
                    -- lo = 2^p - 1, dlo = (2^p - 1) · 2^e' is Odd.
                    have h_lo_eq : lo = (2 : ℤ) ^ ((p : ℕ+) : ℕ) - 1 := by omega
                    -- Show F''.IsOdd dlo via mixed_subnormal characterization.
                    -- |lo| = 2^p - 1 < 2^p (since 2^p > 0).
                    have h_lo_pos : (0 : ℤ) < (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by positivity
                    have h_abs_lo_eq : |lo| = (2 : ℤ) ^ ((p : ℕ+) : ℕ) - 1 := by
                      rw [h_lo_eq]; exact abs_of_nonneg (by linarith)
                    have h_lo_ne : lo ≠ 0 := by
                      rw [h_lo_eq]
                      have : (2 : ℤ) ^ ((p : ℕ+) : ℕ) > 1 := by
                        calc (2 : ℤ) ^ ((p : ℕ+) : ℕ) ≥ 2 := by
                              calc (2 : ℤ) ^ ((p : ℕ+) : ℕ) ≥ (2 : ℤ) ^ 1 :=
                                  pow_le_pow_right₀ (by norm_num) (p : ℕ+).pos
                                _ = 2 := by ring
                          _ > 1 := by norm_num
                      omega
                    have h_log_lo' := log_lt_p_of_abs_lt_two_pow
                      (k := lo) (by rw [h_abs_lo_eq]; linarith)
                    have h_dlo_at_e' : dlo = Dyadic.ofIntZpow lo e' := by
                      rw [h_dlo_def, h_e_eq]
                    apply hodd
                    rw [h_dlo_at_e']
                    rw [ParityFormat.isOdd_iff_odd_at_canonical_mixed_subnormal
                        hp_eq hp_ne_1 hexp_eq h_lo_ne h_log_lo']
                    -- Show Odd lo = Odd (2^p - 1).
                    rw [h_lo_eq]
                    have h2p_even : Even ((2 : ℤ) ^ ((p : ℕ+) : ℕ)) := by
                      refine ⟨(2 : ℤ) ^ (((p : ℕ+) : ℕ) - 1), ?_⟩
                      have := Dyadic.two_pow_succ_pred (p : ℕ+).pos
                      linarith
                    have h_neg_odd : Odd ((2 : ℤ) ^ ((p : ℕ+) : ℕ) - 1) := by
                      rcases h2p_even with ⟨m, hm⟩
                      refine ⟨m - 1, ?_⟩
                      linarith
                    exact h_neg_odd
                · -- |lo| = 2^p saturation. Must be lo = -2^p (since lo ≤ s < 2^p).
                  have h2p_nn : (0 : ℤ) ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by positivity
                  have h2p_pos : (0 : ℤ) < (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by positivity
                  -- lo ≤ s < 2^p (real), so lo < 2^p as integers.
                  have h_lo_lt_2p : lo < (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by
                    have h_floor_le : (lo : ℝ) ≤ s := Int.floor_le _
                    have h_s_lt' : s < (2 : ℝ) ^ ((p : ℕ+) : ℕ) := by
                      have := h_s_lt; rw [abs_lt] at this; exact this.2
                    have h_cast : ((2 : ℤ) ^ ((p : ℕ+) : ℕ) : ℝ) =
                        (2 : ℝ) ^ ((p : ℕ+) : ℕ) := by push_cast; rfl
                    have h_lo_lt_r : (lo : ℝ) < ((2 : ℤ) ^ ((p : ℕ+) : ℕ) : ℝ) := by
                      rw [h_cast]; linarith
                    exact_mod_cast h_lo_lt_r
                  have h_lo_neg : lo = -((2 : ℤ) ^ ((p : ℕ+) : ℕ)) := by
                    rcases (abs_eq h2p_nn).mp h_lo_sat with h | h
                    · omega
                    · exact h
                  -- lo + 1 = -2^p + 1, |lo+1| = 2^p - 1 < 2^p.
                  have h_lop1_ne : lo + 1 ≠ 0 := by
                    rw [h_lo_neg]
                    have h_2_le : 2 ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by
                      calc (2 : ℤ) = (2 : ℤ) ^ 1 := by ring
                        _ ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) :=
                            pow_le_pow_right₀ (by norm_num) (p : ℕ+).pos
                    omega
                  have h_abs_lop1 : |lo + 1| = (2 : ℤ) ^ ((p : ℕ+) : ℕ) - 1 := by
                    rw [h_lo_neg]
                    rw [show -((2 : ℤ) ^ ((p : ℕ+) : ℕ)) + 1 =
                          -((2 : ℤ) ^ ((p : ℕ+) : ℕ) - 1) by ring]
                    rw [abs_neg]
                    have h_pos : 0 ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) - 1 := by
                      have : (1 : ℤ) ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) := one_le_pow₀ (by norm_num)
                      linarith
                    exact abs_of_nonneg h_pos
                  have h_log_lop1' := log_lt_p_of_abs_lt_two_pow
                    (k := lo + 1) (by rw [h_abs_lop1]; linarith)
                  have h_dhi_at_e' : dhi = Dyadic.ofIntZpow (lo + 1) e' := by
                    rw [h_dhi_def, h_e_eq]
                  rw [h_dhi_at_e']
                  rw [ParityFormat.isOdd_iff_odd_at_canonical_mixed_subnormal
                      hp_eq hp_ne_1 hexp_eq h_lop1_ne h_log_lop1']
                  -- Show Odd (lo + 1) = Odd (-2^p + 1).
                  rw [h_lo_neg]
                  have h2p_even : Even ((2 : ℤ) ^ ((p : ℕ+) : ℕ)) := by
                    refine ⟨(2 : ℤ) ^ (((p : ℕ+) : ℕ) - 1), ?_⟩
                    have := Dyadic.two_pow_succ_pred (p : ℕ+).pos
                    linarith
                  have h_neg_2p_even : Even (-((2 : ℤ) ^ ((p : ℕ+) : ℕ))) := h2p_even.neg
                  exact h_neg_2p_even.add_one
              · -- Normal regime: e = log|x|+1-p.
                push Not at h_regime
                have h_e_eq_log : e = Int.log 2 |x| + 1 - ((p : ℕ+) : ℤ) := by
                  change F.canonicalExp x = _
                  unfold FiniteFormat.canonicalExp
                  simp only [hp_F, hexp_F]
                  rw [if_neg hx]
                  exact max_eq_left (le_of_lt h_regime)
                have h_s_lo_real : ((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) ≤
                    |x * (2 : ℝ) ^ (-e)| :=
                  two_pow_pred_le_scaled (p := p) hx h_e_eq_log
                have h_lo_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo| :=
                  abs_floor_ge_two_pow_pred (p := p) h_s_lo_real
                -- |lo + 1| ≥ 2^(p-1) (non-exact case).
                have h_lop1_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo + 1| := by
                  by_cases hs_nn : 0 ≤ s
                  · have h_lo_nn : 0 ≤ lo := Int.floor_nonneg.mpr hs_nn
                    rw [abs_of_nonneg (by linarith : (0 : ℤ) ≤ lo + 1)]
                    linarith [h_lo_lo, abs_of_nonneg h_lo_nn]
                  · have hs_neg : s < 0 := not_le.mp hs_nn
                    have h_lo_le_r : (lo : ℝ) ≤ -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) := by
                      have h_s_le_r : s ≤ -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) := by
                        have h_abs_eq : |s| = -s := abs_of_neg hs_neg
                        linarith [h_s_lo_real]
                      have h_floor_le : (lo : ℝ) ≤ s := Int.floor_le _
                      linarith
                    have h_lo_le : lo ≤ -((2 : ℤ) ^ ((p : ℕ) - 1)) := by
                      exact_mod_cast h_lo_le_r
                    have h_lo_ne : lo ≠ -((2 : ℤ) ^ ((p : ℕ) - 1)) := by
                      intro h_lo_eq
                      apply hs
                      have h_floor_le : (lo : ℝ) ≤ s := Int.floor_le _
                      have h_s_le_lo : s ≤ -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) := by
                        have h_abs_eq : |s| = -s := abs_of_neg hs_neg
                        linarith [h_s_lo_real]
                      have h_lo_r : (lo : ℝ) = -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) := by
                        exact_mod_cast h_lo_eq
                      linarith
                    have h_lo_lt : lo < -((2 : ℤ) ^ ((p : ℕ) - 1)) :=
                      lt_of_le_of_ne h_lo_le h_lo_ne
                    have h_lop1_le : lo + 1 ≤ -((2 : ℤ) ^ ((p : ℕ) - 1)) := by linarith
                    have hp_ge_2 : 2 ≤ (p : ℕ) := by
                      by_contra h_neg
                      push Not at h_neg
                      have hp_pos : 1 ≤ (p : ℕ) := p.pos
                      have hp_one : (p : ℕ) = 1 := by omega
                      have hp_subt : p = 1 := Subtype.ext hp_one
                      exact hp_eq_1 hp_subt
                    have h_2p1_ge_2 : 2 ≤ (2 : ℤ) ^ ((p : ℕ) - 1) := by
                      calc (2 : ℤ) = (2 : ℤ) ^ 1 := by ring
                        _ ≤ (2 : ℤ) ^ ((p : ℕ) - 1) :=
                            pow_le_pow_right₀ (by norm_num) (by omega)
                    have h_lop1_neg : lo + 1 < 0 := by linarith
                    rw [abs_of_neg h_lop1_neg]; linarith
                -- |lo| ≤ 2^p, |lo+1| ≤ 2^p from h_lo_bound, h_lop1_bound.
                have h_lo_hi : |lo| ≤ (2 : ℤ) ^ ((p : ℕ) : ℕ) := h_lo_bound hp_F
                have h_lop1_hi : |lo + 1| ≤ (2 : ℤ) ^ ((p : ℕ) : ℕ) := h_lop1_bound hp_F
                -- Mixed-normal log bounds: p ≤ Int.log 2 |dlo| - e' + 1.
                -- |dlo| = |lo| · 2^e ≥ 2^(p-1) · 2^e = 2^(p-1+e) = 2^(log|x|).
                have h_lo_ne : lo ≠ 0 := by
                  intro h_lo_zero
                  rw [h_lo_zero] at h_lo_lo
                  simp at h_lo_lo
                  have : (0 : ℤ) < (2 : ℤ) ^ ((p : ℕ) - 1) := by positivity
                  omega
                have h_lop1_ne : lo + 1 ≠ 0 := by
                  intro h_lop1_zero
                  rw [h_lop1_zero] at h_lop1_lo
                  simp at h_lop1_lo
                  have : (0 : ℤ) < (2 : ℤ) ^ ((p : ℕ) - 1) := by positivity
                  omega
                have h_dlo_ne : (dlo : ℝ) ≠ 0 := by
                  rw [h_dlo_real]
                  exact mul_ne_zero (Int.cast_ne_zero.mpr h_lo_ne)
                    (ne_of_gt (zpow_pos (by norm_num) _))
                have h_dhi_ne : (dhi : ℝ) ≠ 0 := by
                  rw [h_dhi_real]
                  exact mul_ne_zero (Int.cast_ne_zero.mpr h_lop1_ne)
                    (ne_of_gt (zpow_pos (by norm_num) _))
                have h_log_dlo : Int.log 2 |(dlo : ℝ)| =
                    Int.log 2 |(lo : ℝ)| + e := by
                  rw [h_dlo_real]
                  exact ParityFormat.log_abs_mul_zpow h_lo_ne e
                have h_log_dhi : Int.log 2 |(dhi : ℝ)| =
                    Int.log 2 |((lo + 1 : ℤ) : ℝ)| + e := by
                  rw [h_dhi_real]
                  exact ParityFormat.log_abs_mul_zpow h_lop1_ne e
                -- Helper: compute Int.log 2 (2^n : ℝ) = n for natural n.
                have h_log_lo_lb := log_ge_p_pred_of_two_pow_pred_le (k := lo) h_lo_lo
                have h_log_lop1_lb := log_ge_p_pred_of_two_pow_pred_le (k := lo + 1) h_lop1_lo
                -- Combine: log|dlo| = log|lo| + e ≥ (p-1) + (log|x|+1-p) = log|x|.
                have h_log_lo : ((p : ℕ) : ℤ) ≤
                    Int.log 2 |(dlo : ℝ)| - e' + 1 := by
                  rw [h_log_dlo, h_e_eq_log]
                  have : Int.log 2 |x| - e' ≥ ((p : ℕ) : ℤ) := by linarith
                  linarith [h_log_lo_lb]
                have h_log_hi : ((p : ℕ) : ℤ) ≤
                    Int.log 2 |(dhi : ℝ)| - e' + 1 := by
                  rw [h_log_dhi, h_e_eq_log]
                  have : Int.log 2 |x| - e' ≥ ((p : ℕ) : ℤ) := by linarith
                  linarith [h_log_lop1_lb]
                -- Apply alternating_parity_mixed_normal_pne1.
                apply ParityFormat.alternating_parity_mixed_normal_pne1
                  hp_eq hp_ne_1 hexp_eq h_dlo_ne h_dhi_ne h_log_lo h_log_hi
                  h_dlo_real h_dhi_real h_lo_lo h_lo_hi h_lop1_lo h_lop1_hi
                exact hodd

theorem rndUnbounded_satisfies_nearest (F : FiniteFormat) (tb : TieBreak) (x : ℝ)
    (h : ¬ F.IsUndefined (.nearest tb)) :
    RoundsFinite F.unbounded (.nearest tb) x (rndUnbounded F (.nearest tb) x h) := by
  -- Setup mirrors `rndUnbounded_satisfies_toOdd`.
  set e := F.canonicalExp x with h_e_def
  set s := x * (2 : ℝ) ^ (-e)
  set lo : ℤ := ⌊s⌋ with h_lo_def
  set dlo : Dyadic := Dyadic.ofIntZpow lo e with h_dlo_def
  set dhi : Dyadic := Dyadic.ofIntZpow (lo + 1) e with h_dhi_def
  have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  -- Mantissa bounds for dlo, dhi membership.
  have h_lo_bound : ∀ {p : ℕ+}, F.p = ((p : ℕ+) : WithTop ℕ+) →
      |lo| ≤ (2 : ℤ) ^ (p : ℕ) := fun hp => by
    apply abs_floor_le_of_abs_lt
    push_cast; exact floor_mantissa_lt hp
  have h_lop1_bound : ∀ {p : ℕ+}, F.p = ((p : ℕ+) : WithTop ℕ+) →
      |lo + 1| ≤ (2 : ℤ) ^ (p : ℕ) := fun hp =>
    abs_floor_add_one_le_of_abs_lt (floor_mantissa_lt hp)
  have h_exp_le : ∀ {e' : ℤ}, F.exp = (e' : WithBot ℤ) → e' ≤ e :=
    fun hexp => F.exp_le_canonicalExp x hexp
  have h_dlo_mem : dlo ∈ F.unbounded :=
    ofIntZpow_mem_unbounded F h_exp_le h_lo_bound
  have h_dhi_mem : dhi ∈ F.unbounded :=
    ofIntZpow_mem_unbounded F h_exp_le h_lop1_bound
  have h_dlo_real : (dlo : ℝ) = (lo : ℝ) * (2 : ℝ) ^ e :=
    Dyadic.coe_ofIntZpow _ _
  have h_dhi_real : (dhi : ℝ) = ((lo + 1 : ℤ) : ℝ) * (2 : ℝ) ^ e :=
    Dyadic.coe_ofIntZpow _ _
  have h_floor_le_s : (lo : ℝ) ≤ s := Int.floor_le _
  have h_s_lt_succ : s < (lo : ℝ) + 1 := Int.lt_floor_add_one _
  have h_s_unscale : s * (2 : ℝ) ^ e = x := mul_zpow_neg_self x e
  have h_dlo_le_x : (dlo : ℝ) ≤ x := by
    rw [h_dlo_real, ← h_s_unscale]
    exact mul_le_mul_of_nonneg_right h_floor_le_s h_2e_pos.le
  have h_x_le_dhi : x ≤ (dhi : ℝ) := by
    rw [h_dhi_real, ← h_s_unscale]
    apply mul_le_mul_of_nonneg_right _ h_2e_pos.le
    push_cast; linarith
  -- Faithfulness witnesses.
  have h_dlo_round_down : ∀ z : Dyadic, z ∈ F.unbounded → (z : ℝ) ≤ x →
      (z : ℝ) ≤ (dlo : ℝ) := by
    intro z hz hz_le_x
    obtain ⟨hz_prec, hz_quant, _⟩ := hz
    rw [h_dlo_real]
    exact floor_minimality F x hz_prec hz_quant hz_le_x
  have h_dhi_round_up : (lo : ℝ) ≠ s →
      ∀ z : Dyadic, z ∈ F.unbounded → x ≤ (z : ℝ) → (dhi : ℝ) ≤ (z : ℝ) := by
    intro hs_ne z hz hx_le_z
    obtain ⟨hz_prec, hz_quant, _⟩ := hz
    rw [h_dhi_real]
    have h_ceil_eq : (⌈s⌉ : ℤ) = lo + 1 := by
      have h_lo_lt_s : (lo : ℝ) < s := lt_of_le_of_ne h_floor_le_s hs_ne
      have h_ceil_le : ⌈s⌉ ≤ lo + 1 :=
        Int.ceil_le.mpr (by push_cast; linarith)
      have h_ceil_ge : lo + 1 ≤ ⌈s⌉ := by
        have h_lt_ceil : (lo : ℝ) < (⌈s⌉ : ℝ) :=
          lt_of_lt_of_le h_lo_lt_s (Int.le_ceil _)
        have : lo < ⌈s⌉ := by exact_mod_cast h_lt_ceil
        omega
      omega
    have hh := ceil_minimality F x hz_prec hz_quant hx_le_z
    have h_subst : ((lo + 1 : ℤ) : ℝ) = ((⌈s⌉ : ℤ) : ℝ) := by exact_mod_cast h_ceil_eq.symm
    rw [h_subst]
    convert hh using 2
  -- Any faithful round of x is dlo or dhi.
  have h_faithful_eq : ∀ y : Dyadic, IsFaithfulRound F.unbounded x y →
      y = dlo ∨ y = dhi := by
    intro y hf
    rcases hf with ⟨hy_mem, hy_le, hy_max⟩ | ⟨hy_mem, hy_ge, hy_min⟩
    · left
      apply Subtype.ext
      exact le_antisymm (h_dlo_round_down y hy_mem hy_le)
        (hy_max dlo h_dlo_mem h_dlo_le_x)
    · by_cases hs_eq : (lo : ℝ) = s
      · -- Exact: x = dlo. y ≥ x = dlo and y ≤ dlo (via hy_min applied to dlo).
        left; apply Subtype.ext
        have hx_eq_dlo : x = (dlo : ℝ) := by
          rw [h_dlo_real]
          have h_x_eq : x = s * (2 : ℝ) ^ e := by
            change x = x * (2 : ℝ) ^ (-e) * (2 : ℝ) ^ e
            rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
                neg_add_cancel, zpow_zero, mul_one]
          rw [h_x_eq, ← hs_eq]
        have h_y_le_dlo : (y : ℝ) ≤ (dlo : ℝ) :=
          hy_min dlo h_dlo_mem (le_of_eq hx_eq_dlo)
        have h_y_ge_dlo : (dlo : ℝ) ≤ (y : ℝ) := hx_eq_dlo ▸ hy_ge
        exact le_antisymm h_y_le_dlo h_y_ge_dlo
      · right; apply Subtype.ext
        exact le_antisymm (hy_min dhi h_dhi_mem h_x_le_dhi)
          (h_dhi_round_up hs_eq y hy_mem hy_ge)
  -- Distances |x - dlo| = δ · 2^e and |x - dhi| = (1 - δ) · 2^e.
  set δ := s - (lo : ℝ) with h_δ_def
  have h_δ_nn : 0 ≤ δ := by change 0 ≤ s - (lo : ℝ); linarith
  have h_δ_lt : δ < 1 := by change s - (lo : ℝ) < 1; linarith
  have h_x_minus_dlo : x - (dlo : ℝ) = δ * (2 : ℝ) ^ e := by
    rw [h_dlo_real, ← h_s_unscale]
    rw [h_δ_def]; ring
  have h_dhi_minus_x : (dhi : ℝ) - x = (1 - δ) * (2 : ℝ) ^ e := by
    rw [h_dhi_real, ← h_s_unscale]
    push_cast
    change ((lo : ℝ) + 1) * (2 : ℝ) ^ e - s * (2 : ℝ) ^ e = (1 - δ) * (2 : ℝ) ^ e
    rw [h_δ_def]; ring
  have h_abs_x_minus_dlo : |x - (dlo : ℝ)| = δ * (2 : ℝ) ^ e := by
    rw [h_x_minus_dlo]
    rw [abs_mul, abs_of_pos h_2e_pos, abs_of_nonneg h_δ_nn]
  have h_abs_x_minus_dhi : |x - (dhi : ℝ)| = (1 - δ) * (2 : ℝ) ^ e := by
    rw [show x - (dhi : ℝ) = -((dhi : ℝ) - x) by ring, abs_neg, h_dhi_minus_x]
    rw [abs_mul, abs_of_pos h_2e_pos, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - δ)]
  -- Distance min reduces to δ vs 1 - δ, i.e., δ vs 1/2.
  have h_dlo_closer : δ < 1/2 → |x - (dlo : ℝ)| < |x - (dhi : ℝ)| := by
    intro h_δ_lt_half
    rw [h_abs_x_minus_dlo, h_abs_x_minus_dhi]
    have : δ < 1 - δ := by linarith
    exact mul_lt_mul_of_pos_right this h_2e_pos
  have h_dhi_closer : 1/2 < δ → |x - (dhi : ℝ)| < |x - (dlo : ℝ)| := by
    intro h_δ_gt_half
    rw [h_abs_x_minus_dlo, h_abs_x_minus_dhi]
    have : 1 - δ < δ := by linarith
    exact mul_lt_mul_of_pos_right this h_2e_pos
  have h_dist_eq : δ = 1/2 → |x - (dlo : ℝ)| = |x - (dhi : ℝ)| := by
    intro h_δ_half
    rw [h_abs_x_minus_dlo, h_abs_x_minus_dhi]
    congr 1; linarith
  -- Now split on tb.
  cases tb with
  | awayZero =>
    -- rndUnbounded F (.nearest .awayZero) x h = Dyadic.ofIntZpow (rndInt ...) e.
    have h_rnd_eq : rndUnbounded F (.nearest .awayZero) x h =
        Dyadic.ofIntZpow (rndInt (.nearest .awayZero) x e) e := by
      unfold rndUnbounded
      rw [dif_neg (by decide : (RoundingMode.nearest .awayZero) ≠ .toOdd)]
      rw [dif_neg (by decide :
        (RoundingMode.nearest .awayZero) ≠ .nearest .toEven)]
    rw [h_rnd_eq]
    -- Establish rndInt's value depending on δ.
    have h_rndInt_eq : rndInt (.nearest .awayZero) x e =
        (if δ < 1/2 then lo
         else if 1/2 < δ then lo + 1
         else if 0 ≤ x then lo + 1 else lo) := by
      change (if s - (lo : ℝ) < 1/2 then lo
              else if 1/2 < s - (lo : ℝ) then lo + 1
              else if 0 ≤ x then lo + 1 else lo) =
             if δ < 1/2 then lo
             else if 1/2 < δ then lo + 1
             else if 0 ≤ x then lo + 1 else lo
      rw [h_δ_def]
    rw [h_rndInt_eq]
    by_cases h_lt_half : δ < 1/2
    · -- y = dlo.
      rw [if_pos h_lt_half]
      refine ⟨h_dlo_mem, ?_, ?_, ?_⟩
      · left; exact ⟨h_dlo_mem, h_dlo_le_x, h_dlo_round_down⟩
      · intro z hz_mem hz_faith
        rcases h_faithful_eq z hz_faith with h_eq | h_eq
        · rw [h_eq]
        · rw [h_eq]; exact le_of_lt (h_dlo_closer h_lt_half)
      · intro z hz_mem hz_faith hz_ne hz_dist
        rcases h_faithful_eq z hz_faith with h_eq | h_eq
        · rw [h_eq]
        · exfalso
          rw [h_eq] at hz_dist
          have := h_dlo_closer h_lt_half
          linarith
    · rw [if_neg h_lt_half]
      by_cases h_gt_half : 1/2 < δ
      · -- y = dhi.
        rw [if_pos h_gt_half]
        have h_lo_ne_s : (lo : ℝ) ≠ s := by
          intro h_eq
          have : δ = 0 := by rw [h_δ_def]; linarith
          linarith
        refine ⟨h_dhi_mem, ?_, ?_, ?_⟩
        · right; exact ⟨h_dhi_mem, h_x_le_dhi, h_dhi_round_up h_lo_ne_s⟩
        · intro z hz_mem hz_faith
          rcases h_faithful_eq z hz_faith with h_eq | h_eq
          · rw [h_eq]; exact le_of_lt (h_dhi_closer h_gt_half)
          · rw [h_eq]
        · intro z hz_mem hz_faith hz_ne hz_dist
          rcases h_faithful_eq z hz_faith with h_eq | h_eq
          · exfalso
            rw [h_eq] at hz_dist
            have := h_dhi_closer h_gt_half
            linarith
          · rw [h_eq]
      · -- Tie: δ = 1/2.
        rw [if_neg h_gt_half]
        have h_δ_eq : δ = 1/2 := by
          push Not at h_lt_half h_gt_half
          linarith
        have h_dist_eq' : |x - (dlo : ℝ)| = |x - (dhi : ℝ)| := h_dist_eq h_δ_eq
        have h_lo_ne_s : (lo : ℝ) ≠ s := by
          intro h_eq
          have : δ = 0 := by rw [h_δ_def]; linarith
          linarith
        by_cases hx_nn : 0 ≤ x
        · rw [if_pos hx_nn]
          refine ⟨h_dhi_mem, ?_, ?_, ?_⟩
          · right; exact ⟨h_dhi_mem, h_x_le_dhi, h_dhi_round_up h_lo_ne_s⟩
          · intro z hz_mem hz_faith
            rcases h_faithful_eq z hz_faith with h_eq | h_eq
            · rw [h_eq, h_dist_eq']
            · rw [h_eq]
          · -- Tie rule: |z| ≤ |dhi|. In tie case, z = dlo or dhi. Show |dlo| ≤ |dhi|.
            intro z hz_mem hz_faith hz_ne hz_dist
            rcases h_faithful_eq z hz_faith with h_eq | h_eq
            · -- z = dlo. Show |dlo| ≤ |dhi|.
              rw [h_eq]
              -- x ≥ 0, dlo ≤ x ≤ dhi. So 0 ≤ x ≤ dhi means dhi ≥ 0.
              -- |dhi| = dhi. dlo ≤ dhi. If dlo ≥ 0, |dlo| = dlo ≤ dhi = |dhi|.
              -- If dlo < 0, |dlo| = -dlo. dlo ≤ x with |x - dlo| = |x - dhi| = (1/2)·2^e.
              -- dhi - x = (1/2)·2^e = x - dlo. dhi = 2x - dlo. |dhi| = 2x - dlo (since dhi ≥ 0).
              -- |dlo| = -dlo. |dlo| ≤ |dhi| iff -dlo ≤ 2x - dlo iff 0 ≤ 2x iff x ≥ 0. ✓
              have h_dhi_nn : (0 : ℝ) ≤ (dhi : ℝ) := le_trans hx_nn h_x_le_dhi
              rw [abs_of_nonneg h_dhi_nn]
              by_cases hdlo_nn : (0 : ℝ) ≤ (dlo : ℝ)
              · rw [abs_of_nonneg hdlo_nn]
                linarith [h_x_minus_dlo, h_dhi_minus_x, h_δ_eq]
              · push Not at hdlo_nn
                rw [abs_of_neg hdlo_nn]
                have h1 : x - (dlo : ℝ) = (1/2) * (2 : ℝ) ^ e := by
                  rw [h_x_minus_dlo, h_δ_eq]
                have h2 : (dhi : ℝ) - x = (1/2) * (2 : ℝ) ^ e := by
                  rw [h_dhi_minus_x, h_δ_eq]; ring
                linarith
            · rw [h_eq]
        · push Not at hx_nn
          rw [if_neg (by linarith : ¬ 0 ≤ x)]
          refine ⟨h_dlo_mem, ?_, ?_, ?_⟩
          · left; exact ⟨h_dlo_mem, h_dlo_le_x, h_dlo_round_down⟩
          · intro z hz_mem hz_faith
            rcases h_faithful_eq z hz_faith with h_eq | h_eq
            · rw [h_eq]
            · rw [h_eq, ← h_dist_eq']
          · -- Tie rule: x < 0, |z| ≤ |dlo|.
            intro z hz_mem hz_faith hz_ne hz_dist
            rcases h_faithful_eq z hz_faith with h_eq | h_eq
            · rw [h_eq]
            · -- z = dhi. dlo ≤ x < 0. |dlo| = -dlo, |dhi| = ?
              -- dhi - x = (1/2)·2^e = x - dlo. dhi = 2x - dlo.
              -- If dhi ≥ 0: |dhi| = 2x - dlo. |dlo| = -dlo.
              --   |dhi| ≤ |dlo| iff 2x - dlo ≤ -dlo iff 2x ≤ 0 iff x ≤ 0. ✓
              -- If dhi < 0: |dhi| = -dhi = -(2x - dlo) = dlo - 2x. |dlo| = -dlo.
              --   |dhi| ≤ |dlo| iff dlo - 2x ≤ -dlo iff 2dlo ≤ 2x iff dlo ≤ x. ✓
              rw [h_eq]
              have h_dlo_neg : (dlo : ℝ) < 0 := lt_of_le_of_lt h_dlo_le_x hx_nn
              rw [abs_of_neg h_dlo_neg]
              have h1 : x - (dlo : ℝ) = (1/2) * (2 : ℝ) ^ e := by
                rw [h_x_minus_dlo, h_δ_eq]
              have h2 : (dhi : ℝ) - x = (1/2) * (2 : ℝ) ^ e := by
                rw [h_dhi_minus_x, h_δ_eq]; ring
              by_cases hdhi_nn : (0 : ℝ) ≤ (dhi : ℝ)
              · rw [abs_of_nonneg hdhi_nn]
                linarith
              · push Not at hdhi_nn
                rw [abs_of_neg hdhi_nn]
                linarith
  | toEven =>
    have h_unb : ¬ F.unbounded.IsUndefined (.nearest .toEven) := h
    set F'' := F.toParityFormatOfNearestEven h with hF''_def
    set F' := F.unbounded.toParityFormatOfNearestEven h_unb with hF'_def
    have h_F'_eq : F'.toFormat = F.unbounded.toFormat := rfl
    -- Bridge: F'' and F' agree on IsEven (same p, exp).
    have h_isEven_bridge : ∀ (y : Dyadic), F''.IsEven y ↔ F'.IsEven y :=
      fun y => Iff.rfl
    have h_rnd_eq : rndUnbounded F (.nearest .toEven) x h =
        rndParity F'' (.nearest .toEven) x e := by
      unfold rndUnbounded
      rw [dif_neg (by decide : (RoundingMode.nearest .toEven) ≠ .toOdd)]
      rw [dif_pos rfl]
    rw [h_rnd_eq]
    -- rndParity for .nearest .toEven uses δ.
    have h_rndParity_eq : rndParity F'' (.nearest .toEven) x e =
        if δ < 1/2 then dlo
        else if 1/2 < δ then dhi
        else if F''.IsEven dlo then dlo else dhi := by
      change (if s - (lo : ℝ) < 1/2 then dlo
              else if 1/2 < s - (lo : ℝ) then dhi
              else if F''.IsEven dlo then dlo else dhi) =
           if δ < 1/2 then dlo
           else if 1/2 < δ then dhi
           else if F''.IsEven dlo then dlo else dhi
      rw [h_δ_def]
    rw [h_rndParity_eq]
    by_cases h_lt_half : δ < 1/2
    · rw [if_pos h_lt_half]
      refine ⟨h_dlo_mem, ?_, ?_, ?_⟩
      · left; exact ⟨h_dlo_mem, h_dlo_le_x, h_dlo_round_down⟩
      · intro z hz_mem hz_faith
        rcases h_faithful_eq z hz_faith with h_eq | h_eq
        · rw [h_eq]
        · rw [h_eq]; exact le_of_lt (h_dlo_closer h_lt_half)
      · -- No tie: no z ≠ dlo equidistant with dlo.
        rintro ⟨z, hz_mem, hz_faith, hz_ne, hz_dist⟩
        exfalso
        rcases h_faithful_eq z hz_faith with h_eq | h_eq
        · exact hz_ne h_eq
        · rw [h_eq] at hz_dist
          have := h_dlo_closer h_lt_half
          linarith
    · rw [if_neg h_lt_half]
      by_cases h_gt_half : 1/2 < δ
      · rw [if_pos h_gt_half]
        have h_lo_ne_s : (lo : ℝ) ≠ s := by
          intro h_eq
          have : δ = 0 := by rw [h_δ_def]; linarith
          linarith
        refine ⟨h_dhi_mem, ?_, ?_, ?_⟩
        · right; exact ⟨h_dhi_mem, h_x_le_dhi, h_dhi_round_up h_lo_ne_s⟩
        · intro z hz_mem hz_faith
          rcases h_faithful_eq z hz_faith with h_eq | h_eq
          · rw [h_eq]; exact le_of_lt (h_dhi_closer h_gt_half)
          · rw [h_eq]
        · rintro ⟨z, hz_mem, hz_faith, hz_ne, hz_dist⟩
          exfalso
          rcases h_faithful_eq z hz_faith with h_eq | h_eq
          · rw [h_eq] at hz_dist
            have := h_dhi_closer h_gt_half
            linarith
          · exact hz_ne h_eq
      · rw [if_neg h_gt_half]
        have h_δ_eq : δ = 1/2 := by
          push Not at h_lt_half h_gt_half; linarith
        have h_dist_eq' : |x - (dlo : ℝ)| = |x - (dhi : ℝ)| := h_dist_eq h_δ_eq
        have h_lo_ne_s : (lo : ℝ) ≠ s := by
          intro h_eq
          have : δ = 0 := by rw [h_δ_def]; linarith
          linarith
        by_cases h_even_dlo : F''.IsEven dlo
        · rw [if_pos h_even_dlo]
          refine ⟨h_dlo_mem, ?_, ?_, ?_⟩
          · left; exact ⟨h_dlo_mem, h_dlo_le_x, h_dlo_round_down⟩
          · intro z hz_mem hz_faith
            rcases h_faithful_eq z hz_faith with h_eq | h_eq
            · rw [h_eq]
            · rw [h_eq, h_dist_eq']
          · intro _
            refine ⟨F', h_F'_eq, (h_isEven_bridge dlo).mp h_even_dlo⟩
        · rw [if_neg h_even_dlo]
          refine ⟨h_dhi_mem, ?_, ?_, ?_⟩
          · right; exact ⟨h_dhi_mem, h_x_le_dhi, h_dhi_round_up h_lo_ne_s⟩
          · intro z hz_mem hz_faith
            rcases h_faithful_eq z hz_faith with h_eq | h_eq
            · rw [h_eq, ← h_dist_eq']
            · rw [h_eq]
          · intro _
            refine ⟨F', h_F'_eq, ?_⟩
            rw [← h_isEven_bridge dhi]
            -- Case on F's format to apply the right alternating_isEven_* lemma.
            have h_dlo_at_e : dlo = Dyadic.ofIntZpow lo e := h_dlo_def
            have h_dhi_at_e : dhi = Dyadic.ofIntZpow (lo + 1) e := h_dhi_def
            cases hp_F : F.p with
            | top =>
              cases hexp_F : F.exp with
              | bot =>
                exfalso
                rcases F.finite with hf | hf
                · exact hf hp_F
                · exact hf hexp_F
              | coe e'' =>
                -- Fixedpoint case.
                have h_e_eq : e = e'' := by
                  change F.canonicalExp x = _
                  unfold FiniteFormat.canonicalExp
                  simp [hp_F, hexp_F]
                have h_dlo_at_e'' : dlo = Dyadic.ofIntZpow lo e'' := by
                  rw [h_dlo_at_e, h_e_eq]
                have h_dhi_at_e'' : dhi = Dyadic.ofIntZpow (lo + 1) e'' := by
                  rw [h_dhi_at_e, h_e_eq]
                have hp_top_F'' : F''.toFormat.p = ⊤ := hp_F
                have hexp_F'' : F''.toFormat.exp = (e'' : WithBot ℤ) := hexp_F
                rw [h_dhi_at_e'']
                apply ParityFormat.alternating_isEven_fixedpoint hp_top_F'' hexp_F''
                rw [← h_dlo_at_e'']
                exact h_even_dlo
            | coe p =>
              cases hexp_F : F.exp with
              | bot =>
                -- Floating case. p ≠ 1 (else undefined for .nearest .toEven).
                have hp_eq : F''.toFormat.p = ((p : ℕ+) : WithTop ℕ+) := hp_F
                have hexp_bot : F''.toFormat.exp = ⊥ := hexp_F
                have hp_ne_1 : F''.toFormat.p ≠ ((1 : ℕ+) : WithTop ℕ+) := by
                  change F.p ≠ _
                  rw [hp_F]
                  intro h_eq
                  have h_eq' : p = (1 : ℕ+) := by exact_mod_cast h_eq
                  exact h ⟨by rw [hp_F, h_eq'], hexp_F, Or.inr rfl⟩
                -- Derive x ≠ 0 from δ = 1/2 (s = lo + 1/2 ≠ 0).
                have hx_ne : x ≠ 0 := by
                  intro hx0
                  subst hx0
                  -- s = 0 · 2^(-e) = 0, δ = 0 - lo. For δ = 1/2: lo = -1/2 (not int).
                  have h_s_zero : s = 0 := by
                    change (0 : ℝ) * (2 : ℝ) ^ (-e) = 0; ring
                  have h_δ_zero_lo : δ = -lo := by
                    change s - (lo : ℝ) = -lo
                    rw [h_s_zero]; ring
                  rw [h_δ_zero_lo] at h_δ_eq
                  -- -lo = 1/2 with lo : ℤ is impossible.
                  have h_2lo_neg1 : 2 * lo = -1 := by
                    have h_real : (2 * lo : ℝ) = -1 := by linarith
                    exact_mod_cast h_real
                  omega
                -- e = log|x| + 1 - p (floating canonical exp).
                have h_e_eq_log : e = Int.log 2 |x| + 1 - (p : ℤ) := by
                  change F.canonicalExp x = _
                  unfold FiniteFormat.canonicalExp
                  simp [hp_F, hexp_F, hx_ne]
                have h_s_lo_real : ((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) ≤ |s| :=
                  two_pow_pred_le_scaled (p := p) hx_ne h_e_eq_log
                -- Derive h_lo_lo (|lo| ≥ 2^(p-1)) by sign-split on x.
                have h_lo_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo| :=
                  abs_floor_ge_two_pow_pred (p := p) h_s_lo_real
                -- h_lop1_lo: similar argument. Use δ ≠ 0 to handle "exact" case.
                have h_lop1_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo + 1| := by
                  -- δ = 1/2 ≠ 0, so lo ≠ s. Use strict reasoning.
                  by_cases hs_nn : 0 ≤ s
                  · have h_lo_nn : 0 ≤ lo := Int.floor_nonneg.mpr hs_nn
                    rw [abs_of_nonneg (by linarith : (0 : ℤ) ≤ lo + 1)]
                    have h_lo_ge : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ lo := by
                      rw [← abs_of_nonneg h_lo_nn]; exact h_lo_lo
                    linarith
                  · push Not at hs_nn
                    have hs_neg : s < 0 := hs_nn
                    have h_floor_lt : (lo : ℝ) < s := by
                      have : (lo : ℝ) ≠ s := by
                        intro h_eq
                        have : δ = 0 := by rw [h_δ_def]; linarith
                        linarith
                      have h_floor_le : (lo : ℝ) ≤ s := Int.floor_le _
                      exact lt_of_le_of_ne h_floor_le this
                    have h_s_le_r : s ≤ -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) := by
                      have h_abs_eq : |s| = -s := abs_of_neg hs_neg
                      linarith [h_s_lo_real]
                    have h_lo_lt_neg : (lo : ℝ) < -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) :=
                      lt_of_lt_of_le h_floor_lt h_s_le_r
                    have h_lo_lt_int : lo < -((2 : ℤ) ^ ((p : ℕ) - 1)) := by
                      exact_mod_cast h_lo_lt_neg
                    have h_lop1_le : lo + 1 ≤ -((2 : ℤ) ^ ((p : ℕ) - 1)) := by
                      linarith
                    have h_lop1_neg : lo + 1 < 0 := by
                      have : (0 : ℤ) < (2 : ℤ) ^ ((p : ℕ) - 1) := by positivity
                      linarith
                    rw [abs_of_neg h_lop1_neg]; linarith
                rw [h_dhi_at_e]
                apply ParityFormat.alternating_isEven_floating hp_eq hp_ne_1 hexp_bot
                  h_lo_lo (h_lo_bound hp_F) h_lop1_lo (h_lop1_bound hp_F)
                rw [← h_dlo_at_e]
                exact h_even_dlo
              | coe e'' =>
                -- Mixed case. Mirrors structure of `_toOdd_satisfies` mixed case.
                have hp_eq : F''.toFormat.p = ((p : ℕ+) : WithTop ℕ+) := hp_F
                have hexp_eq : F''.toFormat.exp = (e'' : WithBot ℤ) := hexp_F
                -- hx_ne from tie (s = lo + 1/2 ≠ 0).
                have hx_ne : x ≠ 0 := by
                  intro hx0
                  subst hx0
                  have h_s_zero : s = 0 := by
                    change (0 : ℝ) * (2 : ℝ) ^ (-e) = 0; ring
                  have h_δ_zero_lo : δ = -lo := by
                    change s - (lo : ℝ) = -lo
                    rw [h_s_zero]; ring
                  rw [h_δ_zero_lo] at h_δ_eq
                  have h_2lo_neg1 : 2 * lo = -1 := by
                    have h_real : (2 * lo : ℝ) = -1 := by linarith
                    exact_mod_cast h_real
                  omega
                by_cases hp_eq_1 : p = (1 : ℕ+)
                · -- p = 1.
                  subst hp_eq_1
                  have hp_eq_1' : F''.toFormat.p = ((1 : ℕ+) : WithTop ℕ+) := hp_F
                  have h_e_ge : e'' ≤ e := F.exp_le_canonicalExp x hexp_F
                  have h_s_lt : |x * (2 : ℝ) ^ (-e)| < (2 : ℝ) ^ ((1 : ℕ+) : ℕ) :=
                    floor_mantissa_lt hp_F
                  have h_s_lt_2 : |x * (2 : ℝ) ^ (-e)| < ((2 : ℤ) : ℝ) := by
                    have h_cast : ((2 : ℤ) : ℝ) = (2 : ℝ) ^ ((1 : ℕ+) : ℕ) := by
                      change (2 : ℝ) = (2 : ℝ) ^ (1 : ℕ); ring
                    rw [h_cast]; exact h_s_lt
                  have h_lo_hi_int : |lo| ≤ 2 := abs_floor_le_of_abs_lt h_s_lt_2
                  have h_lop1_hi_int : |lo + 1| ≤ 2 :=
                    abs_floor_add_one_le_of_abs_lt (p := 1) h_s_lt
                  by_cases h_regime : Int.log 2 |x| + 1 - ((1 : ℕ+) : ℤ) ≤ e''
                  · -- Subnormal: e = e''.
                    have h_e_eq : e = e'' := by
                      change F.canonicalExp x = e''
                      unfold FiniteFormat.canonicalExp
                      simp only [hp_F, hexp_F]
                      rw [if_neg hx_ne]
                      exact max_eq_right h_regime
                    rw [h_dhi_at_e, h_e_eq]
                    apply ParityFormat.alternating_isEven_mixed_subnormal_p1
                      hp_eq_1' hexp_eq h_lo_hi_int h_lop1_hi_int
                    rw [← h_e_eq, ← h_dlo_at_e]; exact h_even_dlo
                  · -- Normal.
                    push Not at h_regime
                    have h_pcast : ((1 : ℕ+) : ℤ) = 1 := rfl
                    have h_e_eq_log : e = Int.log 2 |x| := by
                      change F.canonicalExp x = _
                      unfold FiniteFormat.canonicalExp
                      simp only [hp_F, hexp_F]
                      rw [if_neg hx_ne]
                      rw [show (((1 : ℕ+) : ℕ) : ℤ) = 1 from rfl]
                      have h_max_eq : max (Int.log 2 |x| + 1 - 1) e'' =
                          Int.log 2 |x| + 1 - 1 := by
                        apply max_eq_left
                        have := h_regime; rw [h_pcast] at this; linarith
                      rw [h_max_eq]; ring
                    have h_x_ge : (2 : ℝ) ^ (Int.log 2 |x|) ≤ |x| :=
                      Int.zpow_log_le_self (b := 2) (by norm_num : (1 : ℕ) < 2)
                        (abs_pos.mpr hx_ne)
                    have h_abs_s : 1 ≤ |x * (2 : ℝ) ^ (-e)| := by
                      have h_abs_eq : |x * (2 : ℝ) ^ (-e)| = |x| * (2 : ℝ) ^ (-e) := by
                        rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)]
                      rw [h_abs_eq, h_e_eq_log]
                      have h_pow_eq : (2 : ℝ) ^ (Int.log 2 |x|) *
                          (2 : ℝ) ^ (-Int.log 2 |x|) = 1 := by
                        rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
                            add_neg_cancel, zpow_zero]
                      have h_le := mul_le_mul_of_nonneg_right h_x_ge
                        (zpow_pos (by norm_num : (0 : ℝ) < 2) (-Int.log 2 |x|)).le
                      rw [h_pow_eq] at h_le
                      exact h_le
                    have h_lo_lo_int : 1 ≤ |lo| := by
                      by_cases hs_nn : 0 ≤ x * (2 : ℝ) ^ (-e)
                      · have h_s_ge : 1 ≤ x * (2 : ℝ) ^ (-e) := by
                          have h_abs_eq : |x * (2 : ℝ) ^ (-e)| = x * (2 : ℝ) ^ (-e) :=
                            abs_of_nonneg hs_nn
                          linarith [h_abs_s]
                        have h_lo_ge_1 : 1 ≤ lo := by
                          apply Int.le_floor.mpr; push_cast; exact h_s_ge
                        rw [abs_of_nonneg (by linarith : (0 : ℤ) ≤ lo)]; exact h_lo_ge_1
                      · push Not at hs_nn
                        have h_s_le : x * (2 : ℝ) ^ (-e) ≤ -1 := by
                          have h_abs_eq : |x * (2 : ℝ) ^ (-e)| =
                              -(x * (2 : ℝ) ^ (-e)) := abs_of_neg hs_nn
                          linarith [h_abs_s]
                        have h_floor_le : (lo : ℝ) ≤ x * (2 : ℝ) ^ (-e) :=
                          Int.floor_le _
                        have h_lo_le : (lo : ℝ) ≤ -1 := le_trans h_floor_le h_s_le
                        have h_lo_le_int : lo ≤ -1 := by exact_mod_cast h_lo_le
                        rw [abs_of_neg (by linarith : lo < 0)]; linarith
                    -- lo ≠ -1 from tie (δ = 1/2 means s = lo + 1/2; if lo = -1,
                    -- s = -1/2, but |s| ≥ 1 contradicts).
                    have h_lo_ne_neg1 : lo ≠ -1 := by
                      intro h_eq
                      -- s = lo + 1/2 = -1 + 1/2 = -1/2. |s| = 1/2 < 1.
                      have h_s_eq : s = (lo : ℝ) + 1/2 := by
                        change s = (lo : ℝ) + 1/2
                        have := h_δ_eq; change s - (lo : ℝ) = 1/2 at this
                        linarith
                      rw [h_eq] at h_s_eq
                      push_cast at h_s_eq
                      have h_s_lt_1 : |s| < 1 := by
                        rw [h_s_eq]
                        rw [show |(-1 + 1/2 : ℝ)| = 1/2 by norm_num]
                        norm_num
                      linarith [h_abs_s]
                    have h_lop1_lo_int : 1 ≤ |lo + 1| := by
                      have h_lop1_ne : lo + 1 ≠ 0 := by
                        intro h0; apply h_lo_ne_neg1; omega
                      exact Int.one_le_abs h_lop1_ne
                    rw [h_dhi_at_e]
                    apply ParityFormat.alternating_isEven_mixed_normal_p1
                      hp_eq_1' hexp_eq h_e_ge h_lo_lo_int h_lo_hi_int
                      h_lop1_lo_int h_lop1_hi_int
                    rw [← h_dlo_at_e]; exact h_even_dlo
                · -- p ≠ 1.
                  have hp_ne_1 : F''.toFormat.p ≠ ((1 : ℕ+) : WithTop ℕ+) := by
                    change F.p ≠ _
                    rw [hp_F]
                    intro h
                    apply hp_eq_1
                    exact_mod_cast h
                  by_cases h_regime : Int.log 2 |x| + 1 - ((p : ℕ+) : ℤ) ≤ e''
                  · -- Subnormal: e = e''.
                    have h_e_eq : e = e'' := by
                      change F.canonicalExp x = e''
                      unfold FiniteFormat.canonicalExp
                      simp only [hp_F, hexp_F]
                      rw [if_neg hx_ne]
                      exact max_eq_right h_regime
                    have h_x_lt : |x| < (2 : ℝ) ^ (e'' + (p : ℤ)) := by
                      have h_log_le : Int.log 2 |x| ≤ e'' + (p : ℤ) - 1 := by
                        have h_pcast : ((p : ℕ+) : ℤ) = (p : ℤ) := rfl
                        linarith
                      have h_lt := Int.lt_zpow_succ_log_self
                        (by norm_num : (1 : ℕ) < 2) |x|
                      have : Int.log 2 |x| + 1 ≤ e'' + (p : ℤ) := by linarith
                      exact lt_of_lt_of_le h_lt
                        (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) this)
                    have h_s_lt : |x * (2 : ℝ) ^ (-e)| < (2 : ℝ) ^ ((p : ℕ+) : ℕ) := by
                      rw [h_e_eq]
                      have h_abs : |x * (2 : ℝ) ^ (-e'')| = |x| * (2 : ℝ) ^ (-e'') := by
                        rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)]
                      rw [h_abs]
                      have h_2neg_pos : (0 : ℝ) < (2 : ℝ) ^ (-e'') := zpow_pos (by norm_num) _
                      have h_eq_split : (2 : ℝ) ^ (e'' + (p : ℤ)) =
                          (2 : ℝ) ^ e'' * (2 : ℝ) ^ ((p : ℕ+) : ℕ) := by
                        rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
                        have h_pcast : ((p : ℕ+) : ℤ) = (((p : ℕ+) : ℕ) : ℤ) := rfl
                        rw [h_pcast, zpow_natCast]
                      have h_x2neg : |x| * (2 : ℝ) ^ (-e'') <
                          (2 : ℝ) ^ (e'' + (p : ℤ)) * (2 : ℝ) ^ (-e'') :=
                        mul_lt_mul_of_pos_right h_x_lt h_2neg_pos
                      rw [h_eq_split] at h_x2neg
                      have h_cancel : (2 : ℝ) ^ e'' * (2 : ℝ) ^ ((p : ℕ+) : ℕ) *
                          (2 : ℝ) ^ (-e'') = (2 : ℝ) ^ ((p : ℕ+) : ℕ) := by
                        rw [mul_right_comm, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
                            add_neg_cancel, zpow_zero, one_mul]
                      rw [h_cancel] at h_x2neg
                      exact h_x2neg
                    have h_lo_le : |lo| ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by
                      apply abs_floor_le_of_abs_lt
                      push_cast; exact h_s_lt
                    have h_lop1_le : |lo + 1| ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) :=
                      abs_floor_add_one_le_of_abs_lt h_s_lt
                    have h_dlo_at_e'' : dlo = Dyadic.ofIntZpow lo e'' := by
                      rw [h_dlo_at_e, h_e_eq]
                    have h_dhi_at_e'' : dhi = Dyadic.ofIntZpow (lo + 1) e'' := by
                      rw [h_dhi_at_e, h_e_eq]
                    -- Case-split on saturation.
                    rcases lt_or_eq_of_le h_lo_le with h_lo_lt | h_lo_sat
                    · rcases lt_or_eq_of_le h_lop1_le with h_lop1_lt | h_lop1_sat
                      · -- Both non-sat: apply alternating_isEven_mixed_subnormal_pne1.
                        have h_log_lo' := log_lt_p_of_abs_lt_two_pow h_lo_lt
                        have h_log_lop1_raw := log_lt_p_of_abs_lt_two_pow h_lop1_lt
                        have h_log_lop1' : Int.log 2 |((lo : ℝ) + 1)| + 1 ≤
                            (((p : ℕ+) : ℕ) : ℤ) := by
                          have h_eq : |((lo : ℝ) + 1)| = |((lo + 1 : ℤ) : ℝ)| := by
                            push_cast; rfl
                          rw [h_eq]; exact h_log_lop1_raw
                        rw [h_dhi_at_e'']
                        apply ParityFormat.alternating_isEven_mixed_subnormal_pne1
                          hp_eq hp_ne_1 hexp_eq h_log_lo' h_log_lop1'
                        rw [← h_dlo_at_e'']; exact h_even_dlo
                      · -- |lo+1| = 2^p sat: IsEven dhi via saturation lemma.
                        rw [h_dhi_at_e'']
                        have h_dhi_real_e'' : (Dyadic.ofIntZpow (lo + 1) e'' : ℝ) =
                            ((lo + 1 : ℤ) : ℝ) * (2 : ℝ) ^ e'' :=
                          Dyadic.coe_ofIntZpow _ _
                        have h_lop1_ne : lo + 1 ≠ 0 := by
                          intro h_zero
                          rw [h_zero] at h_lop1_sat
                          simp at h_lop1_sat
                          have : (0 : ℤ) < (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by positivity
                          omega
                        have h_dhi_ne : (Dyadic.ofIntZpow (lo + 1) e'' : ℝ) ≠ 0 := by
                          rw [h_dhi_real_e'']
                          exact mul_ne_zero (Int.cast_ne_zero.mpr h_lop1_ne)
                            (ne_of_gt (zpow_pos (by norm_num) _))
                        have h_log_2p : Int.log 2 (|lo + 1| : ℝ) =
                            (((p : ℕ+) : ℕ) : ℤ) := by
                          have h_bridge : (|lo + 1| : ℝ) = ((|lo + 1| : ℤ) : ℝ) := by
                            push_cast; rfl
                          rw [h_bridge, h_lop1_sat]
                          have h_cast : (((2 : ℤ) ^ ((p : ℕ+) : ℕ) : ℤ) : ℝ) =
                              (2 : ℝ) ^ (((p : ℕ+) : ℕ) : ℤ) := by
                            rw [zpow_natCast]; push_cast; rfl
                          rw [h_cast]
                          exact Int.log_zpow (by norm_num : 1 < 2) _
                        have h_log_dhi : Int.log 2 |(Dyadic.ofIntZpow (lo + 1) e'' : ℝ)| =
                            (((p : ℕ+) : ℕ) : ℤ) + e'' := by
                          rw [h_dhi_real_e'', ParityFormat.log_abs_mul_zpow h_lop1_ne e'']
                          have h_cast_eq : |((lo + 1 : ℤ) : ℝ)| = (|lo + 1| : ℝ) := by
                            push_cast; rfl
                          rw [h_cast_eq, h_log_2p]
                        have h_log_y_ge : (((p : ℕ+) : ℕ) : ℤ) ≤
                            Int.log 2 |(Dyadic.ofIntZpow (lo + 1) e'' : ℝ)| - e'' + 1 := by
                          rw [h_log_dhi]; linarith
                        exact ParityFormat.isEven_at_saturation_mixed_normal hp_eq
                          hp_ne_1 hexp_eq h_dhi_ne h_log_y_ge h_dhi_real_e'' h_lop1_sat
                    · -- |lo| = 2^p sat: IsEven dlo holds, contradicts h_even_dlo.
                      exfalso; apply h_even_dlo
                      rw [h_dlo_at_e'']
                      have h_dlo_real_e'' : (Dyadic.ofIntZpow lo e'' : ℝ) =
                          (lo : ℝ) * (2 : ℝ) ^ e'' := Dyadic.coe_ofIntZpow _ _
                      have h_lo_ne : lo ≠ 0 := by
                        intro h_zero
                        rw [h_zero] at h_lo_sat
                        simp at h_lo_sat
                        have : (0 : ℤ) < (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by positivity
                        omega
                      have h_dlo_ne : (Dyadic.ofIntZpow lo e'' : ℝ) ≠ 0 := by
                        rw [h_dlo_real_e'']
                        exact mul_ne_zero (Int.cast_ne_zero.mpr h_lo_ne)
                          (ne_of_gt (zpow_pos (by norm_num) _))
                      have h_log_2p : Int.log 2 (|lo| : ℝ) = (((p : ℕ+) : ℕ) : ℤ) := by
                        have h_bridge : (|lo| : ℝ) = ((|lo| : ℤ) : ℝ) := by
                          push_cast; rfl
                        rw [h_bridge, h_lo_sat]
                        have h_cast : (((2 : ℤ) ^ ((p : ℕ+) : ℕ) : ℤ) : ℝ) =
                            (2 : ℝ) ^ (((p : ℕ+) : ℕ) : ℤ) := by
                          rw [zpow_natCast]; push_cast; rfl
                        rw [h_cast]
                        exact Int.log_zpow (by norm_num : 1 < 2) _
                      have h_log_dlo : Int.log 2 |(Dyadic.ofIntZpow lo e'' : ℝ)| =
                          (((p : ℕ+) : ℕ) : ℤ) + e'' := by
                        rw [h_dlo_real_e'', ParityFormat.log_abs_mul_zpow h_lo_ne e'']
                        have h_cast_eq : |(lo : ℝ)| = (|lo| : ℝ) := by rfl
                        rw [h_cast_eq, h_log_2p]
                      have h_log_y_ge : (((p : ℕ+) : ℕ) : ℤ) ≤
                          Int.log 2 |(Dyadic.ofIntZpow lo e'' : ℝ)| - e'' + 1 := by
                        rw [h_log_dlo]; linarith
                      exact ParityFormat.isEven_at_saturation_mixed_normal hp_eq
                        hp_ne_1 hexp_eq h_dlo_ne h_log_y_ge h_dlo_real_e'' h_lo_sat
                  · -- Normal regime.
                    push Not at h_regime
                    have h_dlo_real_e : (dlo : ℝ) = (lo : ℝ) * (2 : ℝ) ^ e := by
                      rw [h_dlo_at_e]; exact Dyadic.coe_ofIntZpow _ _
                    have h_dhi_real_e : (dhi : ℝ) = ((lo + 1 : ℤ) : ℝ) * (2 : ℝ) ^ e := by
                      rw [h_dhi_at_e]; exact Dyadic.coe_ofIntZpow _ _
                    have h_e_eq_log : e = Int.log 2 |x| + 1 - ((p : ℕ+) : ℤ) := by
                      change F.canonicalExp x = _
                      unfold FiniteFormat.canonicalExp
                      simp only [hp_F, hexp_F]
                      rw [if_neg hx_ne]
                      exact max_eq_left (le_of_lt h_regime)
                    have h_x_ge : (2 : ℝ) ^ (Int.log 2 |x|) ≤ |x| :=
                      Int.zpow_log_le_self (b := 2) (by norm_num : (1 : ℕ) < 2)
                        (abs_pos.mpr hx_ne)
                    have h_pcast : ((p : ℕ+) : ℤ) = ((p : ℕ) : ℤ) := rfl
                    have h_2neg_pos : (0 : ℝ) < (2 : ℝ) ^ (-e) :=
                      zpow_pos (by norm_num) _
                    have h_s_lo_real : ((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) ≤
                        |x * (2 : ℝ) ^ (-e)| :=
                      two_pow_pred_le_scaled (p := p) hx_ne h_e_eq_log
                    have h_lo_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo| :=
                      abs_floor_ge_two_pow_pred (p := p) h_s_lo_real
                    have h_lop1_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo + 1| := by
                      -- δ = 1/2 ≠ 0, so lo ≠ s (strict).
                      by_cases hs_nn : 0 ≤ s
                      · have h_lo_nn : 0 ≤ lo := Int.floor_nonneg.mpr hs_nn
                        rw [abs_of_nonneg (by linarith : (0 : ℤ) ≤ lo + 1)]
                        linarith [h_lo_lo, abs_of_nonneg h_lo_nn]
                      · have hs_neg : s < 0 := not_le.mp hs_nn
                        have h_floor_lt : (lo : ℝ) < s := by
                          have h_ne : (lo : ℝ) ≠ s := by
                            intro h_eq
                            have : δ = 0 := by rw [h_δ_def]; linarith
                            linarith
                          have h_floor_le : (lo : ℝ) ≤ s := Int.floor_le _
                          exact lt_of_le_of_ne h_floor_le h_ne
                        have h_s_le_r : s ≤ -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) := by
                          have h_abs_eq : |s| = -s := abs_of_neg hs_neg
                          linarith [h_s_lo_real]
                        have h_lo_lt_neg : (lo : ℝ) < -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) :=
                          lt_of_lt_of_le h_floor_lt h_s_le_r
                        have h_lo_lt_int : lo < -((2 : ℤ) ^ ((p : ℕ) - 1)) := by
                          exact_mod_cast h_lo_lt_neg
                        have h_lop1_le : lo + 1 ≤ -((2 : ℤ) ^ ((p : ℕ) - 1)) := by linarith
                        have h_lop1_neg : lo + 1 < 0 := by
                          have : (0 : ℤ) < (2 : ℤ) ^ ((p : ℕ) - 1) := by positivity
                          linarith
                        rw [abs_of_neg h_lop1_neg]; linarith
                    have h_lo_hi : |lo| ≤ (2 : ℤ) ^ ((p : ℕ) : ℕ) := h_lo_bound hp_F
                    have h_lop1_hi : |lo + 1| ≤ (2 : ℤ) ^ ((p : ℕ) : ℕ) :=
                      h_lop1_bound hp_F
                    have h_lo_ne : lo ≠ 0 := by
                      intro h_lo_zero
                      rw [h_lo_zero] at h_lo_lo
                      simp at h_lo_lo
                      have : (0 : ℤ) < (2 : ℤ) ^ ((p : ℕ) - 1) := by positivity
                      omega
                    have h_lop1_ne : lo + 1 ≠ 0 := by
                      intro h_lop1_zero
                      rw [h_lop1_zero] at h_lop1_lo
                      simp at h_lop1_lo
                      have : (0 : ℤ) < (2 : ℤ) ^ ((p : ℕ) - 1) := by positivity
                      omega
                    have h_dlo_ne : (dlo : ℝ) ≠ 0 := by
                      rw [h_dlo_real_e]
                      exact mul_ne_zero (Int.cast_ne_zero.mpr h_lo_ne)
                        (ne_of_gt (zpow_pos (by norm_num) _))
                    have h_dhi_ne : (dhi : ℝ) ≠ 0 := by
                      rw [h_dhi_real_e]
                      exact mul_ne_zero (Int.cast_ne_zero.mpr h_lop1_ne)
                        (ne_of_gt (zpow_pos (by norm_num) _))
                    have h_log_dlo : Int.log 2 |(dlo : ℝ)| =
                        Int.log 2 |(lo : ℝ)| + e := by
                      rw [h_dlo_real_e]
                      exact ParityFormat.log_abs_mul_zpow h_lo_ne e
                    have h_log_dhi : Int.log 2 |(dhi : ℝ)| =
                        Int.log 2 |((lo + 1 : ℤ) : ℝ)| + e := by
                      rw [h_dhi_real_e]
                      exact ParityFormat.log_abs_mul_zpow h_lop1_ne e
                    have h_log_2pow_nat := log_two_pow_nat
                    have h_log_lo_lb := log_ge_p_pred_of_two_pow_pred_le
                      (k := lo) h_lo_lo
                    have h_log_lop1_lb := log_ge_p_pred_of_two_pow_pred_le
                      (k := lo + 1) h_lop1_lo
                    have h_log_lo : ((p : ℕ) : ℤ) ≤ Int.log 2 |(dlo : ℝ)| - e'' + 1 := by
                      rw [h_log_dlo, h_e_eq_log]
                      have : Int.log 2 |x| - e'' ≥ ((p : ℕ) : ℤ) := by linarith
                      linarith [h_log_lo_lb]
                    have h_log_hi : ((p : ℕ) : ℤ) ≤ Int.log 2 |(dhi : ℝ)| - e'' + 1 := by
                      rw [h_log_dhi, h_e_eq_log]
                      have : Int.log 2 |x| - e'' ≥ ((p : ℕ) : ℤ) := by linarith
                      linarith [h_log_lop1_lb]
                    exact ParityFormat.alternating_isEven_mixed_normal_pne1
                      hp_eq hp_ne_1 hexp_eq h_dlo_ne h_dhi_ne h_log_lo h_log_hi
                      h_dlo_real_e h_dhi_real_e h_lo_lo h_lo_hi h_lop1_lo h_lop1_hi
                      h_even_dlo

/-- The constructive `rndUnbounded` satisfies the unbounded rounding spec. -/
theorem rndUnbounded_satisfies (F : FiniteFormat) (rm : RoundingMode) (x : ℝ)
    (h : ¬ F.IsUndefined rm) :
    RoundsFinite F.unbounded rm x (rndUnbounded F rm x h) := by
  cases rm with
  | toNegative => exact rndUnbounded_satisfies_toNegative F x h
  | toPositive => exact rndUnbounded_satisfies_toPositive F x h
  | toZero => exact rndUnbounded_satisfies_toZero F x h
  | awayZero => exact rndUnbounded_satisfies_awayZero F x h
  | toOdd => exact rndUnbounded_satisfies_toOdd F x h
  | nearest tb => exact rndUnbounded_satisfies_nearest F tb x h

/-! Per-mode uniqueness obligations. The pattern follows the spec:
two values agreeing on the mode-spec must equal each other. -/

theorem rndUnbounded_unique_toNegative (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .toNegative) {y : Dyadic}
    (hy : RoundsFinite F.unbounded .toNegative x y) :
    y = rndUnbounded F .toNegative x h := by
  set y' := rndUnbounded F .toNegative x h
  have hy' : RoundsFinite F.unbounded .toNegative x y' :=
    rndUnbounded_satisfies_toNegative F x h
  obtain ⟨hy_mem, hy_le, hy_max⟩ := hy
  obtain ⟨hy'_mem, hy'_le, hy'_max⟩ := hy'
  have h1 : (y' : ℝ) ≤ (y : ℝ) := hy_max y' hy'_mem hy'_le
  have h2 : (y : ℝ) ≤ (y' : ℝ) := hy'_max y hy_mem hy_le
  exact Subtype.ext (le_antisymm h2 h1)

theorem rndUnbounded_unique_toPositive (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .toPositive) {y : Dyadic}
    (hy : RoundsFinite F.unbounded .toPositive x y) :
    y = rndUnbounded F .toPositive x h := by
  set y' := rndUnbounded F .toPositive x h
  have hy' : RoundsFinite F.unbounded .toPositive x y' :=
    rndUnbounded_satisfies_toPositive F x h
  obtain ⟨hy_mem, hy_ge, hy_min⟩ := hy
  obtain ⟨hy'_mem, hy'_ge, hy'_min⟩ := hy'
  have h1 : (y : ℝ) ≤ (y' : ℝ) := hy_min y' hy'_mem hy'_ge
  have h2 : (y' : ℝ) ≤ (y : ℝ) := hy'_min y hy_mem hy_ge
  exact Subtype.ext (le_antisymm h1 h2)

theorem rndUnbounded_unique_toZero (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .toZero) {y : Dyadic}
    (hy : RoundsFinite F.unbounded .toZero x y) :
    y = rndUnbounded F .toZero x h := by
  set y' := rndUnbounded F .toZero x h
  have hy' : RoundsFinite F.unbounded .toZero x y' :=
    rndUnbounded_satisfies_toZero F x h
  obtain ⟨hy_mem, hy_bnd, hy_sign, hy_max⟩ := hy
  obtain ⟨hy'_mem, hy'_bnd, hy'_sign, hy'_max⟩ := hy'
  have h1 : |(y' : ℝ)| ≤ |(y : ℝ)| := hy_max y' hy'_mem hy'_bnd hy'_sign
  have h2 : |(y : ℝ)| ≤ |(y' : ℝ)| := hy'_max y hy_mem hy_bnd hy_sign
  have habs : |(y : ℝ)| = |(y' : ℝ)| := le_antisymm h2 h1
  apply Subtype.ext
  rcases abs_eq_abs.mp habs with heq | hneg
  · exact heq
  · -- y = -y': combine the two `* x ≥ 0` constraints to force y'·x = 0.
    have h_prod_le : (y' : ℝ) * x + (y' : ℝ) * x ≤ 0 := by
      have h_y : (y : ℝ) * x = -((y' : ℝ) * x) := by rw [hneg]; ring
      linarith [hy_sign, hy'_sign, h_y]
    have h_prod_zero : (y' : ℝ) * x = 0 := by linarith [hy'_sign]
    rcases mul_eq_zero.mp h_prod_zero with h' | hx0
    · rw [hneg, h']; ring
    · -- x = 0: the `|y| ≤ |x|` clause directly forces y = y' = 0.
      have hy0 : (y : ℝ) = 0 := by
        have : |(y : ℝ)| ≤ 0 := by rw [hx0] at hy_bnd; simpa using hy_bnd
        exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
      have hy'0 : (y' : ℝ) = 0 := by
        have : |(y' : ℝ)| ≤ 0 := by rw [hx0] at hy'_bnd; simpa using hy'_bnd
        exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
      rw [hy0, hy'0]

theorem rndUnbounded_unique_awayZero (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .awayZero) {y : Dyadic}
    (hy : RoundsFinite F.unbounded .awayZero x y) :
    y = rndUnbounded F .awayZero x h := by
  set y' := rndUnbounded F .awayZero x h
  have hy' : RoundsFinite F.unbounded .awayZero x y' :=
    rndUnbounded_satisfies_awayZero F x h
  obtain ⟨hy_mem, hy_bnd, hy_sign, hy_min⟩ := hy
  obtain ⟨hy'_mem, hy'_bnd, hy'_sign, hy'_min⟩ := hy'
  have h1 : |(y : ℝ)| ≤ |(y' : ℝ)| := hy_min y' hy'_mem hy'_bnd hy'_sign
  have h2 : |(y' : ℝ)| ≤ |(y : ℝ)| := hy'_min y hy_mem hy_bnd hy_sign
  have habs : |(y : ℝ)| = |(y' : ℝ)| := le_antisymm h1 h2
  apply Subtype.ext
  rcases abs_eq_abs.mp habs with heq | hneg
  · exact heq
  · have h_prod_zero : (y' : ℝ) * x = 0 := by
      have h_y : (y : ℝ) * x = -((y' : ℝ) * x) := by rw [hneg]; ring
      linarith [hy_sign, hy'_sign, h_y]
    rcases mul_eq_zero.mp h_prod_zero with h' | hx0
    · rw [hneg, h']; ring
    · -- x = 0: RAZ's bound clause is vacuous; min-clause via `0 ∈ F` pins y = y' = 0.
      have h_zero_mem : (0 : Dyadic) ∈ F.unbounded := FiniteFormat.zero_mem F.unbounded
      have h_zero_bnd : |x| ≤ |((0 : Dyadic) : ℝ)| := by rw [hx0]; simp
      have h_zero_sign : ((0 : Dyadic) : ℝ) * x ≥ 0 := by simp
      have hy_le_0 : |(y : ℝ)| ≤ |((0 : Dyadic) : ℝ)| :=
        hy_min 0 h_zero_mem h_zero_bnd h_zero_sign
      have hy'_le_0 : |(y' : ℝ)| ≤ |((0 : Dyadic) : ℝ)| :=
        hy'_min 0 h_zero_mem h_zero_bnd h_zero_sign
      have hy0 : (y : ℝ) = 0 := by
        have : |(y : ℝ)| ≤ 0 := by simpa using hy_le_0
        exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
      have hy'0 : (y' : ℝ) = 0 := by
        have : |(y' : ℝ)| ≤ 0 := by simpa using hy'_le_0
        exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
      linarith

theorem rndUnbounded_unique_toOdd (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .toOdd) {y : Dyadic}
    (hy : RoundsFinite F.unbounded .toOdd x y) :
    y = rndUnbounded F .toOdd x h := by
  set y' := rndUnbounded F .toOdd x h
  have hy' : RoundsFinite F.unbounded .toOdd x y' :=
    rndUnbounded_satisfies_toOdd F x h
  obtain ⟨hy_mem, hy_faith, hy_par⟩ := hy
  obtain ⟨hy'_mem, hy'_faith, hy'_par⟩ := hy'
  apply Subtype.ext
  -- Mixed-case helper: given `y` is RoundDown, `y'` is RoundUp, show `y = y'`.
  -- This is the asymmetric case; the symmetric one is identical with `y` and
  -- `y'` swapped.
  have h_mixed_eq : ∀ {y y' : Dyadic},
      y ∈ F.unbounded → y' ∈ F.unbounded →
      (y : ℝ) ≤ x → (∀ z : Dyadic, z ∈ F.unbounded → (z : ℝ) ≤ x →
        (z : ℝ) ≤ (y : ℝ)) →
      x ≤ (y' : ℝ) → (∀ z : Dyadic, z ∈ F.unbounded → x ≤ (z : ℝ) →
        (y' : ℝ) ≤ (z : ℝ)) →
      (x ≠ (y : ℝ) → ∃ F' : ParityFormat, F'.toFormat = F.unbounded.toFormat ∧ F'.IsOdd y) →
      (x ≠ (y' : ℝ) → ∃ F' : ParityFormat, F'.toFormat = F.unbounded.toFormat ∧ F'.IsOdd y') →
      (y : ℝ) = (y' : ℝ) := by
    intro y y' hy_mem hy'_mem hy_le hy_max hy'_ge hy'_min hy_par hy'_par
    by_cases h_yx : (y : ℝ) = x
    · -- y = x: y' ≤ y by min property applied to y.
      have : (y' : ℝ) ≤ (y : ℝ) := hy'_min y hy_mem (by linarith [h_yx])
      linarith
    by_cases h_y'x : (y' : ℝ) = x
    · -- y' = x: y ≥ y' by max property applied to y'.
      have : (y' : ℝ) ≤ (y : ℝ) := hy_max y' hy'_mem (by linarith [h_y'x])
      linarith
    exfalso
    have hy_lt : (y : ℝ) < x := lt_of_le_of_ne hy_le h_yx
    have hx_lt : x < (y' : ℝ) := lt_of_le_of_ne hy'_ge (Ne.symm h_y'x)
    have h_xne_y : x ≠ (y : ℝ) := fun h_eq => h_yx h_eq.symm
    have h_xne_y' : x ≠ (y' : ℝ) := fun h_eq => h_y'x h_eq.symm
    obtain ⟨F_y, hF_y_eq, hF_y_odd⟩ := hy_par h_xne_y
    obtain ⟨F_y', hF_y'_eq, hF_y'_odd⟩ := hy'_par h_xne_y'
    set e := F.canonicalExp x with h_e_def
    set lo := ⌊x * (2 : ℝ) ^ (-e)⌋ with h_lo_def
    set dlo : Dyadic := Dyadic.ofIntZpow lo e with h_dlo_def
    set dhi : Dyadic := Dyadic.ofIntZpow (lo + 1) e with h_dhi_def
    have h_not_neg : ¬ F.IsUndefined .toNegative := fun ⟨_, _, hrm⟩ => by simp at hrm
    have h_not_pos : ¬ F.IsUndefined .toPositive := fun ⟨_, _, hrm⟩ => by simp at hrm
    -- y = dlo via uniqueness of RoundDown.
    have h_dlo_RD : RoundsFinite F.unbounded .toNegative x dlo := by
      have h_eq : rndUnbounded F .toNegative x h_not_neg = dlo := by
        unfold rndUnbounded
        rw [dif_neg (by decide : (RoundingMode.toNegative : RoundingMode) ≠ .toOdd)]
        rw [dif_neg (by decide :
          (RoundingMode.toNegative : RoundingMode) ≠ .nearest .toEven)]
        rfl
      rw [← h_eq]
      exact rndUnbounded_satisfies_toNegative F x h_not_neg
    obtain ⟨h_dlo_mem, h_dlo_le_x, h_dlo_max⟩ := h_dlo_RD
    have h_y_eq_dlo_r : (y : ℝ) = (dlo : ℝ) :=
      le_antisymm (h_dlo_max y hy_mem hy_le) (hy_max dlo h_dlo_mem h_dlo_le_x)
    -- x is strictly between dlo and dhi (not at lo · 2^e).
    have h_x_not_at_lo : x ≠ ((lo : ℝ) * (2 : ℝ) ^ e) := by
      intro hx_eq
      have h_y_eq_x : (y : ℝ) = x := by
        rw [h_y_eq_dlo_r, h_dlo_def, Dyadic.coe_ofIntZpow]
        exact hx_eq.symm
      exact h_yx h_y_eq_x
    have h_ceil_eq : ⌈x * (2 : ℝ) ^ (-e)⌉ = lo + 1 := by
      have h_floor_le : (lo : ℝ) ≤ x * (2 : ℝ) ^ (-e) := Int.floor_le _
      have h_floor_lt : (lo : ℝ) < x * (2 : ℝ) ^ (-e) := by
        rcases lt_or_eq_of_le h_floor_le with h_lt | h_eq
        · exact h_lt
        · exfalso
          apply h_x_not_at_lo
          have := mul_zpow_neg_self x e
          have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
          have hh : (lo : ℝ) * (2 : ℝ) ^ e = x := by
            calc (lo : ℝ) * (2 : ℝ) ^ e = (x * (2 : ℝ) ^ (-e)) * (2 : ℝ) ^ e := by
                  rw [← h_eq]
              _ = x := mul_zpow_neg_self x e
          linarith
      have h_lt_succ : x * (2 : ℝ) ^ (-e) < (lo : ℝ) + 1 :=
        Int.lt_floor_add_one _
      apply le_antisymm
      · exact Int.ceil_le.mpr (by push_cast; linarith)
      · have : lo < ⌈x * (2 : ℝ) ^ (-e)⌉ := by
          have h_lt_ceil := lt_of_lt_of_le h_floor_lt (Int.le_ceil _)
          exact_mod_cast h_lt_ceil
        omega
    have h_dhi_RU : RoundsFinite F.unbounded .toPositive x dhi := by
      have h_eq : rndUnbounded F .toPositive x h_not_pos = dhi := by
        unfold rndUnbounded
        rw [dif_neg (by decide : (RoundingMode.toPositive : RoundingMode) ≠ .toOdd)]
        rw [dif_neg (by decide :
          (RoundingMode.toPositive : RoundingMode) ≠ .nearest .toEven)]
        change Dyadic.ofIntZpow (rndInt .toPositive x e) e = dhi
        rw [show rndInt .toPositive x e = lo + 1 from h_ceil_eq]
      rw [← h_eq]
      exact rndUnbounded_satisfies_toPositive F x h_not_pos
    obtain ⟨h_dhi_mem, h_x_le_dhi, h_dhi_min⟩ := h_dhi_RU
    have h_y'_eq_dhi_r : (y' : ℝ) = (dhi : ℝ) :=
      le_antisymm (hy'_min dhi h_dhi_mem h_x_le_dhi)
        (h_dhi_min y' hy'_mem hy'_ge)
    have h_y_eq_dlo : y = dlo := Subtype.ext h_y_eq_dlo_r
    have h_y'_eq_dhi : y' = dhi := Subtype.ext h_y'_eq_dhi_r
    -- Transfer IsOdd via the F_y → F'' bridge.
    cases hp_F : F.p with
    | top =>
      cases hexp_F : F.exp with
      | bot =>
        exfalso
        rcases F.finite with hf | hf
        · exact hf hp_F
        · exact hf hexp_F
      | coe e'' =>
        -- F.p = ⊤, F.exp = (e'' : ℤ). Apply not_both_isOdd_fixedpoint.
        have h_e_eq : e = e'' := by
          change F.canonicalExp x = _
          unfold FiniteFormat.canonicalExp
          simp [hp_F, hexp_F]
        have h_dlo_def_e'' : dlo = Dyadic.ofIntZpow lo e'' := by
          rw [h_dlo_def, h_e_eq]
        have h_dhi_def_e'' : dhi = Dyadic.ofIntZpow (lo + 1) e'' := by
          rw [h_dhi_def, h_e_eq]
        -- F_y, F_y' both have toFormat = F.unbounded, with .p = ⊤, .exp = e''.
        have h_unb : ¬ F.unbounded.IsUndefined .toOdd := h
        set F'' := F.unbounded.toParityFormatOfToOdd h_unb with hF''_def
        have hF_y_eq_F'' : F_y.toFormat = F''.toFormat := by
          rw [hF_y_eq]; rfl
        have hF_y'_eq_F'' : F_y'.toFormat = F''.toFormat := by
          rw [hF_y'_eq]; rfl
        have h_F''_top : F''.toFormat.p = ⊤ := hp_F
        have h_F''_exp : F''.toFormat.exp = (e'' : WithBot ℤ) := hexp_F
        have h_F''_odd_dlo : F''.IsOdd dlo :=
          ((ParityFormat.IsOdd_iff_of_toFormat_eq hF_y_eq_F'' dlo).mp
            (h_y_eq_dlo ▸ hF_y_odd))
        have h_F''_odd_dhi : F''.IsOdd dhi :=
          ((ParityFormat.IsOdd_iff_of_toFormat_eq hF_y'_eq_F'' dhi).mp
            (h_y'_eq_dhi ▸ hF_y'_odd))
        rw [h_dlo_def_e''] at h_F''_odd_dlo
        rw [h_dhi_def_e''] at h_F''_odd_dhi
        exact ParityFormat.not_both_isOdd_fixedpoint h_F''_top h_F''_exp
          ⟨h_F''_odd_dlo, h_F''_odd_dhi⟩
    | coe p =>
      cases hexp_F : F.exp with
      | bot =>
        have h_unb : ¬ F.unbounded.IsUndefined .toOdd := h
        set F'' := F.unbounded.toParityFormatOfToOdd h_unb with h_F''_def
        have hF''_eq : F''.toFormat = F.unbounded.toFormat := rfl
        have hF_y_eq_F'' : F_y.toFormat = F''.toFormat := by
          rw [hF_y_eq, hF''_eq]
        have hF_y'_eq_F'' : F_y'.toFormat = F''.toFormat := by
          rw [hF_y'_eq, hF''_eq]
        have h_F''_isOdd_dlo : F''.IsOdd dlo :=
          ((ParityFormat.IsOdd_iff_of_toFormat_eq hF_y_eq_F'' dlo).mp
            (h_y_eq_dlo ▸ hF_y_odd))
        have h_F''_isOdd_dhi : F''.IsOdd dhi :=
          ((ParityFormat.IsOdd_iff_of_toFormat_eq hF_y'_eq_F'' dhi).mp
            (h_y'_eq_dhi ▸ hF_y'_odd))
        have hp_eq : F''.toFormat.p = ((p : ℕ+) : WithTop ℕ+) := hp_F
        have hexp_eq : F''.toFormat.exp = ⊥ := hexp_F
        have hp_ne_1 : F''.toFormat.p ≠ ((1 : ℕ+) : WithTop ℕ+) := by
          change F.p ≠ ((1 : ℕ+) : WithTop ℕ+)
          intro h_eq
          exact h ⟨h_eq, hexp_F, Or.inl rfl⟩
        have h_s_lt_p : |x * (2 : ℝ) ^ (-e)| < (2 : ℝ) ^ (p : ℕ) :=
          floor_mantissa_lt hp_F
        have h_lo_hi : |lo| ≤ (2 : ℤ) ^ (p : ℕ) := by
          apply abs_floor_le_of_abs_lt
          push_cast; exact h_s_lt_p
        have h_lop1_hi : |lo + 1| ≤ (2 : ℤ) ^ (p : ℕ) :=
          abs_floor_add_one_le_of_abs_lt h_s_lt_p
        -- Derive x ≠ 0 from strict y < x (impossible if x = 0 since RoundDown
        -- of 0 in F.unbounded must be 0).
        have hx_ne : x ≠ 0 := by
          intro hx0
          subst hx0
          -- y is RoundDown of 0; 0 ∈ F.unbounded so y ≥ 0. Combined with y ≤ 0:
          -- y = 0. But hy_lt : y < 0. Contradiction.
          have h_zero_mem : (0 : Dyadic) ∈ F.unbounded := FiniteFormat.zero_mem F.unbounded
          have h_zero_le_y : ((0 : Dyadic) : ℝ) ≤ (y : ℝ) :=
            hy_max 0 h_zero_mem (by simp)
          simp at h_zero_le_y
          linarith
        -- e = log|x|+1-p from canonicalExp formula (F.exp = ⊥, x ≠ 0).
        have h_e_eq_log : e = Int.log 2 |x| + 1 - (p : ℤ) := by
          change F.canonicalExp x = _
          unfold FiniteFormat.canonicalExp
          simp [hp_F, hexp_F, hx_ne]
        have h_2neg_pos : (0 : ℝ) < (2 : ℝ) ^ (-e) := zpow_pos (by norm_num) _
        have h_s_lo_real : ((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) ≤
            |x * (2 : ℝ) ^ (-e)| :=
          two_pow_pred_le_scaled (p := p) hx_ne h_e_eq_log
        have h_lo_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo| :=
          abs_floor_ge_two_pow_pred (p := p) h_s_lo_real
        have h_lop1_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo + 1| := by
          by_cases hx_nn : 0 ≤ x
          · -- x ≥ 0: lo ≥ 2^(p-1) ⟹ lo+1 ≥ 2^(p-1) + 1.
            have h_lo_nn : 0 ≤ lo := by
              have h_s_ge_r : ((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) ≤ x * (2 : ℝ) ^ (-e) := by
                have hs_nn : 0 ≤ x * (2 : ℝ) ^ (-e) :=
                  mul_nonneg hx_nn h_2neg_pos.le
                have h_abs_eq : |x * (2 : ℝ) ^ (-e)| = x * (2 : ℝ) ^ (-e) :=
                  abs_of_nonneg hs_nn
                linarith [h_s_lo_real]
              exact Int.floor_nonneg.mpr (le_trans (by positivity) h_s_ge_r)
            rw [abs_of_nonneg (by linarith : (0 : ℤ) ≤ lo + 1)]
            have h_lo_ge : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ lo := by
              rw [← abs_of_nonneg h_lo_nn]; exact h_lo_lo
            linarith
          · -- x < 0: strict case gives lo < x · 2^(-e) ≤ -2^(p-1),
            -- so lo ≤ -2^(p-1) - 1 ⟹ lo+1 ≤ -2^(p-1).
            push Not at hx_nn
            have hs_neg : x * (2 : ℝ) ^ (-e) < 0 :=
              mul_neg_of_neg_of_pos hx_nn h_2neg_pos
            -- Use h_floor_lt from earlier: lo < x · 2^(-e) (strict from non-exact).
            -- Wait we need h_floor_lt. It was inside the ceil_eq proof. Let me re-derive.
            have h_floor_lt : (lo : ℝ) < x * (2 : ℝ) ^ (-e) := by
              -- From y < x and y = dlo = lo · 2^e:
              have h_y_real : (y : ℝ) = (lo : ℝ) * (2 : ℝ) ^ e := by
                rw [h_y_eq_dlo_r, h_dlo_def, Dyadic.coe_ofIntZpow]
              have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
              have h_lo_e_lt_x : (lo : ℝ) * (2 : ℝ) ^ e < x := by linarith [hy_lt, h_y_real]
              have := mul_lt_mul_of_pos_right h_lo_e_lt_x h_2neg_pos
              rw [show (lo : ℝ) * (2 : ℝ) ^ e * (2 : ℝ) ^ (-e) = (lo : ℝ) by
                rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
                    add_neg_cancel, zpow_zero, mul_one]] at this
              exact this
            have h_s_le_r : x * (2 : ℝ) ^ (-e) ≤ -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) := by
              have h_abs_eq : |x * (2 : ℝ) ^ (-e)| = -(x * (2 : ℝ) ^ (-e)) :=
                abs_of_neg hs_neg
              linarith [h_s_lo_real]
            have h_lo_lt_neg : (lo : ℝ) < -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) :=
              lt_of_lt_of_le h_floor_lt h_s_le_r
            have h_lo_lt_int : lo < -((2 : ℤ) ^ ((p : ℕ) - 1)) := by
              exact_mod_cast h_lo_lt_neg
            have h_lop1_le : lo + 1 ≤ -((2 : ℤ) ^ ((p : ℕ) - 1)) := by linarith
            have h_lop1_neg : lo + 1 < 0 := by
              have : (0 : ℤ) < (2 : ℤ) ^ ((p : ℕ) - 1) := by positivity
              linarith
            rw [abs_of_neg h_lop1_neg]; linarith
        -- Apply not_both_isOdd_floating.
        exact ParityFormat.not_both_isOdd_floating hp_eq hp_ne_1 hexp_eq
          h_lo_lo h_lo_hi h_lop1_lo h_lop1_hi ⟨h_F''_isOdd_dlo, h_F''_isOdd_dhi⟩
      | coe e'' =>
        -- F.p = (p : ℕ+), F.exp = (e'' : ℤ). Mixed case.
        have h_unb : ¬ F.unbounded.IsUndefined .toOdd := h
        set F'' := F.unbounded.toParityFormatOfToOdd h_unb with hF''_def
        have hF''_eq : F''.toFormat = F.unbounded.toFormat := rfl
        have hF_y_eq_F'' : F_y.toFormat = F''.toFormat := by rw [hF_y_eq, hF''_eq]
        have hF_y'_eq_F'' : F_y'.toFormat = F''.toFormat := by rw [hF_y'_eq, hF''_eq]
        have h_F''_isOdd_dlo : F''.IsOdd dlo :=
          ((ParityFormat.IsOdd_iff_of_toFormat_eq hF_y_eq_F'' dlo).mp
            (h_y_eq_dlo ▸ hF_y_odd))
        have h_F''_isOdd_dhi : F''.IsOdd dhi :=
          ((ParityFormat.IsOdd_iff_of_toFormat_eq hF_y'_eq_F'' dhi).mp
            (h_y'_eq_dhi ▸ hF_y'_odd))
        have hp_eq : F''.toFormat.p = ((p : ℕ+) : WithTop ℕ+) := hp_F
        have hexp_eq : F''.toFormat.exp = (e'' : WithBot ℤ) := hexp_F
        by_cases hp_eq_1 : p = (1 : ℕ+)
        · -- p = 1: exponent-index parity branch.
          subst hp_eq_1
          have hp_eq_1' : F''.toFormat.p = ((1 : ℕ+) : WithTop ℕ+) := hp_F
          have hexp_eq_1 : F''.toFormat.exp = (e'' : WithBot ℤ) := hexp_F
          have hx_ne : x ≠ 0 := by
            intro hx0
            subst hx0
            have h_zero_mem : (0 : Dyadic) ∈ F.unbounded :=
              FiniteFormat.zero_mem F.unbounded
            have h_zero_le_y : ((0 : Dyadic) : ℝ) ≤ (y : ℝ) :=
              hy_max 0 h_zero_mem (by simp)
            simp at h_zero_le_y
            linarith
          have h_e_ge : e'' ≤ e := F.exp_le_canonicalExp x hexp_F
          have h_s_lt : |x * (2 : ℝ) ^ (-e)| < (2 : ℝ) ^ ((1 : ℕ+) : ℕ) :=
            floor_mantissa_lt hp_F
          have h_s_lt_2 : |x * (2 : ℝ) ^ (-e)| < ((2 : ℤ) : ℝ) := by
            have h_cast : ((2 : ℤ) : ℝ) = (2 : ℝ) ^ ((1 : ℕ+) : ℕ) := by
              change (2 : ℝ) = (2 : ℝ) ^ (1 : ℕ); ring
            rw [h_cast]; exact h_s_lt
          have h_lo_hi_int : |lo| ≤ 2 := abs_floor_le_of_abs_lt h_s_lt_2
          have h_lop1_hi_int : |lo + 1| ≤ 2 :=
            abs_floor_add_one_le_of_abs_lt (p := 1) h_s_lt
          have h_dlo_at : dlo = Dyadic.ofIntZpow lo e := h_dlo_def
          have h_dhi_at : dhi = Dyadic.ofIntZpow (lo + 1) e := h_dhi_def
          by_cases h_regime : Int.log 2 |x| + 1 - ((1 : ℕ+) : ℤ) ≤ e''
          · -- Subnormal: e = e''.
            have h_e_eq : e = e'' := by
              change F.canonicalExp x = e''
              unfold FiniteFormat.canonicalExp
              simp only [hp_F, hexp_F]
              rw [if_neg hx_ne]
              exact max_eq_right h_regime
            rw [h_dlo_at, h_e_eq] at h_F''_isOdd_dlo
            rw [h_dhi_at, h_e_eq] at h_F''_isOdd_dhi
            exact ParityFormat.not_both_isOdd_mixed_subnormal_p1
              hp_eq_1' hexp_eq_1 h_lo_hi_int h_lop1_hi_int
              ⟨h_F''_isOdd_dlo, h_F''_isOdd_dhi⟩
          · -- Normal: e = log|x|. Need |lo|, |lo+1| ≥ 1.
            push Not at h_regime
            have h_pcast : ((1 : ℕ+) : ℤ) = 1 := rfl
            have h_e_eq_log : e = Int.log 2 |x| := by
              change F.canonicalExp x = _
              unfold FiniteFormat.canonicalExp
              simp only [hp_F, hexp_F]
              rw [if_neg hx_ne]
              rw [show (((1 : ℕ+) : ℕ) : ℤ) = 1 from rfl]
              have h_max_eq : max (Int.log 2 |x| + 1 - 1) e'' =
                  Int.log 2 |x| + 1 - 1 := by
                apply max_eq_left
                have := h_regime; rw [h_pcast] at this; linarith
              rw [h_max_eq]; ring
            have h_x_ge : (2 : ℝ) ^ (Int.log 2 |x|) ≤ |x| :=
              Int.zpow_log_le_self (b := 2) (by norm_num : (1 : ℕ) < 2)
                (abs_pos.mpr hx_ne)
            have h_2neg_pos : (0 : ℝ) < (2 : ℝ) ^ (-e) :=
              zpow_pos (by norm_num) _
            have h_abs_s : 1 ≤ |x * (2 : ℝ) ^ (-e)| := by
              have h_abs_eq : |x * (2 : ℝ) ^ (-e)| = |x| * (2 : ℝ) ^ (-e) := by
                rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)]
              rw [h_abs_eq, h_e_eq_log]
              have h_pow_eq : (2 : ℝ) ^ (Int.log 2 |x|) *
                  (2 : ℝ) ^ (-Int.log 2 |x|) = 1 := by
                rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
                    add_neg_cancel, zpow_zero]
              have h_le := mul_le_mul_of_nonneg_right h_x_ge
                (zpow_pos (by norm_num : (0 : ℝ) < 2) (-Int.log 2 |x|)).le
              rw [h_pow_eq] at h_le
              exact h_le
            have h_lo_lo_int : 1 ≤ |lo| := by
              by_cases hs_nn : 0 ≤ x * (2 : ℝ) ^ (-e)
              · have h_s_ge : 1 ≤ x * (2 : ℝ) ^ (-e) := by
                  have h_abs_eq : |x * (2 : ℝ) ^ (-e)| = x * (2 : ℝ) ^ (-e) :=
                    abs_of_nonneg hs_nn
                  linarith [h_abs_s]
                have h_lo_ge_1 : 1 ≤ lo := by
                  apply Int.le_floor.mpr; push_cast; exact h_s_ge
                rw [abs_of_nonneg (by linarith : (0 : ℤ) ≤ lo)]; exact h_lo_ge_1
              · push Not at hs_nn
                have h_s_le : x * (2 : ℝ) ^ (-e) ≤ -1 := by
                  have h_abs_eq : |x * (2 : ℝ) ^ (-e)| =
                      -(x * (2 : ℝ) ^ (-e)) := abs_of_neg hs_nn
                  linarith [h_abs_s]
                have h_floor_le : (lo : ℝ) ≤ x * (2 : ℝ) ^ (-e) :=
                  Int.floor_le _
                have h_lo_le : (lo : ℝ) ≤ -1 := le_trans h_floor_le h_s_le
                have h_lo_le_int : lo ≤ -1 := by exact_mod_cast h_lo_le
                rw [abs_of_neg (by linarith : lo < 0)]; linarith
            -- lo ≠ -1 (in unique, via h_y_eq_dlo_r and hy_lt to exclude).
            have h_lo_ne_neg1 : lo ≠ -1 := by
              intro h_eq
              set s := x * (2 : ℝ) ^ (-e)
              have h_lo_int : ⌊s⌋ = -1 := h_eq
              have h_floor_le : (-1 : ℝ) ≤ s := by
                have h_fl := Int.floor_le s
                rw [h_lo_int] at h_fl; push_cast at h_fl; exact h_fl
              have h_lt_succ : s < 0 := by
                have h_lt := Int.lt_floor_add_one s
                rw [h_lo_int] at h_lt; push_cast at h_lt; linarith
              have h_s_le_neg1 : s ≤ -1 := by
                have h_abs_eq : |s| = -s := abs_of_neg (by linarith : s < 0)
                have h_abs_ge : 1 ≤ |s| := h_abs_s
                linarith
              have h_s_eq : s = -1 := le_antisymm h_s_le_neg1 h_floor_le
              have h_x_eq : x = (-1 : ℝ) * (2 : ℝ) ^ e := by
                have h_s_eq' : x * (2 : ℝ) ^ (-e) = -1 := h_s_eq
                have h_mul_inv : (2 : ℝ) ^ (-e) * (2 : ℝ) ^ e = 1 := by
                  rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
                  rw [neg_add_cancel, zpow_zero]
                calc x = x * 1 := by ring
                  _ = x * ((2 : ℝ) ^ (-e) * (2 : ℝ) ^ e) := by rw [h_mul_inv]
                  _ = (x * (2 : ℝ) ^ (-e)) * (2 : ℝ) ^ e := by ring
                  _ = (-1 : ℝ) * (2 : ℝ) ^ e := by rw [h_s_eq']
              have h_y_real : (y : ℝ) = (lo : ℝ) * (2 : ℝ) ^ e := by
                rw [h_y_eq_dlo_r, h_dlo_def, Dyadic.coe_ofIntZpow]
              rw [h_eq] at h_y_real
              push_cast at h_y_real
              have h_yx_eq : (y : ℝ) = x := by rw [h_y_real, h_x_eq]
              linarith [hy_lt]
            have h_lop1_lo_int : 1 ≤ |lo + 1| := by
              have h_lop1_ne : lo + 1 ≠ 0 := by
                intro h0; apply h_lo_ne_neg1; omega
              exact Int.one_le_abs h_lop1_ne
            rw [h_dlo_at] at h_F''_isOdd_dlo
            rw [h_dhi_at] at h_F''_isOdd_dhi
            exact ParityFormat.not_both_isOdd_mixed_normal_p1
              hp_eq_1' hexp_eq_1 h_e_ge h_lo_lo_int h_lo_hi_int
              h_lop1_lo_int h_lop1_hi_int
              ⟨h_F''_isOdd_dlo, h_F''_isOdd_dhi⟩
        · have hp_ne_1 : F''.toFormat.p ≠ ((1 : ℕ+) : WithTop ℕ+) := by
            change F.p ≠ _
            rw [hp_F]
            intro h_eq
            apply hp_eq_1
            exact_mod_cast h_eq
          -- Derive x ≠ 0.
          have hx_ne : x ≠ 0 := by
            intro hx0
            subst hx0
            have h_zero_mem : (0 : Dyadic) ∈ F.unbounded := FiniteFormat.zero_mem F.unbounded
            have h_zero_le_y : ((0 : Dyadic) : ℝ) ≤ (y : ℝ) :=
              hy_max 0 h_zero_mem (by simp)
            simp at h_zero_le_y
            linarith
          by_cases h_regime : Int.log 2 |x| + 1 - ((p : ℕ+) : ℤ) ≤ e''
          · -- Subnormal: e = e''.
            have h_e_eq : e = e'' := by
              change F.canonicalExp x = e''
              unfold FiniteFormat.canonicalExp
              simp only [hp_F, hexp_F]
              rw [if_neg hx_ne]
              exact max_eq_right h_regime
            -- |x| < 2^(e'' + p) from h_regime.
            have h_x_lt : |x| < (2 : ℝ) ^ (e'' + (p : ℤ)) := by
              have h_log_le : Int.log 2 |x| ≤ e'' + (p : ℤ) - 1 := by
                have h_pcast : ((p : ℕ+) : ℤ) = (p : ℤ) := rfl
                linarith
              have h_lt := Int.lt_zpow_succ_log_self
                (by norm_num : (1 : ℕ) < 2) |x|
              have : Int.log 2 |x| + 1 ≤ e'' + (p : ℤ) := by linarith
              exact lt_of_lt_of_le h_lt
                (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) this)
            have h_s_lt : |x * (2 : ℝ) ^ (-e)| < (2 : ℝ) ^ ((p : ℕ+) : ℕ) := by
              rw [h_e_eq]
              have h_abs : |x * (2 : ℝ) ^ (-e'')| = |x| * (2 : ℝ) ^ (-e'') := by
                rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)]
              rw [h_abs]
              have h_2neg_pos : (0 : ℝ) < (2 : ℝ) ^ (-e'') := zpow_pos (by norm_num) _
              have h_eq_split : (2 : ℝ) ^ (e'' + (p : ℤ)) =
                  (2 : ℝ) ^ e'' * (2 : ℝ) ^ ((p : ℕ+) : ℕ) := by
                rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
                have h_pcast : ((p : ℕ+) : ℤ) = (((p : ℕ+) : ℕ) : ℤ) := rfl
                rw [h_pcast, zpow_natCast]
              have h_x2neg : |x| * (2 : ℝ) ^ (-e'') <
                  (2 : ℝ) ^ (e'' + (p : ℤ)) * (2 : ℝ) ^ (-e'') :=
                mul_lt_mul_of_pos_right h_x_lt h_2neg_pos
              rw [h_eq_split] at h_x2neg
              have h_cancel : (2 : ℝ) ^ e'' * (2 : ℝ) ^ ((p : ℕ+) : ℕ) *
                  (2 : ℝ) ^ (-e'') = (2 : ℝ) ^ ((p : ℕ+) : ℕ) := by
                rw [mul_right_comm, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
                    add_neg_cancel, zpow_zero, one_mul]
              rw [h_cancel] at h_x2neg
              exact h_x2neg
            have h_lo_le : |lo| ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by
              apply abs_floor_le_of_abs_lt
              push_cast; exact h_s_lt
            have h_lop1_le : |lo + 1| ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) :=
              abs_floor_add_one_le_of_abs_lt h_s_lt
            -- Helper: |k| ≤ 2^p ⟹ log|k| + 1 ≤ p (when |k| < 2^p strict — saturation
            -- excluded for h_F''_isOdd_* by separate argument).
            -- Apply not_both_isOdd_mixed_subnormal_pne1 after establishing log bounds.
            -- Handle saturation by showing IsOdd doesn't hold.
            have h_dlo_at_e'' : dlo = Dyadic.ofIntZpow lo e'' := by
              rw [h_dlo_def, h_e_eq]
            have h_dhi_at_e'' : dhi = Dyadic.ofIntZpow (lo + 1) e'' := by
              rw [h_dhi_def, h_e_eq]
            -- Case-split on |lo| vs |lo+1| saturation.
            rcases lt_or_eq_of_le h_lo_le with h_lo_lt | h_lo_sat
            · rcases lt_or_eq_of_le h_lop1_le with h_lop1_lt | h_lop1_sat
              · -- Both non-saturated. Apply not_both_isOdd_mixed_subnormal_pne1.
                have h_log_lo := log_lt_p_of_abs_lt_two_pow h_lo_lt
                have h_log_lop1_raw := log_lt_p_of_abs_lt_two_pow h_lop1_lt
                have h_log_lop1 : Int.log 2 |((lo : ℝ) + 1)| + 1 ≤
                    (((p : ℕ+) : ℕ) : ℤ) := by
                  have h_eq : |((lo : ℝ) + 1)| = |((lo + 1 : ℤ) : ℝ)| := by
                    push_cast; rfl
                  rw [h_eq]; exact h_log_lop1_raw
                rw [h_dlo_at_e''] at h_F''_isOdd_dlo
                rw [h_dhi_at_e''] at h_F''_isOdd_dhi
                exact ParityFormat.not_both_isOdd_mixed_subnormal_pne1
                  hp_eq hp_ne_1 hexp_eq h_log_lo h_log_lop1
                  ⟨h_F''_isOdd_dlo, h_F''_isOdd_dhi⟩
              · -- |lo+1| saturation: |lo+1| = 2^p. F''.IsOdd dhi fails.
                rw [h_dhi_at_e''] at h_F''_isOdd_dhi
                have h_dhi_real_e'' : (Dyadic.ofIntZpow (lo + 1) e'' : ℝ) =
                    ((lo + 1 : ℤ) : ℝ) * (2 : ℝ) ^ e'' := Dyadic.coe_ofIntZpow _ _
                have h_lop1_ne : lo + 1 ≠ 0 := by
                  intro h_zero
                  rw [h_zero] at h_lop1_sat
                  simp at h_lop1_sat
                  have : (0 : ℤ) < (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by positivity
                  omega
                have h_dhi_ne : (Dyadic.ofIntZpow (lo + 1) e'' : ℝ) ≠ 0 := by
                  rw [h_dhi_real_e'']
                  exact mul_ne_zero (Int.cast_ne_zero.mpr h_lop1_ne)
                    (ne_of_gt (zpow_pos (by norm_num) _))
                have h_log_2p : Int.log 2 (|lo + 1| : ℝ) = (((p : ℕ+) : ℕ) : ℤ) := by
                  have h_bridge : (|lo + 1| : ℝ) = ((|lo + 1| : ℤ) : ℝ) := by
                    push_cast; rfl
                  rw [h_bridge, h_lop1_sat]
                  have h_cast : (((2 : ℤ) ^ ((p : ℕ+) : ℕ) : ℤ) : ℝ) =
                      (2 : ℝ) ^ (((p : ℕ+) : ℕ) : ℤ) := by
                    rw [zpow_natCast]; push_cast; rfl
                  rw [h_cast]
                  exact Int.log_zpow (by norm_num : 1 < 2) _
                have h_log_dhi : Int.log 2 |(Dyadic.ofIntZpow (lo + 1) e'' : ℝ)| =
                    (((p : ℕ+) : ℕ) : ℤ) + e'' := by
                  rw [h_dhi_real_e'']
                  rw [ParityFormat.log_abs_mul_zpow h_lop1_ne e'']
                  have h_cast_eq : |((lo + 1 : ℤ) : ℝ)| = (|lo + 1| : ℝ) := by
                    push_cast; rfl
                  rw [h_cast_eq, h_log_2p]
                have h_log_y_ge : (((p : ℕ+) : ℕ) : ℤ) ≤
                    Int.log 2 |(Dyadic.ofIntZpow (lo + 1) e'' : ℝ)| - e'' + 1 := by
                  rw [h_log_dhi]; linarith
                exact (ParityFormat.not_isOdd_at_saturation_mixed_normal hp_eq
                  hp_ne_1 hexp_eq h_dhi_ne h_log_y_ge h_dhi_real_e'' h_lop1_sat)
                  h_F''_isOdd_dhi
            · -- |lo| saturation: |lo| = 2^p. F''.IsOdd dlo fails.
              rw [h_dlo_at_e''] at h_F''_isOdd_dlo
              have h_dlo_real_e'' : (Dyadic.ofIntZpow lo e'' : ℝ) =
                  (lo : ℝ) * (2 : ℝ) ^ e'' := Dyadic.coe_ofIntZpow _ _
              have h_lo_ne : lo ≠ 0 := by
                intro h_zero
                rw [h_zero] at h_lo_sat
                simp at h_lo_sat
                have : (0 : ℤ) < (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by positivity
                omega
              have h_dlo_ne : (Dyadic.ofIntZpow lo e'' : ℝ) ≠ 0 := by
                rw [h_dlo_real_e'']
                exact mul_ne_zero (Int.cast_ne_zero.mpr h_lo_ne)
                  (ne_of_gt (zpow_pos (by norm_num) _))
              have h_log_2p : Int.log 2 (|lo| : ℝ) = (((p : ℕ+) : ℕ) : ℤ) := by
                have h_bridge : (|lo| : ℝ) = ((|lo| : ℤ) : ℝ) := by
                  push_cast; rfl
                rw [h_bridge, h_lo_sat]
                have h_cast : (((2 : ℤ) ^ ((p : ℕ+) : ℕ) : ℤ) : ℝ) =
                    (2 : ℝ) ^ (((p : ℕ+) : ℕ) : ℤ) := by
                  rw [zpow_natCast]; push_cast; rfl
                rw [h_cast]
                exact Int.log_zpow (by norm_num : 1 < 2) _
              have h_log_dlo : Int.log 2 |(Dyadic.ofIntZpow lo e'' : ℝ)| =
                  (((p : ℕ+) : ℕ) : ℤ) + e'' := by
                rw [h_dlo_real_e'']
                rw [ParityFormat.log_abs_mul_zpow h_lo_ne e'']
                have h_cast_eq : |(lo : ℝ)| = (|lo| : ℝ) := by rfl
                rw [h_cast_eq, h_log_2p]
              have h_log_y_ge : (((p : ℕ+) : ℕ) : ℤ) ≤
                  Int.log 2 |(Dyadic.ofIntZpow lo e'' : ℝ)| - e'' + 1 := by
                rw [h_log_dlo]; linarith
              exact (ParityFormat.not_isOdd_at_saturation_mixed_normal hp_eq
                hp_ne_1 hexp_eq h_dlo_ne h_log_y_ge h_dlo_real_e'' h_lo_sat)
                h_F''_isOdd_dlo
          · -- Normal regime: e = log|x|+1-p.
            push Not at h_regime
            have h_dlo_real : (dlo : ℝ) = (lo : ℝ) * (2 : ℝ) ^ e :=
              Dyadic.coe_ofIntZpow _ _
            have h_dhi_real : (dhi : ℝ) = ((lo + 1 : ℤ) : ℝ) * (2 : ℝ) ^ e :=
              Dyadic.coe_ofIntZpow _ _
            have h_e_eq_log : e = Int.log 2 |x| + 1 - ((p : ℕ+) : ℤ) := by
              change F.canonicalExp x = _
              unfold FiniteFormat.canonicalExp
              simp only [hp_F, hexp_F]
              rw [if_neg hx_ne]
              exact max_eq_left (le_of_lt h_regime)
            have h_2neg_pos : (0 : ℝ) < (2 : ℝ) ^ (-e) := zpow_pos (by norm_num) _
            have h_s_lo_real : ((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) ≤
                |x * (2 : ℝ) ^ (-e)| :=
              two_pow_pred_le_scaled (p := p) hx_ne h_e_eq_log
            have h_lo_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo| :=
              abs_floor_ge_two_pow_pred (p := p) h_s_lo_real
            -- Derive lo+1 lower bound. Use h_floor_lt from y < x.
            have h_lop1_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo + 1| := by
              by_cases hx_nn : 0 ≤ x
              · have h_lo_nn : 0 ≤ lo := by
                  have h_s_ge_r : ((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) ≤ x * (2 : ℝ) ^ (-e) := by
                    have hs_nn : 0 ≤ x * (2 : ℝ) ^ (-e) :=
                      mul_nonneg hx_nn h_2neg_pos.le
                    have h_abs_eq : |x * (2 : ℝ) ^ (-e)| = x * (2 : ℝ) ^ (-e) :=
                      abs_of_nonneg hs_nn
                    linarith [h_s_lo_real]
                  exact Int.floor_nonneg.mpr (le_trans (by positivity) h_s_ge_r)
                rw [abs_of_nonneg (by linarith : (0 : ℤ) ≤ lo + 1)]
                have h_lo_ge : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ lo := by
                  rw [← abs_of_nonneg h_lo_nn]; exact h_lo_lo
                linarith
              · push Not at hx_nn
                have hs_neg : x * (2 : ℝ) ^ (-e) < 0 :=
                  mul_neg_of_neg_of_pos hx_nn h_2neg_pos
                have h_floor_lt : (lo : ℝ) < x * (2 : ℝ) ^ (-e) := by
                  have h_y_real : (y : ℝ) = (lo : ℝ) * (2 : ℝ) ^ e := by
                    rw [h_y_eq_dlo_r, h_dlo_def, Dyadic.coe_ofIntZpow]
                  have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
                  have h_lo_e_lt_x : (lo : ℝ) * (2 : ℝ) ^ e < x := by
                    linarith [hy_lt, h_y_real]
                  have := mul_lt_mul_of_pos_right h_lo_e_lt_x h_2neg_pos
                  rw [show (lo : ℝ) * (2 : ℝ) ^ e * (2 : ℝ) ^ (-e) = (lo : ℝ) by
                    rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
                        add_neg_cancel, zpow_zero, mul_one]] at this
                  exact this
                have h_s_le_r : x * (2 : ℝ) ^ (-e) ≤ -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) := by
                  have h_abs_eq : |x * (2 : ℝ) ^ (-e)| = -(x * (2 : ℝ) ^ (-e)) :=
                    abs_of_neg hs_neg
                  linarith [h_s_lo_real]
                have h_lo_lt_neg : (lo : ℝ) < -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) :=
                  lt_of_lt_of_le h_floor_lt h_s_le_r
                have h_lo_lt_int : lo < -((2 : ℤ) ^ ((p : ℕ) - 1)) := by
                  exact_mod_cast h_lo_lt_neg
                have h_lop1_le : lo + 1 ≤ -((2 : ℤ) ^ ((p : ℕ) - 1)) := by linarith
                have h_lop1_neg : lo + 1 < 0 := by
                  have : (0 : ℤ) < (2 : ℤ) ^ ((p : ℕ) - 1) := by positivity
                  linarith
                rw [abs_of_neg h_lop1_neg]; linarith
            -- |lo|, |lo+1| ≤ 2^p (via h_s_lt_p analog).
            have h_s_lt_p : |x * (2 : ℝ) ^ (-e)| < (2 : ℝ) ^ ((p : ℕ+) : ℕ) :=
              floor_mantissa_lt hp_F
            have h_lo_hi : |lo| ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by
              apply abs_floor_le_of_abs_lt
              push_cast; exact h_s_lt_p
            have h_lop1_hi : |lo + 1| ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) :=
              abs_floor_add_one_le_of_abs_lt h_s_lt_p
            -- Derive log bounds and apply not_both_isOdd_mixed_normal_pne1.
            have h_lo_ne : lo ≠ 0 := by
              intro h_lo_zero
              rw [h_lo_zero] at h_lo_lo
              simp at h_lo_lo
              have : (0 : ℤ) < (2 : ℤ) ^ ((p : ℕ) - 1) := by positivity
              omega
            have h_lop1_ne : lo + 1 ≠ 0 := by
              intro h_lop1_zero
              rw [h_lop1_zero] at h_lop1_lo
              simp at h_lop1_lo
              have : (0 : ℤ) < (2 : ℤ) ^ ((p : ℕ) - 1) := by positivity
              omega
            have h_dlo_ne : (dlo : ℝ) ≠ 0 := by
              rw [h_dlo_real]
              exact mul_ne_zero (Int.cast_ne_zero.mpr h_lo_ne)
                (ne_of_gt (zpow_pos (by norm_num) _))
            have h_dhi_ne : (dhi : ℝ) ≠ 0 := by
              rw [h_dhi_real]
              exact mul_ne_zero (Int.cast_ne_zero.mpr h_lop1_ne)
                (ne_of_gt (zpow_pos (by norm_num) _))
            have h_log_dlo : Int.log 2 |(dlo : ℝ)| =
                Int.log 2 |(lo : ℝ)| + e := by
              rw [h_dlo_real]
              exact ParityFormat.log_abs_mul_zpow h_lo_ne e
            have h_log_dhi : Int.log 2 |(dhi : ℝ)| =
                Int.log 2 |((lo + 1 : ℤ) : ℝ)| + e := by
              rw [h_dhi_real]
              exact ParityFormat.log_abs_mul_zpow h_lop1_ne e
            have h_log_2pow_nat := log_two_pow_nat
            have h_log_lo_lb := log_ge_p_pred_of_two_pow_pred_le (k := lo) h_lo_lo
            have h_log_lop1_lb := log_ge_p_pred_of_two_pow_pred_le (k := lo + 1) h_lop1_lo
            have h_log_lo : ((p : ℕ) : ℤ) ≤ Int.log 2 |(dlo : ℝ)| - e'' + 1 := by
              rw [h_log_dlo, h_e_eq_log]
              have : Int.log 2 |x| - e'' ≥ ((p : ℕ) : ℤ) := by linarith
              linarith [h_log_lo_lb]
            have h_log_hi : ((p : ℕ) : ℤ) ≤ Int.log 2 |(dhi : ℝ)| - e'' + 1 := by
              rw [h_log_dhi, h_e_eq_log]
              have : Int.log 2 |x| - e'' ≥ ((p : ℕ) : ℤ) := by linarith
              linarith [h_log_lop1_lb]
            -- Apply not_both_isOdd_mixed_normal_pne1.
            exact ParityFormat.not_both_isOdd_mixed_normal_pne1
              hp_eq hp_ne_1 hexp_eq h_dlo_ne h_dhi_ne h_log_lo h_log_hi
              h_dlo_real h_dhi_real h_lo_lo h_lo_hi h_lop1_lo h_lop1_hi
              ⟨h_F''_isOdd_dlo, h_F''_isOdd_dhi⟩
  rcases hy_faith with ⟨_, hy_le, hy_max⟩ | ⟨_, hy_ge, hy_min⟩
  · rcases hy'_faith with ⟨_, hy'_le, hy'_max⟩ | ⟨_, hy'_ge, hy'_min⟩
    · -- Both RoundDown.
      exact le_antisymm (hy'_max y hy_mem hy_le) (hy_max y' hy'_mem hy'_le)
    · exact h_mixed_eq hy_mem hy'_mem hy_le hy_max hy'_ge hy'_min hy_par hy'_par
  · rcases hy'_faith with ⟨_, hy'_le, hy'_max⟩ | ⟨_, hy'_ge, hy'_min⟩
    · -- Mixed (y RoundUp, y' RoundDown): apply helper with swap.
      exact (h_mixed_eq hy'_mem hy_mem hy'_le hy'_max hy_ge hy_min hy'_par hy_par).symm
    · -- Both RoundUp.
      exact le_antisymm (hy_min y' hy'_mem hy'_ge) (hy'_min y hy_mem hy_ge)

theorem rndUnbounded_unique_nearest (F : FiniteFormat) (tb : TieBreak) (x : ℝ)
    (h : ¬ F.IsUndefined (.nearest tb)) {y : Dyadic}
    (hy : RoundsFinite F.unbounded (.nearest tb) x y) :
    y = rndUnbounded F (.nearest tb) x h := by
  set y' := rndUnbounded F (.nearest tb) x h with hy'_def
  have hy' : RoundsFinite F.unbounded (.nearest tb) x y' :=
    rndUnbounded_satisfies_nearest F tb x h
  -- Both y, y' satisfy the same spec. They're equidistant, and the tie-break
  -- uniquely determines them.
  cases tb with
  | awayZero =>
    obtain ⟨hy_mem, hy_faith, hy_min, hy_tie⟩ := hy
    obtain ⟨hy'_mem, hy'_faith, hy'_min, hy'_tie⟩ := hy'
    have h_dist_eq : |x - (y : ℝ)| = |x - (y' : ℝ)| :=
      le_antisymm (hy_min y' hy'_mem hy'_faith) (hy'_min y hy_mem hy_faith)
    by_cases h_yy : y = y'
    · exact h_yy
    · apply Subtype.ext
      have h_y_le_y' : |(y : ℝ)| ≤ |(y' : ℝ)| :=
        hy'_tie y hy_mem hy_faith h_yy h_dist_eq.symm
      have h_y'_le_y : |(y' : ℝ)| ≤ |(y : ℝ)| :=
        hy_tie y' hy'_mem hy'_faith (Ne.symm h_yy) h_dist_eq
      -- |y| = |y'| and dist eq give y² = y'² and 2x(y - y') = 0. y ≠ y' ⟹ x = 0.
      have h_abs_eq : |(y : ℝ)| = |(y' : ℝ)| := le_antisymm h_y_le_y' h_y'_le_y
      have h_sq : (y : ℝ) ^ 2 = (y' : ℝ) ^ 2 := by
        have h1 : |(y : ℝ)| ^ 2 = |(y' : ℝ)| ^ 2 := by rw [h_abs_eq]
        rw [sq_abs, sq_abs] at h1
        exact h1
      have h_x_zero : x = 0 := by
        have h_dist_sq : (x - (y : ℝ)) ^ 2 = (x - (y' : ℝ)) ^ 2 := by
          have h1 : |x - (y : ℝ)| ^ 2 = |x - (y' : ℝ)| ^ 2 := by rw [h_dist_eq]
          rw [sq_abs, sq_abs] at h1
          exact h1
        have h_expand : 2 * x * ((y : ℝ) - (y' : ℝ)) = 0 := by
          have : (x - (y : ℝ)) ^ 2 - (x - (y' : ℝ)) ^ 2 = 0 := by linarith
          have : 2 * x * ((y' : ℝ) - (y : ℝ)) + ((y : ℝ)^2 - (y' : ℝ)^2) = 0 := by
            ring_nf; ring_nf at this; linarith
          linarith [h_sq]
        have h_y_ne_y' : (y : ℝ) ≠ (y' : ℝ) := fun heq =>
          h_yy (Subtype.ext heq)
        have h_diff_ne : (y : ℝ) - (y' : ℝ) ≠ 0 := sub_ne_zero.mpr h_y_ne_y'
        have h_2x : 2 * x = 0 := by
          by_contra h2x
          have : 2 * x * ((y : ℝ) - (y' : ℝ)) ≠ 0 := mul_ne_zero h2x h_diff_ne
          exact this h_expand
        linarith
      -- At x = 0, faithful round of 0 must be 0 (since 0 ∈ F). So y = y' = 0.
      have h_zero_mem : (0 : Dyadic) ∈ F.unbounded := FiniteFormat.zero_mem F.unbounded
      have h_y_eq_zero : (y : ℝ) = 0 := by
        rcases hy_faith with ⟨_, hy_le, hy_max⟩ | ⟨_, hy_ge, hy_min'⟩
        · -- y ≤ x = 0 and 0 ∈ F means y is max F-elt ≤ 0, hence y = 0.
          rw [h_x_zero] at hy_le
          have h_zero_le_y : ((0 : Dyadic) : ℝ) ≤ (y : ℝ) := by
            have := hy_max 0 h_zero_mem (by rw [h_x_zero]; simp)
            simpa using this
          simp at h_zero_le_y
          linarith
        · rw [h_x_zero] at hy_ge
          have h_y_le_zero : (y : ℝ) ≤ ((0 : Dyadic) : ℝ) := by
            have := hy_min' 0 h_zero_mem (by rw [h_x_zero]; simp)
            simpa using this
          simp at h_y_le_zero
          linarith
      have h_y'_eq_zero : (y' : ℝ) = 0 := by
        rcases hy'_faith with ⟨_, hy'_le, hy'_max⟩ | ⟨_, hy'_ge, hy'_min'⟩
        · rw [h_x_zero] at hy'_le
          have h_zero_le_y' : ((0 : Dyadic) : ℝ) ≤ (y' : ℝ) := by
            have := hy'_max 0 h_zero_mem (by rw [h_x_zero]; simp)
            simpa using this
          simp at h_zero_le_y'
          linarith
        · rw [h_x_zero] at hy'_ge
          have h_y'_le_zero : (y' : ℝ) ≤ ((0 : Dyadic) : ℝ) := by
            have := hy'_min' 0 h_zero_mem (by rw [h_x_zero]; simp)
            simpa using this
          simp at h_y'_le_zero
          linarith
      rw [h_y_eq_zero, h_y'_eq_zero]
  | toEven =>
    obtain ⟨hy_mem, hy_faith, hy_min, hy_tie⟩ := hy
    obtain ⟨hy'_mem, hy'_faith, hy'_min, hy'_tie⟩ := hy'
    have h_dist_eq : |x - (y : ℝ)| = |x - (y' : ℝ)| :=
      le_antisymm (hy_min y' hy'_mem hy'_faith) (hy'_min y hy_mem hy_faith)
    by_cases h_yy : y = y'
    · exact h_yy
    · -- Tie case: both y and y' must be IsEven (per tie-break). Among {dlo, dhi},
      -- at most one is IsEven. So y = y' — contradiction with h_yy unless
      -- y = y' = unique even.
      -- But here we have y ≠ y'. Derive that both are IsEven and arrive at
      -- contradiction via parity dichotomy + alternating.
      exfalso
      have h_F_y_even : ∃ F' : ParityFormat, F'.toFormat = F.unbounded.toFormat ∧ F'.IsEven y :=
        hy_tie ⟨y', hy'_mem, hy'_faith, fun heq => h_yy heq.symm, h_dist_eq⟩
      have h_F_y'_even : ∃ F' : ParityFormat, F'.toFormat = F.unbounded.toFormat ∧ F'.IsEven y' :=
        hy'_tie ⟨y, hy_mem, hy_faith, h_yy, h_dist_eq.symm⟩
      obtain ⟨F_y, hF_y_eq, hF_y_even⟩ := h_F_y_even
      obtain ⟨F_y', hF_y'_eq, hF_y'_even⟩ := h_F_y'_even
      -- Bridge via IsEven_iff_of_toFormat_eq to a common ParityFormat F''.
      have h_unb : ¬ F.unbounded.IsUndefined (.nearest .toEven) := h
      set F'' := F.unbounded.toParityFormatOfNearestEven h_unb with hF''_def
      have hF''_eq : F''.toFormat = F.unbounded.toFormat := rfl
      have hF_y_eq_F'' : F_y.toFormat = F''.toFormat := by rw [hF_y_eq, hF''_eq]
      have hF_y'_eq_F'' : F_y'.toFormat = F''.toFormat := by rw [hF_y'_eq, hF''_eq]
      have hF''_even_y : F''.IsEven y :=
        ((ParityFormat.IsEven_iff_of_toFormat_eq hF_y_eq_F'' y).mp hF_y_even)
      have hF''_even_y' : F''.IsEven y' :=
        ((ParityFormat.IsEven_iff_of_toFormat_eq hF_y'_eq_F'' y').mp hF_y'_even)
      -- Setup canonical-exp infrastructure (mirroring _nearest_satisfies).
      have h_not_undef : ¬ (F.p = ⊤ ∧ F.exp = ⊥) :=
        fun ⟨hp, hexp⟩ => F.finite.elim (fun h => h hp) (fun h => h hexp)
      set e := F.canonicalExp x with h_e_def
      set s := x * (2 : ℝ) ^ (-e)
      set lo : ℤ := ⌊s⌋ with h_lo_def
      set dlo : Dyadic := Dyadic.ofIntZpow lo e with h_dlo_def
      set dhi : Dyadic := Dyadic.ofIntZpow (lo + 1) e with h_dhi_def
      have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
      have h_lo_bound : ∀ {p : ℕ+}, F.p = ((p : ℕ+) : WithTop ℕ+) →
          |lo| ≤ (2 : ℤ) ^ (p : ℕ) := fun hp => by
        apply abs_floor_le_of_abs_lt
        push_cast; exact floor_mantissa_lt hp
      have h_lop1_bound : ∀ {p : ℕ+}, F.p = ((p : ℕ+) : WithTop ℕ+) →
          |lo + 1| ≤ (2 : ℤ) ^ (p : ℕ) := fun hp =>
        abs_floor_add_one_le_of_abs_lt (floor_mantissa_lt hp)
      have h_exp_le : ∀ {e' : ℤ}, F.exp = (e' : WithBot ℤ) → e' ≤ e :=
        fun hexp => F.exp_le_canonicalExp x hexp
      have h_dlo_mem : dlo ∈ F.unbounded :=
        ofIntZpow_mem_unbounded F h_exp_le h_lo_bound
      have h_dhi_mem : dhi ∈ F.unbounded :=
        ofIntZpow_mem_unbounded F h_exp_le h_lop1_bound
      have h_dlo_real : (dlo : ℝ) = (lo : ℝ) * (2 : ℝ) ^ e :=
        Dyadic.coe_ofIntZpow _ _
      have h_dhi_real : (dhi : ℝ) = ((lo + 1 : ℤ) : ℝ) * (2 : ℝ) ^ e :=
        Dyadic.coe_ofIntZpow _ _
      have h_floor_le_s : (lo : ℝ) ≤ s := Int.floor_le _
      have h_s_lt_succ : s < (lo : ℝ) + 1 := Int.lt_floor_add_one _
      have h_s_unscale : s * (2 : ℝ) ^ e = x := mul_zpow_neg_self x e
      have h_dlo_le_x : (dlo : ℝ) ≤ x := by
        rw [h_dlo_real, ← h_s_unscale]
        exact mul_le_mul_of_nonneg_right h_floor_le_s h_2e_pos.le
      have h_x_le_dhi : x ≤ (dhi : ℝ) := by
        rw [h_dhi_real, ← h_s_unscale]
        apply mul_le_mul_of_nonneg_right _ h_2e_pos.le
        push_cast; linarith
      have h_dlo_round_down : ∀ z : Dyadic, z ∈ F.unbounded → (z : ℝ) ≤ x →
          (z : ℝ) ≤ (dlo : ℝ) := by
        intro z hz hz_le_x
        obtain ⟨hz_prec, hz_quant, _⟩ := hz
        rw [h_dlo_real]
        exact floor_minimality F x hz_prec hz_quant hz_le_x
      have h_dhi_round_up : (lo : ℝ) ≠ s →
          ∀ z : Dyadic, z ∈ F.unbounded → x ≤ (z : ℝ) → (dhi : ℝ) ≤ (z : ℝ) := by
        intro hs_ne z hz hx_le_z
        obtain ⟨hz_prec, hz_quant, _⟩ := hz
        rw [h_dhi_real]
        have h_ceil_eq : (⌈s⌉ : ℤ) = lo + 1 := by
          have h_lo_lt_s : (lo : ℝ) < s := lt_of_le_of_ne h_floor_le_s hs_ne
          have h_ceil_le : ⌈s⌉ ≤ lo + 1 :=
            Int.ceil_le.mpr (by push_cast; linarith)
          have h_ceil_ge : lo + 1 ≤ ⌈s⌉ := by
            have h_lt_ceil : (lo : ℝ) < (⌈s⌉ : ℝ) :=
              lt_of_lt_of_le h_lo_lt_s (Int.le_ceil _)
            have : lo < ⌈s⌉ := by exact_mod_cast h_lt_ceil
            omega
          omega
        have hh := ceil_minimality F x hz_prec hz_quant hx_le_z
        have h_subst : ((lo + 1 : ℤ) : ℝ) = ((⌈s⌉ : ℤ) : ℝ) := by
          exact_mod_cast h_ceil_eq.symm
        rw [h_subst]
        convert hh using 2
      have h_faithful_eq : ∀ z : Dyadic, IsFaithfulRound F.unbounded x z →
          z = dlo ∨ z = dhi := by
        intro z hf
        rcases hf with ⟨hz_mem, hz_le, hz_max⟩ | ⟨hz_mem, hz_ge, hz_min⟩
        · left
          apply Subtype.ext
          exact le_antisymm (h_dlo_round_down z hz_mem hz_le)
            (hz_max dlo h_dlo_mem h_dlo_le_x)
        · by_cases hs_eq : (lo : ℝ) = s
          · left; apply Subtype.ext
            have hx_eq_dlo : x = (dlo : ℝ) := by
              rw [h_dlo_real]
              have h_x_eq : x = s * (2 : ℝ) ^ e := by
                change x = x * (2 : ℝ) ^ (-e) * (2 : ℝ) ^ e
                rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
                    neg_add_cancel, zpow_zero, mul_one]
              rw [h_x_eq, ← hs_eq]
            have h_z_le_dlo : (z : ℝ) ≤ (dlo : ℝ) :=
              hz_min dlo h_dlo_mem (le_of_eq hx_eq_dlo)
            have h_z_ge_dlo : (dlo : ℝ) ≤ (z : ℝ) := hx_eq_dlo ▸ hz_ge
            exact le_antisymm h_z_le_dlo h_z_ge_dlo
          · right; apply Subtype.ext
            exact le_antisymm (hz_min dhi h_dhi_mem h_x_le_dhi)
              (h_dhi_round_up hs_eq z hz_mem hz_ge)
      -- y, y' ∈ {dlo, dhi}.
      have h_both_even : F''.IsEven dlo ∧ F''.IsEven dhi := by
        rcases h_faithful_eq y hy_faith with h_y_dlo | h_y_dhi
        · rcases h_faithful_eq y' hy'_faith with h_y'_dlo | h_y'_dhi
          · exact absurd (h_y_dlo.trans h_y'_dlo.symm) h_yy
          · refine ⟨?_, ?_⟩
            · rw [h_y_dlo] at hF''_even_y; exact hF''_even_y
            · rw [h_y'_dhi] at hF''_even_y'; exact hF''_even_y'
        · rcases h_faithful_eq y' hy'_faith with h_y'_dlo | h_y'_dhi
          · refine ⟨?_, ?_⟩
            · rw [h_y'_dlo] at hF''_even_y'; exact hF''_even_y'
            · rw [h_y_dhi] at hF''_even_y; exact hF''_even_y
          · exact absurd (h_y_dhi.trans h_y'_dhi.symm) h_yy
      obtain ⟨h_F''_even_dlo, h_F''_even_dhi⟩ := h_both_even
      -- Now derive contradiction by format case-split: alternating_parity gives
      -- IsOdd dlo ∨ IsOdd dhi. Combined with IsEven on both, not_isEven_and_isOdd.
      have h_not_isOdd_dlo : ¬ F''.IsOdd dlo := fun h_odd =>
        ParityFormat.not_isEven_and_isOdd h_F''_even_dlo h_odd
      have h_isOdd_dhi : F''.IsOdd dhi := by
        -- Format case-split: each gives the alternating_parity application.
        cases hp_F : F.p with
        | top =>
          cases hexp_F : F.exp with
          | bot => exact absurd ⟨hp_F, hexp_F⟩ h_not_undef
          | coe e'' =>
            have h_e_eq : e = e'' := by
              change F.canonicalExp x = _
              unfold FiniteFormat.canonicalExp
              simp [hp_F, hexp_F]
            have h_dlo_at_e'' : dlo = Dyadic.ofIntZpow lo e'' := by
              rw [h_dlo_def, h_e_eq]
            have h_dhi_at_e'' : dhi = Dyadic.ofIntZpow (lo + 1) e'' := by
              rw [h_dhi_def, h_e_eq]
            rw [h_dhi_at_e'']
            apply ParityFormat.alternating_parity_fixedpoint hp_F hexp_F
            rw [← h_dlo_at_e'']; exact h_not_isOdd_dlo
        | coe p =>
          cases hexp_F : F.exp with
          | bot =>
            -- Floating. p ≠ 1 (else .nearest .toEven undefined).
            have hp_ne_1 : F.p ≠ ((1 : ℕ+) : WithTop ℕ+) := fun h_eq =>
              h ⟨h_eq, hexp_F, Or.inr rfl⟩
            have h_s_lt_p : |x * (2 : ℝ) ^ (-e)| < (2 : ℝ) ^ (p : ℕ) :=
              floor_mantissa_lt hp_F
            have h_lo_hi : |lo| ≤ (2 : ℤ) ^ (p : ℕ) := by
              apply abs_floor_le_of_abs_lt; push_cast; exact h_s_lt_p
            have h_lop1_hi : |lo + 1| ≤ (2 : ℤ) ^ (p : ℕ) :=
              abs_floor_add_one_le_of_abs_lt h_s_lt_p
            -- Faithful + tie at x = 0 forces y = y' = 0; combined with h_yy.
            have hx_ne : x ≠ 0 := by
              intro hx0
              subst hx0
              have h_zero_mem : (0 : Dyadic) ∈ F.unbounded :=
                FiniteFormat.zero_mem F.unbounded
              have h_y_eq_z : (y : ℝ) = 0 := by
                rcases hy_faith with ⟨_, hy_le, hy_max⟩ | ⟨_, hy_ge, hy_min'⟩
                · have h_zero_le_y : ((0 : Dyadic) : ℝ) ≤ (y : ℝ) := by
                    have := hy_max 0 h_zero_mem (by simp)
                    simpa using this
                  simp at h_zero_le_y; linarith
                · have h_y_le_z : (y : ℝ) ≤ ((0 : Dyadic) : ℝ) := by
                    have := hy_min' 0 h_zero_mem (by simp)
                    simpa using this
                  simp at h_y_le_z; linarith
              have h_y'_eq_z : (y' : ℝ) = 0 := by
                rcases hy'_faith with ⟨_, hy'_le, hy'_max⟩ | ⟨_, hy'_ge, hy'_min'⟩
                · have h_zero_le_y' : ((0 : Dyadic) : ℝ) ≤ (y' : ℝ) := by
                    have := hy'_max 0 h_zero_mem (by simp)
                    simpa using this
                  simp at h_zero_le_y'; linarith
                · have h_y'_le_z : (y' : ℝ) ≤ ((0 : Dyadic) : ℝ) := by
                    have := hy'_min' 0 h_zero_mem (by simp)
                    simpa using this
                  simp at h_y'_le_z; linarith
              exact h_yy (Subtype.ext (h_y_eq_z.trans h_y'_eq_z.symm))
            have h_e_eq_log : e = Int.log 2 |x| + 1 - (p : ℤ) := by
              change F.canonicalExp x = _
              unfold FiniteFormat.canonicalExp
              simp [hp_F, hexp_F, hx_ne]
            have h_s_lo_real : ((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) ≤
                |x * (2 : ℝ) ^ (-e)| :=
              two_pow_pred_le_scaled (p := p) hx_ne h_e_eq_log
            have h_lo_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo| :=
              abs_floor_ge_two_pow_pred (p := p) h_s_lo_real
            -- Distance equality at tie forces s ≠ lo (else x = dlo = y = y').
            have h_lo_ne_s : (lo : ℝ) ≠ s := by
              intro h_eq
              have h_x_eq_dlo : x = (dlo : ℝ) := by
                rw [h_dlo_real]
                have : x = s * (2 : ℝ) ^ e := h_s_unscale.symm
                rw [this, ← h_eq]
              have h_y_eq_dlo' : (y : ℝ) = (dlo : ℝ) := by
                rcases hy_faith with ⟨_, hy_le, hy_max⟩ | ⟨_, hy_ge, hy_min'⟩
                · exact le_antisymm (h_dlo_round_down y hy_mem hy_le)
                    (hy_max dlo h_dlo_mem h_dlo_le_x)
                · exact le_antisymm (hy_min' dlo h_dlo_mem (le_of_eq h_x_eq_dlo))
                    (h_x_eq_dlo ▸ hy_ge)
              have h_y'_eq_dlo' : (y' : ℝ) = (dlo : ℝ) := by
                rcases hy'_faith with ⟨_, hy'_le, hy'_max⟩ | ⟨_, hy'_ge, hy'_min'⟩
                · exact le_antisymm (h_dlo_round_down y' hy'_mem hy'_le)
                    (hy'_max dlo h_dlo_mem h_dlo_le_x)
                · exact le_antisymm (hy'_min' dlo h_dlo_mem (le_of_eq h_x_eq_dlo))
                    (h_x_eq_dlo ▸ hy'_ge)
              exact h_yy (Subtype.ext (h_y_eq_dlo'.trans h_y'_eq_dlo'.symm))
            have h_lop1_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo + 1| := by
              by_cases hs_nn : 0 ≤ s
              · have h_lo_nn : 0 ≤ lo := Int.floor_nonneg.mpr hs_nn
                rw [abs_of_nonneg (by linarith : (0 : ℤ) ≤ lo + 1)]
                linarith [h_lo_lo, abs_of_nonneg h_lo_nn]
              · have hs_neg : s < 0 := not_le.mp hs_nn
                have h_floor_lt : (lo : ℝ) < s := lt_of_le_of_ne h_floor_le_s h_lo_ne_s
                have h_s_le_r : s ≤ -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) := by
                  have h_abs_eq : |s| = -s := abs_of_neg hs_neg
                  linarith [h_s_lo_real]
                have h_lo_lt_neg : (lo : ℝ) < -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) :=
                  lt_of_lt_of_le h_floor_lt h_s_le_r
                have h_lo_lt_int : lo < -((2 : ℤ) ^ ((p : ℕ) - 1)) := by
                  exact_mod_cast h_lo_lt_neg
                have h_lop1_le : lo + 1 ≤ -((2 : ℤ) ^ ((p : ℕ) - 1)) := by linarith
                have h_lop1_neg : lo + 1 < 0 := by
                  have : (0 : ℤ) < (2 : ℤ) ^ ((p : ℕ) - 1) := by positivity
                  linarith
                rw [abs_of_neg h_lop1_neg]; linarith
            exact ParityFormat.alternating_parity_floating hp_F hp_ne_1 hexp_F
              h_lo_lo h_lo_hi h_lop1_lo h_lop1_hi h_not_isOdd_dlo
          | coe e'' =>
            -- Mixed case. Derive hx_ne and dispatch.
            have hx_ne : x ≠ 0 := by
              intro hx0
              subst hx0
              have h_zero_mem : (0 : Dyadic) ∈ F.unbounded :=
                FiniteFormat.zero_mem F.unbounded
              have h_y_eq_z : (y : ℝ) = 0 := by
                rcases hy_faith with ⟨_, hy_le, hy_max⟩ | ⟨_, hy_ge, hy_min'⟩
                · have h_zero_le_y : ((0 : Dyadic) : ℝ) ≤ (y : ℝ) := by
                    have := hy_max 0 h_zero_mem (by simp); simpa using this
                  simp at h_zero_le_y; linarith
                · have h_y_le_z : (y : ℝ) ≤ ((0 : Dyadic) : ℝ) := by
                    have := hy_min' 0 h_zero_mem (by simp); simpa using this
                  simp at h_y_le_z; linarith
              have h_y'_eq_z : (y' : ℝ) = 0 := by
                rcases hy'_faith with ⟨_, hy'_le, hy'_max⟩ | ⟨_, hy'_ge, hy'_min'⟩
                · have h_zero_le_y' : ((0 : Dyadic) : ℝ) ≤ (y' : ℝ) := by
                    have := hy'_max 0 h_zero_mem (by simp); simpa using this
                  simp at h_zero_le_y'; linarith
                · have h_y'_le_z : (y' : ℝ) ≤ ((0 : Dyadic) : ℝ) := by
                    have := hy'_min' 0 h_zero_mem (by simp); simpa using this
                  simp at h_y'_le_z; linarith
              exact h_yy (Subtype.ext (h_y_eq_z.trans h_y'_eq_z.symm))
            -- h_lo_ne_s from tie (same as floating case).
            have h_lo_ne_s : (lo : ℝ) ≠ s := by
              intro h_eq
              have h_x_eq_dlo : x = (dlo : ℝ) := by
                rw [h_dlo_real]
                have : x = s * (2 : ℝ) ^ e := h_s_unscale.symm
                rw [this, ← h_eq]
              have h_y_eq_dlo' : (y : ℝ) = (dlo : ℝ) := by
                rcases hy_faith with ⟨_, hy_le, hy_max⟩ | ⟨_, hy_ge, hy_min'⟩
                · exact le_antisymm (h_dlo_round_down y hy_mem hy_le)
                    (hy_max dlo h_dlo_mem h_dlo_le_x)
                · exact le_antisymm (hy_min' dlo h_dlo_mem (le_of_eq h_x_eq_dlo))
                    (h_x_eq_dlo ▸ hy_ge)
              have h_y'_eq_dlo' : (y' : ℝ) = (dlo : ℝ) := by
                rcases hy'_faith with ⟨_, hy'_le, hy'_max⟩ | ⟨_, hy'_ge, hy'_min'⟩
                · exact le_antisymm (h_dlo_round_down y' hy'_mem hy'_le)
                    (hy'_max dlo h_dlo_mem h_dlo_le_x)
                · exact le_antisymm (hy'_min' dlo h_dlo_mem (le_of_eq h_x_eq_dlo))
                    (h_x_eq_dlo ▸ hy'_ge)
              exact h_yy (Subtype.ext (h_y_eq_dlo'.trans h_y'_eq_dlo'.symm))
            by_cases hp_eq_1 : p = (1 : ℕ+)
            · -- p = 1.
              subst hp_eq_1
              have h_e_ge : e'' ≤ e := F.exp_le_canonicalExp x hexp_F
              have h_s_lt : |x * (2 : ℝ) ^ (-e)| < (2 : ℝ) ^ ((1 : ℕ+) : ℕ) :=
                floor_mantissa_lt hp_F
              have h_s_lt_2 : |x * (2 : ℝ) ^ (-e)| < ((2 : ℤ) : ℝ) := by
                have h_cast : ((2 : ℤ) : ℝ) = (2 : ℝ) ^ ((1 : ℕ+) : ℕ) := by
                  change (2 : ℝ) = (2 : ℝ) ^ (1 : ℕ); ring
                rw [h_cast]; exact h_s_lt
              have h_lo_hi_int : |lo| ≤ 2 := abs_floor_le_of_abs_lt h_s_lt_2
              have h_lop1_hi_int : |lo + 1| ≤ 2 :=
                abs_floor_add_one_le_of_abs_lt (p := 1) h_s_lt
              have h_dlo_at : dlo = Dyadic.ofIntZpow lo e := h_dlo_def
              have h_dhi_at : dhi = Dyadic.ofIntZpow (lo + 1) e := h_dhi_def
              by_cases h_regime : Int.log 2 |x| + 1 - ((1 : ℕ+) : ℤ) ≤ e''
              · -- Subnormal: e = e''.
                have h_e_eq : e = e'' := by
                  change F.canonicalExp x = e''
                  unfold FiniteFormat.canonicalExp
                  simp only [hp_F, hexp_F]
                  rw [if_neg hx_ne]
                  exact max_eq_right h_regime
                rw [h_dlo_at, h_e_eq] at h_not_isOdd_dlo
                rw [h_dhi_at, h_e_eq]
                exact ParityFormat.alternating_parity_mixed_subnormal_p1
                  hp_F hexp_F h_lo_hi_int h_lop1_hi_int h_not_isOdd_dlo
              · -- Normal.
                push Not at h_regime
                have h_pcast : ((1 : ℕ+) : ℤ) = 1 := rfl
                have h_e_eq_log : e = Int.log 2 |x| := by
                  change F.canonicalExp x = _
                  unfold FiniteFormat.canonicalExp
                  simp only [hp_F, hexp_F]
                  rw [if_neg hx_ne]
                  rw [show (((1 : ℕ+) : ℕ) : ℤ) = 1 from rfl]
                  have h_max_eq : max (Int.log 2 |x| + 1 - 1) e'' =
                      Int.log 2 |x| + 1 - 1 := by
                    apply max_eq_left
                    have := h_regime; rw [h_pcast] at this; linarith
                  rw [h_max_eq]; ring
                have h_x_ge : (2 : ℝ) ^ (Int.log 2 |x|) ≤ |x| :=
                  Int.zpow_log_le_self (b := 2) (by norm_num : (1 : ℕ) < 2)
                    (abs_pos.mpr hx_ne)
                have h_abs_s : 1 ≤ |x * (2 : ℝ) ^ (-e)| := by
                  have h_abs_eq : |x * (2 : ℝ) ^ (-e)| = |x| * (2 : ℝ) ^ (-e) := by
                    rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)]
                  rw [h_abs_eq, h_e_eq_log]
                  have h_pow_eq : (2 : ℝ) ^ (Int.log 2 |x|) *
                      (2 : ℝ) ^ (-Int.log 2 |x|) = 1 := by
                    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
                        add_neg_cancel, zpow_zero]
                  have h_le := mul_le_mul_of_nonneg_right h_x_ge
                    (zpow_pos (by norm_num : (0 : ℝ) < 2) (-Int.log 2 |x|)).le
                  rw [h_pow_eq] at h_le
                  exact h_le
                have h_lo_lo_int : 1 ≤ |lo| := by
                  by_cases hs_nn : 0 ≤ x * (2 : ℝ) ^ (-e)
                  · have h_s_ge : 1 ≤ x * (2 : ℝ) ^ (-e) := by
                      have h_abs_eq : |x * (2 : ℝ) ^ (-e)| = x * (2 : ℝ) ^ (-e) :=
                        abs_of_nonneg hs_nn
                      linarith [h_abs_s]
                    have h_lo_ge_1 : 1 ≤ lo := by
                      apply Int.le_floor.mpr; push_cast; exact h_s_ge
                    rw [abs_of_nonneg (by linarith : (0 : ℤ) ≤ lo)]; exact h_lo_ge_1
                  · push Not at hs_nn
                    have h_s_le : x * (2 : ℝ) ^ (-e) ≤ -1 := by
                      have h_abs_eq : |x * (2 : ℝ) ^ (-e)| =
                          -(x * (2 : ℝ) ^ (-e)) := abs_of_neg hs_nn
                      linarith [h_abs_s]
                    have h_floor_le : (lo : ℝ) ≤ x * (2 : ℝ) ^ (-e) :=
                      Int.floor_le _
                    have h_lo_le : (lo : ℝ) ≤ -1 := le_trans h_floor_le h_s_le
                    have h_lo_le_int : lo ≤ -1 := by exact_mod_cast h_lo_le
                    rw [abs_of_neg (by linarith : lo < 0)]; linarith
                have h_lo_ne_neg1 : lo ≠ -1 := by
                  intro h_eq
                  have h_lo_int : ⌊s⌋ = -1 := h_eq
                  have h_floor_le_neg1 : (-1 : ℝ) ≤ s := by
                    have h_fl := Int.floor_le s
                    rw [h_lo_int] at h_fl; push_cast at h_fl; exact h_fl
                  have h_lt_succ_zero : s < 0 := by
                    have h_lt := Int.lt_floor_add_one s
                    rw [h_lo_int] at h_lt; push_cast at h_lt; linarith
                  have h_s_le_neg1 : s ≤ -1 := by
                    have h_abs_eq : |s| = -s := abs_of_neg (by linarith : s < 0)
                    have h_abs_ge : 1 ≤ |s| := h_abs_s
                    linarith
                  have h_s_eq : s = -1 := le_antisymm h_s_le_neg1 h_floor_le_neg1
                  apply h_lo_ne_s
                  rw [h_s_eq, h_eq]; push_cast; ring
                have h_lop1_lo_int : 1 ≤ |lo + 1| := by
                  have h_lop1_ne : lo + 1 ≠ 0 := by
                    intro h0; apply h_lo_ne_neg1; omega
                  exact Int.one_le_abs h_lop1_ne
                rw [h_dlo_at] at h_not_isOdd_dlo
                rw [h_dhi_at]
                exact ParityFormat.alternating_parity_mixed_normal_p1
                  hp_F hexp_F h_e_ge h_lo_lo_int h_lo_hi_int
                  h_lop1_lo_int h_lop1_hi_int h_not_isOdd_dlo
            · -- p ≠ 1.
              have hp_ne_1 : F.p ≠ ((1 : ℕ+) : WithTop ℕ+) := by
                rw [hp_F]
                intro h_eq
                apply hp_eq_1
                exact_mod_cast h_eq
              by_cases h_regime : Int.log 2 |x| + 1 - ((p : ℕ+) : ℤ) ≤ e''
              · -- Subnormal: e = e''.
                have h_e_eq : e = e'' := by
                  change F.canonicalExp x = e''
                  unfold FiniteFormat.canonicalExp
                  simp only [hp_F, hexp_F]
                  rw [if_neg hx_ne]
                  exact max_eq_right h_regime
                have h_x_lt : |x| < (2 : ℝ) ^ (e'' + (p : ℤ)) := by
                  have h_log_le : Int.log 2 |x| ≤ e'' + (p : ℤ) - 1 := by
                    have h_pcast : ((p : ℕ+) : ℤ) = (p : ℤ) := rfl
                    linarith
                  have h_lt := Int.lt_zpow_succ_log_self
                    (by norm_num : (1 : ℕ) < 2) |x|
                  have : Int.log 2 |x| + 1 ≤ e'' + (p : ℤ) := by linarith
                  exact lt_of_lt_of_le h_lt
                    (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) this)
                have h_s_lt : |x * (2 : ℝ) ^ (-e)| < (2 : ℝ) ^ ((p : ℕ+) : ℕ) := by
                  rw [h_e_eq]
                  have h_abs : |x * (2 : ℝ) ^ (-e'')| = |x| * (2 : ℝ) ^ (-e'') := by
                    rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)]
                  rw [h_abs]
                  have h_2neg_pos : (0 : ℝ) < (2 : ℝ) ^ (-e'') :=
                    zpow_pos (by norm_num) _
                  have h_eq_split : (2 : ℝ) ^ (e'' + (p : ℤ)) =
                      (2 : ℝ) ^ e'' * (2 : ℝ) ^ ((p : ℕ+) : ℕ) := by
                    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
                    have h_pcast : ((p : ℕ+) : ℤ) = (((p : ℕ+) : ℕ) : ℤ) := rfl
                    rw [h_pcast, zpow_natCast]
                  have h_x2neg : |x| * (2 : ℝ) ^ (-e'') <
                      (2 : ℝ) ^ (e'' + (p : ℤ)) * (2 : ℝ) ^ (-e'') :=
                    mul_lt_mul_of_pos_right h_x_lt h_2neg_pos
                  rw [h_eq_split] at h_x2neg
                  have h_cancel : (2 : ℝ) ^ e'' * (2 : ℝ) ^ ((p : ℕ+) : ℕ) *
                      (2 : ℝ) ^ (-e'') = (2 : ℝ) ^ ((p : ℕ+) : ℕ) := by
                    rw [mul_right_comm, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
                        add_neg_cancel, zpow_zero, one_mul]
                  rw [h_cancel] at h_x2neg
                  exact h_x2neg
                have h_lo_le : |lo| ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by
                  apply abs_floor_le_of_abs_lt; push_cast; exact h_s_lt
                have h_lop1_le : |lo + 1| ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) :=
                  abs_floor_add_one_le_of_abs_lt h_s_lt
                have h_dlo_at_e'' : dlo = Dyadic.ofIntZpow lo e'' := by
                  rw [h_dlo_def, h_e_eq]
                have h_dhi_at_e'' : dhi = Dyadic.ofIntZpow (lo + 1) e'' := by
                  rw [h_dhi_def, h_e_eq]
                rcases lt_or_eq_of_le h_lo_le with h_lo_lt | h_lo_sat
                · rcases lt_or_eq_of_le h_lop1_le with h_lop1_lt | h_lop1_sat
                  · -- Both non-sat.
                    have h_log_lo' := log_lt_p_of_abs_lt_two_pow h_lo_lt
                    have h_log_lop1_raw := log_lt_p_of_abs_lt_two_pow h_lop1_lt
                    have h_log_lop1' : Int.log 2 |((lo : ℝ) + 1)| + 1 ≤
                        (((p : ℕ+) : ℕ) : ℤ) := by
                      have h_eq : |((lo : ℝ) + 1)| = |((lo + 1 : ℤ) : ℝ)| := by
                        push_cast; rfl
                      rw [h_eq]; exact h_log_lop1_raw
                    rw [h_dlo_at_e''] at h_not_isOdd_dlo
                    rw [h_dhi_at_e'']
                    exact ParityFormat.alternating_parity_mixed_subnormal_pne1
                      hp_F hp_ne_1 hexp_F h_log_lo' h_log_lop1' h_not_isOdd_dlo
                  · -- |lo+1| sat: lo = ±2^p ∓ 1 is odd, so IsOdd dlo holds,
                    -- contradicting h_not_isOdd_dlo.
                    have h_log_lo' := log_lt_p_of_abs_lt_two_pow h_lo_lt
                    have h_lo_ne : lo ≠ 0 := by
                      intro h_zero
                      rw [h_zero] at h_lop1_sat
                      simp at h_lop1_sat
                      have h2p_ge : (2 : ℤ) ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by
                        calc (2 : ℤ) = (2 : ℤ) ^ 1 := by ring
                          _ ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) :=
                              pow_le_pow_right₀ (by norm_num) (p : ℕ+).pos
                      linarith
                    have h_isOdd_dlo : F''.IsOdd dlo := by
                      rw [h_dlo_at_e'']
                      rw [ParityFormat.isOdd_iff_odd_at_canonical_mixed_subnormal
                        hp_F hp_ne_1 hexp_F h_lo_ne h_log_lo']
                      have h2p_nn : (0 : ℤ) ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by positivity
                      rcases (abs_eq h2p_nn).mp h_lop1_sat with hpos | hneg
                      · have h_lo_eq : lo = (2 : ℤ) ^ ((p : ℕ+) : ℕ) - 1 := by omega
                        rw [h_lo_eq]
                        have h_even : Even ((2 : ℤ) ^ ((p : ℕ+) : ℕ)) := by
                          refine ⟨(2 : ℤ) ^ (((p : ℕ+) : ℕ) - 1), ?_⟩
                          have := Dyadic.two_pow_succ_pred (p : ℕ+).pos
                          linarith
                        obtain ⟨m, hm⟩ := h_even
                        exact ⟨m - 1, by linarith⟩
                      · have h_lo_eq : lo = -((2 : ℤ) ^ ((p : ℕ+) : ℕ)) - 1 := by omega
                        rw [h_lo_eq]
                        have h_even : Even ((2 : ℤ) ^ ((p : ℕ+) : ℕ)) := by
                          refine ⟨(2 : ℤ) ^ (((p : ℕ+) : ℕ) - 1), ?_⟩
                          have := Dyadic.two_pow_succ_pred (p : ℕ+).pos
                          linarith
                        obtain ⟨m, hm⟩ := h_even
                        exact ⟨-m - 1, by linarith⟩
                    exact (h_not_isOdd_dlo h_isOdd_dlo).elim
                · -- |lo| sat. Similar reasoning: dlo at sat has IsEven (which matches),
                  -- and from |lop1| ≤ 2^p with |lo| = 2^p, |lop1| < 2^p forced or
                  -- equals. We derive IsOdd dhi at lo+1 non-sat with Odd value.
                  -- lo = ±2^p. If lo = 2^p: |lop1| = 2^p+1 > 2^p contradicts h_lop1_le.
                  -- So lo = -2^p, lo+1 = -2^p + 1, Odd.
                  have h2p_nn : (0 : ℤ) ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by positivity
                  have h_lo_neg : lo = -((2 : ℤ) ^ ((p : ℕ+) : ℕ)) := by
                    rcases (abs_eq h2p_nn).mp h_lo_sat with hpos | hneg
                    · exfalso
                      rw [hpos] at h_lop1_le
                      have h_abs : |(2 : ℤ) ^ ((p : ℕ+) : ℕ) + 1| =
                          (2 : ℤ) ^ ((p : ℕ+) : ℕ) + 1 := by
                        apply abs_of_pos; positivity
                      linarith
                    · exact hneg
                  have h_lop1_lt : |lo + 1| < (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by
                    rw [h_lo_neg]
                    have h_pos_inner : (0 : ℤ) < (2 : ℤ) ^ ((p : ℕ+) : ℕ) - 1 := by
                      have h2le : (2 : ℤ) ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) := by
                        calc (2 : ℤ) = (2 : ℤ) ^ 1 := by ring
                          _ ≤ (2 : ℤ) ^ ((p : ℕ+) : ℕ) :=
                              pow_le_pow_right₀ (by norm_num) (p : ℕ+).pos
                      linarith
                    have h_rw : -((2 : ℤ) ^ ((p : ℕ+) : ℕ)) + 1 =
                        -((2 : ℤ) ^ ((p : ℕ+) : ℕ) - 1) := by ring
                    rw [h_rw, abs_neg, abs_of_pos h_pos_inner]; linarith
                  have h_log_lop1' := log_lt_p_of_abs_lt_two_pow h_lop1_lt
                  have h_lop1_ne : lo + 1 ≠ 0 := by
                    rw [h_lo_neg]
                    have : (2 : ℤ) ^ ((p : ℕ+) : ℕ) ≥ 2 := by
                      calc (2 : ℤ) ^ ((p : ℕ+) : ℕ) ≥ (2 : ℤ) ^ 1 :=
                          pow_le_pow_right₀ (by norm_num) (p : ℕ+).pos
                        _ = 2 := by ring
                    omega
                  rw [h_dhi_at_e'']
                  rw [ParityFormat.isOdd_iff_odd_at_canonical_mixed_subnormal
                    hp_F hp_ne_1 hexp_F h_lop1_ne h_log_lop1']
                  rw [h_lo_neg]
                  -- Show Odd (-2^p + 1).
                  have h_even : Even ((2 : ℤ) ^ ((p : ℕ+) : ℕ)) := by
                    refine ⟨(2 : ℤ) ^ (((p : ℕ+) : ℕ) - 1), ?_⟩
                    have := Dyadic.two_pow_succ_pred (p : ℕ+).pos
                    linarith
                  obtain ⟨m, hm⟩ := h_even
                  exact ⟨-m, by linarith⟩
              · -- Normal regime.
                push Not at h_regime
                have h_dlo_real_e : (dlo : ℝ) = (lo : ℝ) * (2 : ℝ) ^ e := h_dlo_real
                have h_dhi_real_e : (dhi : ℝ) = ((lo + 1 : ℤ) : ℝ) * (2 : ℝ) ^ e :=
                  h_dhi_real
                have h_e_eq_log : e = Int.log 2 |x| + 1 - ((p : ℕ+) : ℤ) := by
                  change F.canonicalExp x = _
                  unfold FiniteFormat.canonicalExp
                  simp only [hp_F, hexp_F]
                  rw [if_neg hx_ne]
                  exact max_eq_left (le_of_lt h_regime)
                have h_s_lo_real : ((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) ≤
                    |x * (2 : ℝ) ^ (-e)| :=
                  two_pow_pred_le_scaled (p := p) hx_ne h_e_eq_log
                have h_lo_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo| :=
                  abs_floor_ge_two_pow_pred (p := p) h_s_lo_real
                have h_lop1_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo + 1| := by
                  by_cases hs_nn : 0 ≤ s
                  · have h_lo_nn : 0 ≤ lo := Int.floor_nonneg.mpr hs_nn
                    rw [abs_of_nonneg (by linarith : (0 : ℤ) ≤ lo + 1)]
                    linarith [h_lo_lo, abs_of_nonneg h_lo_nn]
                  · have hs_neg : s < 0 := not_le.mp hs_nn
                    have h_floor_lt : (lo : ℝ) < s :=
                      lt_of_le_of_ne h_floor_le_s h_lo_ne_s
                    have h_s_le_r : s ≤ -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) := by
                      have h_abs_eq : |s| = -s := abs_of_neg hs_neg
                      linarith [h_s_lo_real]
                    have h_lo_lt_neg : (lo : ℝ) < -((2 : ℤ) ^ ((p : ℕ) - 1) : ℝ) :=
                      lt_of_lt_of_le h_floor_lt h_s_le_r
                    have h_lo_lt_int : lo < -((2 : ℤ) ^ ((p : ℕ) - 1)) := by
                      exact_mod_cast h_lo_lt_neg
                    have h_lop1_le_int : lo + 1 ≤ -((2 : ℤ) ^ ((p : ℕ) - 1)) := by
                      linarith
                    have h_lop1_neg : lo + 1 < 0 := by
                      have : (0 : ℤ) < (2 : ℤ) ^ ((p : ℕ) - 1) := by positivity
                      linarith
                    rw [abs_of_neg h_lop1_neg]; linarith
                have h_lo_hi : |lo| ≤ (2 : ℤ) ^ ((p : ℕ) : ℕ) := h_lo_bound hp_F
                have h_lop1_hi : |lo + 1| ≤ (2 : ℤ) ^ ((p : ℕ) : ℕ) :=
                  h_lop1_bound hp_F
                have h_lo_ne : lo ≠ 0 := by
                  intro h_lo_zero
                  rw [h_lo_zero] at h_lo_lo
                  simp at h_lo_lo
                  have : (0 : ℤ) < (2 : ℤ) ^ ((p : ℕ) - 1) := by positivity
                  omega
                have h_lop1_ne : lo + 1 ≠ 0 := by
                  intro h_lop1_zero
                  rw [h_lop1_zero] at h_lop1_lo
                  simp at h_lop1_lo
                  have : (0 : ℤ) < (2 : ℤ) ^ ((p : ℕ) - 1) := by positivity
                  omega
                have h_dlo_ne : (dlo : ℝ) ≠ 0 := by
                  rw [h_dlo_real_e]
                  exact mul_ne_zero (Int.cast_ne_zero.mpr h_lo_ne)
                    (ne_of_gt (zpow_pos (by norm_num) _))
                have h_dhi_ne : (dhi : ℝ) ≠ 0 := by
                  rw [h_dhi_real_e]
                  exact mul_ne_zero (Int.cast_ne_zero.mpr h_lop1_ne)
                    (ne_of_gt (zpow_pos (by norm_num) _))
                have h_log_dlo : Int.log 2 |(dlo : ℝ)| =
                    Int.log 2 |(lo : ℝ)| + e := by
                  rw [h_dlo_real_e]
                  exact ParityFormat.log_abs_mul_zpow h_lo_ne e
                have h_log_dhi : Int.log 2 |(dhi : ℝ)| =
                    Int.log 2 |((lo + 1 : ℤ) : ℝ)| + e := by
                  rw [h_dhi_real_e]
                  exact ParityFormat.log_abs_mul_zpow h_lop1_ne e
                have h_log_lo_lb := log_ge_p_pred_of_two_pow_pred_le
                  (k := lo) h_lo_lo
                have h_log_lop1_lb := log_ge_p_pred_of_two_pow_pred_le
                  (k := lo + 1) h_lop1_lo
                have h_log_lo : ((p : ℕ) : ℤ) ≤ Int.log 2 |(dlo : ℝ)| - e'' + 1 := by
                  rw [h_log_dlo, h_e_eq_log]
                  have : Int.log 2 |x| - e'' ≥ ((p : ℕ) : ℤ) := by linarith
                  linarith [h_log_lo_lb]
                have h_log_hi : ((p : ℕ) : ℤ) ≤ Int.log 2 |(dhi : ℝ)| - e'' + 1 := by
                  rw [h_log_dhi, h_e_eq_log]
                  have : Int.log 2 |x| - e'' ≥ ((p : ℕ) : ℤ) := by linarith
                  linarith [h_log_lop1_lb]
                exact ParityFormat.alternating_parity_mixed_normal_pne1
                  hp_F hp_ne_1 hexp_F h_dlo_ne h_dhi_ne h_log_lo h_log_hi
                  h_dlo_real_e h_dhi_real_e h_lo_lo h_lo_hi h_lop1_lo h_lop1_hi
                  h_not_isOdd_dlo
      exact ParityFormat.not_isEven_and_isOdd h_F''_even_dhi h_isOdd_dhi

/-- Uniqueness: any `y` satisfying the unbounded rounding spec equals
`rndUnbounded F rm x h`. -/
theorem rndUnbounded_unique (F : FiniteFormat) (rm : RoundingMode) (x : ℝ)
    (h : ¬ F.IsUndefined rm) {y : Dyadic}
    (hy : RoundsFinite F.unbounded rm x y) :
    y = rndUnbounded F rm x h := by
  cases rm with
  | toNegative => exact rndUnbounded_unique_toNegative F x h hy
  | toPositive => exact rndUnbounded_unique_toPositive F x h hy
  | toZero => exact rndUnbounded_unique_toZero F x h hy
  | awayZero => exact rndUnbounded_unique_awayZero F x h hy
  | toOdd => exact rndUnbounded_unique_toOdd F x h hy
  | nearest tb => exact rndUnbounded_unique_nearest F tb x h hy

/-! ### Bridge lemma

The `RoundResult`-typed `Rounds` collapses the per-mode bridges to one
uniform statement: `rnd` and `Rounds` agree on the same `RoundResult`. -/

theorem rnd_iff_rounds (F : FiniteFormat) (rm : RoundingMode) (x : ℝ) (r : RoundResult) :
    rnd F rm x = r ↔ Rounds F rm x r := by
  cases r with
  | undefined =>
    -- `Rounds F rm x .undefined` reduces to `F.IsUndefined rm` by definition.
    -- `rnd F rm x = .undefined` is true iff the outer `if` of `rnd` fires,
    -- i.e., iff `F.IsUndefined rm` holds.
    change rnd F rm x = .undefined ↔ F.IsUndefined rm
    constructor
    · intro h_eq
      by_contra h_undef
      unfold rnd at h_eq
      rw [dif_neg h_undef] at h_eq
      -- `let y := rndUnbounded ...; if boundOK ... then .finite y else .overflow`
      -- doesn't auto-reduce; force it with `dsimp only` so `split_ifs`
      -- can see the inner conditional and decompose to constructor-mismatch.
      dsimp only at h_eq
      split_ifs at h_eq
    · intro h_undef
      unfold rnd
      rw [dif_pos h_undef]
  | overflow b =>
    change rnd F rm x = .overflow b ↔
      ¬ F.IsUndefined rm ∧
      ∃ y, RoundsFinite F.unbounded rm x y ∧ ¬ Format.boundOK F.b y ∧
           (b ↔ (0 : ℝ) < (y : ℝ))
    constructor
    · intro h_eq
      have h_undef : ¬ F.IsUndefined rm := by
        intro h
        unfold rnd at h_eq
        rw [dif_pos h] at h_eq
        exact RoundResult.noConfusion h_eq
      refine ⟨h_undef, rndUnbounded F rm x h_undef,
              rndUnbounded_satisfies F rm x h_undef, ?_, ?_⟩
      · intro hb
        unfold rnd at h_eq
        rw [dif_neg h_undef] at h_eq
        dsimp only at h_eq
        rw [if_pos hb] at h_eq
        exact RoundResult.noConfusion h_eq
      · unfold rnd at h_eq
        rw [dif_neg h_undef] at h_eq
        dsimp only at h_eq
        split_ifs at h_eq with hb hpos
        · injection h_eq with hb_eq
          subst hb_eq
          exact ⟨fun _ => hpos, fun _ => rfl⟩
        · injection h_eq with hb_eq
          subst hb_eq
          exact ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd h hpos⟩
    · rintro ⟨h_undef, y, hRF, hBN, hSign⟩
      have h_y_eq : y = rndUnbounded F rm x h_undef :=
        rndUnbounded_unique F rm x h_undef hRF
      unfold rnd
      rw [dif_neg h_undef]
      dsimp only
      rw [if_neg (h_y_eq ▸ hBN)]
      congr 1
      by_cases hpos : (0 : ℝ) < (rndUnbounded F rm x h_undef : ℝ)
      · rw [if_pos hpos]
        have hy_pos : (0 : ℝ) < (y : ℝ) := h_y_eq ▸ hpos
        exact (hSign.mpr hy_pos).symm
      · rw [if_neg hpos]
        have hy_npos : ¬ (0 : ℝ) < (y : ℝ) := fun h => hpos (h_y_eq ▸ h)
        cases hb : b
        · rfl
        · exfalso
          exact hy_npos (hSign.mp (by rw [hb]))
  | finite y =>
    change rnd F rm x = .finite y ↔
      ¬ F.IsUndefined rm ∧
      RoundsFinite F.unbounded rm x y ∧ Format.boundOK F.b y
    constructor
    · -- Forward: rnd = .finite y ⇒ ⟨h_undef, RoundsFinite y, boundOK y⟩.
      -- Reading off `rnd`'s `if`s: the equation pins y = rndUnbounded ... and
      -- the bound check succeeded.
      intro h_eq
      have h_undef : ¬ F.IsUndefined rm := by
        intro h
        unfold rnd at h_eq
        rw [dif_pos h] at h_eq
        exact RoundResult.noConfusion h_eq
      unfold rnd at h_eq
      rw [dif_neg h_undef] at h_eq
      dsimp only at h_eq
      split_ifs at h_eq with hb
      · have h_y_eq : rndUnbounded F rm x h_undef = y := by injection h_eq
        refine ⟨h_undef, ?_, ?_⟩
        · rw [← h_y_eq]; exact rndUnbounded_satisfies F rm x h_undef
        · rw [← h_y_eq]; exact hb
    · -- Reverse: ⟨h_undef, RoundsFinite y, boundOK y⟩ ⇒ rnd = .finite y.
      -- By uniqueness, y = rndUnbounded; the bound check succeeds.
      rintro ⟨h_undef, hRF, hBOK⟩
      have h_y_eq : y = rndUnbounded F rm x h_undef :=
        rndUnbounded_unique F rm x h_undef hRF
      unfold rnd
      rw [dif_neg h_undef]
      dsimp only
      rw [if_pos (h_y_eq ▸ hBOK)]
      exact congrArg _ h_y_eq.symm

end Mpfx2
