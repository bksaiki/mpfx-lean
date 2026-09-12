import Mpfx.RoundOp.Defs
import Mpfx.Parity
import Mpfx.RoundOp.Directed
import Mpfx.RoundPred

/-!
# Constructive rounding: `toOdd` obligations

Soundness and uniqueness for the `toOdd` rounding mode.
-/

namespace Mpfx

attribute [local instance] Classical.propDecidable

/-- `Dyadic.ofIntZpow k e` is in `F.unbounded` provided `e ≥ F.exp` and (when
`F.p` is finite) `|k| ≤ 2^p`. The mantissa-bound boundary case `|k| = 2^p`
is handled by `precisionAtMost_of_abs_le`. -/
theorem rndUnbounded_satisfies_toOdd (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .toOdd) :
    RoundsFinite F.unbounded .toOdd x (rndUnbounded F .toOdd x h) := by
  set F'' := F.toParityFormatOfToOdd h with hF''_def
  set F' := F.unbounded.toParityFormatOfToOdd h with hF'_def
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
  have h_lo_bound : ∀ {p : ℕ}, F.p = (p : Prec) →
      |lo| ≤ (2 : ℤ) ^ p := fun hp => by
    apply abs_floor_le_of_abs_lt
    push_cast; exact floor_mantissa_lt hp
  have h_lop1_bound : ∀ {p : ℕ}, F.p = (p : Prec) →
      |lo + 1| ≤ (2 : ℤ) ^ p := fun hp =>
    abs_floor_add_one_le_of_abs_lt (floor_mantissa_lt hp)
  have h_exp_le : ∀ {e' : ℤ}, F.exp = (e' : QExp) → e' ≤ e :=
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
        exact (toOdd_neighbors_alternate x h hx hs).mpr hodd


end Mpfx
