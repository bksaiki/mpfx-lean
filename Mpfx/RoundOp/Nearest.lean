import Mpfx.RoundOp.Defs
import Mpfx.Parity
import Mpfx.RoundOp.ToOdd

/-!
# Constructive rounding: `nearest` obligations

Soundness and uniqueness for the `nearest tb` rounding modes.
-/

namespace Mpfx

attribute [local instance] Classical.propDecidable

/-- Neighbour setup for the `nearest` soundness proof, its only consumer since
the uniqueness proofs moved to `Mpfx/RoundPred.lean`. Given the canonical
scaling data
`e = canonicalExp x`, `s = x·2^(-e)`, `lo = ⌊s⌋` and the two neighbours
`dlo = lo·2^e`, `dhi = (lo+1)·2^e`, it packages: positivity of `2^e`,
membership of both neighbours, their real values, the floor sandwich,
the unscaling identity, the enclosure `dlo ≤ x ≤ dhi`, the two rounding
directions (`round-down`/`round-up`) and the faithful-round dichotomy
(any faithful round of `x` is `dlo` or `dhi`). The caller establishes the
`set` variables and passes the defining equations.

This bundle predates the relational layer and several conjuncts are now
redundant against it — the two rounding directions are
`RoundsFinite.toNegative_floor` / `toPositive_ceil`, and the dichotomy is
`isFaithfulRound_iff_directed` composed with the `_eq_floor` / `_eq_ceil`
bridges. Slimming it is the reason this construction-free helper still sits
under `RoundOp/`; see `ROUND_PRED_TODO.md`. -/
private theorem nearest_neighbors_setup (F : FiniteFormat) (x : ℝ)
    {e : ℤ} (h_e_def : e = F.canonicalExp x)
    {s : ℝ} (h_s_def : s = x * (2 : ℝ) ^ (-e))
    {lo : ℤ} (h_lo_def : lo = ⌊s⌋)
    {dlo dhi : Dyadic}
    (h_dlo_def : dlo = Dyadic.ofIntZpow lo e)
    (h_dhi_def : dhi = Dyadic.ofIntZpow (lo + 1) e) :
    (0 : ℝ) < (2 : ℝ) ^ e
    ∧ dlo ∈ F.unbounded ∧ dhi ∈ F.unbounded
    ∧ (dlo : ℝ) = (lo : ℝ) * (2 : ℝ) ^ e
    ∧ (dhi : ℝ) = ((lo + 1 : ℤ) : ℝ) * (2 : ℝ) ^ e
    ∧ (lo : ℝ) ≤ s ∧ s < (lo : ℝ) + 1 ∧ s * (2 : ℝ) ^ e = x
    ∧ (dlo : ℝ) ≤ x ∧ x ≤ (dhi : ℝ)
    ∧ (∀ z : Dyadic, z ∈ F.unbounded → (z : ℝ) ≤ x → (z : ℝ) ≤ (dlo : ℝ))
    ∧ ((lo : ℝ) ≠ s →
        ∀ z : Dyadic, z ∈ F.unbounded → x ≤ (z : ℝ) → (dhi : ℝ) ≤ (z : ℝ))
    ∧ (∀ y : Dyadic, IsFaithfulRound F.unbounded x y → y = dlo ∨ y = dhi) := by
  subst h_dhi_def h_dlo_def h_lo_def h_s_def h_e_def
  set e := F.canonicalExp x
  set s := x * (2 : ℝ) ^ (-e)
  set lo : ℤ := ⌊s⌋
  set dlo : Dyadic := Dyadic.ofIntZpow lo e
  set dhi : Dyadic := Dyadic.ofIntZpow (lo + 1) e
  have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have h_lop1_bound : ∀ {p : ℕ}, F.p = (p : Prec) →
      |lo + 1| ≤ (2 : ℤ) ^ p := fun hp =>
    abs_floor_add_one_le_of_abs_lt (floor_mantissa_lt hp)
  have h_exp_le : ∀ {e' : ℤ}, F.exp = (e' : QExp) → e' ≤ e :=
    fun hexp => F.exp_le_canonicalExp x hexp
  -- after the `set`s, `dlo` *is* the floor grid point at the canonical exponent
  have h_dn : RoundsFinite F.unbounded .toNegative x dlo :=
    RoundsFinite.toNegative_floor F x
  have h_dlo_mem : dlo ∈ F.unbounded := h_dn.1
  have h_dhi_mem : dhi ∈ F.unbounded :=
    ofIntZpow_mem_unbounded F h_exp_le h_lop1_bound
  have h_dlo_real : (dlo : ℝ) = (lo : ℝ) * (2 : ℝ) ^ e :=
    Dyadic.coe_ofIntZpow _ _
  have h_dhi_real : (dhi : ℝ) = ((lo + 1 : ℤ) : ℝ) * (2 : ℝ) ^ e :=
    Dyadic.coe_ofIntZpow _ _
  have h_floor_le_s : (lo : ℝ) ≤ s := Int.floor_le _
  have h_s_lt_succ : s < (lo : ℝ) + 1 := Int.lt_floor_add_one _
  have h_s_unscale : s * (2 : ℝ) ^ e = x := mul_zpow_neg_self x e
  have h_dlo_le_x : (dlo : ℝ) ≤ x := h_dn.2.1
  have h_x_le_dhi : x ≤ (dhi : ℝ) := by
    rw [h_dhi_real, ← h_s_unscale]
    apply mul_le_mul_of_nonneg_right _ h_2e_pos.le
    push_cast; linarith
  have h_dlo_round_down : ∀ z : Dyadic, z ∈ F.unbounded → (z : ℝ) ≤ x →
      (z : ℝ) ≤ (dlo : ℝ) := h_dn.2.2
  have h_dhi_round_up : (lo : ℝ) ≠ s →
      ∀ z : Dyadic, z ∈ F.unbounded → x ≤ (z : ℝ) → (dhi : ℝ) ≤ (z : ℝ) := by
    intro hs_ne z hz hx_le_z
    obtain ⟨hz_prec, hz_quant, _⟩ := hz
    rw [h_dhi_real]
    have h_ceil_eq : (⌈s⌉ : ℤ) = lo + 1 := by
      have h1 : lo < ⌈s⌉ := Int.lt_ceil.mpr (lt_of_le_of_ne h_floor_le_s hs_ne)
      have h2 : ⌈s⌉ ≤ lo + 1 := Int.ceil_le_floor_add_one s
      omega
    have hh := ceil_minimality F x hz_prec hz_quant hx_le_z
    have h_subst : ((lo + 1 : ℤ) : ℝ) = ((⌈s⌉ : ℤ) : ℝ) := by exact_mod_cast h_ceil_eq.symm
    rw [h_subst]
    convert hh using 2
  have h_faithful_eq : ∀ y : Dyadic, IsFaithfulRound F.unbounded x y →
      y = dlo ∨ y = dhi := by
    intro y hf
    rcases isFaithfulRound_iff_directed.mp hf with hdn | hup
    · exact Or.inl (RoundsFinite.unique_toNegative hdn h_dn)
    · by_cases hs_eq : (lo : ℝ) = s
      · -- `x` sits on the grid at `dlo`, so its round-up is `dlo` too.
        have hx_eq : x = (dlo : ℝ) := by rw [h_dlo_real, hs_eq, h_s_unscale]
        exact Or.inl (RoundsFinite.unique_toPositive hup
          ⟨h_dlo_mem, hx_eq.le, fun z _ hz => by rw [← hx_eq]; exact hz⟩)
      · exact Or.inr (RoundsFinite.unique_toPositive hup
          ⟨h_dhi_mem, h_x_le_dhi, h_dhi_round_up hs_eq⟩)
  exact ⟨h_2e_pos, h_dlo_mem, h_dhi_mem, h_dlo_real, h_dhi_real, h_floor_le_s,
         h_s_lt_succ, h_s_unscale, h_dlo_le_x, h_x_le_dhi, h_dlo_round_down,
         h_dhi_round_up, h_faithful_eq⟩

theorem rndUnbounded_satisfies_nearest (F : FiniteFormat) (tb : TieBreak) (x : ℝ)
    (h : ¬ F.IsUndefined (.nearest tb)) :
    RoundsFinite F.unbounded (.nearest tb) x (rndUnbounded F (.nearest tb) x h) := by
  -- Setup mirrors `rndUnbounded_satisfies_toOdd`.
  set e := F.canonicalExp x with h_e_def
  set s := x * (2 : ℝ) ^ (-e) with h_s_def
  set lo : ℤ := ⌊s⌋ with h_lo_def
  set dlo : Dyadic := Dyadic.ofIntZpow lo e with h_dlo_def
  set dhi : Dyadic := Dyadic.ofIntZpow (lo + 1) e with h_dhi_def
  obtain ⟨h_2e_pos, h_dlo_mem, h_dhi_mem, h_dlo_real, h_dhi_real, h_floor_le_s,
      h_s_lt_succ, h_s_unscale, h_dlo_le_x, h_x_le_dhi, h_dlo_round_down,
      h_dhi_round_up, h_faithful_eq⟩ :=
    nearest_neighbors_setup F x h_e_def h_s_def h_lo_def h_dlo_def h_dhi_def
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
    set F'' := F.toParityFormatOfNearestEven h with hF''_def
    set F' := F.unbounded.toParityFormatOfNearestEven h with hF'_def
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
            -- Alternation from the shared `nearest .toEven` dispatch lemma.
            have hx_ne : x ≠ 0 := by
              intro hx0
              subst hx0
              have h_s_zero : s = 0 := by change (0 : ℝ) * (2 : ℝ) ^ (-e) = 0; ring
              have h_δ_zero_lo : δ = -lo := by
                change s - (lo : ℝ) = -lo
                rw [h_s_zero]; ring
              rw [h_δ_zero_lo] at h_δ_eq
              have h_2lo_neg1 : 2 * lo = -1 := by
                have h_real : (2 * lo : ℝ) = -1 := by linarith
                exact_mod_cast h_real
              omega
            exact (nearest_toEven_neighbors_alternate x h hx_ne h_lo_ne_s).2 h_even_dlo


end Mpfx
