import Mpfx.DoubleRounding.Basic

/-!
# `rnd-RTO-RNE` / `rnd-RTO-RNA` (§5.2)

`roundsRTO_RN_finite`: round-to-odd in `F₂` then round-to-nearest in `F₁` (either
tie-break) is correct double rounding.
-/

namespace Mpfx

/-! ## Round-to-nearest helpers for `roundsRTO_RN_finite` -/

/-- Helper for tie-break: from `|x - w'| = |x - z'|` with `w' ≠ z'`, derive
`x = (w' + z') / 2`. -/
private theorem nearest_midpoint_of_tie {x : ℝ} {w' z' : Dyadic}
    (h_ne : z' ≠ w') (h_tie : |x - (w' : ℝ)| = |x - (z' : ℝ)|) :
    x = ((w' : ℝ) + (z' : ℝ)) / 2 := by
  rcases abs_eq_abs.mp h_tie with h1 | h1
  · -- x - w' = x - z' ⇒ w' = z', contradicting h_ne
    have hwz : (w' : ℝ) = (z' : ℝ) := by linarith
    exact absurd ((Dyadic.coe_real_inj w' z').mp hwz).symm h_ne
  · -- x - w' = -(x - z') ⇒ 2x = w' + z'
    linarith

/-- F-adjacency of `(w', z')` in `F₁`: no F₁ element strictly between. Derived
from `RTN w'` ∨ `RTP w'` and `RTN z'` ∨ `RTP z'` for `x`, when `w' ≤ x ≤ z'`:
any F₁-`y` with `w' < y` must be `≥ z'`. -/
private theorem F_adjacent_of_RN_round_pair {F₁ : FiniteFormat}
    {x : ℝ} {w' z' : Dyadic}
    (hw'_adj : RoundsFinite F₁ .toNegative x w' ∨ RoundsFinite F₁ .toPositive x w')
    (hz'_adj : RoundsFinite F₁ .toNegative x z' ∨ RoundsFinite F₁ .toPositive x z')
    (hw'_le_x : (w' : ℝ) ≤ x) (hx_le_z' : x ≤ (z' : ℝ)) :
    ∀ y : Dyadic, y ∈ F₁ → (w' : ℝ) < (y : ℝ) → (z' : ℝ) ≤ (y : ℝ) := by
  intro y hyF₁ h_w_lt_y
  by_cases h_y_le_x : (y : ℝ) ≤ x
  · -- y ≤ x. By RTN w' (or via RTP w' contradicting w' ≤ x), y ≤ w'.
    exfalso
    rcases hw'_adj with hwRD | hwRU
    · obtain ⟨_, _, hw_max⟩ := hwRD
      have h_y_le_w' : (y : ℝ) ≤ (w' : ℝ) := hw_max y hyF₁ h_y_le_x
      linarith
    · obtain ⟨_, hxw, _⟩ := hwRU
      have hxw' : x = (w' : ℝ) := le_antisymm hxw hw'_le_x
      rw [← hxw'] at h_w_lt_y
      linarith
  · push Not at h_y_le_x
    -- y > x. By RTP z' (or RTN z' contradicting), z' ≤ y.
    rcases hz'_adj with hzRD | hzRU
    · obtain ⟨_, hzx_le, _⟩ := hzRD
      have hxz' : x = (z' : ℝ) := le_antisymm hx_le_z' hzx_le
      linarith
    · obtain ⟨_, _, hz_min⟩ := hzRU
      exact hz_min y hyF₁ (le_of_lt h_y_le_x)

/-- F-adjacent midpoint membership in `F₂`. Gets `midpoint y₁ y₂ ∈ F₁.extend 1`
from `Mpfx/Format/Discrete.lean` (dispatching on `F₁`'s precision/exponent shape) and then
applies the subset hypothesis. -/
private theorem midpoint_F₁_in_F₂_of_F_adjacent {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat)
    {y₁ y₂ : Dyadic} (hy₁F : y₁ ∈ F₁) (hy₂F : y₂ ∈ F₁)
    (h_lt : (y₁ : ℝ) < (y₂ : ℝ))
    (h_adj : ∀ y : Dyadic, y ∈ F₁ → (y₁ : ℝ) < (y : ℝ) → (y₂ : ℝ) ≤ (y : ℝ)) :
    Dyadic.midpoint y₁ y₂ ∈ F₂ :=
  hsub _ (midpoint_in_F₁_extend_one_of_F_adjacent hy₁F hy₂F h_lt h_adj)

/-- If `F₁` is trivial (contains only `0`) then `RoundsFinite F₁ (.nearest tb) x w'`
holds for any real `x` and tie-break `tb`, whenever `w' ∈ F₁` (so `w' = 0`).
The closeness and tie-break conditions are vacuous; faithfulness holds by the
round-down branch (`x ≥ 0`) or round-up branch (`x < 0`). -/
private theorem RoundsFinite.nearest_of_trivial {F₁ : FiniteFormat} {tb : TieBreak}
    (hF₁_triv : ∀ d : Dyadic, d ∈ F₁ → (d : ℝ) = 0)
    {x : ℝ} {w' : Dyadic} (hw : w' ∈ F₁) :
    RoundsFinite F₁ (.nearest tb) x w' := by
  have hw'_zero : (w' : ℝ) = 0 := hF₁_triv w' hw
  -- Every F₁ element equals w' (both are 0).
  have h_eq_w' : ∀ z : Dyadic, z ∈ F₁ → z = w' := fun z hzF₁ =>
    (Dyadic.coe_real_inj z w').mp (by rw [hF₁_triv z hzF₁, hw'_zero])
  -- Shared faithfulness.
  have h_adj : IsFaithfulRound F₁ x w' := by
    rcases lt_or_ge x 0 with hx_neg | hx_nn
    · right
      refine ⟨hw, by rw [hw'_zero]; linarith, ?_⟩
      intro v hvF₁ _
      rw [hF₁_triv v hvF₁, hw'_zero]
    · left
      refine ⟨hw, by rw [hw'_zero]; exact hx_nn, ?_⟩
      intro v hvF₁ _
      rw [hF₁_triv v hvF₁, hw'_zero]
  -- Shared closeness.
  have h_close : ∀ z : Dyadic, z ∈ F₁ → IsFaithfulRound F₁ x z →
      |x - (w' : ℝ)| ≤ |x - (z : ℝ)| := by
    intro z hzF₁ _
    rw [hF₁_triv z hzF₁, hw'_zero]
  -- Dispatch on tb only for the tie-break clause shape.
  cases tb with
  | toEven =>
    refine ⟨hw, h_adj, h_close, ?_⟩
    rintro ⟨z, hzF₁, _, hz_ne_w', _⟩
    exact (hz_ne_w' (h_eq_w' z hzF₁)).elim
  | awayZero =>
    refine ⟨hw, h_adj, h_close, ?_⟩
    intro z hzF₁ _ hz_ne_w' _
    exact (hz_ne_w' (h_eq_w' z hzF₁)).elim

/-! ## `rnd-RTO-RN` — round-to-odd then round-to-nearest -/

/-- The closeness transfer step for `roundsRTO_RN_finite`: given that `z = RTO F₂ x`
sits outside `F₁.extend 1` (RTO-padding lemma) and `w' = RN F₁ z`, every F₁-adjacent
`z'` to `x` satisfies `|x - w'| ≤ |x - z'|`. The argument uses the midpoint
`m = (w' + z') / 2` (in F₂ via `midpoint_F₁_in_F₂_of_F_adjacent`, in
`F₁.extend 1` via `midpoint_in_F₁_extend_one_of_F_adjacent`), shows
`z ≠ m`, and concludes `x` lies on `w'`'s side of `m`. -/
private lemma rndRTO_RN_close_transfer {F₁ F₂ : FiniteFormat}
    (hsub_ext1 : (F₁.extend 1).toFormat ⊆ F₂.toFormat)
    (hsub' : F₁.toFormat ⊆ F₂.toFormat)
    (hF₁_sub_ext1 : F₁.toFormat ⊆ (F₁.extend 1).toFormat)
    {x : ℝ} {z w' : Dyadic}
    (hz_adj : RoundsFinite F₂ .toNegative x z ∨ RoundsFinite F₂ .toPositive x z)
    (hw'F₁ : w' ∈ F₁)
    (h_adj_x : RoundsFinite F₁ .toNegative x w' ∨ RoundsFinite F₁ .toPositive x w')
    (hw_close_inner : ∀ z' : Dyadic, z' ∈ F₁ →
        (RoundsFinite F₁ .toNegative ((z : Dyadic) : ℝ) z'
          ∨ RoundsFinite F₁ .toPositive ((z : Dyadic) : ℝ) z') →
        |((z : Dyadic) : ℝ) - ((w' : Dyadic) : ℝ)| ≤
            |((z : Dyadic) : ℝ) - ((z' : Dyadic) : ℝ)|)
    (hz_not_F₁_ext1 : z ∉ F₁.extend 1) :
    ∀ z' : Dyadic, z' ∈ F₁ →
      (RoundsFinite F₁ .toNegative x z' ∨ RoundsFinite F₁ .toPositive x z') →
      |x - ((w' : Dyadic) : ℝ)| ≤ |x - ((z' : Dyadic) : ℝ)| := by
  intro z' hz'F₁ hz'_adj
  by_cases h_eq : ((z' : Dyadic) : ℝ) = ((w' : Dyadic) : ℝ)
  · rw [h_eq]
  · have h_w_ne_z' : ((w' : Dyadic) : ℝ) ≠ ((z' : Dyadic) : ℝ) := fun h => h_eq h.symm
    have h_z_ne_w'_real : ((z : Dyadic) : ℝ) ≠ ((w' : Dyadic) : ℝ) := by
      intro h
      apply hz_not_F₁_ext1
      have hzw : z = w' := (Dyadic.coe_real_inj z w').mp h
      rw [hzw]; exact hF₁_sub_ext1 _ hw'F₁
    have h_z_ne_z'_real : ((z : Dyadic) : ℝ) ≠ ((z' : Dyadic) : ℝ) := by
      intro h
      apply hz_not_F₁_ext1
      have hzz' : z = z' := (Dyadic.coe_real_inj z z').mp h
      rw [hzz']; exact hF₁_sub_ext1 _ hz'F₁
    have hw'F₂ : w' ∈ F₂ := hsub' _ hw'F₁
    have hz'F₂ : z' ∈ F₂ := hsub' _ hz'F₁
    rcases lt_or_gt_of_ne h_w_ne_z' with h_w_lt_z | h_z_lt_w
    · have hwRD : RoundsFinite F₁ .toNegative x w' := by
        rcases h_adj_x with hwRD | hwRU
        · exact hwRD
        · exfalso
          rcases hz'_adj with hzRD | hzRU
          · linarith [hwRU.2.1, hzRD.2.1]
          · have h1 : ((w' : Dyadic) : ℝ) ≤ ((z' : Dyadic) : ℝ) :=
              hwRU.2.2 z' hz'F₁ hzRU.2.1
            have h2 : ((z' : Dyadic) : ℝ) ≤ ((w' : Dyadic) : ℝ) :=
              hzRU.2.2 w' hw'F₁ hwRU.2.1
            exact h_w_ne_z' (le_antisymm h1 h2)
      have hzRU : RoundsFinite F₁ .toPositive x z' := by
        rcases hz'_adj with hzRD | hzRU
        · exfalso
          have h1 : ((w' : Dyadic) : ℝ) ≤ ((z' : Dyadic) : ℝ) :=
            hzRD.2.2 w' hw'F₁ hwRD.2.1
          have h2 : ((z' : Dyadic) : ℝ) ≤ ((w' : Dyadic) : ℝ) :=
            hwRD.2.2 z' hz'F₁ hzRD.2.1
          exact h_w_ne_z' (le_antisymm h1 h2)
        · exact hzRU
      have h_w_le_x : ((w' : Dyadic) : ℝ) ≤ x := hwRD.2.1
      have h_x_le_z : x ≤ ((z' : Dyadic) : ℝ) := hzRU.2.1
      have h_F_adj : ∀ y : Dyadic, y ∈ F₁ →
          ((w' : Dyadic) : ℝ) < ((y : Dyadic) : ℝ) →
          ((z' : Dyadic) : ℝ) ≤ ((y : Dyadic) : ℝ) :=
        F_adjacent_of_RN_round_pair (Or.inl hwRD) (Or.inr hzRU) h_w_le_x h_x_le_z
      have h_mid_F₂ : Dyadic.midpoint w' z' ∈ F₂ :=
        midpoint_F₁_in_F₂_of_F_adjacent hsub_ext1 hw'F₁ hz'F₁
          h_w_lt_z h_F_adj
      have h_mid_F₁_ext1 : Dyadic.midpoint w' z' ∈ F₁.extend 1 :=
        midpoint_in_F₁_extend_one_of_F_adjacent hw'F₁ hz'F₁
          h_w_lt_z h_F_adj
      have h_mid_real : ((Dyadic.midpoint w' z' : Dyadic) : ℝ) =
          (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2 := Dyadic.coe_midpoint w' z'
      have h_z_ne_m : ((z : Dyadic) : ℝ) ≠ ((Dyadic.midpoint w' z' : Dyadic) : ℝ) := by
        intro h_eq_m
        apply hz_not_F₁_ext1
        have : z = Dyadic.midpoint w' z' := (Dyadic.coe_real_inj z _).mp h_eq_m
        rw [this]; exact h_mid_F₁_ext1
      have h_w_le_z_F : ((w' : Dyadic) : ℝ) ≤ ((z : Dyadic) : ℝ) := by
        rcases hz_adj with hzRD' | hzRU'
        · exact hzRD'.2.2 w' hw'F₂ h_w_le_x
        · linarith [hzRU'.2.1]
      have h_z_le_z'_F : ((z : Dyadic) : ℝ) ≤ ((z' : Dyadic) : ℝ) := by
        rcases hz_adj with hzRD' | hzRU'
        · linarith [hzRD'.2.1]
        · exact hzRU'.2.2 z' hz'F₂ h_x_le_z
      have h_w_lt_z_F : ((w' : Dyadic) : ℝ) < ((z : Dyadic) : ℝ) :=
        lt_of_le_of_ne h_w_le_z_F (Ne.symm h_z_ne_w'_real)
      have h_z_lt_z' : ((z : Dyadic) : ℝ) < ((z' : Dyadic) : ℝ) :=
        lt_of_le_of_ne h_z_le_z'_F h_z_ne_z'_real
      have hz_RU_z' : RoundsFinite F₁ .toPositive z z' := by
        refine ⟨hz'F₁, le_of_lt h_z_lt_z', ?_⟩
        intro y hyF₁ h_z_le_y
        have h_w_lt_y : ((w' : Dyadic) : ℝ) < ((y : Dyadic) : ℝ) := by linarith
        exact h_F_adj y hyF₁ h_w_lt_y
      have h_z_close : |((z : Dyadic) : ℝ) - ((w' : Dyadic) : ℝ)|
          ≤ |((z : Dyadic) : ℝ) - ((z' : Dyadic) : ℝ)| :=
        hw_close_inner z' hz'F₁ (Or.inr hz_RU_z')
      have h_z_w_pos : 0 < ((z : Dyadic) : ℝ) - ((w' : Dyadic) : ℝ) := by linarith
      have h_z_z_neg : ((z : Dyadic) : ℝ) - ((z' : Dyadic) : ℝ) < 0 := by linarith
      rw [abs_of_pos h_z_w_pos, abs_of_neg h_z_z_neg] at h_z_close
      have h_z_le_m : ((z : Dyadic) : ℝ)
          ≤ (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2 := by linarith
      have h_z_lt_m : ((z : Dyadic) : ℝ)
          < (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2 := by
        have : ((z : Dyadic) : ℝ) ≠ (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2 := by
          rw [← h_mid_real]; exact h_z_ne_m
        exact lt_of_le_of_ne h_z_le_m this
      have h_x_le_m : x ≤ (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2 := by
        rcases hz_adj with hzRD' | hzRU'
        · by_contra h_x_gt
          push Not at h_x_gt
          have h_m_le_x : (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2 ≤ x :=
            le_of_lt h_x_gt
          have h_m_le_x' : ((Dyadic.midpoint w' z' : Dyadic) : ℝ) ≤ x := by
            rw [h_mid_real]; exact h_m_le_x
          have h_m_le_z : ((Dyadic.midpoint w' z' : Dyadic) : ℝ) ≤ ((z : Dyadic) : ℝ) :=
            hzRD'.2.2 (Dyadic.midpoint w' z') h_mid_F₂ h_m_le_x'
          rw [h_mid_real] at h_m_le_z
          linarith
        · linarith [hzRU'.2.1]
      have h_x_w_pos : 0 ≤ x - ((w' : Dyadic) : ℝ) := by linarith
      have h_x_z_nonpos : x - ((z' : Dyadic) : ℝ) ≤ 0 := by linarith
      rw [abs_of_nonneg h_x_w_pos, abs_of_nonpos h_x_z_nonpos]
      linarith
    · have hwRU : RoundsFinite F₁ .toPositive x w' := by
        rcases h_adj_x with hwRD | hwRU
        · exfalso
          rcases hz'_adj with hzRD | hzRU
          · have h1 : ((w' : Dyadic) : ℝ) ≤ ((z' : Dyadic) : ℝ) :=
              hzRD.2.2 w' hw'F₁ hwRD.2.1
            have h2 : ((z' : Dyadic) : ℝ) ≤ ((w' : Dyadic) : ℝ) :=
              hwRD.2.2 z' hz'F₁ hzRD.2.1
            exact h_w_ne_z' (le_antisymm h1 h2)
          · linarith [hwRD.2.1, hzRU.2.1]
        · exact hwRU
      have hzRD : RoundsFinite F₁ .toNegative x z' := by
        rcases hz'_adj with hzRD | hzRU
        · exact hzRD
        · exfalso
          have h1 : ((w' : Dyadic) : ℝ) ≤ ((z' : Dyadic) : ℝ) :=
            hwRU.2.2 z' hz'F₁ hzRU.2.1
          have h2 : ((z' : Dyadic) : ℝ) ≤ ((w' : Dyadic) : ℝ) :=
            hzRU.2.2 w' hw'F₁ hwRU.2.1
          exact h_w_ne_z' (le_antisymm h1 h2)
      have h_x_le_w : x ≤ ((w' : Dyadic) : ℝ) := hwRU.2.1
      have h_z_le_x : ((z' : Dyadic) : ℝ) ≤ x := hzRD.2.1
      have h_F_adj : ∀ y : Dyadic, y ∈ F₁ →
          ((z' : Dyadic) : ℝ) < ((y : Dyadic) : ℝ) →
          ((w' : Dyadic) : ℝ) ≤ ((y : Dyadic) : ℝ) :=
        F_adjacent_of_RN_round_pair (Or.inl hzRD) (Or.inr hwRU) h_z_le_x h_x_le_w
      have h_mid_F₂_swap : Dyadic.midpoint z' w' ∈ F₂ :=
        midpoint_F₁_in_F₂_of_F_adjacent hsub_ext1 hz'F₁ hw'F₁
          h_z_lt_w h_F_adj
      have h_mid_F₁_ext1_swap : Dyadic.midpoint z' w' ∈ F₁.extend 1 :=
        midpoint_in_F₁_extend_one_of_F_adjacent hz'F₁ hw'F₁
          h_z_lt_w h_F_adj
      have h_mid_swap_eq : Dyadic.midpoint z' w' = Dyadic.midpoint w' z' :=
        Dyadic.midpoint_comm z' w'
      have h_mid_F₂ : Dyadic.midpoint w' z' ∈ F₂ := h_mid_swap_eq ▸ h_mid_F₂_swap
      have h_mid_F₁_ext1 : Dyadic.midpoint w' z' ∈ F₁.extend 1 :=
        h_mid_swap_eq ▸ h_mid_F₁_ext1_swap
      have h_mid_real : ((Dyadic.midpoint w' z' : Dyadic) : ℝ) =
          (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2 := Dyadic.coe_midpoint w' z'
      have h_z_ne_m : ((z : Dyadic) : ℝ) ≠ ((Dyadic.midpoint w' z' : Dyadic) : ℝ) := by
        intro h_eq_m
        apply hz_not_F₁_ext1
        have : z = Dyadic.midpoint w' z' := (Dyadic.coe_real_inj z _).mp h_eq_m
        rw [this]; exact h_mid_F₁_ext1
      have h_z_le_w_F : ((z : Dyadic) : ℝ) ≤ ((w' : Dyadic) : ℝ) := by
        rcases hz_adj with hzRD' | hzRU'
        · linarith [hzRD'.2.1]
        · exact hzRU'.2.2 w' hw'F₂ h_x_le_w
      have h_z'_le_z_F : ((z' : Dyadic) : ℝ) ≤ ((z : Dyadic) : ℝ) := by
        rcases hz_adj with hzRD' | hzRU'
        · exact hzRD'.2.2 z' hz'F₂ h_z_le_x
        · linarith [hzRU'.2.1]
      have h_z_lt_w_F : ((z : Dyadic) : ℝ) < ((w' : Dyadic) : ℝ) :=
        lt_of_le_of_ne h_z_le_w_F h_z_ne_w'_real
      have h_z'_lt_z : ((z' : Dyadic) : ℝ) < ((z : Dyadic) : ℝ) :=
        lt_of_le_of_ne h_z'_le_z_F (Ne.symm h_z_ne_z'_real)
      have hz_RD_z' : RoundsFinite F₁ .toNegative z z' := by
        refine ⟨hz'F₁, le_of_lt h_z'_lt_z, ?_⟩
        intro y hyF₁ h_y_le_z
        by_contra h_lt
        push Not at h_lt
        have h_w_le_y := h_F_adj y hyF₁ h_lt
        linarith
      have h_z_close : |((z : Dyadic) : ℝ) - ((w' : Dyadic) : ℝ)|
          ≤ |((z : Dyadic) : ℝ) - ((z' : Dyadic) : ℝ)| :=
        hw_close_inner z' hz'F₁ (Or.inl hz_RD_z')
      have h_z_w_neg : ((z : Dyadic) : ℝ) - ((w' : Dyadic) : ℝ) < 0 := by linarith
      have h_z_z_pos : 0 < ((z : Dyadic) : ℝ) - ((z' : Dyadic) : ℝ) := by linarith
      rw [abs_of_neg h_z_w_neg, abs_of_pos h_z_z_pos] at h_z_close
      have h_m_le_z : (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2
          ≤ ((z : Dyadic) : ℝ) := by linarith
      have h_m_lt_z : (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2
          < ((z : Dyadic) : ℝ) := by
        have : (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2 ≠ ((z : Dyadic) : ℝ) := by
          intro h_eq2
          rw [← h_mid_real] at h_eq2
          exact h_z_ne_m h_eq2.symm
        exact lt_of_le_of_ne h_m_le_z this
      have h_m_le_x : (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2 ≤ x := by
        rcases hz_adj with hzRD' | hzRU'
        · linarith [hzRD'.2.1]
        · by_contra h_x_lt
          push Not at h_x_lt
          have h_x_le_m : x ≤ (((w' : Dyadic) : ℝ) + ((z' : Dyadic) : ℝ)) / 2 :=
            le_of_lt h_x_lt
          have h_x_le_m' : x ≤ ((Dyadic.midpoint w' z' : Dyadic) : ℝ) := by
            rw [h_mid_real]; exact h_x_le_m
          have h_z_le_m : ((z : Dyadic) : ℝ) ≤ ((Dyadic.midpoint w' z' : Dyadic) : ℝ) :=
            hzRU'.2.2 (Dyadic.midpoint w' z') h_mid_F₂ h_x_le_m'
          rw [h_mid_real] at h_z_le_m
          linarith
      have h_x_w_neg : x - ((w' : Dyadic) : ℝ) ≤ 0 := by linarith
      have h_x_z_pos : 0 ≤ x - ((z' : Dyadic) : ℝ) := by linarith
      rw [abs_of_nonpos h_x_w_neg, abs_of_nonneg h_x_z_pos]
      linarith

/-- The "no-tie" derivation used by the nearest-rounding branch of `roundsRTO_RN_finite`.
Given that `z = RTO F₂ x` is unrepresentable in `F₁` and that `z'` is supposedly
tied with `w'` for `x`'s nearest-rounding in `F₁`, derive `False`: the tie
equation forces `x = midpoint(w', z')`, F-adjacency makes that midpoint lie in
`F₂`, and `RoundsFinite.toOdd_unique_of_mem` then forces `z = midpoint`, so
`x = z`, contradicting `hxne`. -/
private lemma rndRTO_no_tie_contradiction {F₁ F₂ : FiniteFormat}
    (hsub_ext1 : (F₁.extend 1).toFormat ⊆ F₂.toFormat)
    {x : ℝ} {z w' z' : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hxne : x ≠ (z : ℝ))
    (hw'F₁ : w' ∈ F₁) (hz'F₁ : z' ∈ F₁)
    (h_adj_x : RoundsFinite F₁ .toNegative x w' ∨ RoundsFinite F₁ .toPositive x w')
    (hz'_adj : RoundsFinite F₁ .toNegative x z' ∨ RoundsFinite F₁ .toPositive x z')
    (hz'_ne_w' : z' ≠ w')
    (hz'_eq_dist : |x - ((w' : Dyadic) : ℝ)| = |x - ((z' : Dyadic) : ℝ)|) :
    False := by
  have hx_mid : x = ((w' : ℝ) + (z' : ℝ)) / 2 :=
    nearest_midpoint_of_tie hz'_ne_w' hz'_eq_dist
  have hw'_ne_z'_real : ((w' : Dyadic) : ℝ) ≠ ((z' : Dyadic) : ℝ) := by
    intro heq
    apply hz'_ne_w'
    exact (Dyadic.coe_real_inj z' w').mp heq.symm
  -- F-adjacency: between w' and z' (in either order), no F₁ element strictly between.
  have h_F_adj_pair : ∀ (a b : Dyadic), a ∈ F₁ → b ∈ F₁ →
      ((a : ℝ) = (w' : ℝ) ∧ (b : ℝ) = (z' : ℝ)) ∨
        ((a : ℝ) = (z' : ℝ) ∧ (b : ℝ) = (w' : ℝ)) →
      ((a : Dyadic) : ℝ) < ((b : Dyadic) : ℝ) →
      ∀ y : Dyadic, y ∈ F₁ → ((a : Dyadic) : ℝ) < ((y : Dyadic) : ℝ) →
        ((b : Dyadic) : ℝ) ≤ ((y : Dyadic) : ℝ) := by
    intro a b haF₁ hbF₁ h_ab_eq h_ab_lt y hyF₁ h_a_lt_y
    have hx_mid' : x = ((a : ℝ) + (b : ℝ)) / 2 := by
      rcases h_ab_eq with ⟨ha_eq, hb_eq⟩ | ⟨ha_eq, hb_eq⟩
      · rw [ha_eq, hb_eq]; exact hx_mid
      · rw [ha_eq, hb_eq, hx_mid]; ring
    have h_a_lt_x : (a : ℝ) < x := by rw [hx_mid']; linarith
    have h_x_lt_b : x < (b : ℝ) := by rw [hx_mid']; linarith
    by_cases h_y_le_x : ((y : Dyadic) : ℝ) ≤ x
    · exfalso
      rcases h_ab_eq with ⟨ha_eq, _⟩ | ⟨ha_eq, _⟩
      · rcases h_adj_x with hwRD | hwRU
        · obtain ⟨_, _, hw_max⟩ := hwRD
          have h_y_le_w' : ((y : Dyadic) : ℝ) ≤ (w' : ℝ) := hw_max y hyF₁ h_y_le_x
          rw [ha_eq] at h_a_lt_y
          linarith
        · obtain ⟨_, hxw, _⟩ := hwRU
          rw [ha_eq] at h_a_lt_x
          linarith
      · rcases hz'_adj with hzRD | hzRU
        · obtain ⟨_, _, hz_max⟩ := hzRD
          have h_y_le_z' : ((y : Dyadic) : ℝ) ≤ (z' : ℝ) := hz_max y hyF₁ h_y_le_x
          rw [ha_eq] at h_a_lt_y
          linarith
        · obtain ⟨_, hxz, _⟩ := hzRU
          rw [ha_eq] at h_a_lt_x
          linarith
    · push Not at h_y_le_x
      rcases h_ab_eq with ⟨_, hb_eq⟩ | ⟨_, hb_eq⟩
      · rcases hz'_adj with hzRD | hzRU
        · obtain ⟨_, hzx_le, _⟩ := hzRD
          rw [hb_eq] at h_x_lt_b
          linarith
        · obtain ⟨_, _, hz_min⟩ := hzRU
          have h_z'_le_y : (z' : ℝ) ≤ ((y : Dyadic) : ℝ) := hz_min y hyF₁ (le_of_lt h_y_le_x)
          rw [hb_eq]; exact h_z'_le_y
      · rcases h_adj_x with hwRD | hwRU
        · obtain ⟨_, hwx_le, _⟩ := hwRD
          rw [hb_eq] at h_x_lt_b
          linarith
        · obtain ⟨_, _, hw_min⟩ := hwRU
          have h_w'_le_y : (w' : ℝ) ≤ ((y : Dyadic) : ℝ) := hw_min y hyF₁ (le_of_lt h_y_le_x)
          rw [hb_eq]; exact h_w'_le_y
  have h_mid_F₂ : Dyadic.midpoint w' z' ∈ F₂ := by
    rcases lt_or_gt_of_ne hw'_ne_z'_real with h_w_lt_z | h_z_lt_w
    · have h_adj_pair := h_F_adj_pair w' z' hw'F₁ hz'F₁
        (Or.inl ⟨rfl, rfl⟩) h_w_lt_z
      exact midpoint_F₁_in_F₂_of_F_adjacent hsub_ext1 hw'F₁ hz'F₁
        h_w_lt_z h_adj_pair
    · have h_mid_swap : Dyadic.midpoint w' z' = Dyadic.midpoint z' w' :=
        Dyadic.midpoint_comm w' z'
      rw [h_mid_swap]
      have h_adj_pair := h_F_adj_pair z' w' hz'F₁ hw'F₁
        (Or.inr ⟨rfl, rfl⟩) h_z_lt_w
      exact midpoint_F₁_in_F₂_of_F_adjacent hsub_ext1 hz'F₁ hw'F₁
        h_z_lt_w h_adj_pair
  set m := Dyadic.midpoint w' z' with hm_def
  have hm_eq : ((m : Dyadic) : ℝ) = ((w' : ℝ) + (z' : ℝ)) / 2 := by
    rw [hm_def, Dyadic.coe_midpoint]
  have hm_x : (m : ℝ) = x := by rw [hm_eq, ← hx_mid]
  have hz_eq : z = m := by
    have hz' : RoundsFinite F₂ .toOdd ((m : ℝ)) z := by rw [hm_x]; exact hz
    exact RoundsFinite.toOdd_unique_of_mem h_mid_F₂ hz'
  exact hxne (by rw [hz_eq]; exact hm_x.symm)

/-- Shared core for the nearest-rounding branch of `roundsRTO_RN_finite`. From the
derived subset facts plus extracted hypotheses from the inner nearest-rounding,
produces the three facts needed by either tie-break: adjacency transfer
(`h_adj_x`), closeness transfer (`h_close`), and an absence-of-tie property
(`h_no_tie`). -/
private theorem rndRTO_nearest_facts {F₁ F₂ : FiniteFormat}
    (hsub2 : (F₁.extend 2).toFormat ⊆ F₂.toFormat)
    (hsub_ext1 : (F₁.extend 1).toFormat ⊆ F₂.toFormat)
    (hsub' : F₁.toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {x : ℝ} {z w' : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hxne : x ≠ (z : ℝ))
    (hw'F₁ : w' ∈ F₁)
    (hw_adj : RoundsFinite F₁ .toNegative ((z : Dyadic) : ℝ) w'
              ∨ RoundsFinite F₁ .toPositive ((z : Dyadic) : ℝ) w')
    (hw_close_inner : ∀ z' : Dyadic, z' ∈ F₁ →
        (RoundsFinite F₁ .toNegative ((z : Dyadic) : ℝ) z'
          ∨ RoundsFinite F₁ .toPositive ((z : Dyadic) : ℝ) z') →
        |((z : Dyadic) : ℝ) - ((w' : Dyadic) : ℝ)| ≤
            |((z : Dyadic) : ℝ) - ((z' : Dyadic) : ℝ)|) :
    (RoundsFinite F₁ .toNegative x w' ∨ RoundsFinite F₁ .toPositive x w') ∧
    (∀ z' : Dyadic, z' ∈ F₁ →
        (RoundsFinite F₁ .toNegative x z' ∨ RoundsFinite F₁ .toPositive x z') →
        |x - ((w' : Dyadic) : ℝ)| ≤ |x - ((z' : Dyadic) : ℝ)|) ∧
    (∀ z' : Dyadic, z' ∈ F₁ →
        (RoundsFinite F₁ .toNegative x z' ∨ RoundsFinite F₁ .toPositive x z') →
        z' ≠ w' →
        |x - ((w' : Dyadic) : ℝ)| = |x - ((z' : Dyadic) : ℝ)| → False) := by
  have hF₁_sub_ext1 : F₁.toFormat ⊆ (F₁.extend 1).toFormat :=
    Format.self_subset_extend F₁.toFormat 1
  have hz_not_F₁ : z ∉ F₁ :=
    toOdd_notMem_of_extend_subset hsub_ext1 hp_F₂ hz hxne
  have hz_adj : RoundsFinite F₂ .toNegative x z ∨ RoundsFinite F₂ .toPositive x z :=
    isFaithfulRound_iff_directed.mp hz.2.1
  have hz_ne_w' : (z : ℝ) ≠ (w' : ℝ) := by
    intro h_eq
    apply hz_not_F₁
    rw [show z = w' from (Dyadic.coe_real_inj z w').mp h_eq]
    exact hw'F₁
  -- Adjacency transfer (4-way case split).
  have h_adj_x : RoundsFinite F₁ .toNegative x w' ∨ RoundsFinite F₁ .toPositive x w' := by
    rcases hz_adj with hzRD | hzRU
    · rcases hw_adj with hwRD | hwRU
      · left
        obtain ⟨_, hwz, hw_max⟩ := hwRD
        have hzx_le := hzRD.2.1
        refine ⟨hw'F₁, le_trans hwz hzx_le, ?_⟩
        intro v hvF₁ hvx
        exact hw_max v hvF₁ (hzRD.2.2 v (hsub' _ hvF₁) hvx)
      · obtain ⟨_, hzw, hw_min⟩ := hwRU
        by_cases hw'_le_x : (w' : ℝ) ≤ x
        · exfalso
          have hw_le_z : (w' : ℝ) ≤ (z : ℝ) := hzRD.2.2 w' (hsub' _ hw'F₁) hw'_le_x
          exact hz_ne_w' (le_antisymm hw_le_z hzw).symm
        · push Not at hw'_le_x
          right
          refine ⟨hw'F₁, hw'_le_x.le, ?_⟩
          intro v hvF₁ hxv
          exact hw_min v hvF₁ (le_trans hzRD.2.1 hxv)
    · rcases hw_adj with hwRD | hwRU
      · obtain ⟨_, hwz, hw_max⟩ := hwRD
        by_cases hw'_le_x : (w' : ℝ) ≤ x
        · left
          refine ⟨hw'F₁, hw'_le_x, ?_⟩
          intro v hvF₁ hvx
          exact hw_max v hvF₁ (le_trans hvx hzRU.2.1)
        · exfalso
          push Not at hw'_le_x
          have hw_ge_z : (z : ℝ) ≤ (w' : ℝ) :=
            hzRU.2.2 w' (hsub' _ hw'F₁) hw'_le_x.le
          exact hz_ne_w' (le_antisymm hwz hw_ge_z).symm
      · right
        obtain ⟨_, hzw, hw_min⟩ := hwRU
        have hxz := hzRU.2.1
        refine ⟨hw'F₁, le_trans hxz hzw, ?_⟩
        intro v hvF₁ hxv
        exact hw_min v hvF₁ (hzRU.2.2 v (hsub' _ hvF₁) hxv)
  have hsub_double : ((F₁.extend 1).extend 1).toFormat ⊆ F₂.toFormat :=
      Format.subset_of_mem hsub2.specials fun y hy =>
    hsub2 y (Format.extend_one_extend_one_subset_extend_two F₁.toFormat y hy)
  have hz_not_F₁_ext1 : z ∉ F₁.extend 1 :=
    toOdd_notMem_of_extend_subset hsub_double hp_F₂ hz hxne
  have h_close := rndRTO_RN_close_transfer hsub_ext1 hsub' hF₁_sub_ext1
    hz_adj hw'F₁ h_adj_x hw_close_inner hz_not_F₁_ext1
  refine ⟨h_adj_x, h_close, ?_⟩
  intro z' hz'F₁ hz'_adj hz'_ne_w' hz'_eq_dist
  exact rndRTO_no_tie_contradiction hsub_ext1 hz hxne hw'F₁ hz'F₁
    h_adj_x hz'_adj hz'_ne_w' hz'_eq_dist

/-- **rnd-RTO-RN** under `F₁.extend 2 ⊆ F₂` and `2 ≤ F₂.p`, without the relaxed
bound. -/
theorem roundsRTO_RN_finite_of_extend {F₁ F₂ : FiniteFormat}
    (hsub2 : (F₁.extend 2).toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {tb : TieBreak} {x : ℝ} {z w' : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z)
    (hw : RoundsFinite F₁ (.nearest tb) (z : ℝ) w') :
    RoundsFinite F₁ (.nearest tb) x w' := by
  have h_ext1_sub_ext2 : (F₁.extend 1).toFormat ⊆ (F₁.extend 2).toFormat :=
    Format.extend_mono F₁.toFormat (by exact_mod_cast (by omega : (1 : ℕ) ≤ 2) : (1 : ℕ) ≤ 2)
  have hsub_ext1 : (F₁.extend 1).toFormat ⊆ F₂.toFormat :=
      Format.subset_of_mem hsub2.specials fun y hy =>
    hsub2 _ (h_ext1_sub_ext2 _ hy)
  have hsub' : F₁.toFormat ⊆ F₂.toFormat :=
      Format.subset_of_mem hsub_ext1.specials fun y hy =>
    hsub_ext1 _ (Format.self_subset_extend F₁.toFormat 1 _ hy)
  rcases eq_or_ne ((z : ℝ)) x with hzx | hzx
  · -- x = z: hw already has the right shape after rewriting.
    rw [hzx] at hw; exact hw
  have hxne : x ≠ (z : ℝ) := fun h => hzx h.symm
  cases tb with
  | toEven =>
    obtain ⟨hw'F₁, hw_faithful, hw_close, _⟩ := hw
    have hw_adj := isFaithfulRound_iff_directed.mp hw_faithful
    have hw_close_inner : ∀ z'' : Dyadic, z'' ∈ F₁ →
        (RoundsFinite F₁ .toNegative ((z : Dyadic) : ℝ) z''
          ∨ RoundsFinite F₁ .toPositive ((z : Dyadic) : ℝ) z'') →
        |((z : Dyadic) : ℝ) - ((w' : Dyadic) : ℝ)| ≤
            |((z : Dyadic) : ℝ) - ((z'' : Dyadic) : ℝ)| :=
      fun z'' h1 h2 => hw_close z'' h1 (isFaithfulRound_iff_directed.mpr h2)
    obtain ⟨h_adj_x, h_close, h_no_tie⟩ :=
      rndRTO_nearest_facts hsub2 hsub_ext1 hsub' hp_F₂ hz hxne hw'F₁ hw_adj hw_close_inner
    refine ⟨hw'F₁, isFaithfulRound_iff_directed.mpr h_adj_x,
      fun z' h1 h2 => h_close z' h1 (isFaithfulRound_iff_directed.mp h2), ?_⟩
    rintro ⟨z', hz'F₁, hz'_faithful, hz'_ne_w', hz'_eq_dist⟩
    exact (h_no_tie z' hz'F₁ (isFaithfulRound_iff_directed.mp hz'_faithful)
      hz'_ne_w' hz'_eq_dist).elim
  | awayZero =>
    obtain ⟨hw'F₁, hw_faithful, hw_close, _⟩ := hw
    have hw_adj := isFaithfulRound_iff_directed.mp hw_faithful
    have hw_close_inner : ∀ z'' : Dyadic, z'' ∈ F₁ →
        (RoundsFinite F₁ .toNegative ((z : Dyadic) : ℝ) z''
          ∨ RoundsFinite F₁ .toPositive ((z : Dyadic) : ℝ) z'') →
        |((z : Dyadic) : ℝ) - ((w' : Dyadic) : ℝ)| ≤
            |((z : Dyadic) : ℝ) - ((z'' : Dyadic) : ℝ)| :=
      fun z'' h1 h2 => hw_close z'' h1 (isFaithfulRound_iff_directed.mpr h2)
    obtain ⟨h_adj_x, h_close, h_no_tie⟩ :=
      rndRTO_nearest_facts hsub2 hsub_ext1 hsub' hp_F₂ hz hxne hw'F₁ hw_adj hw_close_inner
    refine ⟨hw'F₁, isFaithfulRound_iff_directed.mpr h_adj_x,
      fun z' h1 h2 => h_close z' h1 (isFaithfulRound_iff_directed.mp h2), ?_⟩
    intro z' hz'F₁ hz'_faithful hz'_ne_w' hz'_eq_dist
    exact (h_no_tie z' hz'F₁ (isFaithfulRound_iff_directed.mp hz'_faithful)
      hz'_ne_w' hz'_eq_dist).elim

/-- **rnd-RTO-RN** (RNE and RNA) under the relaxed RN containment; `2 ≤ F₂.p`
follows unless `F₁` is trivial. -/
theorem roundsRTO_RN_finite {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
              ⊆ F₂.toFormat)
    {tb : TieBreak} {x : ℝ} {z w' : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z)
    (hw : RoundsFinite F₁ (.nearest tb) (z : ℝ) w') :
    RoundsFinite F₁ (.nearest tb) x w' := by
  rcases two_le_p_or_trivial_of_extend_two_withBound_subset hsub with hp_F₂ | hF₁_triv
  · exact roundsRTO_RN_finite_of_extend (extend_two_subset_of_withBound_subset hsub) hp_F₂
      hz hw
  · -- F₁ trivial: handled uniformly for any tb.
    exact RoundsFinite.nearest_of_trivial hF₁_triv hw.1

end Mpfx
