import Mpfx.DoubleRounding.Propagation

/-!
# Total double rounding (overflow-aware, self-contained)

Stated with `Overflows` and `RoundsInBound`, with no chain hypotheses. For
each double-rounding rule, conclude that either (i) rounding `x` directly in
`F₁` overflows, or (ii) rounding `x` in `F₂` does **not** overflow (finite
`z`), the chained rounding is finite (`w`), and double rounding holds. The
paper's side condition ("the rules hold whenever `rnd_{F₁}(x)` does not
overflow") is the guard between the two disjuncts; the paper's bound
conditions (`next(b₁)` vs `b₁`) become *proof obligations* for no-overflow
propagation. An arbitrary (off-grid) bound is reduced to its grid floor, so
no regularity hypothesis surfaces in the public statements. -/

namespace Mpfx

/-! ## Reduction to a grid-floor bound

`Overflows` and `RoundsInBound` only inspect the bound through `boundOK` at
*grid* values, so replacing the bound `b₁` by its grid floor `d` (the largest grid
point `≤ b₁`, i.e. the RTN rounding of `b₁`) yields the same relation. The
floor is on the grid by construction, so each total theorem's regular-bound
core (`suffices key` in its proof) applies to the floor-adjusted format.
The degenerate corner `exp = ⊥ ∧ d = 0` (where the grid has positive points
of arbitrarily small magnitude, hence no successor of the bound) forces
`b₁ = 0`, where an in-bound direct rounding pins `x = 0` and double
rounding is trivial. -/


/-- On the grid, a value within the floor `D` is within the original bound. -/
private theorem boundOK_of_boundOK_floor {F₁ : FiniteFormat} {D : NonNegDyadic}
    (hD_le : Format.boundOK F₁.b D.val) {v : Dyadic}
    (hv : Format.boundOK ((D : Bound)) v) : Format.boundOK F₁.b v := by
  have hD_abs : |(v : ℝ)| ≤ |((D.val : Dyadic) : ℝ)| := by
    rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast, ← Rat.cast_abs,
      ← Rat.cast_abs]
    exact_mod_cast (by rwa [abs_of_nonneg D.2] :
      |(v : ℚ)| ≤ |((D.val : Dyadic) : ℚ)|)
  exact boundOK_of_abs_le hD_abs hD_le

/-- Replacing the bound by its grid floor `D` preserves overflow: the bound is
only tested at grid values, where `|·| ≤ b₁ ↔ |·| ≤ D`. -/
private theorem overflows_withBoundFF_floor_iff {F₁ : FiniteFormat} {D : NonNegDyadic}
    (hD_le : Format.boundOK F₁.b D.val)
    (hD_max : ∀ v : Dyadic, v ∈ F₁.unbounded → Format.boundOK F₁.b v →
      Format.boundOK ((D : Bound)) v)
    (rm : RoundingMode) (x : ℝ) :
    Overflows F₁ rm x ↔ Overflows (FiniteFormat.withBoundFF F₁ (D : Bound)) rm x :=
  ⟨fun ⟨y, hrf, hnb⟩ => ⟨y, hrf, fun h => hnb (boundOK_of_boundOK_floor hD_le h)⟩,
   fun ⟨y, hrf, hnb⟩ => ⟨y, hrf, fun h => hnb (hD_max y hrf.1 h)⟩⟩

/-- Replacing the bound by its grid floor `D` preserves in-bound rounding. -/
private theorem roundsInBound_withBoundFF_floor_iff {F₁ : FiniteFormat} {D : NonNegDyadic}
    (hD_le : Format.boundOK F₁.b D.val)
    (hD_max : ∀ v : Dyadic, v ∈ F₁.unbounded → Format.boundOK F₁.b v →
      Format.boundOK ((D : Bound)) v)
    (rm : RoundingMode) (x : ℝ) (y : Dyadic) :
    RoundsInBound F₁ rm x y ↔
      RoundsInBound (FiniteFormat.withBoundFF F₁ (D : Bound)) rm x y :=
  ⟨fun ⟨hrf, hb⟩ => ⟨hrf, hD_max y hrf.1 hb⟩,
   fun ⟨hrf, hb⟩ => ⟨hrf, boundOK_of_boundOK_floor hD_le hb⟩⟩

/-- With `exp = ⊥`, a toZero rounding equal to `0` forces `x = 0`: the grid
has positive points of arbitrarily small magnitude. -/
private theorem eq_zero_of_toZero_zero {F₁ : FiniteFormat} (hexp : F₁.exp = ⊥)
    {x : ℝ} {y : Dyadic} (hy : RoundsFinite F₁.unbounded .toZero x y)
    (hy0 : (y : ℝ) = 0) : x = 0 := by
  by_contra hx
  have hx_pos : 0 < |x| := abs_pos.mpr hx
  set K := Int.log 2 |x| with hK_def
  have h2K : (0 : ℝ) < (2 : ℝ) ^ K := zpow_pos (by norm_num) _
  have h2K_le : (2 : ℝ) ^ K ≤ |x| := Int.zpow_log_le_self (by norm_num) hx_pos
  have hg_mem : Dyadic.ofIntZpow 1 K ∈ F₁.unbounded := by
    refine ⟨?_, ?_, trivial⟩
    · change Dyadic.precisionAtMost F₁.p _
      exact precisionAtMost_one_zpow F₁.pos K
    · change Dyadic.quantumAtLeast F₁.exp _
      rw [hexp]
      trivial
  have hg_val : ((Dyadic.ofIntZpow 1 K : Dyadic) : ℝ) = (2 : ℝ) ^ K :=
    coe_real_ofIntZpow_one K
  obtain ⟨-, -, -, hymax⟩ := hy
  by_cases hx_sign : 0 ≤ x
  · have h := hymax (Dyadic.ofIntZpow 1 K) hg_mem
      (by rw [hg_val, abs_of_pos h2K]; exact h2K_le)
      (by rw [hg_val]; positivity)
    rw [hg_val, hy0, abs_zero, abs_of_pos h2K] at h
    linarith
  · push Not at hx_sign
    have hng_mem : (-(Dyadic.ofIntZpow 1 K)) ∈ F₁.unbounded :=
      FiniteFormat.neg_mem hg_mem
    have h := hymax (-(Dyadic.ofIntZpow 1 K)) hng_mem
      (by rw [Dyadic.coe_real_neg, abs_neg, hg_val, abs_of_pos h2K]; exact h2K_le)
      (by rw [Dyadic.coe_real_neg, hg_val]; nlinarith)
    rw [Dyadic.coe_real_neg, abs_neg, hg_val, hy0, abs_zero, abs_of_pos h2K] at h
    linarith

/-- With `exp = ⊥`, a faithful rounding equal to `0` forces `x = 0`. Covers
the RTO and RN direct roundings. -/
private theorem eq_zero_of_faithful_zero {F₁ : FiniteFormat} (hexp : F₁.exp = ⊥)
    {x : ℝ} {y : Dyadic} (hf : IsFaithfulRound F₁.unbounded x y)
    (hy0 : (y : ℝ) = 0) : x = 0 := by
  by_contra hx
  have hx_pos : 0 < |x| := abs_pos.mpr hx
  set K := Int.log 2 |x| with hK_def
  have h2K : (0 : ℝ) < (2 : ℝ) ^ K := zpow_pos (by norm_num) _
  have h2K_le : (2 : ℝ) ^ K ≤ |x| := Int.zpow_log_le_self (by norm_num) hx_pos
  have hg_mem : Dyadic.ofIntZpow 1 K ∈ F₁.unbounded := by
    refine ⟨?_, ?_, trivial⟩
    · change Dyadic.precisionAtMost F₁.p _
      exact precisionAtMost_one_zpow F₁.pos K
    · change Dyadic.quantumAtLeast F₁.exp _
      rw [hexp]
      trivial
  have hg_val : ((Dyadic.ofIntZpow 1 K : Dyadic) : ℝ) = (2 : ℝ) ^ K :=
    coe_real_ofIntZpow_one K
  rcases lt_or_gt_of_ne hx with hx_neg | hx_pos'
  · rcases hf with ⟨-, hy_le, -⟩ | ⟨-, -, hy_min⟩
    · rw [hy0] at hy_le
      linarith
    · have hng_mem : (-(Dyadic.ofIntZpow 1 K)) ∈ F₁.unbounded :=
        FiniteFormat.neg_mem hg_mem
      have h := hy_min (-(Dyadic.ofIntZpow 1 K)) hng_mem
        (by
          rw [Dyadic.coe_real_neg, hg_val]
          rw [abs_of_neg hx_neg] at h2K_le
          linarith)
      rw [Dyadic.coe_real_neg, hg_val, hy0] at h
      linarith
  · rcases hf with ⟨-, -, hy_max⟩ | ⟨-, hy_ge, -⟩
    · have h := hy_max (Dyadic.ofIntZpow 1 K) hg_mem
        (by
          rw [hg_val]
          rw [abs_of_pos hx_pos'] at h2K_le
          linarith)
      rw [hg_val, hy0] at h
      linarith
    · rw [hy0] at hy_ge
      linarith

/-- The degenerate corner `b₁ = 0` (with the per-mode zero lemmas supplied):
an in-bound direct rounding forces `x = 0`, and everything rounds to `0`. -/
private theorem rounds_total_of_zero_bound {F₁ F₂ : FiniteFormat}
    {rm₁ rm₂ : RoundingMode}
    (h₁u : ¬ F₁.IsUndefined rm₁) (h₂u : ¬ F₂.IsUndefined rm₂)
    (hzero₁ : ∀ {x : ℝ} {y : Dyadic}, RoundsFinite F₁.unbounded rm₁ x y →
      (y : ℝ) = 0 → x = 0)
    (hzero₂ : ∀ {z : Dyadic}, RoundsFinite F₂.unbounded rm₂ 0 z → (z : ℝ) = 0)
    {b₁ : NonNegDyadic} (hF₁b : F₁.b = (b₁ : Bound))
    (hb₁_zero : ((b₁.val : Dyadic) : ℝ) = 0) (x : ℝ) :
    Overflows F₁ rm₁ x ∨
    (∃ z w : Dyadic, RoundsInBound F₂ rm₂ x z ∧
      RoundsInBound F₁ rm₁ (z : ℝ) w ∧
      RoundsInBound F₁ rm₁ x w) := by
  have hy := rndUnbounded_satisfies F₁ rm₁ x h₁u
  set y := rndUnbounded F₁ rm₁ x h₁u with hy_def
  by_cases hbOK : Format.boundOK F₁.b y
  · right
    -- `|y| ≤ b₁ = 0`, so `y = 0` and hence `x = 0`.
    have hy0 : (y : ℝ) = 0 := by
      have h := hbOK
      rw [hF₁b] at h
      have h1 : |(y : ℚ)| ≤ ((b₁.val : Dyadic) : ℚ) := h
      have hb₁q : ((b₁.val : Dyadic) : ℚ) = 0 := by
        rw [Dyadic.coe_real_eq_ratCast] at hb₁_zero
        exact_mod_cast hb₁_zero
      rw [hb₁q] at h1
      have h2 : (y : ℚ) = 0 := abs_nonpos_iff.mp h1
      rw [Dyadic.coe_real_eq_ratCast, h2]
      norm_num
    have hx0 : x = 0 := hzero₁ hy hy0
    -- `z = 0` and the chain collapses onto the direct rounding.
    have hz := rndUnbounded_satisfies F₂ rm₂ x h₂u
    set z := rndUnbounded F₂ rm₂ x h₂u with hz_def
    have hz0 : (z : ℝ) = 0 := hzero₂ (hx0 ▸ hz)
    have hz_bnd : Format.boundOK F₂.b z := by
      have hzd : z = 0 := eq_zero_of_coe_real_zero hz0
      rw [hzd]
      exact Format.boundOK_zero _
    have hw := rndUnbounded_satisfies F₁ rm₁ ((z : Dyadic) : ℝ) h₁u
    set w := rndUnbounded F₁ rm₁ ((z : Dyadic) : ℝ) h₁u with hw_def
    have hzx : ((z : Dyadic) : ℝ) = x := by rw [hz0, hx0]
    have hw_x : RoundsFinite F₁.unbounded rm₁ x w := hzx ▸ hw
    have hwy : w = y := (rndUnbounded_unique F₁ rm₁ x h₁u hw_x).trans hy_def.symm
    have hw_bnd : Format.boundOK F₁.b w := by rw [hwy]; exact hbOK
    exact ⟨z, w, ⟨hz, hz_bnd⟩, ⟨hw, hw_bnd⟩, ⟨hw_x, hw_bnd⟩⟩
  · left
    exact ⟨_, hy, hbOK⟩

/-- Bound-floor setup for a finite bound `b₁`: either the degenerate corner
(`exp = ⊥` and `b₁ = 0`), or a floor `D` with a regular floor-adjusted
format, the bound-transfer properties, and monotone `next` bounds at `F₁`
and `F₁.extend 1`. -/
private theorem bound_floor_setup {F₁ : FiniteFormat} {b₁ : NonNegDyadic}
    (hF₁b : F₁.b = (b₁ : Bound)) :
    (F₁.exp = ⊥ ∧ ((b₁.val : Dyadic) : ℝ) = 0) ∨
    (∃ D : NonNegDyadic,
      (∀ b : NonNegDyadic,
        (FiniteFormat.withBoundFF F₁ (D : Bound)).b
          = (b : Bound) →
        b.val ∈ FiniteFormat.withBoundFF F₁ (D : Bound) ∧
        ((FiniteFormat.withBoundFF F₁ (D : Bound)).exp = ⊥ →
          0 < ((b.val : Dyadic) : ℝ))) ∧
      Format.boundOK F₁.b D.val ∧
      (∀ v : Dyadic, v ∈ F₁.unbounded → Format.boundOK F₁.b v →
        Format.boundOK ((D : Bound)) v) ∧
      ((F₁.toFormat.next D.val : Dyadic) : ℝ)
        ≤ ((F₁.toFormat.next b₁.val : Dyadic) : ℝ) ∧
      (((F₁.extend 1).toFormat.next D.val : Dyadic) : ℝ)
        ≤ (((F₁.extend 1).toFormat.next b₁.val : Dyadic) : ℝ)) := by
  have hb₁_nn : 0 ≤ ((b₁.val : Dyadic) : ℝ) := nonneg_coe_real b₁
  obtain ⟨hd_mem, hd_le, hd_max⟩ :=
    rndUnbounded_satisfies F₁ .toNegative ((b₁.val : Dyadic) : ℝ)
      (not_isUndefined_toNegative F₁)
  set d := rndUnbounded F₁ .toNegative ((b₁.val : Dyadic) : ℝ)
    (not_isUndefined_toNegative F₁) with hd_def
  have hd_nn : 0 ≤ ((d : Dyadic) : ℝ) := by
    have h := hd_max 0 F₁.unbounded.zero_mem
      (by rw [Dyadic.coe_real_zero]; exact hb₁_nn)
    rwa [Dyadic.coe_real_zero] at h
  by_cases hdeg : F₁.exp = ⊥ ∧ ((d : Dyadic) : ℝ) = 0
  · -- Degenerate: `b₁ = 0` (a positive `b₁` admits a small power of two below).
    obtain ⟨hexp, hd0⟩ := hdeg
    left
    refine ⟨hexp, ?_⟩
    by_contra hb₁ne
    have hb₁_pos : 0 < ((b₁.val : Dyadic) : ℝ) := lt_of_le_of_ne hb₁_nn (Ne.symm hb₁ne)
    set K := Int.log 2 ((b₁.val : Dyadic) : ℝ) with hK_def
    have h2K : (0 : ℝ) < (2 : ℝ) ^ K := zpow_pos (by norm_num) _
    have h2K_le : (2 : ℝ) ^ K ≤ ((b₁.val : Dyadic) : ℝ) :=
      Int.zpow_log_le_self (by norm_num) hb₁_pos
    have hg_mem : Dyadic.ofIntZpow 1 K ∈ F₁.unbounded := by
      refine ⟨?_, ?_, trivial⟩
      · change Dyadic.precisionAtMost F₁.p _
        exact precisionAtMost_one_zpow F₁.pos K
      · change Dyadic.quantumAtLeast F₁.exp _
        rw [hexp]
        trivial
    have hg_val : ((Dyadic.ofIntZpow 1 K : Dyadic) : ℝ) = (2 : ℝ) ^ K :=
    coe_real_ofIntZpow_one K
    have h := hd_max (Dyadic.ofIntZpow 1 K) hg_mem (by rw [hg_val]; exact h2K_le)
    rw [hg_val, hd0] at h
    linarith
  · right
    push Not at hdeg
    have hguard : F₁.exp = ⊥ → 0 < ((d : Dyadic) : ℝ) := fun h =>
      lt_of_le_of_ne hd_nn (Ne.symm (hdeg h))
    have hd_nn_q : (0 : ℚ) ≤ (d : ℚ) := by
      rw [Dyadic.coe_real_eq_ratCast] at hd_nn
      exact_mod_cast hd_nn
    refine ⟨⟨d, hd_nn_q⟩, ?_, ?_, ?_, ?_, ?_⟩
    · -- The floor-adjusted format has a regular (on-grid) bound.
      intro b hb
      have hDb : (⟨d, hd_nn_q⟩ : NonNegDyadic) = b := WithTop.coe_inj.mp hb
      refine ⟨?_, ?_⟩
      · rw [← hDb]
        exact ⟨hd_mem.1, hd_mem.2.1, by
          change |(d : ℚ)| ≤ ((d : Dyadic) : ℚ)
          rw [abs_of_nonneg hd_nn_q]⟩
      · intro hbot
        rw [← hDb]
        exact hguard hbot
    · -- `D` is in-bound for the original bound.
      rw [hF₁b]
      have hr : |((d : Dyadic) : ℝ)| ≤ ((b₁.val : Dyadic) : ℝ) := by
        rw [abs_of_nonneg hd_nn]; exact hd_le
      rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast, ← Rat.cast_abs] at hr
      change |(d : ℚ)| ≤ ((b₁.val : Dyadic) : ℚ)
      exact_mod_cast hr
    · -- Grid values within `b₁` are within `D`.
      intro v hv hbv
      rw [hF₁b] at hbv
      have h1r : |(v : ℝ)| ≤ ((b₁.val : Dyadic) : ℝ) := by
        rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast, ← Rat.cast_abs]
        exact_mod_cast hbv
      have h2r : |(v : ℝ)| ≤ ((d : Dyadic) : ℝ) := by
        rcases le_or_gt 0 ((v : Dyadic) : ℝ) with hv0 | hv0
        · have h := hd_max v hv (by rwa [abs_of_nonneg hv0] at h1r)
          rwa [abs_of_nonneg hv0]
        · have h := hd_max (-v) (FiniteFormat.neg_mem hv)
            (by rw [Dyadic.coe_real_neg]; rw [abs_of_neg hv0] at h1r; linarith)
          rw [Dyadic.coe_real_neg] at h
          rw [abs_of_neg hv0]
          linarith
      change |(v : ℚ)| ≤ ((d : Dyadic) : ℚ)
      rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast, ← Rat.cast_abs] at h2r
      exact_mod_cast h2r
    · exact next_mono hd_le hguard
    · exact next_mono hd_le
        (fun h => hguard (exp_bot_of_extend_bot (F₁ := F₁) (k := 1) h))

/-- The grid-regularity hypothesis is vacuous when the bound is `⊤`. -/
private theorem regular_of_bound_top {F : FiniteFormat} (hFb : F.b = ⊤) :
    ∀ b : NonNegDyadic, F.b = (b : Bound) →
      b.val ∈ F ∧ (F.exp = ⊥ → 0 < ((b.val : Dyadic) : ℝ)) := by
  intro b hb
  rw [hFb] at hb
  exact absurd hb.symm WithTop.coe_ne_top

/-- Transport the total double-rounding conclusion from the floor-adjusted
format `F₁.withBoundFF D` back to `F₁`, applying
`overflows_withBoundFF_floor_iff` / `roundsInBound_withBoundFF_floor_iff`. -/
private theorem rounds_floor_lift {F₁ F₂ : FiniteFormat} {D : NonNegDyadic}
    (hD_le : Format.boundOK F₁.b D.val)
    (hD_max : ∀ v : Dyadic, v ∈ F₁.unbounded → Format.boundOK F₁.b v →
      Format.boundOK ((D : Bound)) v)
    {rm₁ rm₂ : RoundingMode} {x : ℝ}
    (h : Overflows (FiniteFormat.withBoundFF F₁ (D : Bound)) rm₁ x ∨
      (∃ z w : Dyadic, RoundsInBound F₂ rm₂ x z ∧
        RoundsInBound (FiniteFormat.withBoundFF F₁ (D : Bound)) rm₁ (z : ℝ) w ∧
        RoundsInBound (FiniteFormat.withBoundFF F₁ (D : Bound)) rm₁ x w)) :
    Overflows F₁ rm₁ x ∨
    (∃ z w : Dyadic, RoundsInBound F₂ rm₂ x z ∧
      RoundsInBound F₁ rm₁ (z : ℝ) w ∧
      RoundsInBound F₁ rm₁ x w) := by
  rcases h with hov | ⟨z, w, h1, h2, h3⟩
  · exact Or.inl ((overflows_withBoundFF_floor_iff hD_le hD_max _ _).mpr hov)
  · exact Or.inr ⟨z, w, h1,
      (roundsInBound_withBoundFF_floor_iff hD_le hD_max _ _ _).mpr h2,
      (roundsInBound_withBoundFF_floor_iff hD_le hD_max _ _ _).mpr h3⟩

/-- Lift a regular-bound `noOverflow_direct` to an arbitrary bound through the grid floor
`D`. Needs `F₁` nontrivial: `F₁ = {0}` with `exp = ⊥` rounds every nonzero real
out of bound while a chain may land on `0`. -/
private theorem not_overflows_of_floor {F₁ : FiniteFormat} {rm : RoundingMode}
    {x zr : ℝ} {w : Dyadic} (hnt : F₁.toFormat.Nontrivial)
    (hw : RoundsInBound F₁ rm zr w)
    (core : ∀ b₁ D : NonNegDyadic, F₁.b = (b₁ : Bound) →
      (∀ b : NonNegDyadic, (FiniteFormat.withBoundFF F₁ (D : Bound)).b = (b : Bound) →
        b.val ∈ FiniteFormat.withBoundFF F₁ (D : Bound) ∧
        ((FiniteFormat.withBoundFF F₁ (D : Bound)).exp = ⊥ →
          0 < ((b.val : Dyadic) : ℝ))) →
      ((F₁.toFormat.next D.val : Dyadic) : ℝ) ≤ ((F₁.toFormat.next b₁.val : Dyadic) : ℝ) →
      (((F₁.extend 1).toFormat.next D.val : Dyadic) : ℝ)
        ≤ (((F₁.extend 1).toFormat.next b₁.val : Dyadic) : ℝ) →
      ∀ y : Dyadic, Format.boundOK (FiniteFormat.withBoundFF F₁ (D : Bound)).b w →
        RoundsFinite F₁.unbounded rm x y →
        Format.boundOK (FiniteFormat.withBoundFF F₁ (D : Bound)).b y) :
    ¬ Overflows F₁ rm x := by
  rintro ⟨y, hy, hby⟩
  rcases hF₁b : F₁.b with _ | b₁
  · exact hby (by rw [hF₁b]; trivial)
  rcases bound_floor_setup hF₁b with ⟨-, hb₁0⟩ |
    ⟨D, hreg_G, hD_le, hD_max, hmono, hmono_ext⟩
  · obtain ⟨d, hd, hd0⟩ := hnt
    have h := abs_coe_real_le_of_boundOK (hF₁b ▸ hd.2.2)
    rw [hb₁0] at h
    exact hd0 (eq_zero_of_coe_real_zero (abs_nonpos_iff.mp h))
  · have hbw := ((roundsInBound_withBoundFF_floor_iff hD_le hD_max _ _ _).mp hw).2
    obtain ⟨y', hy', hby'⟩ :=
      (overflows_withBoundFF_floor_iff hD_le hD_max _ _).mp ⟨y, hy, hby⟩
    exact hby' (core b₁ D hF₁b hreg_G hmono hmono_ext y' hbw hy')

/-! ## The total theorems

Each proof first states a regular-bound core (`suffices key`: the bound is
on the grid, and positive when `exp = ⊥`), reduces to it at the
floor-adjusted format via `bound_floor_setup` +
`rounds_floor_lift` (degenerate corner via
`rounds_total_of_zero_bound`), then proves the core. -/

/-- **rnd-RTZ-RTZ**, total form. Either rounding `x` directly in `F₁`
overflows, or rounding `x` in `F₂` does not overflow (finite `z`), the
chained rounding is finite (`w`), and double rounding holds. Uses the
paper's strengthened containment `F₁.withBound next(b₁) ⊆ F₂`. -/
theorem roundsRTZ_RTZ_inBound {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (x : ℝ) :
    Overflows F₁ .toZero x ∨
    (∃ z w : Dyadic, RoundsInBound F₂ .toZero x z ∧
      RoundsInBound F₁ .toZero (z : ℝ) w ∧
      RoundsInBound F₁ .toZero x w) := by
  -- Reduce to a bound that is on the grid (and positive when `exp = ⊥`)
  -- by replacing it with its grid floor.
  suffices key : ∀ F : FiniteFormat,
      (F.toFormat.withBound F.toFormat.boundAfterNext) ⊆ F₂.toFormat →
      (∀ b : NonNegDyadic, F.b = (b : Bound) →
        b.val ∈ F ∧ (F.exp = ⊥ → 0 < ((b.val : Dyadic) : ℝ))) →
      Overflows F .toZero x ∨
      (∃ z w : Dyadic, RoundsInBound F₂ .toZero x z ∧
        RoundsInBound F .toZero (z : ℝ) w ∧
        RoundsInBound F .toZero x w) by
    rcases hF₁b : F₁.b with _ | b₁
    · exact key F₁ hsub (regular_of_bound_top hF₁b)
    · rcases bound_floor_setup hF₁b with ⟨hexp, hb₁0⟩ |
        ⟨D, hreg_G, hD_le, hD_max, hmono, -⟩
      · exact rounds_total_of_zero_bound (not_isUndefined_toZero F₁)
          (not_isUndefined_toZero F₂)
          (fun hy hy0 => eq_zero_of_toZero_zero hexp hy hy0)
          (fun hz => by
            have h := hz.2.1
            rw [abs_zero] at h
            exact abs_nonpos_iff.mp h)
          hF₁b hb₁0 x
      · exact rounds_floor_lift hD_le hD_max (key _
          (Format.subset_of_mem hsub.specials fun v hv => hsub v ⟨hv.1, hv.2.1,
            boundOK_boundAfterNext_mono
              (G := FiniteFormat.withBoundFF F₁ (D : Bound))
              hF₁b rfl rfl hmono hv.2.2⟩) hreg_G)
  intro F hsub hreg
  have h₁u := not_isUndefined_toZero F
  have h₂u := not_isUndefined_toZero F₂
  -- Plain containment, recovered from the paper form.
  have hsub' : F.toFormat ⊆ F₂.toFormat :=
      Format.subset_of_mem hsub.specials fun d hd =>
    hsub d ⟨hd.1, hd.2.1, boundOK_boundAfterNext_of_boundOK hd.2.2⟩
  have hy := rndUnbounded_satisfies F .toZero x h₁u
  set y := rndUnbounded F .toZero x h₁u with hy_def
  by_cases hbOK : Format.boundOK F.b y
  · right
    -- F₂ does not overflow.
    have hz := rndUnbounded_satisfies F₂ .toZero x h₂u
    set z := rndUnbounded F₂ .toZero x h₂u with hz_def
    have hz_bnd : Format.boundOK F₂.b z := toZero_noOverflow_F₂ hsub hreg hy hbOK hz
    have hzR : RoundsInBound F₂ .toZero x z := ⟨hz, hz_bnd⟩
    -- The chain does not overflow.
    have hw := rndUnbounded_satisfies F .toZero (z : ℝ) h₁u
    set w := rndUnbounded F .toZero (z : ℝ) h₁u with hw_def
    have hw_bnd : Format.boundOK F.b w := toZero_noOverflow_chain hy hbOK hz hw
    have hwR : RoundsInBound F .toZero (z : ℝ) w := ⟨hw, hw_bnd⟩
    -- Double rounding holds: restrict the chain, compose spec-relationally,
    -- and lift back along the in-bound direct rounding.
    have hsub_u : F.toFormat ⊆ F₂.unbounded.toFormat :=
      Format.subset_of_mem hsub.specials fun d hd =>
      mem_unbounded_of_mem (F := F₂) (hsub' d hd)
    have hw_bdd : RoundsFinite F .toZero (z : ℝ) w :=
      RoundsFinite.toZero_restrict hw hw_bnd
    have hxw : RoundsFinite F .toZero x w := roundsRTZ_RTZ_finite hsub_u hz hw_bdd
    exact ⟨z, w, hzR, hwR, ⟨RoundsFinite.toZero_lift hxw hy hbOK, hw_bnd⟩⟩
  · left
    exact ⟨_, hy, hbOK⟩

/-- **rnd-RTZ-RTZ**, no overflow from the chain: if the chain stays in bound, so does the direct
rounding. -/
theorem roundsRTZ_RTZ_noOverflow {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial) {x : ℝ} {z w : Dyadic}
    (hz : RoundsInBound F₂ .toZero x z) (hw : RoundsInBound F₁ .toZero (z : ℝ) w) :
    ¬ Overflows F₁ .toZero x :=
  not_overflows_of_floor hnt hw fun _ D hF₁b hreg_G hmono _ _ hbw hy => by
    set G := FiniteFormat.withBoundFF F₁ (D : Bound)
    have hsubG : (G.toFormat.withBound G.toFormat.boundAfterNext) ⊆ F₂.toFormat :=
      Format.subset_of_mem hsub.specials fun v hv => hsub v ⟨hv.1, hv.2.1,
        boundOK_boundAfterNext_mono (G := G) hF₁b rfl rfl hmono hv.2.2⟩
    exact toZero_noOverflow_direct hreg_G (fun _ hb hm => next_mem_of_withBound_subset hsubG hb hm)
      hz.1.isFaithfulRound hw.1 hbw hy

/-- **rnd-RAZ-RAZ**, total form. Either rounding `x` directly in `F₁`
overflows, or rounding `x` in `F₂` does not overflow (finite `z`), the
chained rounding is finite (`w`), and double rounding holds. -/
theorem roundsRAZ_RAZ_inBound {F₁ F₂ : FiniteFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat) (x : ℝ) :
    Overflows F₁ .awayZero x ∨
    (∃ z w : Dyadic, RoundsInBound F₂ .awayZero x z ∧
      RoundsInBound F₁ .awayZero (z : ℝ) w ∧
      RoundsInBound F₁ .awayZero x w) := by
  have h₁u := not_isUndefined_awayZero F₁
  have h₂u := not_isUndefined_awayZero F₂
  have hy := rndUnbounded_satisfies F₁ .awayZero x h₁u
  set y := rndUnbounded F₁ .awayZero x h₁u with hy_def
  by_cases hbOK : Format.boundOK F₁.b y
  · right
    -- F₂ does not overflow.
    have hz := rndUnbounded_satisfies F₂ .awayZero x h₂u
    set z := rndUnbounded F₂ .awayZero x h₂u with hz_def
    have hz_bnd : Format.boundOK F₂.b z := awayZero_noOverflow_F₂ hsub hy hbOK hz
    have hzR : RoundsInBound F₂ .awayZero x z := ⟨hz, hz_bnd⟩
    -- The chain does not overflow.
    have hw := rndUnbounded_satisfies F₁ .awayZero (z : ℝ) h₁u
    set w := rndUnbounded F₁ .awayZero (z : ℝ) h₁u with hw_def
    have hw_bnd : Format.boundOK F₁.b w :=
      awayZero_noOverflow_chain hsub hy hbOK hz hw
    have hwR : RoundsInBound F₁ .awayZero (z : ℝ) w := ⟨hw, hw_bnd⟩
    -- Double rounding holds: restrict the chain, compose spec-relationally,
    -- and lift back along the in-bound direct rounding.
    have hsub_u : F₁.toFormat ⊆ F₂.unbounded.toFormat :=
      Format.subset_of_mem hsub.specials fun d hd =>
      mem_unbounded_of_mem (F := F₂) (hsub d hd)
    have hw_bdd : RoundsFinite F₁ .awayZero (z : ℝ) w :=
      RoundsFinite.awayZero_restrict hw hw_bnd
    have hxw : RoundsFinite F₁ .awayZero x w := roundsRAZ_RAZ_finite hsub_u hz hw_bdd
    exact ⟨z, w, hzR, hwR, ⟨RoundsFinite.awayZero_lift hxw hy hbOK, hw_bnd⟩⟩
  · left
    exact ⟨_, hy, hbOK⟩

/-- **rnd-RAZ-RAZ**, no overflow from the chain: the chained rounding is a candidate for the
direct one, so it bounds it. No containment is needed. -/
theorem roundsRAZ_RAZ_noOverflow {F₁ F₂ : FiniteFormat} {x : ℝ} {z w : Dyadic}
    (hz : RoundsInBound F₂ .awayZero x z) (hw : RoundsInBound F₁ .awayZero (z : ℝ) w) :
    ¬ Overflows F₁ .awayZero x := by
  rintro ⟨y, hy, hby⟩
  have hwx : (w : ℝ) * x ≥ 0 := by
    rcases eq_or_ne (z : ℝ) 0 with h0 | h0
    · have hx : x = 0 := abs_nonpos_iff.mp (by simpa [h0] using hz.1.2.1)
      rw [hx, mul_zero]
    · exact mul_nonneg_of_common_sign hw.1.2.2.1
        (by linarith [hz.1.2.2.1] : x * (z : ℝ) ≥ 0) fun h => absurd h h0
  exact hby (awayZero_noOverflow_direct hw.1.1 (hz.1.2.1.trans hw.1.2.1) hwx hw.2 hy)

/-- **rnd-RTO-RTO**, total form (unified — no parity split on `b₁`). Either
rounding `x` directly in `F₁` (RTO) overflows, or the RTO rounding of `x` in
`F₂` does not overflow (finite `z`), the chained RTO rounding is finite
(`w`), and double rounding holds. -/
theorem roundsRTO_RTO_inBound {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    (h₁u : ¬ F₁.IsUndefined .toOdd) (x : ℝ) :
    Overflows F₁ .toOdd x ∨
    (∃ z w : Dyadic, RoundsInBound F₂ .toOdd x z ∧
      RoundsInBound F₁ .toOdd (z : ℝ) w ∧
      RoundsInBound F₁ .toOdd x w) := by
  -- Reduce to a bound that is on the grid (and positive when `exp = ⊥`)
  -- by replacing it with its grid floor.
  suffices key : ∀ F : FiniteFormat,
      (F.toFormat.withBound F.toFormat.boundAfterNext) ⊆ F₂.toFormat →
      (∀ b : NonNegDyadic, F.b = (b : Bound) →
        b.val ∈ F ∧ (F.exp = ⊥ → 0 < ((b.val : Dyadic) : ℝ))) →
      ¬ F.IsUndefined .toOdd →
      Overflows F .toOdd x ∨
      (∃ z w : Dyadic, RoundsInBound F₂ .toOdd x z ∧
        RoundsInBound F .toOdd (z : ℝ) w ∧
        RoundsInBound F .toOdd x w) by
    rcases hF₁b : F₁.b with _ | b₁
    · exact key F₁ hsub (regular_of_bound_top hF₁b) h₁u
    · rcases bound_floor_setup hF₁b with ⟨hexp, hb₁0⟩ |
        ⟨D, hreg_G, hD_le, hD_max, hmono, -⟩
      · exact rounds_total_of_zero_bound h₁u (not_isUndefined_of_two_le_p hp_F₂)
          (fun hy hy0 => eq_zero_of_faithful_zero hexp hy.2.1 hy0)
          (fun hz => by rw [RoundsFinite.eq_zero_of_zero hz, Dyadic.coe_real_zero])
          hF₁b hb₁0 x
      · exact rounds_floor_lift hD_le hD_max (key _
          (Format.subset_of_mem hsub.specials fun v hv => hsub v ⟨hv.1, hv.2.1,
            boundOK_boundAfterNext_mono
              (G := FiniteFormat.withBoundFF F₁ (D : Bound))
              hF₁b rfl rfl hmono hv.2.2⟩) hreg_G h₁u)
  intro F hsub hreg h₁u
  have h₂u : ¬ F₂.IsUndefined .toOdd := not_isUndefined_of_two_le_p hp_F₂
  have hy := rndUnbounded_satisfies F .toOdd x h₁u
  set y := rndUnbounded F .toOdd x h₁u with hy_def
  by_cases hbOK : Format.boundOK F.b y
  · right
    have hz := rndUnbounded_satisfies F₂ .toOdd x h₂u
    set z := rndUnbounded F₂ .toOdd x h₂u with hz_def
    -- F₂ does not overflow.
    have hz_bnd : Format.boundOK F₂.b z := by
      rcases hFb : F.b with _ | b₁
      · rw [b_eq_top_of_withBound_subset hsub hFb]
        trivial
      · obtain ⟨hb₁_mem, hguard⟩ := hreg b₁ hFb
        obtain ⟨hb₁_nn, hN_lt, hN_nn, hN_mem⟩ := next_facts hb₁_mem
        have hN_F₂ : F.toFormat.next b₁.val ∈ F₂ :=
          hsub _ ⟨hN_mem.1, hN_mem.2.1, boundOK_boundAfterNext_next hFb hN_nn⟩
        have hxN : |x| < ((F.toFormat.next b₁.val : Dyadic) : ℝ) :=
          abs_lt_next_of_toOdd_inbound hFb hb₁_mem hy hbOK
        have hz_abs : |(z : ℝ)| ≤ ((F.toFormat.next b₁.val : Dyadic) : ℝ) :=
          abs_faithful_le_of_le (mem_unbounded_of_mem hN_F₂) hxN.le hz.2.1
        exact boundOK_of_abs_le (by rwa [abs_of_nonneg hN_nn]) hN_F₂.2.2
    have hzR : RoundsInBound F₂ .toOdd x z := ⟨hz, hz_bnd⟩
    -- The chain does not overflow.
    have hw := rndUnbounded_satisfies F .toOdd (z : ℝ) h₁u
    set w := rndUnbounded F .toOdd (z : ℝ) h₁u with hw_def
    have hw_bnd : Format.boundOK F.b w :=
      toOdd_toOdd_noOverflow_chain hsub hreg hp_F₂ h₁u hy hbOK hz hw
    have hwR : RoundsInBound F .toOdd (z : ℝ) w := ⟨hw, hw_bnd⟩
    -- Double rounding holds: restrict the chain, compose spec-relationally,
    -- and lift back along the in-bound direct rounding.
    have hsub_u : F.toFormat ⊆ F₂.unbounded.toFormat :=
      Format.subset_of_mem hsub.specials fun d hd =>
      mem_unbounded_of_mem (F := F₂)
        (hsub d ⟨hd.1, hd.2.1, boundOK_boundAfterNext_of_boundOK hd.2.2⟩)
    have hw_bdd : RoundsFinite F .toOdd (z : ℝ) w :=
      RoundsFinite.toOdd_restrict hw hw_bnd
    have hxw : RoundsFinite F .toOdd x w := roundsRTO_RTO_finite hsub_u hp_F₂ hz hw_bdd
    exact ⟨z, w, hzR, hwR, ⟨RoundsFinite.toOdd_lift hxw hy hbOK, hw_bnd⟩⟩
  · left
    exact ⟨_, hy, hbOK⟩

/-- **rnd-RTO-RTO**, no overflow from the chain: if the chain stays in bound, so does the direct
rounding. -/
theorem roundsRTO_RTO_noOverflow {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p) (h₁u : ¬ F₁.IsUndefined .toOdd)
    (hnt : F₁.toFormat.Nontrivial) {x : ℝ} {z w : Dyadic}
    (hz : RoundsInBound F₂ .toOdd x z) (hw : RoundsInBound F₁ .toOdd (z : ℝ) w) :
    ¬ Overflows F₁ .toOdd x :=
  not_overflows_of_floor hnt hw fun _ D hF₁b hreg_G hmono _ _ hbw hy => by
    set G := FiniteFormat.withBoundFF F₁ (D : Bound)
    have hsubG : (G.toFormat.withBound G.toFormat.boundAfterNext) ⊆ F₂.toFormat :=
      Format.subset_of_mem hsub.specials fun v hv => hsub v ⟨hv.1, hv.2.1,
        boundOK_boundAfterNext_mono (G := G) hF₁b rfl rfl hmono hv.2.2⟩
    exact toOdd_toOdd_noOverflow_direct hsubG hreg_G hp_F₂ h₁u hz.1 hw.1 hbw hy

/-- **rnd-RTO-RTZ**, total form. Either rounding `x` directly in `F₁` (RTZ)
overflows, or the RTO rounding of `x` in `F₂` does not overflow (finite `z`),
the chained RTZ rounding is finite (`w`), and double rounding holds.
Nontriviality of `F₁` forces `2 ≤ F₂.p` through the containment. -/
theorem roundsRTO_RTZ_inBound {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial) (x : ℝ) :
    Overflows F₁ .toZero x ∨
    (∃ z w : Dyadic, RoundsInBound F₂ .toOdd x z ∧
      RoundsInBound F₁ .toZero (z : ℝ) w ∧
      RoundsInBound F₁ .toZero x w) := by
  have hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p := two_le_p_of_nontrivial hsub hnt
  -- Reduce to a bound that is on the grid (and positive when `exp = ⊥`)
  -- by replacing it with its grid floor.
  suffices key : ∀ F : FiniteFormat,
      ((F.extend 1).toFormat.withBound F.toFormat.boundAfterNext) ⊆ F₂.toFormat →
      (∀ b : NonNegDyadic, F.b = (b : Bound) →
        b.val ∈ F ∧ (F.exp = ⊥ → 0 < ((b.val : Dyadic) : ℝ))) →
      Overflows F .toZero x ∨
      (∃ z w : Dyadic, RoundsInBound F₂ .toOdd x z ∧
        RoundsInBound F .toZero (z : ℝ) w ∧
        RoundsInBound F .toZero x w) by
    rcases hF₁b : F₁.b with _ | b₁
    · exact key F₁ hsub (regular_of_bound_top hF₁b)
    · rcases bound_floor_setup hF₁b with ⟨hexp, hb₁0⟩ |
        ⟨D, hreg_G, hD_le, hD_max, hmono, -⟩
      · exact rounds_total_of_zero_bound (not_isUndefined_toZero F₁)
          (not_isUndefined_of_two_le_p hp_F₂)
          (fun hy hy0 => eq_zero_of_toZero_zero hexp hy hy0)
          (fun hz => by rw [RoundsFinite.eq_zero_of_zero hz, Dyadic.coe_real_zero])
          hF₁b hb₁0 x
      · exact rounds_floor_lift hD_le hD_max (key _
          (Format.subset_of_mem hsub.specials fun v hv => hsub v ⟨hv.1, hv.2.1,
            boundOK_boundAfterNext_mono
              (G := FiniteFormat.withBoundFF F₁ (D : Bound))
              hF₁b rfl rfl hmono hv.2.2⟩) hreg_G)
  intro F hsub hreg
  have h₁u := not_isUndefined_toZero F
  have h₂u : ¬ F₂.IsUndefined .toOdd := not_isUndefined_of_two_le_p hp_F₂
  have hy := rndUnbounded_satisfies F .toZero x h₁u
  set y := rndUnbounded F .toZero x h₁u with hy_def
  by_cases hbOK : Format.boundOK F.b y
  · right
    have hz := rndUnbounded_satisfies F₂ .toOdd x h₂u
    set z := rndUnbounded F₂ .toOdd x h₂u with hz_def
    -- F₂ does not overflow.
    have hz_bnd : Format.boundOK F₂.b z := by
      rcases hFb : F.b with _ | b₁
      · -- `b₁ = ⊤` forces `b₂ = ⊤` (the containment swallows the whole grid).
        have h1 : ((F.extend 1).toFormat.withBound ⊤) ⊆ F₂.toFormat := by
          rw [← Format.boundAfterNext_top hFb]; exact hsub
        rw [bound_top_of_withBound_top_subset h1]
        trivial
      · obtain ⟨hb₁_mem, hguard⟩ := hreg b₁ hFb
        obtain ⟨hb₁_nn, hN_lt, hN_nn, hN_mem⟩ := next_facts hb₁_mem
        have hN_F₂ : F.toFormat.next b₁.val ∈ F₂ :=
          hsub _ (mem_extend_one_withBound_of_mem_unbounded hN_mem
            (boundOK_boundAfterNext_next hFb hN_nn))
        have hxN : |x| < ((F.toFormat.next b₁.val : Dyadic) : ℝ) :=
          abs_lt_next_of_toZero_inbound hFb hb₁_mem hy hbOK
        have hz_abs : |(z : ℝ)| ≤ ((F.toFormat.next b₁.val : Dyadic) : ℝ) :=
          abs_faithful_le_of_le (mem_unbounded_of_mem hN_F₂) hxN.le hz.2.1
        exact boundOK_of_abs_le (by rwa [abs_of_nonneg hN_nn]) hN_F₂.2.2
    have hzR : RoundsInBound F₂ .toOdd x z := ⟨hz, hz_bnd⟩
    -- The chain does not overflow.
    have hw := rndUnbounded_satisfies F .toZero (z : ℝ) h₁u
    set w := rndUnbounded F .toZero (z : ℝ) h₁u with hw_def
    have hw_bnd : Format.boundOK F.b w :=
      toOdd_toZero_noOverflow_chain hsub hreg hp_F₂ hy hbOK hz hw
    have hwR : RoundsInBound F .toZero (z : ℝ) w := ⟨hw, hw_bnd⟩
    -- Double rounding holds: restrict the chain, compose spec-relationally,
    -- and lift back along the in-bound direct rounding.
    have hsub_u : ((F.extend 1).toFormat.withBound F.toFormat.boundAfterNext)
        ⊆ F₂.unbounded.toFormat :=
      Format.subset_of_mem hsub.specials fun d hd =>
      mem_unbounded_of_mem (F := F₂) (hsub d hd)
    have hw_bdd : RoundsFinite F .toZero (z : ℝ) w :=
      RoundsFinite.toZero_restrict hw hw_bnd
    have hxw : RoundsFinite F .toZero x w := roundsRTO_RTZ_finite hsub_u hz hw_bdd
    exact ⟨z, w, hzR, hwR, ⟨RoundsFinite.toZero_lift hxw hy hbOK, hw_bnd⟩⟩
  · left
    exact ⟨_, hy, hbOK⟩

/-- **rnd-RTO-RTZ**, no overflow from the chain: if the chain stays in bound, so does the direct
rounding. -/
theorem roundsRTO_RTZ_noOverflow {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial) {x : ℝ} {z w : Dyadic}
    (hz : RoundsInBound F₂ .toOdd x z) (hw : RoundsInBound F₁ .toZero (z : ℝ) w) :
    ¬ Overflows F₁ .toZero x :=
  not_overflows_of_floor hnt hw fun _ D hF₁b hreg_G hmono _ _ hbw hy => by
    set G := FiniteFormat.withBoundFF F₁ (D : Bound)
    have hsubG : ((G.extend 1).toFormat.withBound G.toFormat.boundAfterNext) ⊆ F₂.toFormat :=
      Format.subset_of_mem hsub.specials fun v hv => hsub v ⟨hv.1, hv.2.1,
        boundOK_boundAfterNext_mono (G := G) hF₁b rfl rfl hmono hv.2.2⟩
    exact toZero_noOverflow_direct hreg_G
      (fun _ hb hm => next_mem_of_extend_withBound_subset hsubG hb hm)
      hz.1.isFaithfulRound hw.1 hbw hy

/-- **rnd-RTO-RAZ**, total form. Either rounding `x` directly in `F₁` (RAZ)
overflows, or the RTO rounding of `x` in `F₂` does not overflow (finite `z`),
the chained RAZ rounding is finite (`w`), and double rounding holds.
Nontriviality of `F₁` forces, through the containment, that `F₂` supports
RTO. -/
theorem roundsRTO_RAZ_inBound {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial) (x : ℝ) :
    Overflows F₁ .awayZero x ∨
    (∃ z w : Dyadic, RoundsInBound F₂ .toOdd x z ∧
      RoundsInBound F₁ .awayZero (z : ℝ) w ∧
      RoundsInBound F₁ .awayZero x w) := by
  have h₂u : ¬ F₂.IsUndefined .toOdd :=
    not_isUndefined_of_two_le_p (two_le_p_of_nontrivial hsub hnt)
  have h₁u := not_isUndefined_awayZero F₁
  have hy := rndUnbounded_satisfies F₁ .awayZero x h₁u
  set y := rndUnbounded F₁ .awayZero x h₁u with hy_def
  by_cases hbOK : Format.boundOK F₁.b y
  · right
    -- F₂ does not overflow.
    have hz := rndUnbounded_satisfies F₂ .toOdd x h₂u
    set z := rndUnbounded F₂ .toOdd x h₂u with hz_def
    obtain ⟨hzy_abs, hzy_sign⟩ := toOdd_abs_le_of_awayZero hsub hy hbOK hz
    have hyF₂ : y ∈ F₂ :=
      hsub y (mem_extend_one_withBound_of_mem (mem_of_mem_unbounded_of_boundOK hy.1 hbOK))
    have hz_bnd : Format.boundOK F₂.b z := boundOK_of_abs_le hzy_abs hyF₂.2.2
    have hzR : RoundsInBound F₂ .toOdd x z := ⟨hz, hz_bnd⟩
    -- The chain does not overflow: `y` competes for `w` at the point `z`.
    have hw := rndUnbounded_satisfies F₁ .awayZero (z : ℝ) h₁u
    set w := rndUnbounded F₁ .awayZero (z : ℝ) h₁u with hw_def
    have hw_bnd : Format.boundOK F₁.b w := by
      have h1 := hw.2.2.2 y hy.1 hzy_abs hzy_sign
      exact boundOK_of_abs_le h1 hbOK
    have hwR : RoundsInBound F₁ .awayZero (z : ℝ) w := ⟨hw, hw_bnd⟩
    -- Double rounding holds: restrict the chain, compose spec-relationally,
    -- and lift back along the in-bound direct rounding.
    have hsub_u : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext)
        ⊆ F₂.unbounded.toFormat :=
      Format.subset_of_mem hsub.specials fun d hd =>
      mem_unbounded_of_mem (F := F₂) (hsub d hd)
    have hw_bdd : RoundsFinite F₁ .awayZero (z : ℝ) w :=
      RoundsFinite.awayZero_restrict hw hw_bnd
    have hxw : RoundsFinite F₁ .awayZero x w := roundsRTO_RAZ_finite hsub_u hz hw_bdd
    exact ⟨z, w, hzR, hwR, ⟨RoundsFinite.awayZero_lift hxw hy hbOK, hw_bnd⟩⟩
  · left
    exact ⟨_, hy, hbOK⟩

/-- **rnd-RTO-RAZ**, no overflow from the chain: the chained rounding is a candidate for the
direct one (RTO padding), so it bounds it. -/
theorem roundsRTO_RAZ_noOverflow {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial) {x : ℝ} {z w : Dyadic}
    (hz : RoundsInBound F₂ .toOdd x z) (hw : RoundsInBound F₁ .awayZero (z : ℝ) w) :
    ¬ Overflows F₁ .awayZero x := by
  rintro ⟨y, hy, hby⟩
  obtain ⟨hxw, hwx⟩ := toOdd_awayZero_candidate hsub
    (two_le_p_of_nontrivial hsub hnt) hz.1 hw.1 hw.2
  exact hby (awayZero_noOverflow_direct hw.1.1 hxw hwx hw.2 hy)

/-- **rnd-RTO-RN**, total form, parameterized by the tie-break `tb`. Either
rounding `x` directly in `F₁` (RN) overflows, or the RTO rounding of `x` in
`F₂` does not overflow (finite `z`), the chained RN rounding is finite (`w`),
and double rounding holds. Nontriviality of `F₁` forces `2 ≤ F₂.p` through
the containment; `F₁` must support the tie-break (vacuous for RNA). -/
theorem roundsRTO_RN_inBound {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
      ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial)
    {tb : TieBreak} (h₁u : ¬ F₁.IsUndefined (.nearest tb)) (x : ℝ) :
    Overflows F₁ (.nearest tb) x ∨
    (∃ z w : Dyadic, RoundsInBound F₂ .toOdd x z ∧
      RoundsInBound F₁ (.nearest tb) (z : ℝ) w ∧
      RoundsInBound F₁ (.nearest tb) x w) := by
  have hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p := two_le_p_of_nontrivial_extend_two hsub hnt
  -- Reduce to a bound that is on the grid (and positive when `exp = ⊥`)
  -- by replacing it with its grid floor.
  suffices key : ∀ F : FiniteFormat,
      ((F.extend 2).toFormat.withBound (F.extend 1).toFormat.boundAfterNext)
        ⊆ F₂.toFormat →
      (∀ b : NonNegDyadic, F.b = (b : Bound) →
        b.val ∈ F ∧ (F.exp = ⊥ → 0 < ((b.val : Dyadic) : ℝ))) →
      ¬ F.IsUndefined (.nearest tb) →
      Overflows F (.nearest tb) x ∨
      (∃ z w : Dyadic, RoundsInBound F₂ .toOdd x z ∧
        RoundsInBound F (.nearest tb) (z : ℝ) w ∧
        RoundsInBound F (.nearest tb) x w) by
    rcases hF₁b : F₁.b with _ | b₁
    · exact key F₁ hsub (regular_of_bound_top hF₁b) h₁u
    · rcases bound_floor_setup hF₁b with ⟨hexp, hb₁0⟩ |
        ⟨D, hreg_G, hD_le, hD_max, -, hmono_ext⟩
      · exact rounds_total_of_zero_bound h₁u (not_isUndefined_of_two_le_p hp_F₂)
          (fun hy hy0 => eq_zero_of_faithful_zero hexp (nearest_components hy).2.1 hy0)
          (fun hz => by rw [RoundsFinite.eq_zero_of_zero hz, Dyadic.coe_real_zero])
          hF₁b hb₁0 x
      · exact rounds_floor_lift hD_le hD_max (key _
          (Format.subset_of_mem hsub.specials fun v hv => hsub v ⟨hv.1, hv.2.1,
            boundOK_boundAfterNext_mono (F := F₁.extend 1)
              (G := (FiniteFormat.withBoundFF F₁ (D : Bound)).extend 1)
              hF₁b rfl rfl hmono_ext hv.2.2⟩) hreg_G h₁u)
  intro F hsub hreg h₁u
  have h₂u : ¬ F₂.IsUndefined .toOdd := not_isUndefined_of_two_le_p hp_F₂
  have hy := rndUnbounded_satisfies F (.nearest tb) x h₁u
  set y := rndUnbounded F (.nearest tb) x h₁u with hy_def
  by_cases hbOK : Format.boundOK F.b y
  · right
    have hz := rndUnbounded_satisfies F₂ .toOdd x h₂u
    set z := rndUnbounded F₂ .toOdd x h₂u with hz_def
    -- F₂ does not overflow.
    have hz_bnd : Format.boundOK F₂.b z := by
      rcases hFb : F.b with _ | b₁
      · have hB_top : (F.extend 1).toFormat.boundAfterNext = ⊤ :=
          Format.boundAfterNext_top hFb
        rw [hB_top] at hsub
        rw [bound_top_of_withBound_top_subset hsub]
        trivial
      · obtain ⟨hb₁_mem, hguard⟩ := hreg b₁ hFb
        obtain ⟨hymem, hyfaithful, hyclose⟩ := nearest_components hy
        have hxM : |x| ≤ (((F.extend 1).toFormat.next b₁.val : Dyadic) : ℝ) :=
          abs_le_mid_of_nearest_inbound hFb hb₁_mem hguard hyfaithful hyclose hbOK
        have hM_F₂ : (F.extend 1).toFormat.next b₁.val ∈ F₂ :=
          hsub _ (next_mem_extend_two_withBound hFb hb₁_mem)
        have hb₁_nn : 0 ≤ ((b₁.val : Dyadic) : ℝ) := nonneg_coe_real b₁
        have hM_nn : 0 ≤ (((F.extend 1).toFormat.next b₁.val : Dyadic) : ℝ) :=
          Format.next_nonneg (F.extend 1).toFormat b₁.val hb₁_nn
        have hz_abs : |(z : ℝ)| ≤ (((F.extend 1).toFormat.next b₁.val : Dyadic) : ℝ) :=
          abs_faithful_le_of_le (mem_unbounded_of_mem hM_F₂) hxM hz.2.1
        exact boundOK_of_abs_le (by rwa [abs_of_nonneg hM_nn]) hM_F₂.2.2
    have hzR : RoundsInBound F₂ .toOdd x z := ⟨hz, hz_bnd⟩
    -- The chain does not overflow.
    have hw := rndUnbounded_satisfies F (.nearest tb) (z : ℝ) h₁u
    set w := rndUnbounded F (.nearest tb) (z : ℝ) h₁u with hw_def
    have hw_bnd : Format.boundOK F.b w :=
      toOdd_nearest_noOverflow_chain hsub hreg hp_F₂ h₁u hy hbOK hz hw
    have hwR : RoundsInBound F (.nearest tb) (z : ℝ) w := ⟨hw, hw_bnd⟩
    -- Double rounding holds: restrict the chain, compose spec-relationally,
    -- and lift back along the in-bound direct rounding.
    have hsub_u : ((F.extend 2).toFormat.withBound (F.extend 1).toFormat.boundAfterNext)
        ⊆ F₂.unbounded.toFormat :=
      Format.subset_of_mem hsub.specials fun d hd =>
      mem_unbounded_of_mem (F := F₂) (hsub d hd)
    have hw_bdd : RoundsFinite F (.nearest tb) (z : ℝ) w :=
      RoundsFinite.nearest_restrict hw hw_bnd
    have hxw : RoundsFinite F (.nearest tb) x w := roundsRTO_RN_finite hsub_u hz hw_bdd
    exact ⟨z, w, hzR, hwR, ⟨RoundsFinite.nearest_lift hxw hy hbOK, hw_bnd⟩⟩
  · left
    exact ⟨_, hy, hbOK⟩

/-- **rnd-RTO-RN**, no overflow from the chain: if the chain stays in bound, so does the direct
rounding. -/
theorem roundsRTO_RN_noOverflow {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
      ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial) {tb : TieBreak} (h₁u : ¬ F₁.IsUndefined (.nearest tb))
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsInBound F₂ .toOdd x z) (hw : RoundsInBound F₁ (.nearest tb) (z : ℝ) w) :
    ¬ Overflows F₁ (.nearest tb) x :=
  not_overflows_of_floor hnt hw fun _ D hF₁b hreg_G _ hmono_ext _ hbw hy => by
    set G := FiniteFormat.withBoundFF F₁ (D : Bound)
    have hsubG : ((G.extend 2).toFormat.withBound (G.extend 1).toFormat.boundAfterNext)
          ⊆ F₂.toFormat :=
      Format.subset_of_mem hsub.specials fun v hv => hsub v ⟨hv.1, hv.2.1,
        boundOK_boundAfterNext_mono (F := F₁.extend 1) (G := G.extend 1)
          hF₁b rfl rfl hmono_ext hv.2.2⟩
    exact toOdd_nearest_noOverflow_direct hsubG hreg_G (two_le_p_of_nontrivial_extend_two hsub hnt)
      h₁u hz.1 hw.1 hbw hy

end Mpfx
