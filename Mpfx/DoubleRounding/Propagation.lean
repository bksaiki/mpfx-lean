import Mpfx.DoubleRounding.Basic
import Mpfx.Rounding.Restrict

/-!
# The midpoint for round-to-nearest

Overflow facts for RTO → RN, which `localDoubleRounding_RTO_RN` in
`Mpfx.DoubleRounding.Total` assembles. With the bound `b₁` on the grid and `M`
the midpoint of `b₁` and `next(b₁)`: an in-bound nearest rounding puts its
input within `M` (`abs_le_mid_of_nearest_inbound`), a nearest rounding of an
input strictly inside `M` stays in bound (`nearest_boundOK_of_abs_lt_mid`), and
an inexact RTO result never lands on `±M` (`abs_lt_mid_of_toOdd`).
-/

namespace Mpfx

/-- The mode-independent components of a `.nearest` rounding spec:
membership, faithfulness, and the closest-distance clause. -/
theorem nearest_components {F : FiniteFormat} {tb : TieBreak} {x : ℝ}
    {y : Dyadic} (h : RoundsFinite F (.nearest tb) x y) :
    y ∈ F ∧ IsFaithfulRound F x y ∧
      ∀ c : Dyadic, c ∈ F → IsFaithfulRound F x c →
        |x - (y : ℝ)| ≤ |x - (c : ℝ)| :=
  ⟨h.1, h.isFaithfulRound, fun _ hc hcf => h.nearest_min hc hcf⟩

/-- The midpoint `M = nextᵉ(b₁)` lies in the paper RN containment format
`(F₁.extend 2).withBound (F₁.extend 1).boundAfterNext`. -/
theorem next_mem_extend_two_withBound {F₁ : FiniteFormat} {b₁ : NonNegDyadic}
    (hF₁b : F₁.b = (b₁ : Bound)) (hb₁_mem : b₁.val ∈ F₁) :
    (F₁.extend 1).toFormat.next b₁.val
      ∈ ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext) := by
  have hb₁_nn : 0 ≤ ((b₁.val : Dyadic) : ℝ) := nonneg_coe_real b₁
  have hb₁_memx : b₁.val ∈ (F₁.extend 1).unbounded := by
    have h := Format.self_subset_extend F₁.toFormat.unbounded 1 b₁.val
      (mem_unbounded_of_mem hb₁_mem)
    exact ⟨h.1, h.2.1, trivial⟩
  have hM_mem : (F₁.extend 1).toFormat.next b₁.val ∈ (F₁.extend 1).unbounded :=
    next_mem_unbounded' hb₁_memx hb₁_nn
  have hM_nn : 0 ≤ (((F₁.extend 1).toFormat.next b₁.val : Dyadic) : ℝ) :=
    Format.next_nonneg (F₁.extend 1).toFormat b₁.val hb₁_nn
  have hmono := Format.extend_mono F₁.toFormat.unbounded
    (by exact_mod_cast (by omega : (1 : ℕ) ≤ 2) : (1 : ℕ) ≤ 2)
  have h2 := hmono _ hM_mem
  exact ⟨h2.1, h2.2.1,
    boundOK_boundAfterNext_next (F₁ := F₁.extend 1) hF₁b hM_nn⟩

/-- An in-bound RN rounding pins `|x|` to at most the midpoint
`M = nextᵉ(b₁)` of `b₁` and `next(b₁)`: beyond the midpoint, the
away-side candidate `±next(b₁)` is strictly closer than anything in-bound. -/
theorem abs_le_mid_of_nearest_inbound {F₁ : FiniteFormat}
    {b₁ : NonNegDyadic}
    (hF₁b : F₁.b = (b₁ : Bound)) (hb₁_mem : b₁.val ∈ F₁)
    (hguard : F₁.exp = ⊥ → 0 < ((b₁.val : Dyadic) : ℝ))
    {x : ℝ} {y : Dyadic}
    (hyfaithful : IsFaithfulRound F₁.unbounded x y)
    (hyclose : ∀ c : Dyadic, c ∈ F₁.unbounded → IsFaithfulRound F₁.unbounded x c →
      |x - (y : ℝ)| ≤ |x - (c : ℝ)|)
    (hby : Format.boundOK F₁.b y) :
    |x| ≤ (((F₁.extend 1).toFormat.next b₁.val : Dyadic) : ℝ) := by
  obtain ⟨hb₁_nn, hN_lt, -, hN_mem⟩ := next_facts hb₁_mem
  set N := F₁.toFormat.next b₁.val with hN_def
  set M := (F₁.extend 1).toFormat.next b₁.val with hM_def
  have hM_mid : (M : ℝ) = (((b₁.val : Dyadic) : ℝ) + (N : ℝ)) / 2 :=
    next_extend_midpoint' hb₁_nn hguard
  have hb₁_lt_M : ((b₁.val : Dyadic) : ℝ) < (M : ℝ) := by
    rw [hM_mid]; linarith
  have hy_le : |(y : ℝ)| ≤ ((b₁.val : Dyadic) : ℝ) :=
    abs_coe_real_le_of_boundOK (hF₁b ▸ hby)
  have hy_bounds := abs_le.mp hy_le
  by_contra hxM; push Not at hxM
  by_cases hx_sign : 0 ≤ x
  · -- `M < x`.
    have hM_lt_x : (M : ℝ) < x := by rwa [abs_of_nonneg hx_sign] at hxM
    by_cases hxN : x ≤ (N : ℝ)
    · -- `M < x ≤ N`: `N` is RU-faithful and strictly closer than `y`.
      have hN_faithful : IsFaithfulRound F₁.unbounded x N := by
        right
        refine ⟨hN_mem, hxN, ?_⟩
        intro v hv hxv
        have hv_gt : ((b₁.val : Dyadic) : ℝ) < (v : ℝ) := by linarith
        exact next_min' (mem_unbounded_of_mem hb₁_mem) hv hb₁_nn hguard hv_gt
      have h1 := hyclose N hN_mem hN_faithful
      have h2 : |x - (N : ℝ)| = (N : ℝ) - x := by
        rw [abs_of_nonpos (by linarith)]; ring
      have h3 : x - (y : ℝ) ≤ |x - (y : ℝ)| := le_abs_self _
      linarith
    · -- `N < x`: both faithful candidates exceed `N`, breaking the bound.
      push Not at hxN
      rcases hyfaithful with ⟨-, -, hy_max⟩ | ⟨-, hx_le_y, -⟩
      · have h1 := hy_max N hN_mem hxN.le
        linarith
      · linarith
  · -- Mirror: `x < -M`.
    push Not at hx_sign
    have hx_lt_nM : x < -(M : ℝ) := by
      rw [abs_of_neg hx_sign] at hxM
      linarith
    have hnN_mem : (-N) ∈ F₁.unbounded := FiniteFormat.neg_mem hN_mem
    by_cases hxN : -(N : ℝ) ≤ x
    · -- `-N ≤ x < -M`: `-N` is RD-faithful and strictly closer than `y`.
      have hnN_faithful : IsFaithfulRound F₁.unbounded x (-N) := by
        left
        refine ⟨hnN_mem, by rw [Dyadic.coe_real_neg]; exact hxN, ?_⟩
        intro v hv hvx
        rw [Dyadic.coe_real_neg]
        by_contra hvb; push Not at hvb
        have h1 : ((b₁.val : Dyadic) : ℝ) < ((-v : Dyadic) : ℝ) := by
          rw [Dyadic.coe_real_neg]
          linarith
        have h2 := next_min' (mem_unbounded_of_mem hb₁_mem)
          (FiniteFormat.neg_mem hv) hb₁_nn hguard h1
        rw [Dyadic.coe_real_neg] at h2
        linarith
      have h1 := hyclose (-N) hnN_mem hnN_faithful
      have h2 : |x - ((-N : Dyadic) : ℝ)| = x + (N : ℝ) := by
        rw [Dyadic.coe_real_neg, abs_of_nonneg (by linarith)]; ring
      have h3 : (y : ℝ) - x ≤ |x - (y : ℝ)| := by
        rw [abs_sub_comm]; exact le_abs_self _
      linarith
    · -- `x < -N`: both faithful candidates are below `-N`.
      push Not at hxN
      rcases hyfaithful with ⟨-, hy_le_x, -⟩ | ⟨-, -, hy_min⟩
      · linarith
      · have h1 := hy_min (-N) hnN_mem (by rw [Dyadic.coe_real_neg]; linarith)
        rw [Dyadic.coe_real_neg] at h1
        linarith

/-- A nearest rounding of an input strictly inside the midpoint `M` of
`(b₁, next(b₁))` stays in bound: past `±b₁` the in-bound side is strictly
closer. -/
theorem nearest_boundOK_of_abs_lt_mid {F₁ : FiniteFormat} {b₁ : NonNegDyadic}
    (hF₁b : F₁.b = (b₁ : Bound)) (hb₁_mem : b₁.val ∈ F₁)
    (hguard : F₁.exp = ⊥ → 0 < ((b₁.val : Dyadic) : ℝ))
    {tb : TieBreak} {z : ℝ} {w : Dyadic}
    (hw : RoundsFinite F₁.unbounded (.nearest tb) z w)
    (hzM_lt : |z| < (((F₁.extend 1).toFormat.next b₁.val : Dyadic) : ℝ)) :
    Format.boundOK F₁.b w := by
  rw [hF₁b]
  obtain ⟨hwmem, hwfaithful, hwclose⟩ := nearest_components hw
  obtain ⟨hb₁_nn, hN_lt, -, -⟩ := next_facts hb₁_mem
  set N := F₁.toFormat.next b₁.val with hN_def
  set M := (F₁.extend 1).toFormat.next b₁.val with hM_def
  have hb₁_mem_u : b₁.val ∈ F₁.unbounded := mem_unbounded_of_mem hb₁_mem
  have hM_mid : (M : ℝ) = (((b₁.val : Dyadic) : ℝ) + (N : ℝ)) / 2 :=
    next_extend_midpoint' hb₁_nn hguard
  -- If `|z| ≤ b₁`, the chained rounding is squeezed in-bound directly.
  by_cases hzb : |z| ≤ ((b₁.val : Dyadic) : ℝ)
  · have hw_abs : |(w : ℝ)| ≤ ((b₁.val : Dyadic) : ℝ) :=
      abs_faithful_le_of_le hb₁_mem_u hzb hwfaithful
    have hb₁_ok : Format.boundOK ((b₁ : Bound)) b₁.val := by
      change |(b₁.val : ℚ)| ≤ ((b₁.val : Dyadic) : ℚ)
      rw [abs_of_nonneg (by exact_mod_cast b₁.2 : (0 : ℚ) ≤ (b₁.val : ℚ))]
    exact boundOK_of_abs_le (by rwa [abs_of_nonneg hb₁_nn]) hb₁_ok
  push Not at hzb
  -- Sign split: the chained rounding must stay on the `±b₁` side.
  by_contra hbw
  have hbw' : ((b₁.val : Dyadic) : ℝ) < |(w : ℝ)| :=
    lt_abs_coe_real_of_not_boundOK hbw
  by_cases hz_sign : 0 ≤ z
  · -- `b₁ < z < M`.
    have hz_gt : ((b₁.val : Dyadic) : ℝ) < z := by
      rwa [abs_of_nonneg hz_sign] at hzb
    have hz_lt : z < (M : ℝ) := by rwa [abs_of_nonneg hz_sign] at hzM_lt
    -- `b₁` is RD-faithful at `z`.
    have hb₁_faithful : IsFaithfulRound F₁.unbounded z b₁.val := by
      left
      refine ⟨hb₁_mem_u, hz_gt.le, ?_⟩
      intro v hv hvz
      by_contra hvb; push Not at hvb
      have h1 := next_min' hb₁_mem_u hv hb₁_nn hguard hvb
      linarith
    -- An out-of-bound `w` must be the RU candidate `≥ N`.
    have hw_ge_N : (N : ℝ) ≤ (w : ℝ) := by
      rcases hwfaithful with ⟨-, hw_le, hw_max⟩ | ⟨-, hw_ge, -⟩
      · exfalso
        have h1 : ((-(b₁.val) : Dyadic) : ℝ) ≤ (w : ℝ) := by
          apply hw_max _ (FiniteFormat.neg_mem hb₁_mem_u)
          rw [Dyadic.coe_real_neg]; linarith
        rw [Dyadic.coe_real_neg] at h1
        rcases le_or_gt 0 ((w : Dyadic) : ℝ) with h | h
        · rw [abs_of_nonneg h] at hbw'
          have h2 := next_min' hb₁_mem_u hwmem hb₁_nn hguard hbw'
          linarith
        · rw [abs_of_neg h] at hbw'
          linarith
      · have h1 : ((b₁.val : Dyadic) : ℝ) < (w : ℝ) := by linarith
        exact next_min' hb₁_mem_u hwmem hb₁_nn hguard h1
    -- Closest-distance contradiction across the midpoint.
    have h1 := hwclose b₁.val hb₁_mem_u hb₁_faithful
    have h2 : |z - ((b₁.val : Dyadic) : ℝ)|
        = z - ((b₁.val : Dyadic) : ℝ) := abs_of_nonneg (by linarith)
    have h3 : |z - ((w : Dyadic) : ℝ)| = (w : ℝ) - z := by
      rw [abs_sub_comm]
      exact abs_of_nonneg (by linarith)
    rw [h2, h3] at h1
    linarith
  · -- Mirror: `-M < z < -b₁`.
    push Not at hz_sign
    have hz_lt : z < -((b₁.val : Dyadic) : ℝ) := by
      rw [abs_of_neg hz_sign] at hzb
      linarith
    have hz_gt : -(M : ℝ) < z := by
      rw [abs_of_neg hz_sign] at hzM_lt
      linarith
    -- `-b₁` is RU-faithful at `z`.
    have hnb₁_faithful : IsFaithfulRound F₁.unbounded z
        (-(b₁.val)) := by
      right
      refine ⟨FiniteFormat.neg_mem hb₁_mem_u,
        by rw [Dyadic.coe_real_neg]; linarith, ?_⟩
      intro v hv hzv
      rw [Dyadic.coe_real_neg]
      by_contra hvb; push Not at hvb
      have h1 : ((b₁.val : Dyadic) : ℝ) < ((-v : Dyadic) : ℝ) := by
        rw [Dyadic.coe_real_neg]; linarith
      have h2 := next_min' hb₁_mem_u (FiniteFormat.neg_mem hv) hb₁_nn hguard h1
      rw [Dyadic.coe_real_neg] at h2
      linarith
    -- An out-of-bound `w` must be the RD candidate `≤ -N`.
    have hw_le_nN : (w : ℝ) ≤ -(N : ℝ) := by
      rcases hwfaithful with ⟨-, hw_le, -⟩ | ⟨-, hw_ge, hw_min⟩
      · have h1 : ((b₁.val : Dyadic) : ℝ) < ((-w : Dyadic) : ℝ) := by
          rw [Dyadic.coe_real_neg]; linarith
        have h2 := next_min' hb₁_mem_u (FiniteFormat.neg_mem hwmem) hb₁_nn hguard h1
        rw [Dyadic.coe_real_neg] at h2
        linarith
      · exfalso
        have h1 : (w : ℝ) ≤ ((-(b₁.val) : Dyadic) : ℝ) := by
          apply hw_min _ (FiniteFormat.neg_mem hb₁_mem_u)
          rw [Dyadic.coe_real_neg]; linarith
        rw [Dyadic.coe_real_neg] at h1
        rcases le_or_gt 0 ((w : Dyadic) : ℝ) with h | h
        · rw [abs_of_nonneg h] at hbw'
          linarith
        · rw [abs_of_neg h] at hbw'
          have h2 := next_min' hb₁_mem_u (FiniteFormat.neg_mem hwmem) hb₁_nn hguard
            (by rw [Dyadic.coe_real_neg]; linarith)
          rw [Dyadic.coe_real_neg] at h2
          linarith
    -- Closest-distance contradiction across the midpoint.
    have h1 := hwclose (-(b₁.val)) (FiniteFormat.neg_mem hb₁_mem_u) hnb₁_faithful
    have h2 : |z - ((-(b₁.val) : Dyadic) : ℝ)|
        = -((b₁.val : Dyadic) : ℝ) - z := by
      rw [Dyadic.coe_real_neg, abs_of_nonpos (by linarith)]
      ring
    have h3 : |z - ((w : Dyadic) : ℝ)| = z - (w : ℝ) :=
      abs_of_nonneg (by linarith)
    rw [h2, h3] at h1
    linarith

/-- RTO padding at the midpoint: an inexact RTO rounding into `F₂` cannot land on
`±M`, `M` the midpoint of `(b₁, next(b₁))`, since `M` has a free trailing digit
in `F₂` (through the `extend 2` containment). -/
theorem abs_lt_mid_of_toOdd {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
      ⊆ F₂.toFormat)
    {b₁ : NonNegDyadic} (hF₁b : F₁.b = (b₁ : Bound)) (hb₁_mem : b₁.val ∈ F₁)
    (hguard : F₁.exp = ⊥ → 0 < ((b₁.val : Dyadic) : ℝ))
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p) {x : ℝ} {z : Dyadic}
    (hz : RoundsFinite F₂.unbounded .toOdd x z) (hxz : x ≠ (z : ℝ))
    (hzM : |(z : ℝ)| ≤ (((F₁.extend 1).toFormat.next b₁.val : Dyadic) : ℝ)) :
    |(z : ℝ)| < (((F₁.extend 1).toFormat.next b₁.val : Dyadic) : ℝ) := by
  obtain ⟨hb₁_nn, hN_lt, -, -⟩ := next_facts hb₁_mem
  set M := (F₁.extend 1).toFormat.next b₁.val with hM_def
  have hb₁_mem_u : b₁.val ∈ F₁.unbounded := mem_unbounded_of_mem hb₁_mem
  have hM_nn : 0 ≤ (M : ℝ) := by
    rw [next_extend_midpoint' hb₁_nn hguard]; linarith
  have h_notmem : z ∉ FiniteFormat.withBoundFF (F₁.extend 1)
      ((F₁.extend 1).toFormat.boundAfterNext) := by
    apply toOdd_notMem_of_extend_subset (F₂ := F₂.unbounded) ?_ hp_F₂ hz hxz
    exact ((Format.extend_one_extend_one_subset_extend_two
      (F₁.toFormat.withBound ((F₁.extend 1).toFormat.boundAfterNext))).trans hsub).trans
      F₂.subset_unbounded
  have hM_G' : M ∈ FiniteFormat.withBoundFF (F₁.extend 1)
      ((F₁.extend 1).toFormat.boundAfterNext) := by
    have hb₁_memx : b₁.val ∈ (F₁.extend 1).unbounded := by
      have h' := Format.self_subset_extend F₁.toFormat.unbounded 1 b₁.val hb₁_mem_u
      exact ⟨h'.1, h'.2.1, trivial⟩
    have hM_mem : M ∈ (F₁.extend 1).unbounded := next_mem_unbounded' hb₁_memx hb₁_nn
    exact ⟨hM_mem.1, hM_mem.2.1,
      boundOK_boundAfterNext_next (F₁ := F₁.extend 1) hF₁b hM_nn⟩
  have hzM_lt : |(z : ℝ)| < (M : ℝ) := by
    rcases lt_or_eq_of_le hzM with h | h
    · exact h
    · exfalso
      rcases (abs_eq hM_nn).mp h with hz_eq | hz_eq
      · exact h_notmem ((Dyadic.coe_real_inj z M).mp hz_eq ▸ hM_G')
      · have h1 : z = -M := by
          apply (Dyadic.coe_real_inj z (-M)).mp
          rw [Dyadic.coe_real_neg]
          exact hz_eq
        exact h_notmem (h1 ▸ FiniteFormat.neg_mem hM_G')
  exact hzM_lt

end Mpfx
