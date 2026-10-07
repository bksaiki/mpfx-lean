import Mpfx.DoubleRounding.Nearest
import Mpfx.Rounding.Restrict

/-!
# Overflow propagation between the formats of a double rounding

Per rule, how the bound check moves between the direct rounding into `F₁`, the
rounding into `F₂`, and the chained rounding into `F₁`: no-overflow propagation
(`*_noOverflow_F₂`, `*_noOverflow_chain`: an in-bound direct rounding keeps
`F₂` and the chain in bound) and back (`*_noOverflow_direct`: an in-bound chain
keeps the direct rounding in bound). Each lemma assumes a regular bound (on the grid, positive
when `exp = ⊥`); `Mpfx.DoubleRounding.Total` reduces arbitrary bounds to it.
-/

namespace Mpfx

/-! ## rnd-RTZ-RTZ: no-overflow propagation

Unlike the spec-relational form, the total form needs the paper containment
`F₁.withBound F₁.boundAfterNext ⊆ F₂` in place of plain `F₁ ⊆ F₂`;
otherwise no-overflow propagation fails — e.g.
`F₁ = A(1, ⊥, 5)`, `F₂ = A(3, ⊥, 4)` satisfy the paper containment
(`A(1, ⊥, 6) ⊆ A(3, ⊥, 4)`), yet at `x = 5.2` the `F₁`-RTZ rounding is `4`
(no overflow) while the `F₂`-RTZ rounding is `5 > 4` (overflow). -/


/-- An in-bound RTZ rounding pins `x` strictly below `next(b₁)`: otherwise
`±next(b₁)` would compete and force `|y| > b₁`. -/
theorem abs_lt_next_of_toZero_inbound {F₁ : FiniteFormat}
    {b₁ : NonNegDyadic}
    (hF₁b : F₁.b = (b₁ : Bound)) (hb₁_mem : b₁.val ∈ F₁)
    {x : ℝ} {y : Dyadic}
    (hy : RoundsFinite F₁.unbounded .toZero x y) (hby : Format.boundOK F₁.b y) :
    |x| < ((F₁.toFormat.next b₁.val : Dyadic) : ℝ) := by
  obtain ⟨hb₁_nn, hN_lt, hN_nn, hN_mem⟩ := next_facts hb₁_mem
  set N := F₁.toFormat.next b₁.val with hN_def
  by_contra hxN; push Not at hxN
  obtain ⟨-, -, -, hymax⟩ := hy
  have hy_le : |(y : ℝ)| ≤ ((b₁.val : Dyadic) : ℝ) :=
    abs_coe_real_le_of_boundOK (hF₁b ▸ hby)
  by_cases hx_sign : 0 ≤ x
  · have habs : |(N : ℝ)| ≤ |x| := by rwa [abs_of_nonneg hN_nn]
    have hN_y := hymax N hN_mem habs (mul_nonneg hN_nn hx_sign)
    rw [abs_of_nonneg hN_nn] at hN_y
    linarith
  · push Not at hx_sign
    have hnN_mem : (-N) ∈ F₁.unbounded := FiniteFormat.neg_mem hN_mem
    have habs : |((-N : Dyadic) : ℝ)| ≤ |x| := by
      rwa [Dyadic.coe_real_neg, abs_neg, abs_of_nonneg hN_nn]
    have hsign : ((-N : Dyadic) : ℝ) * x ≥ 0 := by
      rw [Dyadic.coe_real_neg]; nlinarith
    have hN_y := hymax (-N) hnN_mem habs hsign
    rw [Dyadic.coe_real_neg, abs_neg, abs_of_nonneg hN_nn] at hN_y
    linarith

/-- No-overflow propagation for RTZ-RTZ: if the unbounded RTZ rounding `y`
of `x` in `F₁` is in-bound, then the unbounded RTZ rounding `z` of `x` in
`F₂` is in-bound: `|x| < next(b₁)` by `abs_lt_next_of_toZero_inbound`, and
`next(b₁) ∈ F₂` via the containment, so `|z| ≤ |x| < next(b₁)` is within
`F₂`'s bound. -/
theorem toZero_noOverflow_F₂ {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hreg : ∀ b : NonNegDyadic, F₁.b = (b : Bound) →
      b.val ∈ F₁ ∧ (F₁.exp = ⊥ → 0 < ((b.val : Dyadic) : ℝ)))
    {x : ℝ} {y z : Dyadic}
    (hy : RoundsFinite F₁.unbounded .toZero x y) (hby : Format.boundOK F₁.b y)
    (hz : RoundsFinite F₂.unbounded .toZero x z) :
    Format.boundOK F₂.b z := by
  rcases hF₁b : F₁.b with _ | b₁
  · -- `b₁ = ⊤` forces `b₂ = ⊤`.
    rw [b_eq_top_of_withBound_subset hsub hF₁b]
    trivial
  · obtain ⟨hb₁_mem, -⟩ := hreg b₁ hF₁b
    obtain ⟨hb₁_nn, hN_lt, hN_nn, hN_mem⟩ := next_facts hb₁_mem
    set N := F₁.toFormat.next b₁.val with hN_def
    have hxN : |x| < (N : ℝ) :=
      abs_lt_next_of_toZero_inbound hF₁b hb₁_mem hy hby
    -- `|z| ≤ |x| < N` and `N ∈ F₂`, so `z` is in-bound.
    have hN_F₂ : N ∈ F₂ := by
      apply hsub.mem
      exact ⟨hN_mem.1, hN_mem.2.1, boundOK_boundAfterNext_next hF₁b hN_nn⟩
    have hzN : |(z : ℝ)| ≤ |(N : ℝ)| := by
      rw [abs_of_nonneg hN_nn]
      exact le_trans hz.2.1 hxN.le
    exact boundOK_of_abs_le hzN hN_F₂.2.2

/-- Chain no-overflow for RTZ-RTZ: the unbounded RTZ rounding `w` of `z` in
`F₁` is in-bound, given that the direct rounding `y` is (`w` competes
against `y` at `x`). -/
theorem toZero_noOverflow_chain {F₁ F₂ : FiniteFormat} {x : ℝ}
    {y z w : Dyadic}
    (hy : RoundsFinite F₁.unbounded .toZero x y) (hby : Format.boundOK F₁.b y)
    (hz : RoundsFinite F₂.unbounded .toZero x z)
    (hw : RoundsFinite F₁.unbounded .toZero (z : ℝ) w) :
    Format.boundOK F₁.b w := by
  obtain ⟨hwmem, hwbnd, hwsign, -⟩ := hw
  obtain ⟨-, hzbnd, hzsign, -⟩ := hz
  have hwx_bnd : |(w : ℝ)| ≤ |x| := le_trans hwbnd hzbnd
  have hw0 : (z : ℝ) = 0 → (w : ℝ) = 0 := by
    intro h
    have h1 : |(w : ℝ)| ≤ 0 := by rw [← abs_zero, ← h]; exact hwbnd
    exact abs_nonpos_iff.mp h1
  have hwx_sign : (w : ℝ) * x ≥ 0 :=
    mul_nonneg_of_common_sign hwsign (by linarith [hzsign] : x * (z : ℝ) ≥ 0) hw0
  have hwy := hy.2.2.2 w hwmem hwx_bnd hwx_sign
  exact boundOK_of_abs_le hwy hby


/-! ## rnd-RAZ-RAZ: no-overflow propagation -/

/-- No-overflow propagation for RAZ: if the unbounded RAZ rounding `y` of `x`
in `F₁` is in-bound, then the unbounded RAZ rounding `z` of `x` in `F₂` is
in-bound (`y ∈ F₁ ⊆ F₂` competes, so `|z| ≤ |y|`). -/
theorem awayZero_noOverflow_F₂ {F₁ F₂ : FiniteFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat) {x : ℝ} {y z : Dyadic}
    (hy : RoundsFinite F₁.unbounded .awayZero x y) (hby : Format.boundOK F₁.b y)
    (hz : RoundsFinite F₂.unbounded .awayZero x z) :
    Format.boundOK F₂.b z := by
  obtain ⟨hymem, hybnd, hysign, _⟩ := hy
  obtain ⟨_, _, _, hzmin⟩ := hz
  have hyF₂ : y ∈ F₂ := hsub y (mem_of_mem_unbounded_of_boundOK hymem hby)
  have hzy : |(z : ℝ)| ≤ |(y : ℝ)| :=
    hzmin y (mem_unbounded_of_mem hyF₂) hybnd hysign
  exact boundOK_of_abs_le hzy hyF₂.2.2

/-- Chain no-overflow for RAZ-RAZ: the unbounded RAZ rounding `w` of `z` in
`F₁` is in-bound, given that the direct rounding `y` is. -/
theorem awayZero_noOverflow_chain {F₁ F₂ : FiniteFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat) {x : ℝ} {y z w : Dyadic}
    (hy : RoundsFinite F₁.unbounded .awayZero x y) (hby : Format.boundOK F₁.b y)
    (hz : RoundsFinite F₂.unbounded .awayZero x z)
    (hw : RoundsFinite F₁.unbounded .awayZero (z : ℝ) w) :
    Format.boundOK F₁.b w := by
  obtain ⟨hymem, hybnd, hysign, hymin⟩ := hy
  obtain ⟨_, hzbnd, hzsign, hzmin⟩ := hz
  obtain ⟨_, _, _, hwmin⟩ := hw
  -- `|z| ≤ |y|` since `y ∈ F₂.unbounded` competes for `z`.
  have hyF₂ : y ∈ F₂ := hsub y (mem_of_mem_unbounded_of_boundOK hymem hby)
  have hzy : |(z : ℝ)| ≤ |(y : ℝ)| :=
    hzmin y (mem_unbounded_of_mem hyF₂) hybnd hysign
  -- `y·z ≥ 0` (common sign through `x`; at `x = 0` minimality forces `y = 0`).
  have hy0 : x = 0 → (y : ℝ) = 0 := by
    intro hx
    have h0 := hymin 0 F₁.unbounded.toFormat.zero_mem
      (by rw [Dyadic.coe_real_zero, abs_zero, hx, abs_zero])
      (by rw [Dyadic.coe_real_zero, zero_mul])
    rw [Dyadic.coe_real_zero, abs_zero] at h0
    exact abs_nonpos_iff.mp h0
  have hyz : (y : ℝ) * (z : ℝ) ≥ 0 :=
    mul_nonneg_of_common_sign hysign hzsign hy0
  -- `y` competes for `w` at the point `z`.
  have hwy : |(w : ℝ)| ≤ |(y : ℝ)| := hwmin y hymem hzy hyz
  exact boundOK_of_abs_le hwy hby


/-! ## rnd-RTO-RAZ: no-overflow propagation -/


/-- The RTO rounding `z` of `x` in `F₂` is dominated (in magnitude, with
matching sign) by any in-bound RAZ rounding `y` of `x` in `F₁`: the faithful
candidates of `z` are squeezed between `0` and `±y`, since `y ∈ F₂` competes
on `z`'s side. -/
theorem toOdd_abs_le_of_awayZero {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {x : ℝ} {y z : Dyadic}
    (hy : RoundsFinite F₁.unbounded .awayZero x y) (hby : Format.boundOK F₁.b y)
    (hz : RoundsFinite F₂.unbounded .toOdd x z) :
    |(z : ℝ)| ≤ |(y : ℝ)| ∧ ((y : ℝ)) * ((z : ℝ)) ≥ 0 := by
  obtain ⟨hymem, hyabs, hysign, hymin⟩ := hy
  have hyF₂ : y ∈ F₂ :=
    hsub y (mem_extend_one_withBound_of_mem (mem_of_mem_unbounded_of_boundOK hymem hby))
  have hyF₂u : y ∈ F₂.unbounded := mem_unbounded_of_mem hyF₂
  rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
  · -- `x < 0`: `y ≤ x < 0`, both faithful candidates of `z` lie in `[y, 0]`.
    have hy_np : (y : ℝ) ≤ 0 := by nlinarith
    have hy_le_x : (y : ℝ) ≤ x := by
      have h := hyabs
      rw [abs_of_neg hx_neg, abs_of_nonpos hy_np] at h
      linarith
    obtain ⟨-, hfaithful, -⟩ := hz
    rcases hfaithful with ⟨-, hz_le, hz_max⟩ | ⟨-, hz_ge, hz_min⟩
    · have h1 : (y : ℝ) ≤ (z : ℝ) := hz_max y hyF₂u hy_le_x
      constructor
      · rw [abs_of_nonpos (by linarith), abs_of_nonpos hy_np]; linarith
      · nlinarith
    · have h1 : (z : ℝ) ≤ 0 := by
        have h := hz_min 0 F₂.unbounded.zero_mem
          (by rw [Dyadic.coe_real_zero]; linarith)
        rwa [Dyadic.coe_real_zero] at h
      constructor
      · rw [abs_of_nonpos h1, abs_of_nonpos hy_np]; linarith
      · nlinarith
  · -- `x = 0`: `z = 0`.
    have hz0 : z = 0 := RoundsFinite.eq_zero_of_zero (hx_zero ▸ hz)
    rw [hz0]
    constructor
    · rw [Dyadic.coe_real_zero, abs_zero]; exact abs_nonneg _
    · rw [Dyadic.coe_real_zero, mul_zero]
  · -- `x > 0`: mirror image.
    have hy_nn : 0 ≤ (y : ℝ) := by nlinarith
    have hx_le_y : x ≤ (y : ℝ) := by
      have h := hyabs
      rw [abs_of_pos hx_pos, abs_of_nonneg hy_nn] at h
      linarith
    obtain ⟨-, hfaithful, -⟩ := hz
    rcases hfaithful with ⟨-, hz_le, hz_max⟩ | ⟨-, hz_ge, hz_min⟩
    · have h1 : 0 ≤ (z : ℝ) := by
        have h := hz_max 0 F₂.unbounded.zero_mem
          (by rw [Dyadic.coe_real_zero]; linarith)
        rwa [Dyadic.coe_real_zero] at h
      constructor
      · rw [abs_of_nonneg h1, abs_of_nonneg hy_nn]; linarith
      · nlinarith
    · have h1 : (z : ℝ) ≤ (y : ℝ) := hz_min y hyF₂u hx_le_y
      constructor
      · rw [abs_of_nonneg (by linarith), abs_of_nonneg hy_nn]; linarith
      · nlinarith


/-! ## rnd-RTO-RTZ: no-overflow propagation -/


/-- The faithful candidates of any rounding of `x` in `F₂.unbounded` are
squeezed into `[-N, N]` once `|x| ≤ N` and `±N ∈ F₂.unbounded`. -/
theorem abs_faithful_le_of_le {F₂ : FiniteFormat} {x : ℝ} {z N : Dyadic}
    (hN_mem : N ∈ F₂.unbounded) (hxN : |x| ≤ (N : ℝ))
    (hfaithful : IsFaithfulRound F₂.unbounded x z) :
    |(z : ℝ)| ≤ (N : ℝ) := by
  have hnN_mem : (-N) ∈ F₂.unbounded := FiniteFormat.neg_mem hN_mem
  rcases hfaithful with ⟨-, hz_le, hz_max⟩ | ⟨-, hz_ge, hz_min⟩
  · have h1 : ((-N : Dyadic) : ℝ) ≤ (z : ℝ) := by
      apply hz_max (-N) hnN_mem
      rw [Dyadic.coe_real_neg]
      have := abs_le.mp hxN
      linarith [this.1]
    rw [Dyadic.coe_real_neg] at h1
    have h2 := abs_le.mp hxN
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · have h1 : (z : ℝ) ≤ (N : ℝ) := by
      apply hz_min N hN_mem
      have := abs_le.mp hxN
      linarith [this.2]
    have h2 := abs_le.mp hxN
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Chain no-overflow for RTO-RTZ. If the chained RTZ rounding `w` of
`z = RTO_{F₂}(x)` escaped the bound, grid minimality would force
`|w| = |z| = next(b₁)`; but `z` is `F₂`-odd (RTO-padding transfer through the
`extend 1` containment shows `z` cannot lie on the `F₁`-grid within the
relaxed bound), contradiction. -/
theorem toOdd_toZero_noOverflow_chain {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hreg : ∀ b : NonNegDyadic, F₁.b = (b : Bound) →
      b.val ∈ F₁ ∧ (F₁.exp = ⊥ → 0 < ((b.val : Dyadic) : ℝ)))
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {x : ℝ} {y z w : Dyadic}
    (hy : RoundsFinite F₁.unbounded .toZero x y) (hby : Format.boundOK F₁.b y)
    (hz : RoundsFinite F₂.unbounded .toOdd x z)
    (hw : RoundsFinite F₁.unbounded .toZero (z : ℝ) w) :
    Format.boundOK F₁.b w := by
  by_contra hbw
  -- The bound must be finite for the check to fail.
  obtain ⟨b₁, hF₁b⟩ : ∃ b₁ : NonNegDyadic, F₁.b = (b₁ : Bound) := by
    cases hc : F₁.b using Bound.recTopCoe with
    | top => rw [hc] at hbw; exact (hbw trivial).elim
    | coe b => exact ⟨b, rfl⟩
  obtain ⟨hb₁_mem, hguard⟩ := hreg b₁ hF₁b
  obtain ⟨hb₁_nn, hN_lt, hN_nn, hN_mem⟩ := next_facts hb₁_mem
  set N := F₁.toFormat.next b₁.val with hN_def
  -- `|x| < N` (no direct overflow), hence `|z| ≤ N`.
  have hxN : |x| < (N : ℝ) :=
    abs_lt_next_of_toZero_inbound hF₁b hb₁_mem hy hby
  have hN_F₂u : N ∈ F₂.unbounded :=
    mem_unbounded_of_mem
      (hsub N (mem_extend_one_withBound_of_mem_unbounded hN_mem
        (boundOK_boundAfterNext_next hF₁b hN_nn)))
  have hz_abs : |(z : ℝ)| ≤ (N : ℝ) :=
    abs_faithful_le_of_le hN_F₂u hxN.le hz.2.1
  -- `b₁ < |w| ≤ |z| ≤ N`, and grid minimality pins `|w| = N`.
  have hbw' : ((b₁.val : Dyadic) : ℝ) < |(w : ℝ)| :=
    lt_abs_coe_real_of_not_boundOK (hF₁b ▸ hbw)
  have hw_abs : |(w : ℝ)| ≤ |(z : ℝ)| := hw.2.1
  have hN_le_w : (N : ℝ) ≤ |(w : ℝ)| := by
    by_cases hw_sign : 0 ≤ (w : ℝ)
    · rw [abs_of_nonneg hw_sign] at hbw' ⊢
      exact next_min' (mem_unbounded_of_mem hb₁_mem) hw.1 hb₁_nn hguard hbw'
    · push Not at hw_sign
      rw [abs_of_neg hw_sign] at hbw' ⊢
      have h1 := next_min' (mem_unbounded_of_mem hb₁_mem)
        (FiniteFormat.neg_mem hw.1) hb₁_nn hguard (by rwa [Dyadic.coe_real_neg])
      rwa [Dyadic.coe_real_neg] at h1
  -- So `z = ±N`, and `z ≠ x`; `z` is the `F₂`-odd RTO result.
  have hzN : |(z : ℝ)| = (N : ℝ) := le_antisymm hz_abs (le_trans hN_le_w hw_abs)
  have hxz : x ≠ (z : ℝ) := by
    intro h
    rw [← h] at hzN
    linarith
  -- RTO-padding transfer: `z` cannot lie on the `F₁` grid within the relaxed
  -- bound — but `±N` does.
  set F₁wB : FiniteFormat := FiniteFormat.withBoundFF F₁ F₁.toFormat.boundAfterNext
    with hF₁wB_def
  have hsub' : ((F₁wB.extend 1)).toFormat ⊆ F₂.unbounded.toFormat :=
      Format.subset_of_mem hsub.specials fun d hd =>
    mem_unbounded_of_mem (F := F₂) (hsub d ⟨hd.1, hd.2.1, hd.2.2⟩)
  have h_notmem : z ∉ F₁wB :=
    toOdd_notMem_of_extend_subset hsub' hp_F₂ hz hxz
  have hN_wB : N ∈ F₁wB :=
    ⟨hN_mem.1, hN_mem.2.1, boundOK_boundAfterNext_next hF₁b hN_nn⟩
  rcases abs_eq hN_nn |>.mp hzN with hz_eq | hz_eq
  · exact h_notmem ((Dyadic.coe_real_inj z N).mp hz_eq ▸ hN_wB)
  · have h1 : z = -N := by
      apply (Dyadic.coe_real_inj z (-N)).mp
      rw [Dyadic.coe_real_neg]
      exact hz_eq
    exact h_notmem (h1 ▸ FiniteFormat.neg_mem hN_wB)


/-! ## rnd-RTO-RTO: no-overflow propagation -/

/-- An in-bound RTO rounding pins `x` strictly below `next(b₁)`: otherwise
both faithful candidates lie beyond `±next(b₁)`, forcing `|y| > b₁`. -/
theorem abs_lt_next_of_toOdd_inbound {F₁ : FiniteFormat}
    {b₁ : NonNegDyadic}
    (hF₁b : F₁.b = (b₁ : Bound)) (hb₁_mem : b₁.val ∈ F₁)
    {x : ℝ} {y : Dyadic}
    (hy : RoundsFinite F₁.unbounded .toOdd x y) (hby : Format.boundOK F₁.b y) :
    |x| < ((F₁.toFormat.next b₁.val : Dyadic) : ℝ) := by
  obtain ⟨hb₁_nn, hN_lt, hN_nn, hN_mem⟩ := next_facts hb₁_mem
  set N := F₁.toFormat.next b₁.val with hN_def
  by_contra hxN; push Not at hxN
  have hy_le : |(y : ℝ)| ≤ ((b₁.val : Dyadic) : ℝ) :=
    abs_coe_real_le_of_boundOK (hF₁b ▸ hby)
  obtain ⟨-, hfaithful, -⟩ := hy
  by_cases hx_sign : 0 ≤ x
  · -- `N ≤ x`: both faithful candidates are `≥ N`.
    have hN_le_x : (N : ℝ) ≤ x := by rwa [abs_of_nonneg hx_sign] at hxN
    rcases hfaithful with ⟨-, -, hy_max⟩ | ⟨-, hx_le_y, -⟩
    · have h1 := hy_max N hN_mem hN_le_x
      have h2 : (N : ℝ) ≤ |(y : ℝ)| := le_trans h1 (le_abs_self _)
      linarith
    · have h2 : (N : ℝ) ≤ |(y : ℝ)| :=
        le_trans (le_trans hN_le_x hx_le_y) (le_abs_self _)
      linarith
  · -- `x ≤ -N`: both faithful candidates are `≤ -N`.
    push Not at hx_sign
    have hx_le_nN : x ≤ -(N : ℝ) := by
      rw [abs_of_neg hx_sign] at hxN
      linarith
    have hnN_mem : (-N) ∈ F₁.unbounded := FiniteFormat.neg_mem hN_mem
    rcases hfaithful with ⟨-, hy_le_x, -⟩ | ⟨-, -, hy_min⟩
    · have h2 : (N : ℝ) ≤ |(y : ℝ)| := by
        rw [abs_of_nonpos (by linarith : (y : ℝ) ≤ 0)]
        linarith
      linarith
    · have h1 := hy_min (-N) hnN_mem (by rw [Dyadic.coe_real_neg]; linarith)
      rw [Dyadic.coe_real_neg] at h1
      have h2 : (N : ℝ) ≤ |(y : ℝ)| := by
        rw [abs_of_nonpos (by linarith : (y : ℝ) ≤ 0)]
        linarith
      linarith

/-- Chain no-overflow for RTO-RTO, via composition at the *intermediate*
format `G := F₁.withBound next(b₁)`: the chained rounding `w` is in-`G`
(its faithful candidates are squeezed into `[-N, N]`), so the
spec-relational composition at `(G, F₂.unbounded)` plus restrict/lift shows
`w` is *the* unbounded RTO rounding of `x` in `F₁` — which is in-bound by
hypothesis. -/
theorem toOdd_toOdd_noOverflow_chain {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hreg : ∀ b : NonNegDyadic, F₁.b = (b : Bound) →
      b.val ∈ F₁ ∧ (F₁.exp = ⊥ → 0 < ((b.val : Dyadic) : ℝ)))
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    (h₁u : ¬ F₁.IsUndefined .toOdd)
    {x : ℝ} {y z w : Dyadic}
    (hy : RoundsFinite F₁.unbounded .toOdd x y) (hby : Format.boundOK F₁.b y)
    (hz : RoundsFinite F₂.unbounded .toOdd x z)
    (hw : RoundsFinite F₁.unbounded .toOdd (z : ℝ) w) :
    Format.boundOK F₁.b w := by
  rcases hF₁b : F₁.b with _ | b₁
  · trivial
  obtain ⟨hb₁_mem, hguard⟩ := hreg b₁ hF₁b
  obtain ⟨hb₁_nn, hN_lt, hN_nn, hN_mem⟩ := next_facts hb₁_mem
  set N := F₁.toFormat.next b₁.val with hN_def
  -- `|x| < N` (no direct overflow), hence `|z| ≤ N`, hence `|w| ≤ N`.
  have hby' : Format.boundOK F₁.b y := hby
  rw [hF₁b] at hby'
  have hxN : |x| < (N : ℝ) :=
    abs_lt_next_of_toOdd_inbound hF₁b hb₁_mem hy hby
  have hN_F₂ : N ∈ F₂ :=
    hsub N ⟨hN_mem.1, hN_mem.2.1, boundOK_boundAfterNext_next hF₁b hN_nn⟩
  have hz_abs : |(z : ℝ)| ≤ (N : ℝ) :=
    abs_faithful_le_of_le (mem_unbounded_of_mem hN_F₂) hxN.le hz.2.1
  have hw_abs : |(w : ℝ)| ≤ (N : ℝ) :=
    abs_faithful_le_of_le hN_mem hz_abs hw.2.1
  -- `w` is in-`G` for the intermediate format `G := F₁.withBound next(b₁)`.
  set G : FiniteFormat := FiniteFormat.withBoundFF F₁ F₁.toFormat.boundAfterNext
    with hG_def
  have hG_bnd_w : Format.boundOK G.b w :=
    boundOK_of_abs_le (by rwa [abs_of_nonneg hN_nn])
      (boundOK_boundAfterNext_next hF₁b hN_nn)
  have hG_bnd_y : Format.boundOK G.b y :=
    boundOK_boundAfterNext_of_boundOK hby
  -- Restrict the chained rounding to `G`, compose at `(G, F₂.unbounded)`,
  -- and lift back: `w` is the unbounded RTO rounding of `x` in `F₁`.
  have hw_G : RoundsFinite G .toOdd (z : ℝ) w :=
    RoundsFinite.toOdd_restrict (F := G) hw hG_bnd_w
  have hsub_G : G.toFormat ⊆ F₂.unbounded.toFormat :=
      Format.subset_of_mem hsub.specials fun d hd =>
    mem_unbounded_of_mem (F := F₂) (hsub d hd)
  have hxw_G : RoundsFinite G .toOdd x w := roundsRTO_RTO_finite hsub_G hp_F₂ hz hw_G
  have hxw : RoundsFinite F₁.unbounded .toOdd x w :=
    RoundsFinite.toOdd_lift (F := G) hxw_G hy hG_bnd_y
  -- Uniqueness against the in-bound direct rounding.
  have h_eq : w = y := by
    rw [rndUnbounded_unique F₁ .toOdd x h₁u hxw,
      rndUnbounded_unique F₁ .toOdd x h₁u hy]
  rw [h_eq]
  exact hby'


/-! ## rnd-RTO-RN: no-overflow propagation -/

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
private theorem nearest_boundOK_of_abs_lt_mid {F₁ : FiniteFormat} {b₁ : NonNegDyadic}
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
private theorem abs_lt_mid_of_toOdd {F₁ F₂ : FiniteFormat}
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
    refine Format.subset_of_mem hsub.specials fun d hd => ?_
    exact mem_unbounded_of_mem (F := F₂) (hsub d
      (Format.extend_one_extend_one_subset_extend_two
        (F₁.toFormat.withBound ((F₁.extend 1).toFormat.boundAfterNext)) d hd))
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

/-- Chain no-overflow for RTO-RN. With `|z| ≤ M` (midpoint), an out-of-bound
chained rounding would have to sit at `±next(b₁)`, strictly farther from `z`
than the in-bound side `±b₁` — except at `|z| = M` exactly, which the RTO-padding lemma
(through the `extend 2` containment) rules out. -/
theorem toOdd_nearest_noOverflow_chain {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
      ⊆ F₂.toFormat)
    (hreg : ∀ b : NonNegDyadic, F₁.b = (b : Bound) →
      b.val ∈ F₁ ∧ (F₁.exp = ⊥ → 0 < ((b.val : Dyadic) : ℝ)))
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {tb : TieBreak} (h₁u : ¬ F₁.IsUndefined (.nearest tb))
    {x : ℝ} {y z w : Dyadic}
    (hy : RoundsFinite F₁.unbounded (.nearest tb) x y)
    (hby : Format.boundOK F₁.b y)
    (hz : RoundsFinite F₂.unbounded .toOdd x z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb) (z : ℝ) w) :
    Format.boundOK F₁.b w := by
  -- `x = z` short-circuits through uniqueness.
  rcases eq_or_ne x ((z : Dyadic) : ℝ) with hxz | hxz
  · have hw' : RoundsFinite F₁.unbounded (.nearest tb) x w := hxz ▸ hw
    rw [RoundsFinite.unique h₁u hw' hy]; exact hby
  rcases hF₁b : F₁.b with _ | b₁
  · trivial
  obtain ⟨hb₁_mem, hguard⟩ := hreg b₁ hF₁b
  obtain ⟨-, hyfaithful, hyclose⟩ := nearest_components hy
  -- `|x| ≤ M`, hence `|z| ≤ M`, and padding makes it strict.
  have hxM := abs_le_mid_of_nearest_inbound hF₁b hb₁_mem hguard hyfaithful hyclose hby
  have hM_F₂ := hsub _ (next_mem_extend_two_withBound hF₁b hb₁_mem)
  have hzM := abs_faithful_le_of_le (mem_unbounded_of_mem hM_F₂) hxM hz.2.1
  have h := nearest_boundOK_of_abs_lt_mid hF₁b hb₁_mem hguard hw
    (abs_lt_mid_of_toOdd hsub hF₁b hb₁_mem hguard hp_F₂ hz hxz hzM)
  rwa [hF₁b] at h

/-! ## Back to the direct rounding: an in-bound chain keeps it in bound -/

/-- Dual of `abs_faithful_le_of_le`: a nonnegative grid point at most `|x|`
bounds a faithful rounding of `x` from below in magnitude. -/
private theorem le_abs_faithful_of_le {F : FiniteFormat} {x : ℝ} {z N : Dyadic}
    (hN_mem : N ∈ F.unbounded) (hN_nn : 0 ≤ (N : ℝ)) (hxN : (N : ℝ) ≤ |x|)
    (hf : IsFaithfulRound F.unbounded x z) : (N : ℝ) ≤ |(z : ℝ)| := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx] at hxN
    rcases hf with ⟨-, -, hmax⟩ | ⟨-, hxz, -⟩
    · exact (hmax N hN_mem hxN).trans (le_abs_self _)
    · exact (hxN.trans hxz).trans (le_abs_self _)
  · rw [abs_of_neg hx] at hxN
    rcases hf with ⟨-, hzx, -⟩ | ⟨-, -, hmin⟩
    · rw [abs_of_nonpos (by linarith)]; linarith
    · have h := hmin (-N) (FiniteFormat.neg_mem hN_mem)
        (by rw [Dyadic.coe_real_neg]; linarith)
      rw [Dyadic.coe_real_neg] at h
      rw [abs_of_nonpos (by linarith)]; linarith

/-- An `F₁`-grid point strictly inside `±next(b₁)` is within `b₁`. -/
private theorem boundOK_of_abs_lt_next {F₁ : FiniteFormat} {b₁ : NonNegDyadic}
    (hF₁b : F₁.b = (b₁ : Bound)) (hb₁_mem : b₁.val ∈ F₁)
    (hguard : F₁.exp = ⊥ → 0 < ((b₁.val : Dyadic) : ℝ))
    {y : Dyadic} (hy : y ∈ F₁.unbounded)
    (h : |(y : ℝ)| < ((F₁.toFormat.next b₁.val : Dyadic) : ℝ)) :
    Format.boundOK F₁.b y := by
  rw [hF₁b]
  have hb₁_nn := nonneg_coe_real b₁
  have hb_mem := mem_unbounded_of_mem hb₁_mem
  refine boundOK_coe_of_abs_le (not_lt.mp fun hlt => ?_)
  rcases le_or_gt 0 (y : ℝ) with hy0 | hy0
  · rw [abs_of_nonneg hy0] at hlt h
    exact absurd (next_min' hb_mem hy hb₁_nn hguard hlt) (not_le.mpr h)
  · rw [abs_of_neg hy0] at hlt h
    have h' := next_min' hb_mem (FiniteFormat.neg_mem hy) hb₁_nn hguard
      (by rwa [Dyadic.coe_real_neg])
    rw [Dyadic.coe_real_neg] at h'
    linarith

/-- A faithful rounding has the sign of its input. -/
theorem IsFaithfulRound.mul_nonneg {F : FiniteFormat} {x : ℝ} {z : Dyadic}
    (hf : IsFaithfulRound F x z) : (z : ℝ) * x ≥ 0 := by
  rcases le_or_gt 0 x with hx | hx
  · rcases isFaithfulRound_iff_directed.mp hf with hd | hu
    · exact _root_.mul_nonneg (RoundsFinite.toNegative_nonneg hx hd) hx
    · exact _root_.mul_nonneg (hx.trans hu.2.1) hx
  · rcases isFaithfulRound_iff_directed.mp hf with hd | hu
    · exact mul_nonneg_of_nonpos_of_nonpos (hd.2.1.trans hx.le) hx.le
    · exact mul_nonneg_of_nonpos_of_nonpos (RoundsFinite.toPositive_nonpos hx.le hu) hx.le

/-- **RTZ outer mode.** An in-bound chained RTZ rounding of a faithful `z`
keeps the direct RTZ rounding in bound, given `next(b₁) ∈ F₂`: the chain pins
`|z| < next(b₁)`, hence `|x| < next(b₁)`. -/
theorem toZero_noOverflow_direct {F₁ F₂ : FiniteFormat}
    (hreg : ∀ b : NonNegDyadic, F₁.b = (b : Bound) →
      b.val ∈ F₁ ∧ (F₁.exp = ⊥ → 0 < ((b.val : Dyadic) : ℝ)))
    (hN_F₂ : ∀ b₁ : NonNegDyadic, F₁.b = (b₁ : Bound) → b₁.val ∈ F₁ →
      F₁.toFormat.next b₁.val ∈ F₂.unbounded)
    {x : ℝ} {y z w : Dyadic} (hz : IsFaithfulRound F₂.unbounded x z)
    (hw : RoundsFinite F₁.unbounded .toZero (z : ℝ) w) (hbw : Format.boundOK F₁.b w)
    (hy : RoundsFinite F₁.unbounded .toZero x y) : Format.boundOK F₁.b y := by
  rcases hF₁b : F₁.b with _ | b₁
  · trivial
  obtain ⟨hb₁_mem, hguard⟩ := hreg b₁ hF₁b
  obtain ⟨-, -, hN_nn, -⟩ := next_facts hb₁_mem
  have hzN := abs_lt_next_of_toZero_inbound hF₁b hb₁_mem hw hbw
  have hxN : |x| < ((F₁.toFormat.next b₁.val : Dyadic) : ℝ) := lt_of_not_ge fun h =>
    absurd (le_abs_faithful_of_le (hN_F₂ b₁ hF₁b hb₁_mem) hN_nn h hz) (not_le.mpr hzN)
  have h := boundOK_of_abs_lt_next hF₁b hb₁_mem hguard hy.1 (lt_of_le_of_lt hy.2.1 hxN)
  rwa [hF₁b] at h

/-- `next(b₁) ∈ F₂` from the RTZ / RTO-RTO containment. -/
theorem next_mem_of_withBound_subset {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {b₁ : NonNegDyadic} (hF₁b : F₁.b = (b₁ : Bound)) (hb₁_mem : b₁.val ∈ F₁) :
    F₁.toFormat.next b₁.val ∈ F₂.unbounded := by
  obtain ⟨-, -, hN_nn, hN_mem⟩ := next_facts hb₁_mem
  exact mem_unbounded_of_mem
    (hsub.mem _ ⟨hN_mem.1, hN_mem.2.1, boundOK_boundAfterNext_next hF₁b hN_nn⟩)

/-- `next(b₁) ∈ F₂` from the RTO-RTZ / RTO-RAZ containment. -/
theorem next_mem_of_extend_withBound_subset {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {b₁ : NonNegDyadic} (hF₁b : F₁.b = (b₁ : Bound)) (hb₁_mem : b₁.val ∈ F₁) :
    F₁.toFormat.next b₁.val ∈ F₂.unbounded := by
  obtain ⟨-, -, hN_nn, hN_mem⟩ := next_facts hb₁_mem
  have h := Format.self_subset_extend F₁.toFormat.unbounded 1 _ hN_mem
  exact mem_unbounded_of_mem
    (hsub.mem _ ⟨h.1, h.2.1, boundOK_boundAfterNext_next hF₁b hN_nn⟩)

/-- **RAZ outer mode.** A chained RAZ rounding `w` that is a candidate for `x`
(`|x| ≤ |w|`, same sign) bounds the direct RAZ rounding. -/
theorem awayZero_noOverflow_direct {F₁ : FiniteFormat} {x : ℝ} {y w : Dyadic}
    (hw_mem : w ∈ F₁.unbounded) (hxw : |x| ≤ |(w : ℝ)|) (hwx : (w : ℝ) * x ≥ 0)
    (hbw : Format.boundOK F₁.b w) (hy : RoundsFinite F₁.unbounded .awayZero x y) :
    Format.boundOK F₁.b y :=
  boundOK_of_abs_le (hy.2.2.2 w hw_mem hxw hwx) hbw

/-- **RTO-RAZ.** If the inexact RTO rounding `z` falls short of `|x|`, the
in-bound `w` overshoots `z` (padding keeps `z` off `F₁`'s grid) and, being in
`F₂`, cannot sit strictly between `z` and `x`; so `w` is a candidate for `x`. -/
theorem toOdd_awayZero_candidate {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p) {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded .toOdd x z)
    (hw : RoundsFinite F₁.unbounded .awayZero (z : ℝ) w) (hbw : Format.boundOK F₁.b w) :
    |x| ≤ |(w : ℝ)| ∧ (w : ℝ) * x ≥ 0 := by
  obtain ⟨hwmem, hzw, hwz, hwmin⟩ := hw
  have hzx := hz.2.1.mul_nonneg
  have hw0 : (z : ℝ) = 0 → (w : ℝ) = 0 := fun h0 => by
    have h := hwmin 0 (FiniteFormat.zero_mem _) (by rw [h0]; simp) (by simp)
    rw [Dyadic.coe_real_zero, abs_zero] at h
    exact abs_nonpos_iff.mp h
  have hwx : (w : ℝ) * x ≥ 0 :=
    mul_nonneg_of_common_sign hwz (by linarith [hzx] : x * (z : ℝ) ≥ 0) hw0
  refine ⟨?_, hwx⟩
  by_contra hlt; push Not at hlt
  have hzx_lt : |(z : ℝ)| < |x| := lt_of_le_of_lt hzw hlt
  have hxz : x ≠ (z : ℝ) := fun h => by rw [h] at hzx_lt; exact lt_irrefl _ hzx_lt
  -- `z ∉ F₁`, so `z` is off `F₁`'s grid and `|z| < |w|`.
  have hsub₁ : (F₁.extend 1).toFormat ⊆ F₂.unbounded.toFormat :=
    Format.subset_of_mem hsub.specials fun d hd =>
      mem_unbounded_of_mem (extend_one_subset_of_withBound_subset hsub d hd)
  have hz_notF₁ := toOdd_notMem_of_extend_subset hsub₁ hp_F₂ hz hxz
  have hzw_lt : |(z : ℝ)| < |(w : ℝ)| := by
    refine lt_of_le_of_ne hzw fun heq => hz_notF₁ ?_
    have hwz' : (w : ℝ) = (z : ℝ) := by
      rcases abs_eq_abs.mp heq.symm with h | h
      · exact h
      · rcases eq_or_ne (z : ℝ) 0 with h0 | h0
        · rw [h, h0, neg_zero]
        · nlinarith [mul_self_pos.mpr h0]
    rw [show z = w from (Dyadic.coe_real_inj z w).mp hwz'.symm]
    exact mem_of_mem_unbounded_of_boundOK hwmem hbw
  -- `w ∈ F₂` and `z` is the faithful neighbor of `x` on the near side.
  have hwF₂ : w ∈ F₂.unbounded := by
    have h := Format.self_subset_extend F₁.toFormat.unbounded 1 w hwmem
    exact mem_unbounded_of_mem
      (hsub.mem _ ⟨h.1, h.2.1, boundOK_boundAfterNext_of_boundOK hbw⟩)
  rcases hz.2.1 with ⟨-, hz_le, hzmax⟩ | ⟨-, hz_ge, hzmin⟩
  · -- `z ≤ x`: then `x > 0`, and `w ≤ x` would contradict maximality of `z`.
    have hx : 0 < x := by
      by_contra hx; push Not at hx
      rw [abs_of_nonpos hx, abs_of_nonpos (hz_le.trans hx)] at hzx_lt; linarith
    have hw_pos : 0 < (w : ℝ) := by
      rcases le_or_gt (w : ℝ) 0 with h | h
      · have : (w : ℝ) = 0 := le_antisymm h (by nlinarith)
        rw [this, abs_zero] at hzw_lt; linarith [abs_nonneg (z : ℝ)]
      · exact h
    have hz_nn : 0 ≤ (z : ℝ) := by
      have h := hzmax 0 (FiniteFormat.zero_mem _) (by rw [Dyadic.coe_real_zero]; exact hx.le)
      rwa [Dyadic.coe_real_zero] at h
    rw [abs_of_pos hx, abs_of_pos hw_pos] at hlt
    rw [abs_of_nonneg hz_nn, abs_of_pos hw_pos] at hzw_lt
    linarith [hzmax w hwF₂ hlt.le]
  · -- Mirror: `x ≤ z`, so `x < 0`.
    have hx : x < 0 := by
      by_contra hx; push Not at hx
      rw [abs_of_nonneg hx, abs_of_nonneg (hx.trans hz_ge)] at hzx_lt; linarith
    have hw_neg : (w : ℝ) < 0 := by
      rcases le_or_gt 0 (w : ℝ) with h | h
      · have : (w : ℝ) = 0 := le_antisymm (by nlinarith) h
        rw [this, abs_zero] at hzw_lt; linarith [abs_nonneg (z : ℝ)]
      · exact h
    have hz_np : (z : ℝ) ≤ 0 := by
      have h := hzmin 0 (FiniteFormat.zero_mem _) (by rw [Dyadic.coe_real_zero]; exact hx.le)
      rwa [Dyadic.coe_real_zero] at h
    rw [abs_of_neg hx, abs_of_neg hw_neg] at hlt
    rw [abs_of_nonpos hz_np, abs_of_neg hw_neg] at hzw_lt
    linarith [hzmin w hwF₂ (by linarith)]

/-- **RTO-RTO.** An in-bound chain pins `|x| < next(b₁)`; inside that range
`F₁.unbounded` agrees with `G = F₁.withBound next(b₁) ⊆ F₂`, where the
spec-relational rule composes and uniqueness identifies `w` with the direct
rounding. -/
theorem toOdd_toOdd_noOverflow_direct {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hreg : ∀ b : NonNegDyadic, F₁.b = (b : Bound) →
      b.val ∈ F₁ ∧ (F₁.exp = ⊥ → 0 < ((b.val : Dyadic) : ℝ)))
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p) (h₁u : ¬ F₁.IsUndefined .toOdd)
    {x : ℝ} {y z w : Dyadic} (hz : RoundsFinite F₂.unbounded .toOdd x z)
    (hw : RoundsFinite F₁.unbounded .toOdd (z : ℝ) w) (hbw : Format.boundOK F₁.b w)
    (hy : RoundsFinite F₁.unbounded .toOdd x y) : Format.boundOK F₁.b y := by
  rcases hF₁b : F₁.b with _ | b₁
  · trivial
  obtain ⟨hb₁_mem, -⟩ := hreg b₁ hF₁b
  obtain ⟨-, hN_lt, hN_nn, hN_mem⟩ := next_facts hb₁_mem
  set N := F₁.toFormat.next b₁.val with hN_def
  have hN_F₂ := next_mem_of_withBound_subset hsub hF₁b hb₁_mem
  have hw_le : |(w : ℝ)| ≤ ((b₁.val : Dyadic) : ℝ) :=
    abs_coe_real_le_of_boundOK (by rw [hF₁b] at hbw; exact hbw)
  have hxN : |x| < (N : ℝ) := lt_of_not_ge fun h => by
    have := le_abs_faithful_of_le hN_mem hN_nn
      (le_abs_faithful_of_le hN_F₂ hN_nn h hz.2.1) hw.2.1
    linarith
  -- Compose in `G`.
  set G := FiniteFormat.withBoundFF F₁ F₁.toFormat.boundAfterNext
  have hbG : ∀ v : Dyadic, |(v : ℝ)| ≤ (N : ℝ) → Format.boundOK G.b v := fun v hv =>
    boundOK_of_abs_le (by rwa [abs_of_nonneg hN_nn]) (boundOK_boundAfterNext_next hF₁b hN_nn)
  have hsubG : G.toFormat ⊆ F₂.unbounded.toFormat :=
    Format.subset_of_mem hsub.specials fun d hd => mem_unbounded_of_mem (hsub d hd)
  have hyN := abs_faithful_le_of_le hN_mem hxN.le hy.2.1
  have hwN := abs_faithful_le_of_le hN_mem
    (abs_faithful_le_of_le hN_F₂ hxN.le hz.2.1) hw.2.1
  have hxw : RoundsFinite G .toOdd x w :=
    roundsRTO_RTO_finite hsubG hp_F₂ hz (RoundsFinite.toOdd_restrict hw (hbG w hwN))
  rw [RoundsFinite.unique (F := G) h₁u hy (RoundsFinite.toOdd_lift hxw hy (hbG y hyN))]
  rwa [hF₁b] at hbw

/-- **RTO-RN.** An in-bound chain pins `|z| ≤ M` (midpoint of `(b₁, next b₁)`),
strictly when inexact (padding), hence `|x| < M`, where the direct nearest
rounding is in bound. -/
theorem toOdd_nearest_noOverflow_direct {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
      ⊆ F₂.toFormat)
    (hreg : ∀ b : NonNegDyadic, F₁.b = (b : Bound) →
      b.val ∈ F₁ ∧ (F₁.exp = ⊥ → 0 < ((b.val : Dyadic) : ℝ)))
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {tb : TieBreak} (h₁u : ¬ F₁.IsUndefined (.nearest tb))
    {x : ℝ} {y z w : Dyadic} (hz : RoundsFinite F₂.unbounded .toOdd x z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb) (z : ℝ) w) (hbw : Format.boundOK F₁.b w)
    (hy : RoundsFinite F₁.unbounded (.nearest tb) x y) : Format.boundOK F₁.b y := by
  rcases eq_or_ne x ((z : Dyadic) : ℝ) with hxz | hxz
  · rw [RoundsFinite.unique h₁u hy (hxz ▸ hw)]; exact hbw
  rcases hF₁b : F₁.b with _ | b₁
  · trivial
  obtain ⟨hb₁_mem, hguard⟩ := hreg b₁ hF₁b
  obtain ⟨hb₁_nn, hN_lt, -, -⟩ := next_facts hb₁_mem
  obtain ⟨-, hwfaithful, hwclose⟩ := nearest_components hw
  have hM_nn : 0 ≤ (((F₁.extend 1).toFormat.next b₁.val : Dyadic) : ℝ) := by
    rw [next_extend_midpoint' hb₁_nn hguard]; linarith
  have hM_F₂ := hsub _ (next_mem_extend_two_withBound hF₁b hb₁_mem)
  have hzM := abs_lt_mid_of_toOdd hsub hF₁b hb₁_mem hguard hp_F₂ hz hxz
    (abs_le_mid_of_nearest_inbound hF₁b hb₁_mem hguard hwfaithful hwclose hbw)
  have hxM := lt_of_not_ge fun h =>
    absurd (le_abs_faithful_of_le (mem_unbounded_of_mem hM_F₂) hM_nn h hz.2.1)
      (not_le.mpr hzM)
  have h := nearest_boundOK_of_abs_lt_mid hF₁b hb₁_mem hguard hy hxM
  rwa [hF₁b] at h

end Mpfx
