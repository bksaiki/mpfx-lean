import Mpfx.DoubleRounding.Nearest
import Mpfx.Rounding.Restrict

/-!
# Total double rounding (overflow-aware, self-contained)

The `Rounds` layer: no chain hypotheses at all. For each double-rounding rule, conclude
that either (i) rounding `x` directly in `F₁` overflows, or (ii) rounding
`x` in `F₂` does **not** overflow (finite `z`), the chained rounding is
finite (`w`), and double rounding holds. The paper's side condition ("the
rules hold whenever `rnd_{F₁}(x)` does not overflow") is the guard between
the two disjuncts; the paper's bound conditions (`next(b₁)` vs `b₁`) become
*proof obligations* for no-overflow propagation. An arbitrary (off-grid)
bound is reduced to its grid floor, so no regularity hypothesis surfaces
in the public statements. -/

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
private theorem abs_lt_next_of_toZero_inbound {F₁ : FiniteFormat}
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
private theorem toZero_noOverflow_F₂ {F₁ F₂ : FiniteFormat}
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
      apply hsub
      exact ⟨hN_mem.1, hN_mem.2.1, boundOK_boundAfterNext_next hF₁b hN_nn⟩
    have hzN : |(z : ℝ)| ≤ |(N : ℝ)| := by
      rw [abs_of_nonneg hN_nn]
      exact le_trans hz.2.1 hxN.le
    exact boundOK_of_abs_le hzN hN_F₂.2.2

/-- Chain no-overflow for RTZ-RTZ: the unbounded RTZ rounding `w` of `z` in
`F₁` is in-bound, given that the direct rounding `y` is (`w` competes
against `y` at `x`). -/
private theorem toZero_noOverflow_chain {F₁ F₂ : FiniteFormat} {x : ℝ}
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
private theorem awayZero_noOverflow_F₂ {F₁ F₂ : FiniteFormat}
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
private theorem awayZero_noOverflow_chain {F₁ F₂ : FiniteFormat}
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
private theorem toOdd_abs_le_of_awayZero {F₁ F₂ : FiniteFormat}
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
private theorem abs_faithful_le_of_le {F₂ : FiniteFormat} {x : ℝ} {z N : Dyadic}
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
private theorem toOdd_toZero_noOverflow_chain {F₁ F₂ : FiniteFormat}
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
      (hsub N (mem_extend_one_withBound_of_mem_unbounded hN_mem (boundOK_boundAfterNext_next hF₁b hN_nn)))
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
  have hsub' : ((F₁wB.extend 1)).toFormat ⊆ F₂.unbounded.toFormat := fun d hd =>
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
private theorem abs_lt_next_of_toOdd_inbound {F₁ : FiniteFormat}
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
private theorem toOdd_toOdd_noOverflow_chain {F₁ F₂ : FiniteFormat}
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
  have hsub_G : G.toFormat ⊆ F₂.unbounded.toFormat := fun d hd =>
    mem_unbounded_of_mem (F := F₂) (hsub d hd)
  have hxw_G : RoundsFinite G .toOdd x w := rndRTO_RTO hsub_G hp_F₂ hz hw_G
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
private theorem nearest_components {F : FiniteFormat} {tb : TieBreak} {x : ℝ}
    {y : Dyadic} (h : RoundsFinite F (.nearest tb) x y) :
    y ∈ F ∧ IsFaithfulRound F x y ∧
      ∀ c : Dyadic, c ∈ F → IsFaithfulRound F x c →
        |x - (y : ℝ)| ≤ |x - (c : ℝ)| :=
  ⟨h.1, h.isFaithfulRound, fun _ hc hcf => h.nearest_min hc hcf⟩


/-- The midpoint `M = nextᵉ(b₁)` lies in the paper RN containment format
`(F₁.extend 2).withBound (F₁.extend 1).boundAfterNext`. -/
private theorem next_mem_extend_two_withBound {F₁ : FiniteFormat} {b₁ : NonNegDyadic}
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
    le_trans hb₁_nn (lt_next'' b₁.val hb₁_nn).le
  have hmono := Format.extend_mono F₁.toFormat.unbounded
    (by exact_mod_cast (by omega : (1 : ℕ) ≤ 2) : (1 : ℕ) ≤ 2)
  have h2 := hmono _ hM_mem
  exact ⟨h2.1, h2.2.1,
    boundOK_boundAfterNext_next (F₁ := F₁.extend 1) hF₁b hM_nn⟩

/-- An in-bound RN rounding pins `|x|` to at most the midpoint
`M = nextᵉ(b₁)` of `b₁` and `next(b₁)`: beyond the midpoint, the
away-side candidate `±next(b₁)` is strictly closer than anything in-bound. -/
private theorem abs_le_mid_of_nearest_inbound {F₁ : FiniteFormat}
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

/-- Chain no-overflow for RTO-RN. With `|z| ≤ M` (midpoint), an out-of-bound
chained rounding would have to sit at `±next(b₁)`, strictly farther from `z`
than the in-bound side `±b₁` — except at `|z| = M` exactly, which the RTO-padding lemma
(through the `extend 2` containment) rules out. -/
private theorem toOdd_nearest_noOverflow_chain {F₁ F₂ : FiniteFormat}
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
    have h_eq : w = y := by
      rw [rndUnbounded_unique F₁ (.nearest tb) x h₁u hw',
        rndUnbounded_unique F₁ (.nearest tb) x h₁u hy]
    rw [h_eq]; exact hby
  rcases hF₁b : F₁.b with _ | b₁
  · trivial
  obtain ⟨hb₁_mem, hguard⟩ := hreg b₁ hF₁b
  obtain ⟨hymem, hyfaithful, hyclose⟩ := nearest_components hy
  obtain ⟨hwmem, hwfaithful, hwclose⟩ := nearest_components hw
  obtain ⟨hb₁_nn, hN_lt, -, -⟩ := next_facts hb₁_mem
  set N := F₁.toFormat.next b₁.val with hN_def
  set M := (F₁.extend 1).toFormat.next b₁.val with hM_def
  have hb₁_mem_u : b₁.val ∈ F₁.unbounded := mem_unbounded_of_mem hb₁_mem
  have hM_mid : (M : ℝ) = (((b₁.val : Dyadic) : ℝ) + (N : ℝ)) / 2 :=
    next_extend_midpoint' hb₁_nn hguard
  have hM_nn : 0 ≤ (M : ℝ) := by rw [hM_mid]; linarith
  have hby' : Format.boundOK ((b₁ : Bound)) y := by
    rw [hF₁b] at hby; exact hby
  -- `|x| ≤ M`, hence `|z| ≤ M`.
  have hxM : |x| ≤ (M : ℝ) :=
    abs_le_mid_of_nearest_inbound hF₁b hb₁_mem hguard hyfaithful hyclose hby
  have hM_F₂ : M ∈ F₂ := hsub M (next_mem_extend_two_withBound hF₁b hb₁_mem)
  have hzM : |(z : ℝ)| ≤ (M : ℝ) :=
    abs_faithful_le_of_le (mem_unbounded_of_mem hM_F₂) hxM hz.2.1
  -- If `|z| ≤ b₁`, the chained rounding is squeezed in-bound directly.
  by_cases hzb : |(z : ℝ)| ≤ ((b₁.val : Dyadic) : ℝ)
  · have hw_abs : |(w : ℝ)| ≤ ((b₁.val : Dyadic) : ℝ) :=
      abs_faithful_le_of_le hb₁_mem_u hzb hwfaithful
    have hb₁_ok : Format.boundOK ((b₁ : Bound)) b₁.val := by
      change |(b₁.val : ℚ)| ≤ ((b₁.val : Dyadic) : ℚ)
      rw [abs_of_nonneg (by exact_mod_cast b₁.2 : (0 : ℚ) ≤ (b₁.val : ℚ))]
    exact boundOK_of_abs_le (by rwa [abs_of_nonneg hb₁_nn]) hb₁_ok
  push Not at hzb
  -- `b₁ < |z| ≤ M`; RTO padding through the `extend 2` containment excludes
  -- `|z| = M`, so `b₁ < |z| < M`.
  have h_notmem : z ∉ FiniteFormat.withBoundFF (F₁.extend 1)
      ((F₁.extend 1).toFormat.boundAfterNext) := by
    apply toOdd_notMem_of_extend_subset (F₂ := F₂.unbounded) ?_ hp_F₂ hz hxz
    intro d hd
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
  -- Sign split: the chained rounding must stay on the `±b₁` side.
  by_contra hbw
  have hbw' : ((b₁.val : Dyadic) : ℝ) < |(w : ℝ)| :=
    lt_abs_coe_real_of_not_boundOK hbw
  by_cases hz_sign : 0 ≤ (z : ℝ)
  · -- `b₁ < z < M`.
    have hz_gt : ((b₁.val : Dyadic) : ℝ) < (z : ℝ) := by
      rwa [abs_of_nonneg hz_sign] at hzb
    have hz_lt : (z : ℝ) < (M : ℝ) := by rwa [abs_of_nonneg hz_sign] at hzM_lt
    -- `b₁` is RD-faithful at `z`.
    have hb₁_faithful : IsFaithfulRound F₁.unbounded ((z : Dyadic) : ℝ) b₁.val := by
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
    have h2 : |((z : Dyadic) : ℝ) - ((b₁.val : Dyadic) : ℝ)|
        = (z : ℝ) - ((b₁.val : Dyadic) : ℝ) := abs_of_nonneg (by linarith)
    have h3 : |((z : Dyadic) : ℝ) - ((w : Dyadic) : ℝ)| = (w : ℝ) - (z : ℝ) := by
      rw [abs_sub_comm]
      exact abs_of_nonneg (by linarith)
    rw [h2, h3] at h1
    linarith
  · -- Mirror: `-M < z < -b₁`.
    push Not at hz_sign
    have hz_lt : (z : ℝ) < -((b₁.val : Dyadic) : ℝ) := by
      rw [abs_of_neg hz_sign] at hzb
      linarith
    have hz_gt : -(M : ℝ) < (z : ℝ) := by
      rw [abs_of_neg hz_sign] at hzM_lt
      linarith
    -- `-b₁` is RU-faithful at `z`.
    have hnb₁_faithful : IsFaithfulRound F₁.unbounded ((z : Dyadic) : ℝ)
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
    have h2 : |((z : Dyadic) : ℝ) - ((-(b₁.val) : Dyadic) : ℝ)|
        = -((b₁.val : Dyadic) : ℝ) - (z : ℝ) := by
      rw [Dyadic.coe_real_neg, abs_of_nonpos (by linarith)]
      ring
    have h3 : |((z : Dyadic) : ℝ) - ((w : Dyadic) : ℝ)| = (z : ℝ) - (w : ℝ) :=
      abs_of_nonneg (by linarith)
    rw [h2, h3] at h1
    linarith


/-! ## Reduction to a grid-floor bound

`Rounds F rm x r` only inspects the bound through `boundOK` at *grid*
values, so replacing the bound `b₁` by its grid floor `d` (the largest grid
point `≤ b₁`, i.e. the RTN rounding of `b₁`) yields the same relation. The
floor is on the grid by construction, so each total theorem's regular-bound
core (`suffices key` in its proof) applies to the floor-adjusted format.
The degenerate corner `exp = ⊥ ∧ d = 0` (where the grid has positive points
of arbitrarily small magnitude, hence no successor of the bound) forces
`b₁ = 0`, where an in-bound direct rounding pins `x = 0` and double
rounding is trivial. -/


/-- Replacing the bound by its grid floor `D` preserves the full rounding
relation: `Rounds` only tests the bound at grid values, and on the grid
`|·| ≤ b₁ ↔ |·| ≤ D`. -/
private theorem rounds_withBoundFF_floor_iff {F₁ : FiniteFormat} {D : NonNegDyadic}
    (hD_le : Format.boundOK F₁.b D.val)
    (hD_max : ∀ v : Dyadic, v ∈ F₁.unbounded → Format.boundOK F₁.b v →
      Format.boundOK ((D : Bound)) v)
    (rm : RoundingMode) (x : ℝ) (r : RoundResult) :
    Rounds F₁ rm x r ↔
      Rounds (FiniteFormat.withBoundFF F₁ (D : Bound)) rm x r := by
  have h_to : ∀ v : Dyadic, Format.boundOK ((D : Bound)) v →
      Format.boundOK F₁.b v := by
    intro v hv
    have hD_abs : |(v : ℝ)| ≤ |((D.val : Dyadic) : ℝ)| := by
      rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast, ← Rat.cast_abs,
        ← Rat.cast_abs]
      exact_mod_cast (by rwa [abs_of_nonneg D.2] :
        |(v : ℚ)| ≤ |((D.val : Dyadic) : ℚ)|)
    exact boundOK_of_abs_le hD_abs hD_le
  cases r with
  | undefined => exact Iff.rfl
  | overflow bb =>
    constructor
    · rintro ⟨hu, y, hrf, hnb, hsgn⟩
      exact ⟨hu, y, hrf, fun h => hnb (h_to y h), hsgn⟩
    · rintro ⟨hu, y, hrf, hnb, hsgn⟩
      exact ⟨hu, y, hrf, fun h => hnb (hD_max y hrf.1 h), hsgn⟩
  | finite y =>
    constructor
    · rintro ⟨hu, hrf, hb⟩
      exact ⟨hu, hrf, hD_max y hrf.1 hb⟩
    · rintro ⟨hu, hrf, hb⟩
      exact ⟨hu, hrf, h_to y hb⟩

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
    (∃ b, Rounds F₁ rm₁ x (.overflow b)) ∨
    (∃ z w : Dyadic, Rounds F₂ rm₂ x (.finite z) ∧
      Rounds F₁ rm₁ (z : ℝ) (.finite w) ∧
      Rounds F₁ rm₁ x (.finite w)) := by
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
    exact ⟨z, w, ⟨h₂u, hz, hz_bnd⟩, ⟨h₁u, hw, hw_bnd⟩, ⟨h₁u, hw_x, hw_bnd⟩⟩
  · left
    exact rounds_overflow_of_not_boundOK h₁u hy hbOK

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
`rounds_withBoundFF_floor_iff` to each disjunct. -/
private theorem rounds_floor_lift {F₁ F₂ : FiniteFormat} {D : NonNegDyadic}
    (hD_le : Format.boundOK F₁.b D.val)
    (hD_max : ∀ v : Dyadic, v ∈ F₁.unbounded → Format.boundOK F₁.b v →
      Format.boundOK ((D : Bound)) v)
    {rm₁ rm₂ : RoundingMode} {x : ℝ}
    (h : (∃ b, Rounds (FiniteFormat.withBoundFF F₁ (D : Bound))
            rm₁ x (.overflow b)) ∨
      (∃ z w : Dyadic, Rounds F₂ rm₂ x (.finite z) ∧
        Rounds (FiniteFormat.withBoundFF F₁ (D : Bound))
          rm₁ (z : ℝ) (.finite w) ∧
        Rounds (FiniteFormat.withBoundFF F₁ (D : Bound))
          rm₁ x (.finite w))) :
    (∃ b, Rounds F₁ rm₁ x (.overflow b)) ∨
    (∃ z w : Dyadic, Rounds F₂ rm₂ x (.finite z) ∧
      Rounds F₁ rm₁ (z : ℝ) (.finite w) ∧
      Rounds F₁ rm₁ x (.finite w)) := by
  rcases h with ⟨bb, hov⟩ | ⟨z, w, h1, h2, h3⟩
  · exact Or.inl ⟨bb, (rounds_withBoundFF_floor_iff hD_le hD_max _ _ _).mpr hov⟩
  · exact Or.inr ⟨z, w, h1,
      (rounds_withBoundFF_floor_iff hD_le hD_max _ _ _).mpr h2,
      (rounds_withBoundFF_floor_iff hD_le hD_max _ _ _).mpr h3⟩

/-! ## The total theorems

Each proof first states a regular-bound core (`suffices key`: the bound is
on the grid, and positive when `exp = ⊥`), reduces to it at the
floor-adjusted format via `bound_floor_setup` +
`rounds_withBoundFF_floor_iff` (degenerate corner via
`rounds_total_of_zero_bound`), then proves the core. -/

/-- **rnd-RTZ-RTZ**, total form. Either rounding `x` directly in `F₁`
overflows, or rounding `x` in `F₂` does not overflow (finite `z`), the
chained rounding is finite (`w`), and double rounding holds. Uses the
paper's strengthened containment `F₁.withBound next(b₁) ⊆ F₂`. -/
theorem roundsRTZ_RTZ {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (x : ℝ) :
    (∃ b, Rounds F₁ .toZero x (.overflow b)) ∨
    (∃ z w : Dyadic, Rounds F₂ .toZero x (.finite z) ∧
      Rounds F₁ .toZero (z : ℝ) (.finite w) ∧
      Rounds F₁ .toZero x (.finite w)) := by
  -- Reduce to a bound that is on the grid (and positive when `exp = ⊥`)
  -- by replacing it with its grid floor.
  suffices key : ∀ F : FiniteFormat,
      (F.toFormat.withBound F.toFormat.boundAfterNext) ⊆ F₂.toFormat →
      (∀ b : NonNegDyadic, F.b = (b : Bound) →
        b.val ∈ F ∧ (F.exp = ⊥ → 0 < ((b.val : Dyadic) : ℝ))) →
      (∃ b, Rounds F .toZero x (.overflow b)) ∨
      (∃ z w : Dyadic, Rounds F₂ .toZero x (.finite z) ∧
        Rounds F .toZero (z : ℝ) (.finite w) ∧
        Rounds F .toZero x (.finite w)) by
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
          (fun v hv => hsub v ⟨hv.1, hv.2.1,
            boundOK_boundAfterNext_mono
              (G := FiniteFormat.withBoundFF F₁ (D : Bound))
              hF₁b rfl rfl hmono hv.2.2⟩) hreg_G)
  intro F hsub hreg
  have h₁u := not_isUndefined_toZero F
  have h₂u := not_isUndefined_toZero F₂
  -- Plain containment, recovered from the paper form.
  have hsub' : F.toFormat ⊆ F₂.toFormat := fun d hd =>
    hsub d ⟨hd.1, hd.2.1, boundOK_boundAfterNext_of_boundOK hd.2.2⟩
  have hy := rndUnbounded_satisfies F .toZero x h₁u
  set y := rndUnbounded F .toZero x h₁u with hy_def
  by_cases hbOK : Format.boundOK F.b y
  · right
    -- F₂ does not overflow.
    have hz := rndUnbounded_satisfies F₂ .toZero x h₂u
    set z := rndUnbounded F₂ .toZero x h₂u with hz_def
    have hz_bnd : Format.boundOK F₂.b z := toZero_noOverflow_F₂ hsub hreg hy hbOK hz
    have hzR : Rounds F₂ .toZero x (.finite z) := ⟨h₂u, hz, hz_bnd⟩
    -- The chain does not overflow.
    have hw := rndUnbounded_satisfies F .toZero (z : ℝ) h₁u
    set w := rndUnbounded F .toZero (z : ℝ) h₁u with hw_def
    have hw_bnd : Format.boundOK F.b w := toZero_noOverflow_chain hy hbOK hz hw
    have hwR : Rounds F .toZero (z : ℝ) (.finite w) := ⟨h₁u, hw, hw_bnd⟩
    -- Double rounding holds: restrict the chain, compose spec-relationally,
    -- and lift back along the in-bound direct rounding.
    have hsub_u : F.toFormat ⊆ F₂.unbounded.toFormat := fun d hd =>
      mem_unbounded_of_mem (F := F₂) (hsub' d hd)
    have hw_bdd : RoundsFinite F .toZero (z : ℝ) w :=
      RoundsFinite.toZero_restrict hw hw_bnd
    have hxw : RoundsFinite F .toZero x w := rndRTZ_RTZ hsub_u hz hw_bdd
    exact ⟨z, w, hzR, hwR, ⟨h₁u, RoundsFinite.toZero_lift hxw hy hbOK, hw_bnd⟩⟩
  · left
    exact rounds_overflow_of_not_boundOK h₁u hy hbOK

/-- **rnd-RAZ-RAZ**, total form. Either rounding `x` directly in `F₁`
overflows, or rounding `x` in `F₂` does not overflow (finite `z`), the
chained rounding is finite (`w`), and double rounding holds. -/
theorem roundsRAZ_RAZ {F₁ F₂ : FiniteFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat) (x : ℝ) :
    (∃ b, Rounds F₁ .awayZero x (.overflow b)) ∨
    (∃ z w : Dyadic, Rounds F₂ .awayZero x (.finite z) ∧
      Rounds F₁ .awayZero (z : ℝ) (.finite w) ∧
      Rounds F₁ .awayZero x (.finite w)) := by
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
    have hzR : Rounds F₂ .awayZero x (.finite z) := ⟨h₂u, hz, hz_bnd⟩
    -- The chain does not overflow.
    have hw := rndUnbounded_satisfies F₁ .awayZero (z : ℝ) h₁u
    set w := rndUnbounded F₁ .awayZero (z : ℝ) h₁u with hw_def
    have hw_bnd : Format.boundOK F₁.b w :=
      awayZero_noOverflow_chain hsub hy hbOK hz hw
    have hwR : Rounds F₁ .awayZero (z : ℝ) (.finite w) := ⟨h₁u, hw, hw_bnd⟩
    -- Double rounding holds: restrict the chain, compose spec-relationally,
    -- and lift back along the in-bound direct rounding.
    have hsub_u : F₁.toFormat ⊆ F₂.unbounded.toFormat := fun d hd =>
      mem_unbounded_of_mem (F := F₂) (hsub d hd)
    have hw_bdd : RoundsFinite F₁ .awayZero (z : ℝ) w :=
      RoundsFinite.awayZero_restrict hw hw_bnd
    have hxw : RoundsFinite F₁ .awayZero x w := rndRAZ_RAZ hsub_u hz hw_bdd
    exact ⟨z, w, hzR, hwR, ⟨h₁u, RoundsFinite.awayZero_lift hxw hy hbOK, hw_bnd⟩⟩
  · left
    exact rounds_overflow_of_not_boundOK h₁u hy hbOK

/-- **rnd-RTO-RTO**, total form (unified — no parity split on `b₁`). Either
rounding `x` directly in `F₁` (RTO) overflows, or the RTO rounding of `x` in
`F₂` does not overflow (finite `z`), the chained RTO rounding is finite
(`w`), and double rounding holds. -/
theorem roundsRTO_RTO {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    (h₁u : ¬ F₁.IsUndefined .toOdd) (x : ℝ) :
    (∃ b, Rounds F₁ .toOdd x (.overflow b)) ∨
    (∃ z w : Dyadic, Rounds F₂ .toOdd x (.finite z) ∧
      Rounds F₁ .toOdd (z : ℝ) (.finite w) ∧
      Rounds F₁ .toOdd x (.finite w)) := by
  -- Reduce to a bound that is on the grid (and positive when `exp = ⊥`)
  -- by replacing it with its grid floor.
  suffices key : ∀ F : FiniteFormat,
      (F.toFormat.withBound F.toFormat.boundAfterNext) ⊆ F₂.toFormat →
      (∀ b : NonNegDyadic, F.b = (b : Bound) →
        b.val ∈ F ∧ (F.exp = ⊥ → 0 < ((b.val : Dyadic) : ℝ))) →
      ¬ F.IsUndefined .toOdd →
      (∃ b, Rounds F .toOdd x (.overflow b)) ∨
      (∃ z w : Dyadic, Rounds F₂ .toOdd x (.finite z) ∧
        Rounds F .toOdd (z : ℝ) (.finite w) ∧
        Rounds F .toOdd x (.finite w)) by
    rcases hF₁b : F₁.b with _ | b₁
    · exact key F₁ hsub (regular_of_bound_top hF₁b) h₁u
    · rcases bound_floor_setup hF₁b with ⟨hexp, hb₁0⟩ |
        ⟨D, hreg_G, hD_le, hD_max, hmono, -⟩
      · exact rounds_total_of_zero_bound h₁u (not_isUndefined_of_two_le_p hp_F₂)
          (fun hy hy0 => eq_zero_of_faithful_zero hexp hy.2.1 hy0)
          (fun hz => by rw [RoundsFinite.eq_zero_of_zero hz, Dyadic.coe_real_zero])
          hF₁b hb₁0 x
      · exact rounds_floor_lift hD_le hD_max (key _
          (fun v hv => hsub v ⟨hv.1, hv.2.1,
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
    have hzR : Rounds F₂ .toOdd x (.finite z) := ⟨h₂u, hz, hz_bnd⟩
    -- The chain does not overflow.
    have hw := rndUnbounded_satisfies F .toOdd (z : ℝ) h₁u
    set w := rndUnbounded F .toOdd (z : ℝ) h₁u with hw_def
    have hw_bnd : Format.boundOK F.b w :=
      toOdd_toOdd_noOverflow_chain hsub hreg hp_F₂ h₁u hy hbOK hz hw
    have hwR : Rounds F .toOdd (z : ℝ) (.finite w) := ⟨h₁u, hw, hw_bnd⟩
    -- Double rounding holds: restrict the chain, compose spec-relationally,
    -- and lift back along the in-bound direct rounding.
    have hsub_u : F.toFormat ⊆ F₂.unbounded.toFormat := fun d hd =>
      mem_unbounded_of_mem (F := F₂)
        (hsub d ⟨hd.1, hd.2.1, boundOK_boundAfterNext_of_boundOK hd.2.2⟩)
    have hw_bdd : RoundsFinite F .toOdd (z : ℝ) w :=
      RoundsFinite.toOdd_restrict hw hw_bnd
    have hxw : RoundsFinite F .toOdd x w := rndRTO_RTO hsub_u hp_F₂ hz hw_bdd
    exact ⟨z, w, hzR, hwR, ⟨h₁u, RoundsFinite.toOdd_lift hxw hy hbOK, hw_bnd⟩⟩
  · left
    exact rounds_overflow_of_not_boundOK h₁u hy hbOK

/-- **rnd-RTO-RTZ**, total form. Either rounding `x` directly in `F₁` (RTZ)
overflows, or the RTO rounding of `x` in `F₂` does not overflow (finite `z`),
the chained RTZ rounding is finite (`w`), and double rounding holds.
Nontriviality of `F₁` forces `2 ≤ F₂.p` through the containment. -/
theorem roundsRTO_RTZ {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial) (x : ℝ) :
    (∃ b, Rounds F₁ .toZero x (.overflow b)) ∨
    (∃ z w : Dyadic, Rounds F₂ .toOdd x (.finite z) ∧
      Rounds F₁ .toZero (z : ℝ) (.finite w) ∧
      Rounds F₁ .toZero x (.finite w)) := by
  have hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p := two_le_p_of_nontrivial hsub hnt
  -- Reduce to a bound that is on the grid (and positive when `exp = ⊥`)
  -- by replacing it with its grid floor.
  suffices key : ∀ F : FiniteFormat,
      ((F.extend 1).toFormat.withBound F.toFormat.boundAfterNext) ⊆ F₂.toFormat →
      (∀ b : NonNegDyadic, F.b = (b : Bound) →
        b.val ∈ F ∧ (F.exp = ⊥ → 0 < ((b.val : Dyadic) : ℝ))) →
      (∃ b, Rounds F .toZero x (.overflow b)) ∨
      (∃ z w : Dyadic, Rounds F₂ .toOdd x (.finite z) ∧
        Rounds F .toZero (z : ℝ) (.finite w) ∧
        Rounds F .toZero x (.finite w)) by
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
          (fun v hv => hsub v ⟨hv.1, hv.2.1,
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
    have hzR : Rounds F₂ .toOdd x (.finite z) := ⟨h₂u, hz, hz_bnd⟩
    -- The chain does not overflow.
    have hw := rndUnbounded_satisfies F .toZero (z : ℝ) h₁u
    set w := rndUnbounded F .toZero (z : ℝ) h₁u with hw_def
    have hw_bnd : Format.boundOK F.b w :=
      toOdd_toZero_noOverflow_chain hsub hreg hp_F₂ hy hbOK hz hw
    have hwR : Rounds F .toZero (z : ℝ) (.finite w) := ⟨h₁u, hw, hw_bnd⟩
    -- Double rounding holds: restrict the chain, compose spec-relationally,
    -- and lift back along the in-bound direct rounding.
    have hsub_u : ((F.extend 1).toFormat.withBound F.toFormat.boundAfterNext)
        ⊆ F₂.unbounded.toFormat := fun d hd =>
      mem_unbounded_of_mem (F := F₂) (hsub d hd)
    have hw_bdd : RoundsFinite F .toZero (z : ℝ) w :=
      RoundsFinite.toZero_restrict hw hw_bnd
    have hxw : RoundsFinite F .toZero x w := rndRTO_RTZ hsub_u hz hw_bdd
    exact ⟨z, w, hzR, hwR, ⟨h₁u, RoundsFinite.toZero_lift hxw hy hbOK, hw_bnd⟩⟩
  · left
    exact rounds_overflow_of_not_boundOK h₁u hy hbOK

/-- **rnd-RTO-RAZ**, total form. Either rounding `x` directly in `F₁` (RAZ)
overflows, or the RTO rounding of `x` in `F₂` does not overflow (finite `z`),
the chained RAZ rounding is finite (`w`), and double rounding holds.
Nontriviality of `F₁` forces, through the containment, that `F₂` supports
RTO. -/
theorem roundsRTO_RAZ {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial) (x : ℝ) :
    (∃ b, Rounds F₁ .awayZero x (.overflow b)) ∨
    (∃ z w : Dyadic, Rounds F₂ .toOdd x (.finite z) ∧
      Rounds F₁ .awayZero (z : ℝ) (.finite w) ∧
      Rounds F₁ .awayZero x (.finite w)) := by
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
    have hzR : Rounds F₂ .toOdd x (.finite z) := ⟨h₂u, hz, hz_bnd⟩
    -- The chain does not overflow: `y` competes for `w` at the point `z`.
    have hw := rndUnbounded_satisfies F₁ .awayZero (z : ℝ) h₁u
    set w := rndUnbounded F₁ .awayZero (z : ℝ) h₁u with hw_def
    have hw_bnd : Format.boundOK F₁.b w := by
      have h1 := hw.2.2.2 y hy.1 hzy_abs hzy_sign
      exact boundOK_of_abs_le h1 hbOK
    have hwR : Rounds F₁ .awayZero (z : ℝ) (.finite w) := ⟨h₁u, hw, hw_bnd⟩
    -- Double rounding holds: restrict the chain, compose spec-relationally,
    -- and lift back along the in-bound direct rounding.
    have hsub_u : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext)
        ⊆ F₂.unbounded.toFormat := fun d hd =>
      mem_unbounded_of_mem (F := F₂) (hsub d hd)
    have hw_bdd : RoundsFinite F₁ .awayZero (z : ℝ) w :=
      RoundsFinite.awayZero_restrict hw hw_bnd
    have hxw : RoundsFinite F₁ .awayZero x w := rndRTO_RAZ hsub_u hz hw_bdd
    exact ⟨z, w, hzR, hwR, ⟨h₁u, RoundsFinite.awayZero_lift hxw hy hbOK, hw_bnd⟩⟩
  · left
    exact rounds_overflow_of_not_boundOK h₁u hy hbOK

/-- **rnd-RTO-RN**, total form, parameterized by the tie-break `tb`. Either
rounding `x` directly in `F₁` (RN) overflows, or the RTO rounding of `x` in
`F₂` does not overflow (finite `z`), the chained RN rounding is finite (`w`),
and double rounding holds. Nontriviality of `F₁` forces `2 ≤ F₂.p` through
the containment; `F₁` must support the tie-break (vacuous for RNA). -/
theorem roundsRTO_RN {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
      ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial)
    {tb : TieBreak} (h₁u : ¬ F₁.IsUndefined (.nearest tb)) (x : ℝ) :
    (∃ b, Rounds F₁ (.nearest tb) x (.overflow b)) ∨
    (∃ z w : Dyadic, Rounds F₂ .toOdd x (.finite z) ∧
      Rounds F₁ (.nearest tb) (z : ℝ) (.finite w) ∧
      Rounds F₁ (.nearest tb) x (.finite w)) := by
  have hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p := two_le_p_of_nontrivial_extend_two hsub hnt
  -- Reduce to a bound that is on the grid (and positive when `exp = ⊥`)
  -- by replacing it with its grid floor.
  suffices key : ∀ F : FiniteFormat,
      ((F.extend 2).toFormat.withBound (F.extend 1).toFormat.boundAfterNext)
        ⊆ F₂.toFormat →
      (∀ b : NonNegDyadic, F.b = (b : Bound) →
        b.val ∈ F ∧ (F.exp = ⊥ → 0 < ((b.val : Dyadic) : ℝ))) →
      ¬ F.IsUndefined (.nearest tb) →
      (∃ b, Rounds F (.nearest tb) x (.overflow b)) ∨
      (∃ z w : Dyadic, Rounds F₂ .toOdd x (.finite z) ∧
        Rounds F (.nearest tb) (z : ℝ) (.finite w) ∧
        Rounds F (.nearest tb) x (.finite w)) by
    rcases hF₁b : F₁.b with _ | b₁
    · exact key F₁ hsub (regular_of_bound_top hF₁b) h₁u
    · rcases bound_floor_setup hF₁b with ⟨hexp, hb₁0⟩ |
        ⟨D, hreg_G, hD_le, hD_max, -, hmono_ext⟩
      · exact rounds_total_of_zero_bound h₁u (not_isUndefined_of_two_le_p hp_F₂)
          (fun hy hy0 => eq_zero_of_faithful_zero hexp (nearest_components hy).2.1 hy0)
          (fun hz => by rw [RoundsFinite.eq_zero_of_zero hz, Dyadic.coe_real_zero])
          hF₁b hb₁0 x
      · exact rounds_floor_lift hD_le hD_max (key _
          (fun v hv => hsub v ⟨hv.1, hv.2.1,
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
          le_trans hb₁_nn (lt_next'' b₁.val hb₁_nn).le
        have hz_abs : |(z : ℝ)| ≤ (((F.extend 1).toFormat.next b₁.val : Dyadic) : ℝ) :=
          abs_faithful_le_of_le (mem_unbounded_of_mem hM_F₂) hxM hz.2.1
        exact boundOK_of_abs_le (by rwa [abs_of_nonneg hM_nn]) hM_F₂.2.2
    have hzR : Rounds F₂ .toOdd x (.finite z) := ⟨h₂u, hz, hz_bnd⟩
    -- The chain does not overflow.
    have hw := rndUnbounded_satisfies F (.nearest tb) (z : ℝ) h₁u
    set w := rndUnbounded F (.nearest tb) (z : ℝ) h₁u with hw_def
    have hw_bnd : Format.boundOK F.b w :=
      toOdd_nearest_noOverflow_chain hsub hreg hp_F₂ h₁u hy hbOK hz hw
    have hwR : Rounds F (.nearest tb) (z : ℝ) (.finite w) := ⟨h₁u, hw, hw_bnd⟩
    -- Double rounding holds: restrict the chain, compose spec-relationally,
    -- and lift back along the in-bound direct rounding.
    have hsub_u : ((F.extend 2).toFormat.withBound (F.extend 1).toFormat.boundAfterNext)
        ⊆ F₂.unbounded.toFormat := fun d hd =>
      mem_unbounded_of_mem (F := F₂) (hsub d hd)
    have hw_bdd : RoundsFinite F (.nearest tb) (z : ℝ) w :=
      RoundsFinite.nearest_restrict hw hw_bnd
    have hxw : RoundsFinite F (.nearest tb) x w := rndRTO_RN hsub_u hz hw_bdd
    exact ⟨z, w, hzR, hwR, ⟨h₁u, RoundsFinite.nearest_lift hxw hy hbOK, hw_bnd⟩⟩
  · left
    exact rounds_overflow_of_not_boundOK h₁u hy hbOK

end Mpfx
