import Mpfx.DoubleRounding.Basic

/-!
# `rnd-RTO-RNE` / `rnd-RTO-RNA` (§5.2)

`roundsRTO_RN_finite`: round-to-odd in `F₂` then round-to-nearest in `F₁` (either
tie-break) is correct double rounding.
-/

namespace Mpfx

/-! ## Round-to-nearest helpers for `roundsRTO_RN_finite` -/

/-- Two distinct faithful roundings of `x` are its round-down and round-up, which
no value of `F` separates, so their midpoint is a value of `F.extend 1`. -/
private theorem midpoint_mem_extend_one_of_faithful {F : FiniteFormat} {x : ℝ} {a b : Dyadic}
    (ha : IsFaithfulRound F x a) (hb : IsFaithfulRound F x b) (hab : a ≠ b) :
    Dyadic.midpoint a b ∈ F.extend 1 := by
  have key : ∀ {d u : Dyadic}, RoundsFinite F .toNegative x d →
      RoundsFinite F .toPositive x u → d ≠ u → Dyadic.midpoint d u ∈ F.extend 1 :=
    fun {d u} hd hu hdu => midpoint_in_F₁_extend_one_of_F_adjacent hd.1 hu.1
      (lt_of_le_of_ne (hd.2.1.trans hu.2.1) fun h => hdu (Dyadic.ext_real h))
      fun y hy hdy => hu.2.2 y hy
        (not_le.mp fun hyx => absurd (hd.2.2 y hy hyx) (not_le.mpr hdy)).le
  rcases ha.opposite_sides_of_ne hb hab with ⟨hd, hu⟩ | ⟨hd, hu⟩
  · exact key hd hu hab
  · rw [Dyadic.midpoint_comm]; exact key hd hu hab.symm

/-- If `z` is no farther from `a` than from `b`, is not their midpoint `m`, and
`x` is on `z`'s side of `m`, then `x` is strictly nearer `a`. -/
private theorem closer_of_same_side {x z a b : ℝ} (hab : a ≠ b)
    (hz : |z - a| ≤ |z - b|) (hzm : z ≠ (a + b) / 2)
    (hside : 0 < (x - (a + b) / 2) * (z - (a + b) / 2)) : |x - a| < |x - b| := by
  rw [← sq_lt_sq]
  have h1 := sq_le_sq.mpr hz
  have hzm' : z - (a + b) / 2 ≠ 0 := sub_ne_zero.mpr hzm
  have hP : (b - a) * (z - (a + b) / 2) < 0 :=
    lt_of_le_of_ne (by nlinarith [h1]) (mul_ne_zero (sub_ne_zero.mpr hab.symm) hzm')
  have hz2 : 0 < (z - (a + b) / 2) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hzm'))
  have hQ : (b - a) * (x - (a + b) / 2) < 0 := by
    have := mul_neg_of_neg_of_pos hP hside
    nlinarith
  nlinarith [hQ]

/-- If `F₁` is trivial (contains only `0`) then `RoundsFinite F₁ (.nearest tb) x w'`
holds for any real `x` and tie-break `tb`, whenever `w' ∈ F₁` (so `w' = 0`).
The closeness and tie-break conditions are vacuous; faithfulness holds by the
round-down branch (`x ≥ 0`) or round-up branch (`x < 0`). -/
private theorem RoundsFinite.nearest_of_trivial {F₁ : FiniteFormat} {tb : TieBreak}
    (hF₁_triv : ∀ d : Dyadic, d ∈ F₁ → (d : ℝ) = 0)
    {x : ℝ} {w' : Dyadic} (hw : w' ∈ F₁) :
    RoundsFinite F₁ (.nearest tb) x w' := by
  have hw'_zero : (w' : ℝ) = 0 := hF₁_triv w' hw
  have h_eq_w' : ∀ z : Dyadic, z ∈ F₁ → z = w' := fun z hzF₁ =>
    (Dyadic.coe_real_inj z w').mp (by rw [hF₁_triv z hzF₁, hw'_zero])
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
  have h_close : ∀ z : Dyadic, z ∈ F₁ → IsFaithfulRound F₁ x z →
      |x - (w' : ℝ)| ≤ |x - (z : ℝ)| := by
    intro z hzF₁ _
    rw [hF₁_triv z hzF₁, hw'_zero]
  cases tb with
  | toEven =>
    refine ⟨hw, h_adj, h_close, ?_⟩
    rintro ⟨z, hzF₁, _, hz_ne_w', _⟩
    exact (hz_ne_w' (h_eq_w' z hzF₁)).elim
  | awayZero =>
    refine ⟨hw, h_adj, h_close, ?_⟩
    intro z hzF₁ _ hz_ne_w' _
    exact (hz_ne_w' (h_eq_w' z hzF₁)).elim

/-! ## `rnd-RTO-RN` — round-to-odd then round-to-nearest

Let `z` be an inexact RTO rounding of `x` in `F₂` and `w'` the nearest rounding of
`z` in `F₁`. Padding keeps `z` off `F₁.extend 1`, so off `F₁`: `x` and `z` then
have the same faithful roundings in `F₁` (`IsFaithfulRound.iff_of_between`). For
another such rounding `c`, the midpoint `m` of `w'` and `c` lies in
`F₁.extend 1 ⊆ F₂` but is not `z`, and `x` is not `m` either (else `z = x`).
A faithful rounding stays on its input's side of `m`
(`IsFaithfulRound.same_side`), so `x`, like `z`, is strictly nearer `w'` than
`c`: `w'` is the nearest rounding of `x`, with no tie. -/

/-- **rnd-RTO-RN** under `F₁.extend 2 ⊆ F₂` and `2 ≤ F₂.p`, without the relaxed
bound. -/
theorem roundsRTO_RN_finite_of_extend {F₁ F₂ : FiniteFormat}
    (hsub2 : (F₁.extend 2).toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {tb : TieBreak} {x : ℝ} {z w' : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z)
    (hw : RoundsFinite F₁ (.nearest tb) (z : ℝ) w') :
    RoundsFinite F₁ (.nearest tb) x w' := by
  have hsub_ext1 : (F₁.extend 1).toFormat ⊆ F₂.toFormat :=
    (Format.extend_mono F₁.toFormat (by norm_num)).trans hsub2
  have hsub' : F₁.toFormat ⊆ F₂.toFormat := (Format.self_subset_extend _ 1).trans hsub_ext1
  rcases eq_or_ne ((z : ℝ)) x with hzx | hzx
  · rw [hzx] at hw; exact hw
  have hxne : x ≠ (z : ℝ) := fun h => hzx h.symm
  have hsub_double : ((F₁.extend 1).extend 1).toFormat ⊆ F₂.toFormat :=
    (Format.extend_one_extend_one_subset_extend_two _).trans hsub2
  have hz_ext1 : z ∉ F₁.extend 1 := toOdd_notMem_of_extend_subset hsub_double hp_F₂ hz hxne
  have hz₁ : z ∉ F₁ := fun h => hz_ext1 (Format.self_subset_extend _ 1 z h)
  have hiff := IsFaithfulRound.iff_of_between hsub' hz.2.1 hz₁
  have hwf : IsFaithfulRound F₁ x w' := (hiff w').mpr hw.isFaithfulRound
  -- Every other faithful rounding of `x` is strictly farther than `w'`.
  have hcloser : ∀ c : Dyadic, c ∈ F₁ → IsFaithfulRound F₁ x c → c ≠ w' →
      |x - (w' : ℝ)| < |x - (c : ℝ)| := fun c hc hcf hcw => by
    have hm₁ := midpoint_mem_extend_one_of_faithful hwf hcf hcw.symm
    have hm₂ : Dyadic.midpoint w' c ∈ F₂ := hsub_ext1 _ hm₁
    have hzm : (z : ℝ) ≠ Dyadic.midpoint w' c := fun h => hz_ext1 (Dyadic.ext_real h ▸ hm₁)
    have hxm : x ≠ Dyadic.midpoint w' c := fun h => by
      have hzm' : z = Dyadic.midpoint w' c :=
        RoundsFinite.eq_of_mem hm₂ (by rw [← h]; exact hz)
      exact hxne (by rw [h, hzm'])
    have hside := hz.2.1.same_side hm₂ hxm hzm
    rw [Dyadic.coe_midpoint] at hzm hside
    exact closer_of_same_side (fun h => hcw (Dyadic.ext_real h).symm)
      (hw.nearest_min hc ((hiff c).mp hcf)) hzm hside
  have hclose : ∀ c : Dyadic, c ∈ F₁ → IsFaithfulRound F₁ x c →
      |x - (w' : ℝ)| ≤ |x - (c : ℝ)| := fun c hc hcf => by
    rcases eq_or_ne c w' with rfl | hcw
    · exact le_rfl
    · exact (hcloser c hc hcf hcw).le
  cases tb with
  | toEven => exact ⟨hw.1, hwf, hclose, fun ⟨c, hc, hcf, hcw, h⟩ =>
      absurd h (hcloser c hc hcf hcw).ne⟩
  | awayZero => exact ⟨hw.1, hwf, hclose, fun c hc hcf hcw h =>
      absurd h (hcloser c hc hcf hcw).ne⟩

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
  · exact RoundsFinite.nearest_of_trivial hF₁_triv hw.1

end Mpfx
