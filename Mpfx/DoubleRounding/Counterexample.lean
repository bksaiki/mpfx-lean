import Mpfx.DoubleRounding.Counterexample.Basic
import Mpfx.Format.Discrete

/-!
# Counterexamples to the invalid double-rounding pairings (§5.2)

The ten `no_rounds<rm₂>_<rm₁>` theorems refute every mode pairing absent
from the double-rounding rules: rounding `x` first in `F₂` under `rm₂` and then
in `F₁` under `rm₁` can disagree with rounding `x` directly in `F₁` under
`rm₁`. Each holds for **every** `F₂` satisfying the stated containment, so no
side condition on `F₂` can validate these pairings.

The witness is in bound throughout (`Disagrees`): no rounding overflows, so
it refutes the rule whatever the special-value and overflow maps
(`Disagrees.rnd_ne`). The `no_rnd<rm₂>_<rm₁>` forms state this for the
total `rnd`: a finite input whose chained rounding differs from the direct
one, for every `SpecialMap` and `OverflowMap`.

`F₁` may be bounded. Each theorem asks only for a few positive values of `F₁`
(`Format.HasPositive`), and with the anchors placed at the bottom of `F₁`
those counts are, we believe, the least that work for every `F₂`:

* one positive value (`Nontrivial`, `hasPositive_one_iff`): RNE → RTZ,
  RAZ → RTZ, RTZ → RNE, RNE → RNE;
* two: RTZ → RAZ, RNE → RAZ, RAZ → RTO, RNE → RTO, RAZ → RNE;
* three: RTZ → RTO.

With one value fewer, an `F₂` without a minimum quantum seems to agree on
every input that stays in bound, so only the overflow maps could make it fail.
That minimality is not proved. With no minimum quantum in `F₁`
any positive bound gives infinitely many values, and an unbounded `F₁` has
all of them (`FiniteFormat.hasPositive_of_b_top`).
-/

namespace Mpfx

namespace Cex

/-- Rounding into `F₂` under `rm₂` and then into `F₁` under `rm₁` disagrees
with rounding into `F₁` directly, at an input where no rounding overflows. -/
def Disagrees (F₂ : FiniteFormat) (rm₂ : RoundingMode) (F₁ : FiniteFormat)
    (rm₁ : RoundingMode) : Prop :=
  ∃ (x : ℝ) (z w y : Dyadic), RoundsInBound F₂ rm₂ x z ∧ RoundsInBound F₁ rm₁ (z : ℝ) w ∧
    RoundsInBound F₁ rm₁ x y ∧ w ≠ y

/-- A `Disagrees` witness refutes `rnd₁ ∘ rnd₂ = rnd₁` (the conclusion of
`rnd_double`) at a finite input with a finite intermediate, for every choice of
special-value and overflow maps. -/
theorem Disagrees.rnd_ne {F₂ F₁ : FiniteFormat} {rm₂ rm₁ : RoundingMode}
    (h : Disagrees F₂ rm₂ F₁ rm₁) (h₂ : ¬ F₂.IsUndefined rm₂) (h₁ : ¬ F₁.IsUndefined rm₁)
    (S₂ : SpecialMap F₂.toFormat) (O₂ : OverflowMap F₂.toFormat)
    (S₁ : SpecialMap F₁.toFormat) (O₁ : OverflowMap F₁.toFormat) :
    ∃ (x : ℝ) (z : Dyadic), rnd F₂ S₂ O₂ rm₂ (.finite x) = .value (.finite z) ∧
      rnd F₁ S₁ O₁ rm₁ (.finite (z : ℝ)) ≠ rnd F₁ S₁ O₁ rm₁ (.finite x) := by
  obtain ⟨x, z, w, y, hz, hw, hy, hne⟩ := h
  refine ⟨x, z, by rw [rnd_finite_of_roundsFinite h₂ hz.1, if_pos hz.2], ?_⟩
  rw [rnd_finite_of_roundsFinite h₁ hw.1, if_pos hw.2,
    rnd_finite_of_roundsFinite h₁ hy.1, if_pos hy.2]
  exact fun heq => hne (WithSpecial.finite.inj (RoundResult.value.inj heq))

/-! ## Anchors -/

section Anchors

variable {F₁ : ParityFormat}

private theorem exists_one {F : Format} (h : F.HasPositive 1) :
    ∃ a : Dyadic, a ∈ F ∧ (0 : ℝ) < a := by
  obtain ⟨f, -, hf⟩ := h
  exact ⟨f 0, hf 0⟩

private theorem exists_two {F : Format} (h : F.HasPositive 2) :
    ∃ a b : Dyadic, a ∈ F ∧ b ∈ F ∧ (0 : ℝ) < a ∧ (a : ℝ) < b := by
  obtain ⟨f, hmono, hf⟩ := h
  exact ⟨f 0, f 1, (hf 0).1, (hf 1).1, (hf 0).2, hmono (by decide : (0 : Fin 2) < 1)⟩

private theorem exists_three {F : Format} (h : F.HasPositive 3) :
    ∃ a b c : Dyadic, a ∈ F ∧ b ∈ F ∧ c ∈ F ∧ (0 : ℝ) < a ∧ (a : ℝ) < b ∧ (b : ℝ) < c := by
  obtain ⟨f, hmono, hf⟩ := h
  exact ⟨f 0, f 1, f 2, (hf 0).1, (hf 1).1, (hf 2).1, (hf 0).2,
    hmono (by decide : (0 : Fin 3) < 1), hmono (by decide : (1 : Fin 3) < 2)⟩

/-- A value between `0` and a value of `F` is in `F`'s bound. -/
private theorem boundOK_of_le {F : Format} {z a : Dyadic} (ha : a ∈ F) (hz : 0 ≤ (z : ℝ))
    (hza : (z : ℝ) ≤ a) : Format.boundOK F.b z :=
  boundOK_of_abs_le (by rw [abs_of_nonneg hz, abs_of_nonneg (hz.trans hza)]; exact hza) ha.2.2

/-- Between two positive values `a < b`, a positive value at most `b` that is
not odd: `b` or its predecessor. -/
private theorem exists_not_odd {a b : Dyadic} (ha : a ∈ F₁.toFormat) (hb : b ∈ F₁.toFormat)
    (ha_pos : (0 : ℝ) < a) (hab : (a : ℝ) < b) :
    ∃ h : Dyadic, h ∈ F₁.toFormat ∧ (0 : ℝ) < h ∧ (h : ℝ) ≤ b ∧ ¬ F₁.IsOdd h := by
  obtain ⟨u, hadj, hu0⟩ :=
    exists_pred F₁.toFiniteFormat (mem_unbounded_of_mem hb) (ha_pos.trans hab)
  by_cases hodd : F₁.IsOdd b
  · exact ⟨u, mem_of_mem_unbounded_of_boundOK hadj.1 (boundOK_of_le hb hu0 hadj.2.2.1.le),
      ha_pos.trans_le (hadj.2.2.2 a (mem_unbounded_of_mem ha) hab), hadj.2.2.1.le,
      (alternate_of_adjacent F₁ hadj).1.mp hodd⟩
  · exact ⟨b, hb, ha_pos.trans hab, le_rfl, hodd⟩

/-- Below a positive value `a`, adjacent values `u < u' ≤ a` with `u ≥ 0` even:
the predecessor of `a`, or else the predecessor's predecessor. -/
private theorem exists_even_lower {a : Dyadic} (ha : a ∈ F₁.toFormat) (ha_pos : (0 : ℝ) < a) :
    ∃ u u' : Dyadic, Adjacent F₁.toFiniteFormat u u' ∧ 0 ≤ (u : ℝ) ∧
      u' ∈ F₁.toFormat ∧ F₁.IsEven u := by
  obtain ⟨u, hadj, hu0⟩ := exists_pred F₁.toFiniteFormat (mem_unbounded_of_mem ha) ha_pos
  by_cases heven : F₁.IsEven u
  · exact ⟨u, a, hadj, hu0, ha, heven⟩
  -- `u` is not even, so it is not `0`, and its predecessor is even.
  have hu_pos : (0 : ℝ) < u := hu0.lt_of_ne fun h => heven (by
    rw [Dyadic.ext_real (h.symm.trans Dyadic.coe_real_zero.symm)]
    exact F₁.isEven_zero)
  obtain ⟨u₀, hadj₀, hu₀⟩ := exists_pred F₁.toFiniteFormat hadj.1 hu_pos
  have heven₀ : F₁.IsEven u₀ := by
    by_contra h
    exact heven ((alternate_of_adjacent F₁ hadj₀).2 h)
  exact ⟨u₀, u, hadj₀, hu₀,
    mem_of_mem_unbounded_of_boundOK hadj.1 (boundOK_of_le ha hu0 hadj.2.2.1.le), heven₀⟩

/-- Below the larger of two positive values `a < b`, adjacent values
`u < u' ≤ b` with `u ≥ 0` and `u'` even: `b` and its predecessor, or else the
predecessor and its own. -/
private theorem exists_even_upper {a b : Dyadic} (ha : a ∈ F₁.toFormat) (hb : b ∈ F₁.toFormat)
    (ha_pos : (0 : ℝ) < a) (hab : (a : ℝ) < b) :
    ∃ u u' : Dyadic, Adjacent F₁.toFiniteFormat u u' ∧ 0 ≤ (u : ℝ) ∧
      u' ∈ F₁.toFormat ∧ F₁.IsEven u' := by
  obtain ⟨u, hadj, hu0⟩ :=
    exists_pred F₁.toFiniteFormat (mem_unbounded_of_mem hb) (ha_pos.trans hab)
  by_cases heven : F₁.IsEven b
  · exact ⟨u, b, hadj, hu0, hb, heven⟩
  have heven_u : F₁.IsEven u := by
    by_contra h
    exact heven ((alternate_of_adjacent F₁ hadj).2 h)
  have hu_pos : (0 : ℝ) < u := ha_pos.trans_le (hadj.2.2.2 a (mem_unbounded_of_mem ha) hab)
  obtain ⟨u₀, hadj₀, hu₀⟩ := exists_pred F₁.toFiniteFormat hadj.1 hu_pos
  exact ⟨u₀, u, hadj₀, hu₀,
    mem_of_mem_unbounded_of_boundOK hadj.1 (boundOK_of_le hb hu0 hadj.2.2.1.le), heven_u⟩

end Anchors

/-- The distances from `z ∈ [u, u']` to the two ends. -/
private theorem abs_sub_of_bracket {u u' z : ℝ} (h₁ : u ≤ z) (h₂ : z ≤ u') :
    |z - u| = z - u ∧ |z - u'| = u' - z :=
  ⟨abs_of_nonneg (by linarith), by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)⟩

/-! ## Cores for the directed and round-to-odd targets

Each takes the intermediate rounding of `x` onto an anchor of `F₁` as a
hypothesis; the direct rounding then misses the anchor. -/

/-- The intermediate lands on `a > x`, which RTZ fixes; the direct RTZ is at
most `x`. -/
private theorem disagrees_toZero {F₁ F₂ : FiniteFormat} {rm₂ : RoundingMode} {a : Dyadic}
    (ha : a ∈ F₁.toFormat) {x : ℝ} (hx0 : 0 ≤ x) (hxa : x < a)
    (hz : RoundsInBound F₂ rm₂ x a) : Disagrees F₂ rm₂ F₁ .toZero := by
  have hy := rndDown_spec F₁ x
  have hy_le := rndDown_le F₁ x
  refine ⟨x, a, a, rndDown F₁ x, hz,
    ⟨RoundsFinite.toZero_self (mem_unbounded_of_mem ha), ha.2.2⟩,
    ⟨(RoundsFinite.toNegative_iff_toZero_of_nonneg _ hx0 _).mp hy,
      boundOK_of_le ha (RoundsFinite.toNegative_nonneg hx0 hy) (by linarith)⟩,
    fun h => ?_⟩
  rw [← h] at hy_le
  linarith

/-- The intermediate lands on `a < x`, which RAZ fixes; the direct RAZ is at
least `x`, and at most the value `b ≥ x`. -/
private theorem disagrees_awayZero {F₁ F₂ : FiniteFormat} {rm₂ : RoundingMode} {a b : Dyadic}
    (ha : a ∈ F₁.toFormat) (hb : b ∈ F₁.toFormat) {x : ℝ} (hx0 : 0 ≤ x) (hax : (a : ℝ) < x)
    (hxb : x ≤ b) (hz : RoundsInBound F₂ rm₂ x a) : Disagrees F₂ rm₂ F₁ .awayZero := by
  have hy := rndUp_spec F₁ x
  have hy_ge := le_rndUp F₁ x
  refine ⟨x, a, a, rndUp F₁ x, hz,
    ⟨RoundsFinite.awayZero_self (mem_unbounded_of_mem ha), ha.2.2⟩,
    ⟨(RoundsFinite.toPositive_iff_awayZero_of_nonneg _ hx0 _).mp hy,
      boundOK_of_le hb (by linarith) (rndUp_min F₁ x (mem_unbounded_of_mem hb) hxb)⟩,
    fun h => ?_⟩
  rw [← h] at hy_ge
  linarith

/-- The intermediate lands on a non-odd `h ≠ x`, which RTO fixes; the direct
RTO is inexact and so odd, and at most the value `c ≥ x`. -/
private theorem disagrees_toOdd {F₁ : ParityFormat} {F₂ : FiniteFormat} {rm₂ : RoundingMode}
    {h c : Dyadic} (hh : h ∈ F₁.toFormat) (hh_odd : ¬ F₁.IsOdd h) (hc : c ∈ F₁.toFormat)
    {x : ℝ} (hx0 : 0 ≤ x) (hxc : x ≤ c) (hxh : x ≠ h) (hz : RoundsInBound F₂ rm₂ x h) :
    Disagrees F₂ rm₂ F₁.toFiniteFormat .toOdd := by
  have hy := rndUnbounded_satisfies F₁.toFiniteFormat .toOdd x (F₁.not_isUndefined _)
  have hy_le := abs_faithful_le_of_le (mem_unbounded_of_mem hc)
    (by rwa [abs_of_nonneg hx0]) hy.isFaithfulRound
  refine ⟨x, h, h, _, hz, ⟨RoundsFinite.toOdd_self (mem_unbounded_of_mem hh), hh.2.2⟩,
    ⟨hy, boundOK_of_abs_le (by rwa [abs_of_nonneg (hx0.trans hxc)]) hc.2.2⟩, fun he => ?_⟩
  rw [← he] at hy
  exact hh_odd (isOdd_of_roundsRTO F₁ hy hxh)

/-! ## The counterexamples

Throughout, `2^K` isolates the anchor in `F₂` (and, where the witness must
stay short of a neighboring value, in `F₁`), and the witness `x` lies a
quarter of it from the anchor. -/

/-- **RNE → RTZ.** `x = a − δ` below a positive value `a`: the intermediate RNE
carries `x` up onto `a`, which RTZ fixes, but the direct RTZ falls below
`a`. -/
theorem no_roundsRNE_RTZ (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 1)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    Disagrees F₂ (.nearest .toEven) F₁.toFiniteFormat .toZero := by
  obtain ⟨a, ha, ha_pos⟩ := exists_one h₁
  obtain ⟨K, hK, hK_le⟩ := exists_isolated_le F₂ ha_pos
  have hK_pos : (0 : ℝ) < (2 : ℝ) ^ K := zpow_pos two_pos K
  exact disagrees_toZero (x := a - 2 ^ K / 4) ha (by linarith) (by linarith)
    ⟨roundsRNE_of_isolated hK (mem_unbounded_of_mem (hsub _ ha))
      (abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩), (hsub _ ha).2.2⟩

/-- **RAZ → RTZ.** `x = a − δ`: the intermediate RAZ pushes `x` up onto `a`,
which RTZ fixes, but the direct RTZ falls below `a`. -/
theorem no_roundsRAZ_RTZ (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 1)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    Disagrees F₂ .awayZero F₁.toFiniteFormat .toZero := by
  obtain ⟨a, ha, ha_pos⟩ := exists_one h₁
  obtain ⟨K, hK, hK_le⟩ := exists_isolated_le F₂ ha_pos
  have hK_pos : (0 : ℝ) < (2 : ℝ) ^ K := zpow_pos two_pos K
  exact disagrees_toZero (x := a - 2 ^ K / 4) ha (by linarith) (by linarith)
    ⟨(RoundsFinite.toPositive_iff_awayZero_of_nonneg _ (by linarith) _).mp
      (roundsUp_of_isolated hK (mem_unbounded_of_mem (hsub _ ha)) (by linarith) (by linarith)),
      (hsub _ ha).2.2⟩

/-- **RTZ → RAZ.** `x = a + δ` above the smaller of two positive values
`a < b`: the intermediate RTZ truncates onto `a`, which RAZ fixes, but the
direct RAZ reaches past `a`, to at most `b`. -/
theorem no_roundsRTZ_RAZ (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 2)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    Disagrees F₂ .toZero F₁.toFiniteFormat .awayZero := by
  obtain ⟨a, b, ha, hb, ha_pos, hab⟩ := exists_two h₁
  obtain ⟨K, hK₂, hK₁, -⟩ := exists_isolated₂ F₂ F₁.toFiniteFormat ha_pos
  have hK_pos : (0 : ℝ) < (2 : ℝ) ^ K := zpow_pos two_pos K
  have hKb : (2 : ℝ) ^ K ≤ b - a := by
    have := hK₁.le_abs_sub (mem_unbounded_of_mem hb) (fun h => by rw [h] at hab; linarith)
    rwa [abs_of_pos (by linarith)] at this
  exact disagrees_awayZero (x := a + 2 ^ K / 4) ha hb (by linarith) (by linarith) (by linarith)
    ⟨(RoundsFinite.toNegative_iff_toZero_of_nonneg _ (by linarith) _).mp
      (roundsDown_of_isolated hK₂ (mem_unbounded_of_mem (hsub _ ha)) (by linarith)
        (by linarith)), (hsub _ ha).2.2⟩

/-- **RNE → RAZ.** `x = a + δ`: the intermediate RNE rounds down onto `a`, which
RAZ fixes, but the direct RAZ reaches past `a`, to at most `b`. -/
theorem no_roundsRNE_RAZ (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 2)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    Disagrees F₂ (.nearest .toEven) F₁.toFiniteFormat .awayZero := by
  obtain ⟨a, b, ha, hb, ha_pos, hab⟩ := exists_two h₁
  obtain ⟨K, hK₂, hK₁, -⟩ := exists_isolated₂ F₂ F₁.toFiniteFormat ha_pos
  have hK_pos : (0 : ℝ) < (2 : ℝ) ^ K := zpow_pos two_pos K
  have hKb : (2 : ℝ) ^ K ≤ b - a := by
    have := hK₁.le_abs_sub (mem_unbounded_of_mem hb) (fun h => by rw [h] at hab; linarith)
    rwa [abs_of_pos (by linarith)] at this
  exact disagrees_awayZero (x := a + 2 ^ K / 4) ha hb (by linarith) (by linarith) (by linarith)
    ⟨roundsRNE_of_isolated hK₂ (mem_unbounded_of_mem (hsub _ ha))
      (abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩), (hsub _ ha).2.2⟩

/-- **RAZ → RTO.** `x = h − δ` below a positive value `h` that is not odd: the
intermediate RAZ lands exactly on `h`, which RTO fixes, but the direct RTO is
inexact and so odd. -/
theorem no_roundsRAZ_RTO (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 2)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    Disagrees F₂ .awayZero F₁.toFiniteFormat .toOdd := by
  obtain ⟨a, b, ha, hb, ha_pos, hab⟩ := exists_two h₁
  obtain ⟨h, hh, hh_pos, -, hh_odd⟩ := exists_not_odd ha hb ha_pos hab
  obtain ⟨K, hK, hK_le⟩ := exists_isolated_le F₂ hh_pos
  have hK_pos : (0 : ℝ) < (2 : ℝ) ^ K := zpow_pos two_pos K
  exact disagrees_toOdd (x := h - 2 ^ K / 4) hh hh_odd hh (by linarith) (by linarith)
    (by linarith)
    ⟨(RoundsFinite.toPositive_iff_awayZero_of_nonneg _ (by linarith) _).mp
      (roundsUp_of_isolated hK (mem_unbounded_of_mem (hsub _ hh)) (by linarith) (by linarith)),
      (hsub _ hh).2.2⟩

/-- **RNE → RTO.** `x = h − δ`: the intermediate RNE lands exactly on the
non-odd `h`, which RTO fixes, but the direct RTO is inexact and so odd. -/
theorem no_roundsRNE_RTO (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 2)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    Disagrees F₂ (.nearest .toEven) F₁.toFiniteFormat .toOdd := by
  obtain ⟨a, b, ha, hb, ha_pos, hab⟩ := exists_two h₁
  obtain ⟨h, hh, hh_pos, -, hh_odd⟩ := exists_not_odd ha hb ha_pos hab
  obtain ⟨K, hK, hK_le⟩ := exists_isolated_le F₂ hh_pos
  have hK_pos : (0 : ℝ) < (2 : ℝ) ^ K := zpow_pos two_pos K
  exact disagrees_toOdd (x := h - 2 ^ K / 4) hh hh_odd hh (by linarith) (by linarith)
    (by linarith)
    ⟨roundsRNE_of_isolated hK (mem_unbounded_of_mem (hsub _ hh))
      (abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩), (hsub _ hh).2.2⟩

/-- **RTZ → RTO.** `x = h + δ` above a positive non-odd value `h` with a value
`c > h` above it: the intermediate RTZ truncates onto `h`, which RTO fixes, but
the direct RTO is inexact and so odd, at most `c`. -/
theorem no_roundsRTZ_RTO (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 3)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    Disagrees F₂ .toZero F₁.toFiniteFormat .toOdd := by
  obtain ⟨a, b, c, ha, hb, hc, ha_pos, hab, hbc⟩ := exists_three h₁
  obtain ⟨h, hh, hh_pos, hhb, hh_odd⟩ := exists_not_odd ha hb ha_pos hab
  obtain ⟨K, hK₂, hK₁, -⟩ := exists_isolated₂ F₂ F₁.toFiniteFormat hh_pos
  have hK_pos : (0 : ℝ) < (2 : ℝ) ^ K := zpow_pos two_pos K
  have hKc : (2 : ℝ) ^ K ≤ c - h := by
    have := hK₁.le_abs_sub (mem_unbounded_of_mem hc)
      (fun he => by rw [he] at hbc; linarith)
    rwa [abs_of_pos (by linarith)] at this
  exact disagrees_toOdd (x := h + 2 ^ K / 4) hh hh_odd hc (by linarith) (by linarith)
    (by linarith)
    ⟨(RoundsFinite.toNegative_iff_toZero_of_nonneg _ (by linarith) _).mp
      (roundsDown_of_isolated hK₂ (mem_unbounded_of_mem (hsub _ hh)) (by linarith)
        (by linarith)), (hsub _ hh).2.2⟩

/-- **RTZ → RNE.** Adjacent values `u < u'` with `u ≥ 0` even, and
`x = m + δ` just above their midpoint `m`: the intermediate RTZ lands in
`[u, m]`, where RNE returns `u` (at `m` by the tie-break), but the direct RNE
returns the strictly nearer `u'`. -/
theorem no_roundsRTZ_RNE (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 1)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    Disagrees F₂ .toZero F₁.toFiniteFormat (.nearest .toEven) := by
  obtain ⟨a, ha, ha_pos⟩ := exists_one h₁
  obtain ⟨u, u', hadj, hu0, hu', heven⟩ := exists_even_lower ha ha_pos
  have hlt := hadj.2.2.1
  have hu : u ∈ F₁.toFormat :=
    mem_of_mem_unbounded_of_boundOK hadj.1 (boundOK_of_le hu' hu0 hlt.le)
  set m := Dyadic.midpoint u u'
  have hm : (m : ℝ) = ((u : ℝ) + u') / 2 := Dyadic.coe_midpoint u u'
  obtain ⟨K, hK₂, hK₁, -⟩ := exists_isolated₂ F₂ F₁.toFiniteFormat
    (show (0 : ℝ) < m by rw [hm]; linarith)
  have hK_pos : (0 : ℝ) < (2 : ℝ) ^ K := zpow_pos two_pos K
  have hKu' : (2 : ℝ) ^ K ≤ u' - m := by
    have := hK₁.le_abs_sub hadj.2.1 (fun he => by
      have := (Dyadic.coe_real_inj _ _).mpr he; linarith)
    rwa [abs_of_pos (by linarith)] at this
  set x : ℝ := (m : ℝ) + (2 : ℝ) ^ K / 4 with hx
  have hx0 : 0 ≤ x := by linarith
  -- The intermediate RTZ lands in `[u, m]`.
  set z := rndDown F₂ x
  have hz := rndDown_spec F₂ x
  have hz_le : (z : ℝ) ≤ m := le_of_roundsDown_of_isolated hK₂ hz (by linarith)
  have hz_ge : (u : ℝ) ≤ z := rndDown_max F₂ x (mem_unbounded_of_mem (hsub _ hu)) (by linarith)
  obtain ⟨hzu, hzu'⟩ := abs_sub_of_bracket hz_ge (by linarith : (z : ℝ) ≤ u')
  obtain ⟨hxu, hxu'⟩ := abs_sub_of_bracket (by linarith : (u : ℝ) ≤ x) (by linarith : x ≤ u')
  refine ⟨x, z, u, u',
    ⟨(RoundsFinite.toNegative_iff_toZero_of_nonneg _ hx0 _).mp hz,
      boundOK_of_le (hsub _ hu') (by linarith) (by linarith)⟩,
    ⟨roundsRNE_of_bracket hadj hz_ge (by linarith) (Or.inl rfl)
      ⟨le_rfl, by rw [hzu, hzu']; linarith⟩ fun _ => isEven_witness F₁ heven, hu.2.2⟩,
    ⟨roundsRNE_of_bracket hadj (by linarith) (by linarith) (Or.inr rfl)
      ⟨by rw [hxu, hxu']; linarith, le_rfl⟩ fun he => by rw [hxu, hxu'] at he; linarith,
      hu'.2.2⟩,
    fun he => by rw [he] at hlt; exact lt_irrefl _ hlt⟩

/-- **RAZ → RNE.** Adjacent values `u < u'` with `u ≥ 0` and `u'` even, and
`x = m − δ` just below their midpoint `m`: the intermediate RAZ lands in
`[m, u']`, where RNE returns `u'` (at `m` by the tie-break), but the direct RNE
returns the strictly nearer `u`. -/
theorem no_roundsRAZ_RNE (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 2)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    Disagrees F₂ .awayZero F₁.toFiniteFormat (.nearest .toEven) := by
  obtain ⟨a, b, ha, hb, ha_pos, hab⟩ := exists_two h₁
  obtain ⟨u, u', hadj, hu0, hu', heven⟩ := exists_even_upper ha hb ha_pos hab
  have hlt := hadj.2.2.1
  have hu : u ∈ F₁.toFormat :=
    mem_of_mem_unbounded_of_boundOK hadj.1 (boundOK_of_le hu' hu0 hlt.le)
  set m := Dyadic.midpoint u u'
  have hm : (m : ℝ) = ((u : ℝ) + u') / 2 := Dyadic.coe_midpoint u u'
  obtain ⟨K, hK₂, hK₁, hK_le⟩ := exists_isolated₂ F₂ F₁.toFiniteFormat
    (show (0 : ℝ) < m by rw [hm]; linarith)
  have hK_pos : (0 : ℝ) < (2 : ℝ) ^ K := zpow_pos two_pos K
  have hKu : (2 : ℝ) ^ K ≤ m - u := by
    have := hK₁.le_abs_sub hadj.1 (fun he => by
      have := (Dyadic.coe_real_inj _ _).mpr he; linarith)
    rwa [abs_of_neg (by linarith), neg_sub] at this
  set x : ℝ := (m : ℝ) - (2 : ℝ) ^ K / 4 with hx
  have hx0 : 0 ≤ x := by linarith
  -- The intermediate RAZ lands in `[m, u']`.
  set z := rndUp F₂ x
  have hz := rndUp_spec F₂ x
  have hz_ge : (m : ℝ) ≤ z := le_of_roundsUp_of_isolated hK₂ hz (by linarith)
  have hz_le : (z : ℝ) ≤ u' := rndUp_min F₂ x (mem_unbounded_of_mem (hsub _ hu')) (by linarith)
  obtain ⟨hzu, hzu'⟩ := abs_sub_of_bracket (by linarith : (u : ℝ) ≤ z) hz_le
  obtain ⟨hxu, hxu'⟩ := abs_sub_of_bracket (by linarith : (u : ℝ) ≤ x) (by linarith : x ≤ u')
  refine ⟨x, z, u', u,
    ⟨(RoundsFinite.toPositive_iff_awayZero_of_nonneg _ hx0 _).mp hz,
      boundOK_of_le (hsub _ hu') (by linarith) hz_le⟩,
    ⟨roundsRNE_of_bracket hadj (by linarith) hz_le (Or.inr rfl)
      ⟨by rw [hzu, hzu']; linarith, le_rfl⟩ fun _ => isEven_witness F₁ heven, hu'.2.2⟩,
    ⟨roundsRNE_of_bracket hadj (by linarith) (by linarith) (Or.inl rfl)
      ⟨le_rfl, by rw [hxu, hxu']; linarith⟩ fun he => by rw [hxu, hxu'] at he; linarith,
      hu.2.2⟩,
    fun he => by rw [he] at hlt; exact lt_irrefl _ hlt⟩

/-- **RNE → RNE.** One extra digit makes the midpoint `m` of adjacent values
`u < u'` representable in `F₂`, and one of `u`, `u'` is even. The witness
`x = m ± δ` sits on the side of the other one: the intermediate RNE lands
exactly on `m`, a tie that breaks to the even value, while the direct RNE
returns the strictly nearer other one. (Tight: with `F₂ = F₁`,
RNE ∘ RNE = RNE by idempotence.) -/
theorem no_roundsRNE_RNE (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 1)
    (F₂ : FiniteFormat) (hsub : (F₁.toFiniteFormat.extend 1).toFormat ⊆ F₂.toFormat) :
    Disagrees F₂ (.nearest .toEven) F₁.toFiniteFormat (.nearest .toEven) := by
  obtain ⟨u', hu', hu'_pos⟩ := exists_one h₁
  obtain ⟨u, hadj, hu0⟩ :=
    exists_pred F₁.toFiniteFormat (mem_unbounded_of_mem hu') hu'_pos
  have hlt := hadj.2.2.1
  have hu : u ∈ F₁.toFormat :=
    mem_of_mem_unbounded_of_boundOK hadj.1 (boundOK_of_le hu' hu0 hlt.le)
  set m := Dyadic.midpoint u u'
  have hm : (m : ℝ) = ((u : ℝ) + u') / 2 := Dyadic.coe_midpoint u u'
  -- `m` is a value of `F₁` with one extra digit, hence of `F₂`.
  have hm₂ : m ∈ F₂.toFormat := by
    have h := midpoint_in_F₁_extend_one_of_F_adjacent (F₁ := F₁.unbounded) hadj.1 hadj.2.1 hlt
      fun v hv hv' => not_lt.mp fun h => by linarith [hadj.2.2.2 v hv h]
    have hb : Format.boundOK F₁.b m :=
      boundOK_of_le hu' (by rw [hm]; linarith) (by rw [hm]; linarith)
    exact hsub _ ⟨h.1, h.2.1, hb⟩
  obtain ⟨K, hK₂, hK₁, -⟩ := exists_isolated₂ F₂ F₁.toFiniteFormat
    (show (0 : ℝ) < m by rw [hm]; linarith)
  have hK_pos : (0 : ℝ) < (2 : ℝ) ^ K := zpow_pos two_pos K
  have hKu : (2 : ℝ) ^ K ≤ m - u := by
    have := hK₁.le_abs_sub hadj.1 (fun he => by
      have := (Dyadic.coe_real_inj _ _).mpr he; linarith)
    rwa [abs_of_neg (by linarith), neg_sub] at this
  have hm_mid : |(m : ℝ) - u| = |(m : ℝ) - u'| := by
    rw [(abs_sub_of_bracket (by linarith : (u : ℝ) ≤ m) (by linarith : (m : ℝ) ≤ u')).1,
      (abs_sub_of_bracket (by linarith : (u : ℝ) ≤ m) (by linarith : (m : ℝ) ≤ u')).2, hm]
    ring
  have hm_le : (m : ℝ) ≤ u' := by linarith
  have hu_le : (u : ℝ) ≤ m := by linarith
  have hz₂ : ∀ x : ℝ, |x - m| < (2 : ℝ) ^ K / 2 → RoundsInBound F₂ (.nearest .toEven) x m :=
    fun x hx => ⟨roundsRNE_of_isolated hK₂ (mem_unbounded_of_mem hm₂) hx, hm₂.2.2⟩
  by_cases heven : F₁.IsEven u
  · -- The tie at `m` breaks down to `u`; `x` sits above `m`, nearer `u'`.
    set x : ℝ := (m : ℝ) + (2 : ℝ) ^ K / 4 with hx
    obtain ⟨hxu, hxu'⟩ := abs_sub_of_bracket (by linarith : (u : ℝ) ≤ x) (by linarith : x ≤ u')
    refine ⟨x, m, u, u', hz₂ x (abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩),
      ⟨roundsRNE_of_bracket hadj hu_le hm_le (Or.inl rfl) ⟨le_rfl, hm_mid.le⟩
        fun _ => isEven_witness F₁ heven, hu.2.2⟩,
      ⟨roundsRNE_of_bracket hadj (by linarith) (by linarith) (Or.inr rfl)
        ⟨by rw [hxu, hxu']; linarith, le_rfl⟩ fun he => by rw [hxu, hxu'] at he; linarith,
        hu'.2.2⟩,
      fun he => by rw [he] at hlt; exact lt_irrefl _ hlt⟩
  · -- `u'` is even, so the tie breaks up to it; `x` sits below `m`, nearer `u`.
    have heven' := (alternate_of_adjacent F₁ hadj).2 heven
    set x : ℝ := (m : ℝ) - (2 : ℝ) ^ K / 4 with hx
    obtain ⟨hxu, hxu'⟩ := abs_sub_of_bracket (by linarith : (u : ℝ) ≤ x) (by linarith : x ≤ u')
    refine ⟨x, m, u', u, hz₂ x (abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩),
      ⟨roundsRNE_of_bracket hadj hu_le hm_le (Or.inr rfl) ⟨hm_mid.ge, le_rfl⟩
        fun _ => isEven_witness F₁ heven', hu'.2.2⟩,
      ⟨roundsRNE_of_bracket hadj (by linarith) (by linarith) (Or.inl rfl)
        ⟨le_rfl, by rw [hxu, hxu']; linarith⟩ fun he => by rw [hxu, hxu'] at he; linarith,
        hu.2.2⟩,
      fun he => by rw [he] at hlt; exact lt_irrefl _ hlt⟩

/-! ## On `rnd`

With a nearest-even intermediate, `F₂` must make that mode defined, which only
`𝒜(1, ⊥, ·)` fails. -/

/-- `no_roundsRNE_RTZ` on `rnd`. -/
theorem no_rndRNE_RTZ (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 1)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (h₂ : ¬ F₂.IsUndefined (.nearest .toEven))
    (S₂ : SpecialMap F₂.toFormat) (O₂ : OverflowMap F₂.toFormat)
    (S₁ : SpecialMap F₁.toFormat) (O₁ : OverflowMap F₁.toFormat) :
    ∃ (x : ℝ) (z : Dyadic), rnd F₂ S₂ O₂ (.nearest .toEven) (.finite x) = .value (.finite z) ∧
      rnd F₁.toFiniteFormat S₁ O₁ .toZero (.finite (z : ℝ)) ≠
        rnd F₁.toFiniteFormat S₁ O₁ .toZero (.finite x) :=
  (no_roundsRNE_RTZ F₁ h₁ F₂ hsub).rnd_ne h₂
    (F₁.not_isUndefined _) S₂ O₂ S₁ O₁

/-- `no_roundsRAZ_RTZ` on `rnd`. -/
theorem no_rndRAZ_RTZ (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 1)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (S₂ : SpecialMap F₂.toFormat) (O₂ : OverflowMap F₂.toFormat)
    (S₁ : SpecialMap F₁.toFormat) (O₁ : OverflowMap F₁.toFormat) :
    ∃ (x : ℝ) (z : Dyadic), rnd F₂ S₂ O₂ .awayZero (.finite x) = .value (.finite z) ∧
      rnd F₁.toFiniteFormat S₁ O₁ .toZero (.finite (z : ℝ)) ≠
        rnd F₁.toFiniteFormat S₁ O₁ .toZero (.finite x) :=
  (no_roundsRAZ_RTZ F₁ h₁ F₂ hsub).rnd_ne (not_isUndefined_awayZero F₂)
    (F₁.not_isUndefined _) S₂ O₂ S₁ O₁

/-- `no_roundsRTZ_RAZ` on `rnd`. -/
theorem no_rndRTZ_RAZ (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 2)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (S₂ : SpecialMap F₂.toFormat) (O₂ : OverflowMap F₂.toFormat)
    (S₁ : SpecialMap F₁.toFormat) (O₁ : OverflowMap F₁.toFormat) :
    ∃ (x : ℝ) (z : Dyadic), rnd F₂ S₂ O₂ .toZero (.finite x) = .value (.finite z) ∧
      rnd F₁.toFiniteFormat S₁ O₁ .awayZero (.finite (z : ℝ)) ≠
        rnd F₁.toFiniteFormat S₁ O₁ .awayZero (.finite x) :=
  (no_roundsRTZ_RAZ F₁ h₁ F₂ hsub).rnd_ne (not_isUndefined_toZero F₂)
    (F₁.not_isUndefined _) S₂ O₂ S₁ O₁

/-- `no_roundsRNE_RAZ` on `rnd`. -/
theorem no_rndRNE_RAZ (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 2)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (h₂ : ¬ F₂.IsUndefined (.nearest .toEven))
    (S₂ : SpecialMap F₂.toFormat) (O₂ : OverflowMap F₂.toFormat)
    (S₁ : SpecialMap F₁.toFormat) (O₁ : OverflowMap F₁.toFormat) :
    ∃ (x : ℝ) (z : Dyadic), rnd F₂ S₂ O₂ (.nearest .toEven) (.finite x) = .value (.finite z) ∧
      rnd F₁.toFiniteFormat S₁ O₁ .awayZero (.finite (z : ℝ)) ≠
        rnd F₁.toFiniteFormat S₁ O₁ .awayZero (.finite x) :=
  (no_roundsRNE_RAZ F₁ h₁ F₂ hsub).rnd_ne h₂
    (F₁.not_isUndefined _) S₂ O₂ S₁ O₁

/-- `no_roundsRAZ_RTO` on `rnd`. -/
theorem no_rndRAZ_RTO (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 2)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (S₂ : SpecialMap F₂.toFormat) (O₂ : OverflowMap F₂.toFormat)
    (S₁ : SpecialMap F₁.toFormat) (O₁ : OverflowMap F₁.toFormat) :
    ∃ (x : ℝ) (z : Dyadic), rnd F₂ S₂ O₂ .awayZero (.finite x) = .value (.finite z) ∧
      rnd F₁.toFiniteFormat S₁ O₁ .toOdd (.finite (z : ℝ)) ≠
        rnd F₁.toFiniteFormat S₁ O₁ .toOdd (.finite x) :=
  (no_roundsRAZ_RTO F₁ h₁ F₂ hsub).rnd_ne (not_isUndefined_awayZero F₂)
    (F₁.not_isUndefined _) S₂ O₂ S₁ O₁

/-- `no_roundsRNE_RTO` on `rnd`. -/
theorem no_rndRNE_RTO (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 2)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (h₂ : ¬ F₂.IsUndefined (.nearest .toEven))
    (S₂ : SpecialMap F₂.toFormat) (O₂ : OverflowMap F₂.toFormat)
    (S₁ : SpecialMap F₁.toFormat) (O₁ : OverflowMap F₁.toFormat) :
    ∃ (x : ℝ) (z : Dyadic), rnd F₂ S₂ O₂ (.nearest .toEven) (.finite x) = .value (.finite z) ∧
      rnd F₁.toFiniteFormat S₁ O₁ .toOdd (.finite (z : ℝ)) ≠
        rnd F₁.toFiniteFormat S₁ O₁ .toOdd (.finite x) :=
  (no_roundsRNE_RTO F₁ h₁ F₂ hsub).rnd_ne h₂
    (F₁.not_isUndefined _) S₂ O₂ S₁ O₁

/-- `no_roundsRTZ_RTO` on `rnd`. -/
theorem no_rndRTZ_RTO (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 3)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (S₂ : SpecialMap F₂.toFormat) (O₂ : OverflowMap F₂.toFormat)
    (S₁ : SpecialMap F₁.toFormat) (O₁ : OverflowMap F₁.toFormat) :
    ∃ (x : ℝ) (z : Dyadic), rnd F₂ S₂ O₂ .toZero (.finite x) = .value (.finite z) ∧
      rnd F₁.toFiniteFormat S₁ O₁ .toOdd (.finite (z : ℝ)) ≠
        rnd F₁.toFiniteFormat S₁ O₁ .toOdd (.finite x) :=
  (no_roundsRTZ_RTO F₁ h₁ F₂ hsub).rnd_ne (not_isUndefined_toZero F₂)
    (F₁.not_isUndefined _) S₂ O₂ S₁ O₁

/-- `no_roundsRTZ_RNE` on `rnd`. -/
theorem no_rndRTZ_RNE (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 1)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (S₂ : SpecialMap F₂.toFormat) (O₂ : OverflowMap F₂.toFormat)
    (S₁ : SpecialMap F₁.toFormat) (O₁ : OverflowMap F₁.toFormat) :
    ∃ (x : ℝ) (z : Dyadic), rnd F₂ S₂ O₂ .toZero (.finite x) = .value (.finite z) ∧
      rnd F₁.toFiniteFormat S₁ O₁ (.nearest .toEven) (.finite (z : ℝ)) ≠
        rnd F₁.toFiniteFormat S₁ O₁ (.nearest .toEven) (.finite x) :=
  (no_roundsRTZ_RNE F₁ h₁ F₂ hsub).rnd_ne (not_isUndefined_toZero F₂)
    (F₁.not_isUndefined _) S₂ O₂ S₁ O₁

/-- `no_roundsRAZ_RNE` on `rnd`. -/
theorem no_rndRAZ_RNE (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 2)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (S₂ : SpecialMap F₂.toFormat) (O₂ : OverflowMap F₂.toFormat)
    (S₁ : SpecialMap F₁.toFormat) (O₁ : OverflowMap F₁.toFormat) :
    ∃ (x : ℝ) (z : Dyadic), rnd F₂ S₂ O₂ .awayZero (.finite x) = .value (.finite z) ∧
      rnd F₁.toFiniteFormat S₁ O₁ (.nearest .toEven) (.finite (z : ℝ)) ≠
        rnd F₁.toFiniteFormat S₁ O₁ (.nearest .toEven) (.finite x) :=
  (no_roundsRAZ_RNE F₁ h₁ F₂ hsub).rnd_ne (not_isUndefined_awayZero F₂)
    (F₁.not_isUndefined _) S₂ O₂ S₁ O₁

/-- `no_roundsRNE_RNE` on `rnd`. -/
theorem no_rndRNE_RNE (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 1)
    (F₂ : FiniteFormat) (hsub : (F₁.toFiniteFormat.extend 1).toFormat ⊆ F₂.toFormat)
    (h₂ : ¬ F₂.IsUndefined (.nearest .toEven))
    (S₂ : SpecialMap F₂.toFormat) (O₂ : OverflowMap F₂.toFormat)
    (S₁ : SpecialMap F₁.toFormat) (O₁ : OverflowMap F₁.toFormat) :
    ∃ (x : ℝ) (z : Dyadic), rnd F₂ S₂ O₂ (.nearest .toEven) (.finite x) = .value (.finite z) ∧
      rnd F₁.toFiniteFormat S₁ O₁ (.nearest .toEven) (.finite (z : ℝ)) ≠
        rnd F₁.toFiniteFormat S₁ O₁ (.nearest .toEven) (.finite x) :=
  (no_roundsRNE_RNE F₁ h₁ F₂ hsub).rnd_ne h₂
    (F₁.not_isUndefined _) S₂ O₂ S₁ O₁

end Cex

end Mpfx
