import Mpfx.Rounding.Op

/-!
# Restricting and lifting the unbounded rounding

Shared machinery for the overflow-aware theorems: *restrict* (`unbounded spec +
in-bound ⟹ bounded spec`) and *lift* (`bounded spec + in-bound unbounded
rounding ⟹ unbounded spec`), per mode and for every mode at once
(`RoundsFinite.restrict`, `RoundsFinite.lift`). -/

namespace Mpfx

/-! ## Restrict / lift for the directed modes -/

/-- **Restrict** (`.toNegative`): the bounded format has fewer candidates. -/
private theorem RoundsFinite.toNegative_restrict {F : FiniteFormat} {x : ℝ}
    {y : Dyadic} (h : RoundsFinite F.unbounded .toNegative x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F .toNegative x y :=
  ⟨mem_of_mem_unbounded_of_boundOK h.1 hb, h.2.1, fun v hv => h.2.2 v (mem_unbounded_of_mem hv)⟩

/-- **Lift** (`.toNegative`): an unbounded candidate is below `y`, itself a
bounded candidate. -/
private theorem RoundsFinite.toNegative_lift {F : FiniteFormat} {x : ℝ}
    {w y : Dyadic} (hw : RoundsFinite F .toNegative x w)
    (hy : RoundsFinite F.unbounded .toNegative x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F.unbounded .toNegative x w :=
  ⟨mem_unbounded_of_mem hw.1, hw.2.1, fun v hv hvx =>
    (hy.2.2 v hv hvx).trans (hw.2.2 y (mem_of_mem_unbounded_of_boundOK hy.1 hb) hy.2.1)⟩

/-- **Restrict** (`.toPositive`): the bounded format has fewer candidates. -/
private theorem RoundsFinite.toPositive_restrict {F : FiniteFormat} {x : ℝ}
    {y : Dyadic} (h : RoundsFinite F.unbounded .toPositive x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F .toPositive x y :=
  ⟨mem_of_mem_unbounded_of_boundOK h.1 hb, h.2.1, fun v hv => h.2.2 v (mem_unbounded_of_mem hv)⟩

/-- **Lift** (`.toPositive`): an unbounded candidate is above `y`, itself a
bounded candidate. -/
private theorem RoundsFinite.toPositive_lift {F : FiniteFormat} {x : ℝ}
    {w y : Dyadic} (hw : RoundsFinite F .toPositive x w)
    (hy : RoundsFinite F.unbounded .toPositive x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F.unbounded .toPositive x w :=
  ⟨mem_unbounded_of_mem hw.1, hw.2.1, fun v hv hxv =>
    (hw.2.2 y (mem_of_mem_unbounded_of_boundOK hy.1 hb) hy.2.1).trans (hy.2.2 v hv hxv)⟩

/-! ## Restrict / lift for `.toZero` -/

/-- **Restrict** (`.toZero`): an in-bound unbounded rounding is also the
bounded rounding (the bounded format has fewer candidates). -/
private theorem RoundsFinite.toZero_restrict {F : FiniteFormat} {x : ℝ}
    {y : Dyadic} (h : RoundsFinite F.unbounded .toZero x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F .toZero x y := by
  obtain ⟨hmem, hbnd, hsign, hmax⟩ := h
  exact ⟨mem_of_mem_unbounded_of_boundOK hmem hb, hbnd, hsign,
    fun v hv => hmax v (mem_unbounded_of_mem hv)⟩

/-- **Lift** (`.toZero`): if `w` is the bounded rounding of `x` and the
unbounded rounding `y` of `x` happens to be in-bound, then `w` is also the
unbounded rounding (any unbounded candidate is dominated by `y`, which is
itself a bounded candidate). -/
private theorem RoundsFinite.toZero_lift {F : FiniteFormat} {x : ℝ}
    {w y : Dyadic} (hw : RoundsFinite F .toZero x w)
    (hy : RoundsFinite F.unbounded .toZero x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F.unbounded .toZero x w := by
  obtain ⟨hwmem, hwbnd, hwsign, hwmax⟩ := hw
  obtain ⟨hymem, hybnd, hysign, hymax⟩ := hy
  refine ⟨mem_unbounded_of_mem hwmem, hwbnd, hwsign, ?_⟩
  intro v hv hvbnd hvsign
  have h1 : |(v : ℝ)| ≤ |(y : ℝ)| := hymax v hv hvbnd hvsign
  have h2 : |(y : ℝ)| ≤ |(w : ℝ)| :=
    hwmax y (mem_of_mem_unbounded_of_boundOK hymem hb) hybnd hysign
  exact le_trans h1 h2

/-! ## Restrict / lift for `.awayZero` -/

/-- **Restrict** (`.awayZero`): an in-bound unbounded rounding is also the
bounded rounding (the bounded format has fewer candidates). -/
private theorem RoundsFinite.awayZero_restrict {F : FiniteFormat} {x : ℝ}
    {y : Dyadic} (h : RoundsFinite F.unbounded .awayZero x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F .awayZero x y := by
  obtain ⟨hmem, hbnd, hsign, hmin⟩ := h
  exact ⟨mem_of_mem_unbounded_of_boundOK hmem hb, hbnd, hsign,
    fun v hv => hmin v (mem_unbounded_of_mem hv)⟩

/-- **Lift** (`.awayZero`): if `w` is the bounded rounding of `x` and the
unbounded rounding `y` of `x` happens to be in-bound, then `w` is also the
unbounded rounding (any unbounded candidate dominates `y`, which is itself
a bounded candidate). -/
private theorem RoundsFinite.awayZero_lift {F : FiniteFormat} {x : ℝ}
    {w y : Dyadic} (hw : RoundsFinite F .awayZero x w)
    (hy : RoundsFinite F.unbounded .awayZero x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F.unbounded .awayZero x w := by
  obtain ⟨hwmem, hwbnd, hwsign, hwmin⟩ := hw
  obtain ⟨hymem, hybnd, hysign, hymin⟩ := hy
  refine ⟨mem_unbounded_of_mem hwmem, hwbnd, hwsign, ?_⟩
  intro v hv hvbnd hvsign
  have h1 : |(w : ℝ)| ≤ |(y : ℝ)| :=
    hwmin y (mem_of_mem_unbounded_of_boundOK hymem hb) hybnd hysign
  have h2 : |(y : ℝ)| ≤ |(v : ℝ)| := hymin v hv hvbnd hvsign
  exact le_trans h1 h2


/-! ## Faithful-round restrict / lift -/


/-- **Restrict** for `IsFaithfulRound`: a faithful rounding in `F.unbounded`
that lies in `F` is faithful in `F` (the bounded format has fewer candidates). -/
private theorem IsFaithfulRound.restrict {F : FiniteFormat} {x : ℝ} {y : Dyadic}
    (h : IsFaithfulRound F.unbounded x y) (hb : Format.boundOK F.b y) :
    IsFaithfulRound F x y :=
  h.of_subset F.subset_unbounded
    (mem_of_mem_unbounded_of_boundOK (h.elim (·.1) (·.1)) hb)

/-- **Lift** for `IsFaithfulRound`: a faithful rounding `w` of `x` in `F` is
faithful in `F.unbounded`, provided *some* in-bound `y` is faithful in
`F.unbounded` (no-overflow witness). The unbounded neighbour on `w`'s side lies
between `w` and `y`, so it is in bound, and the directed lift applies. -/
private theorem IsFaithfulRound.unbounded_lift {F : FiniteFormat} {x : ℝ}
    {w y : Dyadic} (hw : IsFaithfulRound F x w)
    (hy : IsFaithfulRound F.unbounded x y) (hb : Format.boundOK F.b y) :
    IsFaithfulRound F.unbounded x w := by
  have hd := RoundsFinite.toNegative_floor F x
  have hu := RoundsFinite.toPositive_ceil F x
  have hwF : w ∈ F := hw.elim (·.1) (·.1)
  rcases hw with hw | hw
  · refine Or.inl (RoundsFinite.toNegative_lift hw hd ?_)
    rcases hy.eq_or_eq hd hu with rfl | rfl
    · exact hb
    · exact boundOK_of_between hwF.2.2 hb (hd.2.2 w (mem_unbounded_of_mem hwF) hw.2.1)
        (hd.2.1.trans hu.2.1)
  · refine Or.inr (RoundsFinite.toPositive_lift hw hu ?_)
    rcases hy.eq_or_eq hd hu with rfl | rfl
    · exact boundOK_of_between hb hwF.2.2 (hd.2.1.trans hu.2.1)
        (hu.2.2 w (mem_unbounded_of_mem hwF) hw.2.1)
    · exact hb

/-! ## Restrict / lift for `.toOdd` -/

/-- **Restrict** (`.toOdd`): an in-bound unbounded RTO rounding is also the
bounded RTO rounding. -/
private theorem RoundsFinite.toOdd_restrict {F : FiniteFormat} {x : ℝ}
    {y : Dyadic} (h : RoundsFinite F.unbounded .toOdd x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F .toOdd x y := by
  obtain ⟨hmem, hfaithful, hparity⟩ := h
  exact ⟨mem_of_mem_unbounded_of_boundOK hmem hb,
    IsFaithfulRound.restrict hfaithful hb,
    fun hne => parity_witness_congr (F := F.unbounded) (G := F) rfl rfl (hparity hne)⟩

/-- **Lift** (`.toOdd`): if `w` is the bounded RTO rounding of `x` and the
unbounded RTO rounding `y` of `x` happens to be in-bound, then `w` is also
the unbounded RTO rounding. -/
private theorem RoundsFinite.toOdd_lift {F : FiniteFormat} {x : ℝ}
    {w y : Dyadic} (hw : RoundsFinite F .toOdd x w)
    (hy : RoundsFinite F.unbounded .toOdd x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F.unbounded .toOdd x w := by
  obtain ⟨hwmem, hwfaithful, hwparity⟩ := hw
  exact ⟨mem_unbounded_of_mem hwmem,
    IsFaithfulRound.unbounded_lift hwfaithful hy.2.1 hb,
    fun hne => parity_witness_congr (F := F) (G := F.unbounded) rfl rfl (hwparity hne)⟩


/-- There are at most two faithful values, one per side, so a third witness
`c ∉ {w, y}` forces `y = w`. -/
private theorem faithful_eq_of_third {F : FiniteFormat} {x : ℝ} {w y c : Dyadic}
    (hwf : IsFaithfulRound F.unbounded x w)
    (hyf : IsFaithfulRound F.unbounded x y)
    (hcf : IsFaithfulRound F.unbounded x c)
    (hc_ne_w : c ≠ w) (hc_ne_y : c ≠ y) : y = w := by
  have hd := RoundsFinite.toNegative_floor F x
  have hu := RoundsFinite.toPositive_ceil F x
  rcases hwf.eq_or_eq hd hu with hw | hw <;> rcases hyf.eq_or_eq hd hu with hy | hy <;>
    rcases hcf.eq_or_eq hd hu with hc | hc <;>
    first
    | exact hy.trans hw.symm
    | exact absurd (hc.trans hw.symm) hc_ne_w
    | exact absurd (hc.trans hy.symm) hc_ne_y

/-! ## Restrict / lift for `.nearest` -/

/-- A bounded-faithful candidate `c` is dominated by the unbounded nearest
rounding `y` in distance; and a *tie* upgrades `c` to an unbounded-faithful
witness (it must coincide with the directed unbounded rounding on its own
side). -/
private theorem nearest_close_upgrade {F : FiniteFormat} {x : ℝ} {y c : Dyadic}
    (hy_close : ∀ v : Dyadic, v ∈ F.unbounded → IsFaithfulRound F.unbounded x v →
      |x - (y : ℝ)| ≤ |x - (v : ℝ)|)
    (hc : c ∈ F) (hc_faithful : IsFaithfulRound F x c) :
    |x - (y : ℝ)| ≤ |x - (c : ℝ)| ∧
      (|x - (y : ℝ)| = |x - (c : ℝ)| → IsFaithfulRound F.unbounded x c) := by
  -- The unbounded neighbour `g` on `c`'s side lies between `c` and `x`.
  obtain ⟨g, hg, hgc, hgc_eq⟩ : ∃ g : Dyadic, IsFaithfulRound F.unbounded x g ∧
      |x - (g : ℝ)| ≤ |x - (c : ℝ)| ∧ (|x - (g : ℝ)| = |x - (c : ℝ)| → g = c) := by
    rcases hc_faithful with ⟨-, hcx, -⟩ | ⟨-, hxc, -⟩
    · have hd := RoundsFinite.toNegative_floor F x
      have hcd := hd.2.2 c (mem_unbounded_of_mem hc) hcx
      have e₁ := abs_of_nonneg (sub_nonneg.mpr hd.2.1)
      have e₂ := abs_of_nonneg (sub_nonneg.mpr hcx)
      exact ⟨_, Or.inl hd, by rw [e₁, e₂]; linarith,
        fun h => Dyadic.ext_real (by rw [e₁, e₂] at h; linarith)⟩
    · have hu := RoundsFinite.toPositive_ceil F x
      have huc := hu.2.2 c (mem_unbounded_of_mem hc) hxc
      have e₁ := abs_of_nonpos (sub_nonpos.mpr hu.2.1)
      have e₂ := abs_of_nonpos (sub_nonpos.mpr hxc)
      exact ⟨_, Or.inr hu, by rw [e₁, e₂]; linarith,
        fun h => Dyadic.ext_real (by rw [e₁, e₂] at h; linarith)⟩
  have h₁ := hy_close g (hg.elim (·.1) (·.1)) hg
  exact ⟨h₁.trans hgc, fun h => hgc_eq (le_antisymm hgc (h.symm.le.trans h₁)) ▸ hg⟩

/-- **Restrict** (`.nearest tb`): an in-bound unbounded RN rounding is also
the bounded RN rounding. -/
private theorem RoundsFinite.nearest_restrict {F : FiniteFormat} {tb : TieBreak}
    {x : ℝ} {y : Dyadic} (h : RoundsFinite F.unbounded (.nearest tb) x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F (.nearest tb) x y := by
  cases tb with
  | toEven =>
    obtain ⟨hmem, hfaithful, hclose, htie⟩ := h
    refine ⟨mem_of_mem_unbounded_of_boundOK hmem hb,
      IsFaithfulRound.restrict hfaithful hb, ?_, ?_⟩
    · intro c hcF hc_faithful
      exact (nearest_close_upgrade hclose hcF hc_faithful).1
    · rintro ⟨c, hcF, hc_faithful, hc_ne, hc_tie⟩
      have hc_up := (nearest_close_upgrade hclose hcF hc_faithful).2 hc_tie
      exact parity_witness_even_congr (F := F.unbounded) (G := F) rfl rfl
        (htie ⟨c, mem_unbounded_of_mem hcF, hc_up, hc_ne, hc_tie⟩)
  | awayZero =>
    obtain ⟨hmem, hfaithful, hclose, htie⟩ := h
    refine ⟨mem_of_mem_unbounded_of_boundOK hmem hb,
      IsFaithfulRound.restrict hfaithful hb, ?_, ?_⟩
    · intro c hcF hc_faithful
      exact (nearest_close_upgrade hclose hcF hc_faithful).1
    · intro c hcF hc_faithful hc_ne hc_tie
      have hc_up := (nearest_close_upgrade hclose hcF hc_faithful).2 hc_tie
      exact htie c (mem_unbounded_of_mem hcF) hc_up hc_ne hc_tie

/-- **Lift** (`.nearest tb`): if `w` is the bounded RN rounding of `x` and
the unbounded RN rounding `y` of `x` happens to be in-bound, then `w` is also
the unbounded RN rounding. -/
private theorem RoundsFinite.nearest_lift {F : FiniteFormat} {tb : TieBreak}
    {x : ℝ} {w y : Dyadic} (hw : RoundsFinite F (.nearest tb) x w)
    (hy : RoundsFinite F.unbounded (.nearest tb) x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F.unbounded (.nearest tb) x w := by
  cases tb with
  | toEven =>
    obtain ⟨hwmem, hwfaithful, hwclose, hwtie⟩ := hw
    obtain ⟨hymem, hyfaithful, hyclose, hytie⟩ := hy
    have hyF : y ∈ F := mem_of_mem_unbounded_of_boundOK hymem hb
    have hwy : |x - (w : ℝ)| ≤ |x - (y : ℝ)| :=
      hwclose y hyF (IsFaithfulRound.restrict hyfaithful hb)
    have hwf_u : IsFaithfulRound F.unbounded x w :=
      IsFaithfulRound.unbounded_lift hwfaithful hyfaithful hb
    refine ⟨mem_unbounded_of_mem hwmem, hwf_u, ?_, ?_⟩
    · intro c hc hc_faithful
      exact le_trans hwy (hyclose c hc hc_faithful)
    · rintro ⟨c, hc, hc_faithful, hc_ne, hc_tie⟩
      by_cases hcb : Format.boundOK F.b c
      · exact parity_witness_even_congr (F := F) (G := F.unbounded) rfl rfl
          (hwtie ⟨c, mem_of_mem_unbounded_of_boundOK hc hcb,
            IsFaithfulRound.restrict hc_faithful hcb, hc_ne, hc_tie⟩)
      · -- `c` out of bound forces `y = w`; fire `y`'s own tie clause.
        have hc_ne_y : c ≠ y := fun h => hcb (h ▸ hb)
        have hyw : y = w := faithful_eq_of_third hwf_u hyfaithful hc_faithful hc_ne hc_ne_y
        rw [← hyw] at hc_ne hc_tie ⊢
        exact hytie ⟨c, hc, hc_faithful, hc_ne, hc_tie⟩
  | awayZero =>
    obtain ⟨hwmem, hwfaithful, hwclose, hwtie⟩ := hw
    obtain ⟨hymem, hyfaithful, hyclose, hytie⟩ := hy
    have hyF : y ∈ F := mem_of_mem_unbounded_of_boundOK hymem hb
    have hwy : |x - (w : ℝ)| ≤ |x - (y : ℝ)| :=
      hwclose y hyF (IsFaithfulRound.restrict hyfaithful hb)
    have hwf_u : IsFaithfulRound F.unbounded x w :=
      IsFaithfulRound.unbounded_lift hwfaithful hyfaithful hb
    refine ⟨mem_unbounded_of_mem hwmem, hwf_u, ?_, ?_⟩
    · intro c hc hc_faithful
      exact le_trans hwy (hyclose c hc hc_faithful)
    · intro c hc hc_faithful hc_ne hc_tie
      by_cases hcb : Format.boundOK F.b c
      · exact hwtie c (mem_of_mem_unbounded_of_boundOK hc hcb)
          (IsFaithfulRound.restrict hc_faithful hcb) hc_ne hc_tie
      · have hc_ne_y : c ≠ y := fun h => hcb (h ▸ hb)
        have hyw : y = w := faithful_eq_of_third hwf_u hyfaithful hc_faithful hc_ne hc_ne_y
        rw [← hyw] at hc_ne hc_tie ⊢
        exact hytie c hc hc_faithful hc_ne hc_tie

/-! ## Every mode -/

/-- **Restrict**: an in-bound unbounded rounding is also the bounded rounding. -/
theorem RoundsFinite.restrict {F : FiniteFormat} {rm : RoundingMode} {x : ℝ}
    {y : Dyadic} (h : RoundsFinite F.unbounded rm x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F rm x y := by
  cases rm with
  | toNegative => exact toNegative_restrict h hb
  | toPositive => exact toPositive_restrict h hb
  | toZero => exact toZero_restrict h hb
  | awayZero => exact awayZero_restrict h hb
  | toOdd => exact toOdd_restrict h hb
  | nearest _ => exact nearest_restrict h hb

/-- **Lift**: if `w` is the bounded rounding of `x` and the unbounded rounding
`y` is in bound, then `w` is also the unbounded rounding. -/
theorem RoundsFinite.lift {F : FiniteFormat} {rm : RoundingMode} {x : ℝ}
    {w y : Dyadic} (hw : RoundsFinite F rm x w)
    (hy : RoundsFinite F.unbounded rm x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F.unbounded rm x w := by
  cases rm with
  | toNegative => exact toNegative_lift hw hy hb
  | toPositive => exact toPositive_lift hw hy hb
  | toZero => exact toZero_lift hw hy hb
  | awayZero => exact awayZero_lift hw hy hb
  | toOdd => exact toOdd_lift hw hy hb
  | nearest _ => exact nearest_lift hw hy hb

end Mpfx
