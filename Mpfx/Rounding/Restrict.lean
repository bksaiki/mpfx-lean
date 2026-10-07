import Mpfx.Rounding.Op

/-!
# Restricting and lifting the unbounded rounding

Shared machinery for the overflow-aware theorems: per-mode *restrict*
(`unbounded spec + in-bound ⟹ bounded spec`) and *lift* (`bounded spec +
in-bound unbounded rounding ⟹ unbounded spec`) lemmas. -/

namespace Mpfx

/-! ## Restrict / lift for `.toZero` -/

/-- **Restrict** (`.toZero`): an in-bound unbounded rounding is also the
bounded rounding (competitors only shrink). -/
theorem RoundsFinite.toZero_restrict {F : FiniteFormat} {x : ℝ}
    {y : Dyadic} (h : RoundsFinite F.unbounded .toZero x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F .toZero x y := by
  obtain ⟨hmem, hbnd, hsign, hmax⟩ := h
  exact ⟨mem_of_mem_unbounded_of_boundOK hmem hb, hbnd, hsign,
    fun v hv => hmax v (mem_unbounded_of_mem hv)⟩

/-- **Lift** (`.toZero`): if `w` is the bounded rounding of `x` and the
unbounded rounding `y` of `x` happens to be in-bound, then `w` is also the
unbounded rounding (any unbounded competitor is dominated by `y`, which is
itself a bounded competitor). -/
theorem RoundsFinite.toZero_lift {F : FiniteFormat} {x : ℝ}
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
bounded rounding (competitors only shrink). -/
theorem RoundsFinite.awayZero_restrict {F : FiniteFormat} {x : ℝ}
    {y : Dyadic} (h : RoundsFinite F.unbounded .awayZero x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F .awayZero x y := by
  obtain ⟨hmem, hbnd, hsign, hmin⟩ := h
  exact ⟨mem_of_mem_unbounded_of_boundOK hmem hb, hbnd, hsign,
    fun v hv => hmin v (mem_unbounded_of_mem hv)⟩

/-- **Lift** (`.awayZero`): if `w` is the bounded rounding of `x` and the
unbounded rounding `y` of `x` happens to be in-bound, then `w` is also the
unbounded rounding (any unbounded competitor dominates `y`, which is itself
a bounded competitor). -/
theorem RoundsFinite.awayZero_lift {F : FiniteFormat} {x : ℝ}
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
that lies in `F` is faithful in `F` (competitors only shrink). -/
private theorem IsFaithfulRound.restrict {F : FiniteFormat} {x : ℝ} {y : Dyadic}
    (h : IsFaithfulRound F.unbounded x y) (hb : Format.boundOK F.b y) :
    IsFaithfulRound F x y := by
  rcases h with ⟨hmem, hle, hmax⟩ | ⟨hmem, hge, hmin⟩
  · exact Or.inl ⟨mem_of_mem_unbounded_of_boundOK hmem hb, hle,
      fun v hv => hmax v (mem_unbounded_of_mem hv)⟩
  · exact Or.inr ⟨mem_of_mem_unbounded_of_boundOK hmem hb, hge,
      fun v hv => hmin v (mem_unbounded_of_mem hv)⟩

/-- **Lift** for `IsFaithfulRound`: a faithful rounding `w` of `x` in `F` is
faithful in `F.unbounded`, provided *some* in-bound `y` is faithful in
`F.unbounded` (no-overflow witness). Key step: the directed unbounded
rounding on `w`'s side is squeezed between `w` and `y` (or equals `y`), hence
in-bound, hence dominated by `w`'s maximality in `F`. -/
private theorem IsFaithfulRound.unbounded_lift {F : FiniteFormat} {x : ℝ}
    {w y : Dyadic} (hw : IsFaithfulRound F x w)
    (hy : IsFaithfulRound F.unbounded x y) (hb : Format.boundOK F.b y) :
    IsFaithfulRound F.unbounded x w := by
  rcases hw with ⟨hwmem, hw_le, hw_max⟩ | ⟨hwmem, hw_ge, hw_min⟩
  · -- RD side: w = max {v ∈ F : v ≤ x}. Show it is also the unbounded max.
    left
    refine ⟨mem_unbounded_of_mem hwmem, hw_le, ?_⟩
    intro c hc hc_le
    -- The unbounded RD rounding `g` of `x`.
    obtain ⟨hgmem, hg_le, hg_max⟩ :=
      rndUnbounded_satisfies F .toNegative x (not_isUndefined_toNegative F)
    set g := rndUnbounded F .toNegative x (not_isUndefined_toNegative F)
    have hc_g : (c : ℝ) ≤ (g : ℝ) := hg_max c hc hc_le
    have hw_g : (w : ℝ) ≤ (g : ℝ) := hg_max w (mem_unbounded_of_mem hwmem) hw_le
    -- `g` is in-bound: either `g = y` (y on the RD side) or `w ≤ g ≤ x ≤ y`.
    have hg_bnd : Format.boundOK F.b g := by
      rcases hy with ⟨hymem, hy_le, hy_max⟩ | ⟨hymem, hy_ge, _⟩
      · have h1 : (g : ℝ) ≤ (y : ℝ) := hy_max g hgmem hg_le
        exact boundOK_of_between hwmem.2.2 hb hw_g h1
      · exact boundOK_of_between hwmem.2.2 hb hw_g (le_trans hg_le hy_ge)
    -- So `g ∈ F`, hence `g ≤ w` by `w`'s maximality in `F`.
    have hg_w : (g : ℝ) ≤ (w : ℝ) :=
      hw_max g (mem_of_mem_unbounded_of_boundOK hgmem hg_bnd) hg_le
    exact le_trans hc_g hg_w
  · -- RU side: symmetric, with the unbounded RU rounding.
    right
    refine ⟨mem_unbounded_of_mem hwmem, hw_ge, ?_⟩
    intro c hc hc_ge
    obtain ⟨humem, hu_ge, hu_min⟩ :=
      rndUnbounded_satisfies F .toPositive x (not_isUndefined_toPositive F)
    set u := rndUnbounded F .toPositive x (not_isUndefined_toPositive F)
    have hu_c : (u : ℝ) ≤ (c : ℝ) := hu_min c hc hc_ge
    have hu_w : (u : ℝ) ≤ (w : ℝ) := hu_min w (mem_unbounded_of_mem hwmem) hw_ge
    have hu_bnd : Format.boundOK F.b u := by
      rcases hy with ⟨hymem, hy_le, _⟩ | ⟨hymem, hy_ge, hy_min⟩
      · exact boundOK_of_between hb hwmem.2.2 (le_trans hy_le hu_ge) hu_w
      · have h1 : (y : ℝ) ≤ (u : ℝ) := hy_min u humem hu_ge
        exact boundOK_of_between hb hwmem.2.2 h1 hu_w
    have hw_u : (w : ℝ) ≤ (u : ℝ) :=
      hw_min u (mem_of_mem_unbounded_of_boundOK humem hu_bnd) hu_ge
    exact le_trans hw_u hu_c

/-! ## Restrict / lift for `.toOdd` -/

/-- **Restrict** (`.toOdd`): an in-bound unbounded RTO rounding is also the
bounded RTO rounding. -/
theorem RoundsFinite.toOdd_restrict {F : FiniteFormat} {x : ℝ}
    {y : Dyadic} (h : RoundsFinite F.unbounded .toOdd x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F .toOdd x y := by
  obtain ⟨hmem, hfaithful, hparity⟩ := h
  exact ⟨mem_of_mem_unbounded_of_boundOK hmem hb,
    IsFaithfulRound.restrict hfaithful hb,
    fun hne => parity_witness_congr (F := F.unbounded) (G := F) rfl rfl (hparity hne)⟩

/-- **Lift** (`.toOdd`): if `w` is the bounded RTO rounding of `x` and the
unbounded RTO rounding `y` of `x` happens to be in-bound, then `w` is also
the unbounded RTO rounding. -/
theorem RoundsFinite.toOdd_lift {F : FiniteFormat} {x : ℝ}
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
  rcases hwf with wRD | wRU <;> rcases hcf with cRD | cRU
  · exact absurd (RoundsFinite.unique_toNegative cRD wRD) hc_ne_w
  · rcases hyf with yRD | yRU
    · exact RoundsFinite.unique_toNegative yRD wRD
    · exact absurd (RoundsFinite.unique_toPositive cRU yRU) hc_ne_y
  · rcases hyf with yRD | yRU
    · exact absurd (RoundsFinite.unique_toNegative cRD yRD) hc_ne_y
    · exact RoundsFinite.unique_toPositive yRU wRU
  · exact absurd (RoundsFinite.unique_toPositive cRU wRU) hc_ne_w

/-! ## Restrict / lift for `.nearest` -/

/-- A bounded-faithful competitor `c` is dominated by the unbounded nearest
rounding `y` in distance; and a *tie* upgrades `c` to an unbounded-faithful
witness (it must coincide with the directed unbounded rounding on its own
side). -/
private theorem nearest_close_upgrade {F : FiniteFormat} {x : ℝ} {y c : Dyadic}
    (hy_close : ∀ v : Dyadic, v ∈ F.unbounded → IsFaithfulRound F.unbounded x v →
      |x - (y : ℝ)| ≤ |x - (v : ℝ)|)
    (hc : c ∈ F) (hc_faithful : IsFaithfulRound F x c) :
    |x - (y : ℝ)| ≤ |x - (c : ℝ)| ∧
      (|x - (y : ℝ)| = |x - (c : ℝ)| → IsFaithfulRound F.unbounded x c) := by
  rcases hc_faithful with ⟨hc_mem, hc_le, hc_max⟩ | ⟨hc_mem, hc_ge, hc_min⟩
  · -- RD side: squeeze against the unbounded RD rounding `g`.
    obtain ⟨hg_mem, hg_le, hg_max⟩ :=
      rndUnbounded_satisfies F .toNegative x (not_isUndefined_toNegative F)
    set g := rndUnbounded F .toNegative x (not_isUndefined_toNegative F) with hg_def
    have hg_faithful : IsFaithfulRound F.unbounded x g := Or.inl ⟨hg_mem, hg_le, hg_max⟩
    have h1 : |x - (y : ℝ)| ≤ |x - (g : ℝ)| := hy_close g hg_mem hg_faithful
    have hcg : (c : ℝ) ≤ (g : ℝ) := hg_max c (mem_unbounded_of_mem hc) hc_le
    have h2 : |x - (g : ℝ)| ≤ |x - (c : ℝ)| := by
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
    refine ⟨le_trans h1 h2, fun heq => ?_⟩
    have h3 : |x - (g : ℝ)| = |x - (c : ℝ)| := le_antisymm h2 (heq ▸ h1)
    have hgc_eq : (g : ℝ) = (c : ℝ) := by
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h3
      linarith
    rw [(Dyadic.coe_real_inj g c).mp hgc_eq] at hg_faithful
    exact hg_faithful
  · -- RU side: squeeze against the unbounded RU rounding `u`.
    obtain ⟨hu_mem, hu_ge, hu_min⟩ :=
      rndUnbounded_satisfies F .toPositive x (not_isUndefined_toPositive F)
    set u := rndUnbounded F .toPositive x (not_isUndefined_toPositive F) with hu_def
    have hu_faithful : IsFaithfulRound F.unbounded x u := Or.inr ⟨hu_mem, hu_ge, hu_min⟩
    have h1 : |x - (y : ℝ)| ≤ |x - (u : ℝ)| := hy_close u hu_mem hu_faithful
    have huc : (u : ℝ) ≤ (c : ℝ) := hu_min c (mem_unbounded_of_mem hc) hc_ge
    have h2 : |x - (u : ℝ)| ≤ |x - (c : ℝ)| := by
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
    refine ⟨le_trans h1 h2, fun heq => ?_⟩
    have h3 : |x - (u : ℝ)| = |x - (c : ℝ)| := le_antisymm h2 (heq ▸ h1)
    have huc_eq : (u : ℝ) = (c : ℝ) := by
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at h3
      linarith
    rw [(Dyadic.coe_real_inj u c).mp huc_eq] at hu_faithful
    exact hu_faithful

/-- **Restrict** (`.nearest tb`): an in-bound unbounded RN rounding is also
the bounded RN rounding. -/
theorem RoundsFinite.nearest_restrict {F : FiniteFormat} {tb : TieBreak}
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
theorem RoundsFinite.nearest_lift {F : FiniteFormat} {tb : TieBreak}
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

end Mpfx
