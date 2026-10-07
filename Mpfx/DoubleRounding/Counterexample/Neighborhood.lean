import Mpfx.DoubleRounding.Counterexample.Basic

/-!
# Double-rounding counterexamples: anchor neighborhoods

The `AnchorNeighborhood` interface and the neighborhood-generic
counterexample cores.
-/

namespace Mpfx

namespace Cex

/-! ## The anchor-neighborhood interface

Everything the ten counterexamples use about the *inner* format `F₁` and its
interaction with an arbitrary `F₂ ⊇ F₁`, bundled as data: three consecutive
`F₁`-elements `lo2 < lo < hi` spaced by a local step `2^t` (`lo2`, `hi`
even, `hi` not odd), the `F₁`-adjacency facts, and — quantified over every
`F₂` containing `F₁` — the local-step gap bounds around the anchors and the
two midpoints. The counterexample cores are proven once against this
interface; it is instantiated per target-format shape in `Instances.lean`. -/

structure AnchorNeighborhood (F₁ : ParityFormat) where
  /-- Upper step exponent: `hi = lo + 2^t`. -/
  t : ℤ
  /-- Lower step exponent: `lo = lo2 + 2^s`. Equals `t` for arithmetic grids,
  but differs at a binade boundary (e.g. when `lo` is a power of two), so the
  two gaps are tracked separately. -/
  s : ℤ
  /-- The even lower anchor. -/
  lo2 : Dyadic
  /-- The odd middle anchor `lo2 + 2^s`. -/
  lo : Dyadic
  /-- The even upper anchor `lo + 2^t`. -/
  hi : Dyadic
  /-- The midpoint of `(lo, hi)`, as a Dyadic for the `extend 1` membership. -/
  mid : Dyadic
  lo2_pos : (0 : ℝ) < ((lo2 : Dyadic) : ℝ)
  coe_lo : ((lo : Dyadic) : ℝ) = ((lo2 : Dyadic) : ℝ) + (2 : ℝ) ^ s
  coe_hi : ((hi : Dyadic) : ℝ) = ((lo : Dyadic) : ℝ) + (2 : ℝ) ^ t
  coe_mid : ((mid : Dyadic) : ℝ) = ((lo : Dyadic) : ℝ) + (2 : ℝ) ^ (t - 1)
  mem_lo2 : lo2 ∈ F₁.toFormat
  mem_lo : lo ∈ F₁.toFormat
  mem_hi : hi ∈ F₁.toFormat
  even_lo2 : F₁.IsEven lo2
  even_hi : F₁.IsEven hi
  not_odd_hi : ¬ F₁.IsOdd hi
  /-- `F₁`-adjacency: no element strictly between `lo2` and `lo`. -/
  f1_floor_lo : ∀ v ∈ F₁.toFormat, ((v : Dyadic) : ℝ) < ((lo : Dyadic) : ℝ) →
    ((v : Dyadic) : ℝ) ≤ ((lo2 : Dyadic) : ℝ)
  f1_ceil_lo2 : ∀ v ∈ F₁.toFormat, ((lo2 : Dyadic) : ℝ) < ((v : Dyadic) : ℝ) →
    ((lo : Dyadic) : ℝ) ≤ ((v : Dyadic) : ℝ)
  /-- `F₁`-adjacency: no element strictly between `lo` and `hi`. -/
  f1_floor_hi : ∀ v ∈ F₁.toFormat, ((v : Dyadic) : ℝ) < ((hi : Dyadic) : ℝ) →
    ((v : Dyadic) : ℝ) ≤ ((lo : Dyadic) : ℝ)
  f1_ceil_hi : ∀ v ∈ F₁.toFormat, ((lo : Dyadic) : ℝ) < ((v : Dyadic) : ℝ) →
    ((hi : Dyadic) : ℝ) ≤ ((v : Dyadic) : ℝ)
  /-- The midpoint of `(lo, hi)` is representable with one extra digit. -/
  mid_mem_ext1 : mid ∈ ((F₁.toFiniteFormat.extend 1).toFormat)
  /-- `F₂`-local gap below `hi`. -/
  f2_below_hi : ∀ F₂ : FiniteFormat, F₁.toFormat ⊆ F₂.toFormat →
    ∃ K : ℤ, K ≤ t ∧ ∀ z ∈ F₂.toFormat,
      ((z : Dyadic) : ℝ) < ((hi : Dyadic) : ℝ) →
      ((z : Dyadic) : ℝ) ≤ ((hi : Dyadic) : ℝ) - (2 : ℝ) ^ K
  /-- `F₂`-local gap above `hi`. -/
  f2_above_hi : ∀ F₂ : FiniteFormat, F₁.toFormat ⊆ F₂.toFormat →
    ∃ K : ℤ, K ≤ t ∧ ∀ z ∈ F₂.toFormat,
      ((hi : Dyadic) : ℝ) < ((z : Dyadic) : ℝ) →
      ((hi : Dyadic) : ℝ) + (2 : ℝ) ^ K ≤ ((z : Dyadic) : ℝ)
  /-- `F₂`-local half-step gaps around the lower midpoint `lo2 + 2^(s−1)`. -/
  f2_mid_lo : ∀ F₂ : FiniteFormat, F₁.toFormat ⊆ F₂.toFormat →
    ∃ K : ℤ, K ≤ s ∧
      (∀ z ∈ F₂.toFormat,
        ((z : Dyadic) : ℝ) < ((lo2 : Dyadic) : ℝ) + (2 : ℝ) ^ (s - 1) →
        ((z : Dyadic) : ℝ) ≤
          ((lo2 : Dyadic) : ℝ) + (2 : ℝ) ^ (s - 1) - (2 : ℝ) ^ (K - 1)) ∧
      (∀ z ∈ F₂.toFormat,
        ((lo2 : Dyadic) : ℝ) + (2 : ℝ) ^ (s - 1) < ((z : Dyadic) : ℝ) →
        ((lo2 : Dyadic) : ℝ) + (2 : ℝ) ^ (s - 1) + (2 : ℝ) ^ (K - 1) ≤
          ((z : Dyadic) : ℝ))
  /-- `F₂`-local half-step gaps around the upper midpoint `lo + 2^(t−1)`. -/
  f2_mid_hi : ∀ F₂ : FiniteFormat, F₁.toFormat ⊆ F₂.toFormat →
    ∃ K : ℤ, K ≤ t ∧
      (∀ z ∈ F₂.toFormat,
        ((z : Dyadic) : ℝ) < ((lo : Dyadic) : ℝ) + (2 : ℝ) ^ (t - 1) →
        ((z : Dyadic) : ℝ) ≤
          ((lo : Dyadic) : ℝ) + (2 : ℝ) ^ (t - 1) - (2 : ℝ) ^ (K - 1)) ∧
      (∀ z ∈ F₂.toFormat,
        ((lo : Dyadic) : ℝ) + (2 : ℝ) ^ (t - 1) < ((z : Dyadic) : ℝ) →
        ((lo : Dyadic) : ℝ) + (2 : ℝ) ^ (t - 1) + (2 : ℝ) ^ (K - 1) ≤
          ((z : Dyadic) : ℝ))
  /-- `F₂`-local full-step gaps around the upper midpoint when it is
  `F₂`-representable. -/
  f2_mem_mid : ∀ F₂ : FiniteFormat, mid ∈ F₂.toFormat →
    ∃ K : ℤ, K ≤ t - 1 ∧
      (∀ z ∈ F₂.toFormat, ((z : Dyadic) : ℝ) < ((mid : Dyadic) : ℝ) →
        ((z : Dyadic) : ℝ) ≤ ((mid : Dyadic) : ℝ) - (2 : ℝ) ^ K) ∧
      (∀ z ∈ F₂.toFormat, ((mid : Dyadic) : ℝ) < ((z : Dyadic) : ℝ) →
        ((mid : Dyadic) : ℝ) + (2 : ℝ) ^ K ≤ ((z : Dyadic) : ℝ))

namespace AnchorNeighborhood

/-- Transport along formats that agree on `p`, `exp` and `b`: the
neighborhood only uses numeric membership and parity. -/
def transport {F G : ParityFormat} (hp : G.p = F.p) (he : G.exp = F.exp)
    (hb : G.b = F.b) (P : AnchorNeighborhood G) : AnchorNeighborhood F :=
  have hmem : ∀ {d : Dyadic}, d ∈ G.toFormat ↔ d ∈ F.toFormat :=
    Format.mem_congr hp he hb
  have hsub : ∀ F₂ : FiniteFormat, F.toFormat ⊆ F₂.toFormat → G.toFormat ⊆ F₂.toFormat :=
    fun _ h d hd => h d (hmem.mp hd)
  { t := P.t, s := P.s, lo2 := P.lo2, lo := P.lo, hi := P.hi, mid := P.mid
    lo2_pos := P.lo2_pos, coe_lo := P.coe_lo, coe_hi := P.coe_hi, coe_mid := P.coe_mid
    mem_lo2 := hmem.mp P.mem_lo2
    mem_lo := hmem.mp P.mem_lo
    mem_hi := hmem.mp P.mem_hi
    even_lo2 := P.even_lo2.congr hp he
    even_hi := P.even_hi.congr hp he
    not_odd_hi := fun h => P.not_odd_hi (h.congr hp.symm he.symm)
    f1_floor_lo := fun v hv => P.f1_floor_lo v (hmem.mpr hv)
    f1_ceil_lo2 := fun v hv => P.f1_ceil_lo2 v (hmem.mpr hv)
    f1_floor_hi := fun v hv => P.f1_floor_hi v (hmem.mpr hv)
    f1_ceil_hi := fun v hv => P.f1_ceil_hi v (hmem.mpr hv)
    mid_mem_ext1 := (Format.mem_congr (F := (G.toFiniteFormat.extend 1).toFormat)
      (G := (F.toFiniteFormat.extend 1).toFormat)
      (congrArg (· + ((1 : ℕ) : Prec)) hp)
      (congrArg (WithBot.map (· - ((1 : ℕ) : ℤ))) he) hb).mp P.mid_mem_ext1
    f2_below_hi := fun F₂ h => P.f2_below_hi F₂ (hsub F₂ h)
    f2_above_hi := fun F₂ h => P.f2_above_hi F₂ (hsub F₂ h)
    f2_mid_lo := fun F₂ h => P.f2_mid_lo F₂ (hsub F₂ h)
    f2_mid_hi := fun F₂ h => P.f2_mid_hi F₂ (hsub F₂ h)
    f2_mem_mid := P.f2_mem_mid }


variable {F₁ : ParityFormat} (P : AnchorNeighborhood F₁)

/-- `F₁`-faithful values of any `s ∈ [lo2, lo2 + 2^(s−1)]` enumerate to
`{lo2, lo}`. -/
private theorem faithful_lo {s : ℝ}
    (h_lo : ((P.lo2 : Dyadic) : ℝ) ≤ s)
    (h_hi : s ≤ ((P.lo2 : Dyadic) : ℝ) + (2 : ℝ) ^ (P.s - 1))
    {v : Dyadic} (hf : IsFaithfulRound F₁.toFiniteFormat s v) :
    ((v : Dyadic) : ℝ) = ((P.lo2 : Dyadic) : ℝ) ∨
    ((v : Dyadic) : ℝ) = ((P.lo : Dyadic) : ℝ) := by
  have h_half_pos : (0 : ℝ) < (2 : ℝ) ^ (P.s - 1) := zpow_pos (by norm_num) _
  have h_half_lt : (2 : ℝ) ^ (P.s - 1) < (2 : ℝ) ^ P.s :=
    zpow_lt_zpow_right₀ (by norm_num) (by omega)
  have h_s_lt_lo : s < ((P.lo : Dyadic) : ℝ) := by
    rw [P.coe_lo]; linarith
  rcases hf with ⟨hvF, hle, hmax⟩ | ⟨hvF, hge, hmin⟩
  · left
    have h1 : ((v : Dyadic) : ℝ) ≤ ((P.lo2 : Dyadic) : ℝ) :=
      P.f1_floor_lo v hvF (lt_of_le_of_lt hle h_s_lt_lo)
    have h2 := hmax P.lo2 P.mem_lo2 h_lo
    linarith
  · rcases le_or_gt ((v : Dyadic) : ℝ) ((P.lo2 : Dyadic) : ℝ) with h1 | h1
    · left; linarith
    · right
      have h2 := P.f1_ceil_lo2 v hvF h1
      have h3 := hmin P.lo P.mem_lo (le_of_lt h_s_lt_lo)
      linarith

/-- RNE in `F₁` at any `s ∈ [lo2, lo2 + 2^(s−1)]` admits `lo2`: strictly
nearest in the interior, even tie-winner at the midpoint. -/
private theorem rounds_RNE_lo2 {s : ℝ}
    (h_lo : ((P.lo2 : Dyadic) : ℝ) ≤ s)
    (h_hi : s ≤ ((P.lo2 : Dyadic) : ℝ) + (2 : ℝ) ^ (P.s - 1)) :
    RoundsFinite F₁.toFiniteFormat (.nearest .toEven) s P.lo2 := by
  have h_half_pos : (0 : ℝ) < (2 : ℝ) ^ (P.s - 1) := zpow_pos (by norm_num) _
  have h_two_half : (2 : ℝ) ^ P.s = 2 * (2 : ℝ) ^ (P.s - 1) := by
    have h := two_zpow_succ (P.s - 1)
    rwa [show P.s - 1 + 1 = P.s by ring] at h
  have h_s_lt_lo : s < ((P.lo : Dyadic) : ℝ) := by
    rw [P.coe_lo]; linarith
  refine ⟨P.mem_lo2, ?_, ?_, ?_⟩
  · left
    refine ⟨P.mem_lo2, h_lo, ?_⟩
    intro v hv hv_le
    exact P.f1_floor_lo v hv (lt_of_le_of_lt hv_le h_s_lt_lo)
  · intro v hv hf
    rcases P.faithful_lo h_lo h_hi hf with h | h
    · rw [h]
    · rw [h, P.coe_lo]
      have hL : |s - ((P.lo2 : Dyadic) : ℝ)| = s - ((P.lo2 : Dyadic) : ℝ) :=
        abs_of_nonneg (by linarith)
      have hR : |s - (((P.lo2 : Dyadic) : ℝ) + (2 : ℝ) ^ P.s)|
          = ((P.lo2 : Dyadic) : ℝ) + (2 : ℝ) ^ P.s - s := by
        rw [abs_sub_comm]
        exact abs_of_nonneg (by linarith)
      rw [hL, hR]
      linarith
  · rintro ⟨_, _, _, _, _⟩
    exact ⟨F₁, rfl, P.even_lo2⟩

/-- `F₁`-faithful values of any `s ∈ [lo + 2^(t−1), hi]` enumerate to
`{lo, hi}`. -/
private theorem faithful_hi {s : ℝ}
    (h_lo : ((P.lo : Dyadic) : ℝ) + (2 : ℝ) ^ (P.t - 1) ≤ s)
    (h_hi : s ≤ ((P.hi : Dyadic) : ℝ))
    {v : Dyadic} (hf : IsFaithfulRound F₁.toFiniteFormat s v) :
    ((v : Dyadic) : ℝ) = ((P.lo : Dyadic) : ℝ) ∨
    ((v : Dyadic) : ℝ) = ((P.hi : Dyadic) : ℝ) := by
  have h_half_pos : (0 : ℝ) < (2 : ℝ) ^ (P.t - 1) := zpow_pos (by norm_num) _
  have h_lo_lt_s : ((P.lo : Dyadic) : ℝ) < s := by linarith
  rcases hf with ⟨hvF, hle, hmax⟩ | ⟨hvF, hge, hmin⟩
  · rcases le_or_gt ((P.hi : Dyadic) : ℝ) ((v : Dyadic) : ℝ) with h1 | h1
    · right; linarith
    · left
      have h2 := P.f1_floor_hi v hvF h1
      have h3 := hmax P.lo P.mem_lo (le_of_lt h_lo_lt_s)
      linarith
  · right
    have h1 := P.f1_ceil_hi v hvF (lt_of_lt_of_le h_lo_lt_s hge)
    have h2 := hmin P.hi P.mem_hi h_hi
    linarith

/-- RNE in `F₁` at any `s ∈ [lo + 2^(t−1), hi]` admits `hi`: strictly
nearest in the interior, even tie-winner at the midpoint. -/
private theorem rounds_RNE_hi {s : ℝ}
    (h_lo : ((P.lo : Dyadic) : ℝ) + (2 : ℝ) ^ (P.t - 1) ≤ s)
    (h_hi : s ≤ ((P.hi : Dyadic) : ℝ)) :
    RoundsFinite F₁.toFiniteFormat (.nearest .toEven) s P.hi := by
  have h_half_pos : (0 : ℝ) < (2 : ℝ) ^ (P.t - 1) := zpow_pos (by norm_num) _
  have h_two_half : (2 : ℝ) ^ P.t = 2 * (2 : ℝ) ^ (P.t - 1) := by
    have h := two_zpow_succ (P.t - 1)
    rwa [show P.t - 1 + 1 = P.t by ring] at h
  have h_hi_lo : ((P.hi : Dyadic) : ℝ) = ((P.lo : Dyadic) : ℝ) + (2 : ℝ) ^ P.t :=
    P.coe_hi
  have h_lo_lt_s : ((P.lo : Dyadic) : ℝ) < s := by linarith
  refine ⟨P.mem_hi, ?_, ?_, ?_⟩
  · right
    refine ⟨P.mem_hi, h_hi, ?_⟩
    intro v hv hv_ge
    exact P.f1_ceil_hi v hv (lt_of_lt_of_le h_lo_lt_s hv_ge)
  · intro v hv hf
    rcases P.faithful_hi h_lo h_hi hf with h | h
    · rw [h]
      have hL : |s - ((P.hi : Dyadic) : ℝ)| = ((P.hi : Dyadic) : ℝ) - s := by
        rw [abs_sub_comm]
        exact abs_of_nonneg (by linarith)
      have hR : |s - ((P.lo : Dyadic) : ℝ)| = s - ((P.lo : Dyadic) : ℝ) :=
        abs_of_nonneg (by linarith)
      rw [hL, hR, h_hi_lo]
      linarith
    · rw [h]
  · rintro ⟨_, _, _, _, _⟩
    exact ⟨F₁, rfl, P.even_hi⟩

end AnchorNeighborhood

/-! ## Neighborhood-generic counterexample cores

The ten counterexamples, proven once against `AnchorNeighborhood`. Throughout,
`δ = 2^(K−2)` is a quarter of `F₂`'s local step `2^K` at the anchor. -/

namespace AnchorNeighborhood

variable {F₁ : ParityFormat} (P : AnchorNeighborhood F₁)

include P

private theorem hi_pos : (0 : ℝ) < ((P.hi : Dyadic) : ℝ) := by
  have h_ulp_pos : (0 : ℝ) < (2 : ℝ) ^ P.t := zpow_pos (by norm_num) _
  have h_ulp_pos' : (0 : ℝ) < (2 : ℝ) ^ P.s := zpow_pos (by norm_num) _
  rw [P.coe_hi, P.coe_lo]
  linarith [P.lo2_pos]

/-- `¬ RoundsFinite F₁ RTZ x hi` for `x < hi`. -/
private theorem not_rounds_RTZ_hi {x : ℝ} (hx_pos : 0 < x)
    (hx_lt : x < ((P.hi : Dyadic) : ℝ)) :
    ¬ RoundsFinite F₁.toFiniteFormat .toZero x P.hi := by
  intro hr
  obtain ⟨_, h_bnd, _, _⟩ := hr
  rw [abs_of_pos hx_pos, abs_of_pos P.hi_pos] at h_bnd
  linarith

/-- `¬ RoundsFinite F₁ RAZ x hi` for `x > hi`. -/
private theorem not_rounds_RAZ_hi {x : ℝ}
    (hx_gt : ((P.hi : Dyadic) : ℝ) < x) :
    ¬ RoundsFinite F₁.toFiniteFormat .awayZero x P.hi := by
  intro hr
  obtain ⟨_, h_bnd, _, _⟩ := hr
  rw [abs_of_pos (lt_trans P.hi_pos hx_gt), abs_of_pos P.hi_pos] at h_bnd
  linarith

/-- `¬ RoundsFinite F₁ RTO x hi` for `x ≠ hi`: `hi` is not odd in `F₁`. -/
private theorem not_rounds_RTO_hi {x : ℝ}
    (hx_ne : x ≠ ((P.hi : Dyadic) : ℝ)) :
    ¬ RoundsFinite F₁.toFiniteFormat .toOdd x P.hi := by
  intro hr
  obtain ⟨_, _, h_parity⟩ := hr
  obtain ⟨F', hF'_eq, hF'_odd⟩ := h_parity hx_ne
  exact P.not_odd_hi ((ParityFormat.IsOdd_iff_of_toFormat_eq hF'_eq _).mp hF'_odd)

/-- Positivity of `x = hi − 2^(K−2)` for `K ≤ t`. -/
private theorem x_below_pos {K : ℤ} (hK_le : K ≤ P.t) :
    0 < ((P.hi : Dyadic) : ℝ) - (2 : ℝ) ^ (K - 2) := by
  have h_ulp_pos : (0 : ℝ) < (2 : ℝ) ^ P.t := zpow_pos (by norm_num) _
  have h_2K2_lt_ulp : (2 : ℝ) ^ (K - 2) < (2 : ℝ) ^ P.t :=
    zpow_lt_zpow_right₀ (by norm_num) (by omega)
  have h_ulp_pos' : (0 : ℝ) < (2 : ℝ) ^ P.s := zpow_pos (by norm_num) _
  rw [P.coe_hi, P.coe_lo]
  linarith [P.lo2_pos]

/-- RNE in `F₂` carries `hi − δ` up onto `hi`. -/
private theorem f₂_RNE_up (F₂ : FiniteFormat) {K : ℤ}
    (h_hi_in_F₂ : P.hi ∈ F₂.toFormat)
    (h_below : ∀ z ∈ F₂.toFormat,
      ((z : Dyadic) : ℝ) < ((P.hi : Dyadic) : ℝ) →
      ((z : Dyadic) : ℝ) ≤ ((P.hi : Dyadic) : ℝ) - (2 : ℝ) ^ K) :
    RoundsFinite F₂ (.nearest .toEven)
      (((P.hi : Dyadic) : ℝ) - (2 : ℝ) ^ (K - 2)) P.hi := by
  have h_2K2_pos : (0 : ℝ) < (2 : ℝ) ^ (K - 2) := zpow_pos (by norm_num) _
  have h_2K_split : (2 : ℝ) ^ K = 4 * (2 : ℝ) ^ (K - 2) := two_zpow_split_minus_two K
  set x_val : ℝ := ((P.hi : Dyadic) : ℝ) - (2 : ℝ) ^ (K - 2) with hx_def
  have h_x_lt_hi : x_val < ((P.hi : Dyadic) : ℝ) := by rw [hx_def]; linarith
  have h_ge_x_to_ge_hi : ∀ z ∈ F₂.toFormat, x_val ≤ ((z : Dyadic) : ℝ) →
      ((P.hi : Dyadic) : ℝ) ≤ ((z : Dyadic) : ℝ) := by
    intro z hz hz_ge
    by_contra h_lt
    push Not at h_lt
    have h := h_below z hz h_lt
    rw [hx_def] at hz_ge
    linarith
  refine ⟨h_hi_in_F₂, ?_, ?_, ?_⟩
  · right
    exact ⟨h_hi_in_F₂, le_of_lt h_x_lt_hi, h_ge_x_to_ge_hi⟩
  · intro z hz _
    rcases le_or_gt ((z : Dyadic) : ℝ) x_val with h_le | h_gt
    · have h := h_below z hz (lt_of_le_of_lt h_le h_x_lt_hi)
      rw [abs_of_neg (by linarith : x_val - ((P.hi : Dyadic) : ℝ) < 0), neg_sub,
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ x_val - ((z : Dyadic) : ℝ)),
          hx_def]
      linarith
    · have h_z_ge_hi := h_ge_x_to_ge_hi z hz (le_of_lt h_gt)
      rw [abs_of_neg (by linarith : x_val - ((P.hi : Dyadic) : ℝ) < 0), neg_sub,
          abs_of_nonpos (by linarith : x_val - ((z : Dyadic) : ℝ) ≤ 0), neg_sub]
      linarith
  · rintro ⟨z, hzF₂, _, hne, heq⟩
    exfalso
    rcases le_or_gt ((z : Dyadic) : ℝ) x_val with h_le | h_gt
    · have h := h_below z hzF₂ (lt_of_le_of_lt h_le h_x_lt_hi)
      rw [abs_of_neg (by linarith : x_val - ((P.hi : Dyadic) : ℝ) < 0), neg_sub,
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ x_val - ((z : Dyadic) : ℝ)),
          hx_def] at heq
      linarith
    · have h_z_ge_hi := h_ge_x_to_ge_hi z hzF₂ (le_of_lt h_gt)
      have h_z_ne : ((z : Dyadic) : ℝ) ≠ ((P.hi : Dyadic) : ℝ) := fun h_eq =>
        hne ((Dyadic.coe_real_inj z P.hi).mp h_eq)
      rw [abs_of_neg (by linarith : x_val - ((P.hi : Dyadic) : ℝ) < 0), neg_sub,
          abs_of_nonpos (by linarith : x_val - ((z : Dyadic) : ℝ) ≤ 0), neg_sub]
        at heq
      exact h_z_ne (by linarith)

/-- RAZ in `F₂` carries `hi − δ` up onto `hi`. -/
private theorem f₂_RAZ_up (F₂ : FiniteFormat) {K : ℤ} (hK_le : K ≤ P.t)
    (h_hi_in_F₂ : P.hi ∈ F₂.toFormat)
    (h_below : ∀ z ∈ F₂.toFormat,
      ((z : Dyadic) : ℝ) < ((P.hi : Dyadic) : ℝ) →
      ((z : Dyadic) : ℝ) ≤ ((P.hi : Dyadic) : ℝ) - (2 : ℝ) ^ K) :
    RoundsFinite F₂ .awayZero
      (((P.hi : Dyadic) : ℝ) - (2 : ℝ) ^ (K - 2)) P.hi := by
  have h_2K2_pos : (0 : ℝ) < (2 : ℝ) ^ (K - 2) := zpow_pos (by norm_num) _
  have h_2K_split : (2 : ℝ) ^ K = 4 * (2 : ℝ) ^ (K - 2) := two_zpow_split_minus_two K
  set x_val : ℝ := ((P.hi : Dyadic) : ℝ) - (2 : ℝ) ^ (K - 2) with hx_def
  have h_x_pos : 0 < x_val := P.x_below_pos hK_le
  have h_x_lt_hi : x_val < ((P.hi : Dyadic) : ℝ) := by rw [hx_def]; linarith
  refine ⟨h_hi_in_F₂, ?_, ?_, ?_⟩
  · rw [abs_of_pos h_x_pos, abs_of_pos P.hi_pos]; linarith
  · exact le_of_lt (mul_pos P.hi_pos h_x_pos)
  · intro z hz hz_bnd hz_sign
    have h_z_nn : 0 ≤ ((z : Dyadic) : ℝ) := nonneg_of_mul_nonneg_pos hz_sign h_x_pos
    rw [abs_of_pos h_x_pos, abs_of_nonneg h_z_nn] at hz_bnd
    rw [abs_of_pos P.hi_pos, abs_of_nonneg h_z_nn]
    by_contra h_lt
    push Not at h_lt
    have h := h_below z hz h_lt
    rw [hx_def] at hz_bnd
    linarith

/-- RTZ in `F₂` carries `hi + δ` down onto `hi`. -/
private theorem f₂_RTZ_down (F₂ : FiniteFormat) {K : ℤ}
    (h_hi_in_F₂ : P.hi ∈ F₂.toFormat)
    (h_above : ∀ z ∈ F₂.toFormat,
      ((P.hi : Dyadic) : ℝ) < ((z : Dyadic) : ℝ) →
      ((P.hi : Dyadic) : ℝ) + (2 : ℝ) ^ K ≤ ((z : Dyadic) : ℝ)) :
    RoundsFinite F₂ .toZero
      (((P.hi : Dyadic) : ℝ) + (2 : ℝ) ^ (K - 2)) P.hi := by
  have h_2K2_pos : (0 : ℝ) < (2 : ℝ) ^ (K - 2) := zpow_pos (by norm_num) _
  have h_2K_split : (2 : ℝ) ^ K = 4 * (2 : ℝ) ^ (K - 2) := two_zpow_split_minus_two K
  set x_val : ℝ := ((P.hi : Dyadic) : ℝ) + (2 : ℝ) ^ (K - 2) with hx_def
  have h_x_pos : 0 < x_val := by linarith [P.hi_pos]
  refine ⟨h_hi_in_F₂, ?_, ?_, ?_⟩
  · rw [abs_of_pos P.hi_pos, abs_of_pos h_x_pos]; linarith
  · exact le_of_lt (mul_pos P.hi_pos h_x_pos)
  · intro z hz hz_bnd hz_sign
    have h_z_nn : 0 ≤ ((z : Dyadic) : ℝ) := nonneg_of_mul_nonneg_pos hz_sign h_x_pos
    rw [abs_of_nonneg h_z_nn, abs_of_pos h_x_pos] at hz_bnd
    rw [abs_of_pos P.hi_pos, abs_of_nonneg h_z_nn]
    by_contra h_gt
    push Not at h_gt
    have h := h_above z hz h_gt
    rw [hx_def] at hz_bnd
    linarith

/-- RNE in `F₂` carries `hi + δ` down onto `hi`. -/
private theorem f₂_RNE_down (F₂ : FiniteFormat) {K : ℤ}
    (h_hi_in_F₂ : P.hi ∈ F₂.toFormat)
    (h_above : ∀ z ∈ F₂.toFormat,
      ((P.hi : Dyadic) : ℝ) < ((z : Dyadic) : ℝ) →
      ((P.hi : Dyadic) : ℝ) + (2 : ℝ) ^ K ≤ ((z : Dyadic) : ℝ)) :
    RoundsFinite F₂ (.nearest .toEven)
      (((P.hi : Dyadic) : ℝ) + (2 : ℝ) ^ (K - 2)) P.hi := by
  have h_2K2_pos : (0 : ℝ) < (2 : ℝ) ^ (K - 2) := zpow_pos (by norm_num) _
  have h_2K_split : (2 : ℝ) ^ K = 4 * (2 : ℝ) ^ (K - 2) := two_zpow_split_minus_two K
  set x_val : ℝ := ((P.hi : Dyadic) : ℝ) + (2 : ℝ) ^ (K - 2) with hx_def
  have h_x_gt_hi : ((P.hi : Dyadic) : ℝ) < x_val := by rw [hx_def]; linarith
  have h_le_x_to_le_hi : ∀ z ∈ F₂.toFormat, ((z : Dyadic) : ℝ) ≤ x_val →
      ((z : Dyadic) : ℝ) ≤ ((P.hi : Dyadic) : ℝ) := by
    intro z hz hz_le
    by_contra h_gt
    push Not at h_gt
    have h := h_above z hz h_gt
    rw [hx_def] at hz_le
    linarith
  refine ⟨h_hi_in_F₂, ?_, ?_, ?_⟩
  · left
    exact ⟨h_hi_in_F₂, le_of_lt h_x_gt_hi, h_le_x_to_le_hi⟩
  · intro z hz _
    rcases le_or_gt ((z : Dyadic) : ℝ) x_val with h_le | h_gt
    · have h := h_le_x_to_le_hi z hz h_le
      rw [abs_of_pos (by linarith : (0 : ℝ) < x_val - ((P.hi : Dyadic) : ℝ)),
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ x_val - ((z : Dyadic) : ℝ))]
      linarith
    · have h_z_gt_hi : ((P.hi : Dyadic) : ℝ) < ((z : Dyadic) : ℝ) := by
        by_contra h_le'
        push Not at h_le'
        linarith
      have h := h_above z hz h_z_gt_hi
      rw [abs_of_pos (by linarith : (0 : ℝ) < x_val - ((P.hi : Dyadic) : ℝ)),
          abs_of_nonpos (by linarith : x_val - ((z : Dyadic) : ℝ) ≤ 0), neg_sub,
          hx_def]
      linarith
  · rintro ⟨z, hzF₂, _, hne, heq⟩
    exfalso
    rcases le_or_gt ((z : Dyadic) : ℝ) x_val with h_le | h_gt
    · have h := h_le_x_to_le_hi z hzF₂ h_le
      have h_z_ne : ((z : Dyadic) : ℝ) ≠ ((P.hi : Dyadic) : ℝ) := fun h_eq =>
        hne ((Dyadic.coe_real_inj z P.hi).mp h_eq)
      rw [abs_of_pos (by linarith : (0 : ℝ) < x_val - ((P.hi : Dyadic) : ℝ)),
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ x_val - ((z : Dyadic) : ℝ))]
        at heq
      exact h_z_ne (by linarith)
    · have h_z_gt_hi : ((P.hi : Dyadic) : ℝ) < ((z : Dyadic) : ℝ) := by linarith
      have h := h_above z hzF₂ h_z_gt_hi
      rw [abs_of_pos (by linarith : (0 : ℝ) < x_val - ((P.hi : Dyadic) : ℝ)),
          abs_of_nonpos (by linarith : x_val - ((z : Dyadic) : ℝ) ≤ 0), neg_sub,
          hx_def] at heq
      linarith

/-- **RNE → RTZ.** -/
theorem no_rndRNE_RTZ (F₂ : FiniteFormat)
    (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ (.nearest .toEven) x z ∧
      RoundsFinite F₁.toFiniteFormat .toZero (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat .toZero x w := by
  obtain ⟨K, hK_le, h_below⟩ := P.f2_below_hi F₂ hsub
  have h_2K2_pos : (0 : ℝ) < (2 : ℝ) ^ (K - 2) := zpow_pos (by norm_num) _
  exact ⟨((P.hi : Dyadic) : ℝ) - (2 : ℝ) ^ (K - 2), P.hi, P.hi,
    P.f₂_RNE_up F₂ (hsub _ P.mem_hi) h_below,
    RoundsFinite.toZero_self P.mem_hi,
    P.not_rounds_RTZ_hi (P.x_below_pos hK_le) (by linarith)⟩

/-- **RAZ → RTZ.** -/
theorem no_rndRAZ_RTZ (F₂ : FiniteFormat)
    (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .awayZero x z ∧
      RoundsFinite F₁.toFiniteFormat .toZero (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat .toZero x w := by
  obtain ⟨K, hK_le, h_below⟩ := P.f2_below_hi F₂ hsub
  have h_2K2_pos : (0 : ℝ) < (2 : ℝ) ^ (K - 2) := zpow_pos (by norm_num) _
  exact ⟨((P.hi : Dyadic) : ℝ) - (2 : ℝ) ^ (K - 2), P.hi, P.hi,
    P.f₂_RAZ_up F₂ hK_le (hsub _ P.mem_hi) h_below,
    RoundsFinite.toZero_self P.mem_hi,
    P.not_rounds_RTZ_hi (P.x_below_pos hK_le) (by linarith)⟩

/-- **RTZ → RAZ.** -/
theorem no_rndRTZ_RAZ (F₂ : FiniteFormat)
    (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .toZero x z ∧
      RoundsFinite F₁.toFiniteFormat .awayZero (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat .awayZero x w := by
  obtain ⟨K, hK_le, h_above⟩ := P.f2_above_hi F₂ hsub
  have h_2K2_pos : (0 : ℝ) < (2 : ℝ) ^ (K - 2) := zpow_pos (by norm_num) _
  exact ⟨((P.hi : Dyadic) : ℝ) + (2 : ℝ) ^ (K - 2), P.hi, P.hi,
    P.f₂_RTZ_down F₂ (hsub _ P.mem_hi) h_above,
    RoundsFinite.awayZero_self P.mem_hi,
    P.not_rounds_RAZ_hi (by linarith)⟩

/-- **RNE → RAZ.** -/
theorem no_rndRNE_RAZ (F₂ : FiniteFormat)
    (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ (.nearest .toEven) x z ∧
      RoundsFinite F₁.toFiniteFormat .awayZero (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat .awayZero x w := by
  obtain ⟨K, hK_le, h_above⟩ := P.f2_above_hi F₂ hsub
  have h_2K2_pos : (0 : ℝ) < (2 : ℝ) ^ (K - 2) := zpow_pos (by norm_num) _
  exact ⟨((P.hi : Dyadic) : ℝ) + (2 : ℝ) ^ (K - 2), P.hi, P.hi,
    P.f₂_RNE_down F₂ (hsub _ P.mem_hi) h_above,
    RoundsFinite.awayZero_self P.mem_hi,
    P.not_rounds_RAZ_hi (by linarith)⟩

/-- **RAZ → RTO.** -/
theorem no_rndRAZ_RTO (F₂ : FiniteFormat)
    (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .awayZero x z ∧
      RoundsFinite F₁.toFiniteFormat .toOdd (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat .toOdd x w := by
  obtain ⟨K, hK_le, h_below⟩ := P.f2_below_hi F₂ hsub
  have h_2K2_pos : (0 : ℝ) < (2 : ℝ) ^ (K - 2) := zpow_pos (by norm_num) _
  exact ⟨((P.hi : Dyadic) : ℝ) - (2 : ℝ) ^ (K - 2), P.hi, P.hi,
    P.f₂_RAZ_up F₂ hK_le (hsub _ P.mem_hi) h_below,
    RoundsFinite.toOdd_self P.mem_hi,
    P.not_rounds_RTO_hi (by intro h; nlinarith)⟩

/-- **RNE → RTO.** -/
theorem no_rndRNE_RTO (F₂ : FiniteFormat)
    (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ (.nearest .toEven) x z ∧
      RoundsFinite F₁.toFiniteFormat .toOdd (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat .toOdd x w := by
  obtain ⟨K, hK_le, h_below⟩ := P.f2_below_hi F₂ hsub
  have h_2K2_pos : (0 : ℝ) < (2 : ℝ) ^ (K - 2) := zpow_pos (by norm_num) _
  exact ⟨((P.hi : Dyadic) : ℝ) - (2 : ℝ) ^ (K - 2), P.hi, P.hi,
    P.f₂_RNE_up F₂ (hsub _ P.mem_hi) h_below,
    RoundsFinite.toOdd_self P.mem_hi,
    P.not_rounds_RTO_hi (by intro h; nlinarith)⟩

/-- **RTZ → RTO.** -/
theorem no_rndRTZ_RTO (F₂ : FiniteFormat)
    (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .toZero x z ∧
      RoundsFinite F₁.toFiniteFormat .toOdd (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat .toOdd x w := by
  obtain ⟨K, hK_le, h_above⟩ := P.f2_above_hi F₂ hsub
  have h_2K2_pos : (0 : ℝ) < (2 : ℝ) ^ (K - 2) := zpow_pos (by norm_num) _
  exact ⟨((P.hi : Dyadic) : ℝ) + (2 : ℝ) ^ (K - 2), P.hi, P.hi,
    P.f₂_RTZ_down F₂ (hsub _ P.mem_hi) h_above,
    RoundsFinite.toOdd_self P.mem_hi,
    P.not_rounds_RTO_hi (by intro h; nlinarith)⟩

/-- **RTZ → RNE.** `x = (lo2 + 2^(t−1)) + δ`, just above the lower midpoint:
RTZ in `F₂` lands at or below the midpoint, RNE then returns the even `lo2`;
the direct RNE of `x` is the strictly nearer `lo`. -/
theorem no_rndRTZ_RNE (F₂ : FiniteFormat)
    (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .toZero x z ∧
      RoundsFinite F₁.toFiniteFormat (.nearest .toEven) (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat (.nearest .toEven) x w := by
  obtain ⟨K, hK_le, h_mid_below, h_mid_above⟩ := P.f2_mid_lo F₂ hsub
  have h_half_pos : (0 : ℝ) < (2 : ℝ) ^ (P.s - 1) := zpow_pos (by norm_num) _
  have h_2K1_pos : (0 : ℝ) < (2 : ℝ) ^ (K - 1) := zpow_pos (by norm_num) _
  have h_2K2_pos : (0 : ℝ) < (2 : ℝ) ^ (K - 2) := zpow_pos (by norm_num) _
  have h_2K2_lt_2K1 : (2 : ℝ) ^ (K - 2) < (2 : ℝ) ^ (K - 1) :=
    zpow_lt_zpow_right₀ (by norm_num) (by omega)
  have h_2K1_le_half : (2 : ℝ) ^ (K - 1) ≤ (2 : ℝ) ^ (P.s - 1) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have h_two_half : (2 : ℝ) ^ P.s = 2 * (2 : ℝ) ^ (P.s - 1) := by
    have h := two_zpow_succ (P.s - 1)
    rwa [show P.s - 1 + 1 = P.s by ring] at h
  set x_val : ℝ := ((P.lo2 : Dyadic) : ℝ) + (2 : ℝ) ^ (P.s - 1) + (2 : ℝ) ^ (K - 2)
    with hx_def
  have h_x_pos : 0 < x_val := by rw [hx_def]; linarith [P.lo2_pos]
  set z : Dyadic := rndUnbounded F₂ .toZero x_val (not_isUndefined_toZero F₂)
    with hz_def
  have hz_unb : RoundsFinite F₂.unbounded .toZero x_val z :=
    rndUnbounded_satisfies F₂ .toZero x_val (not_isUndefined_toZero F₂)
  have h_z_mem : z ∈ F₂.toFormat := by
    obtain ⟨hz_mem_unb, hz_abs', hz_sign', _⟩ := hz_unb
    have h_z_nn : 0 ≤ ((z : Dyadic) : ℝ) := nonneg_of_mul_nonneg_pos hz_sign' h_x_pos
    have h_z_le_x : ((z : Dyadic) : ℝ) ≤ x_val := by
      rwa [abs_of_nonneg h_z_nn, abs_of_pos h_x_pos] at hz_abs'
    have h_x_lt_lo : x_val < ((P.lo : Dyadic) : ℝ) := by rw [P.coe_lo, hx_def]; linarith
    have h_lo_pos : (0 : ℝ) < ((P.lo : Dyadic) : ℝ) :=
      lt_of_le_of_lt h_z_nn (lt_of_le_of_lt h_z_le_x h_x_lt_lo)
    refine mem_of_mem_unbounded_of_boundOK hz_mem_unb
      (boundOK_of_abs_le ?_ (hsub _ P.mem_lo).2.2)
    rw [abs_of_nonneg h_z_nn, abs_of_pos h_lo_pos]; linarith
  have hz_rounds : RoundsFinite F₂ .toZero x_val z :=
    RoundsFinite.toZero_restrict hz_unb h_z_mem.2.2
  obtain ⟨hz_mem, hz_abs, hz_sign, hz_max⟩ := hz_rounds
  have h_z_nn : 0 ≤ ((z : Dyadic) : ℝ) := nonneg_of_mul_nonneg_pos hz_sign h_x_pos
  have h_z_le_x : ((z : Dyadic) : ℝ) ≤ x_val := by
    have h := hz_abs
    rwa [abs_of_nonneg h_z_nn, abs_of_pos h_x_pos] at h
  have h_lo2_in_F₂ : P.lo2 ∈ F₂.toFormat := hsub _ P.mem_lo2
  have h_z_ge : ((P.lo2 : Dyadic) : ℝ) ≤ ((z : Dyadic) : ℝ) := by
    have h_le_abs : |((P.lo2 : Dyadic) : ℝ)| ≤ |x_val| := by
      rw [abs_of_pos P.lo2_pos, abs_of_pos h_x_pos, hx_def]
      linarith
    have h_sign : ((P.lo2 : Dyadic) : ℝ) * x_val ≥ 0 :=
      le_of_lt (mul_pos P.lo2_pos h_x_pos)
    have h := hz_max P.lo2 h_lo2_in_F₂ h_le_abs h_sign
    rwa [abs_of_pos P.lo2_pos, abs_of_nonneg h_z_nn] at h
  have h_z_le_M : ((z : Dyadic) : ℝ)
      ≤ ((P.lo2 : Dyadic) : ℝ) + (2 : ℝ) ^ (P.s - 1) := by
    by_contra h_gt
    push Not at h_gt
    have h := h_mid_above z hz_mem h_gt
    rw [hx_def] at h_z_le_x
    linarith
  refine ⟨x_val, z, P.lo2, ⟨hz_mem, hz_abs, hz_sign, hz_max⟩,
    P.rounds_RNE_lo2 h_z_ge h_z_le_M, ?_⟩
  intro hr
  obtain ⟨_, _, h_close, _⟩ := hr
  have h_x_lt_lo : x_val < ((P.lo : Dyadic) : ℝ) := by
    rw [P.coe_lo, hx_def]
    linarith
  have h_lo_faith : IsFaithfulRound F₁.toFiniteFormat x_val P.lo := by
    right
    refine ⟨P.mem_lo, le_of_lt h_x_lt_lo, ?_⟩
    intro v hv hv_ge
    refine P.f1_ceil_lo2 v hv ?_
    rw [hx_def] at hv_ge
    linarith
  have h := h_close P.lo P.mem_lo h_lo_faith
  rw [P.coe_lo,
      abs_of_nonneg (by rw [hx_def]; linarith :
        (0 : ℝ) ≤ x_val - ((P.lo2 : Dyadic) : ℝ)),
      abs_of_nonpos (by rw [hx_def]; linarith :
        x_val - (((P.lo2 : Dyadic) : ℝ) + (2 : ℝ) ^ P.s) ≤ 0), neg_sub,
      hx_def] at h
  linarith

/-- **RAZ → RNE.** `x = (lo + 2^(t−1)) − δ`, just below the upper midpoint:
RAZ in `F₂` lands at or above the midpoint, RNE then returns the even `hi`;
the direct RNE of `x` is the strictly nearer `lo`. -/
theorem no_rndRAZ_RNE (F₂ : FiniteFormat)
    (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .awayZero x z ∧
      RoundsFinite F₁.toFiniteFormat (.nearest .toEven) (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat (.nearest .toEven) x w := by
  obtain ⟨K, hK_le, h_mid_below, h_mid_above⟩ := P.f2_mid_hi F₂ hsub
  have h_half_pos : (0 : ℝ) < (2 : ℝ) ^ (P.t - 1) := zpow_pos (by norm_num) _
  have h_2K1_pos : (0 : ℝ) < (2 : ℝ) ^ (K - 1) := zpow_pos (by norm_num) _
  have h_2K2_pos : (0 : ℝ) < (2 : ℝ) ^ (K - 2) := zpow_pos (by norm_num) _
  have h_2K2_lt_2K1 : (2 : ℝ) ^ (K - 2) < (2 : ℝ) ^ (K - 1) :=
    zpow_lt_zpow_right₀ (by norm_num) (by omega)
  have h_2K1_le_half : (2 : ℝ) ^ (K - 1) ≤ (2 : ℝ) ^ (P.t - 1) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have h_two_half : (2 : ℝ) ^ P.t = 2 * (2 : ℝ) ^ (P.t - 1) := by
    have h := two_zpow_succ (P.t - 1)
    rwa [show P.t - 1 + 1 = P.t by ring] at h
  have h_lo_pos : (0 : ℝ) < ((P.lo : Dyadic) : ℝ) := by
    have h_ulp_pos : (0 : ℝ) < (2 : ℝ) ^ P.s := zpow_pos (by norm_num) _
    rw [P.coe_lo]
    linarith [P.lo2_pos]
  set x_val : ℝ := ((P.lo : Dyadic) : ℝ) + (2 : ℝ) ^ (P.t - 1) - (2 : ℝ) ^ (K - 2)
    with hx_def
  have h_x_pos : 0 < x_val := by rw [hx_def]; linarith
  set z : Dyadic := rndUnbounded F₂ .awayZero x_val (not_isUndefined_awayZero F₂)
    with hz_def
  have hz_unb : RoundsFinite F₂.unbounded .awayZero x_val z :=
    rndUnbounded_satisfies F₂ .awayZero x_val (not_isUndefined_awayZero F₂)
  have h_hi_in_F₂ : P.hi ∈ F₂.toFormat := hsub _ P.mem_hi
  have h_x_lt_hi : x_val < ((P.hi : Dyadic) : ℝ) := by
    rw [hx_def, P.coe_hi, P.coe_lo]
    linarith
  have h_z_mem : z ∈ F₂.toFormat := by
    obtain ⟨hz_mem_unb, hz_abs', hz_sign', hz_min'⟩ := hz_unb
    have h_z_nn : 0 ≤ ((z : Dyadic) : ℝ) := nonneg_of_mul_nonneg_pos hz_sign' h_x_pos
    have h_z_le_hi : ((z : Dyadic) : ℝ) ≤ ((P.hi : Dyadic) : ℝ) := by
      have h_ge_abs : |x_val| ≤ |((P.hi : Dyadic) : ℝ)| := by
        rw [abs_of_pos h_x_pos, abs_of_pos P.hi_pos]; linarith
      have h_sign : ((P.hi : Dyadic) : ℝ) * x_val ≥ 0 :=
        le_of_lt (mul_pos P.hi_pos h_x_pos)
      have h := hz_min' P.hi (mem_unbounded_of_mem h_hi_in_F₂) h_ge_abs h_sign
      rwa [abs_of_pos P.hi_pos, abs_of_nonneg h_z_nn] at h
    refine mem_of_mem_unbounded_of_boundOK hz_mem_unb
      (boundOK_of_abs_le ?_ h_hi_in_F₂.2.2)
    rw [abs_of_nonneg h_z_nn, abs_of_pos P.hi_pos]; exact h_z_le_hi
  have hz_rounds : RoundsFinite F₂ .awayZero x_val z :=
    RoundsFinite.awayZero_restrict hz_unb h_z_mem.2.2
  obtain ⟨hz_mem, hz_abs, hz_sign, hz_min⟩ := hz_rounds
  have h_z_nn : 0 ≤ ((z : Dyadic) : ℝ) := nonneg_of_mul_nonneg_pos hz_sign h_x_pos
  have h_z_ge_x : x_val ≤ ((z : Dyadic) : ℝ) := by
    have h := hz_abs
    rwa [abs_of_pos h_x_pos, abs_of_nonneg h_z_nn] at h
  have h_z_le_hi : ((z : Dyadic) : ℝ) ≤ ((P.hi : Dyadic) : ℝ) := by
    have h_ge_abs : |x_val| ≤ |((P.hi : Dyadic) : ℝ)| := by
      rw [abs_of_pos h_x_pos, abs_of_pos P.hi_pos]
      linarith
    have h_sign : ((P.hi : Dyadic) : ℝ) * x_val ≥ 0 :=
      le_of_lt (mul_pos P.hi_pos h_x_pos)
    have h := hz_min P.hi h_hi_in_F₂ h_ge_abs h_sign
    rwa [abs_of_pos P.hi_pos, abs_of_nonneg h_z_nn] at h
  have h_z_ge_M : ((P.lo : Dyadic) : ℝ) + (2 : ℝ) ^ (P.t - 1)
      ≤ ((z : Dyadic) : ℝ) := by
    by_contra h_lt
    push Not at h_lt
    have h := h_mid_below z hz_mem h_lt
    rw [hx_def] at h_z_ge_x
    linarith
  refine ⟨x_val, z, P.hi, ⟨hz_mem, hz_abs, hz_sign, hz_min⟩,
    P.rounds_RNE_hi h_z_ge_M h_z_le_hi, ?_⟩
  intro hr
  obtain ⟨_, _, h_close, _⟩ := hr
  have h_x_gt_lo : ((P.lo : Dyadic) : ℝ) < x_val := by
    rw [hx_def]
    linarith
  have h_lo_faith : IsFaithfulRound F₁.toFiniteFormat x_val P.lo := by
    left
    refine ⟨P.mem_lo, le_of_lt h_x_gt_lo, ?_⟩
    intro v hv hv_le
    refine P.f1_floor_hi v hv ?_
    rw [hx_def] at hv_le
    rw [P.coe_lo] at hv_le
    rw [P.coe_hi, P.coe_lo]
    linarith
  have h := h_close P.lo P.mem_lo h_lo_faith
  have h_hi_lo : ((P.hi : Dyadic) : ℝ) = ((P.lo : Dyadic) : ℝ) + (2 : ℝ) ^ P.t :=
    P.coe_hi
  rw [h_hi_lo,
      abs_of_nonpos (by rw [hx_def]; linarith :
        x_val - (((P.lo : Dyadic) : ℝ) + (2 : ℝ) ^ P.t) ≤ 0), neg_sub,
      abs_of_nonneg (by rw [hx_def]; linarith :
        (0 : ℝ) ≤ x_val - ((P.lo : Dyadic) : ℝ)),
      hx_def] at h
  linarith

/-- **RNE → RNE.** Needs one extra digit of containment: with
`mid = lo + 2^(t−1) ∈ F₂`, the witness `x = mid − δ` rounds (RNE, `F₂`) up
onto `mid`, whose `F₁`-tie breaks to the even `hi`; the direct RNE of `x`
is the strictly nearer `lo`. -/
theorem no_rndRNE_RNE (F₂ : FiniteFormat)
    (hsub : (F₁.toFiniteFormat.extend 1).toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ (.nearest .toEven) x z ∧
      RoundsFinite F₁.toFiniteFormat (.nearest .toEven) (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat (.nearest .toEven) x w := by
  have h_mid_in_F₂ : P.mid ∈ F₂.toFormat := hsub _ P.mid_mem_ext1
  obtain ⟨K, hK_le, h_below, h_above⟩ := P.f2_mem_mid F₂ h_mid_in_F₂
  have h_half_pos : (0 : ℝ) < (2 : ℝ) ^ (P.t - 1) := zpow_pos (by norm_num) _
  have h_2K_pos : (0 : ℝ) < (2 : ℝ) ^ K := zpow_pos (by norm_num) _
  have h_2K2_pos : (0 : ℝ) < (2 : ℝ) ^ (K - 2) := zpow_pos (by norm_num) _
  have h_2K_split : (2 : ℝ) ^ K = 4 * (2 : ℝ) ^ (K - 2) := two_zpow_split_minus_two K
  have h_2K_le_half : (2 : ℝ) ^ K ≤ (2 : ℝ) ^ (P.t - 1) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have h_two_half : (2 : ℝ) ^ P.t = 2 * (2 : ℝ) ^ (P.t - 1) := by
    have h := two_zpow_succ (P.t - 1)
    rwa [show P.t - 1 + 1 = P.t by ring] at h
  set x_val : ℝ := ((P.mid : Dyadic) : ℝ) - (2 : ℝ) ^ (K - 2) with hx_def
  have h_x_lt_mid : x_val < ((P.mid : Dyadic) : ℝ) := by rw [hx_def]; linarith
  refine ⟨x_val, P.mid, P.hi, ?_, ?_, ?_⟩
  · -- RNE in F₂ rounds x up onto mid.
    have h_ge_x_to_ge_mid : ∀ z ∈ F₂.toFormat, x_val ≤ ((z : Dyadic) : ℝ) →
        ((P.mid : Dyadic) : ℝ) ≤ ((z : Dyadic) : ℝ) := by
      intro z hz hz_ge
      by_contra h_lt
      push Not at h_lt
      have h := h_below z hz h_lt
      rw [hx_def] at hz_ge
      linarith
    refine ⟨h_mid_in_F₂, ?_, ?_, ?_⟩
    · right
      exact ⟨h_mid_in_F₂, le_of_lt h_x_lt_mid, h_ge_x_to_ge_mid⟩
    · intro z hz _
      rcases le_or_gt ((z : Dyadic) : ℝ) x_val with h_le | h_gt
      · have h := h_below z hz (lt_of_le_of_lt h_le h_x_lt_mid)
        rw [abs_of_neg (by linarith : x_val - ((P.mid : Dyadic) : ℝ) < 0), neg_sub,
            abs_of_nonneg (by linarith : (0 : ℝ) ≤ x_val - ((z : Dyadic) : ℝ)),
            hx_def]
        linarith
      · have h_z_ge_mid := h_ge_x_to_ge_mid z hz (le_of_lt h_gt)
        rw [abs_of_neg (by linarith : x_val - ((P.mid : Dyadic) : ℝ) < 0), neg_sub,
            abs_of_nonpos (by linarith : x_val - ((z : Dyadic) : ℝ) ≤ 0), neg_sub]
        linarith
    · rintro ⟨z, hzF₂, _, hne, heq⟩
      exfalso
      rcases le_or_gt ((z : Dyadic) : ℝ) x_val with h_le | h_gt
      · have h := h_below z hzF₂ (lt_of_le_of_lt h_le h_x_lt_mid)
        rw [abs_of_neg (by linarith : x_val - ((P.mid : Dyadic) : ℝ) < 0), neg_sub,
            abs_of_nonneg (by linarith : (0 : ℝ) ≤ x_val - ((z : Dyadic) : ℝ)),
            hx_def] at heq
        linarith
      · have h_z_ge_mid := h_ge_x_to_ge_mid z hzF₂ (le_of_lt h_gt)
        have h_z_ne : ((z : Dyadic) : ℝ) ≠ ((P.mid : Dyadic) : ℝ) := fun h_eq =>
          hne ((Dyadic.coe_real_inj z P.mid).mp h_eq)
        have h_z_gt_mid : ((P.mid : Dyadic) : ℝ) < ((z : Dyadic) : ℝ) :=
          lt_of_le_of_ne h_z_ge_mid (Ne.symm h_z_ne)
        have h := h_above z hzF₂ h_z_gt_mid
        rw [abs_of_neg (by linarith : x_val - ((P.mid : Dyadic) : ℝ) < 0), neg_sub,
            abs_of_nonpos (by linarith : x_val - ((z : Dyadic) : ℝ) ≤ 0), neg_sub,
            hx_def] at heq
        linarith
  · -- The F₁-tie at mid breaks to the even hi.
    refine P.rounds_RNE_hi (le_of_eq P.coe_mid.symm) ?_
    rw [P.coe_mid, P.coe_hi, P.coe_lo]
    linarith
  · -- The direct RNE of x is lo.
    intro hr
    obtain ⟨_, _, h_close, _⟩ := hr
    have h_x_gt_lo : ((P.lo : Dyadic) : ℝ) < x_val := by
      rw [hx_def, P.coe_mid]
      linarith
    have h_x_lt_hi : x_val < ((P.hi : Dyadic) : ℝ) := by
      rw [hx_def, P.coe_mid, P.coe_hi, P.coe_lo]
      linarith
    have h_lo_faith : IsFaithfulRound F₁.toFiniteFormat x_val P.lo := by
      left
      refine ⟨P.mem_lo, le_of_lt h_x_gt_lo, ?_⟩
      intro v hv hv_le
      exact P.f1_floor_hi v hv (lt_of_le_of_lt hv_le h_x_lt_hi)
    have h := h_close P.lo P.mem_lo h_lo_faith
    have h_hi_lo : ((P.hi : Dyadic) : ℝ)
        = ((P.lo : Dyadic) : ℝ) + (2 : ℝ) ^ P.t :=
      P.coe_hi
    rw [h_hi_lo,
        abs_of_nonpos (by
          rw [hx_def, P.coe_mid]
          linarith :
          x_val - (((P.lo : Dyadic) : ℝ) + (2 : ℝ) ^ P.t) ≤ 0), neg_sub,
        abs_of_nonneg (by
          rw [hx_def, P.coe_mid]
          linarith :
          (0 : ℝ) ≤ x_val - ((P.lo : Dyadic) : ℝ)),
        hx_def, P.coe_mid] at h
    linarith

end AnchorNeighborhood

end Cex

end Mpfx
