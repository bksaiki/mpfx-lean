import Mpfx.Rounding.Defs
import Mpfx.Format.CanonicalExp
import Mpfx.Rounding.Parity

/-!
# Round-predicate layer

Consequences of the `RoundsFinite` spec, per mode and mode-generic: sign
symmetry, the directed-vs-zero-relative mode equivalences, uniqueness,
faithfulness, sign preservation and monotonicity.

Nothing here mentions the `rnd` construction.
-/

namespace Mpfx

/-! ## Sign-symmetry algebraic helpers -/

private lemma neg_sub_neg_abs (a b : ℝ) : |(-a) - (-b)| = |a - b| := by
  rw [show -a - -b = -(a - b) by ring, abs_neg]

private lemma abs_neg_sub_dyadic (x : ℝ) (z : Dyadic) :
    |(-x) - (z : ℝ)| = |x - ((-z : Dyadic) : ℝ)| := by
  rw [Dyadic.coe_real_neg, show -x - (z : ℝ) = -(x - -(z : ℝ)) by ring, abs_neg]

/-- Under `y ↦ -y` with `y ≠ 0`, the overflow sign flips. -/
private lemma decide_neg_lt_zero {y : Dyadic} (hy : (y : ℝ) ≠ 0) :
    decide (((-y : Dyadic) : ℚ) < 0) = !decide ((y : ℚ) < 0) := by
  have hy' : (y : ℚ) ≠ 0 := fun h0 => hy (by rw [Dyadic.coe_real_eq_ratCast, h0, Rat.cast_zero])
  rw [Subring.coe_neg]
  rcases lt_or_gt_of_ne hy' with h | h
  · have h1 : ¬ (-(y : ℚ) < 0) := fun h' => by linarith
    simp [h, h1]
  · have h1 : -(y : ℚ) < 0 := by linarith
    have h2 : ¬ ((y : ℚ) < 0) := fun h' => by linarith
    simp [h1, h2]

/-- An out-of-bound value is nonzero. -/
theorem ne_zero_of_not_boundOK {F : FiniteFormat} {y : Dyadic}
    (h : ¬ Format.boundOK F.b y) : (y : ℝ) ≠ 0 := fun h0 =>
  h (by rw [eq_zero_of_coe_real_zero h0]; exact Format.boundOK_zero _)

/-! ## Sign-symmetry helper: `IsFaithfulRound` -/

/-- `IsFaithfulRound` is invariant under joint negation of `x` and `y`. The
two disjuncts swap roles: a max-below witness for `x` becomes a min-above
witness for `-x`. -/
theorem IsFaithfulRound.neg_iff (F : FiniteFormat) (x : ℝ) (y : Dyadic) :
    IsFaithfulRound F x y ↔ IsFaithfulRound F (-x) (-y) := by
  unfold IsFaithfulRound
  simp only [Dyadic.coe_real_neg, FiniteFormat.mem_neg_iff]
  constructor
  · rintro (⟨hm, h_le, h_max⟩ | ⟨hm, h_le, h_min⟩)
    · right
      refine ⟨hm, by linarith, ?_⟩
      intro z hz hxz
      have hnz : (-z) ∈ F := FiniteFormat.neg_mem hz
      have hnzx : ((-z : Dyadic) : ℝ) ≤ x := by rw [Dyadic.coe_real_neg]; linarith
      have h := h_max (-z) hnz hnzx
      rw [Dyadic.coe_real_neg] at h; linarith
    · left
      refine ⟨hm, by linarith, ?_⟩
      intro z hz hzx
      have hnz : (-z) ∈ F := FiniteFormat.neg_mem hz
      have hnzx : x ≤ ((-z : Dyadic) : ℝ) := by rw [Dyadic.coe_real_neg]; linarith
      have h := h_min (-z) hnz hnzx
      rw [Dyadic.coe_real_neg] at h; linarith
  · rintro (⟨hm, h_le, h_max⟩ | ⟨hm, h_le, h_min⟩)
    · right
      refine ⟨hm, by linarith, ?_⟩
      intro z hz hxz
      have hnz : (-z) ∈ F := FiniteFormat.neg_mem hz
      have hnzx : ((-z : Dyadic) : ℝ) ≤ -x := by rw [Dyadic.coe_real_neg]; linarith
      have h := h_max (-z) hnz hnzx
      rw [Dyadic.coe_real_neg] at h; linarith
    · left
      refine ⟨hm, by linarith, ?_⟩
      intro z hz hzx
      have hnz : (-z) ∈ F := FiniteFormat.neg_mem hz
      have hnzx : -x ≤ ((-z : Dyadic) : ℝ) := by rw [Dyadic.coe_real_neg]; linarith
      have h := h_min (-z) hnz hnzx
      rw [Dyadic.coe_real_neg] at h; linarith

/-- `IsFaithfulRound` is exactly "round-down or round-up", phrased via the
directed `RoundsFinite` specs. This lets the round-to-nearest machinery work
with `RoundsFinite .toNegative/.toPositive` while the `.nearest` spec hands
out an `IsFaithfulRound`. -/
theorem isFaithfulRound_iff_directed {F : FiniteFormat} {x : ℝ} {y : Dyadic} :
    IsFaithfulRound F x y ↔
      RoundsFinite F .toNegative x y ∨ RoundsFinite F .toPositive x y := by
  unfold IsFaithfulRound RoundsFinite
  constructor
  · rintro (⟨hm, h_le, h_max⟩ | ⟨hm, h_le, h_min⟩)
    · exact Or.inl ⟨hm, h_le, h_max⟩
    · exact Or.inr ⟨hm, h_le, h_min⟩
  · rintro (⟨hm, h_le, h_max⟩ | ⟨hm, h_le, h_min⟩)
    · exact Or.inl ⟨hm, h_le, h_max⟩
    · exact Or.inr ⟨hm, h_le, h_min⟩

/-- If `x ∈ F` and `y` is the RTO-rounding of `x` in `F`, then `y = x`. -/
theorem RoundsFinite.toOdd_unique_of_mem {F : FiniteFormat} {x : Dyadic}
    (hx : x ∈ F) {y : Dyadic} (h : RoundsFinite F .toOdd (x : ℝ) y) : y = x := by
  obtain ⟨_, hadj, _⟩ := h
  rcases hadj with ⟨-, hyx, hmax⟩ | ⟨-, hxy, hmin⟩
  · -- round-down: (y:ℝ) ≤ (x:ℝ) and y is largest such
    have hxy : (x : ℝ) ≤ (y : ℝ) := hmax x hx (le_refl _)
    exact (Dyadic.coe_real_inj y x).mp (le_antisymm hyx hxy)
  · -- round-up: (x:ℝ) ≤ (y:ℝ) and y is smallest such
    have hyx : (y : ℝ) ≤ (x : ℝ) := hmin x hx (le_refl _)
    exact (Dyadic.coe_real_inj y x).mp (le_antisymm hyx hxy)

/-- A representable value is its own faithful rounding: `d` is the largest
`F`-element `≤ d` (the round-down disjunct). -/
theorem isFaithfulRound_self {F : FiniteFormat} {d : Dyadic} (hd : d ∈ F) :
    IsFaithfulRound F (d : ℝ) d :=
  Or.inl ⟨hd, le_rfl, fun _ _ hz => hz⟩

/-- RTZ fixes a representable value. -/
theorem RoundsFinite.toZero_self {F : FiniteFormat} {d : Dyadic} (hd : d ∈ F) :
    RoundsFinite F .toZero (d : ℝ) d :=
  ⟨hd, le_refl _, mul_self_nonneg _, fun _ _ hv_bnd _ => hv_bnd⟩

/-- RAZ fixes a representable value. -/
theorem RoundsFinite.awayZero_self {F : FiniteFormat} {d : Dyadic} (hd : d ∈ F) :
    RoundsFinite F .awayZero (d : ℝ) d :=
  ⟨hd, le_refl _, mul_self_nonneg _, fun _ _ hv_bnd _ => hv_bnd⟩

/-- RTO fixes a representable value. -/
theorem RoundsFinite.toOdd_self {F : FiniteFormat} {d : Dyadic} (hd : d ∈ F) :
    RoundsFinite F .toOdd (d : ℝ) d :=
  ⟨hd, isFaithfulRound_self hd, fun h => absurd rfl h⟩

/-- Two reals with equal magnitude and a common sign are equal. -/
private theorem eq_of_abs_eq_of_mul_nonneg {a b : ℝ}
    (habs : |a| = |b|) (hsign : 0 ≤ a * b) : a = b := by
  rcases abs_eq_abs.mp habs with h | h
  · exact h
  · -- `a = -b` forces `b = 0` (else the product is strictly negative), so `a = b`.
    subst h
    have hbb : b * b = 0 :=
      le_antisymm (by nlinarith) (mul_self_nonneg b)
    have hb : b = 0 := mul_self_eq_zero.mp hbb
    rw [hb]; ring

/-- **Rounding fixes representable values** — the spec-relational form of
Flocq's `round_generic` (paper Def. 7: `∀ f ∈ F, ◦(f) = f`). If `d ∈ F` and
`y` is the `rm`-rounding of `(d : ℝ)` in `F`, then `y = d`, for *any* mode `rm`
(including the degenerate `IsUndefined` formats — `RoundsFinite` never consults
`IsUndefined`). -/
theorem RoundsFinite.eq_of_mem {F : FiniteFormat} {rm : RoundingMode} {d : Dyadic}
    (hd : d ∈ F) {y : Dyadic} (h : RoundsFinite F rm (d : ℝ) y) : y = d := by
  obtain ⟨hyF, hcond⟩ := h
  have coe_inj : (y : ℝ) = (d : ℝ) → y = d := (Dyadic.coe_real_inj y d).mp
  cases rm with
  | toNegative =>
      obtain ⟨hle, hmax⟩ := hcond
      exact coe_inj (le_antisymm hle (hmax d hd le_rfl))
  | toPositive =>
      obtain ⟨hle, hmin⟩ := hcond
      exact coe_inj (le_antisymm (hmin d hd le_rfl) hle)
  | toZero =>
      obtain ⟨habs, hsign, hmax⟩ := hcond
      have hge : |(d : ℝ)| ≤ |(y : ℝ)| := hmax d hd le_rfl (mul_self_nonneg _)
      exact coe_inj (eq_of_abs_eq_of_mul_nonneg (le_antisymm habs hge) hsign)
  | awayZero =>
      obtain ⟨habs, hsign, hmin⟩ := hcond
      have hle : |(y : ℝ)| ≤ |(d : ℝ)| := hmin d hd le_rfl (mul_self_nonneg _)
      exact coe_inj (eq_of_abs_eq_of_mul_nonneg (le_antisymm hle habs) hsign)
  | toOdd =>
      exact RoundsFinite.toOdd_unique_of_mem hd ⟨hyF, hcond⟩
  | nearest tb =>
      cases tb with
      | toEven =>
          obtain ⟨_, hnear, _⟩ := hcond
          have hle := hnear d hd (isFaithfulRound_self hd)
          rw [sub_self, abs_zero] at hle
          have : (d : ℝ) - (y : ℝ) = 0 := abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
          exact coe_inj (by linarith)
      | awayZero =>
          obtain ⟨_, hnear, _⟩ := hcond
          have hle := hnear d hd (isFaithfulRound_self hd)
          rw [sub_self, abs_zero] at hle
          have : (d : ℝ) - (y : ℝ) = 0 := abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
          exact coe_inj (by linarith)

/-! ## Sign-symmetry of `Rounds`

For each rounding mode we relate rounding a real `x` under `rm` and overflow
table `O` to rounding `-x` under `rm'` and `O.neg`, with the result negated.
`rm'` is either `rm` itself (modes symmetric around zero) or its "flipped"
partner (`.toNegative` ↔ `.toPositive`). -/

/-- Sign-symmetry of `RoundsFinite` at mode `.toZero`. -/
theorem RoundsFinite.neg_toZero (F : FiniteFormat) (x : ℝ) (y : Dyadic) :
    RoundsFinite F .toZero x y ↔ RoundsFinite F .toZero (-x) (-y) := by
  unfold RoundsFinite
  simp only [Dyadic.coe_real_neg, abs_neg, neg_mul_neg, FiniteFormat.mem_neg_iff]
  refine and_congr_right' (and_congr_right' (and_congr_right' ?_))
  refine ⟨fun h z hz hzabs hzsign => ?_, fun h z hz hzabs hzsign => ?_⟩
  · have hnz : (-z) ∈ F := FiniteFormat.neg_mem hz
    have hnzabs : |((-z : Dyadic) : ℝ)| ≤ |x| := by
      rw [Dyadic.coe_real_neg, abs_neg]; exact hzabs
    have hnzsign : ((-z : Dyadic) : ℝ) * x ≥ 0 := by
      rw [Dyadic.coe_real_neg]; linarith
    have := h (-z) hnz hnzabs hnzsign
    rwa [Dyadic.coe_real_neg, abs_neg] at this
  · have hnz : (-z) ∈ F := FiniteFormat.neg_mem hz
    have hnzabs : |((-z : Dyadic) : ℝ)| ≤ |x| := by
      rw [Dyadic.coe_real_neg, abs_neg]; exact hzabs
    have hnzsign : ((-z : Dyadic) : ℝ) * (-x) ≥ 0 := by
      rw [Dyadic.coe_real_neg]; linarith
    have := h (-z) hnz hnzabs hnzsign
    rwa [Dyadic.coe_real_neg, abs_neg] at this

/-- Sign-symmetry: `.toNegative` ↔ `.toPositive` swaps under negation. -/
theorem RoundsFinite.neg_toNegative_iff_toPositive (F : FiniteFormat) (x : ℝ)
    (y : Dyadic) :
    RoundsFinite F .toNegative x y ↔ RoundsFinite F .toPositive (-x) (-y) := by
  unfold RoundsFinite
  simp only [Dyadic.coe_real_neg, FiniteFormat.mem_neg_iff]
  refine and_congr_right' ?_
  constructor
  · rintro ⟨h_le, h_max⟩
    refine ⟨by linarith, ?_⟩
    intro z hz hzx
    have hnz : (-z) ∈ F := FiniteFormat.neg_mem hz
    have hnzx : ((-z : Dyadic) : ℝ) ≤ x := by
      rw [Dyadic.coe_real_neg]; linarith
    have h := h_max (-z) hnz hnzx
    rw [Dyadic.coe_real_neg] at h
    linarith
  · rintro ⟨h_le, h_max⟩
    refine ⟨by linarith, ?_⟩
    intro z hz hzx
    have hnz : (-z) ∈ F := FiniteFormat.neg_mem hz
    have hnzx : -x ≤ ((-z : Dyadic) : ℝ) := by
      rw [Dyadic.coe_real_neg]; linarith
    have h := h_max (-z) hnz hnzx
    rw [Dyadic.coe_real_neg] at h
    linarith

/-- **Sign-symmetry combinator for `Rounds`.** Given that undefinedness matches
(`hu`) and that the finite spec is negation-symmetric (`hfin`), rounding a
real is negation-symmetric too, with the overflow table negated. Shared by the
`Rounds.neg_*` theorems. -/
theorem Rounds.neg_congr {F : FiniteFormat} {S : SpecialMap F.toFormat}
    {O : OverflowMap F.toFormat} (hF : F.NegClosed) {rm rm' : RoundingMode} {x : ℝ}
    (hu : F.IsUndefined rm ↔ F.IsUndefined rm')
    (hfin : ∀ y : Dyadic,
      RoundsFinite F.unbounded rm x y ↔ RoundsFinite F.unbounded rm' (-x) (-y))
    (r : RoundResult) :
    Rounds F S O rm (.finite x) r ↔ Rounds F S (O.neg hF) rm' (.finite (-x)) r.neg := by
  cases r with
  | undefined => exact hu
  | value v =>
    simp only [Rounds, RoundResult.neg_value]
    refine and_congr (not_congr hu) ⟨?_, ?_⟩
    · rintro ⟨y, hrf, ⟨hb, rfl⟩ | ⟨hb, rfl⟩⟩
      · exact ⟨-y, (hfin y).mp hrf, Or.inl ⟨by rwa [Format.boundOK_neg_iff], rfl⟩⟩
      · refine ⟨-y, (hfin y).mp hrf, Or.inr ⟨by rwa [Format.boundOK_neg_iff], ?_⟩⟩
        rw [OverflowMap.neg_map, decide_neg_lt_zero (ne_zero_of_not_boundOK hb),
          Bool.not_not]
    · rintro ⟨y, hrf, h⟩
      have hiff := hfin (-y)
      simp only [neg_neg] at hiff
      refine ⟨-y, hiff.mpr hrf, ?_⟩
      rcases h with ⟨hb, hv⟩ | ⟨hb, hv⟩
      · refine Or.inl ⟨by rwa [Format.boundOK_neg_iff], ?_⟩
        simpa using congrArg WithSpecial.neg hv
      · refine Or.inr ⟨by rwa [Format.boundOK_neg_iff], ?_⟩
        have hv' := congrArg WithSpecial.neg hv
        rw [WithSpecial.neg_neg, OverflowMap.neg_map, WithSpecial.neg_neg] at hv'
        rw [hv', decide_neg_lt_zero (ne_zero_of_not_boundOK hb)]

/-- `.toNegative` is RTP-symmetric under negation. -/
theorem Rounds.neg_toNegative_iff_toPositive (F : FiniteFormat) (S : SpecialMap F.toFormat)
    (O : OverflowMap F.toFormat) (hF : F.NegClosed) (x : ℝ) (r : RoundResult) :
    Rounds F S O .toNegative (.finite x) r ↔
      Rounds F S (O.neg hF) .toPositive (.finite (-x)) r.neg :=
  Rounds.neg_congr hF (by simp [FiniteFormat.IsUndefined])
    (RoundsFinite.neg_toNegative_iff_toPositive F.unbounded x) r

/-- Sign-symmetry of `RoundsFinite` at mode `.awayZero`. -/
theorem RoundsFinite.neg_awayZero (F : FiniteFormat) (x : ℝ) (y : Dyadic) :
    RoundsFinite F .awayZero x y ↔ RoundsFinite F .awayZero (-x) (-y) := by
  unfold RoundsFinite
  simp only [Dyadic.coe_real_neg, abs_neg, neg_mul_neg, FiniteFormat.mem_neg_iff]
  refine and_congr_right' (and_congr_right' (and_congr_right' ?_))
  refine ⟨fun h z hz hzabs hzsign => ?_, fun h z hz hzabs hzsign => ?_⟩
  · have hnz : (-z) ∈ F := FiniteFormat.neg_mem hz
    have hnzabs : |x| ≤ |((-z : Dyadic) : ℝ)| := by
      rw [Dyadic.coe_real_neg, abs_neg]; exact hzabs
    have hnzsign : ((-z : Dyadic) : ℝ) * x ≥ 0 := by
      rw [Dyadic.coe_real_neg]; linarith
    have := h (-z) hnz hnzabs hnzsign
    rwa [Dyadic.coe_real_neg, abs_neg] at this
  · have hnz : (-z) ∈ F := FiniteFormat.neg_mem hz
    have hnzabs : |x| ≤ |((-z : Dyadic) : ℝ)| := by
      rw [Dyadic.coe_real_neg, abs_neg]; exact hzabs
    have hnzsign : ((-z : Dyadic) : ℝ) * (-x) ≥ 0 := by
      rw [Dyadic.coe_real_neg]; linarith
    have := h (-z) hnz hnzabs hnzsign
    rwa [Dyadic.coe_real_neg, abs_neg] at this

/-- `.awayZero` is symmetric around zero. -/
theorem Rounds.neg_awayZero (F : FiniteFormat) (S : SpecialMap F.toFormat)
    (O : OverflowMap F.toFormat) (hF : F.NegClosed) (x : ℝ) (r : RoundResult) :
    Rounds F S O .awayZero (.finite x) r ↔ Rounds F S (O.neg hF) .awayZero (.finite (-x)) r.neg :=
  Rounds.neg_congr hF Iff.rfl (RoundsFinite.neg_awayZero F.unbounded x) r

/-- Sign-symmetry of `RoundsFinite` at mode `.nearest .awayZero`. -/
theorem RoundsFinite.neg_nearest_awayZero (F : FiniteFormat) (x : ℝ) (y : Dyadic) :
    RoundsFinite F (.nearest .awayZero) x y ↔
      RoundsFinite F (.nearest .awayZero) (-x) (-y) := by
  unfold RoundsFinite
  simp only [FiniteFormat.mem_neg_iff]
  refine and_congr_right' ?_
  rw [← IsFaithfulRound.neg_iff]
  refine and_congr_right' (and_congr ?_ ?_)
  · constructor
    · intro h z hz hfr_z
      have hnz : (-z) ∈ F := FiniteFormat.neg_mem hz
      have hfr_nz : IsFaithfulRound F x (-z) :=
        (IsFaithfulRound.neg_iff F x (-z)).mpr (by simpa)
      have hh := h (-z) hnz hfr_nz
      change |(-x) - ((-y : Dyadic) : ℝ)| ≤ |(-x) - (z : ℝ)|
      rw [Dyadic.coe_real_neg, neg_sub_neg_abs, abs_neg_sub_dyadic]
      exact hh
    · intro h z hz hfr_z
      have hnz : (-z) ∈ F := FiniteFormat.neg_mem hz
      have hfr_nz : IsFaithfulRound F (-x) (-z) :=
        (IsFaithfulRound.neg_iff F x z).mp hfr_z
      have hh := h (-z) hnz hfr_nz
      rw [Dyadic.coe_real_neg, Dyadic.coe_real_neg, neg_sub_neg_abs, neg_sub_neg_abs] at hh
      exact hh
  · constructor
    · intro h z hz hfr_z hzne heq
      have hnz : (-z) ∈ F := FiniteFormat.neg_mem hz
      have hfr_nz : IsFaithfulRound F x (-z) :=
        (IsFaithfulRound.neg_iff F x (-z)).mpr (by simpa)
      have hne : (-z) ≠ y := fun hye => hzne (neg_eq_iff_eq_neg.mp hye)
      have heq' : |x - (y : ℝ)| = |x - ((-z : Dyadic) : ℝ)| := by
        rw [Dyadic.coe_real_neg, neg_sub_neg_abs] at heq
        rw [abs_neg_sub_dyadic] at heq
        exact heq
      have hh := h (-z) hnz hfr_nz hne heq'
      change |(z : ℝ)| ≤ |((-y : Dyadic) : ℝ)|
      rw [Dyadic.coe_real_neg] at hh
      rw [abs_neg] at hh
      rw [Dyadic.coe_real_neg, abs_neg]
      exact hh
    · intro h z hz hfr_z hzne heq
      have hnz : (-z) ∈ F := FiniteFormat.neg_mem hz
      have hfr_nz : IsFaithfulRound F (-x) (-z) :=
        (IsFaithfulRound.neg_iff F x z).mp hfr_z
      have hne : (-z) ≠ -y := fun hye => hzne (neg_inj.mp hye)
      have heq' : |(-x) - ((-y : Dyadic) : ℝ)| = |(-x) - ((-z : Dyadic) : ℝ)| := by
        rw [Dyadic.coe_real_neg, Dyadic.coe_real_neg, neg_sub_neg_abs, neg_sub_neg_abs]
        exact heq
      have hh := h (-z) hnz hfr_nz hne heq'
      rw [Dyadic.coe_real_neg, Dyadic.coe_real_neg, abs_neg, abs_neg] at hh
      exact hh

/-- `.nearest .awayZero` is symmetric around zero. -/
theorem Rounds.neg_nearest_awayZero (F : FiniteFormat) (S : SpecialMap F.toFormat)
    (O : OverflowMap F.toFormat) (hF : F.NegClosed) (x : ℝ) (r : RoundResult) :
    Rounds F S O (.nearest .awayZero) (.finite x) r ↔
      Rounds F S (O.neg hF) (.nearest .awayZero) (.finite (-x)) r.neg :=
  Rounds.neg_congr hF Iff.rfl (RoundsFinite.neg_nearest_awayZero F.unbounded x) r

/-- Sign-symmetry of `RoundsFinite` at mode `.toOdd`. -/
theorem RoundsFinite.neg_toOdd (F : FiniteFormat) (x : ℝ) (y : Dyadic) :
    RoundsFinite F .toOdd x y ↔ RoundsFinite F .toOdd (-x) (-y) := by
  unfold RoundsFinite
  simp only [FiniteFormat.mem_neg_iff, ParityFormat.IsOdd.neg_iff, Dyadic.coe_real_neg,
    ne_eq, neg_inj]
  rw [← IsFaithfulRound.neg_iff]

/-- Sign-symmetry of `RoundsFinite` at mode `.nearest .toEven`. -/
theorem RoundsFinite.neg_nearest_toEven (F : FiniteFormat) (x : ℝ) (y : Dyadic) :
    RoundsFinite F (.nearest .toEven) x y ↔
      RoundsFinite F (.nearest .toEven) (-x) (-y) := by
  unfold RoundsFinite
  simp only [FiniteFormat.mem_neg_iff, ParityFormat.IsEven.neg_iff]
  refine and_congr_right' ?_
  rw [← IsFaithfulRound.neg_iff]
  refine and_congr_right' (and_congr ?_ ?_)
  · constructor
    · intro h z hz hfr_z
      have hnz : (-z) ∈ F := FiniteFormat.neg_mem hz
      have hfr_nz : IsFaithfulRound F x (-z) :=
        (IsFaithfulRound.neg_iff F x (-z)).mpr (by simpa)
      have hh := h (-z) hnz hfr_nz
      change |(-x) - ((-y : Dyadic) : ℝ)| ≤ |(-x) - (z : ℝ)|
      rw [Dyadic.coe_real_neg, neg_sub_neg_abs, abs_neg_sub_dyadic]
      exact hh
    · intro h z hz hfr_z
      have hnz : (-z) ∈ F := FiniteFormat.neg_mem hz
      have hfr_nz : IsFaithfulRound F (-x) (-z) :=
        (IsFaithfulRound.neg_iff F x z).mp hfr_z
      have hh := h (-z) hnz hfr_nz
      rw [Dyadic.coe_real_neg, Dyadic.coe_real_neg, neg_sub_neg_abs, neg_sub_neg_abs] at hh
      exact hh
  · constructor
    · intro h_impl ⟨z, hz, hfr_z, hzne, heq⟩
      apply h_impl
      refine ⟨-z, FiniteFormat.neg_mem hz,
        (IsFaithfulRound.neg_iff F x (-z)).mpr (by simpa), ?_, ?_⟩
      · intro hye; apply hzne; exact neg_eq_iff_eq_neg.mp hye
      · rw [Dyadic.coe_real_neg, neg_sub_neg_abs] at heq
        rw [abs_neg_sub_dyadic] at heq
        exact heq
    · intro h_impl ⟨z, hz, hfr_z, hzne, heq⟩
      apply h_impl
      refine ⟨-z, FiniteFormat.neg_mem hz,
        (IsFaithfulRound.neg_iff F x z).mp hfr_z, ?_, ?_⟩
      · intro hye; apply hzne; exact neg_inj.mp hye
      · change |(-x) - ((-y : Dyadic) : ℝ)| = |(-x) - ((-z : Dyadic) : ℝ)|
        rw [Dyadic.coe_real_neg, Dyadic.coe_real_neg, neg_sub_neg_abs, neg_sub_neg_abs]
        exact heq

/-- `.nearest .toEven` is symmetric around zero. -/
theorem Rounds.neg_nearest_toEven (F : FiniteFormat) (S : SpecialMap F.toFormat)
    (O : OverflowMap F.toFormat) (hF : F.NegClosed) (x : ℝ) (r : RoundResult) :
    Rounds F S O (.nearest .toEven) (.finite x) r ↔
      Rounds F S (O.neg hF) (.nearest .toEven) (.finite (-x)) r.neg :=
  Rounds.neg_congr hF Iff.rfl (RoundsFinite.neg_nearest_toEven F.unbounded x) r

/-- `.toOdd` is symmetric around zero. -/
theorem Rounds.neg_toOdd (F : FiniteFormat) (S : SpecialMap F.toFormat)
    (O : OverflowMap F.toFormat) (hF : F.NegClosed) (x : ℝ) (r : RoundResult) :
    Rounds F S O .toOdd (.finite x) r ↔ Rounds F S (O.neg hF) .toOdd (.finite (-x)) r.neg :=
  Rounds.neg_congr hF Iff.rfl (RoundsFinite.neg_toOdd F.unbounded x) r

/-- `.toZero` is symmetric around zero. -/
theorem Rounds.neg_toZero (F : FiniteFormat) (S : SpecialMap F.toFormat)
    (O : OverflowMap F.toFormat) (hF : F.NegClosed) (x : ℝ) (r : RoundResult) :
    Rounds F S O .toZero (.finite x) r ↔ Rounds F S (O.neg hF) .toZero (.finite (-x)) r.neg :=
  Rounds.neg_congr hF Iff.rfl (RoundsFinite.neg_toZero F.unbounded x) r

/-- Nearest rounding is invariant under joint negation (both tie-breaks). -/
theorem RoundsFinite.neg_nearest (F : FiniteFormat) (tb : TieBreak) (a : ℝ) (v : Dyadic) :
    RoundsFinite F (.nearest tb) a v ↔ RoundsFinite F (.nearest tb) (-a) (-v) := by
  cases tb with
  | toEven => exact RoundsFinite.neg_nearest_toEven F a v
  | awayZero => exact RoundsFinite.neg_nearest_awayZero F a v

/-! ## Directed-vs-zero-relative mode equivalences

For nonnegative `x`, RTP coincides with RAZ and RTN with RTZ; for nonpositive
`x`, the relationships swap. These let callers reduce RTP/RTN to RTZ/RAZ
when the sign of `x` is known. -/

private lemma dyadic_coe_zero : ((0 : Dyadic) : ℝ) = 0 := by push_cast; rfl

theorem RoundsFinite.toPositive_iff_awayZero_of_nonneg
    (F : FiniteFormat) {x : ℝ} (hx : 0 ≤ x) (y : Dyadic) :
    RoundsFinite F .toPositive x y ↔ RoundsFinite F .awayZero x y := by
  unfold RoundsFinite
  refine and_congr_right' ?_
  constructor
  · rintro ⟨hxy, h_min⟩
    have hy_nn : (0 : ℝ) ≤ (y : ℝ) := le_trans hx hxy
    refine ⟨?_, mul_nonneg hy_nn hx, ?_⟩
    · rw [abs_of_nonneg hx, abs_of_nonneg hy_nn]; exact hxy
    · intro z hz hxz hzx
      rw [abs_of_nonneg hx] at hxz
      rcases eq_or_lt_of_le hx with rfl | hx_pos
      · have h_zero_in : (0 : Dyadic) ∈ F := FiniteFormat.zero_mem F
        have hy_le_zero := h_min 0 h_zero_in (by rw [dyadic_coe_zero])
        rw [dyadic_coe_zero] at hy_le_zero
        have hy_eq : (y : ℝ) = 0 := le_antisymm hy_le_zero hy_nn
        rw [hy_eq, abs_zero]; exact abs_nonneg _
      · have hz_nn : (0 : ℝ) ≤ (z : ℝ) := by
          by_contra hz_neg
          rw [not_le] at hz_neg
          linarith [mul_neg_of_neg_of_pos hz_neg hx_pos]
        rw [abs_of_nonneg hz_nn] at hxz
        rw [abs_of_nonneg hy_nn, abs_of_nonneg hz_nn]
        exact h_min z hz hxz
  · rintro ⟨h_xa, h_zx, h_min⟩
    rw [abs_of_nonneg hx] at h_xa
    rcases eq_or_lt_of_le hx with rfl | hx_pos
    · have h_zero_in : (0 : Dyadic) ∈ F := FiniteFormat.zero_mem F
      have h := h_min 0 h_zero_in
        (by rw [dyadic_coe_zero])
        (by rw [dyadic_coe_zero]; simp)
      rw [dyadic_coe_zero, abs_zero] at h
      have hy_abs_zero : |(y : ℝ)| = 0 := le_antisymm h (abs_nonneg _)
      have hy_eq : (y : ℝ) = 0 := abs_eq_zero.mp hy_abs_zero
      refine ⟨by rw [hy_eq], ?_⟩
      intro z hz hxz
      rw [hy_eq]; exact hxz
    · have hy_nn : (0 : ℝ) ≤ (y : ℝ) :=
        (mul_nonneg_iff_of_pos_right hx_pos).mp h_zx
      rw [abs_of_nonneg hy_nn] at h_xa
      refine ⟨h_xa, ?_⟩
      intro z hz hxz
      have hz_nn : (0 : ℝ) ≤ (z : ℝ) := le_trans hx_pos.le hxz
      have h := h_min z hz
        (by rw [abs_of_nonneg hx, abs_of_nonneg hz_nn]; exact hxz)
        (mul_nonneg hz_nn hx_pos.le)
      rw [abs_of_nonneg hy_nn, abs_of_nonneg hz_nn] at h
      exact h

theorem RoundsFinite.toPositive_iff_toZero_of_nonpos
    (F : FiniteFormat) {x : ℝ} (hx : x ≤ 0) (y : Dyadic) :
    RoundsFinite F .toPositive x y ↔ RoundsFinite F .toZero x y := by
  unfold RoundsFinite
  refine and_congr_right' ?_
  constructor
  · rintro ⟨hxy, h_min⟩
    have h_zero_in : (0 : Dyadic) ∈ F := FiniteFormat.zero_mem F
    have hy_le_zero : (y : ℝ) ≤ 0 := by
      have := h_min 0 h_zero_in (by rw [dyadic_coe_zero]; exact hx)
      rwa [dyadic_coe_zero] at this
    refine ⟨?_, ?_, ?_⟩
    · rw [abs_of_nonpos hx, abs_of_nonpos hy_le_zero]; linarith
    · nlinarith
    · intro z hz hzabs hzx
      rw [abs_of_nonpos hx] at hzabs
      rcases eq_or_lt_of_le hx with hx0 | hx_neg
      · subst hx0
        have hy_eq : (y : ℝ) = 0 := le_antisymm hy_le_zero hxy
        rw [hy_eq, abs_zero]
        have h_z_zero : (z : ℝ) = 0 := by
          have : |(z : ℝ)| ≤ 0 := by linarith
          have := abs_nonneg (z : ℝ)
          have : |(z : ℝ)| = 0 := by linarith
          exact abs_eq_zero.mp this
        rw [h_z_zero, abs_zero]
      · have hz_nonpos : (z : ℝ) ≤ 0 := by
          by_contra hz_pos
          rw [not_le] at hz_pos
          have : (z : ℝ) * x < 0 := mul_neg_of_pos_of_neg hz_pos hx_neg
          linarith
        rw [abs_of_nonpos hz_nonpos] at hzabs
        have hxz : x ≤ (z : ℝ) := by linarith
        have h_y_le_z := h_min z hz hxz
        rw [abs_of_nonpos hy_le_zero, abs_of_nonpos hz_nonpos]
        linarith
  · rintro ⟨hya, h_yx, h_min⟩
    rw [abs_of_nonpos hx] at hya
    rcases eq_or_lt_of_le hx with hx0 | hx_neg
    · subst hx0
      have hy_abs_zero : |(y : ℝ)| ≤ 0 := by linarith
      have hy_eq : (y : ℝ) = 0 := by
        have hnn := abs_nonneg (y : ℝ)
        have habs : |(y : ℝ)| = 0 := le_antisymm hy_abs_zero hnn
        exact abs_eq_zero.mp habs
      refine ⟨by rw [hy_eq], ?_⟩
      intro z hz hxz
      rw [hy_eq]; exact hxz
    · have hy_le_zero : (y : ℝ) ≤ 0 := by
        by_contra h_pos
        rw [not_le] at h_pos
        have : (y : ℝ) * x < 0 := mul_neg_of_pos_of_neg h_pos hx_neg
        linarith
      rw [abs_of_nonpos hy_le_zero] at hya
      refine ⟨by linarith, ?_⟩
      intro z hz hxz
      by_cases hz_np : (z : ℝ) ≤ 0
      · have hzabs : |(z : ℝ)| ≤ |x| := by
          rw [abs_of_nonpos hx, abs_of_nonpos hz_np]; linarith
        have hzx : (z : ℝ) * x ≥ 0 := by
          have : (z : ℝ) * x = (-(z : ℝ)) * (-x) := by ring
          rw [this]
          exact mul_nonneg (neg_nonneg.mpr hz_np) (neg_nonneg.mpr hx_neg.le)
        have h := h_min z hz hzabs hzx
        rw [abs_of_nonpos hy_le_zero, abs_of_nonpos hz_np] at h
        linarith
      · push Not at hz_np
        linarith

/-- For `x ≤ 0`, rounding toward `−∞` coincides with rounding away from zero
(both move to the more-negative side). Sign-mirror of
`toPositive_iff_awayZero_of_nonneg`, derived via joint negation. -/
theorem RoundsFinite.toNegative_iff_awayZero_of_nonpos
    (F : FiniteFormat) {x : ℝ} (hx : x ≤ 0) (y : Dyadic) :
    RoundsFinite F .toNegative x y ↔ RoundsFinite F .awayZero x y :=
  calc RoundsFinite F .toNegative x y
      ↔ RoundsFinite F .toPositive (-x) (-y) :=
        RoundsFinite.neg_toNegative_iff_toPositive F x y
    _ ↔ RoundsFinite F .awayZero (-x) (-y) :=
        RoundsFinite.toPositive_iff_awayZero_of_nonneg F (neg_nonneg.mpr hx) (-y)
    _ ↔ RoundsFinite F .awayZero x y := (RoundsFinite.neg_awayZero F x y).symm

/-- For `0 ≤ x`, rounding toward `−∞` coincides with rounding toward zero
(both move down). Sign-mirror of `toPositive_iff_toZero_of_nonpos`. -/
theorem RoundsFinite.toNegative_iff_toZero_of_nonneg
    (F : FiniteFormat) {x : ℝ} (hx : 0 ≤ x) (y : Dyadic) :
    RoundsFinite F .toNegative x y ↔ RoundsFinite F .toZero x y :=
  calc RoundsFinite F .toNegative x y
      ↔ RoundsFinite F .toPositive (-x) (-y) :=
        RoundsFinite.neg_toNegative_iff_toPositive F x y
    _ ↔ RoundsFinite F .toZero (-x) (-y) :=
        RoundsFinite.toPositive_iff_toZero_of_nonpos F (neg_nonpos.mpr hx) (-y)
    _ ↔ RoundsFinite F .toZero x y := (RoundsFinite.neg_toZero F x y).symm

/-- **Result-preserving congruence for `Rounds`.** Companion to `Rounds.neg_congr`
for the same-`x` mode equivalences: matching undefinedness (`hu`) and a same-input
`RoundsFinite` equivalence (`hfin`) lift to `Rounds`. -/
theorem Rounds.congr_of_roundsFinite {F : FiniteFormat} {S : SpecialMap F.toFormat}
    {O : OverflowMap F.toFormat} {rm rm' : RoundingMode} {x : ℝ}
    (hu : F.IsUndefined rm ↔ F.IsUndefined rm')
    (hfin : ∀ y : Dyadic,
      RoundsFinite F.unbounded rm x y ↔ RoundsFinite F.unbounded rm' x y)
    (r : RoundResult) :
    Rounds F S O rm (.finite x) r ↔ Rounds F S O rm' (.finite x) r := by
  cases r with
  | undefined => exact hu
  | value v =>
    simp only [Rounds]
    exact and_congr (not_congr hu)
      ⟨fun ⟨y, h, rest⟩ => ⟨y, (hfin y).mp h, rest⟩,
       fun ⟨y, h, rest⟩ => ⟨y, (hfin y).mpr h, rest⟩⟩

theorem Rounds.toPositive_iff_awayZero_of_nonneg
    (F : FiniteFormat) (S : SpecialMap F.toFormat) (O : OverflowMap F.toFormat)
    {x : ℝ} (hx : 0 ≤ x) (r : RoundResult) :
    Rounds F S O .toPositive (.finite x) r ↔ Rounds F S O .awayZero (.finite x) r :=
  Rounds.congr_of_roundsFinite (by simp [FiniteFormat.IsUndefined])
    (RoundsFinite.toPositive_iff_awayZero_of_nonneg F.unbounded hx) r

theorem Rounds.toPositive_iff_toZero_of_nonpos
    (F : FiniteFormat) (S : SpecialMap F.toFormat) (O : OverflowMap F.toFormat)
    {x : ℝ} (hx : x ≤ 0) (r : RoundResult) :
    Rounds F S O .toPositive (.finite x) r ↔ Rounds F S O .toZero (.finite x) r :=
  Rounds.congr_of_roundsFinite (by simp [FiniteFormat.IsUndefined])
    (RoundsFinite.toPositive_iff_toZero_of_nonpos F.unbounded hx) r

theorem Rounds.toNegative_iff_toZero_of_nonneg
    (F : FiniteFormat) (S : SpecialMap F.toFormat) (O : OverflowMap F.toFormat)
    {x : ℝ} (hx : 0 ≤ x) (r : RoundResult) :
    Rounds F S O .toNegative (.finite x) r ↔ Rounds F S O .toZero (.finite x) r :=
  Rounds.congr_of_roundsFinite (by simp [FiniteFormat.IsUndefined])
    (RoundsFinite.toNegative_iff_toZero_of_nonneg F.unbounded hx) r

theorem Rounds.toNegative_iff_awayZero_of_nonpos
    (F : FiniteFormat) (S : SpecialMap F.toFormat) (O : OverflowMap F.toFormat)
    {x : ℝ} (hx : x ≤ 0) (r : RoundResult) :
    Rounds F S O .toNegative (.finite x) r ↔ Rounds F S O .awayZero (.finite x) r :=
  Rounds.congr_of_roundsFinite (by simp [FiniteFormat.IsUndefined])
    (RoundsFinite.toNegative_iff_awayZero_of_nonpos F.unbounded hx) r


/-! ### Uniqueness for the directed modes -/

/-- Two largest `F`-elements `≤ x` coincide (Flocq `Rnd_DN_pt_unique`). -/
theorem RoundsFinite.unique_toNegative {F : FiniteFormat} {x : ℝ} {y₁ y₂ : Dyadic}
    (h₁ : RoundsFinite F .toNegative x y₁) (h₂ : RoundsFinite F .toNegative x y₂) :
    y₁ = y₂ := by
  obtain ⟨hm₁, hle₁, hmax₁⟩ := h₁
  obtain ⟨hm₂, hle₂, hmax₂⟩ := h₂
  exact Dyadic.ext_real (le_antisymm (hmax₂ y₁ hm₁ hle₁) (hmax₁ y₂ hm₂ hle₂))

/-- Flocq `Rnd_UP_pt_unique`. -/
theorem RoundsFinite.unique_toPositive {F : FiniteFormat} {x : ℝ} {y₁ y₂ : Dyadic}
    (h₁ : RoundsFinite F .toPositive x y₁) (h₂ : RoundsFinite F .toPositive x y₂) :
    y₁ = y₂ := by
  obtain ⟨hm₁, hge₁, hmin₁⟩ := h₁
  obtain ⟨hm₂, hge₂, hmin₂⟩ := h₂
  exact Dyadic.ext_real (le_antisymm (hmin₁ y₂ hm₂ hge₂) (hmin₂ y₁ hm₁ hge₁))

/-- RTZ agrees with round-down on `0 ≤ x` and round-up on `x ≤ 0`. -/
theorem RoundsFinite.unique_toZero {F : FiniteFormat} {x : ℝ} {y₁ y₂ : Dyadic}
    (h₁ : RoundsFinite F .toZero x y₁) (h₂ : RoundsFinite F .toZero x y₂) :
    y₁ = y₂ := by
  rcases le_total 0 x with hx | hx
  · exact unique_toNegative
      ((RoundsFinite.toNegative_iff_toZero_of_nonneg F hx y₁).mpr h₁)
      ((RoundsFinite.toNegative_iff_toZero_of_nonneg F hx y₂).mpr h₂)
  · exact unique_toPositive
      ((RoundsFinite.toPositive_iff_toZero_of_nonpos F hx y₁).mpr h₁)
      ((RoundsFinite.toPositive_iff_toZero_of_nonpos F hx y₂).mpr h₂)

/-- Sign-mirror of `unique_toZero`. -/
theorem RoundsFinite.unique_awayZero {F : FiniteFormat} {x : ℝ} {y₁ y₂ : Dyadic}
    (h₁ : RoundsFinite F .awayZero x y₁) (h₂ : RoundsFinite F .awayZero x y₂) :
    y₁ = y₂ := by
  rcases le_total 0 x with hx | hx
  · exact unique_toPositive
      ((RoundsFinite.toPositive_iff_awayZero_of_nonneg F hx y₁).mpr h₁)
      ((RoundsFinite.toPositive_iff_awayZero_of_nonneg F hx y₂).mpr h₂)
  · exact unique_toNegative
      ((RoundsFinite.toNegative_iff_awayZero_of_nonpos F hx y₁).mpr h₁)
      ((RoundsFinite.toNegative_iff_awayZero_of_nonpos F hx y₂).mpr h₂)

/-! ### Every mode rounds faithfully -/

/-- Whatever the mode, the rounded value is the round-down or the round-up of
`x`. `isFaithfulRound_iff_directed` reads the result back as the two-sided
disjunction (Flocq `Zrnd_DN_or_UP`, `Rnd_N_pt_DN_or_UP`). -/
theorem RoundsFinite.isFaithfulRound {F : FiniteFormat} {rm : RoundingMode} {x : ℝ}
    {y : Dyadic} (h : RoundsFinite F rm x y) :
    IsFaithfulRound F x y := by
  cases rm with
  | toNegative => exact isFaithfulRound_iff_directed.mpr (Or.inl h)
  | toPositive => exact isFaithfulRound_iff_directed.mpr (Or.inr h)
  | toZero =>
      rcases le_total 0 x with hx | hx
      · exact isFaithfulRound_iff_directed.mpr
          (Or.inl ((RoundsFinite.toNegative_iff_toZero_of_nonneg F hx y).mpr h))
      · exact isFaithfulRound_iff_directed.mpr
          (Or.inr ((RoundsFinite.toPositive_iff_toZero_of_nonpos F hx y).mpr h))
  | awayZero =>
      rcases le_total 0 x with hx | hx
      · exact isFaithfulRound_iff_directed.mpr
          (Or.inr ((RoundsFinite.toPositive_iff_awayZero_of_nonneg F hx y).mpr h))
      · exact isFaithfulRound_iff_directed.mpr
          (Or.inl ((RoundsFinite.toNegative_iff_awayZero_of_nonpos F hx y).mpr h))
  | toOdd => exact h.2.1
  | nearest tb => cases tb <;> exact h.2.1

/-- Every mode sends `0` to `0` (Flocq `round_0`),
since `0` lies in every format. -/
theorem RoundsFinite.eq_zero_of_zero {F : FiniteFormat} {rm : RoundingMode}
    {y : Dyadic} (h : RoundsFinite F rm 0 y) : y = 0 :=
  RoundsFinite.eq_of_mem (F.zero_mem) (by rwa [Dyadic.coe_real_zero])

/-- Two *distinct* faithful roundings sit on opposite sides of `x`; same-side
pairs collapse by uniqueness. The case split behind `unique_nearest`. -/
theorem IsFaithfulRound.opposite_sides_of_ne {F : FiniteFormat} {x : ℝ}
    {a b : Dyadic} (ha : IsFaithfulRound F x a) (hb : IsFaithfulRound F x b)
    (hab : a ≠ b) :
    (RoundsFinite F .toNegative x a ∧ RoundsFinite F .toPositive x b) ∨
    (RoundsFinite F .toNegative x b ∧ RoundsFinite F .toPositive x a) := by
  rcases isFaithfulRound_iff_directed.mp ha with hda | hua <;>
    rcases isFaithfulRound_iff_directed.mp hb with hdb | hub
  · exact absurd (RoundsFinite.unique_toNegative hda hdb) hab
  · exact Or.inl ⟨hda, hub⟩
  · exact Or.inr ⟨hdb, hua⟩
  · exact absurd (RoundsFinite.unique_toPositive hua hub) hab

/-! ### Reading the directed roundings off the grid

Stated as *the grid point satisfies the spec*, so uniqueness turns each into an
equation (Flocq `round_DN_eq` / `round_UP_eq`). -/

/-- The floor grid point at the canonical exponent **is** the round-down. -/
theorem RoundsFinite.toNegative_floor (F : FiniteFormat) (x : ℝ) :
    RoundsFinite F.unbounded .toNegative x
      (Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋ (F.canonicalExp x)) := by
  set e := F.canonicalExp x
  set c := ⌊x * (2 : ℝ) ^ (-e)⌋
  set y : Dyadic := Dyadic.ofIntZpow c e
  have h_y_real : (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ e := Dyadic.coe_ofIntZpow c e
  have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have h_c_bound : ∀ {p : ℕ}, F.p = (p : Prec) →
      |c| ≤ (2 : ℤ) ^ p := fun hp => by
    apply abs_floor_le_of_abs_lt
    push_cast; exact floor_mantissa_lt hp
  obtain ⟨h_prec, h_quant, h_bnd⟩ :=
    ofIntZpow_mem_unbounded F (fun hexp => F.exp_le_canonicalExp x hexp) h_c_bound
  refine ⟨⟨h_prec, h_quant, h_bnd⟩, ?_, ?_⟩
  · rw [h_y_real, ← mul_zpow_neg_self x e]
    exact mul_le_mul_of_nonneg_right (Int.floor_le _) h_2e_pos.le
  · intro z hz_mem hz_le_x
    obtain ⟨hz_prec, hz_quant, _⟩ := hz_mem
    rw [h_y_real]
    exact floor_minimality F x hz_prec hz_quant hz_le_x

/-- The ceiling grid point at the canonical exponent **is** the round-up. -/
theorem RoundsFinite.toPositive_ceil (F : FiniteFormat) (x : ℝ) :
    RoundsFinite F.unbounded .toPositive x
      (Dyadic.ofIntZpow ⌈x * (2 : ℝ) ^ (-(F.canonicalExp x))⌉ (F.canonicalExp x)) := by
  set e := F.canonicalExp x
  set c := ⌈x * (2 : ℝ) ^ (-e)⌉
  set y : Dyadic := Dyadic.ofIntZpow c e
  have h_y_real : (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ e := Dyadic.coe_ofIntZpow c e
  have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have h_c_bound : ∀ {p : ℕ}, F.p = (p : Prec) →
      |c| ≤ (2 : ℤ) ^ p := fun hp => by
    apply abs_ceil_le_of_abs_lt
    push_cast; exact floor_mantissa_lt hp
  obtain ⟨h_prec, h_quant, h_bnd⟩ :=
    ofIntZpow_mem_unbounded F (fun hexp => F.exp_le_canonicalExp x hexp) h_c_bound
  refine ⟨⟨h_prec, h_quant, h_bnd⟩, ?_, ?_⟩
  · rw [h_y_real, ← mul_zpow_neg_self x e]
    exact mul_le_mul_of_nonneg_right (Int.le_ceil _) h_2e_pos.le
  · intro z hz_mem hx_le_z
    obtain ⟨hz_prec, hz_quant, _⟩ := hz_mem
    rw [h_y_real]
    exact ceil_minimality F x hz_prec hz_quant hx_le_z

/-- Any round-down of `x` *is* that floor grid point. -/
theorem RoundsFinite.toNegative_eq_floor (F : FiniteFormat) (x : ℝ) {y : Dyadic}
    (hy : RoundsFinite F.unbounded .toNegative x y) :
    y = Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋ (F.canonicalExp x) :=
  RoundsFinite.unique_toNegative hy (RoundsFinite.toNegative_floor F x)

/-- Any round-up of `x` *is* that ceiling grid point. -/
theorem RoundsFinite.toPositive_eq_ceil (F : FiniteFormat) (x : ℝ) {y : Dyadic}
    (hy : RoundsFinite F.unbounded .toPositive x y) :
    y = Dyadic.ofIntZpow ⌈x * (2 : ℝ) ^ (-(F.canonicalExp x))⌉ (F.canonicalExp x) :=
  RoundsFinite.unique_toPositive hy (RoundsFinite.toPositive_ceil F x)

/-! ### Uniqueness for RTO -/

/-- `Parity.neighbors_alternate`, stated over the round-down/round-up specs. -/
theorem isOdd_alternate_of_bracketing {F : FiniteFormat} {x : ℝ}
    (h : ¬ F.IsUndefined .toOdd) {y y' : Dyadic}
    (hy : RoundsFinite F.unbounded .toNegative x y)
    (hy' : RoundsFinite F.unbounded .toPositive x y')
    (hne : x ≠ (y : ℝ)) :
    ((F.toParityFormatOfToOdd h).IsOdd y' ↔
      ¬ (F.toParityFormatOfToOdd h).IsOdd y) := by
  -- `x = 0` would make `y` the round-down of `0`, hence `0 = x`.
  have hx_ne : x ≠ 0 := fun hx0 => hne (by
    have hy0 : RoundsFinite F.unbounded .toNegative 0 y := by rw [← hx0]; exact hy
    rw [hx0, RoundsFinite.eq_zero_of_zero hy0, Dyadic.coe_real_zero])
  set e := F.canonicalExp x with he
  set s := x * (2 : ℝ) ^ (-e) with hs
  have hy_eq : y = Dyadic.ofIntZpow ⌊s⌋ e := RoundsFinite.toNegative_eq_floor F x hy
  -- `x ≠ y` says exactly that `x` is off the grid, i.e. `⌊s⌋ ≠ s`.
  have h_lo_ne_s : (⌊s⌋ : ℝ) ≠ s := by
    intro hcon
    exact hne (by rw [hy_eq, Dyadic.coe_ofIntZpow, hcon, hs, mul_zpow_neg_self])
  -- Off the grid, the ceiling is the floor's successor.
  have h_ceil : ⌈s⌉ = ⌊s⌋ + 1 :=
    le_antisymm (Int.ceil_le_floor_add_one s)
      (Int.lt_ceil.mpr (lt_of_le_of_ne (Int.floor_le s) h_lo_ne_s))
  have hy'_eq : y' = Dyadic.ofIntZpow (⌊s⌋ + 1) e := by
    rw [RoundsFinite.toPositive_eq_ceil F x hy', h_ceil]
  rw [hy_eq, hy'_eq]
  exact toOdd_neighbors_alternate x h hx_ne h_lo_ne_s

/-- Matching sides collapse by directed uniqueness; the mixed case would need
both neighbours odd, which `isOdd_alternate_of_bracketing` forbids. -/
theorem RoundsFinite.unique_toOdd {F : FiniteFormat} {x : ℝ}
    (h : ¬ F.IsUndefined .toOdd) {y₁ y₂ : Dyadic}
    (h₁ : RoundsFinite F.unbounded .toOdd x y₁)
    (h₂ : RoundsFinite F.unbounded .toOdd x y₂) :
    y₁ = y₂ := by
  obtain ⟨-, hf₁, hp₁⟩ := h₁
  obtain ⟨-, hf₂, hp₂⟩ := h₂
  -- `a` rounds down, `b` rounds up. Symmetric, so proved once.
  have mixed : ∀ {a b : Dyadic},
      RoundsFinite F.unbounded .toNegative x a →
      RoundsFinite F.unbounded .toPositive x b →
      (x ≠ (a : ℝ) → ∃ F' : ParityFormat,
        F'.toFormat = F.unbounded.toFormat ∧ F'.IsOdd a) →
      (x ≠ (b : ℝ) → ∃ F' : ParityFormat,
        F'.toFormat = F.unbounded.toFormat ∧ F'.IsOdd b) →
      a = b := by
    intro a b hda hub hpa hpb
    obtain ⟨ha_mem, ha_le, ha_max⟩ := id hda
    obtain ⟨hb_mem, hb_ge, hb_min⟩ := id hub
    by_cases hxa : x = (a : ℝ)
    · exact Dyadic.ext_real (le_antisymm (hxa ▸ hb_ge) (hb_min a ha_mem hxa.le))
    by_cases hxb : x = (b : ℝ)
    · exact Dyadic.ext_real (le_antisymm (hxb ▸ ha_le) (ha_max b hb_mem hxb.ge))
    exfalso
    obtain ⟨Fa, hFa, hFa_odd⟩ := hpa hxa
    obtain ⟨Fb, hFb, hFb_odd⟩ := hpb hxb
    exact (isOdd_alternate_of_bracketing (F := F.unbounded) h hda hub hxa).mp
      ((ParityFormat.IsOdd_iff_of_toFormat_eq hFb b).mp hFb_odd)
      ((ParityFormat.IsOdd_iff_of_toFormat_eq hFa a).mp hFa_odd)
  rcases isFaithfulRound_iff_directed.mp hf₁ with hd₁ | hu₁ <;>
    rcases isFaithfulRound_iff_directed.mp hf₂ with hd₂ | hu₂
  · exact RoundsFinite.unique_toNegative hd₁ hd₂
  · exact mixed hd₁ hu₂ hp₁ hp₂
  · exact (mixed hd₂ hu₁ hp₂ hp₁).symm
  · exact RoundsFinite.unique_toPositive hu₁ hu₂

/-! ### Uniqueness for the nearest modes -/

/-- Two nearest roundings are equidistant from `x`, so if they differ they sit
on opposite sides and the tie-break must separate them. It cannot: `.toEven`
would need both neighbours even, and `.awayZero` equal magnitudes across zero,
forcing `x = 0` where both roundings are `0`. Flocq `Rnd_NG_pt_unique`. -/
theorem RoundsFinite.unique_nearest {F : FiniteFormat} {tb : TieBreak} {x : ℝ}
    (h : ¬ F.IsUndefined (.nearest tb)) {y₁ y₂ : Dyadic}
    (h₁ : RoundsFinite F.unbounded (.nearest tb) x y₁)
    (h₂ : RoundsFinite F.unbounded (.nearest tb) x y₂) :
    y₁ = y₂ := by
  -- A round-down and a round-up that are equidistant from `x` and distinct
  -- put `x` strictly between them; in particular `x` is neither of them, and
  -- `x ≠ 0` (at `0` both roundings are `0`).
  -- Equidistant and distinct puts `x` strictly between, so `x` is neither.
  have ne_of_tie : ∀ {a b : Dyadic}, a ≠ b →
      |x - (a : ℝ)| = |x - (b : ℝ)| → x ≠ (a : ℝ) := by
    intro a b hab hdist hx
    have hzero : |x - (b : ℝ)| = 0 := by rw [← hdist, hx, sub_self, abs_zero]
    exact hab (Dyadic.ext_real (hx.symm.trans (by linarith [abs_eq_zero.mp hzero])))
  cases tb with
  | awayZero =>
    obtain ⟨hm₁, hf₁, hmin₁, htie₁⟩ := h₁
    obtain ⟨hm₂, hf₂, hmin₂, htie₂⟩ := h₂
    by_cases hne : y₁ = y₂
    · exact hne
    exfalso
    have hdist : |x - (y₁ : ℝ)| = |x - (y₂ : ℝ)| :=
      le_antisymm (hmin₁ y₂ hm₂ hf₂) (hmin₂ y₁ hm₁ hf₁)
    -- Each tie-break clause bounds the other's magnitude, so they are equal.
    have habs : |(y₁ : ℝ)| = |(y₂ : ℝ)| :=
      le_antisymm (htie₂ y₁ hm₁ hf₁ hne hdist.symm)
        (htie₁ y₂ hm₂ hf₂ (Ne.symm hne) hdist)
    -- Opposite sides with equal magnitudes: `a = -b`, and equidistance pins
    -- `x = 0`, where both are `0` — contradicting `y₁ ≠ y₂`.
    have key : ∀ {a b : Dyadic}, RoundsFinite F.unbounded .toNegative x a →
        RoundsFinite F.unbounded .toPositive x b → a ≠ b →
        |x - (a : ℝ)| = |x - (b : ℝ)| → |(a : ℝ)| = |(b : ℝ)| → False := by
      intro a b hda hub hab hdist habs'
      have hxa := ne_of_tie hab hdist
      refine (fun hx0 : x = 0 => hxa (by
        have hda0 : RoundsFinite F.unbounded .toNegative 0 a := by rw [← hx0]; exact hda
        rw [hx0, RoundsFinite.eq_zero_of_zero hda0, Dyadic.coe_real_zero])) ?_
      have hle : (a : ℝ) ≤ x := hda.2.1
      have hge : x ≤ (b : ℝ) := hub.2.1
      -- `|a| = |b|` with `a ≠ b` forces `a = -b`, hence `a ≤ 0 ≤ b`.
      have hneg : (a : ℝ) = -(b : ℝ) := by
        rcases abs_eq_abs.mp habs' with hEq | hEq
        · exact absurd (Dyadic.ext_real hEq) hab
        · exact hEq
      rw [hneg] at hle
      -- Equidistance between `-b` and `b` puts `x` at their midpoint, `0`.
      rw [hneg, abs_of_nonneg (by linarith : (0:ℝ) ≤ x - -(b : ℝ)),
          abs_of_nonpos (by linarith : x - (b : ℝ) ≤ 0)] at hdist
      linarith
    rcases hf₁.opposite_sides_of_ne hf₂ hne with ⟨hd, hu⟩ | ⟨hd, hu⟩
    · exact key hd hu hne hdist habs
    · exact key hd hu (Ne.symm hne) hdist.symm habs.symm
  | toEven =>
    obtain ⟨hm₁, hf₁, hmin₁, htie₁⟩ := h₁
    obtain ⟨hm₂, hf₂, hmin₂, htie₂⟩ := h₂
    by_cases hne : y₁ = y₂
    · exact hne
    exfalso
    have hdist : |x - (y₁ : ℝ)| = |x - (y₂ : ℝ)| :=
      le_antisymm (hmin₁ y₂ hm₂ hf₂) (hmin₂ y₁ hm₁ hf₁)
    have hodd : ¬ F.IsUndefined .toOdd := fun ⟨h1, h2, _⟩ => h ⟨h1, h2, Or.inr rfl⟩
    set F'' := F.unbounded.toParityFormatOfToOdd hodd with hF''
    -- Each is a tie for the other, so the tie-break makes both even.
    have even₁ : F''.IsEven y₁ := by
      obtain ⟨F', hF', hev⟩ := htie₁ ⟨y₂, hm₂, hf₂, Ne.symm hne, hdist⟩
      exact (ParityFormat.IsEven_iff_of_toFormat_eq hF' y₁).mp hev
    have even₂ : F''.IsEven y₂ := by
      obtain ⟨F', hF', hev⟩ := htie₂ ⟨y₁, hm₁, hf₁, hne, hdist.symm⟩
      exact (ParityFormat.IsEven_iff_of_toFormat_eq hF' y₂).mp hev
    -- But the two neighbours alternate in parity, so they are not both even.
    have key : ∀ {a b : Dyadic}, RoundsFinite F.unbounded .toNegative x a →
        RoundsFinite F.unbounded .toPositive x b → a ≠ b →
        |x - (a : ℝ)| = |x - (b : ℝ)| → F''.IsEven a → F''.IsEven b → False := by
      intro a b hda hub hab hdist' heva hevb
      exact ParityFormat.not_isEven_and_isOdd hevb
        ((isOdd_alternate_of_bracketing (F := F.unbounded) hodd hda hub
            (ne_of_tie hab hdist')).mpr
          (fun hoa => ParityFormat.not_isEven_and_isOdd heva hoa))
    rcases hf₁.opposite_sides_of_ne hf₂ hne with ⟨hd, hu⟩ | ⟨hd, hu⟩
    · exact key hd hu hne hdist even₁ even₂
    · exact key hd hu (Ne.symm hne) hdist.symm even₂ even₁

/-- The spec pins its value, for every mode (Flocq `round_unique`). -/
theorem RoundsFinite.unique {F : FiniteFormat} {rm : RoundingMode} {x : ℝ}
    (h : ¬ F.IsUndefined rm) {y₁ y₂ : Dyadic}
    (h₁ : RoundsFinite F.unbounded rm x y₁)
    (h₂ : RoundsFinite F.unbounded rm x y₂) :
    y₁ = y₂ := by
  cases rm with
  | toNegative => exact RoundsFinite.unique_toNegative h₁ h₂
  | toPositive => exact RoundsFinite.unique_toPositive h₁ h₂
  | toZero => exact RoundsFinite.unique_toZero h₁ h₂
  | awayZero => exact RoundsFinite.unique_awayZero h₁ h₂
  | toOdd => exact RoundsFinite.unique_toOdd h h₁ h₂
  | nearest _ => exact RoundsFinite.unique_nearest h h₁ h₂

/-! ### Sign preservation and monotonicity -/

/-- `0 ∈ F` is a candidate (Flocq `round_pred_ge_0`). -/
theorem RoundsFinite.toNegative_nonneg {F : FiniteFormat} {x : ℝ} (hx : 0 ≤ x)
    {y : Dyadic} (h : RoundsFinite F .toNegative x y) : (0 : ℝ) ≤ (y : ℝ) := by
  obtain ⟨-, -, hmax⟩ := h
  simpa using hmax 0 F.zero_mem (by simpa using hx)

/-- Flocq `round_pred_le_0`. -/
theorem RoundsFinite.toPositive_nonpos {F : FiniteFormat} {x : ℝ} (hx : x ≤ 0)
    {y : Dyadic} (h : RoundsFinite F .toPositive x y) : (y : ℝ) ≤ 0 := by
  obtain ⟨-, -, hmin⟩ := h
  simpa using hmin 0 F.zero_mem (by simpa using hx)

/-- A nonzero faithful rounding has the sign of `x`. -/
theorem IsFaithfulRound.decide_lt_zero {F : FiniteFormat} {x : ℝ} {y : Dyadic}
    (h : IsFaithfulRound F x y) (hy : (y : ℝ) ≠ 0) :
    decide ((y : ℚ) < 0) = decide (x < 0) := by
  have key : (y : ℝ) < 0 ↔ x < 0 := by
    rcases isFaithfulRound_iff_directed.mp h with hd | hu
    · refine ⟨fun hy0 => ?_, fun hx => lt_of_le_of_lt hd.2.1 hx⟩
      by_contra hx
      linarith [RoundsFinite.toNegative_nonneg (not_lt.mp hx) hd]
    · refine ⟨fun hy0 => lt_of_le_of_lt hu.2.1 hy0, fun hx => ?_⟩
      exact lt_of_le_of_ne (RoundsFinite.toPositive_nonpos hx.le hu) hy
  rw [decide_eq_decide, ← key, Dyadic.coe_real_lt_zero_iff]

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

/-- A faithful rounding of `x` lies in `[-N, N]` once `|x| ≤ N ∈ F`. -/
theorem abs_faithful_le_of_le {F : FiniteFormat} {x : ℝ} {z N : Dyadic}
    (hN_mem : N ∈ F) (hxN : |x| ≤ (N : ℝ))
    (hfaithful : IsFaithfulRound F x z) :
    |(z : ℝ)| ≤ (N : ℝ) := by
  have hnN_mem : (-N) ∈ F := FiniteFormat.neg_mem hN_mem
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

/-- Dual of `abs_faithful_le_of_le`: a nonnegative `N ∈ F` with `N ≤ |x|`
bounds a faithful rounding of `x` from below in magnitude. -/
theorem le_abs_faithful_of_le {F : FiniteFormat} {x : ℝ} {z N : Dyadic}
    (hN_mem : N ∈ F) (hN_nn : 0 ≤ (N : ℝ)) (hxN : (N : ℝ) ≤ |x|)
    (hf : IsFaithfulRound F x z) : (N : ℝ) ≤ |(z : ℝ)| := by
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

/-- `a ≤ x ≤ y`, so `a` loses to the maximality of `y`'s round-down
(Flocq `Rnd_DN_pt_monotone`). -/
theorem RoundsFinite.monotone_toNegative {F : FiniteFormat} {x y : ℝ} {a b : Dyadic}
    (ha : RoundsFinite F .toNegative x a) (hb : RoundsFinite F .toNegative y b)
    (hxy : x ≤ y) : (a : ℝ) ≤ (b : ℝ) := by
  obtain ⟨ha_mem, ha_le, -⟩ := ha
  obtain ⟨-, -, hb_max⟩ := hb
  exact hb_max a ha_mem (ha_le.trans hxy)

/-- Flocq `Rnd_UP_pt_monotone`. -/
theorem RoundsFinite.monotone_toPositive {F : FiniteFormat} {x y : ℝ} {a b : Dyadic}
    (ha : RoundsFinite F .toPositive x a) (hb : RoundsFinite F .toPositive y b)
    (hxy : x ≤ y) : (a : ℝ) ≤ (b : ℝ) := by
  obtain ⟨-, -, ha_min⟩ := ha
  obtain ⟨hb_mem, hb_ge, -⟩ := hb
  exact ha_min b hb_mem (hxy.trans hb_ge)

/-- On each side of zero RTZ is a directed mode; across zero the two results
straddle `0` (Flocq `Rnd_ZR_pt_monotone`). -/
theorem RoundsFinite.monotone_toZero {F : FiniteFormat} {x y : ℝ} {a b : Dyadic}
    (ha : RoundsFinite F .toZero x a) (hb : RoundsFinite F .toZero y b)
    (hxy : x ≤ y) : (a : ℝ) ≤ (b : ℝ) := by
  rcases le_total 0 x with hx | hx
  · exact monotone_toNegative ((toNegative_iff_toZero_of_nonneg F hx a).mpr ha)
      ((toNegative_iff_toZero_of_nonneg F (hx.trans hxy) b).mpr hb) hxy
  rcases le_total y 0 with hy | hy
  · exact monotone_toPositive ((toPositive_iff_toZero_of_nonpos F (hxy.trans hy) a).mpr ha)
      ((toPositive_iff_toZero_of_nonpos F hy b).mpr hb) hxy
  · exact (toPositive_nonpos hx ((toPositive_iff_toZero_of_nonpos F hx a).mpr ha)).trans
      (toNegative_nonneg hy ((toNegative_iff_toZero_of_nonneg F hy b).mpr hb))

/-- Across zero the results straddle it outward: `a ≤ x ≤ 0 ≤ y ≤ b`. -/
theorem RoundsFinite.monotone_awayZero {F : FiniteFormat} {x y : ℝ} {a b : Dyadic}
    (ha : RoundsFinite F .awayZero x a) (hb : RoundsFinite F .awayZero y b)
    (hxy : x ≤ y) : (a : ℝ) ≤ (b : ℝ) := by
  rcases le_total 0 x with hx | hx
  · exact monotone_toPositive ((toPositive_iff_awayZero_of_nonneg F hx a).mpr ha)
      ((toPositive_iff_awayZero_of_nonneg F (hx.trans hxy) b).mpr hb) hxy
  rcases le_total y 0 with hy | hy
  · exact monotone_toNegative ((toNegative_iff_awayZero_of_nonpos F (hxy.trans hy) a).mpr ha)
      ((toNegative_iff_awayZero_of_nonpos F hy b).mpr hb) hxy
  · exact (((toNegative_iff_awayZero_of_nonpos F hx a).mpr ha).2.1.trans hx).trans
      (hy.trans ((toPositive_iff_awayZero_of_nonneg F hy b).mpr hb).2.1)

/-- Four side-combinations; three are immediate. In the fourth `a` rounds `x`
up and `b` rounds `y` down: `x ≤ b` or `a ≤ y` settles it by optimality, and
otherwise `b < x ≤ y < a` makes `b` the round-down of `x` too, so `a` and `b`
bracket `x` and cannot both be odd. -/
theorem RoundsFinite.monotone_toOdd {F : FiniteFormat} (h : ¬ F.IsUndefined .toOdd)
    {x y : ℝ} {a b : Dyadic}
    (ha : RoundsFinite F.unbounded .toOdd x a)
    (hb : RoundsFinite F.unbounded .toOdd y b)
    (hxy : x ≤ y) : (a : ℝ) ≤ (b : ℝ) := by
  obtain ⟨ha_mem, ha_faith, ha_par⟩ := ha
  obtain ⟨hb_mem, hb_faith, hb_par⟩ := hb
  rcases isFaithfulRound_iff_directed.mp ha_faith with hda | hua <;>
    rcases isFaithfulRound_iff_directed.mp hb_faith with hdb | hub
  · exact monotone_toNegative hda hdb hxy
  · exact (hda.2.1.trans hxy).trans hub.2.1
  · obtain ⟨-, -, ha_min⟩ := id hua
    obtain ⟨-, -, hb_max⟩ := id hdb
    by_cases hxb : x ≤ (b : ℝ)
    · exact ha_min b hb_mem hxb
    by_cases hay : (a : ℝ) ≤ y
    · exact hb_max a ha_mem hay
    exfalso
    push Not at hxb hay
    have hdn_x : RoundsFinite F.unbounded .toNegative x b :=
      ⟨hb_mem, hxb.le, fun z hz hzx => hb_max z hz (hzx.trans hxy)⟩
    obtain ⟨Fa, hFa, hFa_odd⟩ := ha_par (ne_of_lt (hxy.trans_lt hay))
    obtain ⟨Fb, hFb, hFb_odd⟩ := hb_par (ne_of_lt (hxb.trans_le hxy)).symm
    exact (isOdd_alternate_of_bracketing (F := F.unbounded) h hdn_x hua
        (ne_of_lt hxb).symm).mp
      ((ParityFormat.IsOdd_iff_of_toFormat_eq hFa a).mp hFa_odd)
      ((ParityFormat.IsOdd_iff_of_toFormat_eq hFb b).mp hFb_odd)
  · exact monotone_toPositive hua hub hxy

/-- The nearest-minimality conjunct, uniform in the tie-break: both cases carry
it in the same position, but the mode `match` needs `tb` to reduce. -/
theorem RoundsFinite.nearest_min {F : FiniteFormat} {tb : TieBreak} {x : ℝ}
    {y : Dyadic} (h : RoundsFinite F (.nearest tb) x y) {z : Dyadic}
    (hz : z ∈ F) (hzf : IsFaithfulRound F x z) :
    |x - (y : ℝ)| ≤ |x - (z : ℝ)| := by
  cases tb with
  | toEven => exact h.2.2.1 z hz hzf
  | awayZero => exact h.2.2.1 z hz hzf

/-- As `monotone_toOdd`, but the fourth case closes differently: under
`b < x ≤ y < a` each of `a`, `b` is faithful for the *other* point, so both
minimality clauses apply across the pair and add up to `y ≤ x`. Then `x = y`
and `unique_nearest` finishes (Flocq `Rnd_N_pt_monotone` + `Rnd_NG_pt_monotone`). -/
theorem RoundsFinite.monotone_nearest {F : FiniteFormat} {tb : TieBreak}
    (h : ¬ F.IsUndefined (.nearest tb)) {x y : ℝ} {a b : Dyadic}
    (ha : RoundsFinite F.unbounded (.nearest tb) x a)
    (hb : RoundsFinite F.unbounded (.nearest tb) y b)
    (hxy : x ≤ y) : (a : ℝ) ≤ (b : ℝ) := by
  have ha_mem := ha.1
  have hb_mem := hb.1
  rcases isFaithfulRound_iff_directed.mp ha.isFaithfulRound with hda | hua <;>
    rcases isFaithfulRound_iff_directed.mp hb.isFaithfulRound with hdb | hub
  · exact monotone_toNegative hda hdb hxy
  · exact (hda.2.1.trans hxy).trans hub.2.1
  · obtain ⟨-, -, ha_min⟩ := id hua
    obtain ⟨-, -, hb_max⟩ := id hdb
    by_cases hxb : x ≤ (b : ℝ)
    · exact ha_min b hb_mem hxb
    by_cases hay : (a : ℝ) ≤ y
    · exact hb_max a ha_mem hay
    push Not at hxb hay
    have hbx : IsFaithfulRound F.unbounded x b :=
      Or.inl ⟨hb_mem, hxb.le, fun z hz hzx => hb_max z hz (hzx.trans hxy)⟩
    have hya : IsFaithfulRound F.unbounded y a :=
      Or.inr ⟨ha_mem, hay.le, fun z hz hyz => ha_min z hz (hxy.trans hyz)⟩
    have h1 := ha.nearest_min hb_mem hbx
    have h2 := hb.nearest_min ha_mem hya
    rw [abs_of_nonpos (by linarith : x - (a : ℝ) ≤ 0),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - (b : ℝ))] at h1
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ y - (b : ℝ)),
        abs_of_nonpos (by linarith : y - (a : ℝ) ≤ 0)] at h2
    have hxy_eq : x = y := le_antisymm hxy (by linarith)
    subst hxy_eq
    exact le_of_eq (by rw [RoundsFinite.unique_nearest h ha hb])
  · exact monotone_toPositive hua hub hxy

/-- Flocq `round_le`. Stated on `RoundsFinite`: a `RoundResult` version would
need an order on `WithSpecial Dyadic` and monotone tables. -/
theorem RoundsFinite.monotone {F : FiniteFormat} {rm : RoundingMode}
    (h : ¬ F.IsUndefined rm) {x y : ℝ} {a b : Dyadic}
    (ha : RoundsFinite F.unbounded rm x a)
    (hb : RoundsFinite F.unbounded rm y b)
    (hxy : x ≤ y) : (a : ℝ) ≤ (b : ℝ) := by
  cases rm with
  | toNegative => exact monotone_toNegative ha hb hxy
  | toPositive => exact monotone_toPositive ha hb hxy
  | toZero => exact monotone_toZero ha hb hxy
  | awayZero => exact monotone_awayZero ha hb hxy
  | toOdd => exact monotone_toOdd h ha hb hxy
  | nearest _ => exact monotone_nearest h ha hb hxy

end Mpfx
