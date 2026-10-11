import Mpfx.Rounding.Defs
import Mpfx.Format.CanonicalExp
import Mpfx.Rounding.Parity

/-!
# Round-predicate layer

Consequences of the `RoundsFinite` spec, per mode and mode-generic: sign
symmetry, the directed-vs-zero-relative mode equivalences, uniqueness,
faithfulness and sign preservation.

Nothing here mentions the `rnd` construction.
-/

namespace Mpfx

/-! ## Sign-symmetry algebraic helpers -/

private lemma abs_neg_add (a b : ℝ) : |-a + b| = |a - b| := by
  rw [show -a + b = -(a - b) by ring, abs_neg]

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
  rw [or_comm]
  simp only [Dyadic.coe_real_neg, FiniteFormat.mem_neg_iff, neg_le_neg_iff]
  exact or_congr
    (and_congr_right' (and_congr_right' (FiniteFormat.forall_mem_congr_neg F fun _ => by simp)))
    (and_congr_right' (and_congr_right' (FiniteFormat.forall_mem_congr_neg F fun _ => by simp)))

/-- `IsFaithfulRound` is exactly "round-down or round-up", phrased via the
directed `RoundsFinite` specs (by definition). This lets the round-to-nearest machinery work
with `RoundsFinite .toNegative/.toPositive` while the `.nearest` spec hands
out an `IsFaithfulRound`. -/
theorem isFaithfulRound_iff_directed {F : FiniteFormat} {x : ℝ} {y : Dyadic} :
    IsFaithfulRound F x y ↔
      RoundsFinite F .toNegative x y ∨ RoundsFinite F .toPositive x y :=
  Iff.rfl

/-- A representable value is its own faithful rounding: `d` is the largest
`F`-element `≤ d` (the round-down disjunct). -/
theorem isFaithfulRound_self {F : FiniteFormat} {d : Dyadic} (hd : d ∈ F) :
    IsFaithfulRound F (d : ℝ) d :=
  Or.inl ⟨hd, le_rfl, fun _ _ hz => hz⟩

/-- A faithful rounding of a representable value is that value. -/
theorem IsFaithfulRound.eq_of_mem {F : FiniteFormat} {d y : Dyadic} (hd : d ∈ F)
    (h : IsFaithfulRound F (d : ℝ) y) : y = d := by
  rcases h with ⟨-, hyd, hmax⟩ | ⟨-, hdy, hmin⟩
  · exact Dyadic.ext_real (le_antisymm hyd (hmax d hd le_rfl))
  · exact Dyadic.ext_real (le_antisymm (hmin d hd le_rfl) hdy)

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

/-! ## Sign symmetry of `RoundsFinite`

For each rounding mode, rounding `-x` under `rm'` gives the negated result,
where `rm'` is `rm` itself (modes symmetric around zero) or its flipped partner
(`.toNegative` ↔ `.toPositive`). -/

/-- Sign-symmetry of `RoundsFinite` at mode `.toZero`. -/
theorem RoundsFinite.neg_toZero (F : FiniteFormat) (x : ℝ) (y : Dyadic) :
    RoundsFinite F .toZero x y ↔ RoundsFinite F .toZero (-x) (-y) := by
  unfold RoundsFinite
  simp only [Dyadic.coe_real_neg, abs_neg, neg_mul_neg, FiniteFormat.mem_neg_iff]
  exact and_congr_right' (and_congr_right' (and_congr_right'
    (FiniteFormat.forall_mem_congr_neg F fun _ => by simp)))

/-- Sign-symmetry: `.toNegative` ↔ `.toPositive` swaps under negation. -/
theorem RoundsFinite.neg_toNegative_iff_toPositive (F : FiniteFormat) (x : ℝ)
    (y : Dyadic) :
    RoundsFinite F .toNegative x y ↔ RoundsFinite F .toPositive (-x) (-y) := by
  unfold RoundsFinite
  simp only [Dyadic.coe_real_neg, FiniteFormat.mem_neg_iff, neg_le_neg_iff]
  exact and_congr_right' (and_congr_right'
    (FiniteFormat.forall_mem_congr_neg F fun _ => by simp))

/-- Sign-symmetry of `RoundsFinite` at mode `.awayZero`. -/
theorem RoundsFinite.neg_awayZero (F : FiniteFormat) (x : ℝ) (y : Dyadic) :
    RoundsFinite F .awayZero x y ↔ RoundsFinite F .awayZero (-x) (-y) := by
  unfold RoundsFinite
  simp only [Dyadic.coe_real_neg, abs_neg, neg_mul_neg, FiniteFormat.mem_neg_iff]
  exact and_congr_right' (and_congr_right' (and_congr_right'
    (FiniteFormat.forall_mem_congr_neg F fun _ => by simp)))

/-- Sign-symmetry of `RoundsFinite` at mode `.nearest .awayZero`. -/
theorem RoundsFinite.neg_nearest_awayZero (F : FiniteFormat) (x : ℝ) (y : Dyadic) :
    RoundsFinite F (.nearest .awayZero) x y ↔
      RoundsFinite F (.nearest .awayZero) (-x) (-y) := by
  unfold RoundsFinite
  simp only [FiniteFormat.mem_neg_iff, ← IsFaithfulRound.neg_iff]
  have hf := IsFaithfulRound.neg_iff F x
  exact and_congr_right' (and_congr_right' (and_congr
    (FiniteFormat.forall_mem_congr_neg F fun _ => by simp [abs_neg_add, hf])
    (FiniteFormat.forall_mem_congr_neg F fun _ => by simp [abs_neg_add, hf])))

/-- Sign-symmetry of `RoundsFinite` at mode `.nearest .toEven`. -/
theorem RoundsFinite.neg_nearest_toEven (F : FiniteFormat) (x : ℝ) (y : Dyadic) :
    RoundsFinite F (.nearest .toEven) x y ↔
      RoundsFinite F (.nearest .toEven) (-x) (-y) := by
  unfold RoundsFinite
  simp only [FiniteFormat.mem_neg_iff, ← IsFaithfulRound.neg_iff, ParityFormat.IsEven.neg_iff]
  have hf := IsFaithfulRound.neg_iff F x
  exact and_congr_right' (and_congr_right' (and_congr
    (FiniteFormat.forall_mem_congr_neg F fun _ => by simp [abs_neg_add, hf])
    (imp_congr_left (FiniteFormat.exists_mem_congr_neg F fun _ => by
      simp [abs_neg_add, hf]))))

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

theorem RoundsFinite.toPositive_iff_awayZero_of_nonneg
    (F : FiniteFormat) {x : ℝ} (hx : 0 ≤ x) (y : Dyadic) :
    RoundsFinite F .toPositive x y ↔ RoundsFinite F .awayZero x y := by
  unfold RoundsFinite
  refine and_congr_right fun hy => ?_
  rcases hx.eq_or_lt with rfl | hx
  · -- At `0` both say `y = 0`, the candidate `0` being in `F`.
    have h0 := FiniteFormat.zero_mem F
    refine ⟨fun ⟨hy0, hmin⟩ => ?_, fun ⟨_, _, hmin⟩ => ?_⟩
    · have : (y : ℝ) = 0 := le_antisymm (by simpa using hmin 0 h0 (by simp)) hy0
      exact ⟨by simp, by simp [this], fun z _ _ _ => by simp [this]⟩
    · have : (y : ℝ) = 0 := abs_nonpos_iff.mp (by simpa using hmin 0 h0 (by simp) (by simp))
      exact ⟨by simp [this], fun z _ hz => by simpa [this] using hz⟩
  -- For `x > 0`, a same-signed value at least `|x|` in magnitude is one above `x`.
  have key : ∀ z : ℝ, (|x| ≤ |z| ∧ z * x ≥ 0) ↔ x ≤ z := fun z => by
    constructor
    · rintro ⟨h1, h2⟩
      have hz : 0 ≤ z := nonneg_of_mul_nonneg_left h2 hx
      rwa [abs_of_pos hx, abs_of_nonneg hz] at h1
    · intro h
      rw [abs_of_pos hx, abs_of_nonneg (hx.le.trans h)]
      exact ⟨h, mul_nonneg (hx.le.trans h) hx.le⟩
  have habs : ∀ {a b : ℝ}, x ≤ a → x ≤ b → (|a| ≤ |b| ↔ a ≤ b) := fun ha hb => by
    rw [abs_of_nonneg (hx.le.trans ha), abs_of_nonneg (hx.le.trans hb)]
  constructor
  · rintro ⟨hxy, hmin⟩
    obtain ⟨h1, h2⟩ := (key y).mpr hxy
    exact ⟨h1, h2, fun z hz h1 h2 =>
      (habs hxy ((key z).mp ⟨h1, h2⟩)).mpr (hmin z hz ((key z).mp ⟨h1, h2⟩))⟩
  · rintro ⟨h1, h2, hmin⟩
    have hxy := (key y).mp ⟨h1, h2⟩
    exact ⟨hxy, fun z hz hxz =>
      (habs hxy hxz).mp (hmin z hz ((key z).mpr hxz).1 ((key z).mpr hxz).2)⟩

theorem RoundsFinite.toPositive_iff_toZero_of_nonpos
    (F : FiniteFormat) {x : ℝ} (hx : x ≤ 0) (y : Dyadic) :
    RoundsFinite F .toPositive x y ↔ RoundsFinite F .toZero x y := by
  unfold RoundsFinite
  refine and_congr_right' ?_
  -- For `x ≤ 0`, a same-signed value at most `|x|` in magnitude lies in `[x, 0]`.
  have key : ∀ z : ℝ, (|z| ≤ |x| ∧ z * x ≥ 0) ↔ (x ≤ z ∧ z ≤ 0) := fun z => by
    rw [abs_of_nonpos hx]
    constructor
    · rintro ⟨h1, h2⟩
      rcases hx.lt_or_eq with hx' | rfl
      · have hz : z ≤ 0 := nonpos_of_mul_nonneg_left h2 hx'
        rw [abs_of_nonpos hz] at h1
        exact ⟨by linarith, hz⟩
      · have : z = 0 := by simpa using h1
        exact ⟨this.ge, this.le⟩
    · rintro ⟨h1, h2⟩
      rw [abs_of_nonpos h2]
      exact ⟨by linarith, mul_nonneg_of_nonpos_of_nonpos h2 hx⟩
  have habs : ∀ {a b : ℝ}, a ≤ 0 → b ≤ 0 → (|a| ≤ |b| ↔ b ≤ a) := fun ha hb => by
    rw [abs_of_nonpos ha, abs_of_nonpos hb, neg_le_neg_iff]
  constructor
  · rintro ⟨hxy, hmin⟩
    have hy0 : (y : ℝ) ≤ 0 := by simpa using hmin 0 (FiniteFormat.zero_mem F) (by simpa using hx)
    obtain ⟨h1, h2⟩ := (key y).mpr ⟨hxy, hy0⟩
    exact ⟨h1, h2, fun z hz h1 h2 => by
      obtain ⟨hxz, hz0⟩ := (key z).mp ⟨h1, h2⟩
      exact (habs hz0 hy0).mpr (hmin z hz hxz)⟩
  · rintro ⟨h1, h2, hmax⟩
    obtain ⟨hxy, hy0⟩ := (key y).mp ⟨h1, h2⟩
    refine ⟨hxy, fun z hz hxz => ?_⟩
    rcases le_or_gt (z : ℝ) 0 with hz0 | hz0
    · obtain ⟨h1, h2⟩ := (key z).mpr ⟨hxz, hz0⟩
      exact (habs hz0 hy0).mp (hmax z hz h1 h2)
    · linarith

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

/-- **Rounding fixes representable values** — the spec-relational form of
Flocq's `round_generic` (paper Def. 7: `∀ f ∈ F, ◦(f) = f`). If `d ∈ F` and
`y` is the `rm`-rounding of `(d : ℝ)` in `F`, then `y = d`, for *any* mode `rm`
(including the degenerate `IsUndefined` formats — `RoundsFinite` never consults
`IsUndefined`). -/
theorem RoundsFinite.eq_of_mem {F : FiniteFormat} {rm : RoundingMode} {d : Dyadic}
    (hd : d ∈ F) {y : Dyadic} (h : RoundsFinite F rm (d : ℝ) y) : y = d :=
  h.isFaithfulRound.eq_of_mem hd

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

/-- Every mode fixes a representable value. -/
theorem RoundsFinite.self {F : FiniteFormat} (rm : RoundingMode) {d : Dyadic} (hd : d ∈ F) :
    RoundsFinite F rm (d : ℝ) d := by
  cases rm with
  | toNegative => exact ⟨hd, le_rfl, fun _ _ h => h⟩
  | toPositive => exact ⟨hd, le_rfl, fun _ _ h => h⟩
  | toZero => exact toZero_self hd
  | awayZero => exact awayZero_self hd
  | toOdd => exact toOdd_self hd
  | nearest tb =>
    have hne : ∀ z : Dyadic, z ≠ d → |(d : ℝ) - d| ≠ |(d : ℝ) - z| := fun z hz h =>
      hz (Dyadic.ext_real (by rw [sub_self, abs_zero, eq_comm, abs_eq_zero, sub_eq_zero] at h
                              exact h.symm))
    cases tb with
    | toEven => exact ⟨hd, isFaithfulRound_self hd, fun _ _ _ => by simp,
        fun ⟨z, _, _, hz, h⟩ => absurd h (hne z hz)⟩
    | awayZero => exact ⟨hd, isFaithfulRound_self hd, fun _ _ _ => by simp,
        fun z _ _ hz h => absurd h (hne z hz)⟩

/-- A faithful rounding is the round-down or the round-up. -/
theorem IsFaithfulRound.eq_or_eq {F : FiniteFormat} {x : ℝ} {d u y : Dyadic}
    (hd : RoundsFinite F .toNegative x d) (hu : RoundsFinite F .toPositive x u)
    (h : IsFaithfulRound F x y) : y = d ∨ y = u :=
  h.imp (RoundsFinite.unique_toNegative · hd) (RoundsFinite.unique_toPositive · hu)

/-- Two roundings `y, z ∈ {d, u}` that differ are `d` and `u` in some order. -/
private theorem dist_eq_of_mem_pair {x : ℝ} {d u y z : Dyadic}
    (hy : y = d ∨ y = u) (hz : z = d ∨ z = u) (hzy : z ≠ y)
    (h : |x - (y : ℝ)| = |x - (z : ℝ)|) : |x - (d : ℝ)| = |x - (u : ℝ)| ∧ d ≠ u := by
  rcases hy with rfl | rfl <;> rcases hz with rfl | rfl
  · exact absurd rfl hzy
  · exact ⟨h, hzy.symm⟩
  · exact ⟨h.symm, hzy⟩
  · exact absurd rfl hzy

/-- **Nearest-even between the round-down and the round-up.** The nearer of the
round-down `d` and the round-up `u`, the even one on a tie, is the nearest-even
rounding. -/
theorem RoundsFinite.nearest_toEven_of_bracket {F : FiniteFormat} {x : ℝ} {d u y : Dyadic}
    (hd : RoundsFinite F .toNegative x d) (hu : RoundsFinite F .toPositive x u)
    (hy : y = d ∨ y = u) (hclose : |x - (y : ℝ)| ≤ |x - (d : ℝ)| ∧ |x - (y : ℝ)| ≤ |x - (u : ℝ)|)
    (htie : |x - (d : ℝ)| = |x - (u : ℝ)| → d ≠ u →
      ∃ F' : ParityFormat, F'.toFormat = F.toFormat ∧ F'.IsEven y) :
    RoundsFinite F (.nearest .toEven) x y := by
  have hfy : IsFaithfulRound F x y := hy.elim (· ▸ Or.inl hd) (· ▸ Or.inr hu)
  refine ⟨hy.elim (· ▸ hd.1) (· ▸ hu.1), hfy, fun z _ hz => ?_, fun ⟨z, _, hz, hzy, h⟩ => ?_⟩
  · rcases hz.eq_or_eq hd hu with rfl | rfl
    exacts [hclose.1, hclose.2]
  · exact htie (dist_eq_of_mem_pair hy (hz.eq_or_eq hd hu) hzy h).1
      (dist_eq_of_mem_pair hy (hz.eq_or_eq hd hu) hzy h).2

/-- **Nearest-away between the round-down and the round-up.** The nearer of the
round-down `d` and the round-up `u`, the larger in magnitude on a tie, is the
nearest-away rounding. -/
theorem RoundsFinite.nearest_awayZero_of_bracket {F : FiniteFormat} {x : ℝ} {d u y : Dyadic}
    (hd : RoundsFinite F .toNegative x d) (hu : RoundsFinite F .toPositive x u)
    (hy : y = d ∨ y = u) (hclose : |x - (y : ℝ)| ≤ |x - (d : ℝ)| ∧ |x - (y : ℝ)| ≤ |x - (u : ℝ)|)
    (htie : |x - (d : ℝ)| = |x - (u : ℝ)| → d ≠ u →
      |(d : ℝ)| ≤ |(y : ℝ)| ∧ |(u : ℝ)| ≤ |(y : ℝ)|) :
    RoundsFinite F (.nearest .awayZero) x y := by
  have hfy : IsFaithfulRound F x y := hy.elim (· ▸ Or.inl hd) (· ▸ Or.inr hu)
  refine ⟨hy.elim (· ▸ hd.1) (· ▸ hu.1), hfy, fun z _ hz => ?_, fun z _ hz hzy h => ?_⟩
  · rcases hz.eq_or_eq hd hu with rfl | rfl
    exacts [hclose.1, hclose.2]
  · obtain ⟨h₁, h₂⟩ := dist_eq_of_mem_pair hy (hz.eq_or_eq hd hu) hzy h
    rcases hz.eq_or_eq hd hu with rfl | rfl
    exacts [(htie h₁ h₂).1, (htie h₁ h₂).2]

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

/-- Off the grid, the round-up is the successor of the floor point: the ceiling
is the floor plus one. -/
theorem RoundsFinite.toPositive_floor_add_one (F : FiniteFormat) {x : ℝ}
    (hx : (⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋ : ℝ) ≠ x * (2 : ℝ) ^ (-(F.canonicalExp x))) :
    RoundsFinite F.unbounded .toPositive x
      (Dyadic.ofIntZpow (⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋ + 1) (F.canonicalExp x)) := by
  have h := RoundsFinite.toPositive_ceil F x
  rwa [le_antisymm (Int.ceil_le_floor_add_one _)
    (Int.lt_ceil.mpr (lt_of_le_of_ne (Int.floor_le _) hx))] at h

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
theorem alternate_of_bracketing {F : FiniteFormat} {x : ℝ}
    (h : ¬ F.IsUndefined .toOdd) {y y' : Dyadic}
    (hy : RoundsFinite F.unbounded .toNegative x y)
    (hy' : RoundsFinite F.unbounded .toPositive x y')
    (hne : x ≠ (y : ℝ)) :
    ((F.toParityFormatOfToOdd h).IsOdd y' ↔
      ¬ (F.toParityFormatOfToOdd h).IsOdd y) ∧
    (¬ (F.toParityFormatOfToOdd h).IsEven y → (F.toParityFormatOfToOdd h).IsEven y') := by
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
  have hy'_eq : y' = Dyadic.ofIntZpow (⌊s⌋ + 1) e :=
    RoundsFinite.unique_toPositive hy' (RoundsFinite.toPositive_floor_add_one F h_lo_ne_s)
  rw [hy_eq, hy'_eq]
  exact neighbors_alternate x h hx_ne h_lo_ne_s

/-- The `IsOdd` half of `alternate_of_bracketing`. -/
theorem isOdd_alternate_of_bracketing {F : FiniteFormat} {x : ℝ}
    (h : ¬ F.IsUndefined .toOdd) {y y' : Dyadic}
    (hy : RoundsFinite F.unbounded .toNegative x y)
    (hy' : RoundsFinite F.unbounded .toPositive x y')
    (hne : x ≠ (y : ℝ)) :
    ((F.toParityFormatOfToOdd h).IsOdd y' ↔
      ¬ (F.toParityFormatOfToOdd h).IsOdd y) :=
  (alternate_of_bracketing h hy hy' hne).1

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

/-! ### Sign preservation -/

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

/-- A faithful rounding of a nonnegative input is nonnegative. -/
theorem IsFaithfulRound.nonneg {F : FiniteFormat} {x : ℝ} {z : Dyadic}
    (hf : IsFaithfulRound F x z) (hx : 0 ≤ x) : 0 ≤ (z : ℝ) := by
  rcases isFaithfulRound_iff_directed.mp hf with hd | hu
  · exact RoundsFinite.toNegative_nonneg hx hd
  · exact hx.trans hu.2.1

/-- A faithful rounding of a nonpositive input is nonpositive. -/
theorem IsFaithfulRound.nonpos {F : FiniteFormat} {x : ℝ} {z : Dyadic}
    (hf : IsFaithfulRound F x z) (hx : x ≤ 0) : (z : ℝ) ≤ 0 := by
  rcases isFaithfulRound_iff_directed.mp hf with hd | hu
  · exact hd.2.1.trans hx
  · exact RoundsFinite.toPositive_nonpos hx hu

/-- A faithful rounding has the sign of its input. -/
theorem IsFaithfulRound.mul_nonneg {F : FiniteFormat} {x : ℝ} {z : Dyadic}
    (hf : IsFaithfulRound F x z) : (z : ℝ) * x ≥ 0 := by
  rcases le_total 0 x with hx | hx
  · exact _root_.mul_nonneg (hf.nonneg hx) hx
  · exact mul_nonneg_of_nonpos_of_nonpos (hf.nonpos hx) hx

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

/-- The nearest-minimality conjunct, uniform in the tie-break: both cases carry
it in the same position, but the mode `match` needs `tb` to reduce. -/
theorem RoundsFinite.nearest_min {F : FiniteFormat} {tb : TieBreak} {x : ℝ}
    {y : Dyadic} (h : RoundsFinite F (.nearest tb) x y) {z : Dyadic}
    (hz : z ∈ F) (hzf : IsFaithfulRound F x z) :
    |x - (y : ℝ)| ≤ |x - (z : ℝ)| := by
  cases tb with
  | toEven => exact h.2.2.1 z hz hzf
  | awayZero => exact h.2.2.1 z hz hzf

end Mpfx
