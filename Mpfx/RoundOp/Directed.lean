import Mpfx.RoundOp.Defs

/-!
# Constructive rounding: directed-mode obligations

Soundness and uniqueness for the directed modes
(`toNegative`, `toPositive`, `toZero`, `awayZero`).

`toZero`/`awayZero` are *not* proved from scratch: on `0 ≤ x` they coincide
(as functions) with `toNegative`/`toPositive`, and on `x < 0` with the other,
so their obligations transport through the sign-equivalences
`RoundsFinite.{toNegative_iff_toZero_of_nonneg, …}` already established in
`Mpfx/Rounding.lean` (the mpfx analogues of Flocq `round_ZR_DN`/`round_AW_UP`).
-/

namespace Mpfx

attribute [local instance] Classical.propDecidable

theorem rndUnbounded_satisfies_toNegative (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .toNegative) :
    RoundsFinite F.unbounded .toNegative x (rndUnbounded F .toNegative x h) := by
  have h_rnd_eq : rndUnbounded F .toNegative x h =
      Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋ (F.canonicalExp x) := by
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.toNegative : RoundingMode) ≠ .toOdd)]
    rw [dif_neg (by decide : (RoundingMode.toNegative : RoundingMode) ≠ .nearest .toEven)]
    rfl
  rw [h_rnd_eq]
  set e := F.canonicalExp x
  set c := ⌊x * (2 : ℝ) ^ (-e)⌋
  set y : Dyadic := Dyadic.ofIntZpow c e
  have h_y_real : (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ e := Dyadic.coe_ofIntZpow c e
  have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  -- Membership via `ofIntZpow_mem_unbounded`.
  have h_c_bound : ∀ {p : ℕ+}, F.p = ((p : ℕ+) : WithTop ℕ+) →
      |c| ≤ (2 : ℤ) ^ (p : ℕ) := fun hp => by
    apply abs_floor_le_of_abs_lt
    push_cast; exact floor_mantissa_lt hp
  have h_mem : y ∈ F.unbounded :=
    ofIntZpow_mem_unbounded F (fun hexp => F.exp_le_canonicalExp x hexp) h_c_bound
  obtain ⟨h_prec, h_quant, h_bnd⟩ := h_mem
  refine ⟨⟨h_prec, h_quant, h_bnd⟩, ?_, ?_⟩
  · -- (y : ℝ) ≤ x
    rw [h_y_real, ← mul_zpow_neg_self x e]
    exact mul_le_mul_of_nonneg_right (Int.floor_le _) h_2e_pos.le
  · -- minimality via `floor_minimality` helper.
    intro z hz_mem hz_le_x
    obtain ⟨hz_prec, hz_quant, _⟩ := hz_mem
    rw [h_y_real]
    exact floor_minimality F
      x hz_prec hz_quant hz_le_x

theorem rndUnbounded_satisfies_toPositive (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .toPositive) :
    RoundsFinite F.unbounded .toPositive x (rndUnbounded F .toPositive x h) := by
  have h_rnd_eq : rndUnbounded F .toPositive x h =
      Dyadic.ofIntZpow ⌈x * (2 : ℝ) ^ (-(F.canonicalExp x))⌉ (F.canonicalExp x) := by
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.toPositive : RoundingMode) ≠ .toOdd)]
    rw [dif_neg (by decide : (RoundingMode.toPositive : RoundingMode) ≠ .nearest .toEven)]
    rfl
  rw [h_rnd_eq]
  set e := F.canonicalExp x
  set c := ⌈x * (2 : ℝ) ^ (-e)⌉
  set y : Dyadic := Dyadic.ofIntZpow c e
  have h_y_real : (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ e := Dyadic.coe_ofIntZpow c e
  have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have h_c_bound : ∀ {p : ℕ+}, F.p = ((p : ℕ+) : WithTop ℕ+) →
      |c| ≤ (2 : ℤ) ^ (p : ℕ) := fun hp => by
    apply abs_ceil_le_of_abs_lt
    push_cast; exact floor_mantissa_lt hp
  have h_mem : y ∈ F.unbounded :=
    ofIntZpow_mem_unbounded F (fun hexp => F.exp_le_canonicalExp x hexp) h_c_bound
  obtain ⟨h_prec, h_quant, h_bnd⟩ := h_mem
  refine ⟨⟨h_prec, h_quant, h_bnd⟩, ?_, ?_⟩
  · -- x ≤ (y : ℝ).
    rw [h_y_real, ← mul_zpow_neg_self x e]
    exact mul_le_mul_of_nonneg_right (Int.le_ceil _) h_2e_pos.le
  · -- minimality via `ceil_minimality` helper.
    intro z hz_mem hx_le_z
    obtain ⟨hz_prec, hz_quant, _⟩ := hz_mem
    rw [h_y_real]
    exact ceil_minimality F
      x hz_prec hz_quant hx_le_z

/-! ### Sign bridges

On each side of zero the `toZero`/`awayZero` rounding *function* coincides with a
one-sided directed mode; `rndInt` picks `⌊·⌋`/`⌈·⌉` by the sign of `x`. These
four definitional identities let the `toZero`/`awayZero` obligations reuse the
`toNegative`/`toPositive` proofs. -/

/-- On `0 ≤ x`, round-to-zero is round-to-negative. -/
private theorem rndUnbounded_toZero_eq_toNegative_of_nonneg (F : FiniteFormat) (x : ℝ)
    (hx : 0 ≤ x) (h : ¬ F.IsUndefined .toZero) (h' : ¬ F.IsUndefined .toNegative) :
    rndUnbounded F .toZero x h = rndUnbounded F .toNegative x h' := by
  have hz : rndUnbounded F .toZero x h =
      Dyadic.ofIntZpow (rndInt .toZero x (F.canonicalExp x)) (F.canonicalExp x) := by
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.toZero : RoundingMode) ≠ .toOdd),
        dif_neg (by decide : (RoundingMode.toZero : RoundingMode) ≠ .nearest .toEven)]
  have hn : rndUnbounded F .toNegative x h' =
      Dyadic.ofIntZpow (rndInt .toNegative x (F.canonicalExp x)) (F.canonicalExp x) := by
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.toNegative : RoundingMode) ≠ .toOdd),
        dif_neg (by decide : (RoundingMode.toNegative : RoundingMode) ≠ .nearest .toEven)]
  rw [hz, hn]; congr 1
  change (if 0 ≤ x then ⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋
        else ⌈x * (2 : ℝ) ^ (-(F.canonicalExp x))⌉)
      = ⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋
  rw [if_pos hx]

/-- On `x < 0`, round-to-zero is round-to-positive. -/
private theorem rndUnbounded_toZero_eq_toPositive_of_neg (F : FiniteFormat) (x : ℝ)
    (hx : x < 0) (h : ¬ F.IsUndefined .toZero) (h' : ¬ F.IsUndefined .toPositive) :
    rndUnbounded F .toZero x h = rndUnbounded F .toPositive x h' := by
  have hz : rndUnbounded F .toZero x h =
      Dyadic.ofIntZpow (rndInt .toZero x (F.canonicalExp x)) (F.canonicalExp x) := by
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.toZero : RoundingMode) ≠ .toOdd),
        dif_neg (by decide : (RoundingMode.toZero : RoundingMode) ≠ .nearest .toEven)]
  have hp : rndUnbounded F .toPositive x h' =
      Dyadic.ofIntZpow (rndInt .toPositive x (F.canonicalExp x)) (F.canonicalExp x) := by
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.toPositive : RoundingMode) ≠ .toOdd),
        dif_neg (by decide : (RoundingMode.toPositive : RoundingMode) ≠ .nearest .toEven)]
  rw [hz, hp]; congr 1
  change (if 0 ≤ x then ⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋
        else ⌈x * (2 : ℝ) ^ (-(F.canonicalExp x))⌉)
      = ⌈x * (2 : ℝ) ^ (-(F.canonicalExp x))⌉
  rw [if_neg (not_le.mpr hx)]

/-- On `0 ≤ x`, round-away-from-zero is round-to-positive. -/
private theorem rndUnbounded_awayZero_eq_toPositive_of_nonneg (F : FiniteFormat) (x : ℝ)
    (hx : 0 ≤ x) (h : ¬ F.IsUndefined .awayZero) (h' : ¬ F.IsUndefined .toPositive) :
    rndUnbounded F .awayZero x h = rndUnbounded F .toPositive x h' := by
  have ha : rndUnbounded F .awayZero x h =
      Dyadic.ofIntZpow (rndInt .awayZero x (F.canonicalExp x)) (F.canonicalExp x) := by
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.awayZero : RoundingMode) ≠ .toOdd),
        dif_neg (by decide : (RoundingMode.awayZero : RoundingMode) ≠ .nearest .toEven)]
  have hp : rndUnbounded F .toPositive x h' =
      Dyadic.ofIntZpow (rndInt .toPositive x (F.canonicalExp x)) (F.canonicalExp x) := by
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.toPositive : RoundingMode) ≠ .toOdd),
        dif_neg (by decide : (RoundingMode.toPositive : RoundingMode) ≠ .nearest .toEven)]
  rw [ha, hp]; congr 1
  change (if 0 ≤ x then ⌈x * (2 : ℝ) ^ (-(F.canonicalExp x))⌉
        else ⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋)
      = ⌈x * (2 : ℝ) ^ (-(F.canonicalExp x))⌉
  rw [if_pos hx]

/-- On `x < 0`, round-away-from-zero is round-to-negative. -/
private theorem rndUnbounded_awayZero_eq_toNegative_of_neg (F : FiniteFormat) (x : ℝ)
    (hx : x < 0) (h : ¬ F.IsUndefined .awayZero) (h' : ¬ F.IsUndefined .toNegative) :
    rndUnbounded F .awayZero x h = rndUnbounded F .toNegative x h' := by
  have ha : rndUnbounded F .awayZero x h =
      Dyadic.ofIntZpow (rndInt .awayZero x (F.canonicalExp x)) (F.canonicalExp x) := by
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.awayZero : RoundingMode) ≠ .toOdd),
        dif_neg (by decide : (RoundingMode.awayZero : RoundingMode) ≠ .nearest .toEven)]
  have hn : rndUnbounded F .toNegative x h' =
      Dyadic.ofIntZpow (rndInt .toNegative x (F.canonicalExp x)) (F.canonicalExp x) := by
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.toNegative : RoundingMode) ≠ .toOdd),
        dif_neg (by decide : (RoundingMode.toNegative : RoundingMode) ≠ .nearest .toEven)]
  rw [ha, hn]; congr 1
  change (if 0 ≤ x then ⌈x * (2 : ℝ) ^ (-(F.canonicalExp x))⌉
        else ⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋)
      = ⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋
  rw [if_neg (not_le.mpr hx)]

theorem rndUnbounded_satisfies_toZero (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .toZero) :
    RoundsFinite F.unbounded .toZero x (rndUnbounded F .toZero x h) := by
  by_cases hx : 0 ≤ x
  · rw [rndUnbounded_toZero_eq_toNegative_of_nonneg F x hx h (not_isUndefined_toNegative F)]
    exact (RoundsFinite.toNegative_iff_toZero_of_nonneg F.unbounded hx _).mp
      (rndUnbounded_satisfies_toNegative F x (not_isUndefined_toNegative F))
  · rw [rndUnbounded_toZero_eq_toPositive_of_neg F x (not_le.mp hx) h
        (not_isUndefined_toPositive F)]
    exact (RoundsFinite.toPositive_iff_toZero_of_nonpos F.unbounded (not_le.mp hx).le _).mp
      (rndUnbounded_satisfies_toPositive F x (not_isUndefined_toPositive F))

theorem rndUnbounded_satisfies_awayZero (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .awayZero) :
    RoundsFinite F.unbounded .awayZero x (rndUnbounded F .awayZero x h) := by
  by_cases hx : 0 ≤ x
  · rw [rndUnbounded_awayZero_eq_toPositive_of_nonneg F x hx h (not_isUndefined_toPositive F)]
    exact (RoundsFinite.toPositive_iff_awayZero_of_nonneg F.unbounded hx _).mp
      (rndUnbounded_satisfies_toPositive F x (not_isUndefined_toPositive F))
  · rw [rndUnbounded_awayZero_eq_toNegative_of_neg F x (not_le.mp hx) h
        (not_isUndefined_toNegative F)]
    exact (RoundsFinite.toNegative_iff_awayZero_of_nonpos F.unbounded (not_le.mp hx).le _).mp
      (rndUnbounded_satisfies_toNegative F x (not_isUndefined_toNegative F))

theorem rndUnbounded_unique_toNegative (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .toNegative) {y : Dyadic}
    (hy : RoundsFinite F.unbounded .toNegative x y) :
    y = rndUnbounded F .toNegative x h := by
  set y' := rndUnbounded F .toNegative x h
  have hy' : RoundsFinite F.unbounded .toNegative x y' :=
    rndUnbounded_satisfies_toNegative F x h
  obtain ⟨hy_mem, hy_le, hy_max⟩ := hy
  obtain ⟨hy'_mem, hy'_le, hy'_max⟩ := hy'
  have h1 : (y' : ℝ) ≤ (y : ℝ) := hy_max y' hy'_mem hy'_le
  have h2 : (y : ℝ) ≤ (y' : ℝ) := hy'_max y hy_mem hy_le
  exact Dyadic.ext_real (le_antisymm h2 h1)

theorem rndUnbounded_unique_toPositive (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .toPositive) {y : Dyadic}
    (hy : RoundsFinite F.unbounded .toPositive x y) :
    y = rndUnbounded F .toPositive x h := by
  set y' := rndUnbounded F .toPositive x h
  have hy' : RoundsFinite F.unbounded .toPositive x y' :=
    rndUnbounded_satisfies_toPositive F x h
  obtain ⟨hy_mem, hy_ge, hy_min⟩ := hy
  obtain ⟨hy'_mem, hy'_ge, hy'_min⟩ := hy'
  have h1 : (y : ℝ) ≤ (y' : ℝ) := hy_min y' hy'_mem hy'_ge
  have h2 : (y' : ℝ) ≤ (y : ℝ) := hy'_min y hy_mem hy_ge
  exact Dyadic.ext_real (le_antisymm h1 h2)

theorem rndUnbounded_unique_toZero (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .toZero) {y : Dyadic}
    (hy : RoundsFinite F.unbounded .toZero x y) :
    y = rndUnbounded F .toZero x h := by
  by_cases hx : 0 ≤ x
  · rw [rndUnbounded_toZero_eq_toNegative_of_nonneg F x hx h (not_isUndefined_toNegative F)]
    exact rndUnbounded_unique_toNegative F x (not_isUndefined_toNegative F)
      ((RoundsFinite.toNegative_iff_toZero_of_nonneg F.unbounded hx y).mpr hy)
  · rw [rndUnbounded_toZero_eq_toPositive_of_neg F x (not_le.mp hx) h
        (not_isUndefined_toPositive F)]
    exact rndUnbounded_unique_toPositive F x (not_isUndefined_toPositive F)
      ((RoundsFinite.toPositive_iff_toZero_of_nonpos F.unbounded (not_le.mp hx).le y).mpr hy)

theorem rndUnbounded_unique_awayZero (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .awayZero) {y : Dyadic}
    (hy : RoundsFinite F.unbounded .awayZero x y) :
    y = rndUnbounded F .awayZero x h := by
  by_cases hx : 0 ≤ x
  · rw [rndUnbounded_awayZero_eq_toPositive_of_nonneg F x hx h (not_isUndefined_toPositive F)]
    exact rndUnbounded_unique_toPositive F x (not_isUndefined_toPositive F)
      ((RoundsFinite.toPositive_iff_awayZero_of_nonneg F.unbounded hx y).mpr hy)
  · rw [rndUnbounded_awayZero_eq_toNegative_of_neg F x (not_le.mp hx) h
        (not_isUndefined_toNegative F)]
    exact rndUnbounded_unique_toNegative F x (not_isUndefined_toNegative F)
      ((RoundsFinite.toNegative_iff_awayZero_of_nonpos F.unbounded (not_le.mp hx).le y).mpr hy)

end Mpfx
