import Mpfx.RoundOp

/-!
# ulp, the directed roundings, and the neighbours `succ` / `pred`

`ulp F x` is the spacing of `F` at `x`, `rndDown`/`rndUp` the two directed
roundings as total functions, and `midp F x` the midpoint between them. On top
sit the round-to-nearest error bound, the characterisations of nearest rounding
either side of the midpoint, and the neighbours `succ`/`pred`.
-/

namespace Mpfx

/-- **ulp** — unit in the last place of `x` in `F` (Flocq `ulp`).

**Goldberg's convention**: at a power of two `ulp (2^e) = 2^(e+1-p)`, the
spacing of the binade *above* `x`, twice the spacing just below it. Harrison's
and Kahan's definitions differ exactly there. Consequently `succ x = x + ulp x`
is right at a power of two but `pred x = x - ulp x` is not.

`2 ^ canonicalExp x`, except at `x = 0` with no minimum quantum: the format
then holds `c·2^k` at arbitrarily negative `k`, so the gap at zero has infimum
`0` and no exponent describes it. -/
noncomputable def ulp (F : FiniteFormat) (x : ℝ) : ℝ :=
  if x = 0 ∧ F.exp = ⊥ then 0 else (2 : ℝ) ^ F.canonicalExp x

theorem ulp_of_ne_zero (F : FiniteFormat) {x : ℝ} (hx : x ≠ 0) :
    ulp F x = (2 : ℝ) ^ F.canonicalExp x :=
  if_neg (by simp [hx])

theorem ulp_eq_zpow_of (F : FiniteFormat) {x : ℝ} (h : ¬(x = 0 ∧ F.exp = ⊥)) :
    ulp F x = (2 : ℝ) ^ F.canonicalExp x := if_neg h

theorem ulp_nonneg (F : FiniteFormat) (x : ℝ) : 0 ≤ ulp F x := by
  unfold ulp; split_ifs
  · exact le_refl _
  · exact (zpow_pos (by norm_num) _).le

theorem ulp_pos (F : FiniteFormat) {x : ℝ} (hx : x ≠ 0) : 0 < ulp F x := by
  rw [ulp_of_ne_zero F hx]; exact zpow_pos (by norm_num) _

@[simp] theorem ulp_neg (F : FiniteFormat) (x : ℝ) : ulp F (-x) = ulp F x := by
  unfold ulp; rw [canonicalExp_neg]; simp [neg_eq_zero]

/-- **Round-down** — the round-toward-`−∞` value of `x` in `F`, always finite
(Flocq `round … Zfloor`). -/
noncomputable def rndDown (F : FiniteFormat) (x : ℝ) : Dyadic :=
  rndUnbounded F .toNegative x (not_isUndefined_toNegative F)

/-- `⌊x·2^(−e)⌋·2^e` at `e = canonicalExp x`. -/
theorem rndDown_eq (F : FiniteFormat) (x : ℝ) :
    rndDown F x =
      Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋ (F.canonicalExp x) :=
  RoundsFinite.toNegative_eq_floor F x
    (rndUnbounded_satisfies_toNegative F x (not_isUndefined_toNegative F))

theorem rndDown_spec (F : FiniteFormat) (x : ℝ) :
    RoundsFinite F.unbounded .toNegative x (rndDown F x) :=
  rndUnbounded_satisfies_toNegative F x (not_isUndefined_toNegative F)

theorem rndDown_le (F : FiniteFormat) (x : ℝ) : (rndDown F x : ℝ) ≤ x :=
  (rndDown_spec F x).2.1

theorem rndDown_mem (F : FiniteFormat) (x : ℝ) : rndDown F x ∈ F.unbounded :=
  (rndDown_spec F x).1

theorem rndDown_max (F : FiniteFormat) (x : ℝ) {z : Dyadic}
    (hz : z ∈ F.unbounded) (hzx : (z : ℝ) ≤ x) : (z : ℝ) ≤ (rndDown F x : ℝ) :=
  (rndDown_spec F x).2.2 z hz hzx

theorem lt_rndDown_add_ulp (F : FiniteFormat) {x : ℝ}
    (hx : ¬(x = 0 ∧ F.exp = ⊥)) :
    x < (rndDown F x : ℝ) + ulp F x := by
  rw [rndDown_eq, Dyadic.coe_ofIntZpow]
  set e := F.canonicalExp x with he
  set t := x * (2 : ℝ) ^ (-e) with ht
  have h2 : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have hxt : x = t * (2 : ℝ) ^ e := by rw [ht, mul_zpow_neg_self]
  have hfloor : t < (⌊t⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hlt : t * (2 : ℝ) ^ e < ((⌊t⌋ : ℝ) + 1) * (2 : ℝ) ^ e :=
    mul_lt_mul_of_pos_right hfloor h2
  rw [← hxt] at hlt
  have hulp : ulp F x = (2 : ℝ) ^ e := by rw [ulp_eq_zpow_of F hx, ← he]
  rw [hulp]
  nlinarith [hlt]

/-- **Midpoint** bracketing `x`: `rndDown F x + ulp F x / 2` (Flocq `midp`). -/
noncomputable def midp (F : FiniteFormat) (x : ℝ) : ℝ :=
  (rndDown F x : ℝ) + ulp F x / 2

@[simp] theorem rndDown_zero (F : FiniteFormat) : rndDown F 0 = 0 :=
  RoundsFinite.eq_zero_of_zero (rndDown_spec F 0)

/-- Without a minimum quantum `0` is its own midpoint, so any strict comparison
of `ξ` against `midp F ξ` rules the `ulp` guard out. -/
theorem ulp_guard_of_midp_ne {F : FiniteFormat} {ξ : ℝ} (h : ξ ≠ midp F ξ) :
    ¬(ξ = 0 ∧ F.exp = ⊥) := by
  rintro ⟨rfl, hb⟩
  exact h (by rw [midp, ulp, if_pos ⟨rfl, hb⟩, rndDown_zero]; norm_num)

/-! ## Round-up companion -/

/-- **Round-up** — round-toward-`+∞` value of `x` in `F` (Flocq `round … Zceil`). -/
noncomputable def rndUp (F : FiniteFormat) (x : ℝ) : Dyadic :=
  rndUnbounded F .toPositive x (not_isUndefined_toPositive F)

theorem rndUp_spec (F : FiniteFormat) (x : ℝ) :
    RoundsFinite F.unbounded .toPositive x (rndUp F x) :=
  rndUnbounded_satisfies_toPositive F x (not_isUndefined_toPositive F)

theorem le_rndUp (F : FiniteFormat) (x : ℝ) : x ≤ (rndUp F x : ℝ) :=
  (rndUp_spec F x).2.1

theorem rndUp_mem (F : FiniteFormat) (x : ℝ) : rndUp F x ∈ F.unbounded :=
  (rndUp_spec F x).1

theorem rndUp_min (F : FiniteFormat) (x : ℝ) {z : Dyadic}
    (hz : z ∈ F.unbounded) (hxz : x ≤ (z : ℝ)) : (rndUp F x : ℝ) ≤ (z : ℝ) :=
  (rndUp_spec F x).2.2 z hz hxz

@[simp] theorem rndUp_zero (F : FiniteFormat) : rndUp F 0 = 0 :=
  RoundsFinite.eq_zero_of_zero (rndUp_spec F 0)

/-- The round-up is within one ulp of the round-down. -/
theorem rndUp_le_rndDown_add_ulp (F : FiniteFormat) (x : ℝ) :
    (rndUp F x : ℝ) ≤ (rndDown F x : ℝ) + ulp F x := by
  by_cases hx : x = 0 ∧ F.exp = ⊥
  · obtain ⟨rfl, hb⟩ := hx
    rw [ulp, if_pos ⟨rfl, hb⟩, rndDown_zero, rndUp_zero, Dyadic.coe_real_zero]
    norm_num
  set e := F.canonicalExp x with he
  set d : Dyadic := Dyadic.ofIntZpow (⌊x * (2 : ℝ) ^ (-e)⌋ + 1) e with hd
  have hd_real : (d : ℝ) = (rndDown F x : ℝ) + ulp F x := by
    rw [hd, Dyadic.coe_ofIntZpow, rndDown_eq, Dyadic.coe_ofIntZpow,
        ulp_eq_zpow_of F hx, ← he]
    push_cast; ring
  have hd_mem : d ∈ F.unbounded := by
    rw [hd]
    refine ofIntZpow_mem_unbounded F (fun hexp => F.exp_le_canonicalExp x hexp)
      (fun {p} hp => ?_)
    have hfl := abs_floor_add_one_le_of_abs_lt (floor_mantissa_lt (F := F) (x := x) hp)
    rw [← he] at hfl
    exact hfl
  have hx_le_d : x ≤ (d : ℝ) := by
    rw [hd_real]; exact (lt_rndDown_add_ulp F hx).le
  have := rndUp_min F x hd_mem hx_le_d
  rwa [hd_real] at this

/-- If `F₂`'s canonical exponent at `x` is strictly below `F₁`'s, then
`ulp F₂ x ≤ ulp F₁ x / 2` (integer exponents differ by at least one). -/
theorem ulp_le_half_ulp_of_canonicalExp_lt {F₁ F₂ : FiniteFormat} {x : ℝ}
    (hx : x ≠ 0) (h : F₂.canonicalExp x < F₁.canonicalExp x) :
    ulp F₂ x ≤ ulp F₁ x / 2 := by
  rw [ulp_of_ne_zero F₁ hx, ulp_of_ne_zero F₂ hx]
  have hle : F₂.canonicalExp x ≤ F₁.canonicalExp x - 1 := by omega
  calc (2 : ℝ) ^ F₂.canonicalExp x
      ≤ (2 : ℝ) ^ (F₁.canonicalExp x - 1) := zpow_le_zpow_right₀ (by norm_num) hle
    _ = (2 : ℝ) ^ F₁.canonicalExp x / 2 := by
        rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]; norm_num

/-- **Nearest error bound.** A round-to-nearest value `z` of `x` is within half
an ulp of `x`. Stated over `F.unbounded`, where the directed competitors always
exist. -/
theorem nearest_error_le_half_ulp {F : FiniteFormat} {tb : TieBreak} {x : ℝ}
    {z : Dyadic} (h : RoundsFinite F.unbounded (.nearest tb) x z) :
    |(z : ℝ) - x| ≤ ulp F x / 2 := by
  have hclose : ∀ c : Dyadic, c ∈ F.unbounded → IsFaithfulRound F.unbounded x c →
      |x - (z : ℝ)| ≤ |x - (c : ℝ)| := by
    cases tb with
    | toEven => exact h.2.2.1
    | awayZero => exact h.2.2.1
  have haf : IsFaithfulRound F.unbounded x (rndDown F x) :=
    Or.inl ⟨rndDown_mem F x, rndDown_le F x, fun v hv hvx => rndDown_max F x hv hvx⟩
  have ha'f : IsFaithfulRound F.unbounded x (rndUp F x) :=
    Or.inr ⟨rndUp_mem F x, le_rndUp F x, fun v hv hxv => rndUp_min F x hv hxv⟩
  have h1 : |x - (z : ℝ)| ≤ |x - (rndDown F x : ℝ)| := hclose _ (rndDown_mem F x) haf
  have h2 : |x - (z : ℝ)| ≤ |x - (rndUp F x : ℝ)| := hclose _ (rndUp_mem F x) ha'f
  have hax : (rndDown F x : ℝ) ≤ x := rndDown_le F x
  have hxa' : x ≤ (rndUp F x : ℝ) := le_rndUp F x
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - (rndDown F x : ℝ))] at h1
  rw [abs_of_nonpos (by linarith : x - (rndUp F x : ℝ) ≤ 0), neg_sub] at h2
  have hulp : (rndUp F x : ℝ) - (rndDown F x : ℝ) ≤ ulp F x := by
    have := rndUp_le_rndDown_add_ulp F x; linarith
  rw [abs_sub_comm]
  linarith

/-- **Nearest of a value close to a grid point.** If `v`'s scaled mantissa is
within `½` of an integer `m`, then the grid point `m · 2^(canonicalExp v)` is the
nearest rounding of `v` (either tie-break), whichever side of `m` the scaled
mantissa falls on. -/
theorem nearest_eq_of_close (F : FiniteFormat) (tb : TieBreak) (v : ℝ)
    (hundef : ¬ F.IsUndefined (.nearest tb)) {m : ℤ}
    (h : |v * (2 : ℝ) ^ (-(F.canonicalExp v)) - (m : ℝ)| < 1 / 2) :
    RoundsFinite F.unbounded (.nearest tb) v (Dyadic.ofIntZpow m (F.canonicalExp v)) := by
  have hspec := rndUnbounded_satisfies_nearest F tb v hundef
  suffices heq : rndUnbounded F (.nearest tb) v hundef = Dyadic.ofIntZpow m (F.canonicalExp v) by
    rw [← heq]; exact hspec
  set e := F.canonicalExp v with he
  rw [abs_lt] at h
  rcases lt_or_ge (v * (2 : ℝ) ^ (-e)) (m : ℝ) with hsm | hsm
  · -- `s < m`: floor is `m − 1`, fraction `> ½`, both modes select the ceiling `m`.
    have hfloor : ⌊v * (2 : ℝ) ^ (-e)⌋ = m - 1 := by
      rw [Int.floor_eq_iff]; refine ⟨?_, ?_⟩ <;> push_cast <;> linarith [h.1, hsm]
    have hδ : (1 : ℝ) / 2 < v * (2 : ℝ) ^ (-e) - (⌊v * (2 : ℝ) ^ (-e)⌋ : ℝ) := by
      rw [hfloor]; push_cast; linarith [h.1]
    have hδ_not : ¬ v * (2 : ℝ) ^ (-e) - (⌊v * (2 : ℝ) ^ (-e)⌋ : ℝ) < 1 / 2 :=
      not_lt.mpr (le_of_lt hδ)
    cases tb with
    | awayZero =>
      unfold rndUnbounded
      rw [dif_neg (by decide : (RoundingMode.nearest .awayZero) ≠ .toOdd),
          dif_neg (by decide : (RoundingMode.nearest .awayZero) ≠ .nearest .toEven)]
      simp only [rndInt, ← he, if_neg hδ_not, if_pos hδ]
      rw [hfloor]; congr 1; omega
    | toEven =>
      unfold rndUnbounded
      rw [dif_neg (by decide : (RoundingMode.nearest .toEven) ≠ .toOdd), dif_pos rfl]
      simp only [rndParity, ← he, if_neg hδ_not, if_pos hδ]
      rw [hfloor]; congr 1; omega
  · -- `s ≥ m`: floor is `m`, fraction `< ½`, both modes select the floor `m`.
    have hfloor : ⌊v * (2 : ℝ) ^ (-e)⌋ = m := by
      rw [Int.floor_eq_iff]; exact ⟨hsm, by linarith [h.2]⟩
    have hδ : v * (2 : ℝ) ^ (-e) - (⌊v * (2 : ℝ) ^ (-e)⌋ : ℝ) < 1 / 2 := by
      rw [hfloor]; linarith [h.2]
    cases tb with
    | awayZero =>
      unfold rndUnbounded
      rw [dif_neg (by decide : (RoundingMode.nearest .awayZero) ≠ .toOdd),
          dif_neg (by decide : (RoundingMode.nearest .awayZero) ≠ .nearest .toEven)]
      simp only [rndInt, ← he, if_pos hδ]
      rw [hfloor]
    | toEven =>
      unfold rndUnbounded
      rw [dif_neg (by decide : (RoundingMode.nearest .toEven) ≠ .toOdd), dif_pos rfl]
      simp only [rndParity, ← he, if_pos hδ]
      rw [hfloor]

/-- Dyadic-grid-point form of `nearest_eq_of_close`: if `g ∈ F`-grid at `v`'s
scale (`quantumAtLeast (canonicalExp v) g`) and `|v − g| < ½·ulp F v`, then `g`
is the nearest rounding of `v`. -/
theorem nearest_eq_of_close' (F : FiniteFormat) (tb : TieBreak) (v : ℝ)
    (hundef : ¬ F.IsUndefined (.nearest tb)) {g : Dyadic}
    (hg : Dyadic.quantumAtLeast ((F.canonicalExp v : ℤ) : QExp) g)
    (hclose : |v - (g : ℝ)| < (2 : ℝ) ^ (F.canonicalExp v) / 2) :
    RoundsFinite F.unbounded (.nearest tb) v g := by
  obtain ⟨m, hm⟩ := (Dyadic.quantumAtLeast_coe_real (F.canonicalExp v) g).mp hg
  have hgeq : Dyadic.ofIntZpow m (F.canonicalExp v) = g :=
    (Dyadic.coe_real_inj _ _).mp (by rw [Dyadic.coe_ofIntZpow, hm])
  rw [← hgeq]
  refine nearest_eq_of_close F tb v hundef ?_
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (-(F.canonicalExp v)) := zpow_pos (by norm_num) _
  have hrw : v * (2 : ℝ) ^ (-(F.canonicalExp v)) - (m : ℝ)
      = (v - (g : ℝ)) * (2 : ℝ) ^ (-(F.canonicalExp v)) := by
    rw [hm, sub_mul, mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), add_neg_cancel,
        zpow_zero, mul_one]
  rw [hrw, abs_mul, abs_of_pos h2pos]
  have hcc : (2 : ℝ) ^ (F.canonicalExp v) * (2 : ℝ) ^ (-(F.canonicalExp v)) = 1 := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), add_neg_cancel, zpow_zero]
  calc |v - (g : ℝ)| * (2 : ℝ) ^ (-(F.canonicalExp v))
      < (2 : ℝ) ^ (F.canonicalExp v) / 2 * (2 : ℝ) ^ (-(F.canonicalExp v)) :=
        mul_lt_mul_of_pos_right hclose h2pos
    _ = 1 / 2 := by rw [div_mul_eq_mul_div, hcc]

/-- **Below-midpoint ⟹ nearest rounds down.** If `ξ` lies strictly below its
`F`-midpoint, its round-to-nearest value (either tie-break) is `rndDown F ξ`. -/
theorem nearest_eq_rndDown_of_lt_midp (F : FiniteFormat) (tb : TieBreak) (ξ : ℝ)
    (hundef : ¬ F.IsUndefined (.nearest tb)) (hlt : ξ < midp F ξ) :
    RoundsFinite F.unbounded (.nearest tb) ξ (rndDown F ξ) := by
  set e := F.canonicalExp ξ with he
  have h2e : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have hξ : ξ = (ξ * (2 : ℝ) ^ (-e)) * (2 : ℝ) ^ e := (mul_zpow_neg_self ξ e).symm
  have hmid : midp F ξ =
      (⌊ξ * (2 : ℝ) ^ (-e)⌋ : ℝ) * (2 : ℝ) ^ e + (2 : ℝ) ^ e / 2 := by
    rw [midp, ulp_eq_zpow_of F (ulp_guard_of_midp_ne (ne_of_lt hlt)), rndDown_eq,
      Dyadic.coe_ofIntZpow, ← he]
  have hδ : ξ * (2 : ℝ) ^ (-e) - (⌊ξ * (2 : ℝ) ^ (-e)⌋ : ℝ) < 1 / 2 := by
    rw [hmid] at hlt; nlinarith [hlt, h2e, hξ]
  have hclose : |ξ * (2 : ℝ) ^ (-e) - (⌊ξ * (2 : ℝ) ^ (-e)⌋ : ℝ)| < 1 / 2 := by
    rw [abs_lt]; exact ⟨by linarith [Int.floor_le (ξ * (2 : ℝ) ^ (-e))], hδ⟩
  rw [rndDown_eq]
  exact nearest_eq_of_close F tb ξ hundef (he ▸ hclose)

/-- `⌈x·2^(−e)⌉·2^e`. -/
theorem rndUp_eq (F : FiniteFormat) (x : ℝ) :
    rndUp F x =
      Dyadic.ofIntZpow ⌈x * (2 : ℝ) ^ (-(F.canonicalExp x))⌉ (F.canonicalExp x) :=
  RoundsFinite.toPositive_eq_ceil F x
    (rndUnbounded_satisfies_toPositive F x (not_isUndefined_toPositive F))

/-- **Above-midpoint ⟹ nearest rounds up**, mirroring
`nearest_eq_rndDown_of_lt_midp`. -/
theorem nearest_eq_rndUp_of_midp_lt (F : FiniteFormat) (tb : TieBreak) (ξ : ℝ)
    (hundef : ¬ F.IsUndefined (.nearest tb)) (hlt : midp F ξ < ξ) :
    RoundsFinite F.unbounded (.nearest tb) ξ (rndUp F ξ) := by
  set e := F.canonicalExp ξ with he
  have h2e : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have hξ : ξ = (ξ * (2 : ℝ) ^ (-e)) * (2 : ℝ) ^ e := (mul_zpow_neg_self ξ e).symm
  have hmid : midp F ξ =
      (⌊ξ * (2 : ℝ) ^ (-e)⌋ : ℝ) * (2 : ℝ) ^ e + (2 : ℝ) ^ e / 2 := by
    rw [midp, ulp_eq_zpow_of F (ulp_guard_of_midp_ne (ne_of_gt hlt)), rndDown_eq,
      Dyadic.coe_ofIntZpow, ← he]
  have hδ : (1 : ℝ) / 2 < ξ * (2 : ℝ) ^ (-e) - (⌊ξ * (2 : ℝ) ^ (-e)⌋ : ℝ) := by
    rw [hmid] at hlt; nlinarith [hlt, h2e, hξ]
  have hceil : ⌈ξ * (2 : ℝ) ^ (-e)⌉ = ⌊ξ * (2 : ℝ) ^ (-e)⌋ + 1 := by
    have hfloor_lt : (⌊ξ * (2 : ℝ) ^ (-e)⌋ : ℝ) < ξ * (2 : ℝ) ^ (-e) := by linarith
    have h1 : ⌈ξ * (2 : ℝ) ^ (-e)⌉ ≤ ⌊ξ * (2 : ℝ) ^ (-e)⌋ + 1 := Int.ceil_le_floor_add_one _
    have h2 : ⌊ξ * (2 : ℝ) ^ (-e)⌋ < ⌈ξ * (2 : ℝ) ^ (-e)⌉ := by
      have : (⌊ξ * (2 : ℝ) ^ (-e)⌋ : ℝ) < (⌈ξ * (2 : ℝ) ^ (-e)⌉ : ℝ) :=
        lt_of_lt_of_le hfloor_lt (Int.le_ceil _)
      exact_mod_cast this
    omega
  have hclose : |ξ * (2 : ℝ) ^ (-e) - (⌈ξ * (2 : ℝ) ^ (-e)⌉ : ℝ)| < 1 / 2 := by
    rw [hceil]; push_cast; rw [abs_lt]
    exact ⟨by linarith [hδ], by linarith [Int.lt_floor_add_one (ξ * (2 : ℝ) ^ (-e))]⟩
  rw [rndUp_eq]
  exact nearest_eq_of_close F tb ξ hundef (he ▸ hclose)


/-- Round-down of `−x` is the negation of round-up of `x` (real value). -/
theorem rndDown_neg_real (F : FiniteFormat) (x : ℝ) :
    (rndDown F (-x) : ℝ) = -(rndUp F x : ℝ) := by
  rw [rndDown_eq, rndUp_eq, Dyadic.coe_ofIntZpow, Dyadic.coe_ofIntZpow, canonicalExp_neg,
      show (-x) * (2 : ℝ) ^ (-(F.canonicalExp x)) = -(x * (2 : ℝ) ^ (-(F.canonicalExp x)))
        from by ring, Int.floor_neg]
  push_cast; ring

/-! ## Error bounds -/

/-- A positive round-down pins `x` at or above the format's coarsest step:
below `2 ^ canonicalExp x` the floor collapses to `0`. -/
theorem canonicalExp_le_log_of_rndDown_pos (F : FiniteFormat) {x : ℝ}
    (h : 0 < ((rndDown F x : Dyadic) : ℝ)) : F.canonicalExp x ≤ Int.log 2 x := by
  have hx : 0 < x := lt_of_lt_of_le h (rndDown_le F x)
  set e := F.canonicalExp x with he
  by_contra hc
  push Not at hc
  have hxe : x * (2 : ℝ) ^ (-e) < 1 := by
    have hkhi : x < (2 : ℝ) ^ (Int.log 2 x + 1) := Int.lt_zpow_succ_log_self (by norm_num) x
    have h1 : x < (2 : ℝ) ^ e :=
      lt_of_lt_of_le hkhi (zpow_le_zpow_right₀ (by norm_num) (by omega))
    calc x * (2 : ℝ) ^ (-e) < (2 : ℝ) ^ e * (2 : ℝ) ^ (-e) := by
          nlinarith [zpow_pos (show (0:ℝ) < 2 by norm_num) (-e)]
      _ = 1 := by rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), add_neg_cancel, zpow_zero]
  have hfl : ⌊x * (2 : ℝ) ^ (-e)⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨by positivity, hxe⟩
  rw [rndDown_eq, Dyadic.coe_ofIntZpow, ← he, hfl] at h
  norm_num at h

/-- A positive round-down shares `x`'s canonical exponent: the floor cannot
leave `x`'s binade once `canonicalExp x ≤ ⌊log₂ x⌋`. -/
theorem canonicalExp_rndDown (F : FiniteFormat) {x : ℝ}
    (h : 0 < ((rndDown F x : Dyadic) : ℝ)) :
    F.canonicalExp ((rndDown F x : Dyadic) : ℝ) = F.canonicalExp x := by
  have hx : 0 < x := lt_of_lt_of_le h (rndDown_le F x)
  set e := F.canonicalExp x with he
  set k := Int.log 2 x with hk
  have hek : e ≤ k := canonicalExp_le_log_of_rndDown_pos F h
  have h2e : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have h2e' : (0 : ℝ) < (2 : ℝ) ^ (-e) := zpow_pos (by norm_num) _
  have hrd : ((rndDown F x : Dyadic) : ℝ) = (⌊x * (2 : ℝ) ^ (-e)⌋ : ℝ) * (2 : ℝ) ^ e := by
    rw [rndDown_eq, Dyadic.coe_ofIntZpow, ← he]
  have hklo : (2 : ℝ) ^ k ≤ x := Int.zpow_log_le_self (by norm_num) hx
  have hkhi : x < (2 : ℝ) ^ (k + 1) := Int.lt_zpow_succ_log_self (by norm_num) x
  have hlo : (2 : ℝ) ^ k ≤ ((rndDown F x : Dyadic) : ℝ) := by
    have hcast : (((2 : ℤ) ^ (k - e).toNat : ℤ) : ℝ) = (2 : ℝ) ^ (k - e) := by
      push_cast; rw [← zpow_natCast, Int.toNat_of_nonneg (by omega)]
    have hsplit : (2 : ℝ) ^ (k - e) = (2 : ℝ) ^ k * (2 : ℝ) ^ (-e) := by
      rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_neg, div_eq_mul_inv]
    have hnat : ((2 : ℤ) ^ (k - e).toNat : ℤ) ≤ ⌊x * (2 : ℝ) ^ (-e)⌋ := by
      rw [Int.le_floor, hcast, hsplit]
      exact mul_le_mul_of_nonneg_right hklo h2e'.le
    have hfl : (2 : ℝ) ^ (k - e) ≤ (⌊x * (2 : ℝ) ^ (-e)⌋ : ℝ) := by
      rw [← hcast]; exact_mod_cast hnat
    rw [hrd]
    calc (2 : ℝ) ^ k = (2 : ℝ) ^ (k - e) * (2 : ℝ) ^ e := by
          rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0),
            div_mul_cancel₀ _ (zpow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))]
      _ ≤ (⌊x * (2 : ℝ) ^ (-e)⌋ : ℝ) * (2 : ℝ) ^ e :=
          mul_le_mul_of_nonneg_right hfl h2e.le
  have hhi : ((rndDown F x : Dyadic) : ℝ) < (2 : ℝ) ^ (k + 1) :=
    lt_of_le_of_lt (rndDown_le F x) hkhi
  refine canonicalExp_eq_of_log_eq F (ne_of_gt h) (ne_of_gt hx) ?_
  rw [abs_of_pos h, abs_of_pos hx, log_eq_of_zpow_bounds h hlo hhi]

/-- **`ulp` is unchanged by rounding down** (Flocq `ulp_DN`). -/
theorem ulp_rndDown (F : FiniteFormat) {x : ℝ}
    (h : 0 < ((rndDown F x : Dyadic) : ℝ)) :
    ulp F ((rndDown F x : Dyadic) : ℝ) = ulp F x := by
  have hx : 0 < x := lt_of_lt_of_le h (rndDown_le F x)
  rw [ulp_of_ne_zero F (ne_of_gt h), ulp_of_ne_zero F (ne_of_gt hx), canonicalExp_rndDown F h]

/-- **Faithful error bound** (Flocq `error_lt_ulp`): any faithful rounding of a
nonzero `x` is within one ulp of it. -/
theorem faithful_error_lt_ulp {F : FiniteFormat} {x : ℝ} (hx : x ≠ 0) {y : Dyadic}
    (h : IsFaithfulRound F.unbounded x y) : |((y : Dyadic) : ℝ) - x| < ulp F x := by
  have hupos : (0 : ℝ) < ulp F x := ulp_pos F hx
  have hguard : ¬(x = 0 ∧ F.exp = ⊥) := by simp [hx]
  have hdn_le := rndDown_le F x
  have hlt := lt_rndDown_add_ulp F hguard
  rcases h with hd | hu
  · have hy : y = rndDown F x := RoundsFinite.unique_toNegative hd (rndDown_spec F x)
    rw [hy, abs_of_nonpos (by linarith), neg_sub]
    linarith
  · have hy : y = rndUp F x := RoundsFinite.unique_toPositive hu (rndUp_spec F x)
    have hle := rndUp_le_rndDown_add_ulp F x
    rw [hy, abs_of_nonneg (by linarith [le_rndUp F x])]
    rcases lt_or_eq_of_le hdn_le with hs | hs
    · linarith
    · -- `x` is representable, so the round-up is `x` itself
      have := rndUp_min F x (rndDown_mem F x) hs.ge
      rw [hs] at this
      linarith [le_rndUp F x]

/-- **Faithful error bound, non-strict.** Holds at `x = 0` too, where both sides
are `0` when there is no minimum quantum. -/
theorem faithful_error_le_ulp {F : FiniteFormat} (x : ℝ) {y : Dyadic}
    (h : IsFaithfulRound F.unbounded x y) : |((y : Dyadic) : ℝ) - x| ≤ ulp F x := by
  by_cases hx : x = 0
  · subst hx
    have hy0 : ((y : Dyadic) : ℝ) = 0 := by
      rcases h with hd | hu <;>
        [ have h0 := hd.2.2 0 (FiniteFormat.zero_mem _) (by rw [Dyadic.coe_real_zero]);
          have h0 := hu.2.2 0 (FiniteFormat.zero_mem _) (by rw [Dyadic.coe_real_zero]) ] <;>
        rw [Dyadic.coe_real_zero] at h0
      · linarith [hd.2.1]
      · linarith [hu.2.1]
    rw [hy0]; simpa using ulp_nonneg F 0
  · exact (faithful_error_lt_ulp hx h).le

/-- **Rounding up stays in the binade or lands on its top** — the round-up half
of Flocq `ulp_round`. `hdn` is the non-flush-to-zero side condition: it puts `x`
at or above the format's coarsest step, so `2 ^ (⌊log₂ x⌋ + 1)` is
representable and caps the round-up. -/
theorem ulp_rndUp_pos (F : FiniteFormat) {x : ℝ} (hx : 0 < x)
    (hdn : 0 < ((rndDown F x : Dyadic) : ℝ)) :
    ulp F ((rndUp F x : Dyadic) : ℝ) = ulp F x ∨
      ((rndUp F x : Dyadic) : ℝ) = (2 : ℝ) ^ (Int.log 2 x + 1) := by
  set k := Int.log 2 x with hk
  have hklo : (2 : ℝ) ^ k ≤ x := Int.zpow_log_le_self (by norm_num) hx
  have hup_ge : x ≤ ((rndUp F x : Dyadic) : ℝ) := le_rndUp F x
  have hup_pos : 0 < ((rndUp F x : Dyadic) : ℝ) := lt_of_lt_of_le hx hup_ge
  by_cases hlt : ((rndUp F x : Dyadic) : ℝ) < (2 : ℝ) ^ (k + 1)
  · left
    rw [ulp_of_ne_zero F (ne_of_gt hup_pos), ulp_of_ne_zero F (ne_of_gt hx)]
    refine congrArg _ (canonicalExp_eq_of_log_eq F (ne_of_gt hup_pos) (ne_of_gt hx) ?_)
    rw [abs_of_pos hup_pos, abs_of_pos hx,
      log_eq_of_zpow_bounds hup_pos (le_trans hklo hup_ge) hlt]
  · right
    push Not at hlt
    have hmem : Dyadic.ofIntZpow 1 (k + 1) ∈ F.unbounded :=
      ofIntZpow_mem_unbounded F
        (fun {e'} he' => by
          have := F.exp_le_canonicalExp x he'
          have := canonicalExp_le_log_of_rndDown_pos F hdn
          omega)
        (fun {p} _ => by simpa using one_le_pow₀ (by norm_num : (1 : ℤ) ≤ 2))
    have hcoe : ((Dyadic.ofIntZpow 1 (k + 1) : Dyadic) : ℝ) = (2 : ℝ) ^ (k + 1) := by
      rw [Dyadic.coe_ofIntZpow]; push_cast; ring
    have hkhi : x < (2 : ℝ) ^ (k + 1) := by
      rw [hk]; exact Int.lt_zpow_succ_log_self (by norm_num) x
    have hle := rndUp_min F x hmem (by rw [hcoe]; linarith)
    rw [hcoe] at hle
    linarith

/-- **`ulp` under rounding** (Flocq `ulp_round`), positive side: a faithful
rounding keeps `x`'s ulp unless it lands exactly on the top of `x`'s binade. -/
theorem ulp_round_pos (F : FiniteFormat) {x : ℝ} (hx : 0 < x)
    (hdn : 0 < ((rndDown F x : Dyadic) : ℝ)) {y : Dyadic}
    (h : IsFaithfulRound F.unbounded x y) :
    ulp F ((y : Dyadic) : ℝ) = ulp F x ∨
      ((y : Dyadic) : ℝ) = (2 : ℝ) ^ (Int.log 2 x + 1) := by
  rcases h with hd | hu
  · rw [RoundsFinite.unique_toNegative hd (rndDown_spec F x)]
    exact Or.inl (ulp_rndDown F hdn)
  · rw [RoundsFinite.unique_toPositive hu (rndUp_spec F x)]
    exact ulp_rndUp_pos F hx hdn

/-- The round-down is the nearest-to-zero faithful value, so a faithful rounding
never shrinks the ulp. -/
private theorem canonicalExp_le_of_faithful_pos {F : FiniteFormat} {x : ℝ} (hx : 0 < x)
    {y : Dyadic} (h : IsFaithfulRound F.unbounded x y) (hy : ((y : Dyadic) : ℝ) ≠ 0) :
    F.canonicalExp x ≤ F.canonicalExp ((y : Dyadic) : ℝ) := by
  rcases le_or_gt |x| |((y : Dyadic) : ℝ)| with hge | hlt
  · exact FiniteFormat.canonicalExp_mono F (ne_of_gt hx) hge
  · rw [abs_of_pos hx] at hlt
    have hylt : ((y : Dyadic) : ℝ) < x := lt_of_le_of_lt (le_abs_self _) hlt
    have hd : RoundsFinite F.unbounded .toNegative x y := by
      rcases h with hd | hu
      · exact hd
      · exact absurd hu.2.1 (not_le.mpr hylt)
    have hyeq : y = rndDown F x := RoundsFinite.unique_toNegative hd (rndDown_spec F x)
    have h0 := hd.2.2 0 (FiniteFormat.zero_mem _) (by rw [Dyadic.coe_real_zero]; linarith)
    rw [Dyadic.coe_real_zero] at h0
    rw [hyeq, canonicalExp_rndDown F (by rw [← hyeq]; exact lt_of_le_of_ne h0 (Ne.symm hy))]

/-- **`ulp` does not shrink under rounding.** -/
theorem ulp_le_ulp_of_faithful {F : FiniteFormat} {x : ℝ} (hx : x ≠ 0) {y : Dyadic}
    (h : IsFaithfulRound F.unbounded x y) (hy : ((y : Dyadic) : ℝ) ≠ 0) :
    ulp F x ≤ ulp F ((y : Dyadic) : ℝ) := by
  rw [ulp_of_ne_zero F hx, ulp_of_ne_zero F hy]
  refine zpow_le_zpow_right₀ (by norm_num) ?_
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have h' : IsFaithfulRound F.unbounded (-x) (-y) := (IsFaithfulRound.neg_iff _ _ _).mp h
    have := canonicalExp_le_of_faithful_pos (by linarith : (0 : ℝ) < -x) h'
      (by rw [Dyadic.coe_real_neg]; simpa using hy)
    rwa [canonicalExp_neg, Dyadic.coe_real_neg, canonicalExp_neg] at this
  · exact canonicalExp_le_of_faithful_pos hpos h hy

/-- **Nearest error bound at the rounded value** (Flocq `error_le_half_ulp_round`):
half an ulp *of the result*, not of the argument. -/
theorem nearest_error_le_half_ulp_round {F : FiniteFormat} {tb : TieBreak} {x : ℝ}
    (hx : x ≠ 0) {z : Dyadic} (hz : ((z : Dyadic) : ℝ) ≠ 0)
    (h : RoundsFinite F.unbounded (.nearest tb) x z) :
    |((z : Dyadic) : ℝ) - x| ≤ ulp F ((z : Dyadic) : ℝ) / 2 := by
  linarith [nearest_error_le_half_ulp h, ulp_le_ulp_of_faithful hx h.isFaithfulRound hz]

/-! ## Successor and predecessor

`succ` is uniform — `x + ulp x` on the non-negative side — but `pred` is not.
Under Goldberg's convention `ulp (2^k)` is the spacing of the binade *above*,
so stepping *down* from a power of two moves by half that. `predPos` carries
the special case; `pred` and the negative branch of `succ` reflect through it.
-/

/-- Predecessor of a positive real. At the bottom of a binade the step down is
the spacing of the binade below — `ulp` at `x/2`, which lies in it — rather than
`ulp x`. Flocq `pred_pos`. -/
noncomputable def predPos (F : FiniteFormat) (x : ℝ) : ℝ :=
  if x = (2 : ℝ) ^ Int.log 2 x then x - ulp F (x / 2) else x - ulp F x

/-- The next representable value at or above `x` (Flocq `succ`). -/
noncomputable def succ (F : FiniteFormat) (x : ℝ) : ℝ :=
  if 0 ≤ x then x + ulp F x else -predPos F (-x)

/-- The previous representable value at or below `x` (Flocq `pred`). -/
noncomputable def pred (F : FiniteFormat) (x : ℝ) : ℝ := -succ F (-x)

theorem succ_of_nonneg (F : FiniteFormat) {x : ℝ} (hx : 0 ≤ x) :
    succ F x = x + ulp F x := if_pos hx

theorem succ_of_neg (F : FiniteFormat) {x : ℝ} (hx : x < 0) :
    succ F x = -predPos F (-x) := if_neg (not_le.mpr hx)

/-- `x < succ x` away from zero (Flocq `succ_gt_id`). At `x = 0` with no
minimum quantum `succ 0 = 0`, so the hypothesis is needed. -/
theorem lt_succ (F : FiniteFormat) {x : ℝ} (hx0 : 0 ≤ x) (hne : x ≠ 0) :
    x < succ F x := by
  rw [succ_of_nonneg F hx0]
  linarith [ulp_pos F hne]

/-- `pred x < x` away from zero. At `x = 0` with no minimum quantum
`pred 0 = 0`, so the hypothesis is needed (Flocq `pred_lt_id`). -/
theorem pred_lt (F : FiniteFormat) {x : ℝ} (hne : x ≠ 0) : pred F x < x := by
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · -- `-x > 0`, so `succ` takes its non-negative branch
    rw [pred, succ_of_nonneg F (by linarith : (0:ℝ) ≤ -x), ulp_neg]
    linarith [ulp_pos F hne]
  · -- `-x < 0`, so `succ` reflects through `predPos`
    rw [pred, succ, if_neg (by linarith : ¬ (0:ℝ) ≤ -x)]
    simp only [neg_neg]
    unfold predPos
    split_ifs with h
    · have : (0:ℝ) < x / 2 := by linarith
      linarith [ulp_pos F (ne_of_gt this)]
    · linarith [ulp_pos F hne]

/-- **`succ` really is the next value**: no `F`-element lies strictly between
`x` and `succ x` (Flocq `succ_le_lt`). Both values share `x`'s canonical
exponent as a common quantum, so `y > x` forces `y` a whole step up. -/
theorem succ_le_of_lt (F : FiniteFormat) {p : ℕ} (hp : F.p = (p : Prec))
    {x y : Dyadic} (hx : x ∈ F.unbounded) (hy : y ∈ F.unbounded)
    (hx0 : 0 < ((x : Dyadic) : ℝ)) (hlt : ((x : Dyadic) : ℝ) < ((y : Dyadic) : ℝ)) :
    succ F (x : ℝ) ≤ ((y : Dyadic) : ℝ) := by
  have hy0 : (0:ℝ) < ((y : Dyadic) : ℝ) := lt_trans hx0 hlt
  have hxne : ((x : Dyadic) : ℝ) ≠ 0 := ne_of_gt hx0
  set ex := F.canonicalExp ((x : Dyadic) : ℝ) with hex
  set ey := F.canonicalExp ((y : Dyadic) : ℝ) with hey
  have hmono : ex ≤ ey := by
    rw [hex, hey]
    exact FiniteFormat.canonicalExp_mono F hxne (by rw [abs_of_pos hx0, abs_of_pos hy0]; linarith)
  obtain ⟨cx, -, hxeq⟩ := exists_canonical_rep F.unbounded hp hx hx0
  rw [FiniteFormat.unbounded_canonicalExp] at hxeq
  obtain ⟨cy, -, hyeq⟩ := exists_canonical_rep F.unbounded hp hy hy0
  rw [FiniteFormat.unbounded_canonicalExp] at hyeq
  have h2 : (0:ℝ) < (2:ℝ) ^ ex := zpow_pos (by norm_num) _
  -- `y` sits on `x`'s grid: `2^ey = 2^(ey-ex) * 2^ex` with a whole-number factor
  have hulp : ((y : Dyadic) : ℝ)
      = ((cy * (2:ℤ) ^ (ey - ex).toNat : ℤ) : ℝ) * (2:ℝ) ^ ex := by
    rw [hyeq, ← hey]
    push_cast
    rw [mul_assoc, ← zpow_natCast (2:ℝ) (ey - ex).toNat,
        Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ ey - ex), ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
    ring_nf
  -- both are integer multiples of `2^ex`, and `y > x`, so `y ≥ x + 2^ex`
  have hlt_int : cx < cy * (2:ℤ) ^ (ey - ex).toNat := by
    have := hlt
    rw [hxeq, ← hex, hulp] at this
    exact_mod_cast (mul_lt_mul_iff_of_pos_right h2).mp this
  rw [succ_of_nonneg F hx0.le, ulp_of_ne_zero F hxne, ← hex, hxeq, ← hex, hulp]
  have : (cx : ℝ) + 1 ≤ ((cy * (2:ℤ) ^ (ey - ex).toNat : ℤ) : ℝ) := by exact_mod_cast hlt_int
  nlinarith [h2]

/-- On the positive side `pred` coincides with `predPos`. -/
theorem pred_eq_predPos (F : FiniteFormat) {x : ℝ} (hx : 0 < x) :
    pred F x = predPos F x := by
  rw [pred, succ, if_neg (by linarith : ¬ (0:ℝ) ≤ -x)]; simp only [neg_neg]

/-- A positive `F`-value is at least the format's quantum, so `F.exp ≤ ⌊log₂ z⌋`. -/
theorem exp_le_log_of_mem (F : FiniteFormat) {e : ℤ} (hexp : F.exp = (e : QExp))
    {z : Dyadic} (hz : z ∈ F.unbounded) (hz0 : 0 < ((z : Dyadic) : ℝ)) :
    e ≤ Int.log 2 ((z : Dyadic) : ℝ) := by
  obtain ⟨-, hq, -⟩ := hz
  rw [FiniteFormat.unbounded_exp, hexp, Dyadic.quantumAtLeast_coe_real] at hq
  obtain ⟨c, hc⟩ := hq
  have h2e : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have hc1 : (1 : ℝ) ≤ (c : ℝ) := by
    by_contra hcc
    push Not at hcc
    have h0 : (c : ℤ) ≤ 0 := by exact_mod_cast Int.lt_add_one_iff.mp (by exact_mod_cast hcc)
    have : (c : ℝ) ≤ 0 := by exact_mod_cast h0
    nlinarith
  have hge : (2 : ℝ) ^ e ≤ ((z : Dyadic) : ℝ) := by nlinarith
  exact (Int.zpow_le_iff_le_log (by norm_num) hz0).mp (by exact_mod_cast hge)

/-- `canonicalExp` at a power of two is capped by any bound that caps both the
precision drop and `F.exp`. -/
theorem canonicalExp_zpow_le (F : FiniteFormat) {p : ℕ} (hp : F.p = (p : Prec))
    {m k : ℤ} (hmk : m ≤ k) (hexp : ∀ e : ℤ, F.exp = (e : QExp) → e ≤ k) :
    F.canonicalExp ((2 : ℝ) ^ m) ≤ k := by
  have hpp : 0 < p := FiniteFormat.p_pos hp
  have hpos : (0 : ℝ) < (2 : ℝ) ^ m := zpow_pos (by norm_num) _
  have hlog : Int.log 2 |((2 : ℝ) ^ m)| = m := by
    rw [abs_of_pos hpos]; exact log_two_zpow m
  unfold FiniteFormat.canonicalExp
  cases hexp' : F.exp using QExp.recBotCoe with
  | bot => simp only [hp, hlog, if_neg (ne_of_gt hpos)]; omega
  | coe e =>
    simp only [hp, hlog, if_neg (ne_of_gt hpos)]
    exact max_le (by omega) (hexp e hexp')

/-- A positive `F`-value sits at or above the format's coarsest step:
`canonicalExp z ≤ ⌊log₂ z⌋`. -/
theorem canonicalExp_le_log_of_mem (F : FiniteFormat) {p : ℕ} (hp : F.p = (p : Prec))
    {z : Dyadic} (hz : z ∈ F.unbounded) (hz0 : 0 < ((z : Dyadic) : ℝ)) :
    F.canonicalExp ((z : Dyadic) : ℝ) ≤ Int.log 2 ((z : Dyadic) : ℝ) := by
  have hpp : 0 < p := FiniteFormat.p_pos hp
  unfold FiniteFormat.canonicalExp
  cases hexp : F.exp using QExp.recBotCoe with
  | bot => simp only [hp, if_neg (ne_of_gt hz0), abs_of_pos hz0]; omega
  | coe e =>
    simp only [hp, if_neg (ne_of_gt hz0), abs_of_pos hz0]
    exact max_le (by omega) (exp_le_log_of_mem F hexp hz hz0)

/-- The predecessor of a positive `F`-value is an `F`-value. Away from a binade
floor it is one grid step down; at a floor the step is the finer one from the
binade below, and `k - e' ≤ p` keeps the coefficient in range. -/
theorem pred_mem (F : FiniteFormat) {p : ℕ} (hp : F.p = (p : Prec))
    {x : Dyadic} (hx : x ∈ F.unbounded) (hx0 : 0 < ((x : Dyadic) : ℝ)) :
    ∃ y : Dyadic, y ∈ F.unbounded ∧ ((y : Dyadic) : ℝ) = pred F ((x : Dyadic) : ℝ) := by
  have hxne : ((x : Dyadic) : ℝ) ≠ 0 := ne_of_gt hx0
  rw [pred_eq_predPos F hx0]
  unfold predPos
  split_ifs with hbf
  · -- binade floor: step down by the spacing of the binade below
    set k := Int.log 2 ((x : Dyadic) : ℝ) with hk
    have hhalf : ((x : Dyadic) : ℝ) / 2 = (2 : ℝ) ^ (k - 1) := by
      rw [hbf, zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0), zpow_one]
    have hpos2 : (0:ℝ) < (2:ℝ) ^ (k - 1) := by positivity
    set e' := F.canonicalExp ((2:ℝ) ^ (k - 1)) with he'
    have he'_le : e' ≤ k := by
      rw [he']
      exact canonicalExp_zpow_le F hp (by omega)
        (fun e hexp => by rw [hk]; exact exp_le_log_of_mem F hexp hx hx0)
    have he'_ge : k - (p : ℤ) ≤ e' := by
      rw [he']
      unfold FiniteFormat.canonicalExp
      have hlog : Int.log 2 |((2:ℝ) ^ (k-1))| = k - 1 := by
        rw [abs_of_pos hpos2]; exact log_two_zpow (k-1)
      cases hexp : F.exp using QExp.recBotCoe with
      | bot => simp only [hp, hlog, if_neg (ne_of_gt hpos2)]; omega
      | coe q => simp only [hp, hlog, if_neg (ne_of_gt hpos2)]; exact le_max_of_le_left (by omega)
    refine ⟨Dyadic.ofIntZpow ((2:ℤ) ^ (k - e').toNat - 1) e', ?_, ?_⟩
    · refine ofIntZpow_mem_unbounded F (fun hexp => ?_) (fun {p'} hp' => ?_)
      · rw [he']; exact F.exp_le_canonicalExp _ hexp
      · have hpp : p' = p := by have := hp'.symm.trans hp; exact_mod_cast this
        have h1 : (k - e').toNat ≤ p := by omega
        have hle : (2:ℤ) ^ (k - e').toNat ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) h1
        have h1le : (1:ℤ) ≤ (2:ℤ) ^ (k - e').toNat := one_le_pow₀ (by norm_num)
        rw [hpp, abs_of_nonneg (by linarith : (0:ℤ) ≤ (2:ℤ) ^ (k - e').toNat - 1)]
        linarith
    · rw [Dyadic.coe_ofIntZpow, hhalf, ulp_of_ne_zero F (ne_of_gt hpos2), ← he', hbf]
      push_cast
      rw [sub_mul, one_mul, ← zpow_natCast (2:ℝ) (k - e').toNat,
          Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ k - e'),
          ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
      ring_nf
  · -- interior: one grid step down
    obtain ⟨c, hc, hxeq⟩ := exists_canonical_rep F.unbounded hp hx hx0
    rw [FiniteFormat.unbounded_canonicalExp] at hxeq
    have hcpos : 0 < c := by
      by_contra hcc
      push Not at hcc
      have : (c : ℝ) ≤ 0 := by exact_mod_cast hcc
      nlinarith [zpow_pos (by norm_num : (0:ℝ) < 2) (F.canonicalExp ((x : Dyadic) : ℝ)), hx0, hxeq]
    refine ⟨Dyadic.ofIntZpow (c - 1) (F.canonicalExp ((x : Dyadic) : ℝ)), ?_, ?_⟩
    · refine ofIntZpow_mem_unbounded F (fun hexp => F.exp_le_canonicalExp _ hexp)
        (fun {p'} hp' => ?_)
      have hpp : p' = p := by have := hp'.symm.trans hp; exact_mod_cast this
      rw [hpp, abs_of_nonneg (by omega : (0:ℤ) ≤ c - 1)]
      rw [abs_of_pos hcpos] at hc
      omega
    · rw [Dyadic.coe_ofIntZpow, ulp_of_ne_zero F hxne]
      push_cast; linear_combination -hxeq

/-! ## The `succ` / `pred` involutions -/

/-- With a minimum quantum, `canonicalExp` at `0` is that quantum. -/
theorem canonicalExp_zero (F : FiniteFormat) {e : ℤ} (hexp : F.exp = (e : QExp)) :
    F.canonicalExp 0 = e := by
  unfold FiniteFormat.canonicalExp
  cases F.p using ENat.recTopCoe with
  | top => simp only [hexp]; rfl
  | coe p => simp [hexp]

/-- Two integer multiples of `2 ^ e` that differ are a full step apart. -/
private theorem step_le_of_lt_aligned {c₁ c₂ e : ℤ}
    (h : (c₁ : ℝ) * (2 : ℝ) ^ e < (c₂ : ℝ) * (2 : ℝ) ^ e) :
    (c₁ : ℝ) * (2 : ℝ) ^ e + (2 : ℝ) ^ e ≤ (c₂ : ℝ) * (2 : ℝ) ^ e := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have hc : c₁ < c₂ := by exact_mod_cast (mul_lt_mul_iff_of_pos_right h2).mp h
  have : (c₁ : ℝ) + 1 ≤ (c₂ : ℝ) := by exact_mod_cast hc
  nlinarith

/-- **Binade walls.** A positive `F`-value is an integer multiple of its own ulp
inside `[2^k, 2^(k+1))`, so it clears the top wall by a full ulp and — unless it
*is* the bottom wall — the bottom one too. -/
theorem binade_walls (F : FiniteFormat) {p : ℕ} (hp : F.p = (p : Prec))
    {z : Dyadic} (hz : z ∈ F.unbounded) (hz0 : 0 < ((z : Dyadic) : ℝ)) :
    ((z : Dyadic) : ℝ) + ulp F ((z : Dyadic) : ℝ)
        ≤ (2 : ℝ) ^ (Int.log 2 ((z : Dyadic) : ℝ) + 1) ∧
      (((z : Dyadic) : ℝ) ≠ (2 : ℝ) ^ (Int.log 2 ((z : Dyadic) : ℝ)) →
        (2 : ℝ) ^ (Int.log 2 ((z : Dyadic) : ℝ)) + ulp F ((z : Dyadic) : ℝ)
          ≤ ((z : Dyadic) : ℝ)) := by
  set v := ((z : Dyadic) : ℝ) with hv
  set k := Int.log 2 v with hk
  set e := F.canonicalExp v with he
  have hek : e ≤ k := canonicalExp_le_log_of_mem F hp hz hz0
  have hu : ulp F v = (2 : ℝ) ^ e := by rw [ulp_of_ne_zero F (ne_of_gt hz0), ← he]
  obtain ⟨c, -, hveq⟩ := exists_canonical_rep F.unbounded hp hz hz0
  rw [FiniteFormat.unbounded_canonicalExp, ← hv, ← he] at hveq
  have hwall : ∀ m : ℤ, e ≤ m →
      (2 : ℝ) ^ m = (((2 : ℤ) ^ (m - e).toNat : ℤ) : ℝ) * (2 : ℝ) ^ e := by
    intro m hm; rw [two_zpow_split m e hm]; push_cast; ring
  have hklo : (2 : ℝ) ^ k ≤ v := Int.zpow_log_le_self (by norm_num) hz0
  have hkhi : v < (2 : ℝ) ^ (k + 1) := Int.lt_zpow_succ_log_self (by norm_num) v
  refine ⟨?_, fun hne => ?_⟩
  · have := step_le_of_lt_aligned (c₁ := c) (c₂ := (2 : ℤ) ^ (k + 1 - e).toNat) (e := e)
      (by rw [← hveq, ← hwall (k + 1) (by omega)]; exact hkhi)
    rw [← hveq, ← hwall (k + 1) (by omega), ← hu] at this
    exact this
  · have := step_le_of_lt_aligned (c₁ := (2 : ℤ) ^ (k - e).toNat) (c₂ := c) (e := e)
      (by rw [← hveq, ← hwall k hek]; exact lt_of_le_of_ne hklo (Ne.symm hne))
    rw [← hveq, ← hwall k hek, ← hu] at this
    exact this

/-- **`succ` undoes `predPos`** on positive `F`-values — the positive core of
Flocq `succ_pred`. -/
theorem succ_predPos (F : FiniteFormat) {p : ℕ} (hp : F.p = (p : Prec))
    {z : Dyadic} (hz : z ∈ F.unbounded) (hz0 : 0 < ((z : Dyadic) : ℝ)) :
    succ F (predPos F ((z : Dyadic) : ℝ)) = ((z : Dyadic) : ℝ) := by
  have hzne : ((z : Dyadic) : ℝ) ≠ 0 := ne_of_gt hz0
  obtain ⟨-, hbot⟩ := binade_walls F hp hz hz0
  have hklo : (2 : ℝ) ^ (Int.log 2 ((z : Dyadic) : ℝ)) ≤ ((z : Dyadic) : ℝ) :=
    Int.zpow_log_le_self (by norm_num) hz0
  have hkhi : ((z : Dyadic) : ℝ) < (2 : ℝ) ^ (Int.log 2 ((z : Dyadic) : ℝ) + 1) :=
    Int.lt_zpow_succ_log_self (by norm_num) _
  unfold predPos
  split_ifs with hbf
  · -- `z` is a binade floor `2^k`; the step down is the spacing below
    set k := Int.log 2 ((z : Dyadic) : ℝ) with hk
    have hpos2 : (0 : ℝ) < (2 : ℝ) ^ (k - 1) := zpow_pos (by norm_num) _
    have hhalf : ((z : Dyadic) : ℝ) / 2 = (2 : ℝ) ^ (k - 1) := by
      rw [hbf, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
    set e' := F.canonicalExp ((2 : ℝ) ^ (k - 1)) with he'
    have hu : ulp F (((z : Dyadic) : ℝ) / 2) = (2 : ℝ) ^ e' := by
      rw [hhalf, ulp_of_ne_zero F (ne_of_gt hpos2), ← he']
    have he'_le : e' ≤ k :=
      canonicalExp_zpow_le F hp (by omega)
        (fun e hexp => by rw [hk]; exact exp_le_log_of_mem F hexp hz hz0)
    rw [hu]
    rcases eq_or_lt_of_le he'_le with heq | hlt
    · -- the step down is the whole value, so the format's quantum *is* `2^k`
      have hpp : 0 < p := FiniteFormat.p_pos hp
      have hlog : Int.log 2 |((2 : ℝ) ^ (k - 1))| = k - 1 := by
        rw [abs_of_pos hpos2]; exact log_two_zpow (k - 1)
      have hexp_eq : F.exp = (k : QExp) := by
        cases hexp : F.exp using QExp.recBotCoe with
        | bot =>
          exfalso
          rw [he'] at heq
          unfold FiniteFormat.canonicalExp at heq
          simp only [hp, hexp, hlog, if_neg (ne_of_gt hpos2)] at heq
          omega
        | coe e =>
          rw [he'] at heq
          unfold FiniteFormat.canonicalExp at heq
          simp only [hp, hexp, hlog, if_neg (ne_of_gt hpos2)] at heq
          exact congrArg _ (by omega)
      have hzero : ((z : Dyadic) : ℝ) - (2 : ℝ) ^ e' = 0 := by rw [hbf, heq]; ring
      rw [hzero, succ_of_nonneg F le_rfl, ulp_eq_zpow_of F (by simp [hexp_eq]),
        canonicalExp_zero F hexp_eq, hbf]
      ring
    · -- the predecessor lands in the binade below, where the spacing is `2 ^ e'`
      have hstep : (2 : ℝ) ^ e' ≤ (2 : ℝ) ^ (k - 1) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have hk2 : (2 : ℝ) ^ k = 2 * (2 : ℝ) ^ (k - 1) := by
        rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]; ring
      have hw : (2 : ℝ) ^ (k - 1) ≤ ((z : Dyadic) : ℝ) - (2 : ℝ) ^ e' := by
        rw [hbf, hk2]; linarith
      have hwpos : (0 : ℝ) < ((z : Dyadic) : ℝ) - (2 : ℝ) ^ e' := lt_of_lt_of_le hpos2 hw
      have hlogw : Int.log 2 (((z : Dyadic) : ℝ) - (2 : ℝ) ^ e') = k - 1 := by
        refine log_eq_of_zpow_bounds hwpos hw ?_
        rw [show k - 1 + 1 = k by ring, hbf]
        linarith [zpow_pos (show (0 : ℝ) < 2 by norm_num) e']
      have hcw : F.canonicalExp (((z : Dyadic) : ℝ) - (2 : ℝ) ^ e') = e' := by
        rw [he']
        exact canonicalExp_eq_of_log_eq F (ne_of_gt hwpos) (ne_of_gt hpos2)
          (by rw [abs_of_pos hwpos, abs_of_pos hpos2, hlogw, log_two_zpow])
      rw [succ_of_nonneg F hwpos.le, ulp_of_ne_zero F (ne_of_gt hwpos), hcw]
      ring
  · -- interior: one ulp down, same binade
    set k := Int.log 2 ((z : Dyadic) : ℝ) with hk
    have hupos : (0 : ℝ) < ulp F ((z : Dyadic) : ℝ) := ulp_pos F hzne
    have hw := hbot hbf
    have h2k : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
    have hwpos : (0 : ℝ) < ((z : Dyadic) : ℝ) - ulp F ((z : Dyadic) : ℝ) := by linarith
    have hlogw : Int.log 2 (((z : Dyadic) : ℝ) - ulp F ((z : Dyadic) : ℝ)) = k :=
      log_eq_of_zpow_bounds hwpos (by linarith) (by linarith)
    have hcw : F.canonicalExp (((z : Dyadic) : ℝ) - ulp F ((z : Dyadic) : ℝ))
        = F.canonicalExp ((z : Dyadic) : ℝ) :=
      canonicalExp_eq_of_log_eq F (ne_of_gt hwpos) hzne
        (by rw [abs_of_pos hwpos, abs_of_pos hz0, hlogw, hk])
    rw [succ_of_nonneg F hwpos.le, ulp_of_ne_zero F (ne_of_gt hwpos), hcw,
      ← ulp_of_ne_zero F hzne]
    ring

/-- **`predPos` undoes `succ`** on positive `F`-values — the positive core of
Flocq `pred_succ`. -/
theorem predPos_succ (F : FiniteFormat) {p : ℕ} (hp : F.p = (p : Prec))
    {z : Dyadic} (hz : z ∈ F.unbounded) (hz0 : 0 < ((z : Dyadic) : ℝ)) :
    predPos F (succ F ((z : Dyadic) : ℝ)) = ((z : Dyadic) : ℝ) := by
  have hzne : ((z : Dyadic) : ℝ) ≠ 0 := ne_of_gt hz0
  obtain ⟨htop, -⟩ := binade_walls F hp hz hz0
  set k := Int.log 2 ((z : Dyadic) : ℝ) with hk
  have hupos : (0 : ℝ) < ulp F ((z : Dyadic) : ℝ) := ulp_pos F hzne
  have hklo : (2 : ℝ) ^ k ≤ ((z : Dyadic) : ℝ) := Int.zpow_log_le_self (by norm_num) hz0
  rw [succ_of_nonneg F hz0.le]
  set y := ((z : Dyadic) : ℝ) + ulp F ((z : Dyadic) : ℝ) with hy
  have hypos : (0 : ℝ) < y := by rw [hy]; linarith
  rcases eq_or_lt_of_le htop with heq | hlt
  · -- lands exactly on the top wall, a binade floor
    have hylog : Int.log 2 y = k + 1 := by rw [heq]; exact log_two_zpow (k + 1)
    have hpos2 : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
    have hhalf : y / 2 = (2 : ℝ) ^ k := by
      rw [heq, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]; ring
    have hcw : F.canonicalExp (y / 2) = F.canonicalExp ((z : Dyadic) : ℝ) := by
      rw [hhalf]
      exact canonicalExp_eq_of_log_eq F (ne_of_gt hpos2) hzne
        (by rw [abs_of_pos hpos2, abs_of_pos hz0, log_two_zpow, hk])
    unfold predPos
    rw [if_pos (by rw [hylog, ← heq]), ulp_of_ne_zero F (by rw [hhalf]; exact ne_of_gt hpos2),
      hcw, ← ulp_of_ne_zero F hzne, hy]
    ring
  · -- stays inside the binade
    have hylog : Int.log 2 y = k :=
      log_eq_of_zpow_bounds hypos (by rw [hy]; linarith) hlt
    unfold predPos
    rw [if_neg (by rw [hylog]; intro hc; rw [hy] at hc; linarith),
      ulp_of_ne_zero F (ne_of_gt hypos),
      canonicalExp_eq_of_log_eq F (ne_of_gt hypos) hzne
        (by rw [abs_of_pos hypos, abs_of_pos hz0, hylog, hk]),
      ← ulp_of_ne_zero F hzne, hy]
    ring

/-- At a format with a minimum quantum, the smallest positive value steps back
to `0`. -/
private theorem predPos_ulp_zero (F : FiniteFormat) {p : ℕ} (hp : F.p = (p : Prec))
    {e : ℤ} (hexp : F.exp = (e : QExp)) : predPos F ((2 : ℝ) ^ e) = 0 := by
  have hpp : 0 < p := FiniteFormat.p_pos hp
  have hpos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have hpos2 : (0 : ℝ) < (2 : ℝ) ^ (e - 1) := zpow_pos (by norm_num) _
  have hlog : Int.log 2 |((2 : ℝ) ^ (e - 1))| = e - 1 := by
    rw [abs_of_pos hpos2]; exact log_two_zpow (e - 1)
  have hce : F.canonicalExp ((2 : ℝ) ^ (e - 1)) = e := by
    unfold FiniteFormat.canonicalExp
    simp only [hp, hexp, hlog, if_neg (ne_of_gt hpos2)]
    omega
  have hhalf : (2 : ℝ) ^ e / 2 = (2 : ℝ) ^ (e - 1) := by
    rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
  unfold predPos
  rw [if_pos (by rw [log_two_zpow]), hhalf, ulp_of_ne_zero F (ne_of_gt hpos2), hce]
  ring

/-- **`succ` undoes `pred`** (Flocq `succ_pred`). -/
theorem succ_pred (F : FiniteFormat) {p : ℕ} (hp : F.p = (p : Prec))
    {x : Dyadic} (hx : x ∈ F.unbounded) :
    succ F (pred F ((x : Dyadic) : ℝ)) = ((x : Dyadic) : ℝ) := by
  rcases lt_trichotomy ((x : Dyadic) : ℝ) 0 with hneg | hzero | hpos
  · -- reflect through `0`: below zero `succ` is `predPos` of the negation
    have hcoe : ((-x : Dyadic) : ℝ) = -((x : Dyadic) : ℝ) := Dyadic.coe_real_neg x
    have hnx0 : (0 : ℝ) < -((x : Dyadic) : ℝ) := by linarith
    have hs : (0 : ℝ) < succ F (-((x : Dyadic) : ℝ)) := by
      rw [succ_of_nonneg F hnx0.le]; linarith [ulp_pos F (ne_of_gt hnx0)]
    have hkey : predPos F (succ F (-((x : Dyadic) : ℝ))) = -((x : Dyadic) : ℝ) := by
      have := predPos_succ F hp (FiniteFormat.neg_mem hx) (by rw [hcoe]; exact hnx0)
      rwa [hcoe] at this
    rw [pred, succ_of_neg F (by linarith), neg_neg, hkey, neg_neg]
  · rw [hzero]
    have hs0 : succ F (0 : ℝ) = ulp F 0 := by rw [succ_of_nonneg F le_rfl, zero_add]
    rw [pred, neg_zero, hs0]
    cases hexp : F.exp using QExp.recBotCoe with
    | bot =>
      have h0 : ulp F (0 : ℝ) = 0 := by rw [ulp, if_pos ⟨rfl, hexp⟩]
      rw [h0, neg_zero, hs0, h0]
    | coe e =>
      have hu : ulp F (0 : ℝ) = (2 : ℝ) ^ e := by
        rw [ulp_eq_zpow_of F (by simp [hexp]), canonicalExp_zero F hexp]
      rw [hu, succ_of_neg F (by linarith [zpow_pos (show (0 : ℝ) < 2 by norm_num) e]),
        neg_neg, predPos_ulp_zero F hp hexp, neg_zero]
  · rw [pred_eq_predPos F hpos, succ_predPos F hp hx hpos]

/-- **`pred` undoes `succ`** (Flocq `pred_succ`). -/
theorem pred_succ (F : FiniteFormat) {p : ℕ} (hp : F.p = (p : Prec))
    {x : Dyadic} (hx : x ∈ F.unbounded) :
    pred F (succ F ((x : Dyadic) : ℝ)) = ((x : Dyadic) : ℝ) := by
  rcases lt_trichotomy ((x : Dyadic) : ℝ) 0 with hneg | hzero | hpos
  · have hcoe : ((-x : Dyadic) : ℝ) = -((x : Dyadic) : ℝ) := Dyadic.coe_real_neg x
    have hnx0 : (0 : ℝ) < -((x : Dyadic) : ℝ) := by linarith
    have hkey : succ F (predPos F (-((x : Dyadic) : ℝ))) = -((x : Dyadic) : ℝ) := by
      have := succ_predPos F hp (FiniteFormat.neg_mem hx) (by rw [hcoe]; exact hnx0)
      rwa [hcoe] at this
    rw [succ_of_neg F hneg, pred, neg_neg, hkey, neg_neg]
  · rw [hzero]
    have hs0 : succ F (0 : ℝ) = ulp F 0 := by rw [succ_of_nonneg F le_rfl, zero_add]
    rw [hs0]
    cases hexp : F.exp using QExp.recBotCoe with
    | bot =>
      have h0 : ulp F (0 : ℝ) = 0 := by rw [ulp, if_pos ⟨rfl, hexp⟩]
      rw [h0, pred, neg_zero, hs0, h0, neg_zero]
    | coe e =>
      have hu : ulp F (0 : ℝ) = (2 : ℝ) ^ e := by
        rw [ulp_eq_zpow_of F (by simp [hexp]), canonicalExp_zero F hexp]
      rw [hu, pred_eq_predPos F (zpow_pos (show (0 : ℝ) < 2 by norm_num) e),
        predPos_ulp_zero F hp hexp]
  · have hsp : (0 : ℝ) < succ F ((x : Dyadic) : ℝ) := by
      rw [succ_of_nonneg F hpos.le]; linarith [ulp_pos F (ne_of_gt hpos)]
    rw [pred_eq_predPos F hsp, predPos_succ F hp hx hpos]

/-! ## `FiniteFormat.next` is `succ` in `Dyadic` form -/

/-- The real value of `next` is `succ`, guard branch included: `next F 0 = 0 =
succ F 0` when there is no minimum quantum. -/
theorem next_coe (F : FiniteFormat) {b : Dyadic} (hb : 0 ≤ ((b : Dyadic) : ℝ)) :
    ((F.next b : Dyadic) : ℝ) = succ F ((b : Dyadic) : ℝ) := by
  rw [succ_of_nonneg F hb, FiniteFormat.next]
  split_ifs with hg
  · obtain ⟨hb0, hbot⟩ := hg
    rw [hb0, ulp, if_pos ⟨rfl, hbot⟩]; ring
  · rw [Dyadic.coe_real_add, Dyadic.coe_ofIntZpow, ulp_eq_zpow_of F hg]
    push_cast; ring

/-- `F.next` maps `F` into `F`. -/
theorem next_mem (F : FiniteFormat) {b : Dyadic} (hb : b ∈ F.unbounded) :
    F.next b ∈ F.unbounded := by
  rw [FiniteFormat.next]
  split_ifs with hg
  · exact hb
  · -- `b` is its own round-down, so `b + 2^e` is the next grid point up
    have hfl := RoundsFinite.eq_of_mem hb (rndDown_spec F ((b : Dyadic) : ℝ))
    rw [rndDown_eq] at hfl
    have hflr : ((⌊((b : Dyadic) : ℝ) * (2 : ℝ) ^ (-(F.canonicalExp
          ((b : Dyadic) : ℝ)))⌋ : ℤ) : ℝ)
        * (2 : ℝ) ^ F.canonicalExp ((b : Dyadic) : ℝ) = ((b : Dyadic) : ℝ) := by
      rw [← Dyadic.coe_ofIntZpow, hfl]
    have hulp : b + Dyadic.ofIntZpow 1 (F.canonicalExp ((b : Dyadic) : ℝ))
        = Dyadic.ofIntZpow (⌊((b : Dyadic) : ℝ) * (2 : ℝ) ^ (-(F.canonicalExp
            ((b : Dyadic) : ℝ)))⌋ + 1) (F.canonicalExp ((b : Dyadic) : ℝ)) := by
      apply Dyadic.ext_real
      rw [Dyadic.coe_real_add, Dyadic.coe_ofIntZpow, Dyadic.coe_ofIntZpow]
      push_cast; linear_combination -hflr
    rw [hulp]
    exact ofIntZpow_mem_unbounded F (fun hexp => F.exp_le_canonicalExp _ hexp)
      (fun {p} hp => abs_floor_add_one_le_of_abs_lt (floor_mantissa_lt hp))

/-- On the non-negative side the successor is representable. -/
theorem succ_mem (F : FiniteFormat) {x : Dyadic} (hx : x ∈ F.unbounded)
    (hx0 : 0 ≤ ((x : Dyadic) : ℝ)) :
    ∃ y : Dyadic, y ∈ F.unbounded ∧ ((y : Dyadic) : ℝ) = succ F (x : ℝ) :=
  ⟨F.next x, next_mem F hx, next_coe F hx0⟩

/-- **`succ` is adjacency.** If `y₂` is the next `F`-value above a positive
`y₁` — nothing of `F` strictly between — then `y₂` is exactly `succ y₁`.

This is `adjacent_canonical_form` in `succ` form. -/
theorem succ_eq_of_adjacent (F : FiniteFormat) {p : ℕ} (hp : F.p = (p : Prec))
    {y₁ y₂ : Dyadic} (h₁ : y₁ ∈ F.unbounded) (h₂ : y₂ ∈ F.unbounded)
    (hpos : 0 < ((y₁ : Dyadic) : ℝ))
    (hlt : ((y₁ : Dyadic) : ℝ) < ((y₂ : Dyadic) : ℝ))
    (hadj : ∀ z : Dyadic, z ∈ F.unbounded → ((y₁ : Dyadic) : ℝ) < ((z : Dyadic) : ℝ) →
      ((y₂ : Dyadic) : ℝ) ≤ ((z : Dyadic) : ℝ)) :
    ((y₂ : Dyadic) : ℝ) = succ F ((y₁ : Dyadic) : ℝ) := by
  refine le_antisymm ?_ (succ_le_of_lt F hp h₁ h₂ hpos hlt)
  have hcoe := next_coe F hpos.le
  rw [← hcoe]
  exact hadj _ (next_mem F h₁) (by rw [hcoe]; exact lt_succ F hpos.le (ne_of_gt hpos))

end Mpfx
