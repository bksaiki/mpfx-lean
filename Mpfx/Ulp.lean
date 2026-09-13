import Mpfx.RoundOp

/-!
# ulp, round-down, round-up and the midpoint

`ulp F x` is the spacing of `F` at `x`, `rndDown`/`rndUp` the two directed
roundings as total functions, and `midp F x` the midpoint between them. On top
of these sit the round-to-nearest error bound and the characterisations of
nearest rounding below and above the midpoint.
-/

namespace Mpfx

/-- **ulp** — unit in the last place of `x` in `F` (Flocq `ulp`).

**Goldberg's convention**: at a power of two `ulp (2^e) = 2^(e+1-p)`, the
spacing of the binade *above* `x`, twice the spacing just below it. Harrison's
and Kahan's definitions differ exactly there. Consequently `succ x = x + ulp x`
is right at a power of two but `pred x = x - ulp x` is not.

`2 ^ canonicalExp x`, except at `x = 0` with no minimum quantum: the format
then holds `c·2^k` at arbitrarily negative `k`, so the gap at zero has infimum
`0` and no exponent describes it. `canonicalExp F 0` already returns `e` when
`F.exp = e` is finite, so only the `⊥` branch needs the guard.

This is Flocq's `negligible_exp`, which its `fexp : Z → Z` needs `LPO_Z` to
decide. Our `F.exp : WithBot ℤ` *is* that decision. -/
noncomputable def ulp (F : FiniteFormat) (x : ℝ) : ℝ :=
  if x = 0 ∧ F.exp = ⊥ then 0 else (2 : ℝ) ^ F.canonicalExp x

theorem ulp_of_ne_zero (F : FiniteFormat) {x : ℝ} (hx : x ≠ 0) :
    ulp F x = (2 : ℝ) ^ F.canonicalExp x :=
  if_neg (by simp [hx])

/-- With a minimum quantum the guard never fires, `x = 0` included. -/
theorem ulp_of_exp (F : FiniteFormat) (x : ℝ) {e : ℤ} (he : F.exp = (e : QExp)) :
    ulp F x = (2 : ℝ) ^ F.canonicalExp x :=
  if_neg (by simp [he])

/-- The guard, negated, is what every rewrite of `ulp` needs. -/
theorem ulp_eq_zpow_of (F : FiniteFormat) {x : ℝ} (h : ¬(x = 0 ∧ F.exp = ⊥)) :
    ulp F x = (2 : ℝ) ^ F.canonicalExp x := if_neg h

theorem ulp_nonneg (F : FiniteFormat) (x : ℝ) : 0 ≤ ulp F x := by
  unfold ulp; split_ifs
  · exact le_refl _
  · exact (zpow_pos (by norm_num) _).le

theorem ulp_pos (F : FiniteFormat) {x : ℝ} (hx : x ≠ 0) : 0 < ulp F x := by
  rw [ulp_of_ne_zero F hx]; exact zpow_pos (by norm_num) _

theorem ulp_pos_of_exp (F : FiniteFormat) (x : ℝ) {e : ℤ} (he : F.exp = (e : QExp)) :
    0 < ulp F x := by
  rw [ulp_of_exp F x he]; exact zpow_pos (by norm_num) _

@[simp] theorem ulp_neg (F : FiniteFormat) (x : ℝ) : ulp F (-x) = ulp F x := by
  unfold ulp; rw [canonicalExp_neg]; simp [neg_eq_zero]

/-- **Round-down** — the round-toward-`−∞` value of `x` in `F`, always finite
(the unbounded directed rounding is never undefined). Flocq
`round … Zfloor x`. -/
noncomputable def rndDown (F : FiniteFormat) (x : ℝ) : Dyadic :=
  rndUnbounded F .toNegative x (not_isUndefined_toNegative F)

/-- `⌊x·2^(−e)⌋·2^e` at `e = canonicalExp x`. -/
theorem rndDown_eq (F : FiniteFormat) (x : ℝ) :
    rndDown F x =
      Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋ (F.canonicalExp x) :=
  RoundsFinite.toNegative_eq_floor F x
    (rndUnbounded_satisfies_toNegative F x (not_isUndefined_toNegative F))

/-- The round-down satisfies the RTN spec in the unbounded format. -/
theorem rndDown_spec (F : FiniteFormat) (x : ℝ) :
    RoundsFinite F.unbounded .toNegative x (rndDown F x) :=
  rndUnbounded_satisfies_toNegative F x (not_isUndefined_toNegative F)

theorem rndDown_le (F : FiniteFormat) (x : ℝ) : (rndDown F x : ℝ) ≤ x :=
  (rndDown_spec F x).2.1

theorem rndDown_mem (F : FiniteFormat) (x : ℝ) : rndDown F x ∈ F.unbounded :=
  (rndDown_spec F x).1

/-- Maximality of the round-down among unbounded-format values below `x`. -/
theorem rndDown_max (F : FiniteFormat) (x : ℝ) {z : Dyadic}
    (hz : z ∈ F.unbounded) (hzx : (z : ℝ) ≤ x) : (z : ℝ) ≤ (rndDown F x : ℝ) :=
  (rndDown_spec F x).2.2 z hz hzx

/-- `x` sits within one ulp above its round-down: `x < rndDown F x + ulp F x`. -/
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

/-- The round-up is within one ulp of the round-down: `rndUp ≤ rndDown + ulp`.
Witness: `(⌊x·2^(−e)⌋+1)·2^e` is in the (unbounded) format and `≥ x`, so the
minimal such value `rndUp` is at most it. -/
@[simp] theorem rndUp_zero (F : FiniteFormat) : rndUp F 0 = 0 :=
  RoundsFinite.eq_zero_of_zero (rndUp_spec F 0)

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

/-! ## L1 — ulp gap from the canonical-exponent gap -/

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

/-! ## L2 — the round-to-nearest error bound -/

/-- **Nearest error bound.** A round-to-nearest value `z` of `x` in the
(unbounded) format is within half an ulp of `x`. Proof: `z` beats both the
round-down `a` and round-up `a'` in distance, so `2|z − x| ≤ (a' − a) ≤ ulp`.
Stated over `F.unbounded` (overflow-free, matching Roux's FLX setting), so the
directed competitors are available. -/
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
  have hstep : (rndUp F x : ℝ) - (rndDown F x : ℝ) ≤ ulp F x := by
    have := rndUp_le_rndDown_add_ulp F x; linarith
  rw [abs_sub_comm]
  linarith

/-! ## L3 — below the midpoint, round-to-nearest agrees with round-down -/

/-- **Nearest of a value close to a grid point.** If `v`'s scaled mantissa is
within `½` of an integer `m`, then the grid point `m · 2^(canonicalExp v)` is the
nearest rounding of `v` (either tie-break). The primitive behind the one-sided
`nearest_eq_rndDown_of_lt_midp`/`nearest_eq_rndUp_of_midp_lt`: the nearest integer
to the scaled mantissa is `m` regardless of which side of it `v` falls. -/
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
is the nearest rounding of `v`. The convenient interface for callers holding a
representable candidate `g`. -/
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
`F`-midpoint, its round-to-nearest value (either tie-break) is `rndDown F ξ`:
the scaled-mantissa fraction `s − ⌊s⌋` is `< ½`, so `⌊s⌋` is the nearest integer
(`nearest_eq_of_close` with `m = ⌊s⌋`). -/
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

/-- **Above-midpoint ⟹ nearest rounds up** (mirror of
`nearest_eq_rndDown_of_lt_midp`). If `midp F ξ < ξ`, its round-to-nearest value
is `rndUp F ξ`: the scaled fraction exceeds `½`, so `⌈·⌉ = ⌊·⌋+1` is the nearest
integer (`nearest_eq_of_close` with `m = ⌈s⌉`). -/
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

theorem predPos_of_binade_floor (F : FiniteFormat) {x : ℝ}
    (hx : x = (2 : ℝ) ^ Int.log 2 x) : predPos F x = x - ulp F (x / 2) := if_pos hx

theorem predPos_of_ne (F : FiniteFormat) {x : ℝ}
    (hx : x ≠ (2 : ℝ) ^ Int.log 2 x) : predPos F x = x - ulp F x := if_neg hx

/-- On the non-negative side the successor is the next grid point up. -/
theorem succ_mem (F : FiniteFormat) {x : Dyadic} (hx : x ∈ F.unbounded)
    (hx0 : 0 ≤ ((x : Dyadic) : ℝ)) (hne : ((x : Dyadic) : ℝ) ≠ 0) :
    ∃ y : Dyadic, y ∈ F.unbounded ∧ ((y : Dyadic) : ℝ) = succ F (x : ℝ) := by
  refine ⟨Dyadic.ofIntZpow (⌊(x : ℝ) * (2 : ℝ) ^ (-(F.canonicalExp (x : ℝ)))⌋ + 1)
      (F.canonicalExp (x : ℝ)), ?_, ?_⟩
  · refine ofIntZpow_mem_unbounded F (fun hexp => F.exp_le_canonicalExp _ hexp)
      (fun {p} hp => abs_floor_add_one_le_of_abs_lt (floor_mantissa_lt hp))
  · have hfl := RoundsFinite.eq_of_mem hx (rndDown_spec F (x : ℝ))
    rw [rndDown_eq] at hfl
    have hfl' : ((⌊(x : ℝ) * (2 : ℝ) ^ (-(F.canonicalExp (x : ℝ)))⌋ : ℤ) : ℝ)
        * (2 : ℝ) ^ F.canonicalExp (x : ℝ) = (x : ℝ) := by
      rw [← Dyadic.coe_ofIntZpow, hfl]
    rw [succ_of_nonneg F hx0, ulp_of_ne_zero F hne, Dyadic.coe_ofIntZpow]
    push_cast; linear_combination hfl'

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
  have hstep : ((y : Dyadic) : ℝ)
      = ((cy * (2:ℤ) ^ (ey - ex).toNat : ℤ) : ℝ) * (2:ℝ) ^ ex := by
    rw [hyeq, ← hey]
    push_cast
    rw [mul_assoc, ← zpow_natCast (2:ℝ) (ey - ex).toNat,
        Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ ey - ex), ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
    ring_nf
  -- both are integer multiples of `2^ex`, and `y > x`, so `y ≥ x + 2^ex`
  have hlt_int : cx < cy * (2:ℤ) ^ (ey - ex).toNat := by
    have := hlt
    rw [hxeq, ← hex, hstep] at this
    exact_mod_cast (mul_lt_mul_iff_of_pos_right h2).mp this
  rw [succ_of_nonneg F hx0.le, ulp_of_ne_zero F hxne, ← hex, hxeq, ← hex, hstep]
  have : (cx : ℝ) + 1 ≤ ((cy * (2:ℤ) ^ (ey - ex).toNat : ℤ) : ℝ) := by exact_mod_cast hlt_int
  nlinarith [h2]

/-- On the positive side `pred` coincides with `predPos`. -/
theorem pred_eq_predPos (F : FiniteFormat) {x : ℝ} (hx : 0 < x) :
    pred F x = predPos F x := by
  rw [pred, succ, if_neg (by linarith : ¬ (0:ℝ) ≤ -x)]; simp only [neg_neg]

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
      unfold FiniteFormat.canonicalExp
      have hlog : Int.log 2 |((2:ℝ) ^ (k-1))| = k - 1 := by
        rw [abs_of_pos hpos2]; exact log_two_zpow (k-1)
      cases hexp : F.exp using QExp.recBotCoe with
      | bot => simp only [hp, hlog, if_neg (ne_of_gt hpos2)]; omega
      | coe q =>
          simp only [hp, hlog, if_neg (ne_of_gt hpos2)]
          refine max_le (by omega) ?_
          -- `2^k ∈ F` has quantum at least `2^q`, so `q ≤ k`
          obtain ⟨-, hq, -⟩ := hx
          rw [FiniteFormat.unbounded_exp, hexp, Dyadic.quantumAtLeast_coe_real] at hq
          obtain ⟨c, hc⟩ := hq
          by_contra hlt
          push Not at hlt
          have h1 : ((x : Dyadic) : ℝ) = (c : ℝ) * (2:ℝ) ^ q := hc
          have : (1:ℝ) ≤ (c : ℝ) := by
            by_contra hcc
            push Not at hcc
            have : (c : ℤ) ≤ 0 := by exact_mod_cast Int.lt_add_one_iff.mp (by exact_mod_cast hcc)
            have : (c : ℝ) ≤ 0 := by exact_mod_cast this
            nlinarith [zpow_pos (by norm_num : (0:ℝ) < 2) q, hx0, h1]
          have h2 : (2:ℝ) ^ q ≤ ((x : Dyadic) : ℝ) := by
            nlinarith [zpow_pos (by norm_num : (0:ℝ) < 2) q]
          rw [hbf] at h2
          have := (zpow_le_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp h2
          omega
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

/-! ## `FiniteFormat.next` is `succ` in `Dyadic` form -/

/-- The real value of `next` is `succ`. On the non-negative side the two agree
exactly, guard branch included: `next F 0 = 0 = succ F 0` when there is no
minimum quantum. -/
theorem next_coe (F : FiniteFormat) {b : Dyadic} (hb : 0 ≤ ((b : Dyadic) : ℝ)) :
    ((F.next b : Dyadic) : ℝ) = succ F ((b : Dyadic) : ℝ) := by
  rw [succ_of_nonneg F hb, FiniteFormat.next]
  split_ifs with hg
  · obtain ⟨hb0, hbot⟩ := hg
    rw [hb0, ulp, if_pos ⟨rfl, hbot⟩]; ring
  · rw [Dyadic.coe_real_add, Dyadic.coe_ofIntZpow, ulp_eq_zpow_of F hg]
    push_cast; ring

/-- The successor of a non-negative `F`-value is an `F`-value. -/
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
    have hstep : b + Dyadic.ofIntZpow 1 (F.canonicalExp ((b : Dyadic) : ℝ))
        = Dyadic.ofIntZpow (⌊((b : Dyadic) : ℝ) * (2 : ℝ) ^ (-(F.canonicalExp
            ((b : Dyadic) : ℝ)))⌋ + 1) (F.canonicalExp ((b : Dyadic) : ℝ)) := by
      apply Dyadic.ext_real
      rw [Dyadic.coe_real_add, Dyadic.coe_ofIntZpow, Dyadic.coe_ofIntZpow]
      push_cast; linear_combination -hflr
    rw [hstep]
    exact ofIntZpow_mem_unbounded F (fun hexp => F.exp_le_canonicalExp _ hexp)
      (fun {p} hp => abs_floor_add_one_le_of_abs_lt (floor_mantissa_lt hp))

/-- **`succ` is adjacency.** If `y₂` is the next `F`-value above a positive
`y₁` — nothing of `F` strictly between — then `y₂` is exactly `succ y₁`.

`succ_le_of_lt` gives one direction; the other is that `succ y₁` is itself
representable (`next_mem`) and lies above `y₁`, so adjacency bounds `y₂` by it.
This is `Grid.lean`'s `F_adjacent_step_form` in `succ` form. -/
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

/-- **Discreteness in `succ` form**: no `F`-value lies strictly between `y` and
`succ y`. This is `no_F_element_in_step_interval` restated. -/
theorem not_mem_between_succ (F : FiniteFormat) {p : ℕ} (hp : F.p = (p : Prec))
    {y z : Dyadic} (hy : y ∈ F.unbounded) (hz : z ∈ F.unbounded)
    (hpos : 0 < ((y : Dyadic) : ℝ)) (hlt : ((y : Dyadic) : ℝ) < ((z : Dyadic) : ℝ)) :
    ¬ ((z : Dyadic) : ℝ) < succ F ((y : Dyadic) : ℝ) :=
  not_lt.mpr (succ_le_of_lt F hp hy hz hpos hlt)

end Mpfx
