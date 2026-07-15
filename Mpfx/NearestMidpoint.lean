import Mpfx.RoundOp
import Mpfx.Grid
import Mpfx.Containment

/-!
# Round-to-nearest midpoint theory (Roux Lemma 16)

This file builds the round-to-nearest infrastructure behind Roux's
operation-specific double-rounding results for addition, square root and
division (`docs/agents/DOUBLE_ROUNDING_OPS_PLAN.md`, Phase 2). The centrepiece
is **Lemma 16** (`round_round_lt_mid_further_place` in Flocq
`src/Prop/Double_rounding.v`): when a positive real sits far enough below its
`F₁`-midpoint, an intermediate round-to-nearest in a finer format `F₂` followed
by a round-to-nearest in `F₁` agrees with rounding directly into `F₁`.

## Definitions (faithful to Flocq)

* `ulp F x := 2 ^ (F.canonicalExp x)` — the unit in the last place. `canonicalExp`
  is Flocq's `cexp = fexp (mag x)`, and the Grid theory already proves F-adjacent
  values differ by `2 ^ canonicalExp`, so this is the step the grid rests on.
* `rndDown F x` — the round-**down** (toward `−∞`) value, `⌊x·2^(−e)⌋·2^e`; the
  analog of Flocq's `round … Zfloor`. Total and always finite (taken in the
  unbounded format, directed mode is never `IsUndefined`).
* `midp F x := rndDown F x + ulp F x / 2` — the midpoint bracketing `x`
  (Flocq `midp fexp x`).
-/

namespace Mpfx

/-- **ulp** — unit in the last place of `x` in `F`, `2 ^ (F.canonicalExp x)`
(Flocq `ulp beta fexp x = bpow (cexp x)`). -/
noncomputable def ulp (F : FiniteFormat) (x : ℝ) : ℝ := (2 : ℝ) ^ F.canonicalExp x

theorem ulp_pos (F : FiniteFormat) (x : ℝ) : 0 < ulp F x :=
  zpow_pos (by norm_num) _

/-- **Round-down** — the round-toward-`−∞` value of `x` in `F`, always finite
(the unbounded directed rounding is never undefined). Flocq's
`round … Zfloor x`. -/
noncomputable def rndDown (F : FiniteFormat) (x : ℝ) : Dyadic :=
  rndUnbounded F .toNegative x (not_isUndefined_toNegative F)

/-- Closed form of the round-down: `⌊x·2^(−e)⌋·2^e` at `e = canonicalExp x`. -/
theorem rndDown_eq (F : FiniteFormat) (x : ℝ) :
    rndDown F x =
      Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋ (F.canonicalExp x) := by
  unfold rndDown rndUnbounded
  rw [dif_neg (by decide : (RoundingMode.toNegative : RoundingMode) ≠ .toOdd)]
  rw [dif_neg (by decide : (RoundingMode.toNegative : RoundingMode) ≠ .nearest .toEven)]
  rfl

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
theorem lt_rndDown_add_ulp (F : FiniteFormat) (x : ℝ) :
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
  have hulp : ulp F x = (2 : ℝ) ^ e := by rw [ulp, ← he]
  rw [hulp]
  nlinarith [hlt]

/-- **Midpoint** bracketing `x`: `rndDown F x + ulp F x / 2` (Flocq `midp`). -/
noncomputable def midp (F : FiniteFormat) (x : ℝ) : ℝ :=
  (rndDown F x : ℝ) + ulp F x / 2

theorem rndDown_lt_midp (F : FiniteFormat) (x : ℝ) :
    (rndDown F x : ℝ) < midp F x := by
  unfold midp; have := ulp_pos F x; linarith

theorem midp_lt_rndDown_add_ulp (F : FiniteFormat) (x : ℝ) :
    midp F x < (rndDown F x : ℝ) + ulp F x := by
  unfold midp; have := ulp_pos F x; linarith

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
theorem rndUp_le_rndDown_add_ulp (F : FiniteFormat) (x : ℝ) :
    (rndUp F x : ℝ) ≤ (rndDown F x : ℝ) + ulp F x := by
  set e := F.canonicalExp x with he
  set d : Dyadic := Dyadic.ofIntZpow (⌊x * (2 : ℝ) ^ (-e)⌋ + 1) e with hd
  have hd_real : (d : ℝ) = (rndDown F x : ℝ) + ulp F x := by
    rw [hd, Dyadic.coe_ofIntZpow, rndDown_eq, Dyadic.coe_ofIntZpow, ulp, ← he]
    push_cast; ring
  have hd_mem : d ∈ F.unbounded := by
    rw [hd]
    refine ofIntZpow_mem_unbounded F (fun hexp => F.exp_le_canonicalExp x hexp)
      (fun {p} hp => ?_)
    have hfl := abs_floor_add_one_le_of_abs_lt (floor_mantissa_lt (F := F) (x := x) hp)
    rw [← he] at hfl
    exact hfl
  have hx_le_d : x ≤ (d : ℝ) := by
    rw [hd_real]; exact (lt_rndDown_add_ulp F x).le
  have := rndUp_min F x hd_mem hx_le_d
  rwa [hd_real] at this

/-! ## L1 — ulp gap from the canonical-exponent gap -/

/-- If `F₂`'s canonical exponent at `x` is strictly below `F₁`'s, then
`ulp F₂ x ≤ ulp F₁ x / 2` (integer exponents differ by at least one). -/
theorem ulp_le_half_ulp_of_canonicalExp_lt {F₁ F₂ : FiniteFormat} {x : ℝ}
    (h : F₂.canonicalExp x < F₁.canonicalExp x) :
    ulp F₂ x ≤ ulp F₁ x / 2 := by
  unfold ulp
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

/-- **Below-midpoint ⟹ nearest rounds down.** If `ξ` lies strictly below its
`F`-midpoint, the round-to-nearest value of `ξ` (either tie-break) is the
round-down `rndDown F ξ`. Via the constructive rounding: `ξ < midp F ξ` iff the
scaled-mantissa fraction `s − ⌊s⌋` is `< ½`, and both `rndInt` (`.awayZero`)
and `rndParity` (`.toEven`) select the floor in that case. -/
theorem nearest_eq_rndDown_of_lt_midp (F : FiniteFormat) (tb : TieBreak) (ξ : ℝ)
    (hundef : ¬ F.IsUndefined (.nearest tb)) (hlt : ξ < midp F ξ) :
    RoundsFinite F.unbounded (.nearest tb) ξ (rndDown F ξ) := by
  have hspec := rndUnbounded_satisfies_nearest F tb ξ hundef
  suffices heq : rndUnbounded F (.nearest tb) ξ hundef = rndDown F ξ by
    rw [← heq]; exact hspec
  set e := F.canonicalExp ξ with he
  have h2e : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have hξ : ξ = (ξ * (2 : ℝ) ^ (-e)) * (2 : ℝ) ^ e := (mul_zpow_neg_self ξ e).symm
  have hmid : midp F ξ =
      (⌊ξ * (2 : ℝ) ^ (-e)⌋ : ℝ) * (2 : ℝ) ^ e + (2 : ℝ) ^ e / 2 := by
    unfold midp ulp
    rw [rndDown_eq, Dyadic.coe_ofIntZpow, ← he]
  have hδ : ξ * (2 : ℝ) ^ (-e) - (⌊ξ * (2 : ℝ) ^ (-e)⌋ : ℝ) < 1 / 2 := by
    rw [hmid] at hlt
    nlinarith [hlt, h2e, hξ]
  cases tb with
  | awayZero =>
    rw [rndDown_eq, ← he]
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.nearest .awayZero) ≠ .toOdd),
        dif_neg (by decide : (RoundingMode.nearest .awayZero) ≠ .nearest .toEven)]
    simp only [rndInt, ← he, if_pos hδ]
  | toEven =>
    rw [rndDown_eq, ← he]
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.nearest .toEven) ≠ .toOdd), dif_pos rfl]
    simp only [rndParity, ← he, if_pos hδ]

/-- Closed form of the round-up: `⌈x·2^(−e)⌉·2^e`. -/
theorem rndUp_eq (F : FiniteFormat) (x : ℝ) :
    rndUp F x =
      Dyadic.ofIntZpow ⌈x * (2 : ℝ) ^ (-(F.canonicalExp x))⌉ (F.canonicalExp x) := by
  unfold rndUp rndUnbounded
  rw [dif_neg (by decide : (RoundingMode.toPositive : RoundingMode) ≠ .toOdd)]
  rw [dif_neg (by decide : (RoundingMode.toPositive : RoundingMode) ≠ .nearest .toEven)]
  rfl

/-- **Above-midpoint ⟹ nearest rounds up** (mirror of
`nearest_eq_rndDown_of_lt_midp`). If `midp F ξ < ξ`, the round-to-nearest value
of `ξ` is `rndUp F ξ`: the scaled fraction exceeds `½`, so `⌈·⌉ = ⌊·⌋+1` and
both `rndInt`/`rndParity` select the ceiling. -/
theorem nearest_eq_rndUp_of_midp_lt (F : FiniteFormat) (tb : TieBreak) (ξ : ℝ)
    (hundef : ¬ F.IsUndefined (.nearest tb)) (hlt : midp F ξ < ξ) :
    RoundsFinite F.unbounded (.nearest tb) ξ (rndUp F ξ) := by
  have hspec := rndUnbounded_satisfies_nearest F tb ξ hundef
  suffices heq : rndUnbounded F (.nearest tb) ξ hundef = rndUp F ξ by
    rw [← heq]; exact hspec
  set e := F.canonicalExp ξ with he
  have h2e : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have hξ : ξ = (ξ * (2 : ℝ) ^ (-e)) * (2 : ℝ) ^ e := (mul_zpow_neg_self ξ e).symm
  have hmid : midp F ξ =
      (⌊ξ * (2 : ℝ) ^ (-e)⌋ : ℝ) * (2 : ℝ) ^ e + (2 : ℝ) ^ e / 2 := by
    unfold midp ulp
    rw [rndDown_eq, Dyadic.coe_ofIntZpow, ← he]
  have hδ : (1 : ℝ) / 2 < ξ * (2 : ℝ) ^ (-e) - (⌊ξ * (2 : ℝ) ^ (-e)⌋ : ℝ) := by
    rw [hmid] at hlt
    nlinarith [hlt, h2e, hξ]
  have hfloor_lt : (⌊ξ * (2 : ℝ) ^ (-e)⌋ : ℝ) < ξ * (2 : ℝ) ^ (-e) := by linarith
  have hceil : ⌈ξ * (2 : ℝ) ^ (-e)⌉ = ⌊ξ * (2 : ℝ) ^ (-e)⌋ + 1 := by
    have h1 : ⌈ξ * (2 : ℝ) ^ (-e)⌉ ≤ ⌊ξ * (2 : ℝ) ^ (-e)⌋ + 1 := Int.ceil_le_floor_add_one _
    have h2 : ⌊ξ * (2 : ℝ) ^ (-e)⌋ < ⌈ξ * (2 : ℝ) ^ (-e)⌉ := by
      have : (⌊ξ * (2 : ℝ) ^ (-e)⌋ : ℝ) < (⌈ξ * (2 : ℝ) ^ (-e)⌉ : ℝ) :=
        lt_of_lt_of_le hfloor_lt (Int.le_ceil _)
      exact_mod_cast this
    omega
  have hδ_not_lt : ¬ ξ * (2 : ℝ) ^ (-e) - (⌊ξ * (2 : ℝ) ^ (-e)⌋ : ℝ) < 1 / 2 :=
    not_lt.mpr (le_of_lt hδ)
  cases tb with
  | awayZero =>
    rw [rndUp_eq, ← he, hceil]
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.nearest .awayZero) ≠ .toOdd),
        dif_neg (by decide : (RoundingMode.nearest .awayZero) ≠ .nearest .toEven)]
    simp only [rndInt, ← he, if_neg hδ_not_lt, if_pos hδ]
  | toEven =>
    rw [rndUp_eq, ← he, hceil]
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.nearest .toEven) ≠ .toOdd), dif_pos rfl]
    simp only [rndParity, ← he, if_neg hδ_not_lt, if_pos hδ]

/-! ## Lemma 16 — double rounding below the midpoint (given binade consistency)

Flocq `round_round_lt_mid_further_place`, in the `_place'` form: we take the
binade-consistency `F₁.canonicalExp z = F₁.canonicalExp x` (⟺ Flocq's
`mag x'' = mag x`) as an explicit hypothesis. Deriving it from `hmid` and
`F₁.canonicalExp x ≤ Int.log 2 x + 1` (Flocq's `mag_round_ge`/`mag_le_bpow`
argument) is the remaining sub-lemma — see the plan doc §6. -/

/-- **Lemma 16 (with binade consistency).** For `0 < x` sitting more than
`½·ulp₂` below its `F₁`-midpoint, with `F₂`'s canonical exponent strictly finer
than `F₁`'s and the intermediate nearest rounding `z` staying in `x`'s
`F₁`-binade (`hcexp`), a nearest rounding in `F₂` then in `F₁` agrees with the
direct `F₁` nearest rounding. -/
theorem rnd_lt_mid {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {x : ℝ}
    {z w : Dyadic}
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    (h21 : F₂.canonicalExp x < F₁.canonicalExp x)
    (hmid : x < midp F₁ x - ulp F₂ x / 2)
    (hcexp : F₁.canonicalExp (z : ℝ) = F₁.canonicalExp x)
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) x z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) x w := by
  set e₁ := F₁.canonicalExp x with he₁
  set m : ℤ := ⌊x * (2 : ℝ) ^ (-e₁)⌋ with hm
  have h2e₁ : (0 : ℝ) < (2 : ℝ) ^ e₁ := zpow_pos (by norm_num) _
  have hA : (rndDown F₁ x : ℝ) = (m : ℝ) * (2 : ℝ) ^ e₁ := by
    rw [rndDown_eq, Dyadic.coe_ofIntZpow, ← he₁, ← hm]
  have hmidx : midp F₁ x = (m : ℝ) * (2 : ℝ) ^ e₁ + (2 : ℝ) ^ e₁ / 2 := by
    unfold midp ulp; rw [hA, ← he₁]
  -- real bounds on x and z
  have hax : (m : ℝ) * (2 : ℝ) ^ e₁ ≤ x := hA ▸ rndDown_le F₁ x
  have hulp₂_pos : (0 : ℝ) < ulp F₂ x := ulp_pos F₂ x
  have hx_lt_midp : x < midp F₁ x := by linarith [hmid]
  have hz_err := abs_le.mp (nearest_error_le_half_ulp hz)
  have hulp_gap : ulp F₂ x ≤ ulp F₁ x / 2 := ulp_le_half_ulp_of_canonicalExp_lt h21
  have hulp₁_eq : ulp F₁ x = (2 : ℝ) ^ e₁ := by rw [ulp, ← he₁]
  have hz_lt : (z : ℝ) < (m : ℝ) * (2 : ℝ) ^ e₁ + (2 : ℝ) ^ e₁ / 2 := by
    rw [hmidx] at hmid; linarith [hz_err.2]
  have hz_gt : (m : ℝ) * (2 : ℝ) ^ e₁ - (2 : ℝ) ^ e₁ / 2 < (z : ℝ) := by
    rw [hulp₁_eq] at hulp_gap; linarith [hz_err.1, hax, hulp_gap, hulp₂_pos]
  -- scaled mantissa of z
  set s := (z : ℝ) * (2 : ℝ) ^ (-e₁) with hs
  have hzs : (z : ℝ) = s * (2 : ℝ) ^ e₁ := by rw [hs, mul_zpow_neg_self]
  -- `a := rndDown F₁ x` is the F₁-nearest rounding of z (two cell sub-cases)
  have hP2 : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) (rndDown F₁ x) := by
    rcases lt_or_ge (z : ℝ) ((m : ℝ) * (2 : ℝ) ^ e₁) with hza | hza
    · -- z < a: ⌈s⌉ = m, so rndUp F₁ z = rndDown F₁ x and midp F₁ z < z
      have hfloor : ⌊s⌋ = m - 1 := by
        rw [Int.floor_eq_iff]
        refine ⟨?_, ?_⟩
        · push_cast; nlinarith [hz_gt, hzs, h2e₁]
        · push_cast; nlinarith [hza, hzs, h2e₁]
      have hceil : ⌈s⌉ = m := by
        have h1 : ⌈s⌉ ≤ ⌊s⌋ + 1 := Int.ceil_le_floor_add_one _
        have hlt : (m - 1 : ℝ) < s := by nlinarith [hz_gt, hzs, h2e₁]
        have h3 : (m : ℤ) ≤ ⌈s⌉ := by
          have hcr : ((m - 1 : ℤ) : ℝ) < (⌈s⌉ : ℝ) :=
            lt_of_lt_of_le (by push_cast; linarith) (Int.le_ceil s)
          have : (m - 1 : ℤ) < ⌈s⌉ := by exact_mod_cast hcr
          omega
        omega
      have hru_eq : rndUp F₁ (z : ℝ) = rndDown F₁ x := by
        rw [rndUp_eq, rndDown_eq, hcexp, ← he₁, ← hs, hceil, ← hm]
      have hmidz : midp F₁ (z : ℝ) < (z : ℝ) := by
        have hmz : midp F₁ (z : ℝ) = (m : ℝ) * (2 : ℝ) ^ e₁ - (2 : ℝ) ^ e₁ / 2 := by
          have hrd_eq : rndDown F₁ (z : ℝ) = Dyadic.ofIntZpow (m - 1) e₁ := by
            rw [rndDown_eq, hcexp, ← hs, hfloor]
          unfold midp ulp; rw [hrd_eq, Dyadic.coe_ofIntZpow, hcexp]; push_cast; ring
        rw [hmz]; exact hz_gt
      have := nearest_eq_rndUp_of_midp_lt F₁ tb₁ (z : ℝ) hundef₁ hmidz
      rwa [hru_eq] at this
    · -- z ≥ a: ⌊s⌋ = m, so rndDown F₁ z = rndDown F₁ x and z < midp F₁ z
      have hfloor : ⌊s⌋ = m := by
        rw [Int.floor_eq_iff]
        refine ⟨?_, ?_⟩
        · nlinarith [hza, hzs, h2e₁]
        · nlinarith [hz_lt, hzs, h2e₁]
      have hrd_eq : rndDown F₁ (z : ℝ) = rndDown F₁ x := by
        rw [rndDown_eq, rndDown_eq, hcexp, ← he₁, ← hs, hfloor, ← hm]
      have hmidz : (z : ℝ) < midp F₁ (z : ℝ) := by
        have hmz : midp F₁ (z : ℝ) = (m : ℝ) * (2 : ℝ) ^ e₁ + (2 : ℝ) ^ e₁ / 2 := by
          unfold midp ulp; rw [hrd_eq, hA, hcexp]
        rw [hmz]; exact hz_lt
      have := nearest_eq_rndDown_of_lt_midp F₁ tb₁ (z : ℝ) hundef₁ hmidz
      rwa [hrd_eq] at this
  -- w = rndDown F₁ x by nearest-uniqueness, then close with Lemma L3 on x
  have hu₁ : ¬ (F₁.unbounded).IsUndefined (.nearest tb₁) := by
    rw [FiniteFormat.unbounded_isUndefined]; exact hundef₁
  have hw_eq : w = rndDown F₁ x := by
    rw [rndUnbounded_unique F₁.unbounded (.nearest tb₁) (z : ℝ) hu₁ hw,
        rndUnbounded_unique F₁.unbounded (.nearest tb₁) (z : ℝ) hu₁ hP2]
  rw [hw_eq]
  exact nearest_eq_rndDown_of_lt_midp F₁ tb₁ x hundef₁ hx_lt_midp

end Mpfx
