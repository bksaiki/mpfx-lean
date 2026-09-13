import Mpfx.Ulp
import Mpfx.Discrete
import Mpfx.Containment

/-!
# Round-to-nearest midpoint theory (Roux Lemma 16)

The round-to-nearest infrastructure behind Roux's operation-specific
double-rounding results for addition, square root and division. The centrepiece
is **Lemma 16** (Flocq `round_round_lt_mid_further_place`): when a positive real
sits far enough below its `F₁`-midpoint, an intermediate round-to-nearest in a
finer format `F₂` followed by a round-to-nearest in `F₁` agrees with rounding
directly into `F₁`.

`ulp`, `rndDown`, `rndUp` and `midp` are in `Mpfx/Ulp.lean`.
-/

namespace Mpfx

/-! ## Lemma 16 — double rounding below the midpoint

`rnd_lt_mid` takes binade consistency (`F₁.canonicalExp z = F₁.canonicalExp x`)
as an explicit hypothesis; `canonicalExp_eq_of_lt_mid` derives it from `hmid`
and `F₁.canonicalExp x ≤ Int.log 2 x + 1`, and `rnd_lt_mid'` is the resulting
hypothesis-free form. -/

/-- **Lemma 16 (with binade consistency).** For `0 < x` sitting more than
`½·ulp₂` below its `F₁`-midpoint, with `F₂`'s canonical exponent strictly finer
than `F₁`'s and the intermediate nearest rounding `z` staying in `x`'s
`F₁`-binade (`hcexp`), a nearest rounding in `F₂` then in `F₁` agrees with the
direct `F₁` nearest rounding. -/
theorem rnd_lt_mid {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {x : ℝ}
    {z w : Dyadic}
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    (hx : x ≠ 0)
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
    rw [midp, ulp_of_ne_zero F₁ hx, hA, ← he₁]
  -- real bounds on x and z
  have hax : (m : ℝ) * (2 : ℝ) ^ e₁ ≤ x := hA ▸ rndDown_le F₁ x
  have hulp₂_pos : (0 : ℝ) < ulp F₂ x := ulp_pos F₂ hx
  have hx_lt_midp : x < midp F₁ x := by linarith [hmid]
  have hz_err := abs_le.mp (nearest_error_le_half_ulp hz)
  have hulp_gap : ulp F₂ x ≤ ulp F₁ x / 2 := ulp_le_half_ulp_of_canonicalExp_lt hx h21
  have hulp₁_eq : ulp F₁ x = (2 : ℝ) ^ e₁ := by rw [ulp_of_ne_zero F₁ hx, ← he₁]
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
          -- `z = 0` would force `m = 1`, contradicting `hz_gt`.
          have hg : ¬((z : ℝ) = 0 ∧ F₁.exp = ⊥) := by
            rintro ⟨hz0, -⟩
            have hs0 : s = 0 := by rw [hs, hz0, zero_mul]
            have hm1 : m = 1 := by rw [hs0, Int.floor_zero] at hfloor; omega
            rw [hm1] at hz_gt; rw [hz0] at hz_gt; push_cast at hz_gt; linarith
          rw [midp, ulp_eq_zpow_of F₁ hg, hrd_eq, Dyadic.coe_ofIntZpow, hcexp]
          push_cast; ring
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
      by_cases hg : (z : ℝ) = 0 ∧ F₁.exp = ⊥
      · -- no minimum quantum and `z = 0`: both roundings are `0`
        obtain ⟨hz0, -⟩ := hg
        have hs0 : s = 0 := by rw [hs, hz0, zero_mul]
        have hm0 : m = 0 := by rw [hs0, Int.floor_zero] at hfloor; omega
        have hA0 : rndDown F₁ x = 0 := by
          have : ((rndDown F₁ x : Dyadic) : ℝ) = 0 := by rw [hA, hm0]; push_cast; ring
          exact Dyadic.ext_real (by rw [this, Dyadic.coe_real_zero])
        rw [hA0, hz0]
        have hu : ¬ (F₁.unbounded).IsUndefined (.nearest tb₁) := hundef₁
        have hsat := rndUnbounded_satisfies F₁.unbounded (.nearest tb₁) 0 hu
        rwa [RoundsFinite.eq_zero_of_zero hsat] at hsat
      · have hmidz : (z : ℝ) < midp F₁ (z : ℝ) := by
          have hmz : midp F₁ (z : ℝ) = (m : ℝ) * (2 : ℝ) ^ e₁ + (2 : ℝ) ^ e₁ / 2 := by
            rw [midp, ulp_eq_zpow_of F₁ hg, hrd_eq, hA, hcexp]
          rw [hmz]; exact hz_lt
        have := nearest_eq_rndDown_of_lt_midp F₁ tb₁ (z : ℝ) hundef₁ hmidz
        rwa [hrd_eq] at this
  -- w = rndDown F₁ x by nearest-uniqueness, then round `x` below its midpoint
  have hu₁ : ¬ (F₁.unbounded).IsUndefined (.nearest tb₁) := by
    rw [FiniteFormat.unbounded_isUndefined]; exact hundef₁
  have hw_eq : w = rndDown F₁ x := by
    rw [rndUnbounded_unique F₁.unbounded (.nearest tb₁) (z : ℝ) hu₁ hw,
        rndUnbounded_unique F₁.unbounded (.nearest tb₁) (z : ℝ) hu₁ hP2]
  rw [hw_eq]
  exact nearest_eq_rndDown_of_lt_midp F₁ tb₁ x hundef₁ hx_lt_midp

/-! ## Binade consistency -/

/-- Read off `Int.log 2 x = k` from the binade bounds `2^k ≤ x < 2^(k+1)`. -/
theorem log_eq_of_zpow_bounds {x : ℝ} {k : ℤ} (hx : 0 < x)
    (hlo : (2 : ℝ) ^ k ≤ x) (hhi : x < (2 : ℝ) ^ (k + 1)) : Int.log 2 x = k := by
  have h1 : k ≤ Int.log 2 x :=
    (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hx).mp (by exact_mod_cast hlo)
  have h2 : Int.log 2 x < k + 1 :=
    (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hx).mp (by exact_mod_cast hhi)
  omega

/-- **Binade consistency from a direct upper bound.** For `0 < x` with the
intermediate nearest rounding `z` below the top of `x`'s binade
(`z < 2^(mag x + 1)`) and `F₂` finer than `F₁` at `x` (`h21`, `hle`), `z` stays
in `x`'s `F₁`-binade: `F₁.canonicalExp z = F₁.canonicalExp x`. -/
theorem canonicalExp_eq_of_binade_top {F₁ F₂ : FiniteFormat} {tb₂ : TieBreak} {x : ℝ}
    (hx : 0 < x)
    (h21 : F₂.canonicalExp x < F₁.canonicalExp x)
    (hle : F₁.canonicalExp x ≤ Int.log 2 x + 1)
    {z : Dyadic}
    (hzhi : (z : ℝ) < (2 : ℝ) ^ (Int.log 2 x + 1))
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) x z) :
    F₁.canonicalExp (z : ℝ) = F₁.canonicalExp x := by
  set k := Int.log 2 x with hk
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hxabs : |x| = x := abs_of_pos hx
  have h_xlo : (2 : ℝ) ^ k ≤ x := by
    have := Int.zpow_log_le_self (b := 2) (by norm_num) hx; rw [← hk] at this; exact_mod_cast this
  have he₂_le_k : F₂.canonicalExp x ≤ k := by omega
  have hzf : IsFaithfulRound F₂.unbounded x z := by cases tb₂ <;> exact hz.2.1
  have hdk_mem : Dyadic.ofIntZpow 1 k ∈ F₂.unbounded := by
    refine ofIntZpow_mem_unbounded F₂
      (fun he' => le_trans (F₂.exp_le_canonicalExp x he') he₂_le_k) (fun {p} _ => ?_)
    rw [abs_one]; exact one_le_pow₀ (by norm_num)
  have hdk_real : (Dyadic.ofIntZpow 1 k : ℝ) = (2 : ℝ) ^ k := by
    rw [Dyadic.coe_ofIntZpow]; push_cast; ring
  have h_zlo : (2 : ℝ) ^ k ≤ (z : ℝ) := by
    rcases hzf with ⟨_, _, hmax⟩ | ⟨_, hxz, _⟩
    · have := hmax _ hdk_mem (by rw [hdk_real]; exact h_xlo); rw [hdk_real] at this; exact this
    · linarith [h_xlo]
  have hz_pos : (0 : ℝ) < (z : ℝ) := lt_of_lt_of_le (zpow_pos (by norm_num) k) h_zlo
  have hlogz : Int.log 2 (z : ℝ) = k := log_eq_of_zpow_bounds hz_pos h_zlo hzhi
  have hzabs : |(z : ℝ)| = (z : ℝ) := abs_of_pos hz_pos
  exact (canonicalExp_eq_of_log_eq F₁ (ne_of_gt hz_pos) hx0
    (by rw [hzabs, hxabs, hlogz, ← hk])).trans rfl

/-- **Binade consistency, below-midpoint form.** When `x` lies more than `½·ulp₂`
below its `F₁`-midpoint (`hmid`) and inside its binade (`hle`), the intermediate
`z` stays below the binade top (`z < midp F₁ x < 2^(mag x + 1)`), so
`canonicalExp_eq_of_binade_top` applies. Discharges `rnd_lt_mid`'s `hcexp`. The
bound `midp F₁ x < 2^(k+1)` comes from a floor bound on `rndDown F₁ x`. -/
theorem canonicalExp_eq_of_lt_mid {F₁ F₂ : FiniteFormat} {tb₂ : TieBreak} {x : ℝ}
    (hx : 0 < x)
    (h21 : F₂.canonicalExp x < F₁.canonicalExp x)
    (hle : F₁.canonicalExp x ≤ Int.log 2 x + 1)
    (hmid : x < midp F₁ x - ulp F₂ x / 2)
    {z : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) x z) :
    F₁.canonicalExp (z : ℝ) = F₁.canonicalExp x := by
  set k := Int.log 2 x with hk
  set e₁ := F₁.canonicalExp x with he₁
  have h2e₁ : (0 : ℝ) < (2 : ℝ) ^ e₁ := zpow_pos (by norm_num) _
  have h_xhi : x < (2 : ℝ) ^ (k + 1) := by
    have := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) x
    rw [← hk] at this; exact_mod_cast this
  -- upper bound `z < 2^(k+1)`: `z < midp F₁ x < 2^(k+1)`
  have hz_err := abs_le.mp (nearest_error_le_half_ulp hz)
  have hz_lt_midp : (z : ℝ) < midp F₁ x := by linarith [hz_err.2, hmid]
  have hmidp_lt : midp F₁ x < (2 : ℝ) ^ (k + 1) := by
    set m : ℤ := ⌊x * (2 : ℝ) ^ (-e₁)⌋ with hm
    have hA : (rndDown F₁ x : ℝ) = (m : ℝ) * (2 : ℝ) ^ e₁ := by
      rw [rndDown_eq, Dyadic.coe_ofIntZpow, ← he₁, ← hm]
    have hxs : x * (2 : ℝ) ^ (-e₁) < (2 : ℝ) ^ (k + 1 - e₁) := by
      have key : (2 : ℝ) ^ (k + 1 - e₁) = (2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (-e₁) := by
        rw [show k + 1 - e₁ = (k + 1) + (-e₁) from by ring,
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      rw [key]; exact mul_lt_mul_of_pos_right h_xhi (zpow_pos (by norm_num) _)
    set N : ℤ := (2 : ℤ) ^ (k + 1 - e₁).toNat with hN
    have hN_real : (N : ℝ) = (2 : ℝ) ^ (k + 1 - e₁) := by
      rw [hN]; push_cast
      rw [← zpow_natCast (2 : ℝ) ((k + 1 - e₁).toNat),
          Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ k + 1 - e₁)]
    have hm_lt_N : m < N := by
      have hmfl : (m : ℝ) ≤ x * (2 : ℝ) ^ (-e₁) := Int.floor_le _
      have : (m : ℝ) < (N : ℝ) := by rw [hN_real]; linarith [hmfl, hxs]
      exact_mod_cast this
    have hNe₁ : (N : ℝ) * (2 : ℝ) ^ e₁ = (2 : ℝ) ^ (k + 1) := by
      rw [hN_real, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
    have hA_le : (rndDown F₁ x : ℝ) ≤ (2 : ℝ) ^ (k + 1) - (2 : ℝ) ^ e₁ := by
      rw [hA]
      have hmN : (m : ℝ) ≤ (N : ℝ) - 1 := by
        have : (m : ℤ) ≤ N - 1 := by omega
        exact_mod_cast this
      nlinarith [hmN, h2e₁, hNe₁]
    rw [midp, ulp_of_ne_zero F₁ hx.ne', ← he₁]; linarith [hA_le, h2e₁]
  exact canonicalExp_eq_of_binade_top hx h21 hle (hk ▸ lt_trans hz_lt_midp hmidp_lt) hz

/-- **Lemma 16 (Roux `round_round_lt_mid_further_place`).** The hypothesis-free
form: binade consistency is derived from `hle` via `canonicalExp_eq_of_lt_mid`. -/
theorem rnd_lt_mid' {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {x : ℝ}
    {z w : Dyadic}
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    (hx : 0 < x)
    (h21 : F₂.canonicalExp x < F₁.canonicalExp x)
    (hle : F₁.canonicalExp x ≤ Int.log 2 x + 1)
    (hmid : x < midp F₁ x - ulp F₂ x / 2)
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) x z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) x w :=
  rnd_lt_mid hundef₁ hx.ne' h21 hmid (canonicalExp_eq_of_lt_mid hx h21 hle hmid hz) hz hw

/-! ## Above-midpoint mirror (for subtraction / mixed-sign addition)

`canonicalExp`/`ulp`/`rndDown` reflect under negation, and `rnd_lt_mid` needs no
positivity, so the "above the midpoint ⟹ rounds up" double-rounding theorem
`rnd_gt_mid` follows by applying `rnd_lt_mid` to `−x`. -/

/-- Nearest rounding is invariant under joint negation (both tie-breaks). -/
theorem RoundsFinite.neg_nearest (F : FiniteFormat) (tb : TieBreak) (a : ℝ) (v : Dyadic) :
    RoundsFinite F (.nearest tb) a v ↔ RoundsFinite F (.nearest tb) (-a) (-v) := by
  cases tb with
  | toEven => exact RoundsFinite.neg_nearest_toEven F a v
  | awayZero => exact RoundsFinite.neg_nearest_awayZero F a v

/-- **Double-rounding negation transport.** Both roundings being to-nearest,
double rounding commutes with negation: to double-round `v` it suffices to
double-round `-v` — feed the negated intermediate/result data `(-z, -w)` to
`hbase` and the result negates back. Factors the `RoundsFinite.neg_nearest` dance
shared by the sign-case reductions of `rndDiff`, `rndAdd`, and `rndDiv`. -/
theorem rndNeg {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {v : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) v z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w)
    (hbase : ∀ (z' w' : Dyadic),
      RoundsFinite F₂.unbounded (.nearest tb₂) (-v) z' →
      RoundsFinite F₁.unbounded (.nearest tb₁) (z' : ℝ) w' →
      RoundsFinite F₁.unbounded (.nearest tb₁) (-v) w') :
    RoundsFinite F₁.unbounded (.nearest tb₁) v w := by
  have hz' : RoundsFinite F₂.unbounded (.nearest tb₂) (-v) (-z) :=
    (RoundsFinite.neg_nearest F₂.unbounded tb₂ v z).mp hz
  have hw' : RoundsFinite F₁.unbounded (.nearest tb₁) ((-z : Dyadic) : ℝ) (-w) := by
    rw [Dyadic.coe_real_neg]; exact (RoundsFinite.neg_nearest F₁.unbounded tb₁ (z : ℝ) w).mp hw
  exact (RoundsFinite.neg_nearest F₁.unbounded tb₁ v w).mpr (hbase (-z) (-w) hz' hw')

/-- **Above-midpoint double rounding** (mirror of `rnd_lt_mid`, given binade
consistency). If `x` sits more than `½·ulp₂` above its upper `F₁`-midpoint
`rndUp F₁ x − ½·ulp₁`, double rounding agrees (it rounds *up*). Proved by
applying `rnd_lt_mid` to `−x`. -/
theorem rnd_gt_mid {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {x : ℝ}
    {z w : Dyadic}
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    (hx : x ≠ 0)
    (h21 : F₂.canonicalExp x < F₁.canonicalExp x)
    (hmid : (rndUp F₁ x : ℝ) - ulp F₁ x / 2 + ulp F₂ x / 2 < x)
    (hcexp : F₁.canonicalExp (z : ℝ) = F₁.canonicalExp x)
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) x z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) x w := by
  have h21' : F₂.canonicalExp (-x) < F₁.canonicalExp (-x) := by
    rw [canonicalExp_neg, canonicalExp_neg]; exact h21
  have hmid' : -x < midp F₁ (-x) - ulp F₂ (-x) / 2 := by
    unfold midp; rw [rndDown_neg_real, ulp_neg, ulp_neg]; linarith [hmid]
  have hcexp' : F₁.canonicalExp ((-z : Dyadic) : ℝ) = F₁.canonicalExp (-x) := by
    rw [Dyadic.coe_real_neg, canonicalExp_neg, canonicalExp_neg]; exact hcexp
  have hz' : RoundsFinite F₂.unbounded (.nearest tb₂) (-x) (-z) :=
    (RoundsFinite.neg_nearest F₂.unbounded tb₂ x z).mp hz
  have hw' : RoundsFinite F₁.unbounded (.nearest tb₁) ((-z : Dyadic) : ℝ) (-w) := by
    rw [Dyadic.coe_real_neg]
    exact (RoundsFinite.neg_nearest F₁.unbounded tb₁ (z : ℝ) w).mp hw
  have hres := rnd_lt_mid hundef₁ (neg_ne_zero.mpr hx) h21' hmid' hcexp' hz' hw'
  exact (RoundsFinite.neg_nearest F₁.unbounded tb₁ x w).mpr hres

/-- **Above-midpoint double rounding, crossing-robust** (Flocq
`round_round_gt_mid_further_place`, including the `x'' = bpow(mag x)` branch).
Needs *no* away-from-top hypothesis: if the intermediate `z` stays in `x`'s
binade, binade consistency (`canonicalExp_eq_of_binade_top`) applies;
otherwise `z` crosses to `2^(mag x)`. In the crossing case `z` is the round-up of
`x`, bounded above by `2^(mag x) ∈ F₂`, so `z = 2^(mag x)` exactly — a value of
`F₁` — hence `◦₁(z) = z`, and `◦₁(x) = z` too since `x` is within `½·ulp₂` of it. -/
theorem rnd_gt_mid_robust {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {x : ℝ}
    {z w : Dyadic}
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    (hx : 0 < x)
    (h21 : F₂.canonicalExp x < F₁.canonicalExp x)
    (hle : F₁.canonicalExp x ≤ Int.log 2 x + 1)
    (hmid : (rndUp F₁ x : ℝ) - ulp F₁ x / 2 + ulp F₂ x / 2 < x)
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) x z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) x w := by
  set k := Int.log 2 x with hk
  have hx_hi : x < (2 : ℝ) ^ (k + 1) := by
    have := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) x
    rw [← hk] at this; exact_mod_cast this
  by_cases hzc : (z : ℝ) < (2 : ℝ) ^ (k + 1)
  · -- no crossing: binade consistency, then `rnd_gt_mid`
    have hcexp : F₁.canonicalExp (z : ℝ) = F₁.canonicalExp x :=
      canonicalExp_eq_of_binade_top hx h21 hle (by rw [← hk]; exact hzc) hz
    exact rnd_gt_mid hundef₁ hx.ne' h21 hmid hcexp hz hw
  · -- crossing: `z = 2^(k+1)`
    rw [not_lt] at hzc
    have hu2_le : ulp F₂ x ≤ ulp F₁ x / 2 := ulp_le_half_ulp_of_canonicalExp_lt hx.ne' h21
    have hu1pos := ulp_pos F₁ hx.ne'
    have hz_err := abs_le.mp (nearest_error_le_half_ulp hz)
    have hBmem₂ : Dyadic.ofIntZpow 1 (k + 1) ∈ F₂.unbounded := by
      refine ofIntZpow_mem_unbounded F₂
        (fun he' => le_trans (F₂.exp_le_canonicalExp x he') (by omega)) (fun {p} _ => ?_)
      rw [abs_one]; exact one_le_pow₀ (by norm_num)
    have hB_real : (Dyadic.ofIntZpow 1 (k + 1) : ℝ) = (2 : ℝ) ^ (k + 1) := by
      rw [Dyadic.coe_ofIntZpow]; push_cast; ring
    have hzf : IsFaithfulRound F₂.unbounded x z := by cases tb₂ <;> exact hz.2.1
    have hz_eq : (z : ℝ) = (2 : ℝ) ^ (k + 1) := by
      rcases hzf with ⟨_, hzx, _⟩ | ⟨_, _, hmin⟩
      · exfalso; linarith [hzx, hx_hi, hzc]
      · have := hmin _ hBmem₂ (by rw [hB_real]; exact le_of_lt hx_hi)
        rw [hB_real] at this; linarith [this, hzc]
    have hzmem₁ : z ∈ F₁.unbounded := by
      have hzB : z = Dyadic.ofIntZpow 1 (k + 1) :=
        (Dyadic.coe_real_inj _ _).mp (by rw [hz_eq, hB_real])
      rw [hzB]
      refine ofIntZpow_mem_unbounded F₁
        (fun he' => le_trans (F₁.exp_le_canonicalExp x he') (by omega)) (fun {p} _ => ?_)
      rw [abs_one]; exact one_le_pow₀ (by norm_num)
    have hw_eq : w = z := RoundsFinite.eq_of_mem hzmem₁ hw
    have hx_close : |x - (z : ℝ)| < (2 : ℝ) ^ (F₁.canonicalExp x) / 2 := by
      have h1 : (2 : ℝ) ^ (k + 1) - x ≤ ulp F₂ x / 2 := by
        have := hz_err.2; rw [hz_eq] at this; linarith
      have hu1 : ulp F₁ x = (2 : ℝ) ^ (F₁.canonicalExp x) := ulp_of_ne_zero F₁ hx.ne'
      rw [hz_eq, abs_of_nonpos (by linarith [hx_hi] : x - (2 : ℝ) ^ (k + 1) ≤ 0), ← hu1]
      linarith [h1, hu2_le, hu1pos]
    have hquant_z : Dyadic.quantumAtLeast ((F₁.canonicalExp x : ℤ) : QExp) z := by
      refine (Dyadic.quantumAtLeast_coe_real (F₁.canonicalExp x) z).mpr
        ⟨2 ^ (k + 1 - F₁.canonicalExp x).toNat, ?_⟩
      rw [hz_eq]; push_cast
      rw [← zpow_natCast (2 : ℝ), Int.toNat_of_nonneg (by omega),
          ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1; ring
    rw [hw_eq]
    exact nearest_eq_of_close' F₁ tb₁ x hundef₁ hquant_z hx_close

/-! ## Midpoint case dispatch (Flocq `round_round_mid_cases`)

The shared entry point for the operation-specific results whose output can lie
on *either* side of its `F₁`-midpoint (square root, division). Given `F₂` finer
than `F₁` at `x`, the value is either far enough below the midpoint
(`rnd_lt_mid'`), far enough above it (`rnd_gt_mid_robust`), or within `½·ulp₂` of
it — the last case being where the *operation-specific* algebra shows the result
can never land (so the caller discharges it, typically by `exfalso`). -/

/-- **Midpoint case dispatch** (Flocq `round_round_mid_cases`). For `0 < x` with
`F₂` strictly finer than `F₁` at `x` (`h21`) and `x` inside its binade (`hle`),
double rounding of `x` is innocuous *provided the near-midpoint case is handled*:
if `|x − midp₁ x| ≤ ½·ulp₂` the caller supplies `hcmid`; otherwise `x` sits more
than `½·ulp₂` below the midpoint (→ `rnd_lt_mid'`) or above it
(→ `rnd_gt_mid_robust`, which needs no away-from-top hypothesis). The `√`/`÷`
proofs discharge `hcmid` by showing the result is never within `½·ulp₂` of a
midpoint. -/
theorem round_round_mid_cases {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {x : ℝ}
    {z w : Dyadic}
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    (hx : 0 < x)
    (h21 : F₂.canonicalExp x < F₁.canonicalExp x)
    (hle : F₁.canonicalExp x ≤ Int.log 2 x + 1)
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) x z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w)
    (hcmid : |x - midp F₁ x| ≤ ulp F₂ x / 2 →
      RoundsFinite F₁.unbounded (.nearest tb₁) x w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) x w := by
  have hmidp : midp F₁ x = (rndDown F₁ x : ℝ) + ulp F₁ x / 2 := rfl
  rcases lt_or_ge (x - (rndDown F₁ x : ℝ)) ((ulp F₁ x - ulp F₂ x) / 2) with hlt | hge
  · -- more than `½·ulp₂` below the midpoint
    refine rnd_lt_mid' hundef₁ hx h21 hle ?_ hz hw
    rw [hmidp]; linarith
  · rcases lt_or_ge ((ulp F₁ x + ulp F₂ x) / 2) (x - (rndDown F₁ x : ℝ)) with hgt | hmid
    · -- more than `½·ulp₂` above the midpoint
      refine rnd_gt_mid_robust hundef₁ hx h21 hle ?_ hz hw
      have hup := rndUp_le_rndDown_add_ulp F₁ x
      linarith
    · -- within `½·ulp₂` of the midpoint
      refine hcmid ?_
      rw [abs_le, hmidp]; exact ⟨by linarith, by linarith⟩

end Mpfx
