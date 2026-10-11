import Mpfx.Format.Next
import Mpfx.Format.Parity
import Mpfx.Format.Discrete
import Mpfx.Rounding.Defs
import Mpfx.Rounding.Op

/-!
# Correct double rounding (§5.2)

The double-rounding rules in the `RoundsFinite` layer (`roundsRTZ_RTZ_finite`, …):
stated *spec-relationally* — given that `z` is the rounding of `x` in `F₂`
and `w` is the rounding of `z` in `F₁` (with `F₁ ⊆ F₂`), conclude that `w` is
also the rounding of `x` in `F₁` directly. Overflow bookkeeping is sidestepped
and the existence of `z`, `w` is taken as hypotheses. `roundsRTO_RN_finite` is in
`Mpfx.DoubleRounding.Nearest`; the overflow-aware total forms
(`roundsRTZ_RTZ_inBound`, …) are in `Mpfx.DoubleRounding.Total`.
-/


namespace Mpfx


/-- **Exact-intermediate collapse.** If the input `v` is already representable
in the wide format `F₂`, double rounding is trivially correct for *any* modes:
the intermediate rounding fixes `v` (`z = v` by `RoundsFinite.eq_of_mem`), so
the double rounding of `v` is the direct one. This is the spec-relational
form of Flocq's `round_generic`-based collapse and the shared core of every
"exact intermediate" operation rule. -/
theorem rndExact {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode}
    {v : Dyadic} (hv : v ∈ F₂) {z w : Dyadic}
    (hz : RoundsFinite F₂ rm₂ (v : ℝ) z) (hw : RoundsFinite F₁ rm₁ (z : ℝ) w) :
    RoundsFinite F₁ rm₁ (v : ℝ) w := by
  rw [RoundsFinite.eq_of_mem hv hz] at hw
  exact hw

/-! ## The directed modes

RTN → RTN and RTP → RTP hold under the plain containment `F₁ ⊆ F₂`: each
bound and each extremality clause passes through `z`. Every other rule into
RTZ or RAZ reduces to them by sign: the intermediate `z` is a faithful
rounding of `x`, so it shares `x`'s sign, and on each side RTZ and RAZ agree
with one of the directed modes (`toZero_of_directed`, `awayZero_of_directed`). -/

/-- **rnd-RTN-RTN**. Double rounding toward `−∞` collapses under `F₁ ⊆ F₂`. -/
theorem roundsRTN_RTN_finite {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toNegative x z) (hw : RoundsFinite F₁ .toNegative (z : ℝ) w) :
    RoundsFinite F₁ .toNegative x w :=
  ⟨hw.1, hw.2.1.trans hz.2.1, fun v hv hvx => hw.2.2 v hv (hz.2.2 v (hsub v hv) hvx)⟩

/-- **rnd-RTP-RTP**. Double rounding toward `+∞` collapses under `F₁ ⊆ F₂`. -/
theorem roundsRTP_RTP_finite {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toPositive x z) (hw : RoundsFinite F₁ .toPositive (z : ℝ) w) :
    RoundsFinite F₁ .toPositive x w :=
  ⟨hw.1, hz.2.1.trans hw.2.1, fun v hv hxv => hw.2.2 v hv (hz.2.2 v (hsub v hv) hxv)⟩

/-- Rules into RTN and RTP give the rule into RTZ: RTZ is RTN for `0 ≤ x`
and RTP for `x ≤ 0`, and the faithful intermediate `z` has the sign of `x`. -/
private theorem toZero_of_directed {F₁ F₂ : FiniteFormat} {x : ℝ} {z w : Dyadic}
    (hzx : IsFaithfulRound F₂ x z)
    (hdn : 0 ≤ x → RoundsFinite F₁ .toNegative (z : ℝ) w → RoundsFinite F₁ .toNegative x w)
    (hup : x ≤ 0 → RoundsFinite F₁ .toPositive (z : ℝ) w → RoundsFinite F₁ .toPositive x w)
    (hw : RoundsFinite F₁ .toZero (z : ℝ) w) : RoundsFinite F₁ .toZero x w := by
  rcases le_total 0 x with hx | hx
  · exact (RoundsFinite.toNegative_iff_toZero_of_nonneg F₁ hx w).mp
      (hdn hx ((RoundsFinite.toNegative_iff_toZero_of_nonneg F₁ (hzx.nonneg hx) w).mpr hw))
  · exact (RoundsFinite.toPositive_iff_toZero_of_nonpos F₁ hx w).mp
      (hup hx ((RoundsFinite.toPositive_iff_toZero_of_nonpos F₁ (hzx.nonpos hx) w).mpr hw))

/-- Rules into RTN and RTP give the rule into RAZ: RAZ is RTP for `0 ≤ x`
and RTN for `x ≤ 0`, and the faithful intermediate `z` has the sign of `x`. -/
private theorem awayZero_of_directed {F₁ F₂ : FiniteFormat} {x : ℝ} {z w : Dyadic}
    (hzx : IsFaithfulRound F₂ x z)
    (hdn : x ≤ 0 → RoundsFinite F₁ .toNegative (z : ℝ) w → RoundsFinite F₁ .toNegative x w)
    (hup : 0 ≤ x → RoundsFinite F₁ .toPositive (z : ℝ) w → RoundsFinite F₁ .toPositive x w)
    (hw : RoundsFinite F₁ .awayZero (z : ℝ) w) : RoundsFinite F₁ .awayZero x w := by
  rcases le_total 0 x with hx | hx
  · exact (RoundsFinite.toPositive_iff_awayZero_of_nonneg F₁ hx w).mp
      (hup hx ((RoundsFinite.toPositive_iff_awayZero_of_nonneg F₁ (hzx.nonneg hx) w).mpr hw))
  · exact (RoundsFinite.toNegative_iff_awayZero_of_nonpos F₁ hx w).mp
      (hdn hx ((RoundsFinite.toNegative_iff_awayZero_of_nonpos F₁ (hzx.nonpos hx) w).mpr hw))

/-- **rnd-RTZ-RTZ**. Double rounding toward zero collapses under `F₁ ⊆ F₂`. -/
theorem roundsRTZ_RTZ_finite {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toZero x z) (hw : RoundsFinite F₁ .toZero (z : ℝ) w) :
    RoundsFinite F₁ .toZero x w :=
  toZero_of_directed hz.isFaithfulRound
    (fun hx => roundsRTN_RTN_finite hsub
      ((RoundsFinite.toNegative_iff_toZero_of_nonneg F₂ hx z).mpr hz))
    (fun hx => roundsRTP_RTP_finite hsub
      ((RoundsFinite.toPositive_iff_toZero_of_nonpos F₂ hx z).mpr hz))
    hw

/-- **rnd-RAZ-RAZ**. Double rounding away from zero collapses under `F₁ ⊆ F₂`. -/
theorem roundsRAZ_RAZ_finite {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .awayZero x z) (hw : RoundsFinite F₁ .awayZero (z : ℝ) w) :
    RoundsFinite F₁ .awayZero x w :=
  awayZero_of_directed hz.isFaithfulRound
    (fun hx => roundsRTN_RTN_finite hsub
      ((RoundsFinite.toNegative_iff_awayZero_of_nonpos F₂ hx z).mpr hz))
    (fun hx => roundsRTP_RTP_finite hsub
      ((RoundsFinite.toPositive_iff_awayZero_of_nonneg F₂ hx z).mpr hz))
    hw

/-- **rnd-RTO-RTO** under `F₁ ⊆ F₂` and `2 ≤ F₂.p`. -/
theorem roundsRTO_RTO_finite {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {x : ℝ} {z w' : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toOdd (z : ℝ) w') :
    RoundsFinite F₁ .toOdd x w' := by
  obtain ⟨hzF₂, hz_faithful, hz_odd_imp⟩ := hz
  obtain ⟨hw'F₁, hw_faithful, hw_odd_imp⟩ := hw
  rcases eq_or_ne ((z : ℝ)) x with hzx | hzx
  · rw [hzx] at hw_faithful hw_odd_imp
    exact ⟨hw'F₁, hw_faithful, hw_odd_imp⟩
  · have hxne : x ≠ (z : ℝ) := fun h => hzx h.symm
    rcases eq_or_ne z w' with hzw | hzw
    · -- z = w': w' is x's F₁-rounding directly via hz's faithfulness, and
      -- its F₁-oddness comes from F₂-oddness via RTO-padding transfer.
      subst hzw
      refine ⟨hw'F₁, hz_faithful.of_subset hsub hw'F₁, ?_⟩
      · exact fun _ => IsOdd.transfer_of_subset hsub hp_F₂ hw'F₁ (hz_odd_imp hxne)
    · -- z ≠ w': `z ∉ F₁` (else RTO in `F₁` fixes it), so `x` and `z` share their
      -- faithful roundings in `F₁`.
      have hz_ne_w' : (z : ℝ) ≠ (w' : ℝ) := fun h_eq => hzw (Dyadic.coe_real_inj z w' |>.mp h_eq)
      have hz₁ : z ∉ F₁ := fun h =>
        hzw (RoundsFinite.eq_of_mem (rm := .toOdd) h ⟨hw'F₁, hw_faithful, hw_odd_imp⟩).symm
      refine ⟨hw'F₁, (IsFaithfulRound.iff_of_between hsub hz_faithful hz₁ w').mpr hw_faithful, ?_⟩
      · -- Parity: from `hw`'s own parity clause (z ≠ w').
        intro _
        exact hw_odd_imp hz_ne_w'

/-! ## RTO into the directed modes

An RTO rounding `z` of `x` in the wider `F₂`, then a directed rounding of `z`
in `F₁`, collapses to the directed rounding of `x` in `F₁`. The `_of_extend`
forms take `F₁.extend 1 ⊆ F₂` and `2 ≤ F₂.p`; the plain names take the relaxed
containment that bounds `F₁.extend 1` by `F₁`'s bound after the next value. -/

/-- **RTO-padding lemma, applied form.** From `F₁.extend 1 ⊆ F₂`, `2 ≤ F₂.p`, and
an RTO rounding `z` of `x` in `F₂` with `x ≠ z`, conclude `z ∉ F₁`. `F₁` is the shrink of
`F₁.extend 1`, so its values are even in `F₂`, while an inexact RTO result is
odd. -/
theorem toOdd_notMem_of_extend_subset {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {x : ℝ} {z : Dyadic} (hz : RoundsFinite F₂ .toOdd x z)
    (hxne : x ≠ (z : ℝ)) :
    z ∉ F₁ := by
  intro hzF₁
  refine FiniteFormat.not_isEven_and_isOdd (FiniteFormat.isEven_of_subset hsub hp_F₂
    (Format.self_subset_extend F₁.toFormat 1 z hzF₁) ?_) (hz.2.2 hxne)
  change z ∈ (F₁.toFormat.extend 1).shrink.unbounded
  rw [Format.shrink_extend_one]
  exact mem_unbounded_of_mem hzF₁

/-- An RTO rounding to `0` is exact: `0` is never odd. -/
private theorem toOdd_eq_zero_of_eq_zero {F : FiniteFormat} {x : ℝ} {z : Dyadic}
    (hz : RoundsFinite F .toOdd x z) (hz0 : (z : ℝ) = 0) : x = 0 := by
  by_contra hx
  exact (hz.2.2 (by rw [hz0]; exact hx)).ne_zero (eq_zero_of_coe_real_zero hz0)

/-- RTO then RTN, from the two facts it uses: `F₁`'s values are values of `F₂`,
and an inexact `z` is not in `F₁`. If `z` is the `F₂` round-down of `x`, every
`F₁` value at most `x` is at most `z`. If `z` is the round-up, a `w` above `x`
would be an `F₂` value above `x`, hence `w = z ∈ F₁`. -/
private theorem toOdd_toNegative {F₁ F₂ : FiniteFormat}
    (hmem : ∀ v : Dyadic, v ∈ F₁ → v ∈ F₂) {x : ℝ} {z w : Dyadic}
    (hnot : x ≠ (z : ℝ) → z ∉ F₁)
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toNegative (z : ℝ) w) :
    RoundsFinite F₁ .toNegative x w := by
  obtain ⟨hwF₁, hwz, hw_max⟩ := hw
  rcases isFaithfulRound_iff_directed.mp hz.isFaithfulRound with
    ⟨-, hzx, hz_max⟩ | ⟨-, hxz, hz_min⟩
  · exact ⟨hwF₁, hwz.trans hzx, fun v hv hvx => hw_max v hv (hz_max v (hmem v hv) hvx)⟩
  · refine ⟨hwF₁, ?_, fun v hv hvx => hw_max v hv (hvx.trans hxz)⟩
    by_contra hxw
    push Not at hxw
    have hwz' : (w : ℝ) = z := le_antisymm hwz (hz_min w (hmem w hwF₁) hxw.le)
    exact hnot (hxw.trans_eq hwz').ne (Dyadic.ext_real hwz' ▸ hwF₁)

/-- The mirror of `toOdd_toNegative`. -/
private theorem toOdd_toPositive {F₁ F₂ : FiniteFormat}
    (hmem : ∀ v : Dyadic, v ∈ F₁ → v ∈ F₂) {x : ℝ} {z w : Dyadic}
    (hnot : x ≠ (z : ℝ) → z ∉ F₁)
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toPositive (z : ℝ) w) :
    RoundsFinite F₁ .toPositive x w := by
  obtain ⟨hwF₁, hzw, hw_min⟩ := hw
  rcases isFaithfulRound_iff_directed.mp hz.isFaithfulRound with
    ⟨-, hzx, hz_max⟩ | ⟨-, hxz, hz_min⟩
  · refine ⟨hwF₁, ?_, fun v hv hxv => hw_min v hv (hzx.trans hxv)⟩
    by_contra hwx
    push Not at hwx
    have hwz' : (w : ℝ) = z := le_antisymm (hz_max w (hmem w hwF₁) hwx.le) hzw
    exact hnot (hwz'.symm.trans_lt hwx).ne' (Dyadic.ext_real hwz' ▸ hwF₁)
  · exact ⟨hwF₁, hxz.trans hzw, fun v hv hxv => hw_min v hv (hz_min v (hmem v hv) hxv)⟩

/-- **rnd-RTO-RTN** under `F₁.extend 1 ⊆ F₂` and `2 ≤ F₂.p`, without the relaxed
bound. -/
theorem roundsRTO_RTN_finite_of_extend {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toNegative (z : ℝ) w) :
    RoundsFinite F₁ .toNegative x w :=
  toOdd_toNegative (fun v hv => hsub v (Format.self_subset_extend _ 1 v hv))
    (toOdd_notMem_of_extend_subset hsub hp_F₂ hz) hz hw

/-- **rnd-RTO-RTP** under `F₁.extend 1 ⊆ F₂` and `2 ≤ F₂.p`, without the relaxed
bound. -/
theorem roundsRTO_RTP_finite_of_extend {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toPositive (z : ℝ) w) :
    RoundsFinite F₁ .toPositive x w :=
  toOdd_toPositive (fun v hv => hsub v (Format.self_subset_extend _ 1 v hv))
    (toOdd_notMem_of_extend_subset hsub hp_F₂ hz) hz hw

/-- The relaxed containment gives both facts the RTO → RTN/RTP cores use. A
trivial `F₁ = {0}` holds only `0`, and an RTO rounding is `0` only when exact. -/
private theorem toOdd_directed_facts {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {x : ℝ} {z : Dyadic} (hz : RoundsFinite F₂ .toOdd x z) :
    (∀ v : Dyadic, v ∈ F₁ → v ∈ F₂) ∧ (x ≠ (z : ℝ) → z ∉ F₁) := by
  rcases two_le_p_or_trivial_of_extend_one_withBound_subset hsub with hp | htriv
  · have h := extend_one_subset_of_withBound_subset hsub
    exact ⟨fun v hv => h v (Format.self_subset_extend _ 1 v hv),
      toOdd_notMem_of_extend_subset h hp hz⟩
  · refine ⟨fun v hv => ?_, fun hxz hzF =>
      hxz ((toOdd_eq_zero_of_eq_zero hz (htriv z hzF)).trans (htriv z hzF).symm)⟩
    rw [Dyadic.ext_real (by rw [htriv v hv, Dyadic.coe_real_zero] : (v : ℝ) = (0 : Dyadic))]
    exact F₂.zero_mem

/-- **rnd-RTO-RTN** under the relaxed containment. -/
theorem roundsRTO_RTN_finite {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toNegative (z : ℝ) w) :
    RoundsFinite F₁ .toNegative x w :=
  toOdd_toNegative (toOdd_directed_facts hsub hz).1 (toOdd_directed_facts hsub hz).2 hz hw

/-- **rnd-RTO-RTP** under the relaxed containment. -/
theorem roundsRTO_RTP_finite {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toPositive (z : ℝ) w) :
    RoundsFinite F₁ .toPositive x w :=
  toOdd_toPositive (toOdd_directed_facts hsub hz).1 (toOdd_directed_facts hsub hz).2 hz hw

/-- **rnd-RTO-RTZ** under `F₁.extend 1 ⊆ F₂` and `2 ≤ F₂.p`, without the relaxed
bound. -/
theorem roundsRTO_RTZ_finite_of_extend {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toZero (z : ℝ) w) :
    RoundsFinite F₁ .toZero x w :=
  toZero_of_directed hz.isFaithfulRound
    (fun _ => roundsRTO_RTN_finite_of_extend hsub hp_F₂ hz)
    (fun _ => roundsRTO_RTP_finite_of_extend hsub hp_F₂ hz) hw

/-- **rnd-RTO-RTZ** under the relaxed containment. -/
theorem roundsRTO_RTZ_finite {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .toZero (z : ℝ) w) :
    RoundsFinite F₁ .toZero x w :=
  toZero_of_directed hz.isFaithfulRound
    (fun _ => roundsRTO_RTN_finite hsub hz) (fun _ => roundsRTO_RTP_finite hsub hz) hw

/-- **rnd-RTO-RAZ** under `F₁.extend 1 ⊆ F₂` and `2 ≤ F₂.p`, without the relaxed
bound. -/
theorem roundsRTO_RAZ_finite_of_extend {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .awayZero (z : ℝ) w) :
    RoundsFinite F₁ .awayZero x w :=
  awayZero_of_directed hz.isFaithfulRound
    (fun _ => roundsRTO_RTN_finite_of_extend hsub hp_F₂ hz)
    (fun _ => roundsRTO_RTP_finite_of_extend hsub hp_F₂ hz) hw

/-- **rnd-RTO-RAZ** under the relaxed containment. -/
theorem roundsRTO_RAZ_finite {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z) (hw : RoundsFinite F₁ .awayZero (z : ℝ) w) :
    RoundsFinite F₁ .awayZero x w :=
  awayZero_of_directed hz.isFaithfulRound
    (fun _ => roundsRTO_RTN_finite hsub hz) (fun _ => roundsRTO_RTP_finite hsub hz) hw

end Mpfx
