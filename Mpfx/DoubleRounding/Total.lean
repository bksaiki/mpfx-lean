import Mpfx.DoubleRounding.Nearest
import Mpfx.Rounding.Restrict

/-!
# Total double rounding

Per rule, stated with `Overflows` and `RoundsInBound`:

* `…_inBound`: either the direct rounding into `F₁` overflows, or the rounding
  into `F₂` and the double rounding stay in bound and agree with it;
* `…_noOverflow`: an in-bound double rounding keeps the direct rounding in
  bound;
* `…_agree`: when all three are in bound they agree, under the plain
  containment.

Each rule proves the first two from a `LocalDoubleRounding` instance: a
locality condition on the input that every in-bound rounding satisfies and under
which double rounding is correct. For every rule but RTO → RN the condition is
`|x|` below a value of `F₁` (`BelowValue`). No regularity hypothesis on the bound
appears in the statements. -/

namespace Mpfx

/-! ## Overflow is local

Every total rule has one shape. A locality condition `L` on the input holds
whenever the direct rounding or the double rounding stays in bound, and under
`L` the rounding into `F₂` stays in bound and the double rounding is the direct
rounding. Both total forms follow (`LocalDoubleRounding.inBound`,
`LocalDoubleRounding.not_overflows`). -/

/-- The facts that make double rounding correct up to overflow, relative to a
locality condition `L` on the input. -/
structure LocalDoubleRounding (F₁ F₂ : FiniteFormat) (rm₁ rm₂ : RoundingMode)
    (L : ℝ → Prop) : Prop where
  /-- An in-bound direct rounding puts its input in `L`. -/
  pin_direct : ∀ {x : ℝ} {y : Dyadic}, RoundsInBound F₁ rm₁ x y → L x
  /-- An in-bound double rounding puts its input in `L`. -/
  pin_double : ∀ {x : ℝ} {z w : Dyadic}, RoundsInBound F₂ rm₂ x z →
    RoundsInBound F₁ rm₁ (z : ℝ) w → L x
  /-- In `L`, the rounding into `F₂` stays in bound. -/
  bound : ∀ {x : ℝ} {z : Dyadic}, L x → RoundsFinite F₂.unbounded rm₂ x z →
    Format.boundOK F₂.b z
  /-- In `L`, the double rounding is the direct rounding. -/
  agree : ∀ {x : ℝ} {z w y : Dyadic}, L x → RoundsFinite F₂.unbounded rm₂ x z →
    RoundsFinite F₁.unbounded rm₁ (z : ℝ) w → RoundsFinite F₁.unbounded rm₁ x y → w = y

/-- The total form: the direct rounding overflows, or the rounding into `F₂` and the
double rounding stay in bound and agree with it. -/
theorem LocalDoubleRounding.inBound {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode}
    {L : ℝ → Prop} (h : LocalDoubleRounding F₁ F₂ rm₁ rm₂ L) (h₁u : ¬ F₁.IsUndefined rm₁)
    (h₂u : ¬ F₂.IsUndefined rm₂) (x : ℝ) :
    Overflows F₁ rm₁ x ∨
    (∃ z w : Dyadic, RoundsInBound F₂ rm₂ x z ∧
      RoundsInBound F₁ rm₁ (z : ℝ) w ∧
      RoundsInBound F₁ rm₁ x w) := by
  have hy := rndUnbounded_satisfies F₁ rm₁ x h₁u
  by_cases hb : Format.boundOK F₁.b (rndUnbounded F₁ rm₁ x h₁u)
  · have hL := h.pin_direct ⟨hy, hb⟩
    have hz := rndUnbounded_satisfies F₂ rm₂ x h₂u
    have hw := rndUnbounded_satisfies F₁ rm₁ (rndUnbounded F₂ rm₂ x h₂u : ℝ) h₁u
    have hwy := h.agree hL hz hw hy
    exact Or.inr ⟨_, _, ⟨hz, h.bound hL hz⟩, ⟨hw, hwy ▸ hb⟩, ⟨hwy ▸ hy, hwy ▸ hb⟩⟩
  · exact Or.inl ⟨_, hy, hb⟩

/-- No overflow: if the double rounding stays in bound, so does the direct
rounding. -/
theorem LocalDoubleRounding.not_overflows {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode}
    {L : ℝ → Prop} (h : LocalDoubleRounding F₁ F₂ rm₁ rm₂ L) {x : ℝ} {z w : Dyadic}
    (hz : RoundsInBound F₂ rm₂ x z) (hw : RoundsInBound F₁ rm₁ (z : ℝ) w) :
    ¬ Overflows F₁ rm₁ x := by
  rintro ⟨y, hy, hby⟩
  exact hby (h.agree (h.pin_double hz hw) hz.1 hw.1 hy ▸ hw.2)

/-- Agreement from a finite rule at `F₁` with bound `B`: when the double rounding
and the direct rounding are both within `B`, restrict the double rounding,
compose, and lift. -/
theorem eq_of_rule {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode}
    (h₁u : ¬ F₁.IsUndefined rm₁) {B : Bound}
    (rule : ∀ {x : ℝ} {z w : Dyadic}, RoundsFinite F₂.unbounded rm₂ x z →
      RoundsFinite (F₁.withBoundFF B) rm₁ (z : ℝ) w → RoundsFinite (F₁.withBoundFF B) rm₁ x w)
    {x : ℝ} {z w y : Dyadic} (hz : RoundsFinite F₂.unbounded rm₂ x z)
    (hw : RoundsFinite F₁.unbounded rm₁ (z : ℝ) w) (hy : RoundsFinite F₁.unbounded rm₁ x y)
    (hwB : Format.boundOK B w) (hyB : Format.boundOK B y) : w = y :=
  RoundsFinite.unique h₁u (RoundsFinite.lift (F := F₁.withBoundFF B)
    (rule hz (RoundsFinite.restrict (F := F₁.withBoundFF B) hw hwB)) hy hyB) hy

/-! ### Below a value of `F₁`

The common locality condition: `x` lies within a value `T` of `F₁` that a bound
`B` admits. When such values lie in `F₂` and the finite rule holds at `F₁`
bounded by them, the rounding into `F₂` stays in bound and the double rounding
is the direct rounding (`localDoubleRounding_of_below`). Every rule except
RTO → RN takes this form. -/

/-- `x` lies within a value of `F₁` that the bound `B` admits. -/
abbrev BelowValue (F₁ : FiniteFormat) (B : Bound) (x : ℝ) : Prop :=
  ∃ T : Dyadic, T ∈ F₁.unbounded ∧ Format.boundOK B T ∧ |x| ≤ T

/-- Locality below a value of `F₁`, given the two pins. -/
theorem localDoubleRounding_of_below {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode}
    (h₁u : ¬ F₁.IsUndefined rm₁) {B : Bound}
    (hmem : ∀ {T : Dyadic}, T ∈ F₁.unbounded → Format.boundOK B T → T ∈ F₂)
    (rule : ∀ {T : NonNegDyadic}, T.val ∈ F₁.unbounded → Format.boundOK B T.val →
      ∀ {x : ℝ} {z w : Dyadic}, RoundsFinite F₂.unbounded rm₂ x z →
        RoundsFinite (F₁.withBoundFF T) rm₁ (z : ℝ) w →
        RoundsFinite (F₁.withBoundFF T) rm₁ x w)
    (pin_direct : ∀ {x : ℝ} {y : Dyadic}, RoundsInBound F₁ rm₁ x y → BelowValue F₁ B x)
    (pin_double : ∀ {x : ℝ} {z w : Dyadic}, RoundsInBound F₂ rm₂ x z →
      RoundsInBound F₁ rm₁ (z : ℝ) w → BelowValue F₁ B x) :
    LocalDoubleRounding F₁ F₂ rm₁ rm₂ (BelowValue F₁ B) where
  pin_direct := pin_direct
  pin_double := pin_double
  bound := fun {_ _} ⟨T, hT, hTB, hxT⟩ hz =>
    boundOK_of_abs_le ((abs_faithful_le_of_le (mem_unbounded_of_mem (hmem hT hTB)) hxT
      hz.isFaithfulRound).trans (le_abs_self _)) (hmem hT hTB).2.2
  agree := fun {x _ _ _} ⟨T, hT, hTB, hxT⟩ hz hw hy => by
    have hzT := abs_faithful_le_of_le (mem_unbounded_of_mem (hmem hT hTB)) hxT
      hz.isFaithfulRound
    have hT0 : (0 : ℚ) ≤ (T : ℚ) := by
      have : (0 : ℝ) ≤ (T : ℝ) := (abs_nonneg x).trans hxT
      exact_mod_cast this
    exact eq_of_rule (B := ((⟨T, hT0⟩ : NonNegDyadic) : Bound)) h₁u
      (rule (T := ⟨T, hT0⟩) hT hTB) hz hw hy
      (boundOK_coe_of_abs_le (abs_faithful_le_of_le hT hzT hw.isFaithfulRound))
      (boundOK_coe_of_abs_le (abs_faithful_le_of_le hT hxT hy.isFaithfulRound))

/-- Bounding a format by a value that `B` admits keeps it within `B`. -/
theorem withBound_subset_of_boundOK (F : Format) {B : Bound} {T : NonNegDyadic}
    (hT : Format.boundOK B T.val) : F.withBound (T : Bound) ⊆ F.withBound B :=
  Format.withBound_mono F fun _ hv =>
    boundOK_of_abs_le ((abs_coe_real_le_of_boundOK hv).trans (le_abs_self _)) hT

/-- A value of `F` above `b ≥ 0` and at most `next b`: the successor of `b`'s
floor at its canonical step. -/
theorem exists_mem_above {F : FiniteFormat} {b : Dyadic} (hb : 0 ≤ (b : ℝ)) :
    ∃ N : Dyadic, N ∈ F.unbounded ∧ (b : ℝ) < N ∧ (N : ℝ) ≤ F.toFormat.next b := by
  by_cases hg : F.exp = ⊥ → 0 < (b : ℝ)
  swap
  · -- No minimum quantum and `b = 0`: take `1 = next 0`.
    push Not at hg
    obtain ⟨hexp, hb0⟩ := hg
    obtain rfl : b = 0 := Dyadic.ext_real (by rw [Dyadic.coe_real_zero]; linarith)
    have hnext : F.toFormat.next 0 = Dyadic.ofIntZpow 1 0 := by
      unfold Format.next
      rw [hexp]
      cases hp : F.p using ENat.recTopCoe with
      | top => exact (F.finite.elim (· hp) (· hexp)).elim
      | coe p => exact Dyadic.ext_real (by simp)
    refine ⟨Dyadic.ofIntZpow 1 0, ⟨precisionAtMost_one_zpow F.pos 0, by
      change Dyadic.quantumAtLeast F.exp _; rw [hexp]; trivial, trivial⟩, ?_, ?_⟩
    · rw [coe_real_ofIntZpow_one, Dyadic.coe_real_zero]; norm_num
    · rw [hnext]
  set c := F.canonicalExp (b : ℝ)
  set s := (b : ℝ) * 2 ^ (-c)
  have h2c : (0 : ℝ) < 2 ^ c := zpow_pos two_pos c
  have hs0 : 0 ≤ s := mul_nonneg hb (zpow_pos two_pos _).le
  have hfl := Int.floor_le s
  have hlt := Int.lt_floor_add_one s
  have hb_eq : s * 2 ^ c = b := mul_zpow_neg_self _ _
  refine ⟨Dyadic.ofIntZpow (⌊s⌋ + 1) c, ofIntZpow_mem_unbounded F
    (fun he => F.exp_le_canonicalExp _ he) (fun {p} hp => ?_), ?_, ?_⟩
  · have h1 := (abs_lt.mp (floor_mantissa_lt (F := F) (x := (b : ℝ)) hp)).2
    have h2 : ⌊s⌋ < 2 ^ p := by exact_mod_cast hfl.trans_lt h1
    have h3 : 0 ≤ ⌊s⌋ := Int.floor_nonneg.mpr hs0
    rw [abs_of_nonneg (by omega)]; omega
  · rw [Dyadic.coe_ofIntZpow, ← hb_eq]; push_cast; nlinarith
  · rw [FiniteFormat.format_next_eq F hb hg, Dyadic.coe_real_add, coe_real_ofIntZpow_one,
      Dyadic.coe_ofIntZpow]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hfl h2c.le]

/-- **Locality above the bound.** For the rules whose containment bounds `F₁` by
`next(b₁)`: an in-bound direct or double rounding puts its input below a value
of `F₁` within `next(b₁)`, since every rounding is faithful and so a larger input
rounds past `b₁`. -/
theorem localDoubleRounding_of_above {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode}
    (h₁u : ¬ F₁.IsUndefined rm₁)
    (hmem : ∀ {T : Dyadic}, T ∈ F₁.unbounded →
      Format.boundOK F₁.toFormat.boundAfterNext T → T ∈ F₂)
    (rule : ∀ {T : NonNegDyadic}, T.val ∈ F₁.unbounded →
      Format.boundOK F₁.toFormat.boundAfterNext T.val →
      ∀ {x : ℝ} {z w : Dyadic}, RoundsFinite F₂.unbounded rm₂ x z →
        RoundsFinite (F₁.withBoundFF T) rm₁ (z : ℝ) w →
        RoundsFinite (F₁.withBoundFF T) rm₁ x w) :
    LocalDoubleRounding F₁ F₂ rm₁ rm₂ (BelowValue F₁ F₁.toFormat.boundAfterNext) := by
  -- Without a bound, some power of two above `|x|` will do.
  have htop : ∀ x : ℝ, F₁.b = ⊤ → BelowValue F₁ F₁.toFormat.boundAfterNext x := by
    intro x hF
    obtain ⟨k, hk, hlt⟩ := Format.exists_zpow_gt |x| F₁.exp
    refine ⟨Dyadic.ofIntZpow 1 k, ⟨precisionAtMost_one_zpow F₁.pos k,
      Dyadic.quantumAtLeast_ofIntZpow hk, trivial⟩, by rw [Format.boundAfterNext_top hF]; trivial,
      by rw [coe_real_ofIntZpow_one]; exact hlt.le⟩
  -- With a bound `b₁`, a value `N` of `F₁` above it, within `next(b₁)`.
  have habove : ∀ b₁ : NonNegDyadic, F₁.b = (b₁ : Bound) →
      ∃ N : Dyadic, N ∈ F₁.unbounded ∧ Format.boundOK F₁.toFormat.boundAfterNext N ∧
        0 ≤ (N : ℝ) ∧ ∀ v : Dyadic, Format.boundOK F₁.b v → |(v : ℝ)| < N := by
    intro b₁ hF
    have hb₁ := nonneg_coe_real b₁
    obtain ⟨N, hN, hbN, hNn⟩ := exists_mem_above (F := F₁) hb₁
    have hnext_nn := (Format.self_le_next F₁.toFormat b₁.val hb₁).trans' hb₁
    refine ⟨N, hN, boundOK_of_abs_le ?_ (boundOK_boundAfterNext_next hF hnext_nn),
      hb₁.trans hbN.le, fun v hv => (abs_coe_real_le_of_boundOK (hF ▸ hv)).trans_lt hbN⟩
    rw [abs_of_nonneg (hb₁.trans hbN.le), abs_of_nonneg hnext_nn]
    exact hNn
  refine localDoubleRounding_of_below h₁u hmem rule (fun {x y} ⟨hy, hby⟩ => ?_)
    (fun {x z w} ⟨hz, _⟩ ⟨hw, hbw⟩ => ?_)
  · rcases hF : F₁.b with _ | b₁
    · exact htop x hF
    obtain ⟨N, hN, hNB, hN0, hlt⟩ := habove b₁ hF
    exact ⟨N, hN, hNB, le_of_lt (lt_of_not_ge fun h =>
      absurd (le_abs_faithful_of_le hN hN0 h hy.isFaithfulRound) (not_le.mpr (hlt y hby)))⟩
  · rcases hF : F₁.b with _ | b₁
    · exact htop x hF
    obtain ⟨N, hN, hNB, hN0, hlt⟩ := habove b₁ hF
    exact ⟨N, hN, hNB, le_of_lt (lt_of_not_ge fun h => absurd (le_abs_faithful_of_le hN hN0
      (le_abs_faithful_of_le (mem_unbounded_of_mem (hmem hN hNB)) hN0 h hz.isFaithfulRound)
      hw.isFaithfulRound) (not_le.mpr (hlt w hbw)))⟩

/-! ### The midpoint for round-to-nearest

RTO → RN is local below the midpoint `M` of the bound's floor `d` and its
successor `N`: past `M` a nearest rounding is at least `N`, inside it at most `d`
(`nearest_split`), and an inexact RTO result never lands on `±M`, a value of
`F₁.extend 1` (`abs_ne_of_toOdd`). -/

/-- Nearest rounding of `x ≥ 0` around a value `d` of `F`, its successor `N` and
their midpoint `M`: the result is at most `d` with `x ≤ M`, or at least `N` with
`M ≤ x`. -/
private theorem nearest_split {F : FiniteFormat} {d : Dyadic} (hd : d ∈ F.unbounded)
    (hd0 : 0 ≤ (d : ℝ)) (hguard : F.exp = ⊥ → 0 < (d : ℝ)) {tb : TieBreak} {x : ℝ}
    {y : Dyadic} (hx : 0 ≤ x) (hy : RoundsFinite F.unbounded (.nearest tb) x y) :
    ((y : ℝ) ≤ d ∧ x ≤ ((F.extend 1).toFormat.next d : ℝ)) ∨
      ((F.toFormat.next d : ℝ) ≤ y ∧ ((F.extend 1).toFormat.next d : ℝ) ≤ x) := by
  have hdN : (d : ℝ) < F.toFormat.next d := Format.lt_next d hd0
  have hN : F.toFormat.next d ∈ F.unbounded := next_mem_unbounded' hd hd0
  rw [next_extend_midpoint' hd0 hguard]
  set N := F.toFormat.next d
  have hgap : ∀ v ∈ F.unbounded, (d : ℝ) < v → (N : ℝ) ≤ v := fun v hv h =>
    next_min' hd hv hd0 hguard h
  have hy0 : 0 ≤ (y : ℝ) := hy.isFaithfulRound.nonneg hx
  rcases le_or_gt x d with hxd | hxd
  · have h := abs_faithful_le_of_le hd (by rwa [abs_of_nonneg hx]) hy.isFaithfulRound
    rw [abs_of_nonneg hy0] at h
    exact Or.inl ⟨h, by linarith⟩
  rcases le_or_gt (N : ℝ) x with hNx | hxN
  · have h := le_abs_faithful_of_le hN (hd0.trans hdN.le) (by rwa [abs_of_nonneg hx])
      hy.isFaithfulRound
    rw [abs_of_nonneg hy0] at h
    exact Or.inr ⟨h, by linarith⟩
  -- `d < x < N`: the faithful roundings are `d` and `N`, and `y` is the nearer.
  have h₁ := hy.nearest_min hd (Or.inl ⟨hd, hxd.le, fun v hv hvx =>
    not_lt.mp fun h => absurd (hgap v hv h) (not_le.mpr (hvx.trans_lt hxN))⟩)
  have h₂ := hy.nearest_min hN (Or.inr ⟨hN, hxN.le, fun v hv hxv => hgap v hv (hxd.trans_le hxv)⟩)
  rw [abs_of_pos (sub_pos.mpr hxd)] at h₁
  rw [abs_of_neg (sub_neg.mpr hxN)] at h₂
  rcases le_or_gt (y : ℝ) d with hyd | hyd
  · rw [abs_of_nonneg (by linarith)] at h₂
    exact Or.inl ⟨hyd, by linarith⟩
  · have hNy := hgap y hy.1 hyd
    rw [abs_of_nonpos (by linarith)] at h₁
    exact Or.inr ⟨hNy, by linarith⟩

/-- An input whose nearest rounding is within `d` is within the midpoint. -/
theorem abs_le_mid_of_nearest {F : FiniteFormat} {d : Dyadic} (hd : d ∈ F.unbounded)
    (hd0 : 0 ≤ (d : ℝ)) (hguard : F.exp = ⊥ → 0 < (d : ℝ)) {tb : TieBreak} {x : ℝ}
    {y : Dyadic} (hy : RoundsFinite F.unbounded (.nearest tb) x y) (hyd : |(y : ℝ)| ≤ d) :
    |x| ≤ ((F.extend 1).toFormat.next d : ℝ) := by
  wlog hx : 0 ≤ x generalizing x y
  · have h := this ((RoundsFinite.neg_nearest _ tb x y).mp hy)
      (by rwa [Dyadic.coe_real_neg, abs_neg]) (by linarith)
    rwa [abs_neg] at h
  have hdN : (d : ℝ) < F.toFormat.next d := Format.lt_next d hd0
  rcases nearest_split hd hd0 hguard hx hy with ⟨-, h⟩ | ⟨h, -⟩
  · rwa [abs_of_nonneg hx]
  · linarith [le_abs_self (y : ℝ)]

/-- An input strictly within the midpoint has its nearest rounding within `d`. -/
theorem abs_le_of_nearest_of_abs_lt_mid {F : FiniteFormat} {d : Dyadic}
    (hd : d ∈ F.unbounded) (hd0 : 0 ≤ (d : ℝ)) (hguard : F.exp = ⊥ → 0 < (d : ℝ))
    {tb : TieBreak} {x : ℝ} {y : Dyadic} (hy : RoundsFinite F.unbounded (.nearest tb) x y)
    (hxM : |x| < ((F.extend 1).toFormat.next d : ℝ)) : |(y : ℝ)| ≤ d := by
  wlog hx : 0 ≤ x generalizing x y
  · have h := this ((RoundsFinite.neg_nearest _ tb x y).mp hy) (by rwa [abs_neg]) (by linarith)
    rwa [Dyadic.coe_real_neg, abs_neg] at h
  rw [abs_of_nonneg hx] at hxM
  rcases nearest_split hd hd0 hguard hx hy with ⟨h, -⟩ | ⟨-, h⟩
  · rwa [abs_of_nonneg (hy.isFaithfulRound.nonneg hx)]
  · linarith

/-- **RTO padding at a value of `F₁.extend 1`.** Under the RN containment, an
inexact RTO rounding into `F₂` never has the magnitude of a value `v` of
`F₁.extend 1` within `next(b₁)`: `F₁.extend 1` there is the shrink of a subformat
of `F₂`, so `±v` is even in `F₂`. -/
theorem abs_ne_of_toOdd {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
      ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p) {x : ℝ} {z : Dyadic}
    (hz : RoundsFinite F₂.unbounded .toOdd x z) (hxz : x ≠ (z : ℝ)) {v : Dyadic}
    (hv : v ∈ (F₁.extend 1).unbounded)
    (hvB : Format.boundOK (F₁.extend 1).toFormat.boundAfterNext v) :
    |(z : ℝ)| ≠ |(v : ℝ)| := by
  have hnot : z ∉ FiniteFormat.withBoundFF (F₁.extend 1)
      ((F₁.extend 1).toFormat.boundAfterNext) := by
    apply toOdd_notMem_of_extend_subset (F₂ := F₂.unbounded) ?_ hp_F₂ hz hxz
    exact ((Format.extend_one_extend_one_subset_extend_two
      (F₁.toFormat.withBound ((F₁.extend 1).toFormat.boundAfterNext))).trans hsub).trans
      F₂.subset_unbounded
  have hvG : v ∈ FiniteFormat.withBoundFF (F₁.extend 1)
      ((F₁.extend 1).toFormat.boundAfterNext) := ⟨hv.1, hv.2.1, hvB⟩
  intro h
  rcases abs_eq_abs.mp h with h | h
  · exact hnot (Dyadic.ext_real h ▸ hvG)
  · have hzv : z = -v := Dyadic.ext_real (by rw [h, Dyadic.coe_real_neg])
    exact hnot (by rw [hzv]; exact FiniteFormat.neg_mem hvG)

/-- The floor of a finite bound: the largest value of `F` within it. -/
private theorem exists_floor {F : FiniteFormat} {b : NonNegDyadic} (hFb : F.b = (b : Bound)) :
    ∃ d : Dyadic, d ∈ F.unbounded ∧ 0 ≤ (d : ℝ) ∧ (d : ℝ) ≤ b.val ∧
      ∀ v ∈ F.unbounded, Format.boundOK F.b v → |(v : ℝ)| ≤ d := by
  have hb := nonneg_coe_real b
  obtain ⟨hd, hdb, hmax⟩ := rndUnbounded_satisfies F .toNegative ((b.val : Dyadic) : ℝ)
    (not_isUndefined_toNegative F)
  refine ⟨_, hd, by simpa using hmax 0 F.unbounded.zero_mem (by simpa using hb), hdb,
    fun v hv hbv => ?_⟩
  have h := abs_coe_real_le_of_boundOK (hFb ▸ hbv)
  rcases le_or_gt 0 (v : ℝ) with hv0 | hv0
  · rw [abs_of_nonneg hv0] at h ⊢
    exact hmax v hv h
  · rw [abs_of_neg hv0] at h ⊢
    have h' := hmax (-v) (FiniteFormat.neg_mem hv) (by rw [Dyadic.coe_real_neg]; exact h)
    rwa [Dyadic.coe_real_neg] at h'

/-- **rnd-RTO-RN is local**, with `L` the inputs within the midpoint `M` of the
bound's floor `d` and its successor. Past `M` an in-bound nearest rounding is
impossible; inside it an inexact RTO result stays strictly inside, since padding
keeps it off `M`, and there both roundings are within `d`. -/
private theorem localDoubleRounding_RTO_RN {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
      ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial) {tb : TieBreak} (h₁u : ¬ F₁.IsUndefined (.nearest tb)) :
    ∃ L, LocalDoubleRounding F₁ F₂ (.nearest tb) .toOdd L := by
  have hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p := two_le_p_of_nontrivial_extend_two hsub hnt
  rcases hF₁b : F₁.b with _ | b₁
  · -- No bound on `F₁`, hence none on `F₂`: the finite rule applies everywhere.
    rw [Format.boundAfterNext_top (F := (F₁.extend 1).toFormat) hF₁b] at hsub
    have hF₂b := bound_top_of_withBound_top_subset hsub
    refine ⟨fun _ => True, fun _ => trivial, fun _ _ => trivial,
      fun _ _ => by rw [hF₂b]; trivial, fun _ hz hw hy => eq_of_rule (B := ⊤) h₁u ?_ hz hw hy
        trivial trivial⟩
    intro x z w hz hw
    refine roundsRTO_RN_finite (F₁ := F₁.withBoundFF ⊤) ?_ hz hw
    rw [Format.boundAfterNext_top (F := ((F₁.withBoundFF ⊤).extend 1).toFormat) rfl]
    exact hsub.trans F₂.subset_unbounded
  obtain ⟨d, hd, hd0, hdb, hdmax⟩ := exists_floor hF₁b
  -- Nontriviality makes the floor positive.
  have hd_pos : 0 < (d : ℝ) := by
    obtain ⟨v, hv, hv0⟩ := hnt
    exact (abs_pos.mpr fun h => hv0 (eq_zero_of_coe_real_zero h)).trans_le
      (hdmax v (mem_unbounded_of_mem hv) hv.2.2)
  have hdB : Format.boundOK (F₁.extend 1).toFormat.boundAfterNext d :=
    boundOK_boundAfterNext_of_boundOK (F₁ := F₁.extend 1)
      (by rw [show (F₁.extend 1).b = F₁.b from rfl, hF₁b]
          exact boundOK_coe_of_abs_le (by rwa [abs_of_nonneg hd0]))
  -- The midpoint `M` lies in `F₂`, and so is an `F₂`-bound.
  set M := ((F₁.extend 1).toFormat.next d : Dyadic)
  have hd1 : d ∈ (F₁.extend 1).unbounded := by
    have h := Format.self_subset_extend F₁.toFormat.unbounded 1 d hd
    exact ⟨h.1, h.2.1, trivial⟩
  have hM1 : M ∈ (F₁.extend 1).unbounded := next_mem_unbounded' hd1 hd0
  have hM_nn : 0 ≤ (M : ℝ) := hd0.trans (Format.lt_next d hd0).le
  have hMB : Format.boundOK (F₁.extend 1).toFormat.boundAfterNext M := by
    have hb₁ := nonneg_coe_real b₁
    have hnext := Format.next_nonneg (F₁.extend 1).toFormat b₁.val hb₁
    refine boundOK_of_abs_le ?_ (boundOK_boundAfterNext_next (F₁ := F₁.extend 1) hF₁b hnext)
    rw [abs_of_nonneg hM_nn, abs_of_nonneg hnext]
    exact next_mono (F := F₁.extend 1) hd0 hdb fun _ => hd_pos
  have hM_F₂ : M ∈ F₂ := by
    have h := Format.extend_mono F₁.toFormat.unbounded
      (by exact_mod_cast (by omega : (1 : ℕ) ≤ 2) : (1 : ℕ) ≤ 2) M hM1
    exact hsub _ ⟨h.1, h.2.1, hMB⟩
  have hM_u : M ∈ F₂.unbounded := mem_unbounded_of_mem hM_F₂
  have hguard : F₁.exp = ⊥ → 0 < (d : ℝ) := fun _ => hd_pos
  -- An in-bound nearest rounding puts its input within `M`.
  have pin : ∀ {x : ℝ} {y : Dyadic}, RoundsFinite F₁.unbounded (.nearest tb) x y →
      Format.boundOK F₁.b y → |x| ≤ M := fun hy hb =>
    abs_le_mid_of_nearest hd hd0 hguard hy (hdmax _ hy.1 hb)
  -- An inexact RTO result within `M` is strictly inside, and so is its input.
  have strict : ∀ {x : ℝ} {z : Dyadic}, RoundsFinite F₂.unbounded .toOdd x z →
      x ≠ (z : ℝ) → |(z : ℝ)| ≤ M → |(z : ℝ)| < M ∧ |x| < M := fun {x z} hz hxz hzM => by
    have hzM' : |(z : ℝ)| < M := lt_of_le_of_ne hzM (by
      rw [← abs_of_nonneg hM_nn]; exact abs_ne_of_toOdd hsub hp_F₂ hz hxz hM1 hMB)
    exact ⟨hzM', lt_of_not_ge fun h =>
      absurd (le_abs_faithful_of_le hM_u hM_nn h hz.2.1) (not_le.mpr hzM')⟩
  have hbound : ∀ {x : ℝ} {z : Dyadic}, |x| ≤ M → RoundsFinite F₂.unbounded .toOdd x z →
      Format.boundOK F₂.b z := fun hxM hz => by
    refine boundOK_of_abs_le ?_ hM_F₂.2.2
    rw [abs_of_nonneg hM_nn]
    exact abs_faithful_le_of_le hM_u hxM hz.2.1
  have hd0q : (0 : ℚ) ≤ (d : ℚ) := by exact_mod_cast hd0
  refine ⟨fun x => |x| ≤ M, fun ⟨hy, hb⟩ => pin hy hb, fun {x z w} ⟨hz, _⟩ ⟨hw, hbw⟩ => ?_,
    hbound, fun {x z w y} hxM hz hw hy => ?_⟩
  · rcases eq_or_ne x (z : ℝ) with hxz | hxz
    · rw [hxz]; exact pin hw hbw
    · exact (strict hz hxz (pin hw hbw)).2.le
  · rcases eq_or_ne x (z : ℝ) with hxz | hxz
    · exact RoundsFinite.unique h₁u (by rw [hxz]; exact hw) hy
    obtain ⟨hzM, hxM'⟩ := strict hz hxz (abs_faithful_le_of_le hM_u hxM hz.2.1)
    exact eq_of_rule (B := ((⟨d, hd0q⟩ : NonNegDyadic) : Bound)) h₁u
      (roundsRTO_RN_finite_of_extend (F₁ := F₁.withBoundFF (⟨d, hd0q⟩ : NonNegDyadic))
        (((withBound_subset_of_boundOK (F₁.extend 2).toFormat hdB).trans hsub).trans
          F₂.subset_unbounded) hp_F₂) hz hw hy
      (boundOK_coe_of_abs_le (abs_le_of_nearest_of_abs_lt_mid hd hd0 hguard hw hzM))
      (boundOK_coe_of_abs_le (abs_le_of_nearest_of_abs_lt_mid hd hd0 hguard hy hxM'))

/-! ## The total theorems -/

/-- The containment `F₁.withBound next(b₁) ⊆ F₂` keeps `F₁` bounded by any value
it admits inside `F₂`. -/
private theorem withBoundFF_subset {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {T : NonNegDyadic} (hT : Format.boundOK F₁.toFormat.boundAfterNext T.val) :
    (F₁.withBoundFF T).toFormat ⊆ F₂.unbounded.toFormat :=
  ((withBound_subset_of_boundOK _ hT).trans hsub).trans F₂.subset_unbounded

/-- The same for the containment `(F₁.extend 1).withBound next(b₁) ⊆ F₂`. -/
private theorem withBoundFF_extend_one_subset {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {T : NonNegDyadic} (hT : Format.boundOK F₁.toFormat.boundAfterNext T.val) :
    ((F₁.withBoundFF T).extend 1).toFormat ⊆ F₂.unbounded.toFormat :=
  ((withBound_subset_of_boundOK (F₁.extend 1).toFormat hT).trans hsub).trans
    F₂.subset_unbounded

/-- **rnd-RTZ-RTZ is local** below a value of `F₁` within `next(b₁)`. The relaxed
containment is needed: `A(1, ⊥, 5) ⊆ A(3, ⊥, 4)`, yet at `x = 5.2` RTZ gives `4`
in `F₁` (in bound) and `5` in `F₂` (overflow). -/
private theorem localDoubleRounding_RTZ_RTZ {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat) :
    LocalDoubleRounding F₁ F₂ .toZero .toZero (BelowValue F₁ F₁.toFormat.boundAfterNext) :=
  localDoubleRounding_of_above (not_isUndefined_toZero F₁)
    (fun hT hTB => hsub _ ⟨hT.1, hT.2.1, hTB⟩)
    (fun _ hTB => roundsRTZ_RTZ_finite (withBoundFF_subset hsub hTB))

private theorem localDoubleRounding_RTO_RTO {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p) (h₁u : ¬ F₁.IsUndefined .toOdd) :
    LocalDoubleRounding F₁ F₂ .toOdd .toOdd (BelowValue F₁ F₁.toFormat.boundAfterNext) :=
  localDoubleRounding_of_above h₁u (fun hT hTB => hsub _ ⟨hT.1, hT.2.1, hTB⟩)
    (fun _ hTB => roundsRTO_RTO_finite (withBoundFF_subset hsub hTB) hp_F₂)

private theorem localDoubleRounding_RTO_RTZ {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p) :
    LocalDoubleRounding F₁ F₂ .toZero .toOdd (BelowValue F₁ F₁.toFormat.boundAfterNext) :=
  localDoubleRounding_of_above (not_isUndefined_toZero F₁)
    (fun hT hTB => hsub _ (mem_extend_one_withBound_of_mem_unbounded hT hTB))
    (fun _ hTB => roundsRTO_RTZ_finite_of_extend (withBoundFF_extend_one_subset hsub hTB) hp_F₂)

private theorem localDoubleRounding_RTO_RAZ {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p) :
    LocalDoubleRounding F₁ F₂ .awayZero .toOdd (BelowValue F₁ F₁.toFormat.boundAfterNext) :=
  localDoubleRounding_of_above (not_isUndefined_awayZero F₁)
    (fun hT hTB => hsub _ (mem_extend_one_withBound_of_mem_unbounded hT hTB))
    (fun _ hTB => roundsRTO_RAZ_finite_of_extend (withBoundFF_extend_one_subset hsub hTB)
      hp_F₂)

/-- **rnd-RAZ-RAZ is local** below the in-bound rounding itself: rounding away
from zero never shrinks `|x|`, so the direct rounding, or the double rounding,
is a value of `F₁` within its bound above `|x|`. -/
private theorem localDoubleRounding_RAZ_RAZ {F₁ F₂ : FiniteFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    LocalDoubleRounding F₁ F₂ .awayZero .awayZero (BelowValue F₁ F₁.b) := by
  have habs : ∀ {v : Dyadic}, v ∈ F₁.unbounded → Format.boundOK F₁.b v →
      Dyadic.abs v ∈ F₁.unbounded ∧ Format.boundOK F₁.b (Dyadic.abs v) := fun hv hb =>
    ⟨Format.abs_mem hv, boundOK_of_abs_le (by rw [Dyadic.coe_abs, abs_abs]) hb⟩
  refine localDoubleRounding_of_below (not_isUndefined_awayZero F₁)
    (fun hT hTB => hsub _ ⟨hT.1, hT.2.1, hTB⟩)
    (fun _ hTB => roundsRAZ_RAZ_finite
      (((withBound_subset_of_boundOK F₁.toFormat hTB).trans hsub).trans F₂.subset_unbounded))
    (fun ⟨hy, hby⟩ => ?_) (fun ⟨hz, _⟩ ⟨hw, hbw⟩ => ?_)
  · obtain ⟨h1, h2⟩ := habs hy.1 hby
    exact ⟨_, h1, h2, by rw [Dyadic.coe_abs]; exact hy.2.1⟩
  · obtain ⟨h1, h2⟩ := habs hw.1 hbw
    exact ⟨_, h1, h2, by rw [Dyadic.coe_abs]; exact hz.2.1.trans hw.2.1⟩

/-- **rnd-RTZ-RTZ**, total form: the direct rounding overflows, or the rounding into
`F₂` and the double rounding stay in bound and agree with it. -/
theorem roundsRTZ_RTZ_inBound {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (x : ℝ) :
    Overflows F₁ .toZero x ∨
    (∃ z w : Dyadic, RoundsInBound F₂ .toZero x z ∧
      RoundsInBound F₁ .toZero (z : ℝ) w ∧
      RoundsInBound F₁ .toZero x w) :=
  (localDoubleRounding_RTZ_RTZ hsub).inBound (not_isUndefined_toZero F₁)
    (not_isUndefined_toZero F₂) x

/-- **rnd-RTZ-RTZ**, no overflow: if the double rounding stays in bound, so does the
direct rounding. -/
theorem roundsRTZ_RTZ_noOverflow {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsInBound F₂ .toZero x z) (hw : RoundsInBound F₁ .toZero (z : ℝ) w) :
    ¬ Overflows F₁ .toZero x :=
  (localDoubleRounding_RTZ_RTZ hsub).not_overflows hz hw

/-- **rnd-RAZ-RAZ**, total form: the direct rounding overflows, or the rounding into
`F₂` and the double rounding stay in bound and agree with it. -/
theorem roundsRAZ_RAZ_inBound {F₁ F₂ : FiniteFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat) (x : ℝ) :
    Overflows F₁ .awayZero x ∨
    (∃ z w : Dyadic, RoundsInBound F₂ .awayZero x z ∧
      RoundsInBound F₁ .awayZero (z : ℝ) w ∧
      RoundsInBound F₁ .awayZero x w) :=
  (localDoubleRounding_RAZ_RAZ hsub).inBound (not_isUndefined_awayZero F₁)
    (not_isUndefined_awayZero F₂) x

/-- **rnd-RAZ-RAZ**, no overflow: the double rounding is a candidate for the direct
one, so it bounds it. No containment is needed. -/
theorem roundsRAZ_RAZ_noOverflow {F₁ F₂ : FiniteFormat} {x : ℝ} {z w : Dyadic}
    (hz : RoundsInBound F₂ .awayZero x z) (hw : RoundsInBound F₁ .awayZero (z : ℝ) w) :
    ¬ Overflows F₁ .awayZero x := by
  rintro ⟨y, hy, hby⟩
  have hwx : (w : ℝ) * x ≥ 0 := by
    rcases eq_or_ne (z : ℝ) 0 with h0 | h0
    · have hx : x = 0 := abs_nonpos_iff.mp (by simpa [h0] using hz.1.2.1)
      rw [hx, mul_zero]
    · exact mul_nonneg_of_common_sign hw.1.2.2.1
        (by linarith [hz.1.2.2.1] : x * (z : ℝ) ≥ 0) fun h => absurd h h0
  exact hby (boundOK_of_abs_le (hy.2.2.2 w hw.1.1 (hz.1.2.1.trans hw.1.2.1) hwx) hw.2)

/-- **rnd-RTO-RTO**, total form: the direct rounding overflows, or the rounding into
`F₂` and the double rounding stay in bound and agree with it. -/
theorem roundsRTO_RTO_inBound {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    (h₁u : ¬ F₁.IsUndefined .toOdd) (x : ℝ) :
    Overflows F₁ .toOdd x ∨
    (∃ z w : Dyadic, RoundsInBound F₂ .toOdd x z ∧
      RoundsInBound F₁ .toOdd (z : ℝ) w ∧
      RoundsInBound F₁ .toOdd x w) :=
  (localDoubleRounding_RTO_RTO hsub hp_F₂ h₁u).inBound h₁u
    (not_isUndefined_of_two_le_p hp_F₂) x

/-- **rnd-RTO-RTO**, no overflow: if the double rounding stays in bound, so does the
direct rounding. -/
theorem roundsRTO_RTO_noOverflow {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p) (h₁u : ¬ F₁.IsUndefined .toOdd)
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsInBound F₂ .toOdd x z) (hw : RoundsInBound F₁ .toOdd (z : ℝ) w) :
    ¬ Overflows F₁ .toOdd x :=
  (localDoubleRounding_RTO_RTO hsub hp_F₂ h₁u).not_overflows hz hw

/-- **rnd-RTO-RTZ**, total form: the direct rounding overflows, or the rounding into
`F₂` and the double rounding stay in bound and agree with it. Nontriviality of `F₁`
forces `2 ≤ F₂.p` through the containment. -/
theorem roundsRTO_RTZ_inBound {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial) (x : ℝ) :
    Overflows F₁ .toZero x ∨
    (∃ z w : Dyadic, RoundsInBound F₂ .toOdd x z ∧
      RoundsInBound F₁ .toZero (z : ℝ) w ∧
      RoundsInBound F₁ .toZero x w) :=
  (localDoubleRounding_RTO_RTZ hsub (two_le_p_of_nontrivial hsub hnt)).inBound
    (not_isUndefined_toZero F₁)
    (not_isUndefined_of_two_le_p (two_le_p_of_nontrivial hsub hnt)) x

/-- **rnd-RTO-RTZ**, no overflow: if the double rounding stays in bound, so does the
direct rounding. -/
theorem roundsRTO_RTZ_noOverflow {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial) {x : ℝ} {z w : Dyadic}
    (hz : RoundsInBound F₂ .toOdd x z) (hw : RoundsInBound F₁ .toZero (z : ℝ) w) :
    ¬ Overflows F₁ .toZero x :=
  (localDoubleRounding_RTO_RTZ hsub (two_le_p_of_nontrivial hsub hnt)).not_overflows hz hw

/-- **rnd-RTO-RAZ**, total form: the direct rounding overflows, or the rounding into
`F₂` and the double rounding stay in bound and agree with it. Nontriviality of `F₁`
forces `2 ≤ F₂.p` through the containment. -/
theorem roundsRTO_RAZ_inBound {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial) (x : ℝ) :
    Overflows F₁ .awayZero x ∨
    (∃ z w : Dyadic, RoundsInBound F₂ .toOdd x z ∧
      RoundsInBound F₁ .awayZero (z : ℝ) w ∧
      RoundsInBound F₁ .awayZero x w) :=
  (localDoubleRounding_RTO_RAZ hsub (two_le_p_of_nontrivial hsub hnt)).inBound
    (not_isUndefined_awayZero F₁)
    (not_isUndefined_of_two_le_p (two_le_p_of_nontrivial hsub hnt)) x

/-- **rnd-RTO-RAZ**, no overflow: if the double rounding stays in bound, so does the
direct rounding. -/
theorem roundsRTO_RAZ_noOverflow {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial) {x : ℝ} {z w : Dyadic}
    (hz : RoundsInBound F₂ .toOdd x z) (hw : RoundsInBound F₁ .awayZero (z : ℝ) w) :
    ¬ Overflows F₁ .awayZero x :=
  (localDoubleRounding_RTO_RAZ hsub (two_le_p_of_nontrivial hsub hnt)).not_overflows hz hw

/-- **rnd-RTO-RN**, total form: the direct rounding overflows, or the rounding into `F₂`
and the double rounding stay in bound and agree with it. Nontriviality of `F₁` forces `2
≤ F₂.p` through the containment; `F₁` must support the tie-break (vacuous for RNA). -/
theorem roundsRTO_RN_inBound {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
      ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial)
    {tb : TieBreak} (h₁u : ¬ F₁.IsUndefined (.nearest tb)) (x : ℝ) :
    Overflows F₁ (.nearest tb) x ∨
    (∃ z w : Dyadic, RoundsInBound F₂ .toOdd x z ∧
      RoundsInBound F₁ (.nearest tb) (z : ℝ) w ∧
      RoundsInBound F₁ (.nearest tb) x w) :=
  (localDoubleRounding_RTO_RN hsub hnt h₁u).choose_spec.inBound h₁u
    (not_isUndefined_of_two_le_p (two_le_p_of_nontrivial_extend_two hsub hnt)) x

/-- **rnd-RTO-RN**, no overflow: if the double rounding stays in bound, so does the
direct rounding. -/
theorem roundsRTO_RN_noOverflow {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
      ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial) {tb : TieBreak} (h₁u : ¬ F₁.IsUndefined (.nearest tb))
    {x : ℝ} {z w : Dyadic}
    (hz : RoundsInBound F₂ .toOdd x z) (hw : RoundsInBound F₁ (.nearest tb) (z : ℝ) w) :
    ¬ Overflows F₁ (.nearest tb) x :=
  (localDoubleRounding_RTO_RN hsub hnt h₁u).choose_spec.not_overflows hz hw

/-! ## Agreement in bound

When the double rounding and the direct rounding are both in bound they agree, under
the plain containment: the relaxed bounds above only keep `F₂` from
overflowing. -/

/-- Agreement from a finite rule: restrict the double rounding to `F₁`, apply the rule
against `F₂.unbounded`, lift back, and compare by uniqueness. -/
private theorem eq_of_inBound {F₁ F₂ : FiniteFormat} {rm₁ rm₂ : RoundingMode}
    (h₁u : ¬ F₁.IsUndefined rm₁)
    (rule : ∀ {x : ℝ} {z w : Dyadic}, RoundsFinite F₂.unbounded rm₂ x z →
      RoundsFinite F₁ rm₁ (z : ℝ) w → RoundsFinite F₁ rm₁ x w)
    {x : ℝ} {z w y : Dyadic} (hz : RoundsInBound F₂ rm₂ x z)
    (hw : RoundsInBound F₁ rm₁ (z : ℝ) w) (hy : RoundsInBound F₁ rm₁ x y) : w = y :=
  eq_of_rule (B := F₁.b) h₁u rule hz.1 hw.1 hy.1 hw.2 hy.2

/-- **rnd-RTZ-RTZ**, in bound: the double rounding agrees with the direct rounding. -/
theorem roundsRTZ_RTZ_agree {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    {x : ℝ} {z w y : Dyadic} (hz : RoundsInBound F₂ .toZero x z)
    (hw : RoundsInBound F₁ .toZero (z : ℝ) w) (hy : RoundsInBound F₁ .toZero x y) :
    w = y :=
  eq_of_inBound (not_isUndefined_toZero F₁)
    (roundsRTZ_RTZ_finite (hsub.trans F₂.subset_unbounded)) hz hw hy

/-- **rnd-RAZ-RAZ**, in bound: the double rounding agrees with the direct rounding. -/
theorem roundsRAZ_RAZ_agree {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    {x : ℝ} {z w y : Dyadic} (hz : RoundsInBound F₂ .awayZero x z)
    (hw : RoundsInBound F₁ .awayZero (z : ℝ) w) (hy : RoundsInBound F₁ .awayZero x y) :
    w = y :=
  eq_of_inBound (not_isUndefined_awayZero F₁)
    (roundsRAZ_RAZ_finite (hsub.trans F₂.subset_unbounded)) hz hw hy

/-- **rnd-RTO-RTO**, in bound: the double rounding agrees with the direct rounding. -/
theorem roundsRTO_RTO_agree {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p) (h₁u : ¬ F₁.IsUndefined .toOdd)
    {x : ℝ} {z w y : Dyadic} (hz : RoundsInBound F₂ .toOdd x z)
    (hw : RoundsInBound F₁ .toOdd (z : ℝ) w) (hy : RoundsInBound F₁ .toOdd x y) :
    w = y :=
  eq_of_inBound h₁u (roundsRTO_RTO_finite (hsub.trans F₂.subset_unbounded) hp_F₂) hz hw hy

/-- **rnd-RTO-RTZ**, in bound: the double rounding agrees with the direct rounding. -/
theorem roundsRTO_RTZ_agree {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat) (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {x : ℝ} {z w y : Dyadic} (hz : RoundsInBound F₂ .toOdd x z)
    (hw : RoundsInBound F₁ .toZero (z : ℝ) w) (hy : RoundsInBound F₁ .toZero x y) :
    w = y :=
  eq_of_inBound (not_isUndefined_toZero F₁)
    (roundsRTO_RTZ_finite_of_extend (hsub.trans F₂.subset_unbounded) hp_F₂) hz hw hy

/-- **rnd-RTO-RAZ**, in bound: the double rounding agrees with the direct rounding. -/
theorem roundsRTO_RAZ_agree {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat) (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {x : ℝ} {z w y : Dyadic} (hz : RoundsInBound F₂ .toOdd x z)
    (hw : RoundsInBound F₁ .awayZero (z : ℝ) w) (hy : RoundsInBound F₁ .awayZero x y) :
    w = y :=
  eq_of_inBound (not_isUndefined_awayZero F₁)
    (roundsRTO_RAZ_finite_of_extend (hsub.trans F₂.subset_unbounded) hp_F₂) hz hw hy

/-- **rnd-RTO-RN**, in bound: the double rounding agrees with the direct rounding. -/
theorem roundsRTO_RN_agree {F₁ F₂ : FiniteFormat} {tb : TieBreak}
    (hsub : (F₁.extend 2).toFormat ⊆ F₂.toFormat) (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    (h₁u : ¬ F₁.IsUndefined (.nearest tb))
    {x : ℝ} {z w y : Dyadic} (hz : RoundsInBound F₂ .toOdd x z)
    (hw : RoundsInBound F₁ (.nearest tb) (z : ℝ) w)
    (hy : RoundsInBound F₁ (.nearest tb) x y) : w = y :=
  eq_of_inBound h₁u (roundsRTO_RN_finite_of_extend (hsub.trans F₂.subset_unbounded) hp_F₂) hz hw hy

end Mpfx
