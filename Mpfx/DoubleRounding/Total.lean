import Mpfx.DoubleRounding.Nearest
import Mpfx.DoubleRounding.Propagation

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

/-! ## The floor of the bound

RTO → RN needs the bound on the grid: its threshold is the midpoint between the
bound and its successor. Bounding `F₁` by the floor `d` of `b₁` (the largest
value `≤ b₁`, i.e. the RTN rounding of `b₁`) keeps the same in-bound values. The
corner `exp = ⊥ ∧ d = 0`, where values of arbitrarily small magnitude leave the
bound no successor, forces `b₁ = 0`. -/


/-- Bound-floor setup for a finite bound `b₁`: either the degenerate corner
(`exp = ⊥` and `b₁ = 0`), or a floor `D` with a regular floor-adjusted
format, the bound-transfer properties, and monotone `next` bounds at `F₁`
and `F₁.extend 1`. -/
private theorem bound_floor_setup {F₁ : FiniteFormat} {b₁ : NonNegDyadic}
    (hF₁b : F₁.b = (b₁ : Bound)) :
    (F₁.exp = ⊥ ∧ ((b₁.val : Dyadic) : ℝ) = 0) ∨
    (∃ D : NonNegDyadic,
      (∀ b : NonNegDyadic,
        (FiniteFormat.withBoundFF F₁ (D : Bound)).b
          = (b : Bound) →
        b.val ∈ FiniteFormat.withBoundFF F₁ (D : Bound) ∧
        ((FiniteFormat.withBoundFF F₁ (D : Bound)).exp = ⊥ →
          0 < ((b.val : Dyadic) : ℝ))) ∧
      Format.boundOK F₁.b D.val ∧
      (∀ v : Dyadic, v ∈ F₁.unbounded → Format.boundOK F₁.b v →
        Format.boundOK ((D : Bound)) v) ∧
      ((F₁.toFormat.next D.val : Dyadic) : ℝ)
        ≤ ((F₁.toFormat.next b₁.val : Dyadic) : ℝ) ∧
      (((F₁.extend 1).toFormat.next D.val : Dyadic) : ℝ)
        ≤ (((F₁.extend 1).toFormat.next b₁.val : Dyadic) : ℝ)) := by
  have hb₁_nn : 0 ≤ ((b₁.val : Dyadic) : ℝ) := nonneg_coe_real b₁
  obtain ⟨hd_mem, hd_le, hd_max⟩ :=
    rndUnbounded_satisfies F₁ .toNegative ((b₁.val : Dyadic) : ℝ)
      (not_isUndefined_toNegative F₁)
  set d := rndUnbounded F₁ .toNegative ((b₁.val : Dyadic) : ℝ)
    (not_isUndefined_toNegative F₁) with hd_def
  have hd_nn : 0 ≤ ((d : Dyadic) : ℝ) := by
    have h := hd_max 0 F₁.unbounded.zero_mem
      (by rw [Dyadic.coe_real_zero]; exact hb₁_nn)
    rwa [Dyadic.coe_real_zero] at h
  by_cases hdeg : F₁.exp = ⊥ ∧ ((d : Dyadic) : ℝ) = 0
  · -- Degenerate: `b₁ = 0` (a positive `b₁` admits a small power of two below).
    obtain ⟨hexp, hd0⟩ := hdeg
    left
    refine ⟨hexp, ?_⟩
    by_contra hb₁ne
    have hb₁_pos : 0 < ((b₁.val : Dyadic) : ℝ) := lt_of_le_of_ne hb₁_nn (Ne.symm hb₁ne)
    set K := Int.log 2 ((b₁.val : Dyadic) : ℝ) with hK_def
    have h2K : (0 : ℝ) < (2 : ℝ) ^ K := zpow_pos (by norm_num) _
    have h2K_le : (2 : ℝ) ^ K ≤ ((b₁.val : Dyadic) : ℝ) :=
      Int.zpow_log_le_self (by norm_num) hb₁_pos
    have hg_mem : Dyadic.ofIntZpow 1 K ∈ F₁.unbounded := by
      refine ⟨?_, ?_, trivial⟩
      · change Dyadic.precisionAtMost F₁.p _
        exact precisionAtMost_one_zpow F₁.pos K
      · change Dyadic.quantumAtLeast F₁.exp _
        rw [hexp]
        trivial
    have hg_val : ((Dyadic.ofIntZpow 1 K : Dyadic) : ℝ) = (2 : ℝ) ^ K :=
    coe_real_ofIntZpow_one K
    have h := hd_max (Dyadic.ofIntZpow 1 K) hg_mem (by rw [hg_val]; exact h2K_le)
    rw [hg_val, hd0] at h
    linarith
  · right
    push Not at hdeg
    have hguard : F₁.exp = ⊥ → 0 < ((d : Dyadic) : ℝ) := fun h =>
      lt_of_le_of_ne hd_nn (Ne.symm (hdeg h))
    have hd_nn_q : (0 : ℚ) ≤ (d : ℚ) := by
      exact_mod_cast hd_nn
    refine ⟨⟨d, hd_nn_q⟩, ?_, ?_, ?_, ?_, ?_⟩
    · -- The floor-adjusted format has a regular (on-grid) bound.
      intro b hb
      have hDb : (⟨d, hd_nn_q⟩ : NonNegDyadic) = b := WithTop.coe_inj.mp hb
      refine ⟨?_, ?_⟩
      · rw [← hDb]
        exact ⟨hd_mem.1, hd_mem.2.1, by
          change |(d : ℚ)| ≤ ((d : Dyadic) : ℚ)
          rw [abs_of_nonneg hd_nn_q]⟩
      · intro hbot
        rw [← hDb]
        exact hguard hbot
    · -- `D` is in-bound for the original bound.
      rw [hF₁b]
      have hr : |((d : Dyadic) : ℝ)| ≤ ((b₁.val : Dyadic) : ℝ) := by
        rw [abs_of_nonneg hd_nn]; exact hd_le
      rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast, ← Rat.cast_abs] at hr
      change |(d : ℚ)| ≤ ((b₁.val : Dyadic) : ℚ)
      exact_mod_cast hr
    · -- Grid values within `b₁` are within `D`.
      intro v hv hbv
      rw [hF₁b] at hbv
      have h1r : |(v : ℝ)| ≤ ((b₁.val : Dyadic) : ℝ) := by
        exact_mod_cast hbv
      have h2r : |(v : ℝ)| ≤ ((d : Dyadic) : ℝ) := by
        rcases le_or_gt 0 ((v : Dyadic) : ℝ) with hv0 | hv0
        · have h := hd_max v hv (by rwa [abs_of_nonneg hv0] at h1r)
          rwa [abs_of_nonneg hv0]
        · have h := hd_max (-v) (FiniteFormat.neg_mem hv)
            (by rw [Dyadic.coe_real_neg]; rw [abs_of_neg hv0] at h1r; linarith)
          rw [Dyadic.coe_real_neg] at h
          rw [abs_of_neg hv0]
          linarith
      change |(v : ℚ)| ≤ ((d : Dyadic) : ℚ)
      exact_mod_cast h2r
    · exact next_mono hd_nn hd_le hguard
    · exact next_mono (F := F₁.extend 1) hd_nn hd_le
        (fun h => hguard (exp_bot_of_extend_bot (F₁ := F₁) (k := 1) h))

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

/-- **rnd-RTO-RN is local**, with `L` the inputs within the midpoint `M` of the
bound's grid floor `D` and its successor. Past `M` an in-bound nearest rounding
is impossible; inside it an inexact RTO result stays strictly inside, since
padding keeps it off `M`, and there both roundings are within `D`. -/
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
  rcases bound_floor_setup hF₁b with ⟨-, hb₁0⟩ | ⟨D, hreg_G, -, hD_max, -, hmono_ext⟩
  · -- `b₁ = 0` with `exp = ⊥` leaves `F₁ = {0}`, against nontriviality.
    exfalso
    obtain ⟨d, hd, hd0⟩ := hnt
    have h := abs_coe_real_le_of_boundOK (hF₁b ▸ hd.2.2)
    rw [hb₁0] at h
    exact hd0 (eq_zero_of_coe_real_zero (abs_nonpos_iff.mp h))
  set G := FiniteFormat.withBoundFF F₁ (D : Bound)
  have hsubG : ((G.extend 2).toFormat.withBound (G.extend 1).toFormat.boundAfterNext)
      ⊆ F₂.toFormat :=
    (Format.withBound_mono _ fun _ =>
      boundOK_boundAfterNext_mono (F := F₁.extend 1) (G := G.extend 1)
        hF₁b rfl rfl hmono_ext).trans hsub
  obtain ⟨hD_mem, hguard⟩ := hreg_G D rfl
  set M := ((G.extend 1).toFormat.next D.val : Dyadic)
  have hM_F₂ : M ∈ F₂ := hsubG _ (next_mem_extend_two_withBound (F₁ := G) rfl hD_mem)
  have hM_u : M ∈ F₂.unbounded := mem_unbounded_of_mem hM_F₂
  have hM_nn : 0 ≤ (M : ℝ) := by
    rw [next_extend_midpoint' (nonneg_coe_real D) hguard]
    linarith [nonneg_coe_real D, (next_facts hD_mem).2.1]
  -- An in-bound nearest rounding at `G` puts its input within `M`.
  have pinG : ∀ {x : ℝ} {y : Dyadic}, RoundsFinite F₁.unbounded (.nearest tb) x y →
      Format.boundOK F₁.b y → |x| ≤ M := fun hy hb =>
    abs_le_mid_of_nearest_inbound (F₁ := G) rfl hD_mem hguard hy.isFaithfulRound
      (fun _ hc hcf => hy.nearest_min hc hcf) (hD_max _ hy.1 hb)
  -- An inexact RTO result within `M` is strictly inside, and so is its input.
  have strict : ∀ {x : ℝ} {z : Dyadic}, RoundsFinite F₂.unbounded .toOdd x z →
      x ≠ (z : ℝ) → |(z : ℝ)| ≤ M → |(z : ℝ)| < M ∧ |x| < M := fun hz hxz hzM => by
    have hzM' := abs_lt_mid_of_toOdd (F₁ := G) hsubG rfl hD_mem hguard hp_F₂ hz hxz hzM
    exact ⟨hzM', lt_of_not_ge fun h =>
      absurd (le_abs_faithful_of_le hM_u hM_nn h hz.2.1) (not_le.mpr hzM')⟩
  have hbound : ∀ {x : ℝ} {z : Dyadic}, |x| ≤ M → RoundsFinite F₂.unbounded .toOdd x z →
      Format.boundOK F₂.b z := fun hxM hz => by
    refine boundOK_of_abs_le ?_ hM_F₂.2.2
    rw [abs_of_nonneg hM_nn]
    exact abs_faithful_le_of_le hM_u hxM hz.2.1
  refine ⟨fun x => |x| ≤ M, fun ⟨hy, hb⟩ => pinG hy hb, fun {x z w} ⟨hz, _⟩ ⟨hw, hbw⟩ => ?_,
    hbound, fun {x z w y} hxM hz hw hy => ?_⟩
  · rcases eq_or_ne x (z : ℝ) with hxz | hxz
    · rw [hxz]; exact pinG hw hbw
    · exact (strict hz hxz (pinG hw hbw)).2.le
  · rcases eq_or_ne x (z : ℝ) with hxz | hxz
    · exact RoundsFinite.unique h₁u (by rw [hxz]; exact hw) hy
    obtain ⟨hzM, hxM'⟩ := strict hz hxz (abs_faithful_le_of_le hM_u hxM hz.2.1)
    exact eq_of_rule (B := (D : Bound)) h₁u
      (roundsRTO_RN_finite (F₁ := G) (hsubG.trans F₂.subset_unbounded)) hz hw hy
      (nearest_boundOK_of_abs_lt_mid (F₁ := G) rfl hD_mem hguard hw hzM)
      (nearest_boundOK_of_abs_lt_mid (F₁ := G) rfl hD_mem hguard hy hxM')

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
  RoundsFinite.unique h₁u
    (RoundsFinite.lift (rule hz.1 (RoundsFinite.restrict hw.1 hw.2)) hy.1 hy.2) hy.1

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
