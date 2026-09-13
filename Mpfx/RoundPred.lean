import Mpfx.Rounding
import Mpfx.CanonicalExp
import Mpfx.Parity

/-!
# Round-predicate layer

Consequences of the `RoundsFinite` spec, per mode and mode-generic: uniqueness,
faithfulness, sign preservation and monotonicity.

Nothing here mentions the `rnd` construction.
-/

namespace Mpfx

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
  have offGrid : ∀ {a b : Dyadic}, a ≠ b →
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
      have hxa := offGrid hab hdist
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
            (offGrid hab hdist')).mpr
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
need an order placing `.overflow false` below every `.finite` and
`.overflow true` above. -/
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
