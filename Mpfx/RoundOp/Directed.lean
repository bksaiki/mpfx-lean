import Mpfx.RoundOp.Defs

/-!
# Constructive rounding: directed-mode obligations

Soundness and uniqueness for the directed modes
(`toNegative`, `toPositive`, `toZero`, `awayZero`).
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

theorem rndUnbounded_satisfies_toZero (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .toZero) :
    RoundsFinite F.unbounded .toZero x (rndUnbounded F .toZero x h) := by
  have h_rnd_eq : rndUnbounded F .toZero x h =
      Dyadic.ofIntZpow (rndInt .toZero x (F.canonicalExp x)) (F.canonicalExp x) := by
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.toZero : RoundingMode) ≠ .toOdd)]
    rw [dif_neg (by decide : (RoundingMode.toZero : RoundingMode) ≠ .nearest .toEven)]
  rw [h_rnd_eq]
  set e := F.canonicalExp x
  set c := rndInt .toZero x e
  set y : Dyadic := Dyadic.ofIntZpow c e
  have h_y_real : (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ e := Dyadic.coe_ofIntZpow c e
  have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have h_c_eq : c = if 0 ≤ x then ⌊x * (2 : ℝ) ^ (-e)⌋ else ⌈x * (2 : ℝ) ^ (-e)⌉ := by
    change rndInt .toZero x e = _
    rfl
  have h_c_bound : ∀ {p : ℕ+}, F.p = ((p : ℕ+) : WithTop ℕ+) →
      |c| ≤ (2 : ℤ) ^ (p : ℕ) := fun hp => by
    rw [h_c_eq]
    by_cases hx_nn : 0 ≤ x
    · rw [if_pos hx_nn]
      apply abs_floor_le_of_abs_lt
      push_cast; exact floor_mantissa_lt hp
    · rw [if_neg hx_nn]
      apply abs_ceil_le_of_abs_lt
      push_cast; exact floor_mantissa_lt hp
  have h_mem : y ∈ F.unbounded :=
    ofIntZpow_mem_unbounded F (fun hexp => F.exp_le_canonicalExp x hexp) h_c_bound
  obtain ⟨h_prec, h_quant, h_bnd⟩ := h_mem
  refine ⟨⟨h_prec, h_quant, h_bnd⟩, ?_, ?_, ?_⟩
  · -- |y| ≤ |x|: sign-split.
    rw [h_y_real]
    rw [show (c : ℝ) * (2 : ℝ) ^ e = (c : ℝ) * (2 : ℝ) ^ e from rfl]
    by_cases hx_nn : 0 ≤ x
    · -- x ≥ 0: c = ⌊s⌋, c · 2^e ≤ x, also c · 2^e ≥ 0.
      have h_c : c = ⌊x * (2 : ℝ) ^ (-e)⌋ := by rw [h_c_eq, if_pos hx_nn]
      have h_floor_le : (c : ℝ) ≤ x * (2 : ℝ) ^ (-e) := by rw [h_c]; exact Int.floor_le _
      have h_floor_nn : 0 ≤ c := by
        rw [h_c]; exact Int.floor_nonneg.mpr (mul_nonneg hx_nn (zpow_pos (by norm_num) _).le)
      have hy_nn : 0 ≤ (c : ℝ) * (2 : ℝ) ^ e :=
        mul_nonneg (by exact_mod_cast h_floor_nn) h_2e_pos.le
      rw [abs_of_nonneg hy_nn, abs_of_nonneg hx_nn, ← mul_zpow_neg_self x e]
      exact mul_le_mul_of_nonneg_right h_floor_le h_2e_pos.le
    · -- x < 0: c = ⌈s⌉, x ≤ c · 2^e ≤ 0.
      push Not at hx_nn
      have h_c : c = ⌈x * (2 : ℝ) ^ (-e)⌉ := by rw [h_c_eq, if_neg (not_le.mpr hx_nn)]
      have h_s_neg : x * (2 : ℝ) ^ (-e) < 0 :=
        mul_neg_of_neg_of_pos hx_nn (zpow_pos (by norm_num) _)
      have h_ceil_le : x * (2 : ℝ) ^ (-e) ≤ (c : ℝ) := by rw [h_c]; exact Int.le_ceil _
      have h_ceil_np : c ≤ 0 := by
        rw [h_c]
        exact Int.ceil_le.mpr (by push_cast; exact h_s_neg.le)
      have hy_np : (c : ℝ) * (2 : ℝ) ^ e ≤ 0 :=
        mul_nonpos_iff.mpr (Or.inr ⟨by exact_mod_cast h_ceil_np, h_2e_pos.le⟩)
      rw [abs_of_nonpos hy_np, abs_of_neg hx_nn]
      have hmul : x * (2 : ℝ) ^ (-e) * (2 : ℝ) ^ e ≤ (c : ℝ) * (2 : ℝ) ^ e :=
        mul_le_mul_of_nonneg_right h_ceil_le h_2e_pos.le
      rw [mul_zpow_neg_self] at hmul
      linarith
  · -- y · x ≥ 0: sign-split.
    rw [h_y_real]
    by_cases hx_nn : 0 ≤ x
    · -- x ≥ 0: c ≥ 0 (floor of nonneg), so c · 2^e · x ≥ 0.
      have h_c : c = ⌊x * (2 : ℝ) ^ (-e)⌋ := by rw [h_c_eq, if_pos hx_nn]
      have h_c_nn : 0 ≤ c := by
        rw [h_c]; exact Int.floor_nonneg.mpr (mul_nonneg hx_nn (zpow_pos (by norm_num) _).le)
      have h_y_nn : 0 ≤ (c : ℝ) * (2 : ℝ) ^ e :=
        mul_nonneg (by exact_mod_cast h_c_nn) h_2e_pos.le
      exact mul_nonneg h_y_nn hx_nn
    · -- x < 0: c ≤ 0 (ceil of nonpos), so c · 2^e ≤ 0 and x < 0, product ≥ 0.
      push Not at hx_nn
      have h_c : c = ⌈x * (2 : ℝ) ^ (-e)⌉ := by rw [h_c_eq, if_neg (not_le.mpr hx_nn)]
      have h_s_neg : x * (2 : ℝ) ^ (-e) < 0 :=
        mul_neg_of_neg_of_pos hx_nn (zpow_pos (by norm_num) _)
      have h_c_np : c ≤ 0 := by
        rw [h_c]
        exact Int.ceil_le.mpr (by push_cast; exact h_s_neg.le)
      have h_y_np : (c : ℝ) * (2 : ℝ) ^ e ≤ 0 :=
        mul_nonpos_iff.mpr (Or.inr ⟨by exact_mod_cast h_c_np, h_2e_pos.le⟩)
      exact mul_nonneg_iff.mpr (Or.inr ⟨h_y_np, hx_nn.le⟩)
  · -- minimality: sign-split, reduce to floor/ceil minimality.
    intro z hz_mem hz_abs_le hz_mul_x
    obtain ⟨hz_prec, hz_quant, _⟩ := hz_mem
    rw [h_y_real]
    by_cases hx_nn : 0 ≤ x
    · -- x ≥ 0: y = ⌊x · 2^(-e)⌋ · 2^e ≥ 0, z ≥ 0; reduce to `floor_minimality`.
      have h_c_int : c = ⌊x * (2 : ℝ) ^ (-e)⌋ := by
        rw [h_c_eq]; simp [if_pos hx_nn]
      have h_floor_nn : 0 ≤ ⌊x * (2 : ℝ) ^ (-e)⌋ :=
        Int.floor_nonneg.mpr (mul_nonneg hx_nn (zpow_pos (by norm_num) _).le)
      have hy_nn : 0 ≤ (c : ℝ) * (2 : ℝ) ^ e := by
        rw [show (c : ℝ) = (⌊x * (2 : ℝ) ^ (-e)⌋ : ℝ) from by exact_mod_cast h_c_int]
        exact mul_nonneg (by exact_mod_cast h_floor_nn) h_2e_pos.le
      have hz_nn : 0 ≤ (z : ℝ) := by
        rcases eq_or_lt_of_le hx_nn with hx_eq | hx_pos
        · have hx0 : x = 0 := hx_eq.symm
          rw [hx0, abs_zero] at hz_abs_le
          have : (z : ℝ) = 0 := abs_eq_zero.mp (le_antisymm hz_abs_le (abs_nonneg _))
          linarith
        · by_contra hz_neg
          push Not at hz_neg
          have : (z : ℝ) * x < 0 := mul_neg_of_neg_of_pos hz_neg hx_pos
          linarith
      have hz_le_x : (z : ℝ) ≤ x := by
        have h1 : |x| = x := abs_of_nonneg hx_nn
        have h2 : |(z : ℝ)| = z := abs_of_nonneg hz_nn
        linarith [hz_abs_le, h1, h2]
      rw [abs_of_nonneg hz_nn, abs_of_nonneg hy_nn]
      rw [show (c : ℝ) = (⌊x * (2 : ℝ) ^ (-e)⌋ : ℝ) from by exact_mod_cast h_c_int]
      exact floor_minimality F x hz_prec hz_quant hz_le_x
    · -- x < 0: y = ⌈x · 2^(-e)⌉ · 2^e ≤ 0, z ≤ 0; reduce to `ceil_minimality`.
      push Not at hx_nn
      have h_c_int : c = ⌈x * (2 : ℝ) ^ (-e)⌉ := by
        rw [h_c_eq]; simp [if_neg (not_le.mpr hx_nn)]
      have h_s_neg : x * (2 : ℝ) ^ (-e) < 0 :=
        mul_neg_of_neg_of_pos hx_nn (zpow_pos (by norm_num) _)
      have h_ceil_np : ⌈x * (2 : ℝ) ^ (-e)⌉ ≤ 0 :=
        Int.ceil_le.mpr (by push_cast; exact h_s_neg.le)
      have hy_np : (c : ℝ) * (2 : ℝ) ^ e ≤ 0 := by
        rw [show (c : ℝ) = (⌈x * (2 : ℝ) ^ (-e)⌉ : ℝ) from by exact_mod_cast h_c_int]
        exact mul_nonpos_iff.mpr (Or.inr ⟨by exact_mod_cast h_ceil_np, h_2e_pos.le⟩)
      have hz_np : (z : ℝ) ≤ 0 := by
        by_contra hz_pos
        push Not at hz_pos
        have : (z : ℝ) * x < 0 := mul_neg_of_pos_of_neg hz_pos hx_nn
        linarith
      have hx_le_z : x ≤ (z : ℝ) := by
        have h1 : |x| = -x := abs_of_neg hx_nn
        have h2 : |(z : ℝ)| = -z := abs_of_nonpos hz_np
        linarith [hz_abs_le, h1, h2]
      rw [abs_of_nonpos hz_np, abs_of_nonpos hy_np]
      rw [show (c : ℝ) = (⌈x * (2 : ℝ) ^ (-e)⌉ : ℝ) from by exact_mod_cast h_c_int]
      have := ceil_minimality F x hz_prec hz_quant hx_le_z
      linarith

theorem rndUnbounded_satisfies_awayZero (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .awayZero) :
    RoundsFinite F.unbounded .awayZero x (rndUnbounded F .awayZero x h) := by
  have h_rnd_eq : rndUnbounded F .awayZero x h =
      Dyadic.ofIntZpow (rndInt .awayZero x (F.canonicalExp x)) (F.canonicalExp x) := by
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.awayZero : RoundingMode) ≠ .toOdd)]
    rw [dif_neg (by decide : (RoundingMode.awayZero : RoundingMode) ≠ .nearest .toEven)]
  rw [h_rnd_eq]
  set e := F.canonicalExp x
  set c := rndInt .awayZero x e
  set y : Dyadic := Dyadic.ofIntZpow c e
  have h_y_real : (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ e := Dyadic.coe_ofIntZpow c e
  have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have h_c_eq : c = if 0 ≤ x then ⌈x * (2 : ℝ) ^ (-e)⌉ else ⌊x * (2 : ℝ) ^ (-e)⌋ := by
    change rndInt .awayZero x e = _
    rfl
  have h_c_bound : ∀ {p : ℕ+}, F.p = ((p : ℕ+) : WithTop ℕ+) →
      |c| ≤ (2 : ℤ) ^ (p : ℕ) := fun hp => by
    rw [h_c_eq]
    by_cases hx_nn : 0 ≤ x
    · rw [if_pos hx_nn]
      apply abs_ceil_le_of_abs_lt
      push_cast; exact floor_mantissa_lt hp
    · rw [if_neg hx_nn]
      apply abs_floor_le_of_abs_lt
      push_cast; exact floor_mantissa_lt hp
  have h_mem : y ∈ F.unbounded :=
    ofIntZpow_mem_unbounded F (fun hexp => F.exp_le_canonicalExp x hexp) h_c_bound
  obtain ⟨h_prec, h_quant, h_bnd⟩ := h_mem
  refine ⟨⟨h_prec, h_quant, h_bnd⟩, ?_, ?_, ?_⟩
  · -- |x| ≤ |y|: sign-split. RAZ rounds away from zero, so |y| ≥ |x|.
    rw [h_y_real]
    by_cases hx_nn : 0 ≤ x
    · -- x ≥ 0: c = ⌈s⌉, c · 2^e ≥ x ≥ 0.
      have h_c : c = ⌈x * (2 : ℝ) ^ (-e)⌉ := by rw [h_c_eq, if_pos hx_nn]
      have h_ceil_ge : x * (2 : ℝ) ^ (-e) ≤ (c : ℝ) := by rw [h_c]; exact Int.le_ceil _
      have h_ceil_nn : 0 ≤ c := by
        rw [h_c]; exact Int.ceil_nonneg (mul_nonneg hx_nn (zpow_pos (by norm_num) _).le)
      have hy_nn : 0 ≤ (c : ℝ) * (2 : ℝ) ^ e :=
        mul_nonneg (by exact_mod_cast h_ceil_nn) h_2e_pos.le
      rw [abs_of_nonneg hy_nn, abs_of_nonneg hx_nn, ← mul_zpow_neg_self x e]
      exact mul_le_mul_of_nonneg_right h_ceil_ge h_2e_pos.le
    · -- x < 0: c = ⌊s⌋, c · 2^e ≤ x < 0.
      push Not at hx_nn
      have h_c : c = ⌊x * (2 : ℝ) ^ (-e)⌋ := by rw [h_c_eq, if_neg (not_le.mpr hx_nn)]
      have h_s_neg : x * (2 : ℝ) ^ (-e) < 0 :=
        mul_neg_of_neg_of_pos hx_nn (zpow_pos (by norm_num) _)
      have h_floor_le : (c : ℝ) ≤ x * (2 : ℝ) ^ (-e) := by rw [h_c]; exact Int.floor_le _
      have h_c_neg : c < 0 := by
        rw [h_c]
        exact Int.floor_lt.mpr (by push_cast; exact h_s_neg)
      have hy_np : (c : ℝ) * (2 : ℝ) ^ e ≤ 0 :=
        mul_nonpos_iff.mpr (Or.inr ⟨by exact_mod_cast h_c_neg.le, h_2e_pos.le⟩)
      rw [abs_of_nonpos hy_np, abs_of_neg hx_nn]
      have hmul : (c : ℝ) * (2 : ℝ) ^ e ≤ x * (2 : ℝ) ^ (-e) * (2 : ℝ) ^ e :=
        mul_le_mul_of_nonneg_right h_floor_le h_2e_pos.le
      rw [mul_zpow_neg_self] at hmul
      linarith
  · -- y · x ≥ 0
    rw [h_y_real]
    by_cases hx_nn : 0 ≤ x
    · have h_c : c = ⌈x * (2 : ℝ) ^ (-e)⌉ := by rw [h_c_eq, if_pos hx_nn]
      have h_c_nn : 0 ≤ c := by
        rw [h_c]; exact Int.ceil_nonneg (mul_nonneg hx_nn (zpow_pos (by norm_num) _).le)
      have h_y_nn : 0 ≤ (c : ℝ) * (2 : ℝ) ^ e :=
        mul_nonneg (by exact_mod_cast h_c_nn) h_2e_pos.le
      exact mul_nonneg h_y_nn hx_nn
    · push Not at hx_nn
      have h_c : c = ⌊x * (2 : ℝ) ^ (-e)⌋ := by rw [h_c_eq, if_neg (not_le.mpr hx_nn)]
      have h_s_neg : x * (2 : ℝ) ^ (-e) < 0 :=
        mul_neg_of_neg_of_pos hx_nn (zpow_pos (by norm_num) _)
      have h_c_neg : c < 0 := by
        rw [h_c]
        exact Int.floor_lt.mpr (by push_cast; exact h_s_neg)
      have h_y_np : (c : ℝ) * (2 : ℝ) ^ e ≤ 0 :=
        mul_nonpos_iff.mpr (Or.inr ⟨by exact_mod_cast h_c_neg.le, h_2e_pos.le⟩)
      exact mul_nonneg_iff.mpr (Or.inr ⟨h_y_np, hx_nn.le⟩)
  · -- minimality: sign-split, reduce to ceil/floor minimality (mirror of `_toZero`).
    intro z hz_mem hz_abs_ge hz_mul_x
    obtain ⟨hz_prec, hz_quant, _⟩ := hz_mem
    rw [h_y_real]
    by_cases hx0 : x = 0
    · -- x = 0: c = ⌈0⌉ = 0, y = 0. Need |y| = 0 ≤ |z| (always true).
      have h_c_int : c = 0 := by
        subst hx0
        rw [h_c_eq]; simp
      rw [show (c : ℝ) = 0 from by exact_mod_cast h_c_int]
      simp [abs_nonneg]
    by_cases hx_nn : 0 ≤ x
    · -- 0 < x (since x ≠ 0): y = ⌈⌉ · 2^e ≥ 0, |x| ≤ |z| ⟹ x ≤ z; apply `ceil_minimality`.
      have hx_pos : 0 < x := lt_of_le_of_ne hx_nn (Ne.symm hx0)
      have h_c_int : c = ⌈x * (2 : ℝ) ^ (-e)⌉ := by
        rw [h_c_eq]; simp [if_pos hx_nn]
      have h_ceil_nn : 0 ≤ ⌈x * (2 : ℝ) ^ (-e)⌉ :=
        Int.ceil_nonneg (mul_nonneg hx_nn (zpow_pos (by norm_num) _).le)
      have hy_nn : 0 ≤ (c : ℝ) * (2 : ℝ) ^ e := by
        rw [show (c : ℝ) = (⌈x * (2 : ℝ) ^ (-e)⌉ : ℝ) from by exact_mod_cast h_c_int]
        exact mul_nonneg (by exact_mod_cast h_ceil_nn) h_2e_pos.le
      have hz_nn : 0 ≤ (z : ℝ) := by
        by_contra hz_neg
        push Not at hz_neg
        have : (z : ℝ) * x < 0 := mul_neg_of_neg_of_pos hz_neg hx_pos
        linarith
      have hx_le_z : x ≤ (z : ℝ) := by
        have h1 : |x| = x := abs_of_nonneg hx_nn
        have h2 : |(z : ℝ)| = z := abs_of_nonneg hz_nn
        linarith [hz_abs_ge, h1, h2]
      rw [abs_of_nonneg hy_nn, abs_of_nonneg hz_nn]
      rw [show (c : ℝ) = (⌈x * (2 : ℝ) ^ (-e)⌉ : ℝ) from by exact_mod_cast h_c_int]
      exact ceil_minimality F x hz_prec hz_quant hx_le_z
    · -- x < 0: y = ⌊⌋ · 2^e ≤ 0, |x| ≤ |z| ⟹ z ≤ x; apply `floor_minimality`.
      push Not at hx_nn
      have h_c_int : c = ⌊x * (2 : ℝ) ^ (-e)⌋ := by
        rw [h_c_eq]; simp [if_neg (not_le.mpr hx_nn)]
      have h_s_neg : x * (2 : ℝ) ^ (-e) < 0 :=
        mul_neg_of_neg_of_pos hx_nn (zpow_pos (by norm_num) _)
      have h_floor_neg : ⌊x * (2 : ℝ) ^ (-e)⌋ < 0 :=
        Int.floor_lt.mpr (by push_cast; exact h_s_neg)
      have hy_np : (c : ℝ) * (2 : ℝ) ^ e ≤ 0 := by
        rw [show (c : ℝ) = (⌊x * (2 : ℝ) ^ (-e)⌋ : ℝ) from by exact_mod_cast h_c_int]
        exact mul_nonpos_iff.mpr (Or.inr ⟨by exact_mod_cast h_floor_neg.le, h_2e_pos.le⟩)
      have hz_np : (z : ℝ) ≤ 0 := by
        by_contra hz_pos
        push Not at hz_pos
        have : (z : ℝ) * x < 0 := mul_neg_of_pos_of_neg hz_pos hx_nn
        linarith
      have hz_le_x : (z : ℝ) ≤ x := by
        have h1 : |x| = -x := abs_of_neg hx_nn
        have h2 : |(z : ℝ)| = -z := abs_of_nonpos hz_np
        linarith [hz_abs_ge, h1, h2]
      rw [abs_of_nonpos hy_np, abs_of_nonpos hz_np]
      rw [show (c : ℝ) = (⌊x * (2 : ℝ) ^ (-e)⌋ : ℝ) from by exact_mod_cast h_c_int]
      have := floor_minimality F x hz_prec hz_quant hz_le_x
      linarith


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
  set y' := rndUnbounded F .toZero x h
  have hy' : RoundsFinite F.unbounded .toZero x y' :=
    rndUnbounded_satisfies_toZero F x h
  obtain ⟨hy_mem, hy_bnd, hy_sign, hy_max⟩ := hy
  obtain ⟨hy'_mem, hy'_bnd, hy'_sign, hy'_max⟩ := hy'
  have h1 : |(y' : ℝ)| ≤ |(y : ℝ)| := hy_max y' hy'_mem hy'_bnd hy'_sign
  have h2 : |(y : ℝ)| ≤ |(y' : ℝ)| := hy'_max y hy_mem hy_bnd hy_sign
  have habs : |(y : ℝ)| = |(y' : ℝ)| := le_antisymm h2 h1
  apply Dyadic.ext_real
  rcases abs_eq_abs.mp habs with heq | hneg
  · exact heq
  · -- y = -y': combine the two `* x ≥ 0` constraints to force y'·x = 0.
    have h_prod_le : (y' : ℝ) * x + (y' : ℝ) * x ≤ 0 := by
      have h_y : (y : ℝ) * x = -((y' : ℝ) * x) := by rw [hneg]; ring
      linarith [hy_sign, hy'_sign, h_y]
    have h_prod_zero : (y' : ℝ) * x = 0 := by linarith [hy'_sign]
    rcases mul_eq_zero.mp h_prod_zero with h' | hx0
    · rw [hneg, h']; ring
    · -- x = 0: the `|y| ≤ |x|` clause directly forces y = y' = 0.
      have hy0 : (y : ℝ) = 0 := by
        have : |(y : ℝ)| ≤ 0 := by rw [hx0] at hy_bnd; simpa using hy_bnd
        exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
      have hy'0 : (y' : ℝ) = 0 := by
        have : |(y' : ℝ)| ≤ 0 := by rw [hx0] at hy'_bnd; simpa using hy'_bnd
        exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
      rw [hy0, hy'0]

theorem rndUnbounded_unique_awayZero (F : FiniteFormat) (x : ℝ)
    (h : ¬ F.IsUndefined .awayZero) {y : Dyadic}
    (hy : RoundsFinite F.unbounded .awayZero x y) :
    y = rndUnbounded F .awayZero x h := by
  set y' := rndUnbounded F .awayZero x h
  have hy' : RoundsFinite F.unbounded .awayZero x y' :=
    rndUnbounded_satisfies_awayZero F x h
  obtain ⟨hy_mem, hy_bnd, hy_sign, hy_min⟩ := hy
  obtain ⟨hy'_mem, hy'_bnd, hy'_sign, hy'_min⟩ := hy'
  have h1 : |(y : ℝ)| ≤ |(y' : ℝ)| := hy_min y' hy'_mem hy'_bnd hy'_sign
  have h2 : |(y' : ℝ)| ≤ |(y : ℝ)| := hy'_min y hy_mem hy_bnd hy_sign
  have habs : |(y : ℝ)| = |(y' : ℝ)| := le_antisymm h1 h2
  apply Dyadic.ext_real
  rcases abs_eq_abs.mp habs with heq | hneg
  · exact heq
  · have h_prod_zero : (y' : ℝ) * x = 0 := by
      have h_y : (y : ℝ) * x = -((y' : ℝ) * x) := by rw [hneg]; ring
      linarith [hy_sign, hy'_sign, h_y]
    rcases mul_eq_zero.mp h_prod_zero with h' | hx0
    · rw [hneg, h']; ring
    · -- x = 0: RAZ's bound clause is vacuous; min-clause via `0 ∈ F` pins y = y' = 0.
      have h_zero_mem : (0 : Dyadic) ∈ F.unbounded := FiniteFormat.zero_mem F.unbounded
      have h_zero_bnd : |x| ≤ |((0 : Dyadic) : ℝ)| := by rw [hx0]; simp
      have h_zero_sign : ((0 : Dyadic) : ℝ) * x ≥ 0 := by simp
      have hy_le_0 : |(y : ℝ)| ≤ |((0 : Dyadic) : ℝ)| :=
        hy_min 0 h_zero_mem h_zero_bnd h_zero_sign
      have hy'_le_0 : |(y' : ℝ)| ≤ |((0 : Dyadic) : ℝ)| :=
        hy'_min 0 h_zero_mem h_zero_bnd h_zero_sign
      have hy0 : (y : ℝ) = 0 := by
        have : |(y : ℝ)| ≤ 0 := by simpa using hy_le_0
        exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
      have hy'0 : (y' : ℝ) = 0 := by
        have : |(y' : ℝ)| ≤ 0 := by simpa using hy'_le_0
        exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
      linarith


end Mpfx
