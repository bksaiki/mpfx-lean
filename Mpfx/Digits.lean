import Mpfx.Containment

/-!
# Digit-count and parity-transfer lemmas (Lemma 5.3)

The headline is **Lemma 5.3** — RTO digit-padding preserves representability —
realized here as a parity-transfer chain across a subformat `F₁ ⊆ F₂`:

* `FiniteFormat.numDigits_le_one_of_p_one`,
  `ParityFormat.precisionAtMost_not_IsOdd` — the Lemma 5.3 *corollary*: a
  value with precision `≤ w` can't be `IsOdd` at an effective precision `> w`.
* `numDigits_eq_of_subset_of_isOdd` (+ its hard `≤` core
  `numDigits_eq_of_subset_of_isOdd_aux`) — for an `IsOdd F₂` value `y ∈ F₁`,
  the effective precisions in `F₁` and `F₂` agree.
* `IsOdd.transfer_of_numDigits_eq` — transfers `IsOdd` across the subformat
  once the effective precisions are known equal.
* **`IsOdd.transfer_of_subset`** — the capstone **Lemma 5.3**: `F₁ ⊆ F₂`,
  `2 ≤ F₂.p`, `y ∈ F₁`, `F₂.IsOdd y` ⟹ `F₁.IsOdd y`. This is the form the
  RTO-composition double-rounding rules (`rndRTO_RTO`, …) consume.

Proved over the `ℚ` substrate, with `ℝ` bridges only where `Int.log` /
`numDigits` require them.
-/

namespace Mpfx

/-- `F.numDigits x ≤ 1` whenever `F.p = 1`. When the precision is a single
binary digit, the format rounds every value to `±2^e`, so its effective
digit count never exceeds one. -/
theorem FiniteFormat.numDigits_le_one_of_p_one {F : FiniteFormat}
    (hp1 : F.p = ((1 : ℕ+) : WithTop ℕ+)) (x : ℝ) :
    F.numDigits x ≤ 1 := by
  unfold FiniteFormat.numDigits
  by_cases hx : x = 0
  · simp [hx]
  · simp only [hx, ↓reduceIte]
    -- `F.p = 1`, so only the `(p, ⊥)` and `(p, e')` branches apply.
    cases hexp : F.exp with
    | bot =>
      rw [hp1]
      change ((1 : ℕ) : ℤ) ≤ 1
      norm_num
    | coe e' =>
      rw [hp1]
      change min ((1 : ℕ) : ℤ) (Int.log 2 |x| - e' + 1) ≤ 1
      exact min_le_left _ _

/-- **Lemma 5.3 corollary** (format-parameterized form): If `y` has precision
at most `w` and the rounding precision in `F` (= `numDigits F y`) strictly
exceeds `w`, then `y` cannot be `IsOdd F`. -/
theorem ParityFormat.precisionAtMost_not_IsOdd {F : ParityFormat} {w : ℕ+} {y : Dyadic}
    (hgt : ((w : ℕ) : ℤ) < F.toFiniteFormat.numDigits (y : ℝ))
    (hprec : Dyadic.precisionAtMost ((w : ℕ+) : WithTop ℕ+) y) :
    ¬ F.IsOdd y := by
  intro hodd
  obtain ⟨c₁, e₁, ⟨hy_eq₁, hlow, _hhigh⟩, hp_check⟩ := hodd
  set p_y : ℕ := (F.toFiniteFormat.numDigits (y : ℝ)).toNat with hp_y_def
  have h_nd_pos : 0 ≤ F.toFiniteFormat.numDigits (y : ℝ) := by
    have : (0 : ℤ) ≤ ((w : ℕ) : ℤ) := by positivity
    linarith
  have h_pyZ : (p_y : ℤ) = F.toFiniteFormat.numDigits (y : ℝ) := Int.toNat_of_nonneg h_nd_pos
  have hp_y_ge : p_y ≥ (w : ℕ) + 1 := by
    have : (p_y : ℤ) ≥ ((w : ℕ) : ℤ) + 1 := by rw [h_pyZ]; linarith
    exact_mod_cast this
  -- Show `F.p ≠ 1` (else `numDigits F y ≤ 1`, but `numDigits ≥ w + 1 ≥ 2`).
  have hFp_ne_1 : F.p ≠ ((1 : ℕ+) : WithTop ℕ+) := by
    intro hFp1
    have h_le := F.toFiniteFormat.numDigits_le_one_of_p_one hFp1 (y : ℝ)
    have h1 : (p_y : ℤ) ≤ 1 := by rw [h_pyZ]; exact h_le
    have h2 : p_y ≤ 1 := by exact_mod_cast h1
    have hw_pos : 1 ≤ (w : ℕ) := w.pos
    omega
  rw [if_neg hFp_ne_1] at hp_check
  have hc₁_odd : Odd c₁ := hp_check
  set k : ℕ := p_y - (w : ℕ) with hk_def
  have hpyw : p_y = (w : ℕ) + k := by omega
  -- Unpack the precision witness for `y` (over ℚ).
  rw [Dyadic.precisionAtMost_coe] at hprec
  obtain ⟨c₂, e₂, hy_eq₂, hc₂_low⟩ := hprec
  have heq_rat : (c₁ : ℚ) * (2 : ℚ) ^ e₁ = (c₂ : ℚ) * (2 : ℚ) ^ e₂ := by
    rw [← hy_eq₁]; exact hy_eq₂
  have h2ne : (2 : ℚ) ≠ 0 := two_ne_zero
  have h2pos : (0 : ℚ) < 2 := by norm_num
  rcases lt_or_ge e₁ e₂ with he | he
  · -- `e₁ < e₂`: `c₁ = c₂ · 2^(e₂-e₁)` is even, contradicting `Odd c₁`.
    have h_nat : ((e₂ - e₁).toNat : ℤ) = e₂ - e₁ := Int.toNat_of_nonneg (by omega)
    have heq_int : c₁ = c₂ * 2 ^ (e₂ - e₁).toNat := by
      have h_rat : (c₁ : ℚ) = (c₂ : ℚ) * (2 : ℚ) ^ (e₂ - e₁).toNat := by
        rw [show ((2 : ℚ) ^ (e₂ - e₁).toNat : ℚ) = (2 : ℚ) ^ ((e₂ - e₁).toNat : ℤ) from
            (zpow_natCast _ _).symm, h_nat]
        have h_step : (c₂ : ℚ) * (2 : ℚ) ^ (e₂ - e₁) * (2 : ℚ) ^ e₁
            = (c₁ : ℚ) * (2 : ℚ) ^ e₁ := by
          rw [mul_assoc, ← zpow_add₀ h2ne, show e₂ - e₁ + e₁ = e₂ from by ring]
          exact heq_rat.symm
        have h2e₁_pos : (0 : ℚ) < (2 : ℚ) ^ e₁ := zpow_pos h2pos _
        exact (mul_right_cancel₀ (ne_of_gt h2e₁_pos) h_step).symm
      exact_mod_cast h_rat
    have h_even : Even c₁ := by
      rw [heq_int,
          show (e₂ - e₁).toNat = ((e₂ - e₁).toNat - 1) + 1 from by omega, pow_succ]
      exact ⟨c₂ * 2 ^ ((e₂ - e₁).toNat - 1), by ring⟩
    exact (Int.not_even_iff_odd.mpr hc₁_odd) h_even
  · -- `e₁ ≥ e₂`: `|c₂| = |c₁| · 2^(e₁-e₂) ≥ 2^(p_y-1) ≥ 2^w`, contradicting `|c₂| < 2^w`.
    have h_nat : ((e₁ - e₂).toNat : ℤ) = e₁ - e₂ := Int.toNat_of_nonneg (by omega)
    have heq_int : c₂ = c₁ * 2 ^ (e₁ - e₂).toNat := by
      have h_rat : (c₂ : ℚ) = (c₁ : ℚ) * (2 : ℚ) ^ (e₁ - e₂).toNat := by
        rw [show ((2 : ℚ) ^ (e₁ - e₂).toNat : ℚ) = (2 : ℚ) ^ ((e₁ - e₂).toNat : ℤ) from
            (zpow_natCast _ _).symm, h_nat]
        have h_step : (c₁ : ℚ) * (2 : ℚ) ^ (e₁ - e₂) * (2 : ℚ) ^ e₂
            = (c₂ : ℚ) * (2 : ℚ) ^ e₂ := by
          rw [mul_assoc, ← zpow_add₀ h2ne, show e₁ - e₂ + e₂ = e₁ from by ring]
          exact heq_rat
        have h2e₂_pos : (0 : ℚ) < (2 : ℚ) ^ e₂ := zpow_pos h2pos _
        exact (mul_right_cancel₀ (ne_of_gt h2e₂_pos) h_step).symm
      exact_mod_cast h_rat
    have h_abs : |c₂| = |c₁| * 2 ^ (e₁ - e₂).toNat := by
      rw [heq_int, abs_mul, abs_pow]; congr 1
    -- `2^(p_y - 1) ≤ |c₁|` (the low bound of `IsRepresentableAtP`).
    have hlow' : (2 : ℤ) ^ (p_y - 1) ≤ |c₁| := hlow
    have hpow_le : (2 : ℤ) ^ (w : ℕ) ≤ (2 : ℤ) ^ (p_y - 1) := by
      apply pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
      have hw_pos : 1 ≤ (w : ℕ) := w.pos
      omega
    have h2pow_pos : (0 : ℤ) < 2 ^ (e₁ - e₂).toNat := by positivity
    have h_one_le : (1 : ℤ) ≤ 2 ^ (e₁ - e₂).toNat := h2pow_pos
    have h_chain : (2 : ℤ) ^ (w : ℕ) ≤ |c₂| := by
      calc (2 : ℤ) ^ (w : ℕ)
          ≤ (2 : ℤ) ^ (p_y - 1) := hpow_le
        _ ≤ |c₁| := hlow'
        _ = |c₁| * 1 := (mul_one _).symm
        _ ≤ |c₁| * 2 ^ (e₁ - e₂).toNat :=
            mul_le_mul_of_nonneg_left h_one_le (abs_nonneg _)
        _ = |c₂| := h_abs.symm
    exact absurd (lt_of_le_of_lt h_chain hc₂_low) (lt_irrefl _)

/-- The `≤` direction of `numDigits_eq_of_subset_of_isOdd`, and the hardest
proof in the file: there is no `IsOdd F₂` value `y ∈ F₁` (with `F₁ ⊆ F₂`,
`2 ≤ F₂.p`) whose `F₂`-digit count is strictly below its `F₁`-digit count.
Proof: construct the finer-grid witness `y'' = ofIntZpow (2c − sign c) (e − 1)`
and show `y'' ∈ F₁` but `y'' ∉ F₂`, contradicting `F₁ ⊆ F₂`. -/
private lemma numDigits_eq_of_subset_of_isOdd_aux
    {F₁ : FiniteFormat} {F₂ : ParityFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ+) : WithTop ℕ+) ≤ F₂.p)
    {y : Dyadic} (hyF₁ : y ∈ F₁) (hodd : F₂.IsOdd y)
    (h_lt : F₂.toFiniteFormat.numDigits (y : ℝ) < F₁.numDigits (y : ℝ)) :
    False := by
  have h_F₂_pos : 0 < F₂.toFiniteFormat.numDigits (y : ℝ) := hodd.numDigits_pos
  -- `F₂.p ≠ 1` from `2 ≤ F₂.p`.
  have hF₂_ne_1 : F₂.p ≠ ((1 : ℕ+) : WithTop ℕ+) := by
    intro h
    rw [h] at hp_F₂
    have : ((2 : ℕ+) : ℕ) ≤ ((1 : ℕ+) : ℕ) := by exact_mod_cast hp_F₂
    simp at this
  obtain ⟨c, e, ⟨hy_eq, hc_low, hc_high⟩, hp_check⟩ := hodd
  rw [if_neg hF₂_ne_1] at hp_check
  have hc_odd : Odd c := hp_check
  -- `p₂ := (numDigits F₂ y).toNat` is the precision used in `IsRepresentableAtP`.
  set p₂ : ℕ := (F₂.toFiniteFormat.numDigits (y : ℝ)).toNat with hp₂_def
  have hp₂_eq : (p₂ : ℤ) = F₂.toFiniteFormat.numDigits (y : ℝ) :=
    Int.toNat_of_nonneg (le_of_lt h_F₂_pos)
  have hp₂_pos : 1 ≤ p₂ := by
    have : (0 : ℤ) < F₂.toFiniteFormat.numDigits (y : ℝ) := h_F₂_pos
    rw [← hp₂_eq] at this; exact_mod_cast this
  -- The `IsRepresentableAtP` bounds (`hc_low`/`hc_high`) are stated at `p₂`.
  have hc_low : (2 : ℤ) ^ (p₂ - 1) ≤ |c| := hc_low
  have hc_high : |c| < (2 : ℤ) ^ p₂ := hc_high
  have hc_ne : c ≠ 0 := by
    intro h; rw [h, abs_zero] at hc_low
    have : (1 : ℤ) ≤ (2 : ℤ) ^ (p₂ - 1) := one_le_pow₀ (by norm_num)
    linarith
  -- A real-valued representation of `y` from the ℚ-valued `hy_eq`.
  have hy_real : ((y : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ) ^ e := by
    rw [Dyadic.coe_real_eq_ratCast, hy_eq]; push_cast; ring
  -- Define y'' = Dyadic.ofIntZpow c'' (e - 1) where c'' = 2c - sign(c).
  set c'' : ℤ := 2 * c - (if 0 < c then 1 else -1) with hc''_def
  have hc''_odd : Odd c'' := by
    rcases lt_or_gt_of_ne hc_ne with h | h
    · simp only [hc''_def, if_neg (not_lt.mpr h.le)]
      exact ⟨c, by ring⟩
    · simp only [hc''_def, if_pos h]
      exact ⟨c - 1, by ring⟩
  have hc''_abs : |c''| = 2 * |c| - 1 := by
    rcases lt_or_gt_of_ne hc_ne with h | h
    · simp only [hc''_def, if_neg (not_lt.mpr h.le)]
      have hc_neg : c < 0 := h
      have h1 : 2 * c + 1 < 0 := by linarith
      rw [show (2 * c - -1 : ℤ) = 2 * c + 1 from by ring,
          abs_of_neg h1, abs_of_neg hc_neg]
      linarith
    · simp only [hc''_def, if_pos h]
      have hc_pos : c > 0 := h
      have h1 : 2 * c - 1 > 0 := by linarith
      rw [abs_of_pos h1, abs_of_pos hc_pos]
  have hc''_low : (2 : ℤ) ^ p₂ - 1 ≤ |c''| := by
    rw [hc''_abs, Int.two_pow_succ_pred hp₂_pos]
    linarith
  have hc''_high : |c''| < (2 : ℤ) ^ (p₂ + 1) := by
    rw [hc''_abs, Int.two_pow_succ_pred (by omega : 1 ≤ p₂ + 1)]
    have : (p₂ + 1 - 1 : ℕ) = p₂ := by omega
    rw [this]
    linarith
  set y'' : Dyadic := Dyadic.ofIntZpow c'' (e - 1) with hy''_def
  have hy''_real : ((y'' : Dyadic) : ℝ) = (c'' : ℝ) * (2 : ℝ) ^ (e - 1) :=
    Dyadic.coe_ofIntZpow c'' (e - 1)
  have h2real_pos : (0 : ℝ) < 2 := by norm_num
  have h2real_ne : (2 : ℝ) ≠ 0 := by norm_num
  have habs_y_eq : |((y : Dyadic) : ℝ)| = (|c| : ℝ) * (2 : ℝ) ^ e := by
    rw [hy_real, abs_mul_two_zpow]
  have habs_y''_eq : |((y'' : Dyadic) : ℝ)| = (|c''| : ℝ) * (2 : ℝ) ^ (e - 1) := by
    rw [hy''_real, abs_mul_two_zpow]
  have habs_y''_lt_y : |((y'' : Dyadic) : ℝ)| < |((y : Dyadic) : ℝ)| := by
    rw [habs_y_eq, habs_y''_eq]
    have h2e_pos : (0 : ℝ) < (2 : ℝ) ^ (e - 1) := zpow_pos h2real_pos _
    have habs_split : (2 : ℝ) ^ e = 2 * (2 : ℝ) ^ (e - 1) := by
      conv_lhs => rw [show e = (e - 1) + 1 from by ring]
      rw [zpow_add₀ h2real_ne, zpow_one]; ring
    rw [habs_split]
    have h_cabs_pos : (0 : ℝ) < (|c| : ℝ) := by exact_mod_cast (abs_pos.mpr hc_ne)
    have hcc : (|c''| : ℝ) = 2 * (|c| : ℝ) - 1 := by
      have : (|c''| : ℤ) = 2 * |c| - 1 := hc''_abs
      exact_mod_cast this
    rw [hcc]
    have h_cabs_ge : (1 : ℝ) ≤ (|c| : ℝ) := by
      have : (1 : ℤ) ≤ |c| := by
        rcases lt_or_gt_of_ne hc_ne with h | h
        · exact Int.one_le_abs (Int.ne_of_lt h)
        · exact Int.one_le_abs (Int.ne_of_gt h)
      exact_mod_cast this
    nlinarith [h2e_pos]
  have hy_ne_zero : ((y : Dyadic) : ℝ) ≠ 0 := by
    intro h
    rw [h, abs_zero] at habs_y_eq
    have hp : (0 : ℝ) < (|c| : ℝ) := by exact_mod_cast (abs_pos.mpr hc_ne)
    have h2 : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos h2real_pos _
    have h_prod : (|c| : ℝ) * (2 : ℝ) ^ e = 0 := habs_y_eq.symm
    have hp_ne : (|c| : ℝ) ≠ 0 := ne_of_gt hp
    have h2_ne : (2 : ℝ) ^ e ≠ 0 := ne_of_gt h2
    exact hp_ne ((mul_eq_zero.mp h_prod).resolve_right h2_ne)
  have habs_y_pos : 0 < |((y : Dyadic) : ℝ)| := abs_pos.mpr hy_ne_zero
  have hlog2_nat : (1 : ℕ) < 2 := by norm_num
  have h_cast_pow : ∀ k : ℕ, ((2 : ℤ) ^ k : ℝ) = (2 : ℝ) ^ (k : ℤ) := by
    intro k
    rw [zpow_natCast]
    push_cast; rfl
  have h_log_y_lo : (2 : ℝ) ^ ((p₂ - 1 : ℤ) + e) ≤ |((y : Dyadic) : ℝ)| := by
    rw [habs_y_eq, zpow_add₀ h2real_ne]
    apply mul_le_mul_of_nonneg_right _ (le_of_lt (zpow_pos h2real_pos _))
    have h_cast_low : ((2 : ℤ) ^ (p₂ - 1) : ℝ) ≤ (|c| : ℝ) := by
      exact_mod_cast hc_low
    have h_cast_low_zp : (2 : ℝ) ^ ((p₂ - 1 : ℕ) : ℤ) = ((2 : ℤ) ^ (p₂ - 1) : ℝ) :=
      (h_cast_pow (p₂ - 1)).symm
    have h_eq : (p₂ - 1 : ℤ) = ((p₂ - 1 : ℕ) : ℤ) := by omega
    rw [h_eq, h_cast_low_zp]
    exact h_cast_low
  have h_log_y_hi : |((y : Dyadic) : ℝ)| < (2 : ℝ) ^ ((p₂ : ℤ) + e) := by
    rw [habs_y_eq, zpow_add₀ h2real_ne]
    apply mul_lt_mul_of_pos_right _ (zpow_pos h2real_pos _)
    have h_cast_high : (|c| : ℝ) < ((2 : ℤ) ^ p₂ : ℝ) := by
      exact_mod_cast hc_high
    have h_cast_zp : (2 : ℝ) ^ ((p₂ : ℕ) : ℤ) = ((2 : ℤ) ^ p₂ : ℝ) :=
      (h_cast_pow p₂).symm
    have h_eq : (p₂ : ℤ) = ((p₂ : ℕ) : ℤ) := rfl
    rw [h_eq, h_cast_zp]; exact h_cast_high
  have h_log_y_eq : Int.log 2 |((y : Dyadic) : ℝ)| = (p₂ - 1 : ℤ) + e := by
    apply le_antisymm
    · have : Int.log 2 |((y : Dyadic) : ℝ)| < (p₂ - 1 : ℤ) + e + 1 :=
        (Int.lt_zpow_iff_log_lt hlog2_nat habs_y_pos).mp
          (by rw [show (p₂ - 1 : ℤ) + e + 1 = (p₂ : ℤ) + e from by omega]
              exact h_log_y_hi)
      omega
    · exact (Int.zpow_le_iff_le_log hlog2_nat habs_y_pos).mp h_log_y_lo
  -- Step 1: Show y'' ∈ F₁.
  have hy''_F₁ : y'' ∈ F₁ := by
    refine ⟨?_, ?_, ?_⟩
    · cases hp1 : F₁.p with
      | top => trivial
      | coe n =>
        rw [Dyadic.precisionAtMost_coe]
        refine ⟨c'', e - 1, rfl, ?_⟩
        have h_le_n : F₁.numDigits ((y : Dyadic) : ℝ) ≤ ((n : ℕ) : ℤ) := by
          cases hexp : F₁.exp with
          | bot =>
            rw [F₁.numDigits_coe_bot hy_ne_zero hp1 hexp]
          | coe e' =>
            rw [F₁.numDigits_coe_coe hy_ne_zero hp1 hexp]
            exact min_le_left _ _
        have hp₂_lt_n : (p₂ : ℤ) < ((n : ℕ) : ℤ) := by
          rw [hp₂_eq]; exact lt_of_lt_of_le h_lt h_le_n
        have hp₂_lt_n_nat : p₂ + 1 ≤ (n : ℕ) := by
          exact_mod_cast (by omega : (p₂ : ℤ) + 1 ≤ ((n : ℕ) : ℤ))
        calc |c''|
            < (2 : ℤ) ^ (p₂ + 1) := hc''_high
          _ ≤ (2 : ℤ) ^ (n : ℕ) :=
              pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hp₂_lt_n_nat
    · cases hexp : F₁.exp with
      | bot => trivial
      | coe e₁ =>
        rw [Dyadic.quantumAtLeast_coe]
        have h_e_gt_e₁ : e₁ < e := by
          have h_inner_gt : Int.log 2 |((y : Dyadic) : ℝ)| - e₁ + 1 > (p₂ : ℤ) := by
            have h_F₁_lt : (p₂ : ℤ) < F₁.numDigits ((y : Dyadic) : ℝ) := by
              rw [hp₂_eq]; exact h_lt
            cases hp1 : F₁.p with
            | top =>
              rw [F₁.numDigits_top_coe hy_ne_zero hexp hp1] at h_F₁_lt
              exact h_F₁_lt
            | coe n =>
              rw [F₁.numDigits_coe_coe hy_ne_zero hp1 hexp] at h_F₁_lt
              exact lt_of_lt_of_le h_F₁_lt (min_le_right _ _)
          rw [h_log_y_eq] at h_inner_gt
          omega
        have h_diff_nn : ((e - 1 - e₁).toNat : ℤ) = e - 1 - e₁ :=
          Int.toNat_of_nonneg (by omega)
        refine ⟨c'' * 2 ^ (e - 1 - e₁).toNat, ?_⟩
        rw [Dyadic.coe_rat_ofIntZpow]
        have h_pow_eq : (2 : ℚ) ^ (e - 1) =
            (2 : ℚ) ^ ((e - 1 - e₁).toNat : ℤ) * (2 : ℚ) ^ e₁ := by
          rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), h_diff_nn]
          congr 1; ring
        rw [h_pow_eq, zpow_natCast]
        push_cast
        ring
    · have hyF₁_bnd := hyF₁.2.2
      cases hb : F₁.b with
      | top => trivial
      | coe b =>
        rw [hb] at hyF₁_bnd
        change |((y'' : Dyadic) : ℚ)| ≤ ((b.val : Dyadic) : ℚ)
        have hyF₁_bnd' : |((y : Dyadic) : ℚ)| ≤ ((b.val : Dyadic) : ℚ) := hyF₁_bnd
        -- Bridge `|y''| < |y|` (ℝ) to ℚ.
        have habs_q : |((y'' : Dyadic) : ℚ)| < |((y : Dyadic) : ℚ)| := by
          have hh := habs_y''_lt_y
          rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast,
              ← Rat.cast_abs, ← Rat.cast_abs] at hh
          exact_mod_cast hh
        linarith
  -- For p₂ ≥ 2 with c odd: |c| ≥ 2^(p₂-1) + 1.
  have hc_low_strict : p₂ ≥ 2 → (2 : ℤ) ^ (p₂ - 1) + 1 ≤ |c| := by
    intro hp₂_ge_2
    have h_even : Even ((2 : ℤ) ^ (p₂ - 1)) := by
      refine ⟨(2 : ℤ) ^ (p₂ - 2), ?_⟩
      rw [show (p₂ - 1 : ℕ) = (p₂ - 2) + 1 from by omega, pow_succ]; ring
    have h_abs_odd : Odd |c| := Odd.abs hc_odd
    by_contra h_le
    push Not at h_le
    have h_eq : |c| = (2 : ℤ) ^ (p₂ - 1) := by linarith
    rw [h_eq] at h_abs_odd
    exact (Int.not_odd_iff_even.mpr h_even) h_abs_odd
  -- Step 2: Show y'' ∉ F₂.
  -- Helper: any integer rep (c''', e''') of y'' has e''' ≤ e - 1.
  have h_int_rep_le : ∀ (c''' : ℤ) (e''' : ℤ),
      ((y'' : Dyadic) : ℝ) = (c''' : ℝ) * (2 : ℝ) ^ e''' → e''' ≤ e - 1 := by
    intro c''' e''' h_eq
    by_contra h_gt
    push Not at h_gt
    have h_diff_pos : 0 < e''' - (e - 1) := by omega
    have h_diff_nat : ((e''' - (e - 1)).toNat : ℤ) = e''' - (e - 1) :=
      Int.toNat_of_nonneg (le_of_lt h_diff_pos)
    have h_c''_eq : (c'' : ℝ) = (c''' : ℝ) * (2 : ℝ) ^ (e''' - (e - 1)) := by
      have h2eml_pos : (0 : ℝ) < (2 : ℝ) ^ (e - 1) := zpow_pos h2real_pos _
      have hsplit : (2 : ℝ) ^ e''' =
          (2 : ℝ) ^ (e''' - (e - 1)) * (2 : ℝ) ^ (e - 1) := by
        rw [← zpow_add₀ h2real_ne]; congr 1; ring
      rw [hy''_real] at h_eq
      have key : (c'' : ℝ) * (2 : ℝ) ^ (e - 1) =
          ((c''' : ℝ) * (2 : ℝ) ^ (e''' - (e - 1))) * (2 : ℝ) ^ (e - 1) := by
        rw [h_eq, hsplit]; ring
      exact mul_right_cancel₀ (ne_of_gt h2eml_pos) key
    rw [show (2 : ℝ) ^ (e''' - (e - 1)) =
        (2 : ℝ) ^ ((e''' - (e - 1)).toNat : ℤ) from by rw [h_diff_nat],
        zpow_natCast] at h_c''_eq
    have h_c''_int : c'' = c''' * 2 ^ (e''' - (e - 1)).toNat := by
      have : ((c''' * 2 ^ (e''' - (e - 1)).toNat : ℤ) : ℝ) = (c'' : ℝ) := by
        push_cast; linarith [h_c''_eq]
      exact_mod_cast this.symm
    have h_pow_ge : 1 ≤ (e''' - (e - 1)).toNat := by
      have : ((e''' - (e - 1)).toNat : ℤ) ≥ 1 := by rw [h_diff_nat]; omega
      exact_mod_cast this
    have h_pow_split : (2 : ℤ) ^ (e''' - (e - 1)).toNat =
        2 * (2 : ℤ) ^ ((e''' - (e - 1)).toNat - 1) := Int.two_pow_succ_pred h_pow_ge
    have hc''_even : Even c'' := by
      rw [h_c''_int, h_pow_split]
      exact ⟨c''' * (2 : ℤ) ^ ((e''' - (e - 1)).toNat - 1), by ring⟩
    exact (Int.not_odd_iff_even.mpr hc''_even) hc''_odd
  -- Helper: |c'''| ≥ |c''| from any integer rep.
  have h_int_rep_abs : ∀ (c''' : ℤ) (e''' : ℤ),
      ((y'' : Dyadic) : ℝ) = (c''' : ℝ) * (2 : ℝ) ^ e''' → |c''| ≤ |c'''| := by
    intro c''' e''' h_eq
    have h_e_le := h_int_rep_le c''' e''' h_eq
    have h_diff_nn : ((e - 1 - e''').toNat : ℤ) = e - 1 - e''' :=
      Int.toNat_of_nonneg (by omega)
    have h_c'''_eq : c''' = c'' * 2 ^ (e - 1 - e''').toNat := by
      have h2_pos : (0 : ℝ) < (2 : ℝ) ^ e''' := zpow_pos h2real_pos _
      rw [hy''_real] at h_eq
      have hsplit : (2 : ℝ) ^ (e - 1) =
          (2 : ℝ) ^ (e - 1 - e''') * (2 : ℝ) ^ e''' := by
        rw [← zpow_add₀ h2real_ne]; congr 1; ring
      have key : ((c'' : ℝ) * (2 : ℝ) ^ (e - 1 - e''')) * (2 : ℝ) ^ e''' =
          (c''' : ℝ) * (2 : ℝ) ^ e''' := by
        rw [show ((c'' : ℝ) * (2 : ℝ) ^ (e - 1 - e''')) * (2 : ℝ) ^ e''' =
            (c'' : ℝ) * ((2 : ℝ) ^ (e - 1 - e''') * (2 : ℝ) ^ e''') from by ring]
        rw [← hsplit]; exact h_eq
      have h_real : (c'' : ℝ) * (2 : ℝ) ^ (e - 1 - e''') = (c''' : ℝ) :=
        mul_right_cancel₀ (ne_of_gt h2_pos) key
      rw [show (2 : ℝ) ^ (e - 1 - e''') =
          (2 : ℝ) ^ ((e - 1 - e''').toNat : ℤ) from by rw [h_diff_nn],
          zpow_natCast] at h_real
      have : ((c'' * 2 ^ (e - 1 - e''').toNat : ℤ) : ℝ) = (c''' : ℝ) := by
        push_cast; linarith [h_real]
      exact_mod_cast this.symm
    rw [h_c'''_eq, abs_mul, abs_pow]
    have h2_abs : |(2 : ℤ)| = 2 := by decide
    rw [h2_abs]
    have h_pow_pos : (1 : ℤ) ≤ 2 ^ (e - 1 - e''').toNat := one_le_pow₀ (by norm_num)
    have h_abs_nn : (0 : ℤ) ≤ |c''| := abs_nonneg _
    nlinarith
  -- Bridge: a ℚ-valued rep of `y''` gives an ℝ-valued rep.
  have ratrep_to_realrep : ∀ (c''' e''' : ℤ),
      ((y'' : Dyadic) : ℚ) = (c''' : ℚ) * (2 : ℚ) ^ e''' →
      ((y'' : Dyadic) : ℝ) = (c''' : ℝ) * (2 : ℝ) ^ e''' := by
    intro c''' e''' h
    rw [Dyadic.coe_real_eq_ratCast, h]; push_cast; ring
  -- Combine: y'' ∉ F₂, contradicting y'' ∈ F₁ ⊆ F₂.
  have hy''_not_F₂ : y'' ∉ F₂.toFormat := by
    intro hy''_F₂
    obtain ⟨h_pre, h_qua, _⟩ := hy''_F₂
    change Dyadic.precisionAtMost F₂.p y'' at h_pre
    change Dyadic.quantumAtLeast F₂.exp y'' at h_qua
    cases hexp2 : F₂.exp with
    | bot =>
      have h_F₂_nd := F₂.nondegenerate
      rcases h_F₂_nd with ⟨hp_top_neg, _⟩ | hexp_bot_neg
      · cases hp2 : F₂.p with
        | top => exact absurd hp2 hp_top_neg
        | coe n =>
          have h_numD_eq_n : (p₂ : ℤ) = ((n : ℕ) : ℤ) := by
            rw [hp₂_eq, F₂.toFiniteFormat.numDigits_coe_bot hy_ne_zero hp2 hexp2]
          have hp₂_eq_n : p₂ = (n : ℕ) := by exact_mod_cast h_numD_eq_n
          have hp₂_ge_2 : p₂ ≥ 2 := by
            have h2le : (2 : ℕ) ≤ (n : ℕ) := by
              have : ((2 : ℕ+) : WithTop ℕ+) ≤ ((n : ℕ+) : WithTop ℕ+) := hp2 ▸ hp_F₂
              exact_mod_cast this
            omega
          have hc''_strong : (2 : ℤ) ^ p₂ + 1 ≤ |c''| := by
            rw [hc''_abs]
            have hcs := hc_low_strict hp₂_ge_2
            have h_double : 2 * ((2 : ℤ) ^ (p₂ - 1) + 1) - 1 = (2 : ℤ) ^ p₂ + 1 := by
              rw [Int.two_pow_succ_pred hp₂_pos]; ring
            linarith
          rw [hp2, Dyadic.precisionAtMost_coe] at h_pre
          obtain ⟨c''', e''', hy''_rep, hc'''_low⟩ := h_pre
          have h_abs := h_int_rep_abs c''' e''' (ratrep_to_realrep c''' e''' hy''_rep)
          have hchain : (2 : ℤ) ^ (n : ℕ) + 1 ≤ |c'''| := by
            rw [← hp₂_eq_n]; linarith
          linarith
      · exact absurd hexp2 hexp_bot_neg
    | coe e₂ =>
      cases hp2 : F₂.p with
      | top =>
        have h_numD : F₂.toFiniteFormat.numDigits ((y : Dyadic) : ℝ) =
            Int.log 2 |((y : Dyadic) : ℝ)| - e₂ + 1 := by
          rw [F₂.toFiniteFormat.numDigits_top_coe hy_ne_zero hexp2 hp2]
        rw [h_log_y_eq] at h_numD
        have h_e_eq : e = e₂ := by
          have h1 : (p₂ : ℤ) = (p₂ : ℤ) - 1 + e - e₂ + 1 := by
            rw [← h_numD]; exact hp₂_eq
          omega
        rw [hexp2, Dyadic.quantumAtLeast_coe] at h_qua
        obtain ⟨c''', hy''_rep⟩ := h_qua
        have h_e_le := h_int_rep_le c''' e₂ (ratrep_to_realrep c''' e₂ hy''_rep)
        omega
      | coe n =>
        have h_numD : F₂.toFiniteFormat.numDigits ((y : Dyadic) : ℝ) =
            min ((n : ℕ) : ℤ) (Int.log 2 |((y : Dyadic) : ℝ)| - e₂ + 1) := by
          rw [F₂.toFiniteFormat.numDigits_coe_coe hy_ne_zero hp2 hexp2]
        rw [h_log_y_eq] at h_numD
        have hp₂_le_n : (p₂ : ℤ) ≤ ((n : ℕ) : ℤ) := by
          rw [hp₂_eq, h_numD]; exact min_le_left _ _
        rcases eq_or_lt_of_le hp₂_le_n with hp₂_eq_n | hp₂_lt_n
        · have hn_eq_p₂ : (n : ℕ) = p₂ := by exact_mod_cast hp₂_eq_n.symm
          have hp₂_ge_2 : p₂ ≥ 2 := by
            have h2le : (2 : ℕ) ≤ (n : ℕ) := by
              have : ((2 : ℕ+) : WithTop ℕ+) ≤ ((n : ℕ+) : WithTop ℕ+) := hp2 ▸ hp_F₂
              exact_mod_cast this
            omega
          have hc''_strong : (2 : ℤ) ^ p₂ + 1 ≤ |c''| := by
            rw [hc''_abs]
            have hcs := hc_low_strict hp₂_ge_2
            have h_double : 2 * ((2 : ℤ) ^ (p₂ - 1) + 1) - 1 = (2 : ℤ) ^ p₂ + 1 := by
              rw [Int.two_pow_succ_pred hp₂_pos]; ring
            linarith
          rw [hp2, Dyadic.precisionAtMost_coe] at h_pre
          obtain ⟨c''', e''', hy''_rep, hc'''_low⟩ := h_pre
          have h_abs := h_int_rep_abs c''' e''' (ratrep_to_realrep c''' e''' hy''_rep)
          have h_chain : (2 : ℤ) ^ (n : ℕ) + 1 ≤ |c'''| := by
            rw [hn_eq_p₂]; linarith
          linarith
        · have h_e_eq : e = e₂ := by
            have h1 : (p₂ : ℤ) = min ((n : ℕ) : ℤ) ((p₂ : ℤ) - 1 + e - e₂ + 1) := by
              rw [← h_numD]; exact hp₂_eq
            have h2 : (p₂ : ℤ) = (p₂ : ℤ) - 1 + e - e₂ + 1 := by
              rcases min_cases ((n : ℕ) : ℤ) ((p₂ : ℤ) - 1 + e - e₂ + 1) with
                ⟨hmin, _⟩ | ⟨hmin, _⟩
              · rw [hmin] at h1; omega
              · rw [hmin] at h1; exact h1
            omega
          rw [hexp2, Dyadic.quantumAtLeast_coe] at h_qua
          obtain ⟨c''', hy''_rep⟩ := h_qua
          have h_e_le := h_int_rep_le c''' e₂ (ratrep_to_realrep c''' e₂ hy''_rep)
          omega
  exact hy''_not_F₂ (hsub y'' hy''_F₁)

/-- Lemma 5.3, digit-count half: if `y ∈ F₁`, `F₁ ⊆ F₂`, `2 ≤ F₂.p`, and `y`
is `IsOdd F₂`, then `F₁` and `F₂` assign `y` the same effective precision.
- `≥`: the Lemma 5.3 corollary (`precisionAtMost_not_IsOdd`).
- `≤`: by contradiction via `numDigits_eq_of_subset_of_isOdd_aux`. -/
theorem numDigits_eq_of_subset_of_isOdd
    {F₁ : FiniteFormat} {F₂ : ParityFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ+) : WithTop ℕ+) ≤ F₂.p)
    {y : Dyadic} (hyF₁ : y ∈ F₁) (hodd : F₂.IsOdd y) :
    F₁.numDigits (y : ℝ) = F₂.toFiniteFormat.numDigits (y : ℝ) := by
  have h_F₂_pos : 0 < F₂.toFiniteFormat.numDigits (y : ℝ) := hodd.numDigits_pos
  -- `y ≠ 0` (in ℝ) from `IsOdd`.
  have hy_ne_d : y ≠ 0 := hodd.ne_zero
  have hy_ne_zero : ((y : Dyadic) : ℝ) ≠ 0 := by
    intro h
    apply hy_ne_d
    have : ((y : Dyadic) : ℝ) = ((0 : Dyadic) : ℝ) := by rw [h, Dyadic.coe_real_zero]
    exact Dyadic.coe_real_injective this
  -- `1 ≤ numDigits F₁ y`, so its `toNat` is a `ℕ+`.
  have h_F₁_ge_1 : 1 ≤ F₁.numDigits (y : ℝ) :=
    F₁.numDigits_nonneg y hyF₁ hy_ne_zero
  set n : ℕ := (F₁.numDigits (y : ℝ)).toNat with hn_def
  have hn_eq : (n : ℤ) = F₁.numDigits (y : ℝ) :=
    Int.toNat_of_nonneg (by linarith)
  have hn_pos : 1 ≤ n := by
    have : (1 : ℤ) ≤ (n : ℤ) := by rw [hn_eq]; exact h_F₁_ge_1
    exact_mod_cast this
  set w : ℕ+ := ⟨n, hn_pos⟩ with hw_def
  have hw_val : ((w : ℕ+) : ℕ) = n := rfl
  -- Repackage the `mem_imp` witness (ℝ rep) as `precisionAtMost w y` (ℚ).
  obtain ⟨c, e, hy_rep_real, hc_bound⟩ :=
    F₁.mem_imp_precisionAtMost_numDigits hyF₁ hy_ne_zero
  have hc_bound_w : |c| < (2 : ℤ) ^ ((w : ℕ+) : ℕ) := by rw [hw_val]; exact hc_bound
  have h_prec_F₁ : Dyadic.precisionAtMost ((w : ℕ+) : WithTop ℕ+) y := by
    rw [Dyadic.precisionAtMost_coe_real]
    exact ⟨c, e, hy_rep_real, hc_bound_w⟩
  -- `≥`: from the corollary.
  have h_ge : F₁.numDigits (y : ℝ) ≥ F₂.toFiniteFormat.numDigits (y : ℝ) := by
    rw [← hn_eq, ← hw_val]
    by_contra h
    push Not at h
    exact F₂.precisionAtMost_not_IsOdd h h_prec_F₁ hodd
  -- `≤`: by contradiction via `_aux`.
  refine le_antisymm ?_ h_ge
  by_contra h_lt
  push Not at h_lt
  exact numDigits_eq_of_subset_of_isOdd_aux hsub hp_F₂ hyF₁ hodd h_lt

/-- The `F₁.p = 1` corner of `IsOdd.transfer_of_numDigits_eq`: shows that the
F₂-IsOdd witness exponent `e` equals `F₁.exp`'s value, so the index-counting
parity `Odd (e − F₁.exp + 1)` reduces to `Odd 1`. -/
private lemma odd_index_of_p_one_corner {F₁ F₂ : ParityFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ+) : WithTop ℕ+) ≤ F₂.p)
    (hF₁_p_1 : F₁.p = ((1 : ℕ+) : WithTop ℕ+))
    {y : Dyadic} (hyF₁ : y ∈ F₁.toFiniteFormat) (h_iod_F₂ : F₂.IsOdd y)
    (h_eq : F₁.toFiniteFormat.numDigits (y : ℝ)
            = F₂.toFiniteFormat.numDigits (y : ℝ))
    {c e : ℤ}
    (h_rep_F₂ : Dyadic.IsRepresentableAtP
        (F₂.toFiniteFormat.numDigits (y : ℝ)).toNat c e y) :
    Odd (e - WithBot.unbotD 0 F₁.exp + 1) := by
  -- `F₁.p = 1` forces `F₁.exp ≠ ⊥` (via the `parity` invariant).
  have hF₁_exp_ne : F₁.exp ≠ ⊥ := by
    rcases F₁.parity with hp1 | hexp
    · exact absurd hF₁_p_1 hp1
    · exact hexp
  set e₁ : ℤ := F₁.exp.unbot hF₁_exp_ne with he₁_def
  have hF₁_exp_eq : F₁.exp = (e₁ : WithBot ℤ) :=
    (WithBot.coe_unbot F₁.exp hF₁_exp_ne).symm
  have h_unbot : WithBot.unbotD 0 F₁.exp = e₁ := by rw [hF₁_exp_eq]; rfl
  rw [h_unbot]
  have h_F₂_pos_y : 0 < F₂.toFiniteFormat.numDigits (y : ℝ) :=
    h_iod_F₂.numDigits_pos
  have h_numD_F₁_le_1 : F₁.toFiniteFormat.numDigits (y : ℝ) ≤ 1 :=
    F₁.toFiniteFormat.numDigits_le_one_of_p_one hF₁_p_1 _
  have h_p₂_eq_1 : F₂.toFiniteFormat.numDigits (y : ℝ) = 1 := by
    rw [h_eq] at h_numD_F₁_le_1; omega
  have h_p₂_toNat_eq_1 :
      (F₂.toFiniteFormat.numDigits (y : ℝ)).toNat = 1 := by
    rw [h_p₂_eq_1]; rfl
  obtain ⟨h_y_eq, hc_low_y, hc_high_y⟩ := h_rep_F₂
  rw [h_p₂_toNat_eq_1] at hc_low_y hc_high_y
  have hc_abs_eq : |c| = 1 := by
    have h1 : (1 : ℤ) ≤ |c| := by simpa using hc_low_y
    have h2 : |c| < (2 : ℤ) := by simpa using hc_high_y
    omega
  have hy_ne_zero_d : y ≠ 0 := h_iod_F₂.ne_zero
  have hy_ne_zero : ((y : Dyadic) : ℝ) ≠ 0 := by
    intro h
    apply hy_ne_zero_d
    have : ((y : Dyadic) : ℝ) = ((0 : Dyadic) : ℝ) := by rw [h, Dyadic.coe_real_zero]
    exact Dyadic.coe_real_injective this
  have h2real_pos : (0 : ℝ) < 2 := by norm_num
  have h2real_ne : (2 : ℝ) ≠ 0 := by norm_num
  -- A real-valued rep of `y` from the ℚ-valued `h_y_eq`.
  have h_y_eq_real : ((y : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ) ^ e := by
    rw [Dyadic.coe_real_eq_ratCast, h_y_eq]; push_cast; ring
  have habs_y_eq : |((y : Dyadic) : ℝ)| = (2 : ℝ) ^ e := by
    rw [h_y_eq_real, abs_mul_two_zpow]
    have hc_real : (|c| : ℝ) = 1 := by exact_mod_cast hc_abs_eq
    rw [hc_real]; ring
  have h_log_y_eq : Int.log 2 |((y : Dyadic) : ℝ)| = e := by
    rw [habs_y_eq]
    exact Int.log_zpow (by norm_num : 1 < 2) e
  -- `y = c'_q · 2^e₁` from the F₁-quantum constraint.
  have hyF₁_q : Dyadic.quantumAtLeast F₁.exp y := hyF₁.2.1
  rw [hF₁_exp_eq, Dyadic.quantumAtLeast_coe_real] at hyF₁_q
  obtain ⟨c'_q, hc'_q_eq⟩ := hyF₁_q
  have h_e_ge_e₁ : e₁ ≤ e := by
    by_contra h_gt
    push Not at h_gt
    have h_diff : 0 < e₁ - e := by omega
    have h_diff_nat : ((e₁ - e).toNat : ℤ) = e₁ - e :=
      Int.toNat_of_nonneg (le_of_lt h_diff)
    have h_real : (c : ℝ) = (c'_q : ℝ) * (2 : ℝ) ^ (e₁ - e) := by
      have h2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos h2real_pos _
      have h_split : (2 : ℝ) ^ e₁ = (2 : ℝ) ^ (e₁ - e) * (2 : ℝ) ^ e := by
        rw [← zpow_add₀ h2real_ne]; congr 1; ring
      have key : (c : ℝ) * (2 : ℝ) ^ e =
          ((c'_q : ℝ) * (2 : ℝ) ^ (e₁ - e)) * (2 : ℝ) ^ e := by
        rw [show ((c'_q : ℝ) * (2 : ℝ) ^ (e₁ - e)) * (2 : ℝ) ^ e =
            (c'_q : ℝ) * ((2 : ℝ) ^ (e₁ - e) * (2 : ℝ) ^ e) from by ring]
        rw [← h_split, ← hc'_q_eq, h_y_eq_real]
      exact mul_right_cancel₀ (ne_of_gt h2e_pos) key
    rw [show (2 : ℝ) ^ (e₁ - e) = (2 : ℝ) ^ ((e₁ - e).toNat : ℤ) from by
        rw [h_diff_nat], zpow_natCast] at h_real
    have h_int_eq : c = c'_q * 2 ^ (e₁ - e).toNat := by
      have : ((c'_q * 2 ^ (e₁ - e).toNat : ℤ) : ℝ) = (c : ℝ) := by
        push_cast; linarith
      exact_mod_cast this.symm
    have h_k_ge_1 : 1 ≤ (e₁ - e).toNat := by
      have : ((e₁ - e).toNat : ℤ) ≥ 1 := by rw [h_diff_nat]; omega
      exact_mod_cast this
    have h_pow_ge_2 : (2 : ℤ) ≤ 2 ^ (e₁ - e).toNat := by
      have : (2 : ℤ) ^ 1 ≤ 2 ^ (e₁ - e).toNat :=
        pow_le_pow_right₀ (by norm_num) h_k_ge_1
      simpa using this
    have h_factor : (1 : ℤ) = |c'_q| * 2 ^ (e₁ - e).toNat := by
      have : |c| = |c'_q * 2 ^ (e₁ - e).toNat| := by rw [h_int_eq]
      rw [hc_abs_eq, abs_mul, abs_pow] at this
      have h2_abs : |(2 : ℤ)| = 2 := by decide
      rw [h2_abs] at this
      exact this
    have h_abs_pos : (1 : ℤ) ≤ |c'_q| := by
      rcases eq_or_ne c'_q 0 with hc'0 | hc'_ne
      · rw [hc'0] at h_factor; simp at h_factor
      · exact Int.one_le_abs hc'_ne
    nlinarith
  -- `F₂.exp` is finite (`= e₂`), with `e = e₂`.
  have h_e_eq_F₂_exp_or_p_eq_1 :
      (∃ e₂ : ℤ, F₂.exp = (e₂ : WithBot ℤ) ∧ e = e₂) := by
    cases hF₂_exp_cases : F₂.exp with
    | bot =>
      exfalso
      cases hF₂_p_cases : F₂.p with
      | top =>
        rcases F₂.nondegenerate with ⟨hp_top_neg, _⟩ | hexp_bot_neg
        · exact hp_top_neg hF₂_p_cases
        · exact hexp_bot_neg hF₂_exp_cases
      | coe n =>
        have h_n : F₂.toFiniteFormat.numDigits ((y : Dyadic) : ℝ) = (n : ℤ) := by
          rw [F₂.toFiniteFormat.numDigits_coe_bot hy_ne_zero hF₂_p_cases hF₂_exp_cases]
        rw [h_n] at h_p₂_eq_1
        have hn_eq_1 : (n : ℕ) = 1 := by exact_mod_cast h_p₂_eq_1
        have hn_eq_1' : n = 1 := by
          have : ((n : ℕ+) : ℕ) = ((1 : ℕ+) : ℕ) := hn_eq_1
          exact_mod_cast this
        have hF₂_p_eq_1 : F₂.p = ((1 : ℕ+) : WithTop ℕ+) := by
          rw [hF₂_p_cases, hn_eq_1']
        rw [hF₂_p_eq_1] at hp_F₂
        have : ((2 : ℕ+) : ℕ) ≤ ((1 : ℕ+) : ℕ) := by exact_mod_cast hp_F₂
        simp at this
    | coe e₂ =>
      refine ⟨e₂, rfl, ?_⟩
      cases hF₂_p_cases : F₂.p with
      | top =>
        have h_n : F₂.toFiniteFormat.numDigits ((y : Dyadic) : ℝ) =
            Int.log 2 |((y : Dyadic) : ℝ)| - e₂ + 1 := by
          rw [F₂.toFiniteFormat.numDigits_top_coe hy_ne_zero hF₂_exp_cases hF₂_p_cases]
        rw [h_n, h_log_y_eq] at h_p₂_eq_1
        omega
      | coe n =>
        have h_n : F₂.toFiniteFormat.numDigits ((y : Dyadic) : ℝ) =
            min ((n : ℕ) : ℤ) (Int.log 2 |((y : Dyadic) : ℝ)| - e₂ + 1) := by
          rw [F₂.toFiniteFormat.numDigits_coe_coe hy_ne_zero hF₂_p_cases hF₂_exp_cases]
        rw [h_n, h_log_y_eq] at h_p₂_eq_1
        have hn_ge_2 : (2 : ℤ) ≤ ((n : ℕ) : ℤ) := by
          have : ((2 : ℕ+) : WithTop ℕ+) ≤ ((n : ℕ+) : WithTop ℕ+) := hF₂_p_cases ▸ hp_F₂
          exact_mod_cast this
        rcases min_cases ((n : ℕ) : ℤ) (e - e₂ + 1) with ⟨h1, _⟩ | ⟨h1, _⟩
        · rw [h1] at h_p₂_eq_1; omega
        · rw [h1] at h_p₂_eq_1; omega
  obtain ⟨e₂, hF₂_exp_eq, h_e_eq⟩ := h_e_eq_F₂_exp_or_p_eq_1
  -- The witness `2^e₁ = ofIntZpow 1 e₁ ∈ F₁`.
  have h_2e1_in_F₁ : (Dyadic.ofIntZpow 1 e₁) ∈ F₁.toFormat := by
    refine ⟨?_, ?_, ?_⟩
    · change Dyadic.precisionAtMost F₁.p (Dyadic.ofIntZpow 1 e₁)
      rw [hF₁_p_1, Dyadic.precisionAtMost_coe]
      refine ⟨1, e₁, ?_, ?_⟩
      · rw [Dyadic.coe_rat_ofIntZpow]
      · decide
    · change Dyadic.quantumAtLeast F₁.exp (Dyadic.ofIntZpow 1 e₁)
      rw [hF₁_exp_eq, Dyadic.quantumAtLeast_coe]
      refine ⟨1, ?_⟩
      rw [Dyadic.coe_rat_ofIntZpow]
    · change Mpfx.Format.boundOK F₁.b (Dyadic.ofIntZpow 1 e₁)
      have hyF₁_b := hyF₁.2.2
      cases hb : F₁.b with
      | top => trivial
      | coe b =>
        rw [hb] at hyF₁_b
        change |((Dyadic.ofIntZpow 1 e₁ : Dyadic) : ℚ)| ≤ ((b.val : Dyadic) : ℚ)
        have hyF₁_b' : |((y : Dyadic) : ℚ)| ≤ ((b.val : Dyadic) : ℚ) := hyF₁_b
        -- `|2^e₁| ≤ |y|` over ℝ, bridged to ℚ.
        have habs_q : |((Dyadic.ofIntZpow 1 e₁ : Dyadic) : ℚ)| ≤ |((y : Dyadic) : ℚ)| := by
          have hh : |((Dyadic.ofIntZpow 1 e₁ : Dyadic) : ℝ)| ≤ |((y : Dyadic) : ℝ)| := by
            rw [Dyadic.coe_ofIntZpow]
            have h2e₁_pos : (0 : ℝ) < (2 : ℝ) ^ e₁ := zpow_pos h2real_pos _
            have h_eq_pow : ((1 : ℤ) : ℝ) * (2 : ℝ) ^ e₁ = (2 : ℝ) ^ e₁ := by
              push_cast; ring
            rw [h_eq_pow, abs_of_pos h2e₁_pos, habs_y_eq]
            exact zpow_le_zpow_right₀ (by norm_num) h_e_ge_e₁
          rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast,
              ← Rat.cast_abs, ← Rat.cast_abs] at hh
          exact_mod_cast hh
        linarith
  have h_2e1_in_F₂ : (Dyadic.ofIntZpow 1 e₁) ∈ F₂.toFormat := hsub _ h_2e1_in_F₁
  have hF₂_exp_le_e₁ : e₂ ≤ e₁ := by
    obtain ⟨_, hq, _⟩ := h_2e1_in_F₂
    change Dyadic.quantumAtLeast F₂.exp (Dyadic.ofIntZpow 1 e₁) at hq
    rw [hF₂_exp_eq, Dyadic.quantumAtLeast_coe] at hq
    obtain ⟨c''', hc'''_eq⟩ := hq
    by_contra h_gt
    push Not at h_gt
    have h_gt' : 0 < e₂ - e₁ := by omega
    have h_diff_nat : ((e₂ - e₁).toNat : ℤ) = e₂ - e₁ :=
      Int.toNat_of_nonneg (le_of_lt h_gt')
    have h_real : (1 : ℝ) = (c''' : ℝ) * (2 : ℝ) ^ (e₂ - e₁) := by
      rw [Dyadic.coe_rat_ofIntZpow] at hc'''_eq
      have h_one : ((1 : ℤ) : ℚ) * (2 : ℚ) ^ e₁ =
          (c''' : ℚ) * (2 : ℚ) ^ e₂ := hc'''_eq
      have h_one_real : ((1 : ℤ) : ℝ) * (2 : ℝ) ^ e₁ =
          (c''' : ℝ) * (2 : ℝ) ^ e₂ := by
        have hcast := congrArg (fun q : ℚ => (q : ℝ)) h_one
        push_cast at hcast ⊢; linarith
      have h2e₁_pos : (0 : ℝ) < (2 : ℝ) ^ e₁ := zpow_pos h2real_pos _
      have h_split : (2 : ℝ) ^ e₂ = (2 : ℝ) ^ (e₂ - e₁) * (2 : ℝ) ^ e₁ := by
        rw [← zpow_add₀ h2real_ne]; congr 1; ring
      have key : (1 : ℝ) * (2 : ℝ) ^ e₁ =
          ((c''' : ℝ) * (2 : ℝ) ^ (e₂ - e₁)) * (2 : ℝ) ^ e₁ := by
        rw [show ((1 : ℤ) : ℝ) = (1 : ℝ) from by push_cast; ring] at h_one_real
        rw [h_one_real, h_split]; ring
      exact mul_right_cancel₀ (ne_of_gt h2e₁_pos) key
    rw [show (2 : ℝ) ^ (e₂ - e₁) =
        (2 : ℝ) ^ ((e₂ - e₁).toNat : ℤ) from by rw [h_diff_nat],
        zpow_natCast] at h_real
    have h_int_eq : (1 : ℤ) = c''' * 2 ^ (e₂ - e₁).toNat := by
      have : ((1 : ℤ) : ℝ) = ((c''' * 2 ^ (e₂ - e₁).toNat : ℤ) : ℝ) := by
        push_cast; linarith
      exact_mod_cast this
    have h_2_dvd : (2 : ℤ) ∣ c''' * 2 ^ (e₂ - e₁).toNat := by
      rw [show (e₂ - e₁).toNat = ((e₂ - e₁).toNat - 1) + 1 from by omega,
          pow_succ]
      exact ⟨c''' * 2 ^ ((e₂ - e₁).toNat - 1), by ring⟩
    rw [← h_int_eq] at h_2_dvd
    exact absurd h_2_dvd (by decide)
  have h_e₁_eq_e : e₁ = e := by omega
  rw [show (e - e₁ + 1 : ℤ) = 1 from by omega]
  exact ⟨0, by ring⟩

/-- Transfer `IsOdd` from `F₂` to a subformat `F₁` containing `y`, given that
the effective precisions agree. Handles both `F₁.p ≥ 2` (direct witness
transfer) and `F₁.p = 1` (the index-counting parity discriminator, which
forces `F₁.exp = F₂.exp = e_y` and reduces to `Odd 1`).

The `numDigits F₁ y = numDigits F₂ y` hypothesis is the conclusion of
`numDigits_eq_of_subset_of_isOdd`; together they form the standard
parity-transfer chain used by `rndRTO_RTO`. -/
theorem IsOdd.transfer_of_numDigits_eq {F₁ F₂ : ParityFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ+) : WithTop ℕ+) ≤ F₂.p)
    {y : Dyadic} (hyF₁ : y ∈ F₁.toFiniteFormat) (h_iod_F₂ : F₂.IsOdd y)
    (h_eq : F₁.toFiniteFormat.numDigits (y : ℝ)
            = F₂.toFiniteFormat.numDigits (y : ℝ)) :
    F₁.IsOdd y := by
  have h_iod_F₂' : F₂.IsOdd y := h_iod_F₂
  obtain ⟨c, e, h_rep_F₂, h_par_F₂⟩ := h_iod_F₂
  have hF₂_ne_1 : F₂.p ≠ ((1 : ℕ+) : WithTop ℕ+) := by
    intro h
    rw [h] at hp_F₂
    have : ((2 : ℕ+) : ℕ) ≤ ((1 : ℕ+) : ℕ) := by exact_mod_cast hp_F₂
    simp at this
  rw [if_neg hF₂_ne_1] at h_par_F₂
  have h_par_c : Odd c := h_par_F₂
  refine ⟨c, e, ?_, ?_⟩
  · rw [h_eq]; exact h_rep_F₂
  · by_cases hF₁_p_1 : F₁.p = ((1 : ℕ+) : WithTop ℕ+)
    · rw [if_pos hF₁_p_1]
      exact odd_index_of_p_one_corner hsub hp_F₂ hF₁_p_1 hyF₁ h_iod_F₂' h_eq h_rep_F₂
    · rw [if_neg hF₁_p_1]; exact h_par_c

/-- **Lemma 5.3** (RTO digit-padding preserves oddness across a subformat).
If `F₁ ⊆ F₂`, `F₂` has at least 2 bits, and `y ∈ F₁` is `IsOdd` in `F₂`, then
`y` is `IsOdd` in `F₁` as well. The capstone consumed by the RTO-composition
double-rounding rules (`rndRTO_RTO`, `rndRTO_RTZ`, `rndRTO_RAZ`, `rndRTO_RN`):
it composes the digit-count agreement (`numDigits_eq_of_subset_of_isOdd`)
with the parity transfer (`IsOdd.transfer_of_numDigits_eq`). -/
theorem IsOdd.transfer_of_subset {F₁ F₂ : ParityFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ+) : WithTop ℕ+) ≤ F₂.p)
    {y : Dyadic} (hyF₁ : y ∈ F₁.toFiniteFormat) (hodd : F₂.IsOdd y) :
    F₁.IsOdd y :=
  IsOdd.transfer_of_numDigits_eq hsub hp_F₂ hyF₁ hodd
    (numDigits_eq_of_subset_of_isOdd hsub hp_F₂ hyF₁ hodd)

end Mpfx
