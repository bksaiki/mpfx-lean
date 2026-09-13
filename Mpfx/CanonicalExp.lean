import Mpfx.Grid

/-!
# Canonical exponent: closed forms and grid representation

Format-generic facts about `FiniteFormat.canonicalExp` (Flocq `cexp`), shared by
the operation-specific double-rounding proofs (addition, square root, …):

* `exists_canonical_rep` — a positive member as `c · 2^cexp` with `|c| < 2^p`;
* `canonicalExp_closed` / `canonicalExp_FLX` / `canonicalExp_FLT` — the closed
  forms of `cexp` in the normal range, the FLX regime (`exp = ⊥`), and the FLT
  regime (`exp = emin` finite);
* `exp_le_canonicalExp_coe` — `F.exp ≤ cexp` uniformly over `exp = ⊥`/finite.
-/

namespace Mpfx

/-- **Canonical grid representation.** A positive `y ∈ F` (precision `p`) is
`c · 2^(canonicalExp y)` with `|c| < 2^p`. Unifies the `exp = ⊥` and finite-`exp`
grid lemmas (both have grid step `= canonicalExp`). -/
theorem exists_canonical_rep (F : FiniteFormat) {p : ℕ}
    (hp : F.p = (p : Prec))
    {y : Dyadic} (hmem : y ∈ F) (hpos : 0 < (y : ℝ)) :
    ∃ c : ℤ, |c| < (2 : ℤ) ^ p ∧
      (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ (F.canonicalExp (y : ℝ)) :=
  have ⟨hprec, hquant, _⟩ := hmem
  exists_grid_rep_canonical F hp hprec hquant hpos

/-- **Closed form of `canonicalExp` in the normal range** (unifies FLX and FLT).
When `v` is nonzero and its FLX exponent `log₂|v| + 1 − p` is at least the
format's minimum exponent `F.exp` (the *normal* regime — vacuous for `exp = ⊥`),
`canonicalExp` takes the FLX form. This is the single lemma that lets the FLX
proofs run unchanged for FLT: in the genuine-midpoint case all values are normal. -/
theorem canonicalExp_closed {F : FiniteFormat} {p : ℕ}
    (hp : F.p = (p : Prec)) {v : ℝ} (hv : v ≠ 0)
    (hnorm : F.exp ≤ ((Int.log 2 |v| + 1 - (p : ℤ) : ℤ) : QExp)) :
    F.canonicalExp v = Int.log 2 |v| + 1 - (p : ℤ) := by
  unfold FiniteFormat.canonicalExp
  cases hexp : F.exp using QExp.recBotCoe with
  | bot => simp only [hp, hv, if_false]
  | coe e =>
    simp only [hp, hv, if_false]
    rw [hexp] at hnorm
    exact max_eq_left (by exact_mod_cast hnorm)

/-- Closed form of `canonicalExp` in an FLX format (`exp = ⊥`): `log₂|v| + 1 − p`
(the vacuous-normality special case of `canonicalExp_closed`). -/
theorem canonicalExp_FLX {F : FiniteFormat} {p : ℕ}
    (hp : F.p = (p : Prec)) (hexp : F.exp = ⊥)
    {v : ℝ} (hv : v ≠ 0) : F.canonicalExp v = Int.log 2 |v| + 1 - (p : ℤ) :=
  canonicalExp_closed hp hv (by rw [hexp]; exact bot_le)

/-- Closed form of `canonicalExp` in an FLT format (`exp = emin` finite):
`max(log₂|v| + 1 − p, emin)`. -/
theorem canonicalExp_FLT {F : FiniteFormat} {p : ℕ} {emin : ℤ}
    (hp : F.p = (p : Prec)) (hexp : F.exp = (emin : QExp))
    {v : ℝ} (hv : v ≠ 0) :
    F.canonicalExp v = max (Int.log 2 |v| + 1 - (p : ℤ)) emin := by
  unfold FiniteFormat.canonicalExp; simp only [hp, hexp, hv, if_false]

/-- `F.exp ≤ (F.canonicalExp x : QExp)`, uniformly over `exp = ⊥`/finite. -/
theorem exp_le_canonicalExp_coe (F : FiniteFormat) (x : ℝ) :
    F.exp ≤ ((F.canonicalExp x : ℤ) : QExp) := by
  cases hexp : F.exp using QExp.recBotCoe with
  | bot => exact bot_le
  | coe e => exact_mod_cast F.exp_le_canonicalExp x hexp

/-- The FLX exponent lower-bounds `canonicalExp`: `log₂|v| + 1 − p ≤ canonicalExp v`
(equality for `exp = ⊥`; `≤` via `le_max_left` for finite `exp`). -/
theorem log_sub_prec_le_canonicalExp {F : FiniteFormat} {p : ℕ}
    (hp : F.p = (p : Prec)) {v : ℝ} (hv : v ≠ 0) :
    Int.log 2 |v| + 1 - (p : ℤ) ≤ F.canonicalExp v := by
  cases hexp : F.exp using QExp.recBotCoe with
  | bot => rw [canonicalExp_FLX hp hexp hv]
  | coe e => rw [canonicalExp_FLT hp hexp hv]; exact le_max_left _ _

/-! ### Powers of two: predecessor identities

Shared replacements for the `2^a = 2·2^(a-1)` etc. identities re-proved inline
throughout the operation-specific proofs (`⌊·⌋`-based `set` variables make
`rw [show a = (a-1)+1 …]` self-referential, so these avoid rewriting the
exponent variable). -/

/-- `2^a = 2^(a-1) · 2`. -/
theorem two_zpow_pred (a : ℤ) : (2 : ℝ) ^ a = (2 : ℝ) ^ (a - 1) * 2 := by
  have h : (2 : ℝ) ^ ((a - 1) + 1) = (2 : ℝ) ^ (a - 1) * (2 : ℝ) ^ (1 : ℤ) :=
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (a - 1) 1
  rw [zpow_one, show (a - 1) + 1 = a from by ring] at h; exact h

/-- `2^a / 2 = 2^(a-1)`. -/
theorem two_zpow_half (a : ℤ) : (2 : ℝ) ^ a / 2 = (2 : ℝ) ^ (a - 1) := by
  rw [two_zpow_pred a]; ring

/-- `2^a = 2 · 2^(a-1)`. -/
theorem two_zpow_dbl (a : ℤ) : (2 : ℝ) ^ a = 2 * (2 : ℝ) ^ (a - 1) := by
  rw [two_zpow_pred a]; ring

/-! ### Quantum alignment under arithmetic

A value's *quantum* (`Dyadic.quantumAtLeast e`) is preserved/combined under
negation, `±`, and `×`. Shared by the addition and multiplication proofs. -/

/-- Negation preserves quantum alignment. -/
theorem quantumAtLeast_neg {e : QExp} {a : Dyadic}
    (ha : Dyadic.quantumAtLeast e a) : Dyadic.quantumAtLeast e (-a) := by
  cases e using QExp.recBotCoe with
  | bot => trivial
  | coe e =>
    obtain ⟨ca, hca⟩ := (Dyadic.quantumAtLeast_coe_real e a).mp ha
    refine (Dyadic.quantumAtLeast_coe_real e (-a)).mpr ⟨-ca, ?_⟩
    rw [show ((-a : Dyadic) : ℝ) = -(a : ℝ) from by push_cast; ring, hca]; push_cast; ring

/-- A sum of two quantum-aligned dyadics stays quantum-aligned. -/
theorem quantumAtLeast_add {e : QExp} {a b : Dyadic}
    (ha : Dyadic.quantumAtLeast e a) (hb : Dyadic.quantumAtLeast e b) :
    Dyadic.quantumAtLeast e (a + b) := by
  cases e using QExp.recBotCoe with
  | bot => trivial
  | coe e =>
    obtain ⟨ca, hca⟩ := (Dyadic.quantumAtLeast_coe_real e a).mp ha
    obtain ⟨cb, hcb⟩ := (Dyadic.quantumAtLeast_coe_real e b).mp hb
    refine (Dyadic.quantumAtLeast_coe_real e (a + b)).mpr ⟨ca + cb, ?_⟩
    rw [show ((a + b : Dyadic) : ℝ) = (a : ℝ) + (b : ℝ) from by push_cast; ring, hca, hcb]
    push_cast; ring

/-- A difference of two quantum-aligned dyadics stays quantum-aligned. -/
theorem quantumAtLeast_sub {e : QExp} {a b : Dyadic}
    (ha : Dyadic.quantumAtLeast e a) (hb : Dyadic.quantumAtLeast e b) :
    Dyadic.quantumAtLeast e (a - b) := by
  rw [sub_eq_add_neg]; exact quantumAtLeast_add ha (quantumAtLeast_neg hb)

/-- A product is quantum-aligned at the *sum* of the operands' quanta. -/
theorem quantumAtLeast_mul {e₁ e₂ : QExp} {x y : Dyadic}
    (hx : Dyadic.quantumAtLeast e₁ x) (hy : Dyadic.quantumAtLeast e₂ y) :
    Dyadic.quantumAtLeast (e₁ + e₂) (x * y) := by
  cases e₁ using QExp.recBotCoe with
  | bot => rw [show (⊥ + e₂ : QExp) = ⊥ from by simp]; trivial
  | coe a =>
    cases e₂ using QExp.recBotCoe with
    | bot => rw [show ((a : QExp) + ⊥) = ⊥ from by simp]; trivial
    | coe b =>
      obtain ⟨cx, hcx⟩ := (Dyadic.quantumAtLeast_coe_real a x).mp hx
      obtain ⟨cy, hcy⟩ := (Dyadic.quantumAtLeast_coe_real b y).mp hy
      rw [← WithBot.coe_add]
      refine (Dyadic.quantumAtLeast_coe_real (a + b) (x * y)).mpr ⟨cx * cy, ?_⟩
      rw [show ((x * y : Dyadic) : ℝ) = (x : ℝ) * (y : ℝ) from by push_cast; ring, hcx, hcy,
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; push_cast; ring


/-! ### Format-dependent scaled-mantissa facts

The companions of the `Mpfx/Utils.lean` block that mention the format. -/

/-- Generic floor-minimality: if `z ∈ F.unbounded` and `z ≤ x`, then `z` is
≤ the floor-projection of `x` at the canonical exponent. Used by `_toNegative`
(directly) and by `_toZero` (for the `0 ≤ x` branch). -/
theorem floor_minimality (F : FiniteFormat) (x : ℝ) {z : Dyadic}
    (hz_prec : Dyadic.precisionAtMost F.p z)
    (hz_quant : Dyadic.quantumAtLeast F.exp z) (hz_le_x : (z : ℝ) ≤ x) :
    (z : ℝ) ≤ (⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋ : ℝ) *
              (2 : ℝ) ^ (F.canonicalExp x) := by
  set e := F.canonicalExp x
  set c := ⌊x * (2 : ℝ) ^ (-e)⌋
  have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  cases hp : F.p using ENat.recTopCoe with
  | top =>
    cases hexp : F.exp using QExp.recBotCoe with
    | bot =>
      exfalso
      rcases F.finite with h | h
      · exact h hp
      · exact h hexp
    | coe e' =>
      have h_e_eq : e = e' := by
        change F.canonicalExp x = e'
        unfold FiniteFormat.canonicalExp
        simp [hp, hexp]
        rfl
      rw [hexp, Dyadic.quantumAtLeast_coe_real] at hz_quant
      obtain ⟨k, hk⟩ := hz_quant
      have h_2e'_pos : (0 : ℝ) < (2 : ℝ) ^ e' := zpow_pos (by norm_num) _
      rw [hk] at hz_le_x
      have h_k_le_x_scale : (k : ℝ) ≤ x * (2 : ℝ) ^ (-e') := by
        have h_eq : (k : ℝ) =
            (k : ℝ) * (2 : ℝ) ^ e' * (2 : ℝ) ^ (-e') := by
          rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
              add_neg_cancel, zpow_zero, mul_one]
        rw [h_eq]
        have h_2neg_pos : (0 : ℝ) < (2 : ℝ) ^ (-e') :=
          zpow_pos (by norm_num) _
        exact mul_le_mul_of_nonneg_right hz_le_x h_2neg_pos.le
      have h_k_le_floor : k ≤ ⌊x * (2 : ℝ) ^ (-e')⌋ :=
        Int.le_floor.mpr h_k_le_x_scale
      rw [hk, h_e_eq]
      have h_c_eq : (c : ℝ) = (⌊x * (2 : ℝ) ^ (-e')⌋ : ℝ) := by
        change (⌊x * (2 : ℝ) ^ (-e)⌋ : ℝ) = (⌊x * (2 : ℝ) ^ (-e')⌋ : ℝ)
        rw [h_e_eq]
      rw [h_c_eq]
      apply mul_le_mul_of_nonneg_right _ h_2e'_pos.le
      exact_mod_cast h_k_le_floor
  | coe p =>
    rw [hp, Dyadic.precisionAtMost_coe_real] at hz_prec
    obtain ⟨a, e_a, hz_repr, ha_bound⟩ := hz_prec
    by_cases h_ea_ge : e ≤ e_a
    · -- integer factor argument
      set diff := (e_a - e).toNat
      have h_diff_eq : (diff : ℤ) = e_a - e :=
        Int.toNat_of_nonneg (by omega)
      have h_factor_real : (a : ℝ) * (2 : ℝ) ^ e_a =
          ((a * 2 ^ diff : ℤ) : ℝ) * (2 : ℝ) ^ e := by
        push_cast
        rw [show ((2 : ℝ) ^ diff : ℝ) = (2 : ℝ) ^ (diff : ℤ)
            from (zpow_natCast _ _).symm]
        rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        congr 2; omega
      rw [hz_repr, h_factor_real]
      have h_le_x : ((a * 2 ^ diff : ℤ) : ℝ) * (2 : ℝ) ^ e ≤ x := by
        rw [← h_factor_real, ← hz_repr]; exact hz_le_x
      have h_factor_le_scaled : ((a * 2 ^ diff : ℤ) : ℝ) ≤
          x * (2 : ℝ) ^ (-e) := by
        have h_2neg_pos : (0 : ℝ) < (2 : ℝ) ^ (-e) :=
          zpow_pos (by norm_num) _
        have h_eq : ((a * 2 ^ diff : ℤ) : ℝ) =
            ((a * 2 ^ diff : ℤ) : ℝ) * (2 : ℝ) ^ e * (2 : ℝ) ^ (-e) := by
          rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
              add_neg_cancel, zpow_zero, mul_one]
        rw [h_eq]
        exact mul_le_mul_of_nonneg_right h_le_x h_2neg_pos.le
      have h_factor_le_c : a * 2 ^ diff ≤ c := by
        change a * 2 ^ diff ≤ ⌊x * (2 : ℝ) ^ (-e)⌋
        exact Int.le_floor.mpr h_factor_le_scaled
      apply mul_le_mul_of_nonneg_right _ h_2e_pos.le
      exact_mod_cast h_factor_le_c
    · -- e_a < e: x = 0 case or binade.
      push Not at h_ea_ge
      by_cases hx : x = 0
      · subst hx
        have hy0 : (c : ℝ) * (2 : ℝ) ^ e = 0 := by
          change (⌊(0 : ℝ) * (2 : ℝ) ^ (-e)⌋ : ℝ) * (2 : ℝ) ^ e = 0
          simp
        rw [hy0, hz_repr] at *
        exact hz_le_x
      · cases hexp : F.exp using QExp.recBotCoe with
        | coe e' =>
          by_cases h_e'_eq : e' = e
          · rw [hexp, Dyadic.quantumAtLeast_coe_real] at hz_quant
            obtain ⟨k, hk⟩ := hz_quant
            rw [hk]
            have h_2neg_pos : (0 : ℝ) < (2 : ℝ) ^ (-e) :=
              zpow_pos (by norm_num) _
            have h_k_real_le : (k : ℝ) ≤ x * (2 : ℝ) ^ (-e) := by
              have h_le_x : (k : ℝ) * (2 : ℝ) ^ e' ≤ x := by
                rw [← hk]; exact hz_le_x
              have h_eq : (k : ℝ) =
                  (k : ℝ) * (2 : ℝ) ^ e' * (2 : ℝ) ^ (-e) := by
                rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
                    h_e'_eq, add_neg_cancel, zpow_zero, mul_one]
              rw [h_eq]
              exact mul_le_mul_of_nonneg_right h_le_x h_2neg_pos.le
            have h_k_le_c : k ≤ c := by
              change k ≤ ⌊x * (2 : ℝ) ^ (-e)⌋
              exact Int.le_floor.mpr h_k_real_le
            rw [h_e'_eq]
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast h_k_le_c)
              h_2e_pos.le
          · have h_e'_le : e' ≤ e := F.exp_le_canonicalExp x hexp
            have h_e'_lt : e' < e := lt_of_le_of_ne h_e'_le h_e'_eq
            have h_log_gt_e' : e' < Int.log 2 |x| + 1 - (p : ℤ) := by
              have h_canon_eq : e = max (Int.log 2 |x| + 1 - (p : ℤ)) e' := by
                change F.canonicalExp x = _
                unfold FiniteFormat.canonicalExp
                simp [hp, hexp, hx]
              by_contra h_neg
              push Not at h_neg
              have : e = e' := by rw [h_canon_eq]; exact max_eq_right h_neg
              exact h_e'_eq this.symm
            have h_e_eq_log : e = Int.log 2 |x| + 1 - (p : ℤ) := by
              have h_canon_eq : e = max (Int.log 2 |x| + 1 - (p : ℤ)) e' := by
                change F.canonicalExp x = _
                unfold FiniteFormat.canonicalExp
                simp [hp, hexp, hx]
              rw [h_canon_eq]
              exact max_eq_left h_log_gt_e'.le
            rw [hz_repr] at hz_le_x ⊢
            exact binade_le_floor (F.p_pos hp) hx ha_bound h_ea_ge h_e_eq_log hz_le_x
        | bot =>
          have h_e_eq_log : e = Int.log 2 |x| + 1 - (p : ℤ) := by
            change F.canonicalExp x = _
            unfold FiniteFormat.canonicalExp
            simp [hp, hexp, hx]
          rw [hz_repr] at hz_le_x ⊢
          exact binade_le_floor (F.p_pos hp) hx ha_bound h_ea_ge h_e_eq_log hz_le_x

/-- Mirror of `floor_minimality`: ceil-projection is the smallest F-element
≥ x. Used by `_toPositive` (directly) and by `_toZero` (`x ≤ 0` branch). -/
theorem ceil_minimality (F : FiniteFormat) (x : ℝ) {z : Dyadic}
    (hz_prec : Dyadic.precisionAtMost F.p z)
    (hz_quant : Dyadic.quantumAtLeast F.exp z) (hx_le_z : x ≤ (z : ℝ)) :
    (⌈x * (2 : ℝ) ^ (-(F.canonicalExp x))⌉ : ℝ) *
      (2 : ℝ) ^ (F.canonicalExp x) ≤ (z : ℝ) := by
  -- Reduce to floor_minimality via x ↦ -x, z ↦ -z.
  -- First: -z ∈ F.unbounded? Same precisionAtMost/quantumAtLeast.
  have h_neg_canon : F.canonicalExp (-x) = F.canonicalExp x := by
    unfold FiniteFormat.canonicalExp
    rcases hp : F.p with _ | p
    · rcases hexp : F.exp with _ | e' <;> simp
    · rcases hexp : F.exp with _ | e' <;> simp [abs_neg, neg_eq_zero]
  set e := F.canonicalExp x
  -- Build `(-z) ∈ F.unbounded`'s precision/quantum facts.
  have h_neg_z_prec : Dyadic.precisionAtMost F.p (-z) := by
    cases hp : F.p using ENat.recTopCoe with
    | top => trivial
    | coe p =>
      rw [hp] at hz_prec
      rw [Dyadic.precisionAtMost_coe_real] at hz_prec
      rw [Dyadic.precisionAtMost_coe_real]
      obtain ⟨a, e_a, hz_repr, ha_bound⟩ := hz_prec
      refine ⟨-a, e_a, ?_, ?_⟩
      · push_cast; rw [hz_repr]; ring
      · rwa [abs_neg]
  have h_neg_z_quant : Dyadic.quantumAtLeast F.exp (-z) := by
    cases hexp : F.exp using QExp.recBotCoe with
    | bot => trivial
    | coe e' =>
      rw [hexp, Dyadic.quantumAtLeast_coe_real] at hz_quant
      obtain ⟨k, hk⟩ := hz_quant
      rw [Dyadic.quantumAtLeast_coe_real]
      refine ⟨-k, ?_⟩
      push_cast; rw [hk]; ring
  have h_neg_le : ((-z : Dyadic) : ℝ) ≤ -x := by push_cast; linarith
  have hh := floor_minimality F (-x)
    h_neg_z_prec h_neg_z_quant h_neg_le
  rw [h_neg_canon] at hh
  -- hh : (-z) ≤ ⌊-x · 2^(-e)⌋ · 2^e. Now invert.
  have h_floor_eq : ⌊(-x) * (2 : ℝ) ^ (-e)⌋ = -⌈x * (2 : ℝ) ^ (-e)⌉ := by
    rw [show (-x) * (2 : ℝ) ^ (-e) = -(x * (2 : ℝ) ^ (-e)) by ring,
        Int.floor_neg]
  rw [h_floor_eq] at hh
  push_cast at hh
  linarith

/-- `Dyadic.ofIntZpow k e` is in `F.unbounded` provided `e ≥ F.exp` and (when
`F.p` is finite) `|k| ≤ 2^p`. The mantissa-bound boundary case `|k| = 2^p`
is handled by `precisionAtMost_of_abs_le`. -/
theorem ofIntZpow_mem_unbounded (F : FiniteFormat) {k e : ℤ}
    (he_ge : ∀ {e' : ℤ}, F.exp = (e' : QExp) → e' ≤ e)
    (hk_bound : ∀ {p : ℕ}, F.p = (p : Prec) →
      |k| ≤ (2 : ℤ) ^ p) :
    Dyadic.ofIntZpow k e ∈ F.unbounded := by
  refine ⟨?_, ?_, ?_⟩
  · change Dyadic.precisionAtMost F.p (Dyadic.ofIntZpow k e)
    cases hp : F.p using ENat.recTopCoe with
    | top => trivial
    | coe p =>
      exact Dyadic.precisionAtMost_of_abs_le (F.p_pos hp) k e
        (Dyadic.coe_rat_ofIntZpow k e) (hk_bound hp)
  · change Dyadic.quantumAtLeast F.exp (Dyadic.ofIntZpow k e)
    cases hexp : F.exp using QExp.recBotCoe with
    | bot => trivial
    | coe e' =>
      rw [Dyadic.quantumAtLeast_coe_real]
      have h_e_ge : e' ≤ e := he_ge hexp
      have h_diff_nn : 0 ≤ e - e' := by omega
      refine ⟨k * 2 ^ (e - e').toNat, ?_⟩
      rw [Dyadic.coe_ofIntZpow]
      have h_split : (2 : ℝ) ^ e = (2 : ℝ) ^ (e - e').toNat * (2 : ℝ) ^ e' := by
        rw [show ((2 : ℝ) ^ (e - e').toNat : ℝ) = (2 : ℝ) ^ ((e - e').toNat : ℤ)
            from (zpow_natCast _ _).symm, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
            Int.toNat_of_nonneg h_diff_nn]
        congr 1; ring
      rw [h_split, ← mul_assoc]
      push_cast
      ring
  · change Format.boundOK F.unbounded.b (Dyadic.ofIntZpow k e)
    rw [FiniteFormat.unbounded_b]; trivial

/-- Canonical-mantissa bound: `|x · 2^(-canonicalExp x)| < 2^p` when `F.p`
is finite. Drives the membership proofs for `floor`/`ceil`/`toZero`/`awayZero`
results across the satisfies theorems. -/
theorem floor_mantissa_lt {F : FiniteFormat} {x : ℝ}
    {p : ℕ} (hp : F.p = (p : Prec)) :
    |x * (2 : ℝ) ^ (-(F.canonicalExp x))| < (2 : ℝ) ^ p := by
  set e := F.canonicalExp x
  by_cases hx : x = 0
  · subst hx; simp
  · have h_e_ge : Int.log 2 |x| + 1 - (p : ℤ) ≤ e :=
      F.log_sub_p_le_canonicalExp hx hp
    have h_x_lt : |x| < (2 : ℝ) ^ (Int.log 2 |x| + 1) := by
      exact_mod_cast Int.lt_zpow_succ_log_self (b := 2)
        (by norm_num : (1 : ℕ) < 2) |x|
    have h_abs : |x * (2 : ℝ) ^ (-e)| = |x| * (2 : ℝ) ^ (-e) := by
      rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)]
    have hle : Int.log 2 |x| + 1 + (-e) ≤ (p : ℤ) := by
      linarith [h_e_ge]
    rw [h_abs]
    calc |x| * (2 : ℝ) ^ (-e)
        < (2 : ℝ) ^ (Int.log 2 |x| + 1) * (2 : ℝ) ^ (-e) :=
          mul_lt_mul_of_pos_right h_x_lt (zpow_pos (by norm_num) _)
      _ = (2 : ℝ) ^ (Int.log 2 |x| + 1 + (-e)) := by
          rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      _ ≤ (2 : ℝ) ^ (p : ℤ) := zpow_le_zpow_right₀ (by norm_num) hle
      _ = (2 : ℝ) ^ p := by rw [zpow_natCast]

/-- `canonicalExp` depends only on the binade `Int.log 2 |·|` (away from `0`):
equal logs give equal canonical exponents. -/
theorem canonicalExp_eq_of_log_eq (F : FiniteFormat) {y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0)
    (h : Int.log 2 |y| = Int.log 2 |z|) : F.canonicalExp y = F.canonicalExp z := by
  unfold FiniteFormat.canonicalExp
  cases F.p <;> cases F.exp <;> simp only [if_neg hy, if_neg hz, h]

/-- `canonicalExp` depends only on `|·|`, hence is negation-invariant. -/
theorem canonicalExp_neg (F : FiniteFormat) (x : ℝ) :
    F.canonicalExp (-x) = F.canonicalExp x := by
  unfold FiniteFormat.canonicalExp
  cases F.p <;> cases F.exp <;> simp only [abs_neg, neg_eq_zero]

end Mpfx
