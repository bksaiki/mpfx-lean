import Mpfx.Grid

/-!
# Canonical exponent: closed forms and grid representation

Format-generic facts about `FiniteFormat.canonicalExp` (Flocq `cexp`), shared by
the operation-specific double-rounding proofs (addition, square root, …):

* `exists_canonical_rep` — a positive member as `c · 2^cexp` with `|c| < 2^p`;
* `canonicalExp_mono` — monotone in magnitude;
* `canonicalExp_closed` / `canonicalExp_FLX` / `canonicalExp_FLT` — the closed
  forms of `cexp` in the normal range, the FLX regime (`exp = ⊥`), and the FLT
  regime (`exp = emin` finite);
* `exp_le_canonicalExp_coe` — `F.exp ≤ cexp` uniformly over `exp = ⊥`/finite.
-/

namespace Mpfx

/-- **Canonical grid representation.** A positive `y ∈ F` (precision `p`) is
`c · 2^(canonicalExp y)` with `|c| < 2^p`. Unifies the `exp = ⊥` and finite-`exp`
grid lemmas (both have grid step `= canonicalExp`). -/
theorem exists_canonical_rep (F : FiniteFormat) {p : ℕ+}
    (hp : F.p = ((p : ℕ+) : WithTop ℕ+))
    {y : Dyadic} (hmem : y ∈ F) (hpos : 0 < (y : ℝ)) :
    ∃ c : ℤ, |c| < (2 : ℤ) ^ (p : ℕ) ∧
      (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ (F.canonicalExp (y : ℝ)) := by
  have hy_ne : (y : ℝ) ≠ 0 := ne_of_gt hpos
  obtain ⟨hprec, hquant, _⟩ := hmem
  cases hexp : F.exp with
  | bot =>
    obtain ⟨k, c, hc, hyeq, hk⟩ := exists_grid_rep_exp_bot F hp hprec hpos
    have hcexp : F.canonicalExp (y : ℝ) = Int.log 2 (y : ℝ) + 1 - (p : ℤ) := by
      unfold FiniteFormat.canonicalExp
      simp only [hp, hexp, hy_ne, abs_of_pos hpos, if_false]
    have hkexp : k = F.canonicalExp (y : ℝ) := by rw [hcexp, hk]; omega
    exact ⟨c, hc, by rw [← hkexp]; exact hyeq⟩
  | coe e =>
    obtain ⟨k, c, _, hc, hyeq, hk⟩ :=
      exists_grid_rep F hp hexp hprec (hexp ▸ hquant) hpos
    have hcexp : F.canonicalExp (y : ℝ)
        = max (Int.log 2 (y : ℝ) + 1 - (p : ℤ)) e := by
      unfold FiniteFormat.canonicalExp
      simp only [hp, hexp, hy_ne, abs_of_pos hpos, if_false]
    have hkexp : k = F.canonicalExp (y : ℝ) := by rw [hcexp, hk]; omega
    exact ⟨c, hc, by rw [← hkexp]; exact hyeq⟩

/-- `canonicalExp` is monotone in magnitude. -/
theorem canonicalExp_mono (F : FiniteFormat) {y z : ℝ} (hy : y ≠ 0)
    (hyz : |y| ≤ |z|) : F.canonicalExp y ≤ F.canonicalExp z := by
  have hy_pos : 0 < |y| := abs_pos.mpr hy
  have hz : z ≠ 0 := by
    rintro rfl; rw [abs_zero] at hyz; exact absurd hyz (not_le.mpr hy_pos)
  have hlog : Int.log 2 |y| ≤ Int.log 2 |z| := Int.log_mono_right hy_pos hyz
  unfold FiniteFormat.canonicalExp
  cases F.p with
  | top => cases F.exp <;> simp
  | coe p =>
    cases F.exp with
    | bot => simp only [hy, hz, if_false]; omega
    | coe e => simp only [hy, hz, if_false]; omega

/-- **Closed form of `canonicalExp` in the normal range** (unifies FLX and FLT).
When `v` is nonzero and its FLX exponent `log₂|v| + 1 − p` is at least the
format's minimum exponent `F.exp` (the *normal* regime — vacuous for `exp = ⊥`),
`canonicalExp` takes the FLX form. This is the single lemma that lets the FLX
proofs run unchanged for FLT: in the genuine-midpoint case all values are normal. -/
theorem canonicalExp_closed {F : FiniteFormat} {p : ℕ+}
    (hp : F.p = ((p : ℕ+) : WithTop ℕ+)) {v : ℝ} (hv : v ≠ 0)
    (hnorm : F.exp ≤ ((Int.log 2 |v| + 1 - (p : ℤ) : ℤ) : WithBot ℤ)) :
    F.canonicalExp v = Int.log 2 |v| + 1 - (p : ℤ) := by
  unfold FiniteFormat.canonicalExp
  cases hexp : F.exp with
  | bot => simp only [hp, hv, if_false]
  | coe e =>
    simp only [hp, hv, if_false]
    rw [hexp] at hnorm
    exact max_eq_left (by exact_mod_cast hnorm)

/-- Closed form of `canonicalExp` in an FLX format (`exp = ⊥`): `log₂|v| + 1 − p`
(the vacuous-normality special case of `canonicalExp_closed`). -/
theorem canonicalExp_FLX {F : FiniteFormat} {p : ℕ+}
    (hp : F.p = ((p : ℕ+) : WithTop ℕ+)) (hexp : F.exp = ⊥)
    {v : ℝ} (hv : v ≠ 0) : F.canonicalExp v = Int.log 2 |v| + 1 - (p : ℤ) :=
  canonicalExp_closed hp hv (by rw [hexp]; exact bot_le)

/-- Closed form of `canonicalExp` in an FLT format (`exp = emin` finite):
`max(log₂|v| + 1 − p, emin)`. -/
theorem canonicalExp_FLT {F : FiniteFormat} {p : ℕ+} {emin : ℤ}
    (hp : F.p = ((p : ℕ+) : WithTop ℕ+)) (hexp : F.exp = (emin : WithBot ℤ))
    {v : ℝ} (hv : v ≠ 0) :
    F.canonicalExp v = max (Int.log 2 |v| + 1 - (p : ℤ)) emin := by
  unfold FiniteFormat.canonicalExp; simp only [hp, hexp, hv, if_false]

/-- `F.exp ≤ (F.canonicalExp x : WithBot ℤ)`, uniformly over `exp = ⊥`/finite. -/
theorem exp_le_canonicalExp_coe (F : FiniteFormat) (x : ℝ) :
    F.exp ≤ ((F.canonicalExp x : ℤ) : WithBot ℤ) := by
  cases hexp : F.exp with
  | bot => exact bot_le
  | coe e => exact_mod_cast F.exp_le_canonicalExp x hexp

/-- The FLX exponent lower-bounds `canonicalExp`: `log₂|v| + 1 − p ≤ canonicalExp v`
(equality for `exp = ⊥`; `≤` via `le_max_left` for finite `exp`). -/
theorem log_sub_prec_le_canonicalExp {F : FiniteFormat} {p : ℕ+}
    (hp : F.p = ((p : ℕ+) : WithTop ℕ+)) {v : ℝ} (hv : v ≠ 0) :
    Int.log 2 |v| + 1 - (p : ℤ) ≤ F.canonicalExp v := by
  cases hexp : F.exp with
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
theorem quantumAtLeast_neg {e : WithBot ℤ} {a : Dyadic}
    (ha : Dyadic.quantumAtLeast e a) : Dyadic.quantumAtLeast e (-a) := by
  cases e with
  | bot => trivial
  | coe e =>
    obtain ⟨ca, hca⟩ := (Dyadic.quantumAtLeast_coe_real e a).mp ha
    refine (Dyadic.quantumAtLeast_coe_real e (-a)).mpr ⟨-ca, ?_⟩
    rw [show ((-a : Dyadic) : ℝ) = -(a : ℝ) from by push_cast; ring, hca]; push_cast; ring

/-- A sum of two quantum-aligned dyadics stays quantum-aligned. -/
theorem quantumAtLeast_add {e : WithBot ℤ} {a b : Dyadic}
    (ha : Dyadic.quantumAtLeast e a) (hb : Dyadic.quantumAtLeast e b) :
    Dyadic.quantumAtLeast e (a + b) := by
  cases e with
  | bot => trivial
  | coe e =>
    obtain ⟨ca, hca⟩ := (Dyadic.quantumAtLeast_coe_real e a).mp ha
    obtain ⟨cb, hcb⟩ := (Dyadic.quantumAtLeast_coe_real e b).mp hb
    refine (Dyadic.quantumAtLeast_coe_real e (a + b)).mpr ⟨ca + cb, ?_⟩
    rw [show ((a + b : Dyadic) : ℝ) = (a : ℝ) + (b : ℝ) from by push_cast; ring, hca, hcb]
    push_cast; ring

/-- A difference of two quantum-aligned dyadics stays quantum-aligned. -/
theorem quantumAtLeast_sub {e : WithBot ℤ} {a b : Dyadic}
    (ha : Dyadic.quantumAtLeast e a) (hb : Dyadic.quantumAtLeast e b) :
    Dyadic.quantumAtLeast e (a - b) := by
  rw [sub_eq_add_neg]; exact quantumAtLeast_add ha (quantumAtLeast_neg hb)

/-- A product is quantum-aligned at the *sum* of the operands' quanta. -/
theorem quantumAtLeast_mul {e₁ e₂ : WithBot ℤ} {x y : Dyadic}
    (hx : Dyadic.quantumAtLeast e₁ x) (hy : Dyadic.quantumAtLeast e₂ y) :
    Dyadic.quantumAtLeast (e₁ + e₂) (x * y) := by
  cases e₁ with
  | bot => rw [show (⊥ + e₂ : WithBot ℤ) = ⊥ from by simp]; trivial
  | coe a =>
    cases e₂ with
    | bot => rw [show ((a : WithBot ℤ) + ⊥) = ⊥ from by simp]; trivial
    | coe b =>
      obtain ⟨cx, hcx⟩ := (Dyadic.quantumAtLeast_coe_real a x).mp hx
      obtain ⟨cy, hcy⟩ := (Dyadic.quantumAtLeast_coe_real b y).mp hy
      rw [← WithBot.coe_add]
      refine (Dyadic.quantumAtLeast_coe_real (a + b) (x * y)).mpr ⟨cx * cy, ?_⟩
      rw [show ((x * y : Dyadic) : ℝ) = (x : ℝ) * (y : ℝ) from by push_cast; ring, hcx, hcy,
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; push_cast; ring

end Mpfx
