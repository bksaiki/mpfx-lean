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

end Mpfx
