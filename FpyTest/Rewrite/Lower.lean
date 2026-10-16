import Fpy.Rewrite.Lower

/-!
# Overflow's threshold on MX E4M3

Under round to nearest, ties to even, MX E4M3 overflows exactly beyond `±464`
(§5.2): the tie at `464` rounds to `448`, whose significand is even, and every
larger input rounds to at least `480`. This discharges Overflow's threshold form.
-/

namespace FpyTest

open Fpy Mpfx

/-- MX E4M3: 4 digits, minimum quantum `2⁻⁹`, largest value `448`. -/
def e4m3 : FiniteFormat where
  p := (4 : ℕ)
  exp := ((-9 : ℤ) : QExp)
  b := (⟨Mpfx.Dyadic.ofIntZpow 448 0, by simp⟩ : NonNegDyadic)
  specials := {.nan}
  finite := Or.inl (by simp)
  pos := by simp

theorem e4m3_defined : ¬ e4m3.IsUndefined (.nearest .toEven) :=
  not_isUndefined_of_two_le_p (by simp [e4m3]; norm_num)

/-- RNE into E4M3. -/
noncomputable abbrev rne (y : ℝ) : ℝ :=
  (rndUnbounded e4m3 (.nearest .toEven) y e4m3_defined : Mpfx.Dyadic)

theorem e4m3_cexp {y : ℝ} (h₁ : 256 ≤ y) (h₂ : y < 512) : e4m3.canonicalExp y = 5 := by
  rw [canonicalExp_expFinite (p := 4) rfl rfl (by linarith), abs_of_pos (by linarith),
    log_eq_of_zpow_bounds (k := 8) (by linarith) (by norm_num; linarith) (by norm_num; linarith)]
  norm_num

theorem rne_eq {y : ℝ} (h₁ : 256 ≤ y) (h₂ : y < 512) :
    rne y = (rndInt e4m3 (.nearest .toEven) y 5 : ℝ) * 32 := by
  unfold rne rndUnbounded
  rw [e4m3_cexp h₁ h₂, Mpfx.Dyadic.coe_ofIntZpow]
  norm_num

/-- The tie at `464` rounds to `448 = 14 · 2⁵`, whose significand is even. -/
theorem rne_464 : rne 464 = 448 := by
  rw [rne_eq (by norm_num) (by norm_num)]
  have hs : (464 : ℝ) * 2 ^ (-(5 : ℤ)) = 29 / 2 := by norm_num
  have hfl : ⌊(29 / 2 : ℝ)⌋ = 14 := by norm_num [Int.floor_eq_iff]
  have hce := e4m3_cexp (y := 464) (by norm_num) (by norm_num)
  have heven : e4m3.IsEven (Mpfx.Dyadic.ofIntZpow 14 5) := by
    have h := isEven_neighbor_iff (F := e4m3) (by simp [e4m3]) (x := 464)
      (by rw [hce, hs, hfl]; norm_num) (Or.inl rfl)
    rw [hce, hs, hfl] at h
    exact h.mpr ⟨7, by norm_num⟩
  unfold rndInt
  dsimp only
  rw [hs, hfl, if_neg (by norm_num), if_neg (by norm_num), if_pos heven]
  norm_num

/-- Inputs past the midpoint `464` round up to `480`. -/
theorem rne_above {y : ℝ} (h₁ : 464 < y) (h₂ : y < 480) : rne y = 480 := by
  rw [rne_eq (by linarith) (by linarith)]
  have hfl : ⌊y * 2 ^ (-(5 : ℤ))⌋ = 14 := by
    rw [Int.floor_eq_iff]
    constructor <;> norm_num <;> linarith
  unfold rndInt
  dsimp only
  rw [hfl, if_neg (by norm_num; linarith), if_pos (by norm_num; linarith)]
  norm_num

theorem rne_neg (y : ℝ) : rne (-y) = -rne y := by
  have h := (RoundsFinite.neg_nearest e4m3.unbounded .toEven y _).mp
    (rndUnbounded_satisfies e4m3 _ y e4m3_defined)
  unfold rne
  rw [RoundsFinite.unique e4m3_defined (rndUnbounded_satisfies _ _ _ _) h,
    Mpfx.Dyadic.coe_real_neg]

theorem rne_ge {y : ℝ} (hy : 464 < y) : 480 ≤ rne y := by
  rcases lt_or_ge y 480 with h | h
  · rw [rne_above hy h]
  · calc (480 : ℝ) = rne 470 := (rne_above (by norm_num) (by norm_num)).symm
      _ ≤ rne y := RoundsFinite.mono e4m3_defined (by linarith)
          (rndUnbounded_satisfies _ _ _ _) (rndUnbounded_satisfies _ _ _ _)

theorem boundOK_e4m3 (d : Mpfx.Dyadic) : Format.boundOK e4m3.b d ↔ |(d : ℝ)| ≤ 448 := by
  change |(d : ℚ)| ≤ ((Mpfx.Dyadic.ofIntZpow 448 0 : Mpfx.Dyadic) : ℚ) ↔ _
  rw [Mpfx.Dyadic.coe_rat_ofIntZpow, Mpfx.Dyadic.coe_real_eq_ratCast, ← Rat.cast_abs]
  norm_num
  exact_mod_cast Iff.rfl

/-- **The `464` example**: E4M3 under RNE overflows exactly beyond `±464`. -/
theorem e4m3_overflows_iff (y : ℝ) : Overflows e4m3 (.nearest .toEven) y ↔ y < -464 ∨ 464 < y := by
  refine overflows_iff_of_threshold e4m3_defined ?_ ?_ (fun y hy => ?_) y
  · rw [boundOK_e4m3]
    change |rne (-464)| ≤ 448
    rw [rne_neg, rne_464]
    norm_num
  · rw [boundOK_e4m3]
    change |rne 464| ≤ 448
    rw [rne_464]
    norm_num
  · rw [boundOK_e4m3, not_le]
    change 448 < |rne y|
    rcases hy with hy | hy
    · have h := rne_neg (-y)
      rw [neg_neg] at h
      rw [h, abs_neg]
      exact lt_of_lt_of_le (by norm_num) ((rne_ge (by linarith)).trans (le_abs_self _))
    · exact lt_of_lt_of_le (by norm_num) ((rne_ge hy).trans (le_abs_self _))

/-- Overflow's threshold form for an E4M3 context under RNE. -/
example {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
    {D : FormatDomain} {Γ : AEnv D} {C : Val} {c : RoundCtx} {x t : Var}
    (hC : C.rnd (fpy decode) = some c.round) (hF : c.F = e4m3) (hrm : c.rm = .nearest .toEven)
    (hfin : ∀ σ, Γ.Holds σ → ∀ u, σ t = some (.num u) → ∃ y, u = .finite y) :
    Equiv Φ ∅ Γ (some C) (.assign x (.arithOp .round [.var t]))
      (.ite (.exactOp .lt [.var t, .num (.finite (-464))]) (.assign x (.num (c.O.map true).toReal))
        (.ite (.exactOp .lt [.num (.finite 464), .var t])
          (.assign x (.num (c.O.map false).toReal)) (.assign x (.arithOp .round [.var t])))) :=
  equiv_overflow_threshold hC (by norm_num) (fun y => by rw [hF, hrm]; exact e4m3_overflows_iff y)
    hfin

end FpyTest
