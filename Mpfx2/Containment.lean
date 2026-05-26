import Mpfx2.Format

/-!
# Format containment (§5.1, Fig. 8)

Soundness of the two inference rules:

* `containsPrec` — `𝒜-Contains-Prec`: the general monotone case.
* `containsSub`  — `𝒜-Contains-Sub`: the degenerate case where `F₁`'s bound
  is small enough that nothing in `F₁` uses more than `F₂.p` bits, so
  `F₁.p > F₂.p` is permitted.

Both are stated for `Format` and proved entirely over `ℚ`.
-/

namespace Mpfx2

namespace Format

/-- Format inclusion: every value of `F₁` is also a value of `F₂`. -/
def Subset (F₁ F₂ : Format) : Prop := ∀ x : Dyadic, x ∈ F₁ → x ∈ F₂

instance : HasSubset Format := ⟨Subset⟩

/-- The magnitude-bound check is monotone in the bound. -/
theorem boundOK_mono {b₁ b₂ : WithTop NonNegDyadic} (h : b₁ ≤ b₂) {x : Dyadic} :
    boundOK b₁ x → boundOK b₂ x := by
  match b₁, b₂ with
  | _, ⊤ => intro _; trivial
  | ⊤, (_ : NonNegDyadic) => exact absurd (top_le_iff.mp h) WithTop.coe_ne_top
  | (d₁ : NonNegDyadic), (d₂ : NonNegDyadic) =>
    intro hx
    have h12 : d₁ ≤ d₂ := WithTop.coe_le_coe.mp h
    have hd : ((d₁.val : Dyadic) : ℚ) ≤ ((d₂.val : Dyadic) : ℚ) := by
      exact_mod_cast h12
    exact le_trans hx hd

/-- **𝒜-Contains-Prec** (Fig. 8). If `p₁ ≤ p₂`, `exp₂ ≤ exp₁`, and `b₁ ≤ b₂`,
then `𝒜(p₁, exp₁, b₁) ⊆ 𝒜(p₂, exp₂, b₂)`. -/
theorem containsPrec {F₁ F₂ : Format}
    (hp : F₁.p ≤ F₂.p) (he : F₂.exp ≤ F₁.exp) (hb : F₁.b ≤ F₂.b) :
    F₁ ⊆ F₂ := by
  intro x hx
  obtain ⟨hpx, hex, hbx⟩ := hx
  exact ⟨Dyadic.precisionAtMost_mono hp hpx,
         Dyadic.quantumAtLeast_anti he hex,
         boundOK_mono hb hbx⟩

/-- The non-negative dyadic `2 ^ e = 1 · 2^e`. -/
def nnPow (e : ℤ) : NonNegDyadic :=
  ⟨Dyadic.ofIntZpow 1 e, by rw [Dyadic.coe_rat_ofIntZpow]; positivity⟩

@[simp] theorem coe_nnPow (e : ℤ) : ((nnPow e).val : ℚ) = (2 : ℚ) ^ e := by
  change ((Dyadic.ofIntZpow 1 e : Dyadic) : ℚ) = _
  rw [Dyadic.coe_rat_ofIntZpow]; push_cast; ring

/-- **𝒜-Contains-Sub** (Fig. 8). If `F₁`'s bound is at most `2^(exp₁ + p₂)`
(so every value of `F₁` fits in `F₂.p = p₂` bits at exponent `exp₁`), plus
the standard quantum and bound orderings, then `F₁ ⊆ F₂` — even when
`F₁.p > F₂.p`. -/
theorem containsSub {F₁ F₂ : Format}
    {exp₁ : ℤ} (he₁ : F₁.exp = (exp₁ : WithBot ℤ))
    {p₂ : ℕ+} (hp₂ : F₂.p = ((p₂ : ℕ+) : WithTop ℕ+))
    (hbprec : F₁.b ≤ ((nnPow (exp₁ + (p₂ : ℤ)) : NonNegDyadic) : WithTop NonNegDyadic))
    (he : F₂.exp ≤ F₁.exp)
    (hb : F₁.b ≤ F₂.b) :
    F₁ ⊆ F₂ := by
  intro x hx
  obtain ⟨_, hex, hbx⟩ := hx
  -- x = c · 2^exp₁.
  have hex_coe : Dyadic.quantumAtLeast (exp₁ : WithBot ℤ) x := by rw [← he₁]; exact hex
  obtain ⟨c, hx_eq⟩ := (Dyadic.quantumAtLeast_coe exp₁ x).mp hex_coe
  -- |x| ≤ 2^(exp₁ + p₂), from the bound on F₁.b.
  have hbx' : |(x : ℚ)| ≤ (2 : ℚ) ^ (exp₁ + (p₂ : ℤ)) := by
    have h_bnd := boundOK_mono hbprec hbx
    rw [show boundOK _ x = (|(x : ℚ)| ≤ ((nnPow (exp₁ + (p₂ : ℤ))).val : ℚ)) from rfl] at h_bnd
    rwa [coe_nnPow] at h_bnd
  -- |c| ≤ 2^p₂.
  have h2exp_pos : (0 : ℚ) < (2 : ℚ) ^ exp₁ := zpow_pos (by norm_num) _
  have hc_le_rat : |(c : ℚ)| ≤ (2 : ℚ) ^ (p₂ : ℤ) := by
    have h1 : |(c : ℚ)| * (2 : ℚ) ^ exp₁ ≤ (2 : ℚ) ^ (exp₁ + (p₂ : ℤ)) := by
      calc |(c : ℚ)| * (2 : ℚ) ^ exp₁
          = |(c : ℚ) * (2 : ℚ) ^ exp₁| := by
            rw [abs_mul, abs_of_pos h2exp_pos]
        _ = |(x : ℚ)| := by rw [hx_eq]
        _ ≤ (2 : ℚ) ^ (exp₁ + (p₂ : ℤ)) := hbx'
    have h2 : (2 : ℚ) ^ (exp₁ + (p₂ : ℤ)) = (2 : ℚ) ^ (p₂ : ℤ) * (2 : ℚ) ^ exp₁ := by
      rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]; ring
    rw [h2] at h1
    exact le_of_mul_le_mul_right h1 h2exp_pos
  have hc_le : |c| ≤ (2 : ℤ) ^ (p₂ : ℕ) := by
    have : ((|c| : ℤ) : ℚ) ≤ (((2 : ℤ) ^ (p₂ : ℕ) : ℤ) : ℚ) := by
      rw [Int.cast_abs]; push_cast
      simp only [← zpow_natCast (2 : ℚ) (p₂ : ℕ)]
      exact hc_le_rat
    exact_mod_cast this
  refine ⟨?_, ?_, ?_⟩
  · rw [hp₂]; exact Dyadic.precisionAtMost_of_abs_le c exp₁ hx_eq hc_le
  · exact Dyadic.quantumAtLeast_anti he hex
  · exact boundOK_mono hb hbx

end Format

end Mpfx2
