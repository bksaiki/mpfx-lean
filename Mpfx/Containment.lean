import Mpfx.Format

/-!
# Format containment

Soundness of the two inference rules from §5.1 / Fig. 8:

* `containsPrec`  — `𝒜-Contains-Prec`: covers the general case.
* `containsSub`   — `𝒜-Contains-Sub`: covers degenerate floating-point formats.
-/

namespace Mpfx

namespace AbstractFormat

/-- Format inclusion: every value of `F₁` is also a value of `F₂`. -/
def Subset (F₁ F₂ : AbstractFormat) : Prop := ∀ x : Dyadic, x ∈ F₁ → x ∈ F₂

instance : HasSubset AbstractFormat := ⟨Subset⟩

theorem subset_def (F₁ F₂ : AbstractFormat) :
    F₁ ⊆ F₂ ↔ ∀ x : Dyadic, x ∈ F₁ → x ∈ F₂ := Iff.rfl

theorem boundOK_mono {b₁ b₂ : WithTop Dyadic} (h : b₁ ≤ b₂) {x : Dyadic} :
    boundOK b₁ x → boundOK b₂ x := by
  match b₁, b₂ with
  | _, ⊤ => intro _; trivial
  | ⊤, (_ : Dyadic) => simp at h
  | (d₁ : Dyadic), (d₂ : Dyadic) =>
    intro hx
    have hd : d₁ ≤ d₂ := WithTop.coe_le_coe.mp h
    exact le_trans hx hd

/-- **𝒜-Contains-Prec** (Fig. 8). If `p₁ ≤ p₂`, `exp₂ ≤ exp₁`, and `b₁ ≤ b₂`,
then `𝒜(p₁, exp₁, b₁) ⊆ 𝒜(p₂, exp₂, b₂)`. -/
theorem containsPrec {F₁ F₂ : AbstractFormat}
    (hp : F₁.p ≤ F₂.p) (he : F₂.exp ≤ F₁.exp) (hb : F₁.b ≤ F₂.b) :
    F₁ ⊆ F₂ := by
  intro x hx
  obtain ⟨hpx, hex, hbx⟩ := hx
  refine ⟨?_, ?_, ?_⟩
  · exact Dyadic.precisionAtMost_mono hp hpx
  · exact Dyadic.quantumAtLeast_anti he hex
  · exact boundOK_mono hb hbx

/-- **𝒜-Contains-Sub** (Fig. 8). If `b₁ ≤ 2^(exp₁ + p₂)`, `exp₂ ≤ exp₁`, and
`b₁ ≤ b₂`, then `𝒜(p₁, exp₁, b₁) ⊆ 𝒜(p₂, exp₂, b₂)`. Requires `p₂ ≥ 1`, a
finite `exp₁ : ℤ`, a finite `β₁ : Dyadic`, and the non-degeneracy condition
`p₂ ≠ 1 ∨ exp₂ ≠ ⊥`. The non-negative-bound invariants `hβ` and `hb_nn` are
required to construct the underlying `AbstractFormat`s. -/
theorem containsSub {p₁ : ℕ∞} {p₂ : ℕ} {exp₁ : ℤ} {exp₂ : WithBot ℤ}
    {β₁ : Dyadic} {b₂ : WithTop Dyadic}
    (hp₁ : 1 ≤ p₁)
    (hp₂ : 1 ≤ p₂)
    (hnd₂ : p₂ ≠ 1 ∨ exp₂ ≠ ⊥)
    (hβ : 0 ≤ (β₁ : ℝ))
    (hb_nn : ∀ d : Dyadic, b₂ = ↑d → 0 ≤ (d : ℝ))
    (hbprec : (β₁ : ℝ) ≤ (2 : ℝ) ^ (exp₁ + (p₂ : ℤ)))
    (he : exp₂ ≤ (exp₁ : WithBot ℤ))
    (hb : (β₁ : WithTop Dyadic) ≤ b₂) :
    ({ p := p₁, exp := (exp₁ : WithBot ℤ), b := (β₁ : WithTop Dyadic),
       p_pos := hp₁,
       not_degenerate := Or.inr (by simp),
       b_nn := fun d hd => by
         have : d = β₁ := by exact_mod_cast hd.symm
         rw [this]; exact hβ } : AbstractFormat)
      ⊆ { p := (p₂ : ℕ∞), exp := exp₂, b := b₂,
          p_pos := by exact_mod_cast hp₂,
          not_degenerate := by
            rcases hnd₂ with hne1 | hexp_ne
            · refine Or.inl ⟨by simp, ?_⟩
              intro h
              exact hne1 (by exact_mod_cast h)
            · exact Or.inr hexp_ne,
          b_nn := hb_nn } := by
  intro x hx
  obtain ⟨_, hex, hbx⟩ := hx
  obtain ⟨c, hx_eq⟩ := hex
  have hbx' : |(x : ℝ)| ≤ (β₁ : ℝ) := hbx
  have hc_le_real : |(c : ℝ)| ≤ (2 : ℝ) ^ (p₂ : ℤ) := by
    have h1 : |(c : ℝ)| * (2 : ℝ) ^ exp₁ ≤ (2 : ℝ) ^ (exp₁ + (p₂ : ℤ)) := by
      calc |(c : ℝ)| * (2 : ℝ) ^ exp₁
          = |(x : ℝ)| := by rw [hx_eq, abs_mul_two_zpow]
        _ ≤ (β₁ : ℝ) := hbx'
        _ ≤ (2 : ℝ) ^ (exp₁ + (p₂ : ℤ)) := hbprec
    have h2 : (2 : ℝ) ^ (exp₁ + (p₂ : ℤ)) = (2 : ℝ) ^ (p₂ : ℤ) * (2 : ℝ) ^ exp₁ := by
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; ring
    rw [h2] at h1
    exact le_of_mul_le_mul_right h1 (two_zpow_pos exp₁)
  have hc_le : |c| ≤ (2 : ℤ) ^ p₂ := by
    have : ((|c| : ℤ) : ℝ) ≤ (((2 : ℤ) ^ p₂ : ℤ) : ℝ) := by
      rw [Int.cast_abs]
      push_cast
      simp only [← zpow_natCast (2 : ℝ) p₂]
      exact hc_le_real
    exact_mod_cast this
  refine ⟨?_, ?_, ?_⟩
  · exact Dyadic.precisionAtMost_of_abs_le (by omega : 1 ≤ p₂) c exp₁ hx_eq hc_le
  · exact Dyadic.quantumAtLeast_anti he ⟨c, hx_eq⟩
  · exact boundOK_mono hb hbx

end AbstractFormat

end Mpfx
