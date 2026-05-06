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

end AbstractFormat

end Mpfx
