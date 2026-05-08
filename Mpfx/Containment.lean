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

/-- `F ⊆ F.extend k`: every value of `F` is also a value of the format with
`k` more bits of precision and `k` smaller minimum quantum. -/
theorem self_subset_extend (F : AbstractFormat) (k : ℕ) : F ⊆ F.extend k := by
  apply containsPrec
  · change F.p ≤ F.p + k
    cases F.p with
    | top => simp
    | coe n =>
      change ((n : ℕ) : ℕ∞) ≤ ((n + k : ℕ) : ℕ∞)
      exact_mod_cast Nat.le_add_right n k
  · change F.exp.map (· - (k : ℤ)) ≤ F.exp
    cases F.exp with
    | bot => simp
    | coe e =>
      change ((e - k : ℤ) : WithBot ℤ) ≤ ((e : ℤ) : WithBot ℤ)
      exact WithBot.coe_le_coe.mpr (by linarith)
  · exact le_refl _

/-- Monotonicity of `extend`: `F.extend j ⊆ F.extend k` whenever `j ≤ k`. -/
theorem extend_mono (F : AbstractFormat) {j k : ℕ} (h : j ≤ k) :
    F.extend j ⊆ F.extend k := by
  apply containsPrec
  · change F.p + j ≤ F.p + k
    cases F.p with
    | top => simp
    | coe n =>
      change ((n + j : ℕ) : ℕ∞) ≤ ((n + k : ℕ) : ℕ∞)
      exact_mod_cast (by omega : n + j ≤ n + k)
  · change F.exp.map (· - (k : ℤ)) ≤ F.exp.map (· - (j : ℤ))
    cases F.exp with
    | bot => simp
    | coe e =>
      change ((e - k : ℤ) : WithBot ℤ) ≤ ((e - j : ℤ) : WithBot ℤ)
      exact WithBot.coe_le_coe.mpr (by linarith)
  · exact le_refl _

/-- **𝒜-Contains-Sub** (Fig. 8). If `F₁`'s bound is small enough that all
values of `F₁` fit in `F₂.p` bits at exponent `exp₁`, plus the standard
quantum and bound orderings, then `F₁ ⊆ F₂`. Covers the degenerate-format
case where `F₁.p > F₂.p` is allowed because `F₁`'s bound is so small that
nothing in `F₁` actually uses more than `F₂.p` bits. Requires `F₁.exp` and
`F₂.p` finite. -/
theorem containsSub {F₁ F₂ : AbstractFormat}
    {exp₁ : ℤ} (he₁ : F₁.exp = (exp₁ : WithBot ℤ))
    {p₂ : ℕ} (hp₂ : F₂.p = (p₂ : ℕ∞))
    (hbprec : F₁.b ≤
      ((Dyadic.ofIntZpow 1 (exp₁ + (p₂ : ℤ)) : Dyadic) : WithTop Dyadic))
    (he : F₂.exp ≤ F₁.exp)
    (hb : F₁.b ≤ F₂.b) :
    F₁ ⊆ F₂ := by
  intro x hx
  obtain ⟨_, hex, hbx⟩ := hx
  have hp₂_pos : 1 ≤ p₂ := by
    have := F₂.p_pos; rw [hp₂] at this; exact_mod_cast this
  have hex_coe : Dyadic.quantumAtLeast (exp₁ : WithBot ℤ) x := by
    rw [← he₁]; exact hex
  obtain ⟨c, hx_eq⟩ := hex_coe
  -- |x| ≤ 2^(exp₁ + p₂), via the bound on F₁.b.
  have hbx' : |(x : ℝ)| ≤ (2 : ℝ) ^ (exp₁ + (p₂ : ℤ)) := by
    have h_bnd : AbstractFormat.boundOK
        ((Dyadic.ofIntZpow 1 (exp₁ + (p₂ : ℤ)) : Dyadic) : WithTop Dyadic) x :=
      boundOK_mono hbprec hbx
    have : |(x : ℝ)| ≤ ((Dyadic.ofIntZpow 1 (exp₁ + (p₂ : ℤ)) : Dyadic) : ℝ) := h_bnd
    rw [Dyadic.coe_ofIntZpow] at this
    push_cast at this
    rwa [one_mul] at this
  have hc_le_real : |(c : ℝ)| ≤ (2 : ℝ) ^ (p₂ : ℤ) := by
    have h1 : |(c : ℝ)| * (2 : ℝ) ^ exp₁ ≤ (2 : ℝ) ^ (exp₁ + (p₂ : ℤ)) := by
      calc |(c : ℝ)| * (2 : ℝ) ^ exp₁
          = |(x : ℝ)| := by rw [hx_eq, abs_mul_two_zpow]
        _ ≤ (2 : ℝ) ^ (exp₁ + (p₂ : ℤ)) := hbx'
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
  · -- precisionAtMost F₂.p x
    rw [hp₂]
    exact Dyadic.precisionAtMost_of_abs_le hp₂_pos c exp₁ hx_eq hc_le
  · -- quantumAtLeast F₂.exp x
    exact Dyadic.quantumAtLeast_anti he hex
  · -- boundOK F₂.b x
    exact boundOK_mono hb hbx

end AbstractFormat

end Mpfx
