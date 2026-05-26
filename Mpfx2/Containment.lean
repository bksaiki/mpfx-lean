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

/-! ### Format extension

`F.extend k` adds `k` bits of precision and lowers the minimum quantum by
`k` (bound unchanged). Used by §5.2 to phrase the double-rounding rules'
intermediate formats `A(p₁ + k, exp₁ − k, b₁)`. -/

/-- Extend `F` by `k` bits: `p ↦ p + k`, `exp ↦ exp − k`, `b` unchanged. -/
def extend (F : Format) (k : ℕ+) : Format where
  p := F.p.map (· + k)
  exp := F.exp.map (· - (k : ℤ))
  b := F.b

@[simp] theorem extend_b (F : Format) (k : ℕ+) : (F.extend k).b = F.b := rfl

/-- `F ⊆ F.extend k`: extending only relaxes the precision and quantum
constraints. -/
theorem self_subset_extend (F : Format) (k : ℕ+) : F ⊆ F.extend k := by
  apply containsPrec
  · change F.p ≤ F.p.map (· + k)
    cases F.p with
    | top => simp
    | coe n =>
      rw [WithTop.map_coe]
      exact WithTop.coe_le_coe.mpr (by exact_mod_cast Nat.le_add_right (n : ℕ) (k : ℕ))
  · change F.exp.map (· - (k : ℤ)) ≤ F.exp
    cases F.exp with
    | bot => simp
    | coe e =>
      rw [WithBot.map_coe]
      exact WithBot.coe_le_coe.mpr (sub_le_self e (by positivity))
  · exact le_refl _

/-- `extend` is monotone in the bit count: `F.extend j ⊆ F.extend k` when `j ≤ k`. -/
theorem extend_mono (F : Format) {j k : ℕ+} (h : j ≤ k) :
    F.extend j ⊆ F.extend k := by
  apply containsPrec
  · change F.p.map (· + j) ≤ F.p.map (· + k)
    cases F.p with
    | top => simp
    | coe n =>
      rw [WithTop.map_coe, WithTop.map_coe]
      refine WithTop.coe_le_coe.mpr ?_
      have hjk : (j : ℕ) ≤ (k : ℕ) := by exact_mod_cast h
      exact_mod_cast Nat.add_le_add_left hjk (n : ℕ)
  · change F.exp.map (· - (k : ℤ)) ≤ F.exp.map (· - (j : ℤ))
    cases F.exp with
    | bot => simp
    | coe e =>
      rw [WithBot.map_coe, WithBot.map_coe]
      have hjk : (j : ℤ) ≤ (k : ℤ) := by exact_mod_cast h
      exact WithBot.coe_le_coe.mpr (by omega)
  · exact le_refl _

end Format

namespace FiniteFormat

/-- Extend a `FiniteFormat` by `k` bits. The `finite` invariant is preserved:
`extend` only grows `p` (a finite `p` stays finite) and only shrinks `exp`
(a finite `exp` stays finite). -/
def extend (F : FiniteFormat) (k : ℕ+) : FiniteFormat where
  toFormat := F.toFormat.extend k
  finite := by
    rcases F.finite with hp | he
    · left
      change F.toFormat.p.map (· + k) ≠ ⊤
      cases hF : F.toFormat.p with
      | top => exact absurd hF hp
      | coe n => rw [WithTop.map_coe]; exact WithTop.coe_ne_top
    · right
      change F.toFormat.exp.map (· - (k : ℤ)) ≠ ⊥
      cases hF : F.toFormat.exp with
      | bot => exact absurd hF he
      | coe e => rw [WithBot.map_coe]; exact WithBot.coe_ne_bot

@[simp] theorem extend_toFormat (F : FiniteFormat) (k : ℕ+) :
    (F.extend k).toFormat = F.toFormat.extend k := rfl

/-- **Lemma 5.2**: extending `F` by `k` increases the digit count of every
nonzero `x` by exactly `k`. -/
theorem numDigits_extend (F : FiniteFormat) (k : ℕ+) {x : ℝ} (hx : x ≠ 0) :
    (F.extend k).numDigits x = F.numDigits x + k := by
  have hp_ext : (F.extend k).toFormat.p = F.toFormat.p.map (· + k) := rfl
  have he_ext : (F.extend k).toFormat.exp = F.toFormat.exp.map (· - (k : ℤ)) := rfl
  cases hp : F.toFormat.p with
  | top =>
    cases hexp : F.toFormat.exp with
    | bot =>
      exfalso; rcases F.finite with h | h
      · exact h hp
      · exact h hexp
    | coe e' =>
      have hpe : (F.extend k).toFormat.p = ⊤ := by rw [hp_ext, hp]; rfl
      have hee : (F.extend k).toFormat.exp = ((e' - (k : ℤ) : ℤ) : WithBot ℤ) := by
        rw [he_ext, hexp, WithBot.map_coe]
      rw [F.numDigits_top_coe hx hexp hp,
          (F.extend k).numDigits_top_coe hx hee hpe]
      ring
  | coe n =>
    cases hexp : F.toFormat.exp with
    | bot =>
      have hpe : (F.extend k).toFormat.p = (((n + k : ℕ+)) : WithTop ℕ+) := by
        rw [hp_ext, hp, WithTop.map_coe]
      have hee : (F.extend k).toFormat.exp = ⊥ := by rw [he_ext, hexp]; rfl
      rw [F.numDigits_coe_bot hx hp hexp,
          (F.extend k).numDigits_coe_bot hx hpe hee]
      push_cast; ring
    | coe e' =>
      have hpe : (F.extend k).toFormat.p = (((n + k : ℕ+)) : WithTop ℕ+) := by
        rw [hp_ext, hp, WithTop.map_coe]
      have hee : (F.extend k).toFormat.exp = ((e' - (k : ℤ) : ℤ) : WithBot ℤ) := by
        rw [he_ext, hexp, WithBot.map_coe]
      rw [F.numDigits_coe_coe hx hp hexp,
          (F.extend k).numDigits_coe_coe hx hpe hee]
      have hnk : (((n + k : ℕ+) : ℕ) : ℤ) = (n : ℤ) + (k : ℤ) := by push_cast; ring
      rw [hnk]
      have hlog : Int.log 2 |x| - (e' - (k : ℤ)) + 1
          = Int.log 2 |x| - e' + 1 + (k : ℤ) := by ring
      rw [hlog]; omega

end FiniteFormat

end Mpfx2
