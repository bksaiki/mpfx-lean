import Mpfx.Dyadic

namespace Mpfx

/-- The abstract number format `𝒜(p, exp, b)` from §4.2.

* `p : ℕ∞` — maximum precision (in binary digits). `⊤` denotes "no precision
  constraint" (the format is fixed-point).
* `exp : WithBot ℤ` — exponent of the minimum quantum. `⊥` denotes "no quantum
  constraint" (the format is unbounded floating-point).
* `b : WithTop Dyadic` — magnitude bound. `⊤` denotes "unbounded".
-/
structure AbstractFormat where
  p : ℕ∞
  exp : WithBot ℤ
  b : WithTop Dyadic

namespace AbstractFormat

/-- Bound check: `|x| ≤ b`, with `⊤` interpreted as no constraint. -/
def boundOK : WithTop Dyadic → Dyadic → Prop
  | ⊤, _ => True
  | (b : Dyadic), x => |(x : ℝ)| ≤ (b : ℝ)

@[simp] theorem boundOK_top (x : Dyadic) : boundOK ⊤ x := trivial

theorem boundOK_coe (b : Dyadic) (x : Dyadic) :
    boundOK (b : WithTop Dyadic) x ↔ |(x : ℝ)| ≤ (b : ℝ) := Iff.rfl

/-- Membership in `𝒜(p, exp, b)`: precision ≤ p, quantum ≥ exp, |x| ≤ b. -/
def Mem (F : AbstractFormat) (x : Dyadic) : Prop :=
  Dyadic.precisionAtMost F.p x ∧
  Dyadic.quantumAtLeast F.exp x ∧
  boundOK F.b x

instance : Membership Dyadic AbstractFormat := ⟨fun F x => F.Mem x⟩

theorem mem_iff (F : AbstractFormat) (x : Dyadic) :
    x ∈ F ↔ Dyadic.precisionAtMost F.p x ∧
            Dyadic.quantumAtLeast F.exp x ∧
            boundOK F.b x := Iff.rfl

/-- Every abstract format is closed under negation: `precisionAtMost`,
`quantumAtLeast`, and the bound `|·| ≤ b` are all sign-invariant. -/
theorem neg_mem {F : AbstractFormat} {x : Dyadic} (hx : x ∈ F) : -x ∈ F := by
  obtain ⟨hp, hq, hb⟩ := hx
  refine ⟨?_, ?_, ?_⟩
  · -- precisionAtMost is sign-invariant
    revert hp
    cases F.p with
    | top => intro _; trivial
    | coe n =>
      rintro ⟨c, e, hxeq, hc⟩
      refine ⟨-c, e, ?_, ?_⟩
      · change ((-x : Dyadic) : ℝ) = _
        push_cast
        rw [hxeq]; ring
      · simpa using hc
  · -- quantumAtLeast is sign-invariant
    revert hq
    cases F.exp with
    | bot => intro _; trivial
    | coe n =>
      rintro ⟨c, hxeq⟩
      refine ⟨-c, ?_⟩
      change ((-x : Dyadic) : ℝ) = _
      push_cast
      rw [hxeq]; ring
  · -- bound is sign-invariant
    revert hb
    cases F.b with
    | top => intro _; trivial
    | coe d =>
      intro hb
      change |((-x : Dyadic) : ℝ)| ≤ (d : ℝ)
      push_cast
      rw [abs_neg]
      exact hb

end AbstractFormat

end Mpfx
