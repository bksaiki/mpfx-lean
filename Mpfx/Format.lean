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
  /-- The format is *not* degenerate: either precision is finite *and ≠ 1*
  (`p ∈ {2, 3, …}`) or there is a quantum (`exp > -∞`).

  This rules out two pathological cases:
  * `𝒜(∞, -∞, b)`: doubly-unbounded — the entire dyadic line below `b`.
  * `𝒜(1, -∞, b)`: only powers of 2 with no scale — the parity discriminator
    for `IsOdd` (Odd e in the canonical 1-bit representation) is meaningful
    only with a quantum to anchor the index counting from. -/
  not_degenerate : (p ≠ ⊤ ∧ p ≠ 1) ∨ exp ≠ ⊥
  /-- The bound is non-negative when finite. This rules out degenerate formats
  with negative bounds (which would have no representable values), and
  guarantees that `0` is always representable in any `AbstractFormat`. -/
  b_nn : ∀ d : Dyadic, b = ↑d → 0 ≤ (d : ℝ)

namespace AbstractFormat

/-- When `F.p = 1`, the structural invariant forces `F.exp ≠ ⊥`. -/
theorem exp_finite_of_p_one (F : AbstractFormat) (h : F.p = 1) : F.exp ≠ ⊥ := by
  rcases F.not_degenerate with ⟨_, hp1⟩ | hexp
  · exact absurd h hp1
  · exact hexp

/-- The original `not_degenerate` weakening (`p ≠ ⊤ ∨ exp ≠ ⊥`) is implied. -/
theorem not_doubly_unbounded (F : AbstractFormat) : F.p ≠ ⊤ ∨ F.exp ≠ ⊥ := by
  rcases F.not_degenerate with ⟨hp, _⟩ | hexp
  · exact Or.inl hp
  · exact Or.inr hexp

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

/-- `0` is always representable. Uses the structural `b_nn` invariant. -/
theorem zero_mem (F : AbstractFormat) : (0 : Dyadic) ∈ F := by
  refine ⟨?_, ?_, ?_⟩
  · -- precisionAtMost: take c = 0, e = 0
    cases F.p with
    | top => trivial
    | coe n => exact ⟨0, 0, by push_cast; ring, by positivity⟩
  · -- quantumAtLeast: take c = 0
    cases F.exp with
    | bot => trivial
    | coe e => exact ⟨0, by push_cast; simp⟩
  · -- boundOK: |0| = 0 ≤ b (using b_nn for finite bound)
    cases hb : F.b with
    | top => trivial
    | coe d =>
      change |((0 : Dyadic) : ℝ)| ≤ (d : ℝ)
      push_cast
      simpa using F.b_nn d hb

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
