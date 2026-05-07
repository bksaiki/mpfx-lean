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
  /-- Precision is at least one bit (paper: `p ∈ ℤ≥1 ∪ {∞}`). `p = 0` would
  force the format to contain only `0`, which is not a useful number format. -/
  p_pos : 1 ≤ p
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

/-- Extend `F` by increasing precision by `k` and decreasing the exponent of
the quantum by `k`. The bound is preserved.

Used by §5.2 / Fig. 9 to express the paper's "`A(p₁ + k, exp₁ − k, b₁) ⊆ F₂`"
hypotheses for the RTO-double-rounding rules (`k = 1` for `rnd-RTO-RTZ` /
`rnd-RTO-RAZ`, `k = 2` for `rnd-RTO-RNE`). -/
def extend (F : AbstractFormat) (k : ℕ) : AbstractFormat where
  p := F.p + k
  exp := F.exp.map (· - (k : ℤ))
  b := F.b
  p_pos := by
    -- F.p + k ≥ F.p ≥ 1.
    cases hp : F.p with
    | top => simp
    | coe n =>
      rw [← Nat.cast_add]
      have hn : 1 ≤ n := by
        have := F.p_pos; rw [hp] at this; exact_mod_cast this
      exact_mod_cast (by omega : 1 ≤ n + k)
  not_degenerate := by
    -- We need (p+k ≠ ⊤ ∧ p+k ≠ 1) ∨ exp.map ≠ ⊥.
    -- F.p ≥ 1 (from p_pos), so F.p + k ≥ 1.
    -- F.p + k = 1 iff F.p = 1 ∧ k = 0. In that case, F's `not_degenerate`
    -- (with F.p = 1) forces F.exp ≠ ⊥, which transfers to F.exp.map.
    cases hp : F.p with
    | top =>
      -- F.p = ⊤ ⇒ F.exp ≠ ⊥ (from F.not_degenerate, since (⊤ ≠ ⊤) is false).
      right
      have hexp_ne : F.exp ≠ ⊥ := by
        rcases F.not_degenerate with ⟨hpne, _⟩ | hexpne
        · exact absurd hp hpne
        · exact hexpne
      cases hF : F.exp with
      | bot => exact absurd hF hexp_ne
      | coe e => simp
    | coe n =>
      have hn : 1 ≤ n := by
        have := F.p_pos; rw [hp] at this; exact_mod_cast this
      by_cases hnk : n + k = 1
      · -- n + k = 1 with n ≥ 1 forces n = 1, k = 0. Then F.p = 1 ⇒ F.exp ≠ ⊥
        -- via F's not_degenerate (first disjunct fails since F.p = 1).
        have hn_eq : n = 1 := by omega
        right
        have hF_p_eq_1 : F.p = 1 := by rw [hp, hn_eq]; rfl
        have hexp_ne : F.exp ≠ ⊥ := by
          rcases F.not_degenerate with ⟨_, hp1⟩ | hexpne
          · exact absurd hF_p_eq_1 hp1
          · exact hexpne
        cases hF : F.exp with
        | bot => exact absurd hF hexp_ne
        | coe e => simp
      · left
        refine ⟨?_, ?_⟩
        · rw [← Nat.cast_add]; exact WithTop.coe_ne_top
        · rw [← Nat.cast_add]; exact_mod_cast hnk
  b_nn := F.b_nn

@[simp] theorem extend_p (F : AbstractFormat) (k : ℕ) :
    (F.extend k).p = F.p + k := rfl

@[simp] theorem extend_exp (F : AbstractFormat) (k : ℕ) :
    (F.extend k).exp = F.exp.map (· - (k : ℤ)) := rfl

@[simp] theorem extend_b (F : AbstractFormat) (k : ℕ) :
    (F.extend k).b = F.b := rfl

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
