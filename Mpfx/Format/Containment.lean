import Mpfx.Format.Defs

/-!
# Format containment (§5.1)

Soundness of the two inference rules:

* `containsPrec` — `𝒜-Contains-Prec`: the general monotone case.
* `containsSub`  — `𝒜-Contains-Sub`: the degenerate case where `F₁`'s bound
  is small enough that nothing in `F₁` uses more than `F₂.p` bits, so
  `F₁.p > F₂.p` is permitted.

Both are stated for `Format` and proved entirely over `ℚ`.

`subset_iff_contains` is completeness: for `F₁` with `BoundRep` and
`Nontrivial`, `F₁ ⊆ F₂` iff one rule fires. Also `extend` and the digit-shift
lemma `numDigits_extend`.
-/

namespace Mpfx

namespace Format

/-- Format inclusion: every value of `F₁` is also a value of `F₂`. -/
def Subset (F₁ F₂ : Format) : Prop := ∀ x : Dyadic, x ∈ F₁ → x ∈ F₂

instance : HasSubset Format := ⟨Subset⟩

/-- The magnitude-bound check is monotone in the bound. -/
theorem boundOK_mono {b₁ b₂ : Bound} (h : b₁ ≤ b₂) {x : Dyadic} :
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

/-- **𝒜-Contains-Prec**. If `p₁ ≤ p₂`, `exp₂ ≤ exp₁`, and `b₁ ≤ b₂`,
then `𝒜(p₁, exp₁, b₁) ⊆ 𝒜(p₂, exp₂, b₂)`. -/
theorem containsPrec {F₁ F₂ : Format}
    (hp : F₁.p ≤ F₂.p) (he : F₂.exp ≤ F₁.exp) (hb : F₁.b ≤ F₂.b) :
    F₁ ⊆ F₂ := by
  intro x hx
  obtain ⟨hpx, hex, hbx⟩ := hx
  exact ⟨Dyadic.precisionAtMost_mono hp hpx,
         Dyadic.quantumAtLeast_anti he hex,
         boundOK_mono hb hbx⟩

/-- **Containment into an unbounded format.** Since `F.unbounded.b = ⊤` accepts
every magnitude, `𝒜-Contains-Prec` (`containsPrec`) reduces to the precision and
quantum orderings alone: a format with precision at most `F.p` and quantum at
least `F.exp` is contained in `F.unbounded`. This is the shared "the exact result
is representable in the wide format" step behind every operation-specific
double-rounding rule (§5.2). -/
theorem subset_unbounded_of_le {F G : Format}
    (hp : G.p ≤ F.p) (he : F.exp ≤ G.exp) : G ⊆ F.unbounded :=
  containsPrec hp he le_top

/-- Membership form of `subset_unbounded_of_le`: a value whose precision is at
most `p ≤ F.p` and whose quantum is at least `e ≥ F.exp` lies in `F.unbounded`.
The intermediate format `𝒜(p, e, ⊤)` witnesses the containment, so operations
need only exhibit their result's precision/quantum and the format-widening
inequalities. -/
theorem mem_unbounded_of_le {F : Format} {p : Prec} {e : QExp}
    {v : Dyadic} (hp : p ≤ F.p) (he : F.exp ≤ e)
    (hvp : Dyadic.precisionAtMost p v) (hvq : Dyadic.quantumAtLeast e v) :
    v ∈ F.unbounded :=
  subset_unbounded_of_le (G := { p := p, exp := e, b := ⊤ }) hp he v ⟨hvp, hvq, trivial⟩

/-- The non-negative dyadic `2 ^ e = 1 · 2^e`. -/
def nnPow (e : ℤ) : NonNegDyadic :=
  ⟨Dyadic.ofIntZpow 1 e, by rw [Dyadic.coe_rat_ofIntZpow]; positivity⟩

@[simp] theorem coe_nnPow (e : ℤ) : ((nnPow e).val : ℚ) = (2 : ℚ) ^ e := by
  change ((Dyadic.ofIntZpow 1 e : Dyadic) : ℚ) = _
  rw [Dyadic.coe_rat_ofIntZpow]; push_cast; ring

@[simp] theorem coe_real_nnPow (e : ℤ) : (((nnPow e).val : Dyadic) : ℝ) = (2 : ℝ) ^ e := by
  rw [Dyadic.coe_real_eq_ratCast, coe_nnPow]; push_cast; ring

/-- **𝒜-Contains-Sub**. If `F₁`'s bound is at most `2^(exp₁ + p₂)`
(so every value of `F₁` fits in `F₂.p = p₂` bits at exponent `exp₁`), plus
the standard quantum and bound orderings, then `F₁ ⊆ F₂` — even when
`F₁.p > F₂.p`. -/
theorem containsSub {F₁ F₂ : Format}
    {exp₁ : ℤ} (he₁ : F₁.exp = (exp₁ : QExp))
    {p₂ : ℕ} (hp₂pos : 0 < p₂) (hp₂ : F₂.p = (p₂ : Prec))
    (hbprec : F₁.b ≤ ((nnPow (exp₁ + (p₂ : ℤ)) : NonNegDyadic) : Bound))
    (he : F₂.exp ≤ F₁.exp)
    (hb : F₁.b ≤ F₂.b) :
    F₁ ⊆ F₂ := by
  intro x hx
  obtain ⟨_, hex, hbx⟩ := hx
  -- x = c · 2^exp₁.
  have hex_coe : Dyadic.quantumAtLeast (exp₁ : QExp) x := by rw [← he₁]; exact hex
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
  have hc_le : |c| ≤ (2 : ℤ) ^ p₂ := by
    have : ((|c| : ℤ) : ℚ) ≤ (((2 : ℤ) ^ p₂ : ℤ) : ℚ) := by
      rw [Int.cast_abs]; push_cast
      simp only [← zpow_natCast (2 : ℚ) p₂]
      exact hc_le_rat
    exact_mod_cast this
  refine ⟨?_, ?_, ?_⟩
  · rw [hp₂]; exact Dyadic.precisionAtMost_of_abs_le hp₂pos c exp₁ hx_eq hc_le
  · exact Dyadic.quantumAtLeast_anti he hex
  · exact boundOK_mono hb hbx

/-! ### Completeness of the two rules (§5.1)

The rules above are also *complete*, so together they decide containment
(`subset_iff_contains`). Two of §4.2's well-formedness restrictions are needed,
and only on `F₁`: `BoundRep F₁` (`b₁ ∈ 𝒜(p₁, exp₁, ∞) ∪ {∞}`) and
`F₁.Nontrivial`. Both are essential: `𝒜(∞, 0, 3/2) = 𝒜(∞, 0, 1) = {0, ±1}`
fails both tests on `b₁ ≤ b₂`, and `𝒜(∞, 0, 0) = 𝒜(∞, 1, 0) = {0}` fails both
on `exp₂ ≤ exp₁`.

Each necessity proof exhibits one value of `F₁` that `F₂` cannot represent. -/

/-- Above any real there is a power of two, at an exponent above `e`. -/
theorem exists_zpow_gt (r : ℝ) (e : QExp) :
    ∃ k : ℤ, e ≤ (k : QExp) ∧ r < (2 : ℝ) ^ k := by
  refine ⟨max (e.unbotD 0) (Int.log 2 r + 1), ?_, lt_of_lt_of_le
    (Int.lt_zpow_succ_log_self (by norm_num : (1 : ℕ) < 2) r)
    (zpow_le_zpow_right₀ (by norm_num) (le_max_right _ _))⟩
  cases e using QExp.recBotCoe with
  | bot => exact bot_le
  | coe e => simp

/-- Below any positive real there is a scaled power of two `C · 2^k`, at an
exponent below `e`. -/
theorem exists_mul_zpow_le {C r : ℝ} (hC : 0 < C) (hr : 0 < r) (e : ℤ) :
    ∃ k : ℤ, k ≤ e ∧ C * (2 : ℝ) ^ k ≤ r := by
  refine ⟨min e (Int.log 2 (r / C)), min_le_left _ _, ?_⟩
  have h1 : (2 : ℝ) ^ (min e (Int.log 2 (r / C))) ≤ (2 : ℝ) ^ (Int.log 2 (r / C)) :=
    zpow_le_zpow_right₀ (by norm_num) (min_le_right _ _)
  have h2 : (2 : ℝ) ^ (Int.log 2 (r / C)) ≤ r / C :=
    Int.zpow_log_le_self (by norm_num : (1 : ℕ) < 2) (div_pos hr hC)
  calc C * (2 : ℝ) ^ (min e (Int.log 2 (r / C))) ≤ C * (r / C) := by nlinarith
    _ = r := by field_simp

/-- **Necessity of `b₁ ≤ b₂`.** A finite `b₁` is a value of `F₁`, so it must be
a value of `F₂`; an infinite `b₁` gives `F₁` arbitrarily large powers of two. -/
theorem b_le_of_subset {F₁ F₂ : Format} (hbr : BoundRep F₁) (hnt : F₁.Nontrivial)
    (h : F₁ ⊆ F₂) : F₁.b ≤ F₂.b := by
  cases hb2 : F₂.b using Bound.recTopCoe with
  | top => exact le_top
  | coe b₂ =>
    cases hb1 : F₁.b using Bound.recTopCoe with
    | coe b₁ =>
      refine WithTop.coe_le_coe.mpr (NonNegDyadic.le_iff_coe_real.mpr ?_)
      have := (h _ (bound_mem hbr hb1)).2.2
      rw [hb2] at this
      rw [← abs_of_nonneg (a := ((b₁.val : Dyadic) : ℝ)) (nonneg_coe_real b₁)]
      exact abs_coe_real_le_of_boundOK this
    | top =>
      -- `F₁` is unbounded, so it contains a power of two exceeding `b₂`.
      obtain ⟨k, hk, hgt⟩ := exists_zpow_gt ((b₂.val : Dyadic) : ℝ) F₁.exp
      have hv := (h _ (ofIntZpow_mem (precisionAtMost_one_zpow hnt.p_ne_zero k) hk
        (by rw [hb1]; trivial))).2.2
      rw [hb2] at hv
      have := abs_coe_real_le_of_boundOK hv
      rw [coe_real_ofIntZpow_one, abs_of_pos (zpow_pos (by norm_num) k)] at this
      exact absurd this (not_le_of_gt hgt)

/-- **Necessity of `exp₂ ≤ exp₁`.** `F₁` is non-trivial, so `2^exp₁` is one of
its values (or, when `exp₁ = -∞`, so is `2^k` for arbitrarily small `k`), while
every value of `F₂` is a multiple of `2^exp₂`. -/
theorem exp_le_of_subset {F₁ F₂ : Format} (hnt : F₁.Nontrivial) (h : F₁ ⊆ F₂) :
    F₂.exp ≤ F₁.exp := by
  have hp0 := hnt.p_ne_zero
  obtain ⟨x₀, hx₀, hx₀ne⟩ := hnt
  cases he2 : F₂.exp using QExp.recBotCoe with
  | bot => exact bot_le
  | coe e₂ =>
    -- `2^k ∈ F₁` forces `e₂ ≤ k`, since `F₂`'s values are multiples of `2^e₂`.
    have key : ∀ k : ℤ, Dyadic.ofIntZpow 1 k ∈ F₁ → e₂ ≤ k := by
      intro k hk
      have hq := (h _ hk).2.1
      rw [he2] at hq
      exact quantum_le_of_odd_rep hq odd_one (by rw [coe_real_ofIntZpow_one]; norm_num)
    cases he1 : F₁.exp using QExp.recBotCoe with
    | coe e₁ =>
      -- `2^e₁ ≤ |x₀| ≤ b₁`, so `2^e₁` is in bound.
      refine WithBot.coe_le_coe.mpr (key e₁ (ofIntZpow_mem
        (precisionAtMost_one_zpow hp0 e₁)
        (by rw [he1]) (boundOK_of_abs_le ?_ hx₀.2.2)))
      rw [coe_real_ofIntZpow_one, abs_of_pos (zpow_pos (by norm_num) e₁)]
      exact Dyadic.abs_ge_two_zpow_of_quantum (he1 ▸ hx₀.2.1) (by exact_mod_cast hx₀ne)
    | bot =>
      -- `F₁` has values `2^k` with `k` arbitrarily small, contradicting `e₂ ≤ k`.
      exfalso
      obtain ⟨k, hk_le, hk_bnd⟩ :
          ∃ k : ℤ, k ≤ e₂ - 1 ∧ boundOK F₁.b (Dyadic.ofIntZpow 1 k) := by
        cases hb1 : F₁.b using Bound.recTopCoe with
        | top => exact ⟨e₂ - 1, le_refl _, trivial⟩
        | coe b₁ =>
          have hpos : 0 < ((b₁.val : Dyadic) : ℝ) :=
            lt_of_lt_of_le (abs_pos.mpr (by exact_mod_cast hx₀ne))
              (abs_coe_real_le_of_boundOK (hb1 ▸ hx₀.2.2))
          obtain ⟨k, hk_le, hk⟩ := exists_mul_zpow_le one_pos hpos (e₂ - 1)
          refine ⟨k, hk_le, boundOK_coe_of_abs_le ?_⟩
          rw [coe_real_ofIntZpow_one, abs_of_pos (zpow_pos (by norm_num) k)]
          linarith
      have := key k (ofIntZpow_mem (precisionAtMost_one_zpow hp0 k)
        (by rw [he1]; exact bot_le) hk_bnd)
      omega

/-! ### The precision test

When `p₁ > p₂` containment can still hold, but only because `F₁`'s bound cuts
off every value that needs more than `p₂` digits. The narrowest such value is
`wit p₂ · 2^exp₁`, where `wit p₂ = 2^p₂ + 1` is the smallest odd significand
wider than `p₂` digits. -/

/-- `2^p + 1`: odd, exactly `p+1` digits wide. -/
def wit (p : ℕ) : ℤ := 2 ^ p + 1

theorem one_lt_two_pow {p : ℕ} (hp : 0 < p) : (1 : ℤ) < 2 ^ p := by
  calc (1 : ℤ) = 2 ^ 0 := by norm_num
    _ < 2 ^ p := pow_lt_pow_right₀ (by norm_num) hp

theorem wit_pos (p : ℕ) : 0 < wit p := by unfold wit; positivity

theorem odd_wit {p : ℕ} (hp : 0 < p) : Odd (wit p) :=
  (by rw [Int.even_pow]; exact ⟨even_two, hp.ne'⟩ : Even ((2 : ℤ) ^ p)).add_one

/-- `wit p₂` is too wide for `p₂` digits ... -/
theorem not_precisionAtMost_wit {p₂ : ℕ} (hp : 0 < p₂) (k : ℤ) :
    ¬ Dyadic.precisionAtMost (p₂ : Prec) (Dyadic.ofIntZpow (wit p₂) k) :=
  Dyadic.not_precisionAtMost_of_odd (odd_wit hp) (by rw [Dyadic.coe_ofIntZpow])
    (by rw [abs_of_pos (wit_pos p₂)]; unfold wit; omega)

/-- ... but fits in any strictly larger precision bound. -/
theorem precisionAtMost_wit {p₁ : Prec} {p₂ : ℕ} (hp : 0 < p₂)
    (hlt : (p₂ : Prec) < p₁) (k : ℤ) :
    Dyadic.precisionAtMost p₁ (Dyadic.ofIntZpow (wit p₂) k) := by
  cases hp' : p₁ using ENat.recTopCoe with
  | top => trivial
  | coe q =>
    rw [Dyadic.precisionAtMost_coe]
    refine ⟨wit p₂, k, by rw [Dyadic.coe_rat_ofIntZpow], ?_⟩
    have hq : p₂ + 1 ≤ q := by
      have : (p₂ : Prec) < (q : Prec) := hp' ▸ hlt
      exact_mod_cast this
    have h1 := one_lt_two_pow hp
    calc |wit p₂| = 2 ^ p₂ + 1 := by rw [abs_of_pos (wit_pos p₂)]; rfl
      _ < 2 ^ (p₂ + 1) := by rw [pow_succ]; omega
      _ ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) hq

/-- `wit p₂ · 2^k`, as a positive real. -/
theorem abs_coe_wit (p₂ : ℕ) (k : ℤ) :
    |((Dyadic.ofIntZpow (wit p₂) k : Dyadic) : ℝ)| = ((wit p₂ : ℤ) : ℝ) * (2 : ℝ) ^ k := by
  have hw : (0 : ℝ) < ((wit p₂ : ℤ) : ℝ) := by exact_mod_cast wit_pos p₂
  rw [Dyadic.coe_ofIntZpow, abs_of_pos (mul_pos hw (zpow_pos (by norm_num) k))]

/-- **Necessity of the `𝒜-Contains-Sub` premises.** If `F₁ ⊆ F₂` yet `p₁ > p₂`,
then `exp₁` is finite and `b₁ ≤ 2^(exp₁ + p₂)`; otherwise `wit p₂ · 2^exp₁` is a
value of `F₁` that `F₂` cannot represent. -/
theorem sub_test_of_subset {F₁ F₂ : Format} (hbr : BoundRep F₁) (hnt : F₁.Nontrivial)
    (h : F₁ ⊆ F₂) (hp : ¬ F₁.p ≤ F₂.p) :
    ∃ (e₁ : ℤ) (p₂ : ℕ), F₁.exp = (e₁ : QExp) ∧ 0 < p₂ ∧ F₂.p = (p₂ : Prec) ∧
      F₁.b ≤ ((nnPow (e₁ + (p₂ : ℤ)) : NonNegDyadic) : Bound) := by
  obtain ⟨x₀, hx₀, hx₀ne⟩ := hnt
  have hlt : F₂.p < F₁.p := lt_of_not_ge hp
  cases hp2 : F₂.p using ENat.recTopCoe with
  | top => exact absurd (hp2 ▸ hlt) (not_lt_of_ge le_top)
  | coe p₂ =>
  rcases Nat.eq_zero_or_pos p₂ with rfl | hp₂pos
  · -- `p₂ = 0`: `F₂` holds only `0`, contradicting `F₁`'s nonzero member.
    exfalso
    have hx₀p := (h _ hx₀).1
    rw [hp2] at hx₀p
    exact hx₀ne (Dyadic.precisionAtMost_zero_iff_eq_zero.mp hx₀p)
  have hwpos : (0 : ℝ) < ((wit p₂ : ℤ) : ℝ) := by exact_mod_cast wit_pos p₂
  -- The witness is never in `F₂`, so it must fail `F₁`'s quantum or bound check.
  have key : ∀ k : ℤ, F₁.exp ≤ (k : QExp) →
      boundOK F₁.b (Dyadic.ofIntZpow (wit p₂) k) → False := by
    intro k hk hbk
    have hmem := (h _ (ofIntZpow_mem (precisionAtMost_wit hp₂pos (hp2 ▸ hlt) k) hk hbk)).1
    rw [hp2] at hmem
    exact not_precisionAtMost_wit hp₂pos k hmem
  cases he1 : F₁.exp using QExp.recBotCoe with
  | bot =>
    -- `exp₁ = -∞`: the witness can be scaled below any positive bound.
    exfalso
    obtain ⟨k, hk⟩ : ∃ k : ℤ, boundOK F₁.b (Dyadic.ofIntZpow (wit p₂) k) := by
      cases hb1 : F₁.b using Bound.recTopCoe with
      | top => exact ⟨0, trivial⟩
      | coe b₁ =>
        have hpos : 0 < ((b₁.val : Dyadic) : ℝ) :=
          lt_of_lt_of_le (abs_pos.mpr (by exact_mod_cast hx₀ne))
              (abs_coe_real_le_of_boundOK (hb1 ▸ hx₀.2.2))
        obtain ⟨k, -, hk⟩ := exists_mul_zpow_le hwpos hpos 0
        exact ⟨k, boundOK_coe_of_abs_le (by rw [abs_coe_wit]; exact hk)⟩
    exact key k (by rw [he1]; exact bot_le) hk
  | coe e₁ =>
    refine ⟨e₁, p₂, rfl, hp₂pos, rfl, ?_⟩
    cases hb1 : F₁.b using Bound.recTopCoe with
    | top => exact absurd (key e₁ (by rw [he1]) (by rw [hb1]; trivial)) not_false
    | coe b₁ =>
      -- `b₁` is a grid point, `b₁ = m · 2^exp₁`; if `b₁ > 2^(exp₁+p₂)` then
      -- `m ≥ wit p₂`, so the witness is in bound.
      refine WithTop.coe_le_coe.mpr (NonNegDyadic.le_iff_coe_real.mpr ?_)
      by_contra hcon
      have h2e : (0 : ℝ) < (2 : ℝ) ^ e₁ := zpow_pos (by norm_num) _
      rw [coe_real_nnPow] at hcon
      push Not at hcon
      obtain ⟨m, hm⟩ : ∃ m : ℤ, ((b₁.val : Dyadic) : ℝ) = (m : ℝ) * (2 : ℝ) ^ e₁ := by
        rw [← Dyadic.quantumAtLeast_coe_real]
        exact he1 ▸ (hbr b₁ hb1).2.1
      have hm_ge : ((wit p₂ : ℤ) : ℝ) ≤ (m : ℝ) := by
        have h1 : (2 : ℝ) ^ p₂ < (m : ℝ) := by
          refine lt_of_mul_lt_mul_right ?_ (le_of_lt h2e)
          rw [hm, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast,
            mul_comm ((2 : ℝ) ^ e₁)] at hcon
          exact hcon
        have h2 : (2 : ℤ) ^ p₂ < m := by exact_mod_cast h1
        exact_mod_cast (by unfold wit; omega : wit p₂ ≤ m)
      refine key e₁ (by rw [he1]) (hb1 ▸ boundOK_coe_of_abs_le ?_)
      rw [abs_coe_wit, hm]
      exact mul_le_mul_of_nonneg_right hm_ge (le_of_lt h2e)

/-! ### The decision procedure

`ContainsSub` requires `p₂ < ∞`; the paper's rule does not, but with `p₂ = ∞`
its bound test `b₁ ≤ 2^(exp₁+∞)` is vacuous and its remaining premises are
those of `ContainsPrec` (whose `p₁ ≤ ∞` is free), so the disjunction below is
unchanged either way. -/

/-- Premises of `𝒜-Contains-Prec`. -/
def ContainsPrec (F₁ F₂ : Format) : Prop :=
  F₁.p ≤ F₂.p ∧ F₂.exp ≤ F₁.exp ∧ F₁.b ≤ F₂.b

/-- Premises of `𝒜-Contains-Sub`. -/
def ContainsSub (F₁ F₂ : Format) : Prop :=
  ∃ (e₁ : ℤ) (p₂ : ℕ), F₁.exp = (e₁ : QExp) ∧ 0 < p₂ ∧ F₂.p = (p₂ : Prec) ∧
    F₁.b ≤ ((nnPow (e₁ + (p₂ : ℤ)) : NonNegDyadic) : Bound) ∧
    F₂.exp ≤ F₁.exp ∧ F₁.b ≤ F₂.b

/-- **Completeness of the containment rules.** For `F₁` with a representable bound that
represents a nonzero value, `F₁ ⊆ F₂` holds exactly when one of the two rules
fires. No assumption on `F₂` is needed. -/
theorem subset_iff_contains {F₁ F₂ : Format} (hbr : BoundRep F₁) (hnt : F₁.Nontrivial) :
    F₁ ⊆ F₂ ↔ ContainsPrec F₁ F₂ ∨ ContainsSub F₁ F₂ := by
  constructor
  · intro h
    have hb := b_le_of_subset hbr hnt h
    have he := exp_le_of_subset hnt h
    by_cases hp : F₁.p ≤ F₂.p
    · exact Or.inl ⟨hp, he, hb⟩
    · obtain ⟨e₁, p₂, he₁, hp₂pos, hp₂, hbb⟩ := sub_test_of_subset hbr hnt h hp
      exact Or.inr ⟨e₁, p₂, he₁, hp₂pos, hp₂, hbb, he, hb⟩
  · rintro (⟨hp, he, hb⟩ | ⟨e₁, p₂, he₁, hp₂pos, hp₂, hbb, he, hb⟩)
    · exact containsPrec hp he hb
    · exact containsSub he₁ hp₂pos hp₂ hbb he hb

/-! ### Format extension

`F.extend k` adds `k` bits of precision and lowers the minimum quantum by
`k` (bound unchanged). Used by §5.2 to phrase the double-rounding rules'
intermediate formats `A(p₁ + k, exp₁ − k, b₁)`. -/

/-- Extend `F` by `k` bits: `p ↦ p + k`, `exp ↦ exp − k`, `b` unchanged. -/
def extend (F : Format) (k : ℕ) : Format where
  p := F.p + k
  exp := F.exp.map (· - (k : ℤ))
  b := F.b

@[simp] theorem extend_b (F : Format) k : (F.extend k).b = F.b := rfl

/-- `F ⊆ F.extend k`: extending only relaxes the precision and quantum
constraints. -/
theorem self_subset_extend (F : Format) (k : ℕ) : F ⊆ F.extend k := by
  apply containsPrec
  · exact le_self_add
  · change F.exp.map (· - (k : ℤ)) ≤ F.exp
    cases F.exp using QExp.recBotCoe with
    | bot => simp
    | coe e =>
      rw [WithBot.map_coe]
      exact WithBot.coe_le_coe.mpr (sub_le_self e (by positivity))
  · exact le_refl _

/-- `extend` is monotone in the bit count: `F.extend j ⊆ F.extend k` when `j ≤ k`. -/
theorem extend_mono (F : Format) {j k : ℕ} (h : j ≤ k) :
    F.extend j ⊆ F.extend k := by
  apply containsPrec
  · exact add_le_add_right (Nat.cast_le.mpr h) F.p
  · change F.exp.map (· - (k : ℤ)) ≤ F.exp.map (· - (j : ℤ))
    cases F.exp using QExp.recBotCoe with
    | bot => simp
    | coe e =>
      rw [WithBot.map_coe, WithBot.map_coe]
      have hjk : (j : ℤ) ≤ (k : ℤ) := by exact_mod_cast h
      exact WithBot.coe_le_coe.mpr (by omega)
  · exact le_refl _

/-- `(F.extend 1).extend 1 ⊆ F.extend 2` via precision/quantum equivalence.
The core is `(p+1)+1 = p+2`, `(exp-1)-1 = exp-2`, same bound. -/
theorem extend_one_extend_one_subset_extend_two (F : Format) :
    (F.extend 1).extend 1 ⊆ F.extend 2 := by
  intro y hy
  obtain ⟨hp, hq, hb⟩ := hy
  refine ⟨?_, ?_, hb⟩
  · change Dyadic.precisionAtMost (F.p + ((2 : ℕ) : Prec)) y
    change Dyadic.precisionAtMost (F.p + ((1 : ℕ) : Prec) + ((1 : ℕ) : Prec)) y at hp
    rwa [add_assoc, show ((1 : ℕ) : Prec) + ((1 : ℕ) : Prec) = ((2 : ℕ) : Prec) by
      push_cast; ring] at hp
  · -- quantumAtLeast ((F.exp.map (·-1)).map (·-1)) y → quantumAtLeast (F.exp.map (·-2)) y.
    change Dyadic.quantumAtLeast (F.exp.map (· - (2 : ℤ))) y
    change Dyadic.quantumAtLeast ((F.exp.map (· - (1 : ℤ))).map (· - (1 : ℤ))) y at hq
    have h_eq : (F.exp.map (· - (1 : ℤ))).map (· - (1 : ℤ)) = F.exp.map (· - (2 : ℤ)) := by
      cases F.exp using QExp.recBotCoe with
      | bot => rfl
      | coe e =>
        rw [WithBot.map_coe, WithBot.map_coe, WithBot.map_coe]
        congr 1
        ring
    rw [h_eq] at hq; exact hq

/-- A `Dyadic` not representable in 1 bit cannot live in a format with
`F.p ≤ 1`, so a precision-2 witness in `F` forces `F.p ≥ 2`. -/
theorem two_le_p_of_precision_two_witness {F : Format} {v : Dyadic}
    (hvF : v ∈ F) (hv_not_p1 : ¬ Dyadic.precisionAtMost ((1 : ℕ) : Prec) v) :
    ((2 : ℕ) : Prec) ≤ F.p := by
  by_contra h_p_lt
  push Not at h_p_lt
  have hv_p_F : Dyadic.precisionAtMost F.p v := hvF.1
  cases hpf : F.p using ENat.recTopCoe with
  | top => rw [hpf] at h_p_lt; exact not_top_lt h_p_lt
  | coe n =>
    rw [hpf] at h_p_lt hv_p_F
    have hn : n ≤ 1 := by
      have h2 : n < 2 := by exact_mod_cast h_p_lt
      omega
    exact hv_not_p1 (Dyadic.precisionAtMost_mono (by exact_mod_cast hn) hv_p_F)

end Format

namespace FiniteFormat

/-- Extend a `FiniteFormat` by `k` bits. The `finite` invariant is preserved:
`extend` only grows `p` (a finite `p` stays finite) and only shrinks `exp`
(a finite `exp` stays finite). -/
def extend (F : FiniteFormat) (k : ℕ) : FiniteFormat where
  toFormat := F.toFormat.extend k
  finite := by
    rcases F.finite with hp | he
    · left
      change F.p + (k : Prec) ≠ ⊤
      exact fun h => hp (WithTop.add_eq_top.mp h |>.resolve_right (ENat.coe_ne_top k))
    · right
      change F.exp.map (· - (k : ℤ)) ≠ ⊥
      cases hF : F.exp using QExp.recBotCoe with
      | bot => exact absurd hF he
      | coe e => rw [WithBot.map_coe]; exact WithBot.coe_ne_bot
  pos := by
    change F.p + (k : Prec) ≠ 0
    exact fun h => F.pos (by simpa using (add_eq_zero.mp h).1)

@[simp] theorem extend_toFormat (F : FiniteFormat) k :
    (F.extend k).toFormat = F.toFormat.extend k := rfl

/-- **Digit-shift lemma** (`w₂ = w₁ + k`): extending `F` by `k` increases the digit count of every
nonzero `x` by exactly `k`. -/
theorem numDigits_extend (F : FiniteFormat) (k : ℕ) {x : ℝ} (hx : x ≠ 0) :
    (F.extend k).numDigits x = F.numDigits x + k := by
  have hp_ext : (F.extend k).p = F.p + (k : Prec) := rfl
  have he_ext : (F.extend k).exp = F.exp.map (· - (k : ℤ)) := rfl
  cases hp : F.p using ENat.recTopCoe with
  | top =>
    cases hexp : F.exp using QExp.recBotCoe with
    | bot =>
      exfalso; rcases F.finite with h | h
      · exact h hp
      · exact h hexp
    | coe e' =>
      have hpe : (F.extend k).p = ⊤ := by rw [hp_ext, hp]; rfl
      have hee : (F.extend k).exp = ((e' - (k : ℤ) : ℤ) : QExp) := by
        rw [he_ext, hexp, WithBot.map_coe]
      rw [F.numDigits_top_coe hx hexp hp,
          (F.extend k).numDigits_top_coe hx hee hpe]
      ring
  | coe n =>
    cases hexp : F.exp using QExp.recBotCoe with
    | bot =>
      have hpe : (F.extend k).p = ((n + k : ℕ) : Prec) := by
        rw [hp_ext, hp, ← Nat.cast_add]
      have hee : (F.extend k).exp = ⊥ := by rw [he_ext, hexp]; rfl
      rw [F.numDigits_coe_bot hx hp hexp,
          (F.extend k).numDigits_coe_bot hx hpe hee]
      push_cast; ring
    | coe e' =>
      have hpe : (F.extend k).p = ((n + k : ℕ) : Prec) := by
        rw [hp_ext, hp, ← Nat.cast_add]
      have hee : (F.extend k).exp = ((e' - (k : ℤ) : ℤ) : QExp) := by
        rw [he_ext, hexp, WithBot.map_coe]
      rw [F.numDigits_coe_coe hx hp hexp,
          (F.extend k).numDigits_coe_coe hx hpe hee]
      have hnk : (((n + k : ℕ) : ℕ) : ℤ) = (n : ℤ) + (k : ℤ) := by push_cast; ring
      rw [hnk]
      have hlog : Int.log 2 |x| - (e' - (k : ℤ)) + 1
          = Int.log 2 |x| - e' + 1 + (k : ℤ) := by ring
      rw [hlog]; omega

end FiniteFormat

end Mpfx
