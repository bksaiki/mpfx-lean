import Mpfx.Format

/-!
# Format containment (§5.1, Fig. 8)

Soundness of the two inference rules:

* `containsPrec` — `𝒜-Contains-Prec`: the general monotone case.
* `containsSub`  — `𝒜-Contains-Sub`: the degenerate case where `F₁`'s bound
  is small enough that nothing in `F₁` uses more than `F₂.p` bits, so
  `F₁.p > F₂.p` is permitted.

Both are stated for `Format` and proved entirely over `ℚ`.
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

/-- **𝒜-Contains-Sub** (Fig. 8). If `F₁`'s bound is at most `2^(exp₁ + p₂)`
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

/-- Premises of `𝒜-Contains-Prec` (Fig. 7). -/
def ContainsPrec (F₁ F₂ : Format) : Prop :=
  F₁.p ≤ F₂.p ∧ F₂.exp ≤ F₁.exp ∧ F₁.b ≤ F₂.b

/-- Premises of `𝒜-Contains-Sub` (Fig. 7). -/
def ContainsSub (F₁ F₂ : Format) : Prop :=
  ∃ (e₁ : ℤ) (p₂ : ℕ), F₁.exp = (e₁ : QExp) ∧ 0 < p₂ ∧ F₂.p = (p₂ : Prec) ∧
    F₁.b ≤ ((nnPow (e₁ + (p₂ : ℤ)) : NonNegDyadic) : Bound) ∧
    F₂.exp ≤ F₁.exp ∧ F₁.b ≤ F₂.b

/-- **Figure 7 decides containment.** For `F₁` with a representable bound that
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

/-! ### Bound replacement and the `next` operator

`F.withBound b'` swaps out `F`'s magnitude bound for `b'`. `F.next b` is the
paper's `next_{F.p, F.exp}(b)` from §5.2 / Fig. 9: the smallest Dyadic in the
grid `A(F.p, F.exp, ∞)` strictly above `b`. -/

/-- Replace `F`'s bound with `b'`, keeping precision and quantum. No
non-negativity witness is needed: `NonNegDyadic` already carries `0 ≤ d`. -/
def withBound (F : Format) (b' : Bound) : Format := { F with b := b' }

@[simp] theorem withBound_p (F : Format) (b' : Bound) :
    (F.withBound b').p = F.p := rfl

@[simp] theorem withBound_exp (F : Format) (b' : Bound) :
    (F.withBound b').exp = F.exp := rfl

@[simp] theorem withBound_b (F : Format) (b' : Bound) :
    (F.withBound b').b = b' := rfl

/-- The paper's `next_{F.p, F.exp}(b)` from §5.2 / Fig. 9: the smallest Dyadic
in the grid `A(F.p, F.exp, ∞)` strictly above `b`.

For `b > 0` with finite `(F.p, F.exp)`, computed as `b + step` where the grid
step depends on `b`'s magnitude (for `b ≤ 0` the smallest positive grid
point `2^F.exp` is returned, which is the successor at `b = 0` and junk
for `b < 0`):
- **Subnormal regime** (`|b| < 2^(F.exp + F.p − 1)`): step = `2^F.exp`.
- **Normal regime**: step = `2^(⌊log₂ b⌋ − F.p + 1)` (binade-dependent).
- Unified: step exponent = `max(F.exp, ⌊log₂ b⌋ − F.p + 1)`.

For `F.p = ⊤` and `F.exp = (e : ℤ)`: `A(⊤, e, ∞)` is all dyadics with quantum
≥ e, so the smallest value strictly above `b` is `b + 2^e`.

For `F.exp = ⊥` with `F.p = p` and `b > 0`: there is no quantum, so
the step is purely binade-dependent: `2^(⌊log₂ b⌋ − F.p + 1)`. For `b ≤ 0`
the grid has positive elements of arbitrarily small magnitude, so no
successor exists; `b + 1` is returned as a junk value (only the `b > 0`
case is meaningful). The doubly-unbounded `(⊤, ⊥)` arm is excluded by
`FiniteFormat`. -/
noncomputable def next (F : Format) (b : Dyadic) : Dyadic :=
  match F.exp, F.p with
  | (e : ℤ), (p : ℕ) =>
    if (b : ℝ) ≤ 0 then
      Dyadic.ofIntZpow 1 e
    else
      let logB : ℤ := Int.log 2 ((b : Dyadic) : ℝ)
      let stepExp : ℤ := max e (logB - (p : ℤ) + 1)
      b + Dyadic.ofIntZpow 1 stepExp
  | (e : ℤ), ⊤ => b + Dyadic.ofIntZpow 1 e
  | ⊥, (p : ℕ) =>
    if (b : ℝ) ≤ 0 then
      b + 1
    else
      b + Dyadic.ofIntZpow 1 (Int.log 2 ((b : Dyadic) : ℝ) - (p : ℤ) + 1)
  | ⊥, ⊤ => b + 1

/-- `F.next b > b` for finite `(F.p, F.exp)` and `b ≥ 0`. -/
theorem lt_next_of_finite (F : Format) {e : ℤ} {p : ℕ}
    (he : F.exp = (e : QExp)) (hp : F.p = (p : Prec)) (b : Dyadic)
    (hb : 0 ≤ ((b : Dyadic) : ℝ)) :
    (b : ℝ) < (F.next b : ℝ) := by
  have h_ulp_pos : ∀ k : ℤ, (0 : ℝ) < ((Dyadic.ofIntZpow 1 k : Dyadic) : ℝ) := by
    intro k
    rw [Dyadic.coe_ofIntZpow]
    have h2 : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
    push_cast
    linarith
  have h_next_eq : F.next b =
      if ((b : Dyadic) : ℝ) ≤ 0 then Dyadic.ofIntZpow 1 e
      else b + Dyadic.ofIntZpow 1 (max e (Int.log 2 ((b : Dyadic) : ℝ) - (p : ℤ) + 1)) := by
    unfold next; rw [he, hp]
  rw [h_next_eq]
  by_cases h : ((b : Dyadic) : ℝ) ≤ 0
  · rw [if_pos h]
    have hb_zero : ((b : Dyadic) : ℝ) = 0 := le_antisymm h hb
    rw [hb_zero]
    exact h_ulp_pos e
  · rw [if_neg h]
    push_cast
    have := h_ulp_pos (max e (Int.log 2 ((b : Dyadic) : ℝ) - (p : ℤ) + 1))
    linarith

/-- `F.next b > b` for `F.p = ⊤` and `F.exp = (e : ℤ)`. -/
theorem lt_next_of_p_top (F : Format) {e : ℤ}
    (he : F.exp = (e : QExp)) (hp : F.p = ⊤) (b : Dyadic) :
    (b : ℝ) < (F.next b : ℝ) := by
  have h_ulp_pos : (0 : ℝ) < ((Dyadic.ofIntZpow 1 e : Dyadic) : ℝ) := by
    rw [Dyadic.coe_ofIntZpow]
    have h2 : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
    push_cast; linarith
  have h_next_eq : F.next b = b + Dyadic.ofIntZpow 1 e := by
    -- `⊤ : Prec` is not syntactically `Option.none`, so the `match` on
    -- `(F.exp, F.p)` needs an explicit `rfl` to reduce.
    unfold next
    rw [he, hp]; rfl
  rw [h_next_eq]; push_cast; linarith

/-- Computed form of `next` for `F.exp = ⊥, F.p = ⊤` (junk arm: excluded by
`FiniteFormat`). -/
theorem next_eq_bot_p_top' (F : Format) (he : F.exp = ⊥) (hp : F.p = ⊤)
    (b : Dyadic) : F.next b = b + 1 := by
  unfold next
  rw [he, hp]; rfl

/-- Computed form of `next` for `F.exp = ⊥, b ≤ 0` (junk arm: no grid
successor exists). -/
theorem next_eq_bot_nonpos (F : Format) (he : F.exp = ⊥) {b : Dyadic}
    (hb : ((b : Dyadic) : ℝ) ≤ 0) : F.next b = b + 1 := by
  cases hp : F.p using ENat.recTopCoe with
  | top => exact next_eq_bot_p_top' F he hp b
  | coe p =>
    have h_eq : F.next b =
        if ((b : Dyadic) : ℝ) ≤ 0 then b + 1
        else b + Dyadic.ofIntZpow 1
          (Int.log 2 ((b : Dyadic) : ℝ) - (p : ℤ) + 1) := by
      unfold next; rw [he, hp]
    rw [h_eq, if_pos hb]

/-- Computed form of `next` for `F.exp = ⊥, F.p = p, b > 0`: the
step is purely binade-dependent. -/
theorem next_eq_bot_pos (F : Format) {p : ℕ} (he : F.exp = ⊥)
    (hp : F.p = (p : Prec)) {b : Dyadic}
    (hb_pos : 0 < ((b : Dyadic) : ℝ)) :
    F.next b
      = b + Dyadic.ofIntZpow 1 (Int.log 2 ((b : Dyadic) : ℝ) - (p : ℤ) + 1) := by
  have h_eq : F.next b =
      if ((b : Dyadic) : ℝ) ≤ 0 then b + 1
      else b + Dyadic.ofIntZpow 1
        (Int.log 2 ((b : Dyadic) : ℝ) - (p : ℤ) + 1) := by
    unfold next; rw [he, hp]
  rw [h_eq, if_neg (not_le.mpr hb_pos)]

/-- `F.next b > b` for `F.exp = ⊥` (all `F.p` shapes, any `b`). -/
theorem lt_next_of_bot (F : Format) (he : F.exp = ⊥) (b : Dyadic) :
    ((b : Dyadic) : ℝ) < ((F.next b : Dyadic) : ℝ) := by
  cases hp : F.p using ENat.recTopCoe with
  | top =>
    rw [next_eq_bot_p_top' F he hp b]
    push_cast
    linarith
  | coe p =>
    by_cases hb0 : ((b : Dyadic) : ℝ) ≤ 0
    · rw [next_eq_bot_nonpos F he hb0]
      push_cast
      linarith
    · push Not at hb0
      rw [next_eq_bot_pos F he hp hb0, Dyadic.coe_real_add, Dyadic.coe_ofIntZpow]
      have h2 : (0 : ℝ) < (2 : ℝ) ^ (Int.log 2 ((b : Dyadic) : ℝ) - (p : ℤ) + 1) :=
        zpow_pos (by norm_num) _
      push_cast
      linarith

/-- `F.next b ≥ 0` for `b ≥ 0`. Combines all four `(F.p, F.exp)` shapes:
finite-finite via `lt_next_of_finite`; `F.p = ⊤` finite-exp via
`lt_next_of_p_top`; `F.exp = ⊥` via `lt_next_of_bot`. -/
theorem next_nonneg (F : Format) (b : Dyadic) (hb : 0 ≤ ((b : Dyadic) : ℝ)) :
    0 ≤ ((F.next b : Dyadic) : ℝ) := by
  rcases hF_exp : F.exp with _ | e
  · -- F.exp = ⊥. Use lt_next_of_bot.
    have hlt := lt_next_of_bot F hF_exp b
    linarith
  · rcases hF_p : F.p with _ | p
    · -- F.p = ⊤, F.exp finite. Use lt_next_of_p_top.
      have hlt := lt_next_of_p_top F hF_exp hF_p b
      linarith
    · -- Both finite. Use lt_next_of_finite.
      have hlt := lt_next_of_finite F hF_exp hF_p b hb
      linarith

/-- Computed form of `next` for `F.exp = (e : ℤ), F.p = p, b > 0`. -/
theorem next_eq_finite_pos (F : Format) {e : ℤ} {p : ℕ}
    (he : F.exp = (e : QExp)) (hp : F.p = (p : Prec))
    {b : Dyadic} (hb_pos : 0 < ((b : Dyadic) : ℝ)) :
    F.next b =
      b + Dyadic.ofIntZpow 1
        (max e (Int.log 2 ((b : Dyadic) : ℝ) - (p : ℤ) + 1)) := by
  have h_eq : F.next b =
      if ((b : Dyadic) : ℝ) ≤ 0 then Dyadic.ofIntZpow 1 e
      else b + Dyadic.ofIntZpow 1
        (max e (Int.log 2 ((b : Dyadic) : ℝ) - (p : ℤ) + 1)) := by
    unfold next; rw [he, hp]
  rw [h_eq, if_neg (not_le.mpr hb_pos)]

/-- Computed form of `next` for `F.exp = (e : ℤ), F.p = ⊤`. -/
theorem next_eq_p_top (F : Format) {e : ℤ}
    (he : F.exp = (e : QExp)) (hp : F.p = ⊤) (b : Dyadic) :
    F.next b = b + Dyadic.ofIntZpow 1 e := by
  unfold next
  rw [he, hp]; rfl

/-- `b ≤ F.next b` for `b ≥ 0`. Combines all four `(F.p, F.exp)` shapes via
case-split: finite-finite via `lt_next_of_finite`; `F.p = ⊤` finite-exp via
`lt_next_of_p_top`; `F.exp = ⊥` via `lt_next_of_bot`. -/
theorem self_le_next (F : Format) (b : Dyadic)
    (hb : 0 ≤ ((b : Dyadic) : ℝ)) :
    ((b : Dyadic) : ℝ) ≤ ((F.next b : Dyadic) : ℝ) := by
  rcases hF_exp : F.exp with _ | e
  · -- F.exp = ⊥. lt_next_of_bot.
    have := lt_next_of_bot F hF_exp b; linarith
  · rcases hF_p : F.p with _ | p
    · -- F.p = ⊤, F.exp finite. lt_next_of_p_top.
      have := lt_next_of_p_top F hF_exp hF_p b; linarith
    · -- Both finite. lt_next_of_finite.
      have := lt_next_of_finite F hF_exp hF_p b hb; linarith

/-! ### `boundAfterNext`: the bound for the paper's `F⁺` containment

`next(F.b)` lifted to `Bound`. Returns `⊤` when `F.b = ⊤`,
otherwise `(F.next b : NonNegDyadic)`. The non-negativity witness is carried by
`NonNegDyadic` itself (no separate obligation), and `withBound` takes only the
bound. -/

/-- The bound for the paper's `F⁺` containment: `next(F.b)` lifted to
`Bound`. -/
noncomputable def boundAfterNext (F : Format) : Bound :=
  match F.b with
  | ⊤ => ⊤
  | (b : NonNegDyadic) =>
    (⟨F.next b.val, by
        have hb : 0 ≤ ((b.val : Dyadic) : ℝ) := by
          rw [Dyadic.coe_real_eq_ratCast]; exact_mod_cast b.2
        have h_next_nn : 0 ≤ ((F.next b.val : Dyadic) : ℝ) := next_nonneg F b.val hb
        rw [Dyadic.coe_real_eq_ratCast] at h_next_nn
        exact_mod_cast h_next_nn⟩ : NonNegDyadic)

/-- `boundAfterNext` evaluator: `⊤` case. -/
@[simp] theorem boundAfterNext_top {F : Format} (hF : F.b = ⊤) :
    F.boundAfterNext = ⊤ := by unfold boundAfterNext; rw [hF]

/-- `boundAfterNext` evaluator: coe case. The underlying dyadic is `F.next b`. -/
theorem boundAfterNext_coe {F : Format} {b : NonNegDyadic} (hF : F.b = (b : Bound)) :
    ∃ h, F.boundAfterNext = ((⟨F.next b.val, h⟩ : NonNegDyadic) : Bound) := by
  unfold boundAfterNext; rw [hF]; exact ⟨_, rfl⟩

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

/-- **Lemma 5.2**: extending `F` by `k` increases the digit count of every
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

/-- The next representable value at or above a non-negative `b` — the `Dyadic`
counterpart of `succ`, whose real value it carries (`next_coe`).

Unlike `Format.next` this has no junk branches: without a minimum quantum `0`
has no successor, and `next F 0 = 0` records that rather than inventing one. -/
noncomputable def next (F : FiniteFormat) (b : Dyadic) : Dyadic :=
  if ((b : Dyadic) : ℝ) = 0 ∧ F.exp = ⊥ then b
  else b + Dyadic.ofIntZpow 1 (F.canonicalExp ((b : Dyadic) : ℝ))

theorem next_of_ne (F : FiniteFormat) {b : Dyadic}
    (h : ¬(((b : Dyadic) : ℝ) = 0 ∧ F.exp = ⊥)) :
    F.next b = b + Dyadic.ofIntZpow 1 (F.canonicalExp ((b : Dyadic) : ℝ)) := if_neg h

/-- On positive arguments the two successors agree: `Format.next`'s step
exponent `max exp (⌊log₂ b⌋ − p + 1)` *is* `canonicalExp b`. -/
theorem next_eq_format_next (F : FiniteFormat) {b : Dyadic}
    (hb : 0 < ((b : Dyadic) : ℝ)) : F.toFormat.next b = F.next b := by
  have hne : ((b : Dyadic) : ℝ) ≠ 0 := ne_of_gt hb
  rw [FiniteFormat.next, if_neg (by simp [hne])]
  unfold Format.next FiniteFormat.canonicalExp
  cases hp : F.p using ENat.recTopCoe with
  | top =>
    cases hexp : F.exp using QExp.recBotCoe with
    | bot => exact (F.finite.elim (fun hh => hh hp) (fun hh => hh hexp)).elim
    | coe e => rfl
  | coe p =>
    cases hexp : F.exp using QExp.recBotCoe with
    | bot =>
      simp only [if_neg (not_le.mpr hb), if_neg hne, abs_of_pos hb]
      congr 2; omega
    | coe e =>
      simp only [if_neg (not_le.mpr hb), if_neg hne, abs_of_pos hb]
      congr 2; omega

end FiniteFormat


/-! ### Grid lemmas for `next`: closure, minimality, monotonicity,
midpoints, and the paper containment formats -/

/-- `b < F.next b` for finite `exp` (any `p`), `b ≥ 0`. -/
private theorem lt_next' {F : Format} {e : ℤ} (he : F.exp = (e : QExp))
    (b : Dyadic) (hb : 0 ≤ ((b : Dyadic) : ℝ)) :
    ((b : Dyadic) : ℝ) < ((F.next b : Dyadic) : ℝ) := by
  rcases hp : F.p with _ | p
  · exact Format.lt_next_of_p_top F he hp b
  · exact Format.lt_next_of_finite F he hp b hb

/-- `b < F.next b` for `b ≥ 0`, any `(p, exp)` shape. -/
theorem lt_next'' {F : Format} (b : Dyadic)
    (hb : 0 ≤ ((b : Dyadic) : ℝ)) :
    ((b : Dyadic) : ℝ) < ((F.next b : Dyadic) : ℝ) := by
  cases he : F.exp using QExp.recBotCoe with
  | bot => exact Format.lt_next_of_bot F he b
  | coe e => exact lt_next' he b hb

/-- **Step lemma** for grid closure of `next`: at a positive base
`b = m·2^s` with `logB − p + 1 ≤ s` and `next b = b + 2^s`, the successor is
`(m+1)·2^s` and stays on the `p`-bit precision grid (in the carry case
`m + 1 = 2^p` it is the pure power `2^(p+s)`). -/
private theorem next_ulp_precision {F : Format} {p : ℕ} (hp : 0 < p) {b : Dyadic}
    (hb0 : 0 < ((b : Dyadic) : ℝ)) {m s : ℤ}
    (hm : ((b : Dyadic) : ℝ) = (m : ℝ) * (2 : ℝ) ^ s)
    (hs : Int.log 2 ((b : Dyadic) : ℝ) - (p : ℤ) + 1 ≤ s)
    (h_next : F.next b = b + Dyadic.ofIntZpow 1 s) :
    Dyadic.precisionAtMost (p : Prec) (F.next b) ∧
    ((F.next b : Dyadic) : ℝ) = ((m + 1 : ℤ) : ℝ) * (2 : ℝ) ^ s := by
  have h2s_pos : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  have h_val : ((F.next b : Dyadic) : ℝ) = ((m + 1 : ℤ) : ℝ) * (2 : ℝ) ^ s := by
    rw [h_next, Dyadic.coe_real_add, coe_real_ofIntZpow_one s, hm]
    push_cast; ring
  have hm_pos : 0 < m := by
    rcases le_or_gt m 0 with hneg | hpos
    · exfalso
      have h0 : (m : ℝ) ≤ 0 := by exact_mod_cast hneg
      nlinarith
    · exact hpos
  -- `m < 2^p`: one binade above `b` clears the precision budget.
  have hm_lt : m < 2 ^ p := by
    have hb_ub : ((b : Dyadic) : ℝ)
        < (2 : ℝ) ^ (Int.log 2 ((b : Dyadic) : ℝ) + 1) :=
      Int.lt_zpow_succ_log_self (by norm_num) _
    have h3 : (m : ℝ) * (2 : ℝ) ^ s < (2 : ℝ) ^ (p : ℤ) * (2 : ℝ) ^ s := by
      have h5 : (2 : ℝ) ^ ((p : ℤ) + s)
          = (2 : ℝ) ^ (p : ℤ) * (2 : ℝ) ^ s := by
        rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      rw [← h5]
      calc (m : ℝ) * (2 : ℝ) ^ s = ((b : Dyadic) : ℝ) := hm.symm
        _ < (2 : ℝ) ^ (Int.log 2 ((b : Dyadic) : ℝ) + 1) := hb_ub
        _ ≤ (2 : ℝ) ^ ((p : ℤ) + s) :=
            zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h6 : (m : ℝ) < (2 : ℝ) ^ (p : ℤ) :=
      lt_of_mul_lt_mul_right h3 h2s_pos.le
    have h7 : (m : ℝ) < (2 : ℝ) ^ p := by
      rw [← zpow_natCast (2 : ℝ) p]; exact h6
    exact_mod_cast h7
  rcases lt_or_eq_of_le (Int.add_one_le_iff.mpr hm_lt) with h_lt | h_eq
  · -- Normal case: representation `(m + 1, s)`.
    refine ⟨?_, h_val⟩
    rw [Dyadic.precisionAtMost_coe_real]
    exact ⟨m + 1, s, h_val, by rwa [abs_of_pos (by omega : (0 : ℤ) < m + 1)]⟩
  · -- Carry case: `next b = 2^(p + s)`, representation `(1, p + s)`.
    have h_val' : ((F.next b : Dyadic) : ℝ) = (2 : ℝ) ^ ((p : ℤ) + s) := by
      rw [h_val, h_eq, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
      push_cast; ring
    refine ⟨?_, h_val⟩
    rw [Dyadic.precisionAtMost_coe_real]
    exact ⟨1, (p : ℤ) + s, by rw [h_val']; push_cast; ring,
      abs_one_lt_two_pow hp⟩

/-- **Step lemma** for grid minimality of `next`: if `b = mb·2^s`,
`g = mg·2^s`, `b < g`, and `next b = b + 2^s`, then `next b ≤ g` (a strict
increase between multiples of `2^s` is at least one step). -/
private theorem next_ulp_min {F : Format} {b g : Dyadic} {mb mg s : ℤ}
    (hmb : ((b : Dyadic) : ℝ) = (mb : ℝ) * (2 : ℝ) ^ s)
    (hmg : ((g : Dyadic) : ℝ) = (mg : ℝ) * (2 : ℝ) ^ s)
    (hbg : ((b : Dyadic) : ℝ) < ((g : Dyadic) : ℝ))
    (h_next : F.next b = b + Dyadic.ofIntZpow 1 s) :
    ((F.next b : Dyadic) : ℝ) ≤ ((g : Dyadic) : ℝ) := by
  have h2s_pos : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  have hm_lt : mb < mg := by
    have h1 : (mb : ℝ) < (mg : ℝ) := by
      rw [hmb, hmg] at hbg
      exact lt_of_mul_lt_mul_right hbg h2s_pos.le
    exact_mod_cast h1
  rw [h_next, Dyadic.coe_real_add, coe_real_ofIntZpow_one s, hmb, hmg]
  have h1 : (mb : ℝ) + 1 ≤ (mg : ℝ) := by exact_mod_cast hm_lt
  nlinarith

/-- Halving the grid step lands on the midpoint:
`b + 2^(t−1) = (b + (b + 2^t)) / 2` over `ℝ`. -/
private theorem coe_add_ulp_halves {b : Dyadic} (t : ℤ) :
    ((b + Dyadic.ofIntZpow 1 (t - 1) : Dyadic) : ℝ)
      = (((b : Dyadic) : ℝ) + ((b + Dyadic.ofIntZpow 1 t : Dyadic) : ℝ)) / 2 := by
  rw [Dyadic.coe_real_add, Dyadic.coe_real_add, coe_real_ofIntZpow_one,
    coe_real_ofIntZpow_one, zpow_sub_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
  ring

/-- **Grid closure of `next`**, finite-`exp` case: if `b` lies on the
`(p, exp)` grid, then `F.next b` does as well. -/
private theorem next_mem_unbounded {F : FiniteFormat} {e : ℤ}
    (he : F.exp = (e : QExp)) {b : Dyadic}
    (hb_mem : b ∈ F.unbounded) :
    F.toFormat.next b ∈ F.unbounded := by
  obtain ⟨hb_p, hb_q, -⟩ := hb_mem
  have hb_q' : ∃ m : ℤ, ((b : Dyadic) : ℝ) = (m : ℝ) * (2 : ℝ) ^ e := by
    rw [← Dyadic.quantumAtLeast_coe_real, ← he]; exact hb_q
  obtain ⟨m, hm⟩ := hb_q'
  cases hF_p : F.p using ENat.recTopCoe with
  | top =>
    -- `F.p = ⊤`: `next b = b + 2^e`, quantum is preserved by adding one step.
    have h_next : F.toFormat.next b = b + Dyadic.ofIntZpow 1 e :=
      Format.next_eq_p_top F.toFormat he hF_p b
    refine ⟨?_, ?_, trivial⟩
    · change Dyadic.precisionAtMost F.p _
      rw [hF_p]; trivial
    · change Dyadic.quantumAtLeast F.exp _
      rw [he, Dyadic.quantumAtLeast_coe_real]
      refine ⟨m + 1, ?_⟩
      rw [h_next, Dyadic.coe_real_add, coe_real_ofIntZpow_one e, hm]
      push_cast; ring
  | coe p =>
    by_cases hb0 : ((b : Dyadic) : ℝ) ≤ 0
    · -- `b = 0`: `next b = 2^e`.
      have h_next : F.toFormat.next b = Dyadic.ofIntZpow 1 e := by
        have h_eq : F.toFormat.next b =
            if ((b : Dyadic) : ℝ) ≤ 0 then Dyadic.ofIntZpow 1 e
            else b + Dyadic.ofIntZpow 1
              (max e (Int.log 2 ((b : Dyadic) : ℝ) - (p : ℤ) + 1)) := by
          unfold Format.next; rw [he, hF_p]
        rw [h_eq, if_pos hb0]
      refine ⟨?_, ?_, trivial⟩
      · change Dyadic.precisionAtMost F.p _
        rw [hF_p, h_next]
        exact precisionAtMost_one_zpow (by simpa using (F.p_pos hF_p).ne') e
      · change Dyadic.quantumAtLeast F.exp _
        rw [he, Dyadic.quantumAtLeast_coe_real]
        exact ⟨1, by rw [h_next, Dyadic.coe_ofIntZpow]⟩
    · -- `b > 0`: the main case.
      push Not at hb0
      have hb_p' : Dyadic.precisionAtMost (p : Prec) b := by
        rw [← hF_p]; exact hb_p
      obtain ⟨c, q, hc_eq, hc_odd, -, -, -, hlog_lt⟩ :=
        exists_odd_canonical_pos hb_p' hb0
      -- `e ≤ q`: an odd significand cannot absorb a coarser quantum.
      have hqe : e ≤ q := quantum_le_of_odd_rep (he ▸ hb_q) hc_odd hc_eq
      have h_next := Format.next_eq_finite_pos F.toFormat he hF_p hb0
      set logB := Int.log 2 ((b : Dyadic) : ℝ) with hlogB_def
      -- step exponent `s`, with `e ≤ s ≤ q`.
      set s := max e (logB - (p : ℤ) + 1) with hs_def
      have hs_le_q : s ≤ q := max_le hqe (by omega)
      have he_le_s : e ≤ s := le_max_left _ _
      have hm : ((b : Dyadic) : ℝ)
          = ((c * 2 ^ ((q - s).toNat) : ℤ) : ℝ) * (2 : ℝ) ^ s := by
        rw [hc_eq, two_zpow_split_toNat hs_le_q]
        push_cast; ring
      obtain ⟨h_prec, h_val⟩ :=
        next_ulp_precision (p := p) (F.p_pos hF_p) hb0 hm (le_max_right _ _) h_next
      refine ⟨?_, ?_, trivial⟩
      · change Dyadic.precisionAtMost F.p _
        rw [hF_p]; exact h_prec
      · change Dyadic.quantumAtLeast F.exp _
        rw [he, Dyadic.quantumAtLeast_coe_real]
        refine ⟨(c * 2 ^ ((q - s).toNat) + 1) * 2 ^ ((s - e).toNat), ?_⟩
        rw [h_val, two_zpow_split_toNat he_le_s]
        push_cast; ring

/-- Grid closure of `next`, `exp = ⊥` case (`p` is finite by
`FiniteFormat.finite`; the step is purely binade-dependent, and `b = 0`
falls back to `next 0 = 1`, which is also on the grid). -/
private theorem next_mem_unbounded_bot {F : FiniteFormat} (he : F.exp = ⊥)
    {b : Dyadic} (hb_mem : b ∈ F.unbounded) (hb_nn : 0 ≤ ((b : Dyadic) : ℝ)) :
    F.toFormat.next b ∈ F.unbounded := by
  obtain ⟨hb_p, hb_q, -⟩ := hb_mem
  obtain ⟨p, hF_p⟩ := exists_p_coe_of_exp_bot (he : F.exp = ⊥)
  by_cases hb0 : ((b : Dyadic) : ℝ) ≤ 0
  · -- `b = 0`: `next b = 1`.
    have h_next : F.toFormat.next b = b + 1 :=
      Format.next_eq_bot_nonpos F.toFormat he hb0
    have hb_zero : b = 0 := (Dyadic.coe_real_inj b 0).mp
      (by rw [Dyadic.coe_real_zero]; exact le_antisymm hb0 hb_nn)
    rw [h_next, hb_zero, zero_add]
    refine ⟨?_, ?_, trivial⟩
    · change Dyadic.precisionAtMost F.p (1 : Dyadic)
      rw [hF_p, Dyadic.precisionAtMost_coe]
      refine ⟨1, 0, by push_cast; norm_num, abs_one_lt_two_pow (F.p_pos hF_p)⟩
    · change Dyadic.quantumAtLeast F.exp (1 : Dyadic)
      rw [he]
      trivial
  · -- `b > 0`: the binade-dependent step; mirrors the finite-`exp` case
    -- with `s := logB − p + 1` (no `max`, and the quantum is trivial).
    push Not at hb0
    have hb_p' : Dyadic.precisionAtMost (p : Prec) b := by
      rw [← hF_p]; exact hb_p
    obtain ⟨c, q, hc_eq, -, -, -, -, hlog_lt⟩ :=
      exists_odd_canonical_pos hb_p' hb0
    have h_next := Format.next_eq_bot_pos F.toFormat he hF_p hb0
    set logB := Int.log 2 ((b : Dyadic) : ℝ) with hlogB_def
    set s := logB - (p : ℤ) + 1 with hs_def
    have hs_le_q : s ≤ q := by omega
    have hm : ((b : Dyadic) : ℝ)
        = ((c * 2 ^ ((q - s).toNat) : ℤ) : ℝ) * (2 : ℝ) ^ s := by
      rw [hc_eq, two_zpow_split_toNat hs_le_q]
      push_cast; ring
    obtain ⟨h_prec, -⟩ := next_ulp_precision (p := p) (F.p_pos hF_p) hb0 hm le_rfl h_next
    refine ⟨?_, ?_, trivial⟩
    · change Dyadic.precisionAtMost F.p _
      rw [hF_p]; exact h_prec
    · change Dyadic.quantumAtLeast F.exp _
      rw [he]
      trivial

/-- Grid closure of `next`, any `exp`. -/
theorem next_mem_unbounded' {F : FiniteFormat} {b : Dyadic}
    (hb_mem : b ∈ F.unbounded) (hb_nn : 0 ≤ ((b : Dyadic) : ℝ)) :
    F.toFormat.next b ∈ F.unbounded := by
  cases he : F.exp using QExp.recBotCoe with
  | bot => exact next_mem_unbounded_bot he hb_mem hb_nn
  | coe e => exact next_mem_unbounded he hb_mem

/-- **Grid minimality of `next`**: for `b ≥ 0` on the grid and finite `exp`,
any grid point strictly above `b` is at least `F.next b` — i.e. the grid has
no point in `(b, next b)`. -/
private theorem next_min {F : FiniteFormat} {e : ℤ}
    (he : F.exp = (e : QExp)) {b g : Dyadic}
    (hb_mem : b ∈ F.unbounded) (hg_mem : g ∈ F.unbounded)
    (hb_nn : 0 ≤ ((b : Dyadic) : ℝ))
    (hbg : ((b : Dyadic) : ℝ) < ((g : Dyadic) : ℝ)) :
    ((F.toFormat.next b : Dyadic) : ℝ) ≤ ((g : Dyadic) : ℝ) := by
  obtain ⟨hb_p, hb_q, -⟩ := hb_mem
  obtain ⟨hg_p, hg_q, -⟩ := hg_mem
  cases hF_p : F.p using ENat.recTopCoe with
  | top =>
    -- Both are multiples of `2^e`; a strict increase is at least one step.
    have h_next : F.toFormat.next b = b + Dyadic.ofIntZpow 1 e :=
      Format.next_eq_p_top F.toFormat he hF_p b
    obtain ⟨mb, hmb⟩ : ∃ m : ℤ, ((b : Dyadic) : ℝ) = (m : ℝ) * (2 : ℝ) ^ e := by
      rw [← Dyadic.quantumAtLeast_coe_real, ← he]; exact hb_q
    obtain ⟨mg, hmg⟩ : ∃ m : ℤ, ((g : Dyadic) : ℝ) = (m : ℝ) * (2 : ℝ) ^ e := by
      rw [← Dyadic.quantumAtLeast_coe_real, ← he]; exact hg_q
    exact next_ulp_min hmb hmg hbg h_next
  | coe p =>
    have hg_pos : 0 < ((g : Dyadic) : ℝ) := lt_of_le_of_lt hb_nn hbg
    have hg_p' : Dyadic.precisionAtMost (p : Prec) g := by
      rw [← hF_p]; exact hg_p
    obtain ⟨cg, qg, hg_eq, hg_odd, -, hg_lb, -, hg_log_lt⟩ :=
      exists_odd_canonical_pos hg_p' hg_pos
    have he_qg : e ≤ qg := quantum_le_of_odd_rep (he ▸ hg_q) hg_odd hg_eq
    by_cases hb0 : ((b : Dyadic) : ℝ) ≤ 0
    · -- `b = 0`: `next b = 2^e ≤ 2^qg ≤ g`.
      have h_next : F.toFormat.next b = Dyadic.ofIntZpow 1 e := by
        have h_eq : F.toFormat.next b =
            if ((b : Dyadic) : ℝ) ≤ 0 then Dyadic.ofIntZpow 1 e
            else b + Dyadic.ofIntZpow 1
              (max e (Int.log 2 ((b : Dyadic) : ℝ) - (p : ℤ) + 1)) := by
          unfold Format.next; rw [he, hF_p]
        rw [h_eq, if_pos hb0]
      rw [h_next, coe_real_ofIntZpow_one e]
      have h1 : (2 : ℝ) ^ e ≤ (2 : ℝ) ^ qg :=
        zpow_le_zpow_right₀ (by norm_num) he_qg
      linarith
    · -- `b > 0`: both are multiples of the step `2^s`.
      push Not at hb0
      have hb_p' : Dyadic.precisionAtMost (p : Prec) b := by
        rw [← hF_p]; exact hb_p
      obtain ⟨cb, qb, hb_eq, hb_odd, -, -, -, hb_log_lt⟩ :=
        exists_odd_canonical_pos hb_p' hb0
      have he_qb : e ≤ qb := quantum_le_of_odd_rep (he ▸ hb_q) hb_odd hb_eq
      have h_next := Format.next_eq_finite_pos F.toFormat he hF_p hb0
      have hlog_qg' : Int.log 2 ((b : Dyadic) : ℝ) < qg + (p : ℤ) :=
        lt_of_le_of_lt (Int.log_mono_right hb0 hbg.le) hg_log_lt
      set logB := Int.log 2 ((b : Dyadic) : ℝ) with hlogB_def
      set s := max e (logB - (p : ℤ) + 1) with hs_def
      have hs_le_qb : s ≤ qb := max_le he_qb (by omega)
      have hs_le_qg : s ≤ qg := max_le he_qg (by omega)
      -- both as multiples of `2^s`
      have hkb : ((b : Dyadic) : ℝ) = ((cb * 2 ^ ((qb - s).toNat) : ℤ) : ℝ) * (2 : ℝ) ^ s := by
        rw [hb_eq, two_zpow_split_toNat hs_le_qb]
        push_cast; ring
      have hkg : ((g : Dyadic) : ℝ) = ((cg * 2 ^ ((qg - s).toNat) : ℤ) : ℝ) * (2 : ℝ) ^ s := by
        rw [hg_eq, two_zpow_split_toNat hs_le_qg]
        push_cast; ring
      exact next_ulp_min hkb hkg hbg h_next

/-- Grid minimality of `next`, `exp = ⊥` case. Requires `b > 0` (at `b = 0`
no grid successor exists). -/
private theorem next_min_bot {F : FiniteFormat} (he : F.exp = ⊥) {b g : Dyadic}
    (hb_mem : b ∈ F.unbounded) (hg_mem : g ∈ F.unbounded)
    (hb_pos : 0 < ((b : Dyadic) : ℝ))
    (hbg : ((b : Dyadic) : ℝ) < ((g : Dyadic) : ℝ)) :
    ((F.toFormat.next b : Dyadic) : ℝ) ≤ ((g : Dyadic) : ℝ) := by
  obtain ⟨hb_p, -, -⟩ := hb_mem
  obtain ⟨hg_p, -, -⟩ := hg_mem
  obtain ⟨p, hF_p⟩ := exists_p_coe_of_exp_bot (he : F.exp = ⊥)
  have hg_pos : 0 < ((g : Dyadic) : ℝ) := lt_trans hb_pos hbg
  have hg_p' : Dyadic.precisionAtMost (p : Prec) g := by
    rw [← hF_p]; exact hg_p
  have hb_p' : Dyadic.precisionAtMost (p : Prec) b := by
    rw [← hF_p]; exact hb_p
  obtain ⟨cg, qg, hg_eq, -, -, -, -, hg_log_lt⟩ :=
    exists_odd_canonical_pos hg_p' hg_pos
  obtain ⟨cb, qb, hb_eq, -, -, -, -, hb_log_lt⟩ :=
    exists_odd_canonical_pos hb_p' hb_pos
  have h_next := Format.next_eq_bot_pos F.toFormat he hF_p hb_pos
  have hlog_qg' : Int.log 2 ((b : Dyadic) : ℝ) < qg + (p : ℤ) :=
    lt_of_le_of_lt (Int.log_mono_right hb_pos hbg.le) hg_log_lt
  set logB := Int.log 2 ((b : Dyadic) : ℝ) with hlogB_def
  set s := logB - (p : ℤ) + 1 with hs_def
  have hs_le_qb : s ≤ qb := by omega
  have hs_le_qg : s ≤ qg := by omega
  have hkb : ((b : Dyadic) : ℝ) = ((cb * 2 ^ ((qb - s).toNat) : ℤ) : ℝ) * (2 : ℝ) ^ s := by
    rw [hb_eq, two_zpow_split_toNat hs_le_qb]
    push_cast; ring
  have hkg : ((g : Dyadic) : ℝ) = ((cg * 2 ^ ((qg - s).toNat) : ℤ) : ℝ) * (2 : ℝ) ^ s := by
    rw [hg_eq, two_zpow_split_toNat hs_le_qg]
    push_cast; ring
  exact next_ulp_min hkb hkg hbg h_next

/-- Grid minimality of `next`, any `exp` (for `exp = ⊥` the base point must
be positive). -/
theorem next_min' {F : FiniteFormat} {b g : Dyadic}
    (hb_mem : b ∈ F.unbounded) (hg_mem : g ∈ F.unbounded)
    (hb_nn : 0 ≤ ((b : Dyadic) : ℝ))
    (hguard : F.exp = ⊥ → 0 < ((b : Dyadic) : ℝ))
    (hbg : ((b : Dyadic) : ℝ) < ((g : Dyadic) : ℝ)) :
    ((F.toFormat.next b : Dyadic) : ℝ) ≤ ((g : Dyadic) : ℝ) := by
  cases he : F.exp using QExp.recBotCoe with
  | bot => exact next_min_bot he hb_mem hg_mem (hguard he) hbg
  | coe e => exact next_min he hb_mem hg_mem hb_nn hbg

/-- Package of basic `next` facts over an on-grid base point `b₁`:
non-negativity of the base, strict growth, non-negativity, and grid
membership of the successor. -/
theorem next_facts {F₁ : FiniteFormat} {b₁ : NonNegDyadic}
    (hb₁_mem : b₁.val ∈ F₁) :
    0 ≤ ((b₁.val : Dyadic) : ℝ) ∧
    ((b₁.val : Dyadic) : ℝ) < ((F₁.toFormat.next b₁.val : Dyadic) : ℝ) ∧
    0 ≤ ((F₁.toFormat.next b₁.val : Dyadic) : ℝ) ∧
    F₁.toFormat.next b₁.val ∈ F₁.unbounded := by
  have hb₁_nn : 0 ≤ ((b₁.val : Dyadic) : ℝ) := nonneg_coe_real b₁
  have hN_lt : ((b₁.val : Dyadic) : ℝ) < ((F₁.toFormat.next b₁.val : Dyadic) : ℝ) :=
    lt_next'' b₁.val hb₁_nn
  exact ⟨hb₁_nn, hN_lt, le_trans hb₁_nn hN_lt.le,
    next_mem_unbounded' (mem_unbounded_of_mem hb₁_mem) hb₁_nn⟩

/-- `next` is monotone on `[0, ∞)` (for `exp = ⊥` the smaller point must be
positive, since `next` is junk at `0` there). -/
theorem next_mono {F : Format} {d b : Dyadic}
    (hdb : ((d : Dyadic) : ℝ) ≤ ((b : Dyadic) : ℝ))
    (hguard : F.exp = ⊥ → 0 < ((d : Dyadic) : ℝ)) :
    ((F.next d : Dyadic) : ℝ) ≤ ((F.next b : Dyadic) : ℝ) := by
  cases he : F.exp using QExp.recBotCoe with
  | bot =>
    have hd_pos := hguard he
    have hb_pos : 0 < ((b : Dyadic) : ℝ) := lt_of_lt_of_le hd_pos hdb
    cases hp : F.p using ENat.recTopCoe with
    | top =>
      rw [Format.next_eq_bot_p_top' F he hp d, Format.next_eq_bot_p_top' F he hp b]
      push_cast
      linarith
    | coe p =>
      rw [Format.next_eq_bot_pos F he hp hd_pos, Format.next_eq_bot_pos F he hp hb_pos,
        Dyadic.coe_real_add, Dyadic.coe_real_add, Dyadic.coe_ofIntZpow,
        Dyadic.coe_ofIntZpow]
      have hlog : Int.log 2 ((d : Dyadic) : ℝ) ≤ Int.log 2 ((b : Dyadic) : ℝ) :=
        Int.log_mono_right hd_pos hdb
      have hzp : (2 : ℝ) ^ (Int.log 2 ((d : Dyadic) : ℝ) - (p : ℤ) + 1)
          ≤ (2 : ℝ) ^ (Int.log 2 ((b : Dyadic) : ℝ) - (p : ℤ) + 1) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      push_cast
      linarith
  | coe e =>
    cases hp : F.p using ENat.recTopCoe with
    | top =>
      rw [Format.next_eq_p_top F he hp d, Format.next_eq_p_top F he hp b,
        Dyadic.coe_real_add, Dyadic.coe_real_add]
      linarith
    | coe p =>
      by_cases hd0 : ((d : Dyadic) : ℝ) ≤ 0
      · have h_eqd : F.next d = Dyadic.ofIntZpow 1 e := by
          have h_eq : F.next d =
              if ((d : Dyadic) : ℝ) ≤ 0 then Dyadic.ofIntZpow 1 e
              else d + Dyadic.ofIntZpow 1
                (max e (Int.log 2 ((d : Dyadic) : ℝ) - (p : ℤ) + 1)) := by
            unfold Format.next; rw [he, hp]
          rw [h_eq, if_pos hd0]
        by_cases hb0 : ((b : Dyadic) : ℝ) ≤ 0
        · have h_eqb : F.next b = Dyadic.ofIntZpow 1 e := by
            have h_eq : F.next b =
                if ((b : Dyadic) : ℝ) ≤ 0 then Dyadic.ofIntZpow 1 e
                else b + Dyadic.ofIntZpow 1
                  (max e (Int.log 2 ((b : Dyadic) : ℝ) - (p : ℤ) + 1)) := by
              unfold Format.next; rw [he, hp]
            rw [h_eq, if_pos hb0]
          rw [h_eqd, h_eqb]
        · push Not at hb0
          rw [h_eqd, Format.next_eq_finite_pos F he hp hb0, Dyadic.coe_real_add,
            Dyadic.coe_ofIntZpow, Dyadic.coe_ofIntZpow]
          have h1 : (2 : ℝ) ^ e
              ≤ (2 : ℝ) ^ (max e (Int.log 2 ((b : Dyadic) : ℝ) - (p : ℤ) + 1)) :=
            zpow_le_zpow_right₀ (by norm_num) (le_max_left _ _)
          push_cast
          linarith
      · push Not at hd0
        have hb0 : 0 < ((b : Dyadic) : ℝ) := lt_of_lt_of_le hd0 hdb
        rw [Format.next_eq_finite_pos F he hp hd0, Format.next_eq_finite_pos F he hp hb0,
          Dyadic.coe_real_add, Dyadic.coe_real_add, Dyadic.coe_ofIntZpow,
          Dyadic.coe_ofIntZpow]
        have hlog : Int.log 2 ((d : Dyadic) : ℝ) ≤ Int.log 2 ((b : Dyadic) : ℝ) :=
          Int.log_mono_right hd0 hdb
        have hzp : (2 : ℝ) ^ (max e (Int.log 2 ((d : Dyadic) : ℝ) - (p : ℤ) + 1))
            ≤ (2 : ℝ) ^ (max e (Int.log 2 ((b : Dyadic) : ℝ) - (p : ℤ) + 1)) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
        push_cast
        linarith

/-- An extension with `exp = ⊥` comes from a base with `exp = ⊥`. -/
theorem exp_bot_of_extend_bot {F₁ : FiniteFormat} {k : ℕ}
    (h : (F₁.extend k).toFormat.exp = ⊥) : F₁.exp = ⊥ := by
  cases hc : F₁.exp using QExp.recBotCoe with
  | bot => rfl
  | coe e =>
    exfalso
    have h' : F₁.exp.map (· - (k : ℤ)) = ⊥ := h
    rw [hc] at h'
    exact absurd h' (by simp)

/-- `next` on `F₁.extend 1` lands exactly on the midpoint of `b` and
`F₁.next b`: extending by one bit halves the grid step. -/
private theorem next_extend_midpoint {F₁ : FiniteFormat} {e₁ : ℤ}
    (he₁ : F₁.exp = (e₁ : QExp)) {b : Dyadic}
    (hb_nn : 0 ≤ ((b : Dyadic) : ℝ)) :
    (((F₁.extend 1).toFormat.next b : Dyadic) : ℝ)
      = (((b : Dyadic) : ℝ) + ((F₁.toFormat.next b : Dyadic) : ℝ)) / 2 := by
  have he₁x : (F₁.extend 1).toFormat.exp = ((e₁ - 1 : ℤ) : QExp) := by
    change F₁.exp.map (· - ((1 : ℕ) : ℤ)) = _
    rw [he₁]
    rfl
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  cases hp : F₁.p using ENat.recTopCoe with
  | top =>
    have hpx : (F₁.extend 1).toFormat.p = ⊤ := by
      change F₁.p + ((1 : ℕ) : Prec) = ⊤
      rw [hp]; rfl
    rw [Format.next_eq_p_top F₁.toFormat he₁ hp b,
      Format.next_eq_p_top (F₁.extend 1).toFormat he₁x hpx b]
    exact coe_add_ulp_halves e₁
  | coe p =>
    have hpx : (F₁.extend 1).toFormat.p = ((p + 1 : ℕ) : Prec) := by
      change F₁.p + ((1 : ℕ) : Prec) = _
      rw [hp, ← Nat.cast_add]
    by_cases hb0 : ((b : Dyadic) : ℝ) ≤ 0
    · -- `b = 0`: both `next`s are pure powers of two.
      have h_next : F₁.toFormat.next b = Dyadic.ofIntZpow 1 e₁ := by
        have h_eq : F₁.toFormat.next b =
            if ((b : Dyadic) : ℝ) ≤ 0 then Dyadic.ofIntZpow 1 e₁
            else b + Dyadic.ofIntZpow 1
              (max e₁ (Int.log 2 ((b : Dyadic) : ℝ) - (p : ℤ) + 1)) := by
          unfold Format.next; rw [he₁, hp]
        rw [h_eq, if_pos hb0]
      have h_nextx : (F₁.extend 1).toFormat.next b = Dyadic.ofIntZpow 1 (e₁ - 1) := by
        have h_eq : (F₁.extend 1).toFormat.next b =
            if ((b : Dyadic) : ℝ) ≤ 0 then Dyadic.ofIntZpow 1 (e₁ - 1)
            else b + Dyadic.ofIntZpow 1
              (max (e₁ - 1)
                (Int.log 2 ((b : Dyadic) : ℝ) - (((p + 1 : ℕ) : ℕ) : ℤ) + 1)) := by
          unfold Format.next; rw [he₁x, hpx]
        rw [h_eq, if_pos hb0]
      have hb_eq : ((b : Dyadic) : ℝ) = 0 := le_antisymm hb0 hb_nn
      rw [h_next, h_nextx, coe_real_ofIntZpow_one, coe_real_ofIntZpow_one, hb_eq, zpow_sub_one₀ h2]
      ring
    · -- `b > 0`: the step exponent drops by exactly one.
      push Not at hb0
      have h_next := Format.next_eq_finite_pos F₁.toFormat he₁ hp hb0
      have h_nextx := Format.next_eq_finite_pos (F₁.extend 1).toFormat he₁x hpx hb0
      have h_max : max (e₁ - 1)
            (Int.log 2 ((b : Dyadic) : ℝ) - (((p + 1 : ℕ) : ℕ) : ℤ) + 1)
          = max e₁ (Int.log 2 ((b : Dyadic) : ℝ) - (p : ℤ) + 1) - 1 := by
        have hcast : (((p + 1 : ℕ) : ℕ) : ℤ) = (p : ℤ) + 1 := by
          push_cast; ring
        rw [hcast]
        omega
      rw [h_next, h_nextx, h_max]
      exact coe_add_ulp_halves _

/-- `next` on `F₁.extend 1`, `exp = ⊥` case: the binade step still halves.
Requires `b > 0`. -/
private theorem next_extend_midpoint_bot {F₁ : FiniteFormat} (he₁ : F₁.exp = ⊥)
    {b : Dyadic} (hb_pos : 0 < ((b : Dyadic) : ℝ)) :
    (((F₁.extend 1).toFormat.next b : Dyadic) : ℝ)
      = (((b : Dyadic) : ℝ) + ((F₁.toFormat.next b : Dyadic) : ℝ)) / 2 := by
  have he₁x : (F₁.extend 1).toFormat.exp = ⊥ := by
    change F₁.exp.map (· - ((1 : ℕ) : ℤ)) = ⊥
    rw [he₁]
    rfl
  obtain ⟨p, hF_p⟩ := exists_p_coe_of_exp_bot (he₁ : F₁.exp = ⊥)
  have hpx : (F₁.extend 1).toFormat.p = ((p + 1 : ℕ) : Prec) := by
    change F₁.p + ((1 : ℕ) : Prec) = _
    rw [hF_p, ← Nat.cast_add]
  rw [Format.next_eq_bot_pos F₁.toFormat he₁ hF_p hb_pos,
    Format.next_eq_bot_pos (F₁.extend 1).toFormat he₁x hpx hb_pos]
  have h_idx : Int.log 2 ((b : Dyadic) : ℝ) - (((p + 1 : ℕ) : ℕ) : ℤ) + 1
      = (Int.log 2 ((b : Dyadic) : ℝ) - (p : ℤ) + 1) - 1 := by
    have hcast : (((p + 1 : ℕ) : ℕ) : ℤ) = (p : ℤ) + 1 := by
      push_cast; ring
    omega
  rw [h_idx]
  exact coe_add_ulp_halves _

/-- `next` on `F₁.extend 1` is the midpoint, any `exp` (for `exp = ⊥` the
base point must be positive). -/
theorem next_extend_midpoint' {F₁ : FiniteFormat} {b : Dyadic}
    (hb_nn : 0 ≤ ((b : Dyadic) : ℝ))
    (hguard : F₁.exp = ⊥ → 0 < ((b : Dyadic) : ℝ)) :
    (((F₁.extend 1).toFormat.next b : Dyadic) : ℝ)
      = (((b : Dyadic) : ℝ) + ((F₁.toFormat.next b : Dyadic) : ℝ)) / 2 := by
  cases he : F₁.exp using QExp.recBotCoe with
  | bot => exact next_extend_midpoint_bot he (hguard he)
  | coe e => exact next_extend_midpoint he hb_nn

/-- `F.withBound B`, packaged as a `FiniteFormat` (`p`/`exp` unchanged). -/
def FiniteFormat.withBoundFF (F : FiniteFormat) (B : Bound) :
    FiniteFormat :=
  ⟨F.toFormat.withBound B, F.finite, F.pos⟩

/-- `next(b₁)` satisfies the relaxed bound `boundAfterNext`. -/
theorem boundOK_boundAfterNext_next {F₁ : FiniteFormat} {b₁ : NonNegDyadic}
    (hF₁b : F₁.b = (b₁ : Bound))
    (hN_nn : 0 ≤ ((F₁.toFormat.next b₁.val : Dyadic) : ℝ)) :
    Format.boundOK F₁.toFormat.boundAfterNext (F₁.toFormat.next b₁.val) := by
  obtain ⟨hnn, h_eq⟩ := Format.boundAfterNext_coe hF₁b
  rw [h_eq]
  have hN_nn_q : (0 : ℚ) ≤ ((F₁.toFormat.next b₁.val : Dyadic) : ℚ) := by
    rw [Dyadic.coe_real_eq_ratCast] at hN_nn
    exact_mod_cast hN_nn
  change |((F₁.toFormat.next b₁.val : Dyadic) : ℚ)|
    ≤ ((F₁.toFormat.next b₁.val : Dyadic) : ℚ)
  rw [abs_of_nonneg hN_nn_q]

/-- The relaxed bound `boundAfterNext` accepts anything the original bound
accepts (`b₁ ≤ next(b₁)`). -/
theorem boundOK_boundAfterNext_of_boundOK {F₁ : FiniteFormat} {d : Dyadic}
    (hd_b : Format.boundOK F₁.b d) :
    Format.boundOK F₁.toFormat.boundAfterNext d := by
  cases hF_b : F₁.b using Bound.recTopCoe with
  | top => rw [Format.boundAfterNext_top hF_b]; trivial
  | coe b =>
    obtain ⟨hnn, h_after⟩ := Format.boundAfterNext_coe hF_b
    rw [h_after]
    rw [hF_b] at hd_b
    have hd_b' : |(d : ℚ)| ≤ ((b.val : Dyadic) : ℚ) := hd_b
    have hb_nn : 0 ≤ ((b.val : Dyadic) : ℝ) := nonneg_coe_real b
    have h_le : ((b.val : Dyadic) : ℚ) ≤ ((F₁.toFormat.next b.val : Dyadic) : ℚ) := by
      have h := Format.self_le_next F₁.toFormat b.val hb_nn
      rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast] at h
      exact_mod_cast h
    change |(d : ℚ)| ≤ ((F₁.toFormat.next b.val : Dyadic) : ℚ)
    linarith

/-- Antitonicity of the relaxed bound: if `G` shares `F`'s grid (so their
`next` agree definitionally) but carries a bound `D` with
`next(D) ≤ next(b₁)`, then `G`'s relaxed bound implies `F`'s. -/
theorem boundOK_boundAfterNext_mono {F G : FiniteFormat} {b₁ D : NonNegDyadic}
    {v : Dyadic} (hFb : F.b = (b₁ : Bound))
    (hGb : G.b = (D : Bound))
    (hnext : G.toFormat.next D.val = F.toFormat.next D.val)
    (hmono : ((F.toFormat.next D.val : Dyadic) : ℝ)
      ≤ ((F.toFormat.next b₁.val : Dyadic) : ℝ))
    (hv : Format.boundOK G.toFormat.boundAfterNext v) :
    Format.boundOK F.toFormat.boundAfterNext v := by
  obtain ⟨hnnG, h_eqG⟩ := Format.boundAfterNext_coe hGb
  obtain ⟨hnnF, h_eqF⟩ := Format.boundAfterNext_coe hFb
  rw [h_eqG] at hv
  rw [h_eqF]
  have h1 : |(v : ℚ)| ≤ ((G.toFormat.next D.val : Dyadic) : ℚ) := hv
  rw [hnext] at h1
  have h2 : ((F.toFormat.next D.val : Dyadic) : ℚ)
      ≤ ((F.toFormat.next b₁.val : Dyadic) : ℚ) := by
    rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast] at hmono
    exact_mod_cast hmono
  change |(v : ℚ)| ≤ ((F.toFormat.next b₁.val : Dyadic) : ℚ)
  linarith

/-- Membership transfer into the paper containment format: every `d ∈ F₁`
lies in `(F₁.extend 1).withBound F₁.boundAfterNext` (one more bit of
precision, bound relaxed from `b₁` to `next(b₁)`). -/
theorem mem_paper_of_mem {F₁ : FiniteFormat} {d : Dyadic} (hd : d ∈ F₁) :
    d ∈ ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) := by
  have hd' : d ∈ (F₁.extend 1) := Format.self_subset_extend F₁.toFormat 1 d hd
  exact ⟨hd'.1, hd'.2.1, boundOK_boundAfterNext_of_boundOK hd.2.2⟩

/-- Unbounded grid membership plus the relaxed bound gives membership in the
paper containment format `(F₁.extend 1).withBound F₁.boundAfterNext`. -/
theorem mem_paper_of_mem_unbounded {F₁ : FiniteFormat} {d : Dyadic}
    (hd : d ∈ F₁.unbounded)
    (hb : Format.boundOK F₁.toFormat.boundAfterNext d) :
    d ∈ ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) := by
  have hd' := Format.self_subset_extend F₁.toFormat.unbounded 1 d hd
  exact ⟨hd'.1, hd'.2.1, hb⟩

/-- If the *unbounded* `F₁` grid (bound `⊤`, here via
`withBound boundAfterNext` with `F₁.b = ⊤`) is contained in `F₂`, then `F₂`
cannot have a finite bound: the grid contains arbitrarily large powers of
two. -/
theorem bound_top_of_withBound_top_subset {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound ⊤) ⊆ F₂.toFormat) : F₂.b = ⊤ := by
  by_contra h
  obtain ⟨b₂, hb₂⟩ : ∃ b₂ : NonNegDyadic, F₂.b = (b₂ : Bound) := by
    cases hc : F₂.b using Bound.recTopCoe with
    | top => exact absurd hc h
    | coe b₂ => exact ⟨b₂, rfl⟩
  set E := WithBot.unbotD 0 F₁.exp with hE_def
  set K := max E (Int.log 2 ((b₂.val : Dyadic) : ℚ) + 1) with hK_def
  set w := Dyadic.ofIntZpow 1 K with hw_def
  have hw_mem : w ∈ (F₁.toFormat.withBound ⊤) := by
    refine ⟨?_, ?_, ?_⟩
    · change Dyadic.precisionAtMost F₁.p w
      exact precisionAtMost_one_zpow F₁.pos K
    · change Dyadic.quantumAtLeast F₁.exp w
      cases hexp : F₁.exp using QExp.recBotCoe with
      | bot => trivial
      | coe e =>
        rw [Dyadic.quantumAtLeast_coe]
        have hE : E = e := by rw [hE_def, hexp]; rfl
        have hKe : e ≤ K := by rw [← hE]; exact le_max_left _ _
        refine ⟨2 ^ (K - e).toNat, ?_⟩
        rw [hw_def, Dyadic.coe_rat_ofIntZpow]
        have hk : ((K - e).toNat : ℤ) = K - e := Int.toNat_of_nonneg (by omega)
        push_cast
        rw [← zpow_natCast (2 : ℚ) ((K - e).toNat), hk,
          ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), sub_add_cancel]
        ring
    · change Format.boundOK (⊤ : Bound) w
      trivial
  have hb_w : Format.boundOK F₂.b w := (hsub w hw_mem).2.2
  rw [hb₂] at hb_w
  have hb_w' : |(w : ℚ)| ≤ ((b₂.val : Dyadic) : ℚ) := hb_w
  have h2K_pos : (0 : ℚ) < (2 : ℚ) ^ K := zpow_pos (by norm_num) _
  have hw_val : |(w : ℚ)| = (2 : ℚ) ^ K := by
    rw [hw_def, Dyadic.coe_rat_ofIntZpow]
    push_cast
    rw [one_mul, abs_of_pos h2K_pos]
  have hlt : ((b₂.val : Dyadic) : ℚ) < (2 : ℚ) ^ K :=
    lt_of_lt_of_le (Int.lt_zpow_succ_log_self (by norm_num) _)
      (zpow_le_zpow_right₀ (by norm_num) (le_max_right _ _))
  rw [hw_val] at hb_w'
  linarith

/-- Specialization: the paper containment with `F₁.b = ⊤` forces `F₂.b = ⊤`. -/
theorem bound_top_of_paper_subset {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hb_top : F₁.b = ⊤) : F₂.b = ⊤ := by
  rw [Format.boundAfterNext_top hb_top] at hsub
  exact bound_top_of_withBound_top_subset hsub

end Mpfx
