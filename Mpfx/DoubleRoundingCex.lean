import Mpfx.Rounding

/-!
# Counterexamples to invalid double-rounding pairings

Over `{RNE, RTZ, RAZ, RTO}²`, six pairings are *correctly* double rounding
(the rules in `Mpfx/DoubleRounding.lean`): any `(RTO, *)`, plus
`(RTZ, RTZ)` and `(RAZ, RAZ)`. This file proves counterexamples for the
remaining ten pairings: for every `F₁` of the form `𝒜(p, e, ⊤)` with
`p ≥ 2` and an appropriately compatible `F₂`, there is a real `x` whose
chained F₂-then-F₁ rounding disagrees with the direct F₁ rounding.

The conceptually distinct positive results live in
`Mpfx/DoubleRounding.lean`. This file only depends on the rounding-
relation infrastructure (`Mpfx.Rounding`) and the F-adjacency lemmas
in `Mpfx.Format`, not on those positive theorems.

## Theorems

**Proven:**
* `no_rndRNE_RNE` — the canonical RNE-RNE counterexample.
  Witness `x = 55·2^(e-4)` (just below the F₁-midpoint `7·2^(e-1)`);
  F₂-RNE rounds to the midpoint; F₁-RNE breaks the tie to the even
  neighbor; direct F₁-RNE picks the odd (closer) neighbor.
  Core proof: `no_rndRNE_RNE_arbitrary_F₂`.
* `no_rndRNE_RAZ` — F₂-RNE rounds a small positive `x` down to
  `0`; F₁-RAZ keeps `0`; direct F₁-RAZ rounds up to the smallest
  positive F₁-element.
* `no_rndRNE_RTZ` — F₂-RNE in upper half pushes `x` up to an
  F₁-element; F₁-RTZ keeps it; direct F₁-RTZ truncates down to the
  previous F₁-element.
* `no_rndRTZ_RAZ` — F₂-RTZ truncates `x` to an F₁-element;
  F₁-RAZ keeps it; direct F₁-RAZ rounds up to the next F₁-element.
* `no_rndRAZ_RTZ` — F₂-RAZ pushes `x` up to an F₁-element;
  F₁-RTZ keeps it; direct F₁-RTZ truncates down to `0`.
* `no_rndRAZ_RTO` — F₂-RAZ pushes `x` up to an even-significand
  F₁-element; F₁-RTO returns it; direct F₁-RTO cannot return it
  (the parity clause demands odd, contradicting `IsEven`).
* `no_rndRNE_RTO` — F₂-RNE rounds `x` onto an even-significand
  F₁-element (same witness shape as RAZ-RTO); F₁-RTO returns it;
  direct F₁-RTO fails by the same parity argument.
* `no_rndRTZ_RTO` — F₂-RTZ truncates `x` down to an even-significand
  F₁-element; F₁-RTO returns it; direct F₁-RTO fails by the same
  parity argument.
* `no_rndRAZ_RNE` — F₂-RAZ pushes `x` up to the F₁-midpoint
  `m = 7·2^(e−1)`; F₁-RNE tie-breaks to the even neighbor
  `y_hi = 4·2^e`; direct F₁-RNE on `x` (slightly below `m`) picks
  the closer lower neighbor `y_lo = 3·2^e`.
  Requires `m ∈ F₂` (since `m ∉ F₁_g`).
* `no_rndRTZ_RNE` — F₂-RTZ pulls `x` down to the F₁-midpoint
  `m_low = 5·2^(e−1)` (midpoint of the *lower-even* F-adjacent pair
  `(2·2^e, 3·2^e)` in `F₁_g`); F₁-RNE tie-breaks to the even lower
  neighbor `2·2^e`; direct F₁-RNE on `x` (slightly above `m_low`)
  picks the closer upper neighbor `3·2^e`.
  Requires `m_low ∈ F₂` (since `m_low ∉ F₁_g`).

## Common structure

Most counterexamples use `F₁ = 𝒜(p, e, ⊤)` with `p ≥ 2` (see `F₁_g`) and
take `F₂` as a parameter. The `hsub : F₁_g ⊆ F₂` hypothesis sets up the
standard double-rounding framing; some counterexamples (e.g. `RNE-RAZ`)
do not technically need it because the witness's failure is intrinsic
to the modes rather than to a precision gap between F₁ and F₂. Those
theorems drop `hsub` and explain the consequence in their docstring.
-/

namespace Mpfx

namespace AbstractFormat

/-! ## Counterexample: RN-RN double rounding can be incorrect

The seven rules in §5.2 are exhaustive — an obvious reviewer question is
"why not RNE-RNE, RNA-RNA, RTZ-RAZ, …?" For each omitted pair the answer
is the same: even when `F₁ ⊆ F₂`, there is a real `x` whose chained
two-step rounding disagrees with the direct rounding in `F₁`, and the
failure persists no matter how much we enlarge `F₂`. We formalize the
classical RNE-RNE counterexample.

### Setup

* `F₁ = 𝒜(p, e, ⊤)` with `p ≥ 2`, `e : ℤ`.
* `y_lo = 3·2^e` (odd in F₁ at numDigits 2), `y_hi = 4·2^e = 2^(e+2)`
  (even in F₁).
* `m = 7·2^(e-1)` — the midpoint of the F₁-adjacent pair `(y_lo, y_hi)`,
  living in `F₁.extend 1`.

`RNE_{F₁}(m) = y_hi` (ties broken to the even neighbor). For a witness
`x` strictly between F₂'s predecessor of `m` and `m`,
`RN_{F₂}(x) = m`, so the chain returns `y_hi` — but `x < m` is closer to
`y_lo` in F₁, so `RN_{F₁}(x)` directly returns `y_lo`. -/

private def F₁_g (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ) : AbstractFormat where
  p := (p : ℕ∞)
  exp := ((e : ℤ) : WithBot ℤ)
  b := ⊤
  p_pos := by
    have : (1 : ℕ) ≤ p := by omega
    exact_mod_cast this
  not_degenerate := Or.inr WithBot.coe_ne_bot
  b_nn := le_top

private noncomputable def y_lo_g (e : ℤ) : Dyadic := Dyadic.ofIntZpow 3 e
private noncomputable def y_hi_g (e : ℤ) : Dyadic := Dyadic.ofIntZpow 1 (e + 2)

/-- `2^e` as a Dyadic, used as the smallest positive F₁_g-element witness. -/
private noncomputable def two_e_g (e : ℤ) : Dyadic := Dyadic.ofIntZpow 1 e

private theorem coe_y_lo_g (e : ℤ) : ((y_lo_g e : Dyadic) : ℝ) = 3 * (2 : ℝ)^e := by
  change ((Dyadic.ofIntZpow 3 e : Dyadic) : ℝ) = _
  rw [Dyadic.coe_ofIntZpow]; push_cast; ring

private theorem coe_y_hi_g (e : ℤ) :
    ((y_hi_g e : Dyadic) : ℝ) = (2 : ℝ)^(e + 2) := by
  change ((Dyadic.ofIntZpow 1 (e + 2) : Dyadic) : ℝ) = _
  rw [Dyadic.coe_ofIntZpow]; push_cast; ring

private theorem coe_two_e_g (e : ℤ) : ((two_e_g e : Dyadic) : ℝ) = (2 : ℝ)^e := by
  change ((Dyadic.ofIntZpow 1 e : Dyadic) : ℝ) = _
  rw [Dyadic.coe_ofIntZpow]; push_cast; ring

private theorem y_lo_mem_F₁_g (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ) :
    y_lo_g e ∈ F₁_g p hp_ge_2 e := by
  refine ⟨?_, ?_, trivial⟩
  · -- precisionAtMost p: take (c=3, k=e). |3| < 2^p since p ≥ 2.
    change Dyadic.precisionAtMost ((p : ℕ) : ℕ∞) (y_lo_g e)
    refine ⟨3, e, ?_, ?_⟩
    · rw [coe_y_lo_g]; push_cast; ring
    · have h_pow : (4 : ℤ) ≤ (2 : ℤ)^p :=
        calc (4 : ℤ) = (2 : ℤ)^2 := by norm_num
          _ ≤ (2 : ℤ)^p := pow_le_pow_right₀ (by norm_num) hp_ge_2
      have h_abs : |(3 : ℤ)| = 3 := by decide
      omega
  · -- quantumAtLeast e: take c=3 (i.e., 3·2^e = 3·2^e).
    change Dyadic.quantumAtLeast (((e : ℤ)) : WithBot ℤ) (y_lo_g e)
    rw [Dyadic.quantumAtLeast_coe]
    refine ⟨3, ?_⟩
    rw [coe_y_lo_g]; push_cast; ring

private theorem two_e_mem_F₁_g (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ) :
    two_e_g e ∈ F₁_g p hp_ge_2 e := by
  refine ⟨?_, ?_, trivial⟩
  · change Dyadic.precisionAtMost ((p : ℕ) : ℕ∞) (two_e_g e)
    refine ⟨1, e, ?_, ?_⟩
    · rw [coe_two_e_g]; push_cast; ring
    · have h_pow : (2 : ℤ) ≤ (2 : ℤ)^p :=
        calc (2 : ℤ) = (2 : ℤ)^1 := by norm_num
          _ ≤ (2 : ℤ)^p := pow_le_pow_right₀ (by norm_num) (by omega)
      have : |(1 : ℤ)| = 1 := by decide
      omega
  · change Dyadic.quantumAtLeast (((e : ℤ)) : WithBot ℤ) (two_e_g e)
    rw [Dyadic.quantumAtLeast_coe]
    exact ⟨1, by rw [coe_two_e_g]; push_cast; ring⟩

private theorem F₁_g_quantum (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ)
    {z : Dyadic} (hz : z ∈ F₁_g p hp_ge_2 e) :
    ∃ c : ℤ, (z : ℝ) = (c : ℝ) * (2 : ℝ)^e := hz.2.1

/-- From `F₁_g ⊆ F₂` and `F₂.exp = (f₂ : WithBot ℤ)`, we have `f₂ ≤ e`:
`2^e ∈ F₁_g ⊆ F₂` forces `F₂.quantumAtLeast f₂ (2^e)`, i.e., `2^e = c · 2^f₂`
for some `c : ℤ`. Integer `c` requires `f₂ ≤ e`. -/
private theorem f₂_le_e_of_F₁_g_subset (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ)
    (F₂ : AbstractFormat) (hsub : F₁_g p hp_ge_2 e ⊆ F₂)
    {f₂ : ℤ} (hF₂_exp : F₂.exp = (f₂ : WithBot ℤ)) :
    f₂ ≤ e := by
  have h_two_e_in_F₂ : two_e_g e ∈ F₂ := hsub _ (two_e_mem_F₁_g p hp_ge_2 e)
  have hq : Dyadic.quantumAtLeast F₂.exp (two_e_g e) := h_two_e_in_F₂.2.1
  rw [hF₂_exp, Dyadic.quantumAtLeast_coe] at hq
  obtain ⟨c, hc⟩ := hq
  rw [coe_two_e_g] at hc
  by_contra h_gt; push Not at h_gt
  have h_2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
  have h_split : (2 : ℝ)^e = (2 : ℝ)^(e - f₂) * (2 : ℝ)^f₂ := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
  rw [h_split] at hc
  have hc_real : (c : ℝ) = (2 : ℝ)^(e - f₂) :=
    (mul_right_cancel₀ (ne_of_gt h_2f_pos) hc).symm
  have h_lt_1 : (c : ℝ) < 1 := by
    rw [hc_real]
    have h_diff_neg : e - f₂ < 0 := by omega
    have : (2 : ℝ)^(e - f₂) < (2 : ℝ)^(0 : ℤ) :=
      zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) h_diff_neg
    simpa using this
  have h_pos : 0 < (c : ℝ) := by rw [hc_real]; exact zpow_pos (by norm_num) _
  have hc_int_pos : 0 < c := by exact_mod_cast h_pos
  have hc_int_lt : c < 1 := by exact_mod_cast h_lt_1
  omega

/-- `(2:ℝ)^(e - f) = ((2:ℤ)^n : ℝ)` where `n = (e - f).toNat`, when `f ≤ e`. -/
private theorem two_zpow_diff_eq (e f : ℤ) (h : f ≤ e) :
    (2 : ℝ)^(e - f) = ((2 : ℤ)^(e - f).toNat : ℝ) := by
  have hn_eq : ((e - f).toNat : ℤ) = e - f := Int.toNat_of_nonneg (by omega)
  rw [show (2 : ℝ)^(e - f) = (2 : ℝ)^(((e - f).toNat : ℤ) : ℤ) by rw [hn_eq],
      zpow_natCast]
  push_cast; ring

/-- `(2:ℝ)^e = ((2:ℤ)^n : ℝ) * (2:ℝ)^f` where `n = (e - f).toNat`, when `f ≤ e`. -/
private theorem two_zpow_split (e f : ℤ) (h : f ≤ e) :
    (2 : ℝ)^e = ((2 : ℤ)^(e - f).toNat : ℝ) * (2 : ℝ)^f := by
  have h_split : (2 : ℝ)^e = (2 : ℝ)^(e - f) * (2 : ℝ)^f := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
  rw [h_split, two_zpow_diff_eq e f h]

private noncomputable def m_g (e : ℤ) : Dyadic := Dyadic.ofIntZpow 7 (e - 1)

private theorem coe_m_g (e : ℤ) : ((m_g e : Dyadic) : ℝ) = 7 * (2 : ℝ)^(e - 1) := by
  change ((Dyadic.ofIntZpow 7 (e - 1) : Dyadic) : ℝ) = _
  rw [Dyadic.coe_ofIntZpow]; push_cast; ring

private theorem y_hi_mem_F₁_g (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ) :
    y_hi_g e ∈ F₁_g p hp_ge_2 e := by
  refine ⟨?_, ?_, trivial⟩
  · change Dyadic.precisionAtMost ((p : ℕ) : ℕ∞) (y_hi_g e)
    refine ⟨1, e + 2, ?_, ?_⟩
    · rw [coe_y_hi_g]; push_cast; ring
    · have h_pow : (2 : ℤ) ≤ (2 : ℤ)^p :=
        calc (2 : ℤ) = (2 : ℤ)^1 := by norm_num
          _ ≤ (2 : ℤ)^p := pow_le_pow_right₀ (by norm_num) (by omega : 1 ≤ p)
      have h_abs : |(1 : ℤ)| = 1 := by decide
      omega
  · change Dyadic.quantumAtLeast (((e : ℤ)) : WithBot ℤ) (y_hi_g e)
    rw [Dyadic.quantumAtLeast_coe]
    refine ⟨4, ?_⟩
    rw [coe_y_hi_g]
    -- 2^(e+2) = 4 * 2^e.
    rw [show (e + 2 : ℤ) = e + 2 from rfl,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have : (2 : ℝ)^(2 : ℤ) = 4 := by norm_num
    rw [this]; push_cast; ring

/-- `IsEven F₁ (4·2^e)` for any `p ≥ 2`. At numDigits = min p 3, the canonical
significand of `4·2^e` is even: `2 = 1·2^(e+1)` when `numDigits = 2` (p = 2),
or `4 = 1·2^e` when `numDigits = 3` (p ≥ 3). -/
private theorem isEven_F₁_g_y_hi (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ) :
    IsEven (F₁_g p hp_ge_2 e) (y_hi_g e) := by
  have h_coe : ((y_hi_g e : Dyadic) : ℝ) = (2 : ℝ)^(e + 2) := coe_y_hi_g e
  have h_2_pos : (0 : ℝ) < (2 : ℝ)^(e + 2) := zpow_pos (by norm_num) _
  have h_y_ne_real : ((y_hi_g e : Dyadic) : ℝ) ≠ 0 := by
    rw [h_coe]; exact ne_of_gt h_2_pos
  have h_log : Int.log 2 |((y_hi_g e : Dyadic) : ℝ)| = e + 2 := by
    rw [h_coe, abs_of_pos h_2_pos]
    rw [show (2 : ℝ)^(e + 2) = ((2 : ℕ) : ℝ)^(e + 2) by push_cast; rfl]
    exact Int.log_zpow (R := ℝ) (by omega : 1 < 2) (e + 2)
  -- Compute numDigits = min p 3.
  have h_nd : numDigits (F₁_g p hp_ge_2 e).p (F₁_g p hp_ge_2 e).exp
        ((y_hi_g e : Dyadic) : ℝ) = min ((p : ℕ) : ℤ) 3 := by
    unfold numDigits
    rw [if_neg h_y_ne_real]
    change (min ((p : ℕ) : ℤ) (Int.log 2 |((y_hi_g e : Dyadic) : ℝ)| - (e : ℤ) + 1)) = _
    rw [h_log]
    congr 1; ring
  -- F₁_g.p ≠ 1 since p ≥ 2.
  have h_p_ne_1 : (F₁_g p hp_ge_2 e).p ≠ (1 : ℕ∞) := by
    intro h
    have : (((p : ℕ) : ℕ∞)) = (1 : ℕ∞) := h
    have : p = 1 := by exact_mod_cast this
    omega
  right
  -- Case split on whether numDigits is 2 (p = 2) or 3 (p ≥ 3).
  rcases (lt_or_ge p 3) with hp_lt | hp_ge
  · -- p = 2 (since 2 ≤ p < 3).
    have hp_eq : p = 2 := by omega
    -- numDigits = min 2 3 = 2.
    have h_nd_toNat : (numDigits (F₁_g p hp_ge_2 e).p (F₁_g p hp_ge_2 e).exp
          ((y_hi_g e : Dyadic) : ℝ)).toNat = 2 := by
      rw [h_nd, hp_eq]
      have : min ((2 : ℕ) : ℤ) 3 = 2 := by decide
      rw [this]; rfl
    refine ⟨2, e + 1, ⟨?_, ?_, ?_⟩, ?_⟩
    · -- 4·2^e = 2·2^(e+1)
      rw [h_coe]
      rw [show (e + 2 : ℤ) = (e + 1) + 1 from by ring,
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      have : (2 : ℝ)^(1 : ℤ) = 2 := by norm_num
      rw [this]; push_cast; ring
    · -- 2^(n-1) ≤ |2|. n = 2, so 2^1 = 2 ≤ 2.
      rw [h_nd_toNat]; decide
    · -- |2| < 2^n. 2^2 = 4 > 2.
      rw [h_nd_toNat]; decide
    · rw [if_neg h_p_ne_1]; decide
  · -- p ≥ 3.
    have h_nd_toNat : (numDigits (F₁_g p hp_ge_2 e).p (F₁_g p hp_ge_2 e).exp
          ((y_hi_g e : Dyadic) : ℝ)).toNat = 3 := by
      rw [h_nd]
      have h_min : min ((p : ℕ) : ℤ) 3 = 3 := by
        have : ((p : ℕ) : ℤ) ≥ 3 := by exact_mod_cast hp_ge
        omega
      rw [h_min]; rfl
    refine ⟨4, e, ⟨?_, ?_, ?_⟩, ?_⟩
    · -- 4·2^e = 4·2^e
      rw [h_coe]
      rw [show (e + 2 : ℤ) = e + 2 from rfl,
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      have : (2 : ℝ)^(2 : ℤ) = 4 := by norm_num
      rw [this]; push_cast; ring
    · rw [h_nd_toNat]; decide
    · rw [h_nd_toNat]; decide
    · rw [if_neg h_p_ne_1]; decide

/-- `y_hi = 4·2^e` has precision exactly 1 (canonical `1 · 2^(e+2)`), but
in `F₁_g` the rounding precision `numDigits = min p 3 ≥ 2`. The Lemma 5.3
corollary `precisionAtMost_not_IsOdd` then rules out odd parity. -/
private theorem notIsOdd_F₁_g_y_hi (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ) :
    ¬ IsOdd (F₁_g p hp_ge_2 e) (y_hi_g e) := by
  have h_coe : ((y_hi_g e : Dyadic) : ℝ) = (2 : ℝ)^(e + 2) := coe_y_hi_g e
  have h_2_pos : (0 : ℝ) < (2 : ℝ)^(e + 2) := zpow_pos (by norm_num) _
  have h_y_ne_real : ((y_hi_g e : Dyadic) : ℝ) ≠ 0 := by
    rw [h_coe]; exact ne_of_gt h_2_pos
  have h_log : Int.log 2 |((y_hi_g e : Dyadic) : ℝ)| = e + 2 := by
    rw [h_coe, abs_of_pos h_2_pos]
    rw [show (2 : ℝ)^(e + 2) = ((2 : ℕ) : ℝ)^(e + 2) by push_cast; rfl]
    exact Int.log_zpow (R := ℝ) (by omega : 1 < 2) (e + 2)
  have h_nd_eq : numDigits (F₁_g p hp_ge_2 e).p (F₁_g p hp_ge_2 e).exp
        ((y_hi_g e : Dyadic) : ℝ) = min ((p : ℕ) : ℤ) 3 := by
    unfold numDigits
    rw [if_neg h_y_ne_real]
    change (min ((p : ℕ) : ℤ) (Int.log 2 |((y_hi_g e : Dyadic) : ℝ)| - (e : ℤ) + 1)) = _
    rw [h_log]
    congr 1; ring
  have h_prec : Dyadic.precisionAtMost ((1 : ℕ) : ℕ∞) (y_hi_g e) := by
    rw [Dyadic.precisionAtMost_coe]
    refine ⟨1, e + 2, ?_, ?_⟩
    · rw [h_coe]; push_cast; ring
    · decide
  have h_gt : (1 : ℤ) < numDigits (F₁_g p hp_ge_2 e).p (F₁_g p hp_ge_2 e).exp
        ((y_hi_g e : Dyadic) : ℝ) := by
    rw [h_nd_eq]
    have : ((p : ℕ) : ℤ) ≥ 2 := by exact_mod_cast hp_ge_2
    omega
  exact precisionAtMost_not_IsOdd h_gt h_prec

/-! ### Lower-even F-adjacent pair (used in `no_rndRTZ_RNE`)

In `F₁_g`, the pair `(2·2^e, 3·2^e)` is F-adjacent with the *lower*
element `2·2^e` even (canonical c = 2 at numDigits = 2) and the
upper element `3·2^e` odd. Their midpoint `5·2^(e−1)` is *not* in
`F₁_g` (quantum below `e`), making it the F-midpoint used to force
F₁-RNE to tiebreak to the lower (even) neighbor — the mismatch
required for `no_rndRTZ_RNE`. -/

private noncomputable def y_lo_low_g (e : ℤ) : Dyadic := Dyadic.ofIntZpow 2 e

private theorem coe_y_lo_low_g (e : ℤ) :
    ((y_lo_low_g e : Dyadic) : ℝ) = 2 * (2 : ℝ)^e := by
  change ((Dyadic.ofIntZpow 2 e : Dyadic) : ℝ) = _
  rw [Dyadic.coe_ofIntZpow]; push_cast; ring

private noncomputable def m_low_g (e : ℤ) : Dyadic := Dyadic.ofIntZpow 5 (e - 1)

private theorem coe_m_low_g (e : ℤ) :
    ((m_low_g e : Dyadic) : ℝ) = 5 * (2 : ℝ)^(e - 1) := by
  change ((Dyadic.ofIntZpow 5 (e - 1) : Dyadic) : ℝ) = _
  rw [Dyadic.coe_ofIntZpow]; push_cast; ring

private theorem y_lo_low_mem_F₁_g (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ) :
    y_lo_low_g e ∈ F₁_g p hp_ge_2 e := by
  refine ⟨?_, ?_, trivial⟩
  · change Dyadic.precisionAtMost ((p : ℕ) : ℕ∞) (y_lo_low_g e)
    refine ⟨2, e, ?_, ?_⟩
    · rw [coe_y_lo_low_g]; push_cast; ring
    · have h_pow : (4 : ℤ) ≤ (2 : ℤ)^p :=
        calc (4 : ℤ) = (2 : ℤ)^2 := by norm_num
          _ ≤ (2 : ℤ)^p := pow_le_pow_right₀ (by norm_num) hp_ge_2
      have h_abs : |(2 : ℤ)| = 2 := by decide
      omega
  · change Dyadic.quantumAtLeast (((e : ℤ)) : WithBot ℤ) (y_lo_low_g e)
    rw [Dyadic.quantumAtLeast_coe]
    refine ⟨2, ?_⟩
    rw [coe_y_lo_low_g]; push_cast; ring

/-- `IsEven F₁_g y_lo_low_g`: at numDigits = 2, canonical significand
is `2` (even). The proof mirrors `isEven_F₁_g_y_hi`. -/
private theorem isEven_F₁_g_y_lo_low (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ) :
    IsEven (F₁_g p hp_ge_2 e) (y_lo_low_g e) := by
  have h_coe : ((y_lo_low_g e : Dyadic) : ℝ) = 2 * (2 : ℝ)^e := coe_y_lo_low_g e
  have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
  have h_y_pos : (0 : ℝ) < ((y_lo_low_g e : Dyadic) : ℝ) := by rw [h_coe]; nlinarith
  have h_y_ne_real : ((y_lo_low_g e : Dyadic) : ℝ) ≠ 0 := ne_of_gt h_y_pos
  have h_y_eq_2e1 : ((y_lo_low_g e : Dyadic) : ℝ) = (2 : ℝ)^(e + 1) := by
    rw [h_coe, show e + 1 = e + 1 from rfl,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [show (2 : ℝ)^(1 : ℤ) = 2 by norm_num]; ring
  have h_log : Int.log 2 |((y_lo_low_g e : Dyadic) : ℝ)| = e + 1 := by
    rw [h_y_eq_2e1, abs_of_pos (by rw [← h_y_eq_2e1]; exact h_y_pos)]
    rw [show (2 : ℝ)^(e + 1) = ((2 : ℕ) : ℝ)^(e + 1) by push_cast; rfl]
    exact Int.log_zpow (R := ℝ) (by omega : 1 < 2) (e + 1)
  have h_nd_eq : numDigits (F₁_g p hp_ge_2 e).p (F₁_g p hp_ge_2 e).exp
        ((y_lo_low_g e : Dyadic) : ℝ) = min ((p : ℕ) : ℤ) 2 := by
    unfold numDigits
    rw [if_neg h_y_ne_real]
    change (min ((p : ℕ) : ℤ) (Int.log 2 |((y_lo_low_g e : Dyadic) : ℝ)| - (e : ℤ) + 1)) = _
    rw [h_log]; congr 1; ring
  have h_nd_toNat : (numDigits (F₁_g p hp_ge_2 e).p (F₁_g p hp_ge_2 e).exp
        ((y_lo_low_g e : Dyadic) : ℝ)).toNat = 2 := by
    rw [h_nd_eq]
    have hp_int : ((p : ℕ) : ℤ) ≥ 2 := by exact_mod_cast hp_ge_2
    have h_min : min ((p : ℕ) : ℤ) 2 = 2 := by omega
    rw [h_min]; rfl
  have h_p_ne_1 : (F₁_g p hp_ge_2 e).p ≠ (1 : ℕ∞) := by
    intro h
    have h1 : (((p : ℕ) : ℕ∞)) = (1 : ℕ∞) := h
    have h2 : p = 1 := by exact_mod_cast h1
    omega
  right
  refine ⟨2, e, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [h_coe]; push_cast; ring
  · rw [h_nd_toNat]; decide
  · rw [h_nd_toNat]; decide
  · rw [if_neg h_p_ne_1]; decide

/-- F₁-faithful values of `m_low = 5·2^(e-1)` enumerate to
`{y_lo_low, y_lo_g}` (= `{2·2^e, 3·2^e}`). Note `y_lo_g e = 3·2^e`
plays the role of the *upper* neighbor here. -/
private theorem F₁_faithful_m_low_eq_g (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ)
    {z : Dyadic} (hf : IsFaithfulRound (F₁_g p hp_ge_2 e) ((m_low_g e : Dyadic) : ℝ) z) :
    (z : ℝ) = ((y_lo_low_g e : Dyadic) : ℝ) ∨ (z : ℝ) = ((y_lo_g e : Dyadic) : ℝ) := by
  have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
  have h_m_eq : ((m_low_g e : Dyadic) : ℝ) = (5 / 2) * (2 : ℝ)^e := by
    rw [coe_m_low_g, show (e - 1 : ℤ) = e + (-1 : ℤ) by ring,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [show (2 : ℝ)^(-1 : ℤ) = 1/2 by
      rw [show ((-1 : ℤ)) = -(1 : ℤ) by ring, zpow_neg]; norm_num]
    ring
  rcases hf with ⟨hzF, hle, hmax⟩ | ⟨hzF, hge, hmin⟩
  · left
    obtain ⟨c, hc⟩ := F₁_g_quantum p hp_ge_2 e hzF
    rw [hc, h_m_eq] at hle
    have hc_r_le : (c : ℝ) ≤ 5/2 := le_of_mul_le_mul_right hle h_2e_pos
    have hc_lt : (c : ℝ) < 3 := by linarith
    have hc_int_lt : c < 3 := by exact_mod_cast hc_lt
    have hc_int_le : c ≤ 2 := by omega
    have h_y_lo_low_le : ((y_lo_low_g e : Dyadic) : ℝ) ≤ ((m_low_g e : Dyadic) : ℝ) := by
      rw [coe_y_lo_low_g, h_m_eq]
      nlinarith
    have h_ge_y_lo_low := hmax (y_lo_low_g e) (y_lo_low_mem_F₁_g p hp_ge_2 e) h_y_lo_low_le
    rw [coe_y_lo_low_g, hc] at h_ge_y_lo_low
    have hc_r_ge : (2 : ℝ) ≤ (c : ℝ) := le_of_mul_le_mul_right h_ge_y_lo_low h_2e_pos
    have hc_int_ge : 2 ≤ c := by exact_mod_cast hc_r_ge
    have hc_eq : c = 2 := by omega
    rw [hc, coe_y_lo_low_g, hc_eq]; push_cast; ring
  · right
    obtain ⟨c, hc⟩ := F₁_g_quantum p hp_ge_2 e hzF
    rw [hc, h_m_eq] at hge
    have hc_r_ge : (5/2 : ℝ) ≤ (c : ℝ) := le_of_mul_le_mul_right hge h_2e_pos
    have hc_gt : (2 : ℝ) < (c : ℝ) := by linarith
    have hc_int_gt : 2 < c := by exact_mod_cast hc_gt
    have hc_int_ge : 3 ≤ c := by omega
    have h_y_lo_ge : ((m_low_g e : Dyadic) : ℝ) ≤ ((y_lo_g e : Dyadic) : ℝ) := by
      rw [coe_y_lo_g, h_m_eq]
      nlinarith
    have h_le_y_lo := hmin (y_lo_g e) (y_lo_mem_F₁_g p hp_ge_2 e) h_y_lo_ge
    rw [coe_y_lo_g, hc] at h_le_y_lo
    have hc_r_le : (c : ℝ) ≤ 3 := le_of_mul_le_mul_right h_le_y_lo h_2e_pos
    have hc_int_le : c ≤ 3 := by exact_mod_cast hc_r_le
    have hc_eq : c = 3 := by omega
    rw [hc, coe_y_lo_g, hc_eq]; push_cast; ring

/-- F₁_g-RNE at `m_low = 5·2^(e-1)` is `y_lo_low = 2·2^e` (the even
lower neighbor wins the tie). -/
private theorem rounds_F₁_g_RNE_m_low_y_lo_low (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ) :
    Rounds (F₁_g p hp_ge_2 e) (.Nearest .ToEven)
      ((m_low_g e : Dyadic) : ℝ) (y_lo_low_g e) := by
  have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
  have h_m_eq : ((m_low_g e : Dyadic) : ℝ) = (5 / 2) * (2 : ℝ)^e := by
    rw [coe_m_low_g, show (e - 1 : ℤ) = e + (-1 : ℤ) by ring,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [show (2 : ℝ)^(-1 : ℤ) = 1/2 by
      rw [show ((-1 : ℤ)) = -(1 : ℤ) by ring, zpow_neg]; norm_num]
    ring
  have h_y_lo_low_eq : ((y_lo_low_g e : Dyadic) : ℝ) = 2 * (2 : ℝ)^e := coe_y_lo_low_g e
  refine ⟨y_lo_low_mem_F₁_g p hp_ge_2 e, ?_, ?_, ?_⟩
  · -- IsFaithfulRound (RoundDown y_lo_low).
    left
    refine ⟨y_lo_low_mem_F₁_g p hp_ge_2 e, ?_, ?_⟩
    · rw [h_m_eq, h_y_lo_low_eq]; nlinarith
    · intro z hz hle
      obtain ⟨c, hc⟩ := F₁_g_quantum p hp_ge_2 e hz
      rw [hc, h_m_eq] at hle
      rw [h_y_lo_low_eq, hc]
      have hc_r_le : (c : ℝ) ≤ 5/2 := le_of_mul_le_mul_right hle h_2e_pos
      have hc_lt : (c : ℝ) < 3 := by linarith
      have hc_int_lt : c < 3 := by exact_mod_cast hc_lt
      have hc_int_le : c ≤ 2 := by omega
      have : (c : ℝ) ≤ 2 := by exact_mod_cast hc_int_le
      nlinarith
  · -- Closeness: faithful z ∈ {y_lo_low, y_lo_g}, both equidistant.
    intro z hz hf
    rcases F₁_faithful_m_low_eq_g p hp_ge_2 e hf with hz_lo | hz_hi
    · rw [hz_lo]
    · rw [hz_hi, coe_y_lo_g, h_m_eq, h_y_lo_low_eq]
      have hL : |(5/2 : ℝ) * (2 : ℝ)^e - 2 * (2 : ℝ)^e| = (1/2) * (2 : ℝ)^e := by
        rw [show (5/2 : ℝ) * (2 : ℝ)^e - 2 * (2 : ℝ)^e
            = (1/2) * (2 : ℝ)^e by ring, abs_of_pos]
        nlinarith
      have hR : |(5/2 : ℝ) * (2 : ℝ)^e - 3 * (2 : ℝ)^e| = (1/2) * (2 : ℝ)^e := by
        rw [show (5/2 : ℝ) * (2 : ℝ)^e - 3 * (2 : ℝ)^e
            = -((1/2) * (2 : ℝ)^e) by ring, abs_neg, abs_of_pos]
        nlinarith
      rw [hL, hR]
  · rintro ⟨_, _, _, _, _⟩
    exact isEven_F₁_g_y_lo_low p hp_ge_2 e

/-- F₁-faithful values of `m`: enumeration to `{y_lo, y_hi}`. -/
private theorem F₁_faithful_m_eq_g (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ)
    {z : Dyadic} (hf : IsFaithfulRound (F₁_g p hp_ge_2 e) ((m_g e : Dyadic) : ℝ) z) :
    (z : ℝ) = ((y_lo_g e : Dyadic) : ℝ) ∨ (z : ℝ) = ((y_hi_g e : Dyadic) : ℝ) := by
  have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
  have h_m_eq : ((m_g e : Dyadic) : ℝ) = (7 / 2) * (2 : ℝ)^e := by
    rw [coe_m_g]
    rw [show (e - 1 : ℤ) = e + (-1 : ℤ) by ring,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have : (2 : ℝ)^(-1 : ℤ) = 1/2 := by
      rw [show ((-1 : ℤ)) = -(1 : ℤ) by ring, zpow_neg]; norm_num
    rw [this]; ring
  rcases hf with ⟨hzF, hle, hmax⟩ | ⟨hzF, hge, hmin⟩
  · -- RoundDown: z ≤ m.
    left
    obtain ⟨c, hc⟩ := F₁_g_quantum p hp_ge_2 e hzF
    rw [hc, h_m_eq] at hle
    -- c·2^e ≤ (7/2)·2^e ⇒ c ≤ 3.
    have hc_r_le : (c : ℝ) ≤ 7/2 := le_of_mul_le_mul_right hle h_2e_pos
    have hc_lt : (c : ℝ) < 4 := by linarith
    have hc_int_lt : c < 4 := by exact_mod_cast hc_lt
    have hc_int_le : c ≤ 3 := by omega
    -- y_lo = 3·2^e ≤ m, so by max, z ≥ y_lo.
    have h_y_lo_le : ((y_lo_g e : Dyadic) : ℝ) ≤ ((m_g e : Dyadic) : ℝ) := by
      rw [coe_y_lo_g, h_m_eq]
      have : (3 : ℝ) ≤ 7/2 := by norm_num
      nlinarith
    have h_ge_y_lo := hmax (y_lo_g e) (y_lo_mem_F₁_g p hp_ge_2 e) h_y_lo_le
    rw [coe_y_lo_g, hc] at h_ge_y_lo
    have hc_r_ge : (3 : ℝ) ≤ (c : ℝ) := by
      exact le_of_mul_le_mul_right h_ge_y_lo h_2e_pos
    have hc_int_ge : 3 ≤ c := by exact_mod_cast hc_r_ge
    have hc_eq : c = 3 := by omega
    rw [hc, coe_y_lo_g, hc_eq]; push_cast; ring
  · -- RoundUp: z ≥ m.
    right
    obtain ⟨c, hc⟩ := F₁_g_quantum p hp_ge_2 e hzF
    rw [hc, h_m_eq] at hge
    have hc_r_ge : (7 / 2 : ℝ) ≤ (c : ℝ) := le_of_mul_le_mul_right hge h_2e_pos
    have hc_gt : (3 : ℝ) < (c : ℝ) := by linarith
    have hc_int_gt : 3 < c := by exact_mod_cast hc_gt
    have hc_int_ge : 4 ≤ c := by omega
    -- y_hi = 4·2^e ≥ m, so by min, z ≤ y_hi.
    have h_y_hi_ge : ((m_g e : Dyadic) : ℝ) ≤ ((y_hi_g e : Dyadic) : ℝ) := by
      rw [coe_y_hi_g, h_m_eq]
      have h_split : (2 : ℝ)^(e + 2) = 4 * (2 : ℝ)^e := by
        rw [show (e + 2 : ℤ) = e + 2 from rfl,
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        have : (2 : ℝ)^(2 : ℤ) = 4 := by norm_num
        rw [this]; ring
      rw [h_split]
      have : (7/2 : ℝ) ≤ 4 := by norm_num
      nlinarith
    have h_le_y_hi := hmin (y_hi_g e) (y_hi_mem_F₁_g p hp_ge_2 e) h_y_hi_ge
    rw [coe_y_hi_g, hc] at h_le_y_hi
    have h_split : (2 : ℝ)^(e + 2) = 4 * (2 : ℝ)^e := by
      rw [show (e + 2 : ℤ) = e + 2 from rfl,
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      have : (2 : ℝ)^(2 : ℤ) = 4 := by norm_num
      rw [this]; ring
    rw [h_split] at h_le_y_hi
    have hc_r_le : (c : ℝ) ≤ 4 := le_of_mul_le_mul_right h_le_y_hi h_2e_pos
    have hc_int_le : c ≤ 4 := by exact_mod_cast hc_r_le
    have hc_eq : c = 4 := by omega
    rw [hc, coe_y_hi_g, hc_eq, h_split]; push_cast; ring

/-- Inner step: `Rounds F₁ RNE m y_hi` — at the F₁-midpoint `m`, RNE breaks
the tie between `y_lo = 3·2^e` and `y_hi = 4·2^e` toward the even neighbor. -/
private theorem rounds_F₁_g_RNE_m_y_hi (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ) :
    Rounds (F₁_g p hp_ge_2 e) (.Nearest .ToEven)
      ((m_g e : Dyadic) : ℝ) (y_hi_g e) := by
  have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
  have h_m_eq : ((m_g e : Dyadic) : ℝ) = (7 / 2) * (2 : ℝ)^e := by
    rw [coe_m_g, show (e - 1 : ℤ) = e + (-1 : ℤ) by ring,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have : (2 : ℝ)^(-1 : ℤ) = 1/2 := by
      rw [show ((-1 : ℤ)) = -(1 : ℤ) by ring, zpow_neg]; norm_num
    rw [this]; ring
  have h_y_hi_eq : ((y_hi_g e : Dyadic) : ℝ) = 4 * (2 : ℝ)^e := by
    rw [coe_y_hi_g, show (e + 2 : ℤ) = e + 2 from rfl,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have : (2 : ℝ)^(2 : ℤ) = 4 := by norm_num
    rw [this]; ring
  refine ⟨y_hi_mem_F₁_g p hp_ge_2 e, ?_, ?_, ?_⟩
  · right
    refine ⟨y_hi_mem_F₁_g p hp_ge_2 e, ?_, ?_⟩
    · rw [h_m_eq, h_y_hi_eq]; nlinarith
    · intro z hz hge
      obtain ⟨c, hc⟩ := F₁_g_quantum p hp_ge_2 e hz
      rw [hc, h_m_eq] at hge
      rw [h_y_hi_eq, hc]
      have hc_r_ge : (7/2 : ℝ) ≤ (c : ℝ) := le_of_mul_le_mul_right hge h_2e_pos
      have hc_r_3lt : (3 : ℝ) < (c : ℝ) := by linarith
      have hc_int_3lt : 3 < c := by exact_mod_cast hc_r_3lt
      have hc_int_ge : 4 ≤ c := by omega
      have hc_r_ge_4 : (4 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc_int_ge
      nlinarith
  · intro z hz hf
    rcases F₁_faithful_m_eq_g p hp_ge_2 e hf with hz_lo | hz_hi
    · rw [hz_lo, coe_y_lo_g, h_m_eq, h_y_hi_eq]
      have hL : |(7/2 : ℝ) * (2 : ℝ)^e - 4 * (2 : ℝ)^e| = (1/2) * (2 : ℝ)^e := by
        rw [show (7/2 : ℝ) * (2 : ℝ)^e - 4 * (2 : ℝ)^e
            = -((1/2) * (2 : ℝ)^e) by ring, abs_neg, abs_of_pos]
        nlinarith
      have hR : |(7/2 : ℝ) * (2 : ℝ)^e - 3 * (2 : ℝ)^e| = (1/2) * (2 : ℝ)^e := by
        rw [show (7/2 : ℝ) * (2 : ℝ)^e - 3 * (2 : ℝ)^e
            = (1/2) * (2 : ℝ)^e by ring, abs_of_pos]
        nlinarith
      rw [hL, hR]
    · rw [hz_hi]
  · rintro ⟨_, _, _, _, _⟩
    exact isEven_F₁_g_y_hi p hp_ge_2 e

/-! ### Predecessor-extraction lemma for the witness construction -/

/-- For our specific midpoint `m = 7·2^(e-1)`, F₂'s grid representation
`(c, k)` always has `c ≥ 2` and `Int.log 2 c = Int.log 2 (c-1)` (since
`c = 7·2^j` for some `j ≥ 0` and `7·2^j - 1 ≥ 4·2^j` keeps it in the same
magnitude class). This is the pre-requisite for invoking
`prev_F_adjacent_of_log_eq`. -/
private theorem m_g_grid_log_invariant {q₂ : ℕ} {f₂ : ℤ} {k c : ℤ} {e : ℤ}
    (hq₂ : 4 ≤ q₂) (hf₂_le : f₂ ≤ e - 2)
    (hk_max : k = max f₂ (Int.log 2 ((c : ℝ) * (2 : ℝ) ^ k) - (q₂ : ℤ) + 1))
    (hm_eq : (7 : ℝ) * (2 : ℝ) ^ (e - 1) = (c : ℝ) * (2 : ℝ) ^ k) :
    2 ≤ c ∧ Int.log 2 (((c - 1 : ℤ) : ℝ) * (2 : ℝ)^k) =
            Int.log 2 ((c : ℝ) * (2 : ℝ)^k) := by
  have h_2_pos : (0 : ℝ) < (2 : ℝ)^(e-1) := zpow_pos (by norm_num) _
  have hm_pos : (0 : ℝ) < (7 : ℝ) * (2 : ℝ)^(e - 1) := by nlinarith
  have h_log_m : Int.log 2 ((7 : ℝ) * (2 : ℝ)^(e - 1)) = e + 1 := by
    apply le_antisymm
    · have hle : (7 : ℝ) * (2 : ℝ)^(e-1) < ((2 : ℕ) : ℝ)^(e + 2) := by
        rw [show ((2 : ℕ) : ℝ) = 2 from by push_cast; rfl,
            show e + 2 = (e - 1) + 3 by ring,
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        have : (2 : ℝ)^(3 : ℤ) = 8 := by norm_num
        rw [this]; nlinarith
      have h_lt := (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) hm_pos).mp hle
      omega
    · have hge : ((2 : ℕ) : ℝ)^(e + 1) ≤ (7 : ℝ) * (2 : ℝ)^(e-1) := by
        rw [show ((2 : ℕ) : ℝ) = 2 from by push_cast; rfl,
            show e + 1 = (e - 1) + 2 by ring,
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        have : (2 : ℝ)^(2 : ℤ) = 4 := by norm_num
        rw [this]; nlinarith
      exact (Int.zpow_le_iff_le_log (by norm_num : 1 < (2 : ℕ)) hm_pos).mp hge
  have h_log_cxk : Int.log 2 ((c : ℝ) * (2 : ℝ)^k) = e + 1 := by
    rw [← hm_eq]; exact h_log_m
  rw [h_log_cxk] at hk_max
  have hk_eq : k = max f₂ (e + 2 - q₂) := by
    convert hk_max using 2; ring
  have hk_le : k ≤ e - 2 := by
    rw [hk_eq]
    have h1 : f₂ ≤ e - 2 := hf₂_le
    have h2 : e + 2 - (q₂ : ℤ) ≤ e - 2 := by
      have : (4 : ℤ) ≤ (q₂ : ℤ) := by exact_mod_cast hq₂
      omega
    exact max_le h1 h2
  have h_2k_pos : (0 : ℝ) < (2 : ℝ)^k := zpow_pos (by norm_num) _
  have hc_real : (c : ℝ) = 7 * (2 : ℝ)^(e - 1 - k) := by
    have h_split : (2 : ℝ)^(e - 1) = (2 : ℝ)^(e - 1 - k) * (2 : ℝ)^k := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
    have h1 : (7 : ℝ) * ((2 : ℝ)^(e - 1 - k) * (2 : ℝ)^k) = (c : ℝ) * (2 : ℝ)^k := by
      rw [← h_split]; exact hm_eq
    have h2 : (7 : ℝ) * (2 : ℝ)^(e - 1 - k) * (2 : ℝ)^k = (c : ℝ) * (2 : ℝ)^k := by
      rw [mul_assoc]; exact h1
    exact (mul_right_cancel₀ (ne_of_gt h_2k_pos) h2).symm
  have h_exp_ge : 1 ≤ e - 1 - k := by omega
  have hc_ge_14 : (14 : ℝ) ≤ (c : ℝ) := by
    rw [hc_real]
    have : (2 : ℝ)^(e - 1 - k) ≥ (2 : ℝ)^(1 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h_exp_ge
    nlinarith
  have hc_int_ge : 14 ≤ c := by exact_mod_cast hc_ge_14
  refine ⟨by omega, ?_⟩
  rw [h_log_cxk]
  apply le_antisymm
  · have h_c1_pos : 0 < c - 1 := by omega
    have h_c1_real_pos : (0 : ℝ) < ((c - 1 : ℤ) : ℝ) := by exact_mod_cast h_c1_pos
    have h_prod_pos : (0 : ℝ) < ((c - 1 : ℤ) : ℝ) * (2 : ℝ)^k :=
      mul_pos h_c1_real_pos h_2k_pos
    have h_c1_lt_c : ((c - 1 : ℤ) : ℝ) < (c : ℝ) := by push_cast; linarith
    have h_prod_lt_m : ((c - 1 : ℤ) : ℝ) * (2 : ℝ)^k < (c : ℝ) * (2 : ℝ)^k := by
      nlinarith
    have h_prod_lt_2 : ((c - 1 : ℤ) : ℝ) * (2 : ℝ)^k < ((2 : ℕ) : ℝ)^(e + 2) := by
      rw [show ((2 : ℕ) : ℝ) = 2 from by push_cast; rfl]
      have h_c1_lt : ((c - 1 : ℤ) : ℝ) * (2 : ℝ)^k < (c : ℝ) * (2 : ℝ)^k := h_prod_lt_m
      have h_log_m_ub : (7 : ℝ) * (2 : ℝ)^(e - 1) < (2 : ℝ)^(e + 2) := by
        rw [show e + 2 = (e - 1) + 3 by ring,
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        have : (2 : ℝ)^(3 : ℤ) = 8 := by norm_num
        rw [this]; nlinarith
      have : (c : ℝ) * (2 : ℝ)^k < (2 : ℝ)^(e + 2) := by rw [← hm_eq]; exact h_log_m_ub
      linarith
    have h := (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) h_prod_pos).mp h_prod_lt_2
    omega
  · have h_c1_pos : 0 < c - 1 := by omega
    have h_prod_pos : (0 : ℝ) < ((c - 1 : ℤ) : ℝ) * (2 : ℝ)^k :=
      mul_pos (by exact_mod_cast h_c1_pos) h_2k_pos
    have h_c1_ge_13 : (13 : ℝ) ≤ ((c - 1 : ℤ) : ℝ) := by
      have : (13 : ℤ) ≤ c - 1 := by omega
      exact_mod_cast this
    have h_prod_ge : ((2 : ℕ) : ℝ)^(e + 1) ≤ ((c - 1 : ℤ) : ℝ) * (2 : ℝ)^k := by
      rw [show ((2 : ℕ) : ℝ) = 2 from by push_cast; rfl,
          show e + 1 = (e - 1 - k) + k + 2 by ring,
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      have h22 : (2 : ℝ)^(2 : ℤ) = 4 := by norm_num
      rw [h22]
      have h_2e1k_pos : (0 : ℝ) < (2 : ℝ)^(e - 1 - k) := zpow_pos (by norm_num) _
      have hc_real_alt : (c : ℝ) = 7 * (2 : ℝ)^(e - 1 - k) := hc_real
      have h_c1_real : ((c - 1 : ℤ) : ℝ) = (c : ℝ) - 1 := by push_cast; ring
      rw [h_c1_real, hc_real_alt]
      have h_2e1k_ge_2 : (2 : ℝ) ≤ (2 : ℝ)^(e - 1 - k) := by
        calc (2 : ℝ) = (2 : ℝ)^(1 : ℤ) := by norm_num
          _ ≤ (2 : ℝ)^(e - 1 - k) :=
              zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h_exp_ge
      nlinarith
    exact (Int.zpow_le_iff_le_log (by norm_num : 1 < (2 : ℕ)) h_prod_pos).mp h_prod_ge

/-- **Core RNE-RNE counterexample.** Takes F₂'s structural parameters
explicitly: precision `q₂ ≥ p + 2`, finite quantum `f₂ ≤ e − 2`, and
unbounded magnitude. Witness `x = (3m + pred_{F₂}(m)) / 4` where the F₂-
predecessor of `m` is extracted via `prev_F_adjacent_of_log_eq`. The
public-facing version is `no_rndRNE_RNE`, which takes only
`(F₁.extend 2) ⊆ F₂` plus the finiteness hypotheses and derives the
remaining bounds. -/
theorem no_rndRNE_RNE_arbitrary_F₂
    (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ)
    (F₂ : AbstractFormat)
    {q₂ : ℕ} (hF₂_p : F₂.p = (q₂ : ℕ∞)) (hq₂ : p + 2 ≤ q₂)
    {f₂ : ℤ} (hF₂_exp : F₂.exp = (f₂ : WithBot ℤ)) (hf₂ : f₂ ≤ e - 2)
    (hF₂_b : F₂.b = ⊤) :
    F₁_g p hp_ge_2 e ⊆ F₂ ∧
    ∃ (x : ℝ) (z w : Dyadic),
      Rounds F₂ (.Nearest .ToEven) x z ∧
      Rounds (F₁_g p hp_ge_2 e) (.Nearest .ToEven) (z : ℝ) w ∧
      ¬ Rounds (F₁_g p hp_ge_2 e) (.Nearest .ToEven) x w := by
  -- Hypotheses derived from F₂'s parameters.
  have hq₁_le_q₂ : (((p : ℕ) : ℕ∞)) ≤ F₂.p := by
    rw [hF₂_p]; exact_mod_cast (by omega : p ≤ q₂)
  have hf₂_le_e : F₂.exp ≤ (((e : ℤ)) : WithBot ℤ) := by
    rw [hF₂_exp]
    exact_mod_cast (by omega : f₂ ≤ e)
  have hb_le : (F₁_g p hp_ge_2 e).b ≤ F₂.b := by
    have h1 : (F₁_g p hp_ge_2 e).b = ⊤ := rfl
    rw [h1, hF₂_b]
  have h_F₁_sub : F₁_g p hp_ge_2 e ⊆ F₂ := containsPrec hq₁_le_q₂ hf₂_le_e hb_le
  refine ⟨h_F₁_sub, ?_⟩
  -- m, y_lo, y_hi, etc.
  set m : Dyadic := Dyadic.ofIntZpow 7 (e - 1) with hm_def
  set y_lo : Dyadic := y_lo_g e with hy_lo_def
  set y_hi : Dyadic := y_hi_g e with hy_hi_def
  have h_m_coe : (m : ℝ) = 7 * (2 : ℝ)^(e - 1) := by
    rw [hm_def, Dyadic.coe_ofIntZpow]; push_cast; ring
  have h_m_pos : 0 < (m : ℝ) := by
    rw [h_m_coe]
    have : (0 : ℝ) < (2 : ℝ)^(e - 1) := zpow_pos (by norm_num) _
    nlinarith
  -- m ∈ F₂.
  have h_m_mem_F₂ : m ∈ F₂ := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hF₂_p]
      refine ⟨7, e - 1, ?_, ?_⟩
      · rw [hm_def, Dyadic.coe_ofIntZpow]
      · have h_pow : (8 : ℤ) ≤ (2 : ℤ)^q₂ :=
          calc (8 : ℤ) = (2 : ℤ)^3 := by norm_num
            _ ≤ (2 : ℤ)^q₂ := pow_le_pow_right₀ (by norm_num) (by omega : 3 ≤ q₂)
        have h_abs : |(7 : ℤ)| = 7 := by decide
        omega
    · rw [hF₂_exp]
      rw [Dyadic.quantumAtLeast_coe]
      refine ⟨7 * (2 : ℤ)^(e - 1 - f₂).toNat, ?_⟩
      rw [hm_def, Dyadic.coe_ofIntZpow]
      have h_diff_nn : 0 ≤ e - 1 - f₂ := by omega
      have h_split : (2 : ℝ)^(e - 1) = (2 : ℝ)^((e - 1 - f₂).toNat : ℤ) * (2 : ℝ)^f₂ := by
        rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        congr 1; rw [Int.toNat_of_nonneg h_diff_nn]; ring
      rw [h_split, zpow_natCast]; push_cast; ring
    · rw [hF₂_b]; trivial
  -- Extract grid representation of m in F₂.
  obtain ⟨k, c, hk_ge_f₂, hc_lt_abs, hm_eq_F₂, hk_max⟩ :=
    exists_grid_rep F₂ hF₂_p hF₂_exp h_m_mem_F₂.1 h_m_mem_F₂.2.1 h_m_pos
  -- c > 0.
  have hc_pos : 0 < c := grid_rep_c_pos h_m_pos hm_eq_F₂
  have hc_lt_pos : c < (2 : ℤ)^q₂ := by
    have h_abs : |c| = c := abs_of_pos hc_pos
    rw [← h_abs]; exact hc_lt_abs
  -- m_g_grid_log_invariant: c ≥ 2 and log invariance.
  have hm_eq_simple : (7 : ℝ) * (2 : ℝ)^(e - 1) = (c : ℝ) * (2 : ℝ)^k := by
    rw [← h_m_coe]; exact hm_eq_F₂
  -- Convert hk_max from the `Int.log 2 m` form to the `Int.log 2 (c·2^k)` form.
  have hk_max' : k = max f₂ (Int.log 2 ((c : ℝ) * (2 : ℝ)^k) - (q₂ : ℤ) + 1) := by
    rw [← hm_eq_F₂]; exact hk_max
  obtain ⟨hc_ge_2, h_log_eq⟩ := m_g_grid_log_invariant
    (by omega : 4 ≤ q₂) hf₂ hk_max' hm_eq_simple
  -- Apply prev_F_adjacent_of_log_eq to extract pred.
  obtain ⟨h_pred_mem, h_pred_lt_m, h_pred_max⟩ :=
    prev_F_adjacent_of_log_eq F₂ hF₂_p hF₂_exp h_m_mem_F₂ h_m_pos
      hk_ge_f₂ hc_ge_2 hc_lt_pos hm_eq_F₂ hk_max' h_log_eq
  set pred : Dyadic := Dyadic.ofIntZpow (c - 1) k with h_pred_def
  -- Define x = (3m + pred)/4.
  set x_val : ℝ := (3 * (m : ℝ) + (pred : ℝ)) / 4 with hx_def
  -- Key inequalities about x.
  have h_pred_real : (pred : ℝ) = ((c - 1 : ℤ) : ℝ) * (2 : ℝ)^k := by
    rw [h_pred_def, Dyadic.coe_ofIntZpow]
  have h_m_real : (m : ℝ) = (c : ℝ) * (2 : ℝ)^k := hm_eq_F₂
  have h_m_minus_pred : (m : ℝ) - (pred : ℝ) = (2 : ℝ)^k := by
    rw [h_m_real, h_pred_real]; push_cast; ring
  have h_2k_pos : (0 : ℝ) < (2 : ℝ)^k := zpow_pos (by norm_num) _
  have h_pred_pos : (0 : ℝ) < (pred : ℝ) := by
    rw [h_pred_real]
    have h_c1_pos : (0 : ℝ) < ((c - 1 : ℤ) : ℝ) := by
      have : 0 < c - 1 := by omega
      exact_mod_cast this
    exact mul_pos h_c1_pos h_2k_pos
  have h_x_lt_m : x_val < (m : ℝ) := by
    rw [hx_def]; linarith
  have h_pred_lt_x : (pred : ℝ) < x_val := by
    rw [hx_def]; linarith
  have h_x_pos : 0 < x_val := by linarith
  -- x_val < y_hi/2 (where y_hi = 4·2^e = 2^(e+2)). Specifically x < m, m < y_hi.
  -- Coercions for y_lo and y_hi.
  have h_y_lo_coe : (y_lo : ℝ) = 3 * (2 : ℝ)^e := coe_y_lo_g e
  have h_y_hi_coe : (y_hi : ℝ) = (2 : ℝ)^(e + 2) := coe_y_hi_g e
  -- y_hi = m + Δ where Δ = 2^(e-1). y_lo = m - Δ.
  have h_2e1_pos : (0 : ℝ) < (2 : ℝ)^(e - 1) := zpow_pos (by norm_num) _
  have h_y_hi_eq : (y_hi : ℝ) = (m : ℝ) + (2 : ℝ)^(e - 1) := by
    rw [h_y_hi_coe, h_m_coe]
    rw [show e + 2 = (e - 1) + 3 by ring,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have : (2 : ℝ)^(3 : ℤ) = 8 := by norm_num
    rw [this]; ring
  have h_y_lo_eq : (y_lo : ℝ) = (m : ℝ) - (2 : ℝ)^(e - 1) := by
    rw [h_y_lo_coe, h_m_coe]
    have h_split : (2 : ℝ)^e = (2 : ℝ)^(e - 1) * (2 : ℝ)^(1 : ℤ) := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
    rw [h_split]
    have h_two : (2 : ℝ)^(1 : ℤ) = 2 := by norm_num
    rw [h_two]; ring
  -- k ≤ e - 2 (proven inside m_g_grid_log_invariant, but we need it again).
  have hk_le_e2 : k ≤ e - 2 := by
    have h_log_cxk : Int.log 2 ((c : ℝ) * (2 : ℝ)^k) = e + 1 := by
      have h_log_m : Int.log 2 ((m : ℝ)) = e + 1 := by
        rw [h_m_coe]
        rw [show (7 : ℝ) * (2 : ℝ)^(e - 1) = (7 : ℝ) * (2 : ℝ)^(e - 1) from rfl]
        apply le_antisymm
        · have hle : (7 : ℝ) * (2 : ℝ)^(e-1) < ((2 : ℕ) : ℝ)^(e + 2) := by
            rw [show ((2 : ℕ) : ℝ) = 2 from by push_cast; rfl,
                show e + 2 = (e - 1) + 3 by ring,
                zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
            have : (2 : ℝ)^(3 : ℤ) = 8 := by norm_num
            rw [this]; nlinarith
          have hm_pos' : (0 : ℝ) < (7 : ℝ) * (2 : ℝ)^(e - 1) := by nlinarith
          have h_log_lt : Int.log 2 ((7 : ℝ) * (2 : ℝ)^(e-1)) < e + 2 :=
            (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) hm_pos').mp hle
          omega
        · have hge : ((2 : ℕ) : ℝ)^(e + 1) ≤ (7 : ℝ) * (2 : ℝ)^(e-1) := by
            rw [show ((2 : ℕ) : ℝ) = 2 from by push_cast; rfl,
                show e + 1 = (e - 1) + 2 by ring,
                zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
            have : (2 : ℝ)^(2 : ℤ) = 4 := by norm_num
            rw [this]; nlinarith
          have hm_pos' : (0 : ℝ) < (7 : ℝ) * (2 : ℝ)^(e - 1) := by nlinarith
          exact (Int.zpow_le_iff_le_log (by norm_num : 1 < (2 : ℕ)) hm_pos').mp hge
      rw [h_m_real] at h_log_m
      exact h_log_m
    rw [h_log_cxk] at hk_max'
    have : k = max f₂ (e + 2 - q₂) := by
      convert hk_max' using 2; ring
    rw [this]
    have h2 : e + 2 - (q₂ : ℤ) ≤ e - 2 := by
      have : (4 : ℤ) ≤ (q₂ : ℤ) := by exact_mod_cast (show 4 ≤ q₂ by omega)
      omega
    exact max_le hf₂ h2
  -- m - pred = 2^k, and 2^k ≤ 2^(e-2).
  have h_2k_le : (2 : ℝ)^k ≤ (2 : ℝ)^(e - 2) :=
    zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk_le_e2
  have h_2e2_pos : (0 : ℝ) < (2 : ℝ)^(e - 2) := zpow_pos (by norm_num) _
  -- 2^k ≤ 2^(e-2) < 2^(e-1) < 2^(e+1).
  have h_2k_lt_2e1 : (2 : ℝ)^k < (2 : ℝ)^(e - 1) := by
    calc (2 : ℝ)^k ≤ (2 : ℝ)^(e - 2) := h_2k_le
      _ < (2 : ℝ)^(e - 1) := by
          have h : (e - 2 : ℤ) < e - 1 := by omega
          have : (2 : ℝ)^(e - 2) < (2 : ℝ)^(e - 1) :=
            zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) h
          exact this
  -- 4·x = 3m + pred = 3m + (m - 2^k) = 4m - 2^k.
  -- So x = m - 2^k/4 = m - 2^(k-2).
  -- y_lo ≤ x: m - Δ ≤ m - 2^k/4 iff 2^k/4 ≤ Δ = 2^(e-1) iff 2^k ≤ 2^(e+1). True.
  refine ⟨x_val, m, y_hi, ?_, ?_, ?_⟩
  · -- Rounds F₂ RNE x m.
    refine ⟨h_m_mem_F₂, ?_, ?_, ?_⟩
    · -- IsFaithfulRound (RoundUp).
      right
      refine ⟨h_m_mem_F₂, le_of_lt h_x_lt_m, ?_⟩
      intro z hzF₂ hx_le_z
      by_contra h_z_lt_m
      push Not at h_z_lt_m
      have h_z_le_pred := h_pred_max z hzF₂ h_z_lt_m
      linarith
    · -- Closeness.
      intro z hzF₂ hf
      rcases hf with ⟨_, hz_le, hz_max⟩ | ⟨_, hx_le_z, hz_min⟩
      · -- RoundDown z ≤ pred ⇒ |x - z| ≥ 3·2^k/4 ≥ 2^k/4 = |x - m|.
        have h_z_lt_m : (z : ℝ) < (m : ℝ) := lt_of_le_of_lt hz_le h_x_lt_m
        have h_z_le_pred := h_pred_max z hzF₂ h_z_lt_m
        have h_xm : x_val - (m : ℝ) = -((2 : ℝ)^k / 4) := by
          rw [hx_def]; linarith
        have h_zx : (z : ℝ) ≤ (pred : ℝ) := by
          have hpred_ge_z : (pred : ℝ) ≥ (z : ℝ) := h_z_le_pred
          linarith
        have h_x_pred : x_val - (pred : ℝ) = 3 * (2 : ℝ)^k / 4 := by
          rw [hx_def]; linarith
        have hL : |x_val - (m : ℝ)| = (2 : ℝ)^k / 4 := by
          rw [h_xm, abs_neg, abs_of_pos]; linarith
        rw [hL]
        have h_x_minus_z_ge : (2 : ℝ)^k / 4 ≤ x_val - (z : ℝ) := by
          have : x_val - (pred : ℝ) ≤ x_val - (z : ℝ) := by linarith
          rw [h_x_pred] at this; linarith
        have h_abs : |x_val - (z : ℝ)| = x_val - (z : ℝ) := by
          rw [abs_of_nonneg]; linarith
        rw [h_abs]; exact h_x_minus_z_ge
      · -- RoundUp x ≤ z. F-adjacency (z < m would force z ≤ pred < x ≤ z) gives z = m.
        have h_z_le_m : (z : ℝ) ≤ (m : ℝ) :=
          hz_min m h_m_mem_F₂ (le_of_lt h_x_lt_m)
        have h_z_eq_m : (z : ℝ) = (m : ℝ) := by
          by_contra h_z_ne_m
          have h_z_lt_m : (z : ℝ) < (m : ℝ) := lt_of_le_of_ne h_z_le_m h_z_ne_m
          have h_z_le_pred := h_pred_max z hzF₂ h_z_lt_m
          linarith
        rw [h_z_eq_m]
    · -- No-tie: any tied z faithful and ≠ m would be pred (RoundDown) — but distances differ.
      rintro ⟨z, hzF₂, hf, hne, heq⟩
      rcases hf with ⟨_, hz_le, hz_max⟩ | ⟨_, hx_le_z, hz_min⟩
      · -- RoundDown z ≤ pred ⇒ |x - z| ≥ 3·2^k/4 > 2^k/4 = |x - m|.
        exfalso
        have h_z_lt_m : (z : ℝ) < (m : ℝ) := lt_of_le_of_lt hz_le h_x_lt_m
        have h_z_le_pred := h_pred_max z hzF₂ h_z_lt_m
        have h_xm : x_val - (m : ℝ) = -((2 : ℝ)^k / 4) := by rw [hx_def]; linarith
        have hL : |x_val - (m : ℝ)| = (2 : ℝ)^k / 4 := by
          rw [h_xm, abs_neg, abs_of_pos]; linarith
        have h_xz_ge : x_val - (z : ℝ) ≥ x_val - (pred : ℝ) := by linarith
        have h_x_pred : x_val - (pred : ℝ) = 3 * (2 : ℝ)^k / 4 := by
          rw [hx_def]; linarith
        have h_abs_xz : |x_val - (z : ℝ)| = x_val - (z : ℝ) := by
          rw [abs_of_nonneg]; linarith
        rw [hL, h_abs_xz] at heq
        linarith
      · -- RoundUp z = m (same argument as closeness) contradicts hne.
        exfalso
        apply hne
        apply Subtype.ext
        have h_z_le_m : (z : ℝ) ≤ (m : ℝ) := hz_min m h_m_mem_F₂ (le_of_lt h_x_lt_m)
        by_contra h_z_ne_m
        have h_z_lt_m : (z : ℝ) < (m : ℝ) := lt_of_le_of_ne h_z_le_m h_z_ne_m
        have h_z_le_pred := h_pred_max z hzF₂ h_z_lt_m
        linarith
  · exact rounds_F₁_g_RNE_m_y_hi p hp_ge_2 e
  · -- y_lo is F₁-RoundDown of x, with |x - y_lo| < |x - y_hi|.
    intro hr
    obtain ⟨_, _, h_close, _⟩ := hr
    have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
    have h_y_lo_faith : IsFaithfulRound (F₁_g p hp_ge_2 e) x_val y_lo := by
      left
      refine ⟨y_lo_mem_F₁_g p hp_ge_2 e, ?_, ?_⟩
      · -- y_lo = m - 2^(e-1), x = m - 2^k/4, and 2^k/4 ≤ 2^(e-1) since 2^k ≤ 2^(e-1).
        rw [h_y_lo_eq]
        have h_2k4_le : (2 : ℝ)^k / 4 ≤ (2 : ℝ)^(e - 1) :=
          le_of_lt (by linarith [h_2k_lt_2e1])
        have hx_eq : x_val = (m : ℝ) - (2 : ℝ)^k / 4 := by
          rw [hx_def]; linarith
        rw [hx_eq]; linarith
      · intro z hz hz_le
        obtain ⟨c', hc'⟩ := F₁_g_quantum p hp_ge_2 e hz
        have h_z_lt_m : (z : ℝ) < (m : ℝ) := lt_of_le_of_lt hz_le h_x_lt_m
        rw [hc', h_m_coe] at h_z_lt_m
        have h_7_2 : (7 : ℝ) * (2 : ℝ)^(e-1) = (7/2) * (2 : ℝ)^e := by
          rw [show (e-1 : ℤ) = e + (-1 : ℤ) from by ring,
              zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          have : (2 : ℝ)^(-1 : ℤ) = 1/2 := by
            rw [show ((-1 : ℤ)) = -(1 : ℤ) from by ring, zpow_neg]; norm_num
          rw [this]; ring
        rw [h_7_2] at h_z_lt_m
        have hc'_r_lt : (c' : ℝ) < 7/2 :=
          lt_of_mul_lt_mul_right h_z_lt_m h_2e_pos.le
        have hc'_lt_4 : (c' : ℝ) < 4 := by linarith
        have : c' < 4 := by exact_mod_cast hc'_lt_4
        have hc'_le_3 : c' ≤ 3 := by omega
        change (z : ℝ) ≤ (y_lo : ℝ)
        rw [hc', h_y_lo_coe]
        have : (c' : ℝ) ≤ 3 := by exact_mod_cast hc'_le_3
        nlinarith
    have h_close_lo := h_close y_lo (y_lo_mem_F₁_g p hp_ge_2 e) h_y_lo_faith
    -- |x − y_hi| = 2^(e−1) + 2^k/4, |x − y_lo| = 2^(e−1) − 2^k/4.
    have hx_eq : x_val = (m : ℝ) - (2 : ℝ)^k / 4 := by
      rw [hx_def]; linarith
    have h_x_y_hi : x_val - (y_hi : ℝ) = -((2 : ℝ)^(e-1) + (2 : ℝ)^k/4) := by
      rw [h_y_hi_eq, hx_eq]; ring
    have h_x_y_lo : x_val - (y_lo : ℝ) = (2 : ℝ)^(e-1) - (2 : ℝ)^k/4 := by
      rw [h_y_lo_eq, hx_eq]; ring
    have h_2k4_pos : (0 : ℝ) < (2 : ℝ)^k / 4 := by linarith
    have h_2k4_lt : (2 : ℝ)^k / 4 < (2 : ℝ)^(e - 1) := by linarith [h_2k_lt_2e1]
    have hL : |x_val - (y_hi : ℝ)| = (2 : ℝ)^(e-1) + (2 : ℝ)^k/4 := by
      rw [h_x_y_hi, abs_neg, abs_of_pos]; linarith
    have hR : |x_val - (y_lo : ℝ)| = (2 : ℝ)^(e-1) - (2 : ℝ)^k/4 := by
      rw [h_x_y_lo, abs_of_pos]; linarith
    rw [hL, hR] at h_close_lo
    linarith

/-- **Convenience wrapper** with the minimal user-facing hypotheses: the
paper-style containment `(F₁.extend 2) ⊆ F₂` plus the structural finiteness
of `F₂.p` and `F₂.exp`. The precision/quantum bounds and the unboundedness of
`F₂.b` are derived internally and forwarded to `no_rndRNE_RNE_arbitrary_F₂`.

The two finiteness hypotheses are essential: the predecessor-extraction
machinery needs `exists_grid_rep`, which requires both `F.p` and `F.exp`
finite. (Containment alone does *not* force these — `F₂.p = ⊤` and
`F₂.exp = ⊥` are consistent with `F₁.extend 2 ⊆ F₂`.) -/
theorem no_rndRNE_RNE
    (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ)
    (F₂ : AbstractFormat)
    (hsub : (F₁_g p hp_ge_2 e).extend 2 ⊆ F₂)
    (hF₂_p_fin : F₂.p ≠ ⊤)
    (hF₂_exp_fin : F₂.exp ≠ ⊥) :
    ∃ (x : ℝ) (z w : Dyadic),
      Rounds F₂ (.Nearest .ToEven) x z ∧
      Rounds (F₁_g p hp_ge_2 e) (.Nearest .ToEven) (z : ℝ) w ∧
      ¬ Rounds (F₁_g p hp_ge_2 e) (.Nearest .ToEven) x w := by
  -- Extract finite q₂ and f₂.
  obtain ⟨q₂, hq₂_eq⟩ := WithTop.ne_top_iff_exists.mp hF₂_p_fin
  obtain ⟨f₂, hf₂_eq⟩ := WithBot.ne_bot_iff_exists.mp hF₂_exp_fin
  have hF₂_p : F₂.p = (q₂ : ℕ∞) := hq₂_eq.symm
  have hF₂_exp : F₂.exp = (f₂ : WithBot ℤ) := hf₂_eq.symm
  -- Derive F₂.b = ⊤ from arbitrarily large element.
  have hF₂_b : F₂.b = ⊤ := by
    by_contra h_b_ne
    obtain ⟨b, hb_eq⟩ := WithTop.ne_top_iff_exists.mp h_b_ne
    set N : ℤ := max (e - 2) (Int.log 2 ((b : Dyadic) : ℝ) + 1) with hN_def
    set y_huge : Dyadic := Dyadic.ofIntZpow 1 N with hy_huge_def
    have hN_ge : e - 2 ≤ N := le_max_left _ _
    have hy_huge_real : ((y_huge : Dyadic) : ℝ) = (2 : ℝ)^N := by
      rw [hy_huge_def, Dyadic.coe_ofIntZpow]; push_cast; ring
    have hy_huge_in_ext2 : y_huge ∈ (F₁_g p hp_ge_2 e).extend 2 := by
      refine ⟨?_, ?_, trivial⟩
      · change Dyadic.precisionAtMost ((((p : ℕ) : ℕ∞)) + (2 : ℕ)) y_huge
        have h_eq : ((((p : ℕ) : ℕ∞)) + (2 : ℕ)) = ((p + 2 : ℕ) : ℕ∞) := by
          push_cast; ring
        rw [h_eq]
        refine ⟨1, N, ?_, ?_⟩
        · rw [hy_huge_real]; push_cast; ring
        · have h_pow : (2 : ℤ) ≤ (2 : ℤ)^(p + 2) :=
            calc (2 : ℤ) = (2 : ℤ)^1 := by norm_num
              _ ≤ (2 : ℤ)^(p + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
          have h_abs : |(1 : ℤ)| = 1 := by decide
          omega
      · change Dyadic.quantumAtLeast (((e - 2 : ℤ)) : WithBot ℤ) y_huge
        rw [Dyadic.quantumAtLeast_coe]
        refine ⟨(2 : ℤ)^(N - (e - 2)).toNat, ?_⟩
        rw [hy_huge_real, two_zpow_split_toNat (show e - 2 ≤ N by omega)]
        push_cast; ring
    have hy_huge_in_F₂ : y_huge ∈ F₂ := hsub _ hy_huge_in_ext2
    have hb_ok : boundOK F₂.b y_huge := hy_huge_in_F₂.2.2
    rw [← hb_eq] at hb_ok
    change |((y_huge : Dyadic) : ℝ)| ≤ ((b : Dyadic) : ℝ) at hb_ok
    rw [hy_huge_real] at hb_ok
    have h_2N_pos : (0 : ℝ) < (2 : ℝ)^N := zpow_pos (by norm_num) _
    rw [abs_of_pos h_2N_pos] at hb_ok
    have hN_ge_log : Int.log 2 ((b : Dyadic) : ℝ) + 1 ≤ N := le_max_right _ _
    by_cases hb_pos : 0 < ((b : Dyadic) : ℝ)
    · have h_lt_log_succ :
          ((b : Dyadic) : ℝ) < (2 : ℝ)^(Int.log 2 ((b : Dyadic) : ℝ) + 1) := by
        have := Int.lt_zpow_succ_log_self (b := 2)
          (by norm_num : 1 < (2 : ℕ)) ((b : Dyadic) : ℝ)
        rw [show ((2 : ℕ) : ℝ) = 2 from by push_cast; rfl] at this
        exact this
      have h_2N_ge : (2 : ℝ)^(Int.log 2 ((b : Dyadic) : ℝ) + 1) ≤ (2 : ℝ)^N :=
        zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hN_ge_log
      linarith
    · push Not at hb_pos
      linarith
  -- Derive p + 2 ≤ q₂ and f₂ ≤ e - 2 from a "tight" element.
  have hq₂_hf₂ : p + 2 ≤ q₂ ∧ f₂ ≤ e - 2 := by
    set c_max : ℤ := (2 : ℤ)^(p + 2) - 1 with hc_max_def
    have hc_max_pos : 0 < c_max := by
      have h_pow_ge : (2 : ℤ) ≤ (2 : ℤ)^(p + 2) := by
        calc (2 : ℤ) = (2 : ℤ)^1 := by norm_num
          _ ≤ (2 : ℤ)^(p + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
      omega
    have hc_max_lt : c_max < (2 : ℤ)^(p + 2) := by omega
    have hc_max_odd : Odd c_max := by
      refine ⟨(2 : ℤ)^(p + 1) - 1, ?_⟩
      rw [hc_max_def, show p + 2 = (p + 1) + 1 from by omega, pow_succ]
      ring
    set y_max : Dyadic := Dyadic.ofIntZpow c_max (e - 2) with hy_max_def
    have hy_max_real : ((y_max : Dyadic) : ℝ) = (c_max : ℝ) * (2 : ℝ)^(e - 2) := by
      rw [hy_max_def, Dyadic.coe_ofIntZpow]
    have h_2e2_pos : (0 : ℝ) < (2 : ℝ)^(e - 2) := zpow_pos (by norm_num) _
    have hy_max_pos : 0 < ((y_max : Dyadic) : ℝ) := by
      rw [hy_max_real]
      have : (0 : ℝ) < (c_max : ℝ) := by exact_mod_cast hc_max_pos
      exact mul_pos this h_2e2_pos
    have hy_max_in_ext2 : y_max ∈ (F₁_g p hp_ge_2 e).extend 2 := by
      refine ⟨?_, ?_, trivial⟩
      · change Dyadic.precisionAtMost ((((p : ℕ) : ℕ∞)) + (2 : ℕ)) y_max
        have h_eq : ((((p : ℕ) : ℕ∞)) + (2 : ℕ)) = ((p + 2 : ℕ) : ℕ∞) := by
          push_cast; ring
        rw [h_eq]
        refine ⟨c_max, e - 2, hy_max_real, ?_⟩
        rw [abs_of_pos hc_max_pos]; exact hc_max_lt
      · change Dyadic.quantumAtLeast (((e - 2 : ℤ)) : WithBot ℤ) y_max
        rw [Dyadic.quantumAtLeast_coe]; refine ⟨c_max, hy_max_real⟩
    have hy_max_in_F₂ : y_max ∈ F₂ := hsub _ hy_max_in_ext2
    -- Apply exists_grid_rep at F₂.
    obtain ⟨k, c, hk_ge_f₂, hc_lt_abs, hy_eq, hk_max⟩ :=
      exists_grid_rep F₂ hF₂_p hF₂_exp hy_max_in_F₂.1 hy_max_in_F₂.2.1 hy_max_pos
    have h_eq_real : (c : ℝ) * (2 : ℝ)^k = (c_max : ℝ) * (2 : ℝ)^(e - 2) := by
      rw [← hy_max_real, ← hy_eq]
    -- k ≤ e - 2 from c integer + c_max odd.
    have hk_le : k ≤ e - 2 := by
      by_contra h_gt
      push Not at h_gt
      -- Extract n : ℕ with (n : ℤ) = k - (e - 2) and 1 ≤ n.
      set n : ℕ := (k - (e - 2)).toNat with hn_def
      have h_n_eq : (n : ℤ) = k - (e - 2) := Int.toNat_of_nonneg (by omega)
      have h_n_ge_1 : 1 ≤ n := by
        have : (1 : ℤ) ≤ (n : ℤ) := by rw [h_n_eq]; omega
        exact_mod_cast this
      have h_2e2_ne : (2 : ℝ)^(e - 2) ≠ 0 := ne_of_gt h_2e2_pos
      -- From c·2^k = c_max·2^(e-2), divide by 2^(e-2):
      have h_real_eq2 : (c : ℝ) * (2 : ℝ)^(n : ℤ) = (c_max : ℝ) := by
        have h_split : (2 : ℝ)^k = (2 : ℝ)^(n : ℤ) * (2 : ℝ)^(e - 2) := by
          rw [show (k : ℤ) = (n : ℤ) + (e - 2) from by linarith [h_n_eq],
              zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        rw [h_split, ← mul_assoc] at h_eq_real
        exact mul_right_cancel₀ h_2e2_ne h_eq_real
      -- (2 : ℝ)^(n : ℤ) = (2 : ℕ)^n in ℝ.
      rw [zpow_natCast] at h_real_eq2
      -- Cast to ℤ.
      have h_int_eq : c * (2 : ℤ)^n = c_max := by
        have h_cast : ((c * (2 : ℤ)^n : ℤ) : ℝ) = ((c_max : ℤ) : ℝ) := by
          push_cast; exact h_real_eq2
        exact_mod_cast h_cast
      -- c_max = c · 2^n with n ≥ 1 ⇒ c_max even.
      have h_even : Even c_max := by
        rw [← h_int_eq, show (n : ℕ) = (n - 1) + 1 from by omega, pow_succ]
        refine ⟨c * (2 : ℤ)^(n - 1), ?_⟩
        ring
      exact (Int.not_even_iff_odd.mpr hc_max_odd) h_even
    -- Compute log y_max = e + p - 1.
    have h_log_y_max : Int.log 2 ((y_max : Dyadic) : ℝ) = e + p - 1 := by
      rw [hy_max_real]
      apply le_antisymm
      · -- Upper bound: c_max · 2^(e-2) < 2^(e+p).
        have h_lt : (c_max : ℝ) * (2 : ℝ)^(e - 2) < ((2 : ℕ) : ℝ)^(e + p) := by
          rw [show ((2 : ℕ) : ℝ) = 2 from by push_cast; rfl,
              show e + p = (e - 2) + (p + 2) by ring,
              zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          have h_2p_pow : (2 : ℝ)^((p + 2 : ℕ) : ℤ) = ((2 : ℤ)^(p + 2) : ℝ) := by
            rw [zpow_natCast]; push_cast; ring
          rw [show ((p + 2 : ℤ)) = ((p + 2 : ℕ) : ℤ) from by push_cast; rfl, h_2p_pow]
          have hc_max_lt_r : (c_max : ℝ) < ((2 : ℤ)^(p + 2) : ℝ) := by
            exact_mod_cast hc_max_lt
          nlinarith
        have hy_pos' : (0 : ℝ) < (c_max : ℝ) * (2 : ℝ)^(e - 2) := by
          rw [← hy_max_real]; exact hy_max_pos
        have := (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) hy_pos').mp h_lt
        omega
      · -- Lower bound: 2^(e+p-1) ≤ c_max · 2^(e-2).
        have h_ge : ((2 : ℕ) : ℝ)^(e + p - 1) ≤ (c_max : ℝ) * (2 : ℝ)^(e - 2) := by
          rw [show ((2 : ℕ) : ℝ) = 2 from by push_cast; rfl,
              show e + p - 1 = (e - 2) + (p + 1) by ring,
              zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          have h_2p1_pow : (2 : ℝ)^((p + 1 : ℕ) : ℤ) = ((2 : ℤ)^(p + 1) : ℝ) := by
            rw [zpow_natCast]; push_cast; ring
          rw [show ((p + 1 : ℤ)) = ((p + 1 : ℕ) : ℤ) from by push_cast; rfl, h_2p1_pow]
          have hc_max_ge : ((2 : ℤ)^(p + 1) : ℝ) ≤ (c_max : ℝ) := by
            have h_int : (2 : ℤ)^(p + 1) ≤ c_max := by
              rw [hc_max_def]
              have h_two_pp2 : (2 : ℤ)^(p + 2) = 2 * (2 : ℤ)^(p + 1) := by
                rw [show p + 2 = (p + 1) + 1 from by omega, pow_succ]; ring
              omega
            exact_mod_cast h_int
          nlinarith
        have hy_pos' : (0 : ℝ) < (c_max : ℝ) * (2 : ℝ)^(e - 2) := by
          rw [← hy_max_real]; exact hy_max_pos
        exact (Int.zpow_le_iff_le_log (by norm_num : 1 < (2 : ℕ)) hy_pos').mp h_ge
    rw [h_log_y_max] at hk_max
    have hk_eq : k = max f₂ (e + p - q₂) := by convert hk_max using 2; ring
    rw [hk_eq] at hk_le
    refine ⟨?_, ?_⟩
    · -- p + 2 ≤ q₂
      have h_part : e + p - (q₂ : ℤ) ≤ e - 2 := le_trans (le_max_right _ _) hk_le
      have hq_int : (p + 2 : ℤ) ≤ (q₂ : ℤ) := by omega
      exact_mod_cast hq_int
    · exact le_trans (le_max_left _ _) hk_le
  obtain ⟨hq₂, hf₂⟩ := hq₂_hf₂
  exact (no_rndRNE_RNE_arbitrary_F₂ p hp_ge_2 e F₂ hF₂_p hq₂ hF₂_exp hf₂ hF₂_b).2


/-! ## Other invalid double-rounding pairings

For each invalid `(outer, inner)` pairing in `{RNE, RTZ, RAZ, RTO}²`, we
exhibit a witness `x` whose chained F₂-then-F₁ rounding disagrees with the
direct F₁ rounding. The patterns:

* **Outer-rounds-to-zero** (RTZ outer): `x` lies just above an F₁-element
  `y`; F₂-RTZ truncates `x` down to `y`; the inner rounding then returns
  `y` exact, but direct rounding of the original `x` lands on a different
  F₁-element.
* **Outer-rounds-away-from-zero** (RAZ outer): mirror case — `x` lies just
  below `y`; F₂-RAZ pushes up to `y`.
* **Outer-rounds-to-nearest** (RNE outer): `x` lies in `0`'s F₂-Voronoi
  cell (when `x` is very small) or in an upper-half F₂-bracket below an
  F₁-element. F₂-RNE snaps `x` to an F₁-element; the inner rounding then
  returns that value exact, but direct rounding of `x` would not.

All counterexamples use the same `F₁ = 𝒜(p, e, ⊤)` (with `p ≥ 2`) as the
RNE-RNE case, except `no_rndRTZ_RNE` which needs an F₁-adjacent
pair where the *lower* significand is even — see its docstring. -/

/-- For any `F₂` with finite quantum `f₂`, no F₂-element lies strictly in
`(0, 2^f₂)`: quantumAtLeast forces `z = c · 2^f₂` for some `c : ℤ`, and
`0 < z < 2^f₂` would require `0 < c < 1`. -/
private theorem F₂_no_element_in_zero_quantum_interval
    (F₂ : AbstractFormat) {f₂ : ℤ} (hF₂_exp : F₂.exp = (f₂ : WithBot ℤ))
    {z : Dyadic} (hzF : z ∈ F₂)
    (hz_pos : 0 < ((z : Dyadic) : ℝ))
    (hz_lt : ((z : Dyadic) : ℝ) < (2 : ℝ) ^ f₂) :
    False := by
  obtain ⟨_, hq, _⟩ := hzF
  rw [hF₂_exp, Dyadic.quantumAtLeast_coe] at hq
  obtain ⟨c, hc⟩ := hq
  rw [hc] at hz_pos hz_lt
  have h_2f_pos : (0 : ℝ) < (2 : ℝ) ^ f₂ := zpow_pos (by norm_num) _
  have hc_pos : 0 < (c : ℝ) := pos_of_mul_pos_left (by linarith) h_2f_pos.le
  have hc_lt : (c : ℝ) < 1 := by
    have h1 : (c : ℝ) * (2 : ℝ)^f₂ < 1 * (2 : ℝ)^f₂ := by linarith
    exact lt_of_mul_lt_mul_right h1 h_2f_pos.le
  have hc_int_pos : 0 < c := by exact_mod_cast hc_pos
  have hc_int_lt_1 : c < 1 := by exact_mod_cast hc_lt
  omega

/-- For any F₂ with finite quantum `f₂` and `F₁_g ⊆ F₂`, F₂.b must be `⊤`
(F₁_g has unbounded magnitude, so any finite F₂.b is contradicted by a
large-enough element of F₁_g being in F₂). -/
private theorem F₂_b_top_of_F₁_g_subset
    (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ)
    (F₂ : AbstractFormat) (hsub : F₁_g p hp_ge_2 e ⊆ F₂) :
    F₂.b = ⊤ := by
  by_contra h_b_ne
  obtain ⟨b, hb_eq⟩ := WithTop.ne_top_iff_exists.mp h_b_ne
  set N : ℤ := max e (Int.log 2 ((b : Dyadic) : ℝ) + 1) with hN_def
  set y_huge : Dyadic := Dyadic.ofIntZpow 1 N with hy_huge_def
  have hy_huge_real : ((y_huge : Dyadic) : ℝ) = (2 : ℝ)^N := by
    rw [hy_huge_def, Dyadic.coe_ofIntZpow]; push_cast; ring
  have hN_ge : e ≤ N := le_max_left _ _
  have hy_huge_in_F₁ : y_huge ∈ F₁_g p hp_ge_2 e := by
    refine ⟨?_, ?_, trivial⟩
    · change Dyadic.precisionAtMost ((p : ℕ) : ℕ∞) y_huge
      refine ⟨1, N, ?_, ?_⟩
      · rw [hy_huge_real]; push_cast; ring
      · have h_pow : (2 : ℤ) ≤ (2 : ℤ)^p :=
          calc (2 : ℤ) = (2 : ℤ)^1 := by norm_num
            _ ≤ (2 : ℤ)^p := pow_le_pow_right₀ (by norm_num) (by omega)
        have h_abs : |(1 : ℤ)| = 1 := by decide
        omega
    · change Dyadic.quantumAtLeast (((e : ℤ)) : WithBot ℤ) y_huge
      rw [Dyadic.quantumAtLeast_coe]
      refine ⟨(2 : ℤ)^(N - e).toNat, ?_⟩
      rw [hy_huge_real, two_zpow_split_toNat (show e ≤ N by omega)]
      push_cast; ring
  have hy_huge_in_F₂ : y_huge ∈ F₂ := hsub _ hy_huge_in_F₁
  have hb_ok : boundOK F₂.b y_huge := hy_huge_in_F₂.2.2
  rw [← hb_eq] at hb_ok
  change |((y_huge : Dyadic) : ℝ)| ≤ ((b : Dyadic) : ℝ) at hb_ok
  rw [hy_huge_real] at hb_ok
  have h_2N_pos : (0 : ℝ) < (2 : ℝ)^N := zpow_pos (by norm_num) _
  rw [abs_of_pos h_2N_pos] at hb_ok
  have hN_ge_log : Int.log 2 ((b : Dyadic) : ℝ) + 1 ≤ N := le_max_right _ _
  by_cases hb_pos : 0 < ((b : Dyadic) : ℝ)
  · have h_lt_log_succ :
        ((b : Dyadic) : ℝ) < (2 : ℝ)^(Int.log 2 ((b : Dyadic) : ℝ) + 1) := by
      have := Int.lt_zpow_succ_log_self (b := 2)
        (by norm_num : 1 < (2 : ℕ)) ((b : Dyadic) : ℝ)
      rw [show ((2 : ℕ) : ℝ) = 2 from by push_cast; rfl] at this
      exact this
    have h_2N_ge : (2 : ℝ)^(Int.log 2 ((b : Dyadic) : ℝ) + 1) ≤ (2 : ℝ)^N :=
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hN_ge_log
    linarith
  · push Not at hb_pos; linarith

/-- **Counterexample to `rndRNE_RAZ`.**

For any `F₂` with finite quantum, the witness `x = 2^(F₂.exp - 2)` sits
strictly inside `0`'s F₂-Voronoi cell (it's a quarter of F₂'s grid step
above zero). F₂-RNE rounds it *down* to `0`; F₁-RAZ then keeps `0`; but
direct F₁-RAZ on `x` (a positive real) rounds *up* to the smallest
positive F₁-element.

The standard double-rounding framing assumes `F₁ ⊆ F₂`, but that
hypothesis is *not technically needed* here — the witness lives in
F₂'s "round-to-0" zone where F₁'s structure is irrelevant to the
failure. The counterexample therefore covers the entire family
`F₁ ⊆ F₂`, including the trivial `F₁ = F₂` case: even when F₂ is no
larger than F₁, the witness `x = 2^(e − 2)` is still not in F₂ (it
violates `F₂.quantumAtLeast e`), so the chain is non-trivial and fails
in the same way. This reflects that RNE-RAZ disagreement is intrinsic
to the modes themselves, not to any precision gap between F₁ and F₂. -/
theorem no_rndRNE_RAZ
    (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ)
    (F₂ : AbstractFormat) (hF₂_exp_fin : F₂.exp ≠ ⊥) :
    ∃ (x : ℝ) (z w : Dyadic),
      Rounds F₂ (.Nearest .ToEven) x z ∧
      Rounds (F₁_g p hp_ge_2 e) .AwayZero (z : ℝ) w ∧
      ¬ Rounds (F₁_g p hp_ge_2 e) .AwayZero x w := by
  obtain ⟨f₂, hf₂_eq⟩ := WithBot.ne_bot_iff_exists.mp hF₂_exp_fin
  have hF₂_exp : F₂.exp = (f₂ : WithBot ℤ) := hf₂_eq.symm
  -- Setup constants.
  set x_val : ℝ := (2 : ℝ)^(f₂ - 2) with hx_def
  have h_2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
  have h_2f2_pos : (0 : ℝ) < (2 : ℝ)^(f₂ - 2) := zpow_pos (by norm_num) _
  have h_x_pos : 0 < x_val := h_2f2_pos
  have h_2f_split : (2 : ℝ)^f₂ = 4 * (2 : ℝ)^(f₂ - 2) := by
    have h_eq : (2 : ℝ)^f₂ = (2 : ℝ)^(f₂ - 2) * (2 : ℝ)^(2 : ℤ) := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
    have h2 : (2 : ℝ)^(2 : ℤ) = 4 := by norm_num
    rw [h_eq, h2]; ring
  have h_x_lt_2f : x_val < (2 : ℝ)^f₂ := by rw [h_2f_split]; linarith
  -- For any z ∈ F₂ with z ≤ x, we have z ≤ 0.
  have h_F₂_le_x_to_le_0 : ∀ z ∈ F₂, ((z : Dyadic) : ℝ) ≤ x_val →
      ((z : Dyadic) : ℝ) ≤ 0 := by
    intro z hz hz_le
    obtain ⟨_, hq, _⟩ := hz
    rw [hF₂_exp, Dyadic.quantumAtLeast_coe] at hq
    obtain ⟨c, hc⟩ := hq
    -- c · 2^f₂ ≤ 2^(f₂-2). Multiply both sides by 4/2^f₂: 4c ≤ 1/4·4 = 1.
    rw [hc] at hz_le
    have hc_le_quart : (c : ℝ) ≤ 1/4 := by
      have hxv : x_val = (1/4 : ℝ) * (2 : ℝ)^f₂ := by
        rw [hx_def, h_2f_split]; ring
      rw [hxv] at hz_le
      exact le_of_mul_le_mul_right hz_le h_2f_pos
    have hc_lt_1 : (c : ℝ) < 1 := by linarith
    have hc_int_lt : c < 1 := by exact_mod_cast hc_lt_1
    have hc_le_0 : c ≤ 0 := by omega
    rw [hc]
    have h_cr : (c : ℝ) ≤ 0 := by exact_mod_cast hc_le_0
    nlinarith
  -- For any z ∈ F₂ with z ≥ x, we have z ≥ 2^f₂.
  have h_F₂_ge_x_to_ge_2f : ∀ z ∈ F₂, x_val ≤ ((z : Dyadic) : ℝ) →
      (2 : ℝ)^f₂ ≤ ((z : Dyadic) : ℝ) := by
    intro z hz hz_ge
    obtain ⟨_, hq, _⟩ := hz
    rw [hF₂_exp, Dyadic.quantumAtLeast_coe] at hq
    obtain ⟨c, hc⟩ := hq
    rw [hc] at hz_ge
    have hc_ge_quart : (1/4 : ℝ) ≤ (c : ℝ) := by
      have hxv : x_val = (1/4 : ℝ) * (2 : ℝ)^f₂ := by
        rw [hx_def, h_2f_split]; ring
      rw [hxv] at hz_ge
      exact le_of_mul_le_mul_right hz_ge h_2f_pos
    have hc_gt_0 : (0 : ℝ) < (c : ℝ) := by linarith
    have hc_int_pos : 0 < c := by exact_mod_cast hc_gt_0
    have hc_ge_1 : 1 ≤ c := hc_int_pos
    rw [hc]
    have h_cr : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc_ge_1
    nlinarith
  refine ⟨x_val, 0, 0, ?_, ?_, ?_⟩
  · refine ⟨F₂.zero_mem, ?_, ?_, ?_⟩
    · -- IsFaithfulRound (RoundDown 0).
      left
      refine ⟨F₂.zero_mem, ?_, ?_⟩
      · change ((0 : Dyadic) : ℝ) ≤ x_val
        push_cast; linarith
      · intro z hz hz_le
        have := h_F₂_le_x_to_le_0 z hz hz_le
        change ((z : Dyadic) : ℝ) ≤ ((0 : Dyadic) : ℝ)
        push_cast; linarith
    · -- Closeness. Faithful z is RoundDown (≤ 0) or RoundUp (≥ 2^f₂).
      intro z hz hf
      push_cast
      rcases hf with ⟨_, hz_le, _⟩ | ⟨_, hz_ge, _⟩
      · have h_z_le_0 := h_F₂_le_x_to_le_0 z hz hz_le
        rw [show x_val - 0 = x_val from by ring, abs_of_pos h_x_pos]
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x_val - (z : ℝ))]
        linarith
      · have h_z_ge_2f := h_F₂_ge_x_to_ge_2f z hz hz_ge
        rw [show x_val - 0 = x_val from by ring, abs_of_pos h_x_pos]
        rw [abs_of_nonpos (by linarith : x_val - (z : ℝ) ≤ 0), neg_sub]
        -- z - x ≥ 4·2^(f₂-2) - 2^(f₂-2) = 3·2^(f₂-2) ≥ 2^(f₂-2) = x.
        linarith
    · -- No tie: distances to 0 (= 2^(f₂-2)) and any faithful z ≠ 0 differ.
      rintro ⟨z, hzF, hf, hne, heq⟩
      change |x_val - ((0 : Dyadic) : ℝ)| = |x_val - ((z : Dyadic) : ℝ)| at heq
      push_cast at heq
      rcases hf with ⟨_, hz_le, _⟩ | ⟨_, hz_ge, _⟩
      · have h_z_le_0 := h_F₂_le_x_to_le_0 z hzF hz_le
        have h_z_lt_0 : ((z : Dyadic) : ℝ) < 0 := by
          rcases lt_or_eq_of_le h_z_le_0 with h | h_eq
          · exact h
          · exfalso; apply hne; exact Subtype.ext h_eq
        rw [show x_val - 0 = x_val from by ring, abs_of_pos h_x_pos] at heq
        rw [abs_of_pos (by linarith : 0 < x_val - (z : ℝ))] at heq
        linarith
      · have h_z_ge_2f := h_F₂_ge_x_to_ge_2f z hzF hz_ge
        rw [show x_val - 0 = x_val from by ring, abs_of_pos h_x_pos] at heq
        rw [abs_of_nonpos (by linarith : x_val - (z : ℝ) ≤ 0), neg_sub] at heq
        linarith
  · refine ⟨(F₁_g p hp_ge_2 e).zero_mem, ?_, ?_, ?_⟩
    · change |((0 : Dyadic) : ℝ)| ≤ |((0 : Dyadic) : ℝ)|; rfl
    · change ((0 : Dyadic) : ℝ) * ((0 : Dyadic) : ℝ) ≥ 0
      push_cast; linarith
    · intro v _ _ _
      push_cast
      rw [abs_zero]
      exact abs_nonneg _
  · -- |x| > 0 = |0|, so the bound clause of `Rounds F₁ RAZ x 0` fails.
    intro hr
    obtain ⟨_, h_bnd, _, _⟩ := hr
    change |x_val| ≤ |((0 : Dyadic) : ℝ)| at h_bnd
    push_cast at h_bnd
    rw [abs_of_pos h_x_pos, abs_zero] at h_bnd
    linarith

/-- **Counterexample to `rndRNE_RTZ`.**

For any `F₂` with finite quantum `f₂ ≤ e` (forced by `F₁_g ⊆ F₂`), the
witness `x = 2^e - 2^(f₂ − 2)` lies just below the F₁-element `2^e`,
strictly inside `2^e`'s F₂-Voronoi cell from below (since F₂'s
predecessor of `2^e` is at most `2^e - 2^f₂`). F₂-RNE pushes `x` *up*
to `2^e`; F₁-RTZ then keeps `2^e` (it's exact in F₁); but direct
F₁-RTZ on the original `x` truncates *down* to `0` (the largest
F₁-element `≤ x` with the same sign). -/
theorem no_rndRNE_RTZ
    (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ)
    (F₂ : AbstractFormat) (hsub : F₁_g p hp_ge_2 e ⊆ F₂)
    (hF₂_exp_fin : F₂.exp ≠ ⊥) :
    ∃ (x : ℝ) (z w : Dyadic),
      Rounds F₂ (.Nearest .ToEven) x z ∧
      Rounds (F₁_g p hp_ge_2 e) .ToZero (z : ℝ) w ∧
      ¬ Rounds (F₁_g p hp_ge_2 e) .ToZero x w := by
  obtain ⟨f₂, hf₂_eq⟩ := WithBot.ne_bot_iff_exists.mp hF₂_exp_fin
  have hF₂_exp : F₂.exp = (f₂ : WithBot ℤ) := hf₂_eq.symm
  have h_two_e_in_F₁ := two_e_mem_F₁_g p hp_ge_2 e
  have h_two_e_in_F₂ : two_e_g e ∈ F₂ := hsub _ h_two_e_in_F₁
  have hf₂_le_e : f₂ ≤ e := f₂_le_e_of_F₁_g_subset p hp_ge_2 e F₂ hsub hF₂_exp
  -- Setup.
  set x_val : ℝ := (2 : ℝ)^e - (2 : ℝ)^(f₂ - 2) with hx_def
  have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
  have h_2f2_pos : (0 : ℝ) < (2 : ℝ)^(f₂ - 2) := zpow_pos (by norm_num) _
  have h_2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
  have h_2f2_lt_2e : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^e :=
    zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < e)
  have h_x_pos : 0 < x_val := by rw [hx_def]; linarith
  have h_x_lt_2e : x_val < (2 : ℝ)^e := by rw [hx_def]; linarith
  have h_two_e_coe := coe_two_e_g e
  -- 2^(e - f₂) as a natural-power of 2.
  set n : ℕ := (e - f₂).toNat with hn_def
  have h_2e_eq : (2 : ℝ)^e = ((2 : ℤ)^n : ℝ) * (2 : ℝ)^f₂ := two_zpow_split e f₂ hf₂_le_e
  -- 2^f₂ = 4 · 2^(f₂-2) (split helper).
  have h_2f_split : (2 : ℝ)^f₂ = 4 * (2 : ℝ)^(f₂ - 2) := by
    have h_eq : (2 : ℝ)^f₂ = (2 : ℝ)^(f₂ - 2) * (2 : ℝ)^(2 : ℤ) := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
    rw [h_eq, show (2 : ℝ)^(2 : ℤ) = 4 by norm_num]; ring
  -- Any z ∈ F₂ with z < 2^e satisfies z ≤ 2^e - 2^f₂.
  have h_F₂_lt_2e_bound : ∀ z ∈ F₂, ((z : Dyadic) : ℝ) < (2 : ℝ)^e →
      ((z : Dyadic) : ℝ) ≤ (2 : ℝ)^e - (2 : ℝ)^f₂ := by
    intro z hz hz_lt
    obtain ⟨_, hq, _⟩ := hz
    rw [hF₂_exp, Dyadic.quantumAtLeast_coe] at hq
    obtain ⟨c, hc⟩ := hq
    rw [hc] at hz_lt ⊢
    -- (c + 1) · 2^f₂ ≤ 2^e.
    have h_mul_bnd : ((c : ℝ) + 1) * (2 : ℝ)^f₂ ≤ (2 : ℝ)^e := by
      rw [h_2e_eq] at hz_lt
      have hc_lt : (c : ℝ) < ((2 : ℤ)^n : ℝ) :=
        lt_of_mul_lt_mul_right hz_lt h_2f_pos.le
      have hc_int_lt : c < (2 : ℤ)^n := by exact_mod_cast hc_lt
      have hc_int_le : c + 1 ≤ (2 : ℤ)^n := by omega
      have hc_real_le : (c : ℝ) + 1 ≤ ((2 : ℤ)^n : ℝ) := by exact_mod_cast hc_int_le
      have h_mul : ((c : ℝ) + 1) * (2 : ℝ)^f₂ ≤ ((2 : ℤ)^n : ℝ) * (2 : ℝ)^f₂ :=
        mul_le_mul_of_nonneg_right hc_real_le h_2f_pos.le
      rw [← h_2e_eq] at h_mul; exact h_mul
    linarith
  -- Any z ∈ F₂ with z ≥ x satisfies z ≥ 2^e (no F₂-element strictly between x and 2^e).
  have h_F₂_ge_x_to_ge_2e : ∀ z ∈ F₂, x_val ≤ ((z : Dyadic) : ℝ) →
      (2 : ℝ)^e ≤ ((z : Dyadic) : ℝ) := by
    intro z hz hz_ge
    by_contra h_lt
    push Not at h_lt
    have h_z_bnd := h_F₂_lt_2e_bound z hz h_lt
    -- z ≤ 2^e - 2^f₂. But z ≥ x = 2^e - 2^(f₂-2). 2^f₂ > 2^(f₂-2) so contradiction.
    have h_2f2_lt_2f : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^f₂ := by
      have : f₂ - 2 < f₂ := by omega
      exact zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) this
    linarith
  refine ⟨x_val, two_e_g e, two_e_g e, ?_, ?_, ?_⟩
  · refine ⟨h_two_e_in_F₂, ?_, ?_, ?_⟩
    · -- IsFaithfulRound (RoundUp 2^e).
      right
      refine ⟨h_two_e_in_F₂, ?_, ?_⟩
      · rw [h_two_e_coe]; linarith
      · intro z hz hz_ge
        rw [h_two_e_coe]
        exact h_F₂_ge_x_to_ge_2e z hz hz_ge
    · -- Closeness.
      intro z hz hf
      rw [h_two_e_coe]
      rcases hf with ⟨_, hz_le, _⟩ | ⟨_, hz_ge, _⟩
      · -- RoundDown z ≤ 2^e − 2^f₂, so x − z ≥ 3·2^(f₂−2) ≥ 2^(f₂−2) = 2^e − x.
        have h_z_lt_2e : (z : ℝ) < (2 : ℝ)^e := lt_of_le_of_lt hz_le h_x_lt_2e
        have h_z_bnd := h_F₂_lt_2e_bound z hz h_z_lt_2e
        rw [abs_of_neg (by rw [hx_def]; linarith : x_val - (2 : ℝ)^e < 0), neg_sub]
        rw [abs_of_nonneg (by rw [hx_def]; linarith : (0 : ℝ) ≤ x_val - (z : ℝ))]
        rw [h_2f_split] at h_z_bnd
        rw [hx_def]; linarith
      · -- RoundUp z ≥ 2^e, so z − x ≥ 2^e − x = 2^(f₂−2).
        have h_z_ge_2e := h_F₂_ge_x_to_ge_2e z hz hz_ge
        rw [abs_of_neg (by rw [hx_def]; linarith : x_val - (2 : ℝ)^e < 0), neg_sub]
        rw [abs_of_nonpos (by linarith : x_val - (z : ℝ) ≤ 0), neg_sub]
        linarith
    · -- No tie: RoundDown z has |x−z| ≥ 3·2^(f₂−2); RoundUp z ≠ 2^e jumps to ≥ 2^e + 2^f₂.
      rintro ⟨z, hzF₂, hf, hne, heq⟩
      rw [h_two_e_coe] at heq
      rcases hf with ⟨_, hz_le, _⟩ | ⟨_, hz_ge, _⟩
      · exfalso
        have h_z_lt_2e : (z : ℝ) < (2 : ℝ)^e := lt_of_le_of_lt hz_le h_x_lt_2e
        have h_z_bnd := h_F₂_lt_2e_bound z hzF₂ h_z_lt_2e
        rw [abs_of_neg (by rw [hx_def]; linarith : x_val - (2 : ℝ)^e < 0), neg_sub] at heq
        rw [abs_of_nonneg (by rw [hx_def]; linarith : (0 : ℝ) ≤ x_val - (z : ℝ))] at heq
        rw [h_2f_split] at h_z_bnd
        rw [hx_def] at heq
        linarith
      · exfalso
        have h_z_ge_2e := h_F₂_ge_x_to_ge_2e z hzF₂ hz_ge
        have h_z_ne_2e : (z : ℝ) ≠ (2 : ℝ)^e := by
          intro h_eq
          apply hne
          apply Subtype.ext
          rw [h_two_e_coe]; exact h_eq
        have h_z_gt_2e : (2 : ℝ)^e < (z : ℝ) := lt_of_le_of_ne h_z_ge_2e (Ne.symm h_z_ne_2e)
        -- From the f₂-quantum grid, z > 2^e forces z ≥ 2^e + 2^f₂.
        have h_z_ge_2e_plus : (2 : ℝ)^e + (2 : ℝ)^f₂ ≤ (z : ℝ) := by
          obtain ⟨_, hq, _⟩ := hzF₂
          rw [hF₂_exp, Dyadic.quantumAtLeast_coe] at hq
          obtain ⟨c, hc⟩ := hq
          rw [hc] at h_z_gt_2e ⊢
          rw [h_2e_eq] at h_z_gt_2e
          have hc_gt : ((2 : ℤ)^n : ℝ) < (c : ℝ) :=
            lt_of_mul_lt_mul_right h_z_gt_2e h_2f_pos.le
          have hc_int_gt : (2 : ℤ)^n < c := by exact_mod_cast hc_gt
          have hc_int_ge : (2 : ℤ)^n + 1 ≤ c := by omega
          have hc_real_ge : ((2 : ℤ)^n : ℝ) + 1 ≤ (c : ℝ) := by
            have h1 : (((2 : ℤ)^n + 1 : ℤ) : ℝ) ≤ ((c : ℤ) : ℝ) := by exact_mod_cast hc_int_ge
            push_cast at h1; exact h1
          have h_mul : (((2 : ℤ)^n : ℝ) + 1) * (2 : ℝ)^f₂ ≤ (c : ℝ) * (2 : ℝ)^f₂ :=
            mul_le_mul_of_nonneg_right hc_real_ge h_2f_pos.le
          rw [h_2e_eq]
          linarith
        rw [abs_of_neg (by rw [hx_def]; linarith : x_val - (2 : ℝ)^e < 0), neg_sub] at heq
        rw [abs_of_nonpos (by linarith : x_val - (z : ℝ) ≤ 0), neg_sub] at heq
        rw [hx_def] at heq; linarith
  · refine ⟨h_two_e_in_F₁, ?_, ?_, ?_⟩
    · rfl
    · exact mul_self_nonneg _
    · intro v _ hv_bnd _
      exact hv_bnd
  · -- Bound clause |2^e| ≤ |x| fails: x < 2^e and both are positive.
    intro hr
    obtain ⟨_, h_bnd, _, _⟩ := hr
    rw [h_two_e_coe] at h_bnd
    rw [abs_of_pos h_x_pos, abs_of_pos h_2e_pos] at h_bnd
    linarith

/-- **Counterexample to `rndRTZ_RAZ`.**

For any `F₂` with finite quantum `f₂ ≤ e` (forced by `F₁_g ⊆ F₂`), the
witness `x = 2^e + 2^(f₂ − 2)` lies just above the F₁-element `2^e`,
inside F₂'s "round-toward-zero" zone (F₂'s next grid point above `2^e`
is `2^e + 2^f₂` for the f₂-quantum grid). F₂-RTZ truncates `x` *down*
to `2^e`; F₁-RAZ on `2^e` returns `2^e` (it's already in F₁); but
direct F₁-RAZ on `x` rounds *up* to the next F₁-element `2^(e+1)`. -/
theorem no_rndRTZ_RAZ
    (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ)
    (F₂ : AbstractFormat) (hsub : F₁_g p hp_ge_2 e ⊆ F₂)
    (hF₂_exp_fin : F₂.exp ≠ ⊥) :
    ∃ (x : ℝ) (z w : Dyadic),
      Rounds F₂ .ToZero x z ∧
      Rounds (F₁_g p hp_ge_2 e) .AwayZero (z : ℝ) w ∧
      ¬ Rounds (F₁_g p hp_ge_2 e) .AwayZero x w := by
  obtain ⟨f₂, hf₂_eq⟩ := WithBot.ne_bot_iff_exists.mp hF₂_exp_fin
  have hF₂_exp : F₂.exp = (f₂ : WithBot ℤ) := hf₂_eq.symm
  have h_two_e_in_F₁ := two_e_mem_F₁_g p hp_ge_2 e
  have h_two_e_in_F₂ : two_e_g e ∈ F₂ := hsub _ h_two_e_in_F₁
  have hf₂_le_e : f₂ ≤ e := f₂_le_e_of_F₁_g_subset p hp_ge_2 e F₂ hsub hF₂_exp
  -- 2·2^e = 2^(e+1) ∈ F₁.
  have h_two_e1_in_F₁ : (Dyadic.ofIntZpow 1 (e + 1) : Dyadic) ∈ F₁_g p hp_ge_2 e := by
    refine ⟨?_, ?_, trivial⟩
    · change Dyadic.precisionAtMost ((p : ℕ) : ℕ∞) (Dyadic.ofIntZpow 1 (e + 1))
      refine ⟨1, e + 1, ?_, ?_⟩
      · rw [Dyadic.coe_ofIntZpow]
      · have h_pow : (2 : ℤ) ≤ (2 : ℤ)^p :=
          calc (2 : ℤ) = (2 : ℤ)^1 := by norm_num
            _ ≤ (2 : ℤ)^p := pow_le_pow_right₀ (by norm_num) (by omega)
        have : |(1 : ℤ)| = 1 := by decide
        omega
    · change Dyadic.quantumAtLeast (((e : ℤ)) : WithBot ℤ) (Dyadic.ofIntZpow 1 (e + 1))
      rw [Dyadic.quantumAtLeast_coe]
      refine ⟨2, ?_⟩
      rw [Dyadic.coe_ofIntZpow]
      have h_eq : (2 : ℝ)^(e + 1) = 2 * (2 : ℝ)^e := by
        have h1 : (2 : ℝ)^(e + 1) = (2 : ℝ)^e * (2 : ℝ)^(1 : ℤ) := by
          rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        rw [h1]; have h2 : (2 : ℝ)^(1 : ℤ) = 2 := by norm_num
        rw [h2]; ring
      rw [h_eq]; push_cast; ring
  -- Setup.
  set x_val : ℝ := (2 : ℝ)^e + (2 : ℝ)^(f₂ - 2) with hx_def
  have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
  have h_2f2_pos : (0 : ℝ) < (2 : ℝ)^(f₂ - 2) := zpow_pos (by norm_num) _
  have h_2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
  have h_x_pos : 0 < x_val := by rw [hx_def]; linarith
  have h_x_gt_2e : (2 : ℝ)^e < x_val := by rw [hx_def]; linarith
  have h_two_e_coe := coe_two_e_g e
  have h_two_e1_coe : ((Dyadic.ofIntZpow 1 (e + 1) : Dyadic) : ℝ) = (2 : ℝ)^(e + 1) := by
    rw [Dyadic.coe_ofIntZpow]; push_cast; ring
  have h_2e1_eq : (2 : ℝ)^(e + 1) = 2 * (2 : ℝ)^e := by
    have h : (2 : ℝ)^(e + 1) = (2 : ℝ)^e * (2 : ℝ)^(1 : ℤ) := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have h1 : (2 : ℝ)^(1 : ℤ) = 2 := by norm_num
    rw [h, h1]; ring
  -- x < 2^(e+1).
  have h_x_lt_2e1 : x_val < (2 : ℝ)^(e + 1) := by
    rw [hx_def, h_2e1_eq]
    have h_2f2_lt_2e : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^e :=
      zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < e)
    linarith
  -- 2^(e - f₂) as ℤ via n.
  set n : ℕ := (e - f₂).toNat with hn_def
  have h_2e_eq : (2 : ℝ)^e = ((2 : ℤ)^n : ℝ) * (2 : ℝ)^f₂ := two_zpow_split e f₂ hf₂_le_e
  -- Any z ∈ F₂ with z ≤ x satisfies z ≤ 2^e.
  have h_F₂_le_x_to_le_2e : ∀ z ∈ F₂, ((z : Dyadic) : ℝ) ≤ x_val →
      ((z : Dyadic) : ℝ) ≤ (2 : ℝ)^e := by
    intro z hz hz_le
    obtain ⟨_, hq, _⟩ := hz
    rw [hF₂_exp, Dyadic.quantumAtLeast_coe] at hq
    obtain ⟨c, hc⟩ := hq
    rw [hc] at hz_le ⊢
    by_contra h_gt
    push Not at h_gt
    -- c · 2^f₂ > 2^e ⇒ c > 2^(e-f₂) ⇒ c ≥ 2^(e-f₂) + 1 ⇒ c · 2^f₂ ≥ 2^e + 2^f₂ > x.
    rw [h_2e_eq] at h_gt
    have hc_gt : ((2 : ℤ)^n : ℝ) < (c : ℝ) := lt_of_mul_lt_mul_right h_gt h_2f_pos.le
    have hc_int_gt : (2 : ℤ)^n < c := by exact_mod_cast hc_gt
    have hc_int_ge : (2 : ℤ)^n + 1 ≤ c := by omega
    have hc_real_ge : ((2 : ℤ)^n : ℝ) + 1 ≤ (c : ℝ) := by
      have h1 : (((2 : ℤ)^n + 1 : ℤ) : ℝ) ≤ ((c : ℤ) : ℝ) := by exact_mod_cast hc_int_ge
      push_cast at h1; exact h1
    have h_mul : ((2 : ℤ)^n : ℝ) * (2 : ℝ)^f₂ + (2 : ℝ)^f₂ ≤ (c : ℝ) * (2 : ℝ)^f₂ := by
      have h := mul_le_mul_of_nonneg_right hc_real_ge h_2f_pos.le
      linarith [h, show (((2 : ℤ)^n : ℝ) + 1) * (2 : ℝ)^f₂
        = ((2 : ℤ)^n : ℝ) * (2 : ℝ)^f₂ + (2 : ℝ)^f₂ from by ring]
    have h_2f_gt_2f2 : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^f₂ :=
      zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < f₂)
    rw [hx_def] at hz_le
    rw [h_2e_eq] at hz_le
    linarith
  refine ⟨x_val, two_e_g e, two_e_g e, ?_, ?_, ?_⟩
  · refine ⟨h_two_e_in_F₂, ?_, ?_, ?_⟩
    · rw [h_two_e_coe, abs_of_pos h_2e_pos, abs_of_pos h_x_pos]; linarith
    · rw [h_two_e_coe]; positivity
    · intro z hz hz_bnd hz_sign
      have h_z_nn : 0 ≤ ((z : Dyadic) : ℝ) := by
        rcases le_or_gt 0 ((z : Dyadic) : ℝ) with h | h
        · exact h
        · exfalso; nlinarith
      rw [abs_of_nonneg h_z_nn, abs_of_pos h_x_pos] at hz_bnd
      rw [h_two_e_coe, abs_of_pos h_2e_pos, abs_of_nonneg h_z_nn]
      exact h_F₂_le_x_to_le_2e z hz hz_bnd
  · refine ⟨h_two_e_in_F₁, ?_, ?_, ?_⟩
    · rfl
    · change ((two_e_g e : Dyadic) : ℝ) * ((two_e_g e : Dyadic) : ℝ) ≥ 0
      rw [h_two_e_coe]; positivity
    · intro v _ hv_bnd _
      exact hv_bnd
  · -- Bound clause |x| ≤ |2^e| fails: x > 2^e, both positive.
    intro hr
    obtain ⟨_, h_bnd, _, _⟩ := hr
    rw [h_two_e_coe, abs_of_pos h_x_pos, abs_of_pos h_2e_pos] at h_bnd
    linarith

/-- **Counterexample to `rndRAZ_RTZ`.**

For any `F₂` with finite quantum `f₂ ≤ e` (forced by `F₁_g ⊆ F₂`), the
witness `x = 2^e − 2^(f₂ − 2)` lies just below the F₁-element `2^e`
and strictly above F₂'s grid point `2^e − 2^f₂`. F₂-RAZ rounds away
from zero (here, up) to `2^e`; F₁-RTZ on `2^e` returns `2^e`; but
direct F₁-RTZ on the positive `x < 2^e` truncates *down* to `0` (the
largest F₁-element of magnitude ≤ x with the same sign). -/
theorem no_rndRAZ_RTZ
    (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ)
    (F₂ : AbstractFormat) (hsub : F₁_g p hp_ge_2 e ⊆ F₂)
    (hF₂_exp_fin : F₂.exp ≠ ⊥) :
    ∃ (x : ℝ) (z w : Dyadic),
      Rounds F₂ .AwayZero x z ∧
      Rounds (F₁_g p hp_ge_2 e) .ToZero (z : ℝ) w ∧
      ¬ Rounds (F₁_g p hp_ge_2 e) .ToZero x w := by
  obtain ⟨f₂, hf₂_eq⟩ := WithBot.ne_bot_iff_exists.mp hF₂_exp_fin
  have hF₂_exp : F₂.exp = (f₂ : WithBot ℤ) := hf₂_eq.symm
  have h_two_e_in_F₁ := two_e_mem_F₁_g p hp_ge_2 e
  have h_two_e_in_F₂ : two_e_g e ∈ F₂ := hsub _ h_two_e_in_F₁
  have hf₂_le_e : f₂ ≤ e := f₂_le_e_of_F₁_g_subset p hp_ge_2 e F₂ hsub hF₂_exp
  set x_val : ℝ := (2 : ℝ)^e - (2 : ℝ)^(f₂ - 2) with hx_def
  have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
  have h_2f2_pos : (0 : ℝ) < (2 : ℝ)^(f₂ - 2) := zpow_pos (by norm_num) _
  have h_2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
  have h_2f2_lt_2e : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^e :=
    zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < e)
  have h_x_pos : 0 < x_val := by rw [hx_def]; linarith
  have h_x_lt_2e : x_val < (2 : ℝ)^e := by rw [hx_def]; linarith
  have h_two_e_coe := coe_two_e_g e
  set n : ℕ := (e - f₂).toNat with hn_def
  have h_2e_eq : (2 : ℝ)^e = ((2 : ℤ)^n : ℝ) * (2 : ℝ)^f₂ := two_zpow_split e f₂ hf₂_le_e
  -- Any z ∈ F₂ with z < 2^e satisfies z ≤ 2^e − 2^f₂ (the f₂-quantum predecessor).
  have h_F₂_lt_2e_bound : ∀ z ∈ F₂, ((z : Dyadic) : ℝ) < (2 : ℝ)^e →
      ((z : Dyadic) : ℝ) ≤ (2 : ℝ)^e - (2 : ℝ)^f₂ := by
    intro z hz hz_lt
    obtain ⟨_, hq, _⟩ := hz
    rw [hF₂_exp, Dyadic.quantumAtLeast_coe] at hq
    obtain ⟨c, hc⟩ := hq
    rw [hc] at hz_lt ⊢
    have h_mul_bnd : ((c : ℝ) + 1) * (2 : ℝ)^f₂ ≤ (2 : ℝ)^e := by
      rw [h_2e_eq] at hz_lt
      have hc_lt : (c : ℝ) < ((2 : ℤ)^n : ℝ) :=
        lt_of_mul_lt_mul_right hz_lt h_2f_pos.le
      have hc_int_lt : c < (2 : ℤ)^n := by exact_mod_cast hc_lt
      have hc_int_le : c + 1 ≤ (2 : ℤ)^n := by omega
      have hc_real_le : (c : ℝ) + 1 ≤ ((2 : ℤ)^n : ℝ) := by exact_mod_cast hc_int_le
      have h_mul : ((c : ℝ) + 1) * (2 : ℝ)^f₂ ≤ ((2 : ℤ)^n : ℝ) * (2 : ℝ)^f₂ :=
        mul_le_mul_of_nonneg_right hc_real_le h_2f_pos.le
      rw [← h_2e_eq] at h_mul; exact h_mul
    linarith
  refine ⟨x_val, two_e_g e, two_e_g e, ?_, ?_, ?_⟩
  · refine ⟨h_two_e_in_F₂, ?_, ?_, ?_⟩
    · rw [h_two_e_coe, abs_of_pos h_2e_pos, abs_of_pos h_x_pos]; linarith
    · rw [h_two_e_coe]; positivity
    · intro z hz hz_bnd hz_sign
      have h_z_nn : 0 ≤ ((z : Dyadic) : ℝ) := by
        rcases le_or_gt 0 ((z : Dyadic) : ℝ) with h | h
        · exact h
        · exfalso; nlinarith
      rw [abs_of_nonneg h_z_nn, abs_of_pos h_x_pos] at hz_bnd
      rw [h_two_e_coe, abs_of_pos h_2e_pos, abs_of_nonneg h_z_nn]
      -- z ≥ x > 2^e − 2^f₂, so z ≥ 2^e (no F₂-grid point between).
      by_contra h_lt
      push Not at h_lt
      have h_z_pred := h_F₂_lt_2e_bound z hz h_lt
      have h_2f2_lt_2f : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^f₂ :=
        zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < f₂)
      rw [hx_def] at hz_bnd
      linarith
  · refine ⟨h_two_e_in_F₁, ?_, ?_, ?_⟩
    · rfl
    · exact mul_self_nonneg _
    · intro v _ hv_bnd _
      exact hv_bnd
  · -- Bound clause |2^e| ≤ |x| fails: x < 2^e, both positive.
    intro hr
    obtain ⟨_, h_bnd, _, _⟩ := hr
    rw [h_two_e_coe, abs_of_pos h_2e_pos, abs_of_pos h_x_pos] at h_bnd
    linarith

/-- **Counterexample to `rndRAZ_RTO`.**

For any `F₂` with finite quantum `f₂ ≤ e` (forced by `F₁_g ⊆ F₂`), the
witness `x = 4·2^e − 2^(f₂ − 2)` lies just below the F₁-element
`y_hi = 4·2^e`, inside F₂'s upper Voronoi cell of `y_hi`. F₂-RAZ
rounds *up* to `y_hi`; F₁-RTO on `y_hi` keeps it (`y_hi ∈ F₁`, so the
parity constraint is vacuous). But direct F₁-RTO on `x` cannot
return `y_hi`: `x ≠ y_hi` would force `IsOdd F₁ y_hi`, contradicting
`IsEven F₁ y_hi` (canonical significand `1` is at precision `1`,
which is strictly below `numDigits = min p 3`, so `y_hi` cannot have
an odd-significand representation at the rounding precision). -/
theorem no_rndRAZ_RTO
    (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ)
    (F₂ : AbstractFormat) (hsub : F₁_g p hp_ge_2 e ⊆ F₂)
    (hF₂_exp_fin : F₂.exp ≠ ⊥) :
    ∃ (x : ℝ) (z w : Dyadic),
      Rounds F₂ .AwayZero x z ∧
      Rounds (F₁_g p hp_ge_2 e) .ToOdd (z : ℝ) w ∧
      ¬ Rounds (F₁_g p hp_ge_2 e) .ToOdd x w := by
  obtain ⟨f₂, hf₂_eq⟩ := WithBot.ne_bot_iff_exists.mp hF₂_exp_fin
  have hF₂_exp : F₂.exp = (f₂ : WithBot ℤ) := hf₂_eq.symm
  have h_y_hi_in_F₁ := y_hi_mem_F₁_g p hp_ge_2 e
  have h_y_hi_in_F₂ : y_hi_g e ∈ F₂ := hsub _ h_y_hi_in_F₁
  have hf₂_le_e : f₂ ≤ e := f₂_le_e_of_F₁_g_subset p hp_ge_2 e F₂ hsub hF₂_exp
  have hf₂_le_e2 : f₂ ≤ e + 2 := by omega
  set x_val : ℝ := (2 : ℝ)^(e + 2) - (2 : ℝ)^(f₂ - 2) with hx_def
  have h_2e2_pos : (0 : ℝ) < (2 : ℝ)^(e + 2) := zpow_pos (by norm_num) _
  have h_2f2_pos : (0 : ℝ) < (2 : ℝ)^(f₂ - 2) := zpow_pos (by norm_num) _
  have h_2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
  have h_2f2_lt_2e2 : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^(e + 2) :=
    zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < e + 2)
  have h_x_pos : 0 < x_val := by rw [hx_def]; linarith
  have h_x_lt_y_hi : x_val < (2 : ℝ)^(e + 2) := by rw [hx_def]; linarith
  have h_y_hi_coe : ((y_hi_g e : Dyadic) : ℝ) = (2 : ℝ)^(e + 2) := coe_y_hi_g e
  set n : ℕ := (e + 2 - f₂).toNat with hn_def
  have h_2e2_eq : (2 : ℝ)^(e + 2) = ((2 : ℤ)^n : ℝ) * (2 : ℝ)^f₂ :=
    two_zpow_split (e + 2) f₂ hf₂_le_e2
  -- Any z ∈ F₂ with z < y_hi = 2^(e+2) satisfies z ≤ y_hi − 2^f₂.
  have h_F₂_lt_y_hi_bound : ∀ z ∈ F₂, ((z : Dyadic) : ℝ) < (2 : ℝ)^(e + 2) →
      ((z : Dyadic) : ℝ) ≤ (2 : ℝ)^(e + 2) - (2 : ℝ)^f₂ := by
    intro z hz hz_lt
    obtain ⟨_, hq, _⟩ := hz
    rw [hF₂_exp, Dyadic.quantumAtLeast_coe] at hq
    obtain ⟨c, hc⟩ := hq
    rw [hc] at hz_lt ⊢
    have h_mul_bnd : ((c : ℝ) + 1) * (2 : ℝ)^f₂ ≤ (2 : ℝ)^(e + 2) := by
      rw [h_2e2_eq] at hz_lt
      have hc_lt : (c : ℝ) < ((2 : ℤ)^n : ℝ) :=
        lt_of_mul_lt_mul_right hz_lt h_2f_pos.le
      have hc_int_lt : c < (2 : ℤ)^n := by exact_mod_cast hc_lt
      have hc_int_le : c + 1 ≤ (2 : ℤ)^n := by omega
      have hc_real_le : (c : ℝ) + 1 ≤ ((2 : ℤ)^n : ℝ) := by exact_mod_cast hc_int_le
      have h_mul : ((c : ℝ) + 1) * (2 : ℝ)^f₂ ≤ ((2 : ℤ)^n : ℝ) * (2 : ℝ)^f₂ :=
        mul_le_mul_of_nonneg_right hc_real_le h_2f_pos.le
      rw [← h_2e2_eq] at h_mul; exact h_mul
    linarith
  refine ⟨x_val, y_hi_g e, y_hi_g e, ?_, ?_, ?_⟩
  · refine ⟨h_y_hi_in_F₂, ?_, ?_, ?_⟩
    · rw [h_y_hi_coe, abs_of_pos h_2e2_pos, abs_of_pos h_x_pos]; linarith
    · rw [h_y_hi_coe]; positivity
    · intro z hz hz_bnd hz_sign
      have h_z_nn : 0 ≤ ((z : Dyadic) : ℝ) := by
        rcases le_or_gt 0 ((z : Dyadic) : ℝ) with h | h
        · exact h
        · exfalso; nlinarith
      rw [abs_of_nonneg h_z_nn, abs_of_pos h_x_pos] at hz_bnd
      rw [h_y_hi_coe, abs_of_pos h_2e2_pos, abs_of_nonneg h_z_nn]
      -- z ≥ x > y_hi − 2^f₂, so z ≥ y_hi (no F₂-grid point between).
      by_contra h_lt
      push Not at h_lt
      have h_z_pred := h_F₂_lt_y_hi_bound z hz h_lt
      have h_2f2_lt_2f : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^f₂ :=
        zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < f₂)
      rw [hx_def] at hz_bnd
      linarith
  · -- Rounds F₁ RTO y_hi y_hi: y_hi ∈ F₁ and the parity clause is vacuous (x = y).
    refine ⟨h_y_hi_in_F₁, ?_, ?_⟩
    · left
      refine ⟨h_y_hi_in_F₁, le_refl _, ?_⟩
      intro z _ hz_le; exact hz_le
    · intro h_ne; exfalso; exact h_ne rfl
  · -- F₁-RTO at x ≠ y_hi would require IsOdd F₁ y_hi, but y_hi is IsEven, ruled out
    -- by the precisionAtMost-vs-numDigits gap (`precisionAtMost_not_IsOdd`).
    intro hr
    obtain ⟨_, _, h_parity⟩ := hr
    have h_x_ne_y_hi : x_val ≠ ((y_hi_g e : Dyadic) : ℝ) := by
      rw [h_y_hi_coe, hx_def]; linarith
    exact notIsOdd_F₁_g_y_hi p hp_ge_2 e (h_parity h_x_ne_y_hi)

/-- **Counterexample to `rndRNE_RTO`.**

Same witness `x = 4·2^e − 2^(f₂−2)` as `no_rndRAZ_RTO`. F₂-RNE
rounds `x` *up* to `y_hi = 4·2^e` (the upper F₂-Voronoi cell of
`y_hi`, since F₂'s predecessor `y_hi − 2^f₂ < x` and the gap to
`y_hi` is `2^(f₂−2) < 3·2^(f₂−2) ≤` gap to predecessor). F₁-RTO on
`y_hi` keeps it (vacuous parity). Direct F₁-RTO on `x` would force
`IsOdd F₁ y_hi`, contradicting `IsEven`. -/
theorem no_rndRNE_RTO
    (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ)
    (F₂ : AbstractFormat) (hsub : F₁_g p hp_ge_2 e ⊆ F₂)
    (hF₂_exp_fin : F₂.exp ≠ ⊥) :
    ∃ (x : ℝ) (z w : Dyadic),
      Rounds F₂ (.Nearest .ToEven) x z ∧
      Rounds (F₁_g p hp_ge_2 e) .ToOdd (z : ℝ) w ∧
      ¬ Rounds (F₁_g p hp_ge_2 e) .ToOdd x w := by
  obtain ⟨f₂, hf₂_eq⟩ := WithBot.ne_bot_iff_exists.mp hF₂_exp_fin
  have hF₂_exp : F₂.exp = (f₂ : WithBot ℤ) := hf₂_eq.symm
  have h_y_hi_in_F₁ := y_hi_mem_F₁_g p hp_ge_2 e
  have h_y_hi_in_F₂ : y_hi_g e ∈ F₂ := hsub _ h_y_hi_in_F₁
  have hf₂_le_e : f₂ ≤ e := f₂_le_e_of_F₁_g_subset p hp_ge_2 e F₂ hsub hF₂_exp
  have hf₂_le_e2 : f₂ ≤ e + 2 := by omega
  set x_val : ℝ := (2 : ℝ)^(e + 2) - (2 : ℝ)^(f₂ - 2) with hx_def
  have h_2e2_pos : (0 : ℝ) < (2 : ℝ)^(e + 2) := zpow_pos (by norm_num) _
  have h_2f2_pos : (0 : ℝ) < (2 : ℝ)^(f₂ - 2) := zpow_pos (by norm_num) _
  have h_2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
  have h_2f2_lt_2e2 : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^(e + 2) :=
    zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < e + 2)
  have h_x_pos : 0 < x_val := by rw [hx_def]; linarith
  have h_x_lt_y_hi : x_val < (2 : ℝ)^(e + 2) := by rw [hx_def]; linarith
  have h_y_hi_coe : ((y_hi_g e : Dyadic) : ℝ) = (2 : ℝ)^(e + 2) := coe_y_hi_g e
  set n : ℕ := (e + 2 - f₂).toNat with hn_def
  have h_2e2_eq : (2 : ℝ)^(e + 2) = ((2 : ℤ)^n : ℝ) * (2 : ℝ)^f₂ :=
    two_zpow_split (e + 2) f₂ hf₂_le_e2
  have h_2f_split : (2 : ℝ)^f₂ = 4 * (2 : ℝ)^(f₂ - 2) := by
    have h_eq : (2 : ℝ)^f₂ = (2 : ℝ)^(f₂ - 2) * (2 : ℝ)^(2 : ℤ) := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
    rw [h_eq, show (2 : ℝ)^(2 : ℤ) = 4 by norm_num]; ring
  have h_F₂_lt_y_hi_bound : ∀ z ∈ F₂, ((z : Dyadic) : ℝ) < (2 : ℝ)^(e + 2) →
      ((z : Dyadic) : ℝ) ≤ (2 : ℝ)^(e + 2) - (2 : ℝ)^f₂ := by
    intro z hz hz_lt
    obtain ⟨_, hq, _⟩ := hz
    rw [hF₂_exp, Dyadic.quantumAtLeast_coe] at hq
    obtain ⟨c, hc⟩ := hq
    rw [hc] at hz_lt ⊢
    have h_mul_bnd : ((c : ℝ) + 1) * (2 : ℝ)^f₂ ≤ (2 : ℝ)^(e + 2) := by
      rw [h_2e2_eq] at hz_lt
      have hc_lt : (c : ℝ) < ((2 : ℤ)^n : ℝ) :=
        lt_of_mul_lt_mul_right hz_lt h_2f_pos.le
      have hc_int_lt : c < (2 : ℤ)^n := by exact_mod_cast hc_lt
      have hc_int_le : c + 1 ≤ (2 : ℤ)^n := by omega
      have hc_real_le : (c : ℝ) + 1 ≤ ((2 : ℤ)^n : ℝ) := by exact_mod_cast hc_int_le
      have h_mul : ((c : ℝ) + 1) * (2 : ℝ)^f₂ ≤ ((2 : ℤ)^n : ℝ) * (2 : ℝ)^f₂ :=
        mul_le_mul_of_nonneg_right hc_real_le h_2f_pos.le
      rw [← h_2e2_eq] at h_mul; exact h_mul
    linarith
  have h_F₂_ge_x_to_ge_y_hi : ∀ z ∈ F₂, x_val ≤ ((z : Dyadic) : ℝ) →
      (2 : ℝ)^(e + 2) ≤ ((z : Dyadic) : ℝ) := by
    intro z hz hz_ge
    by_contra h_lt
    push Not at h_lt
    have h_z_bnd := h_F₂_lt_y_hi_bound z hz h_lt
    have h_2f2_lt_2f : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^f₂ :=
      zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < f₂)
    linarith
  refine ⟨x_val, y_hi_g e, y_hi_g e, ?_, ?_, ?_⟩
  · refine ⟨h_y_hi_in_F₂, ?_, ?_, ?_⟩
    · -- IsFaithfulRound (RoundUp y_hi).
      right
      refine ⟨h_y_hi_in_F₂, ?_, ?_⟩
      · rw [h_y_hi_coe]; linarith
      · intro z hz hz_ge
        rw [h_y_hi_coe]
        exact h_F₂_ge_x_to_ge_y_hi z hz hz_ge
    · -- Closeness.
      intro z hz hf
      rw [h_y_hi_coe]
      rcases hf with ⟨_, hz_le, _⟩ | ⟨_, hz_ge, _⟩
      · have h_z_lt_y_hi : (z : ℝ) < (2 : ℝ)^(e + 2) := lt_of_le_of_lt hz_le h_x_lt_y_hi
        have h_z_bnd := h_F₂_lt_y_hi_bound z hz h_z_lt_y_hi
        rw [abs_of_neg (by rw [hx_def]; linarith : x_val - (2 : ℝ)^(e + 2) < 0), neg_sub]
        rw [abs_of_nonneg (by rw [hx_def]; linarith : (0 : ℝ) ≤ x_val - (z : ℝ))]
        rw [h_2f_split] at h_z_bnd
        rw [hx_def]; linarith
      · have h_z_ge_y_hi := h_F₂_ge_x_to_ge_y_hi z hz hz_ge
        rw [abs_of_neg (by rw [hx_def]; linarith : x_val - (2 : ℝ)^(e + 2) < 0), neg_sub]
        rw [abs_of_nonpos (by linarith : x_val - (z : ℝ) ≤ 0), neg_sub]
        linarith
    · -- No tie.
      rintro ⟨z, hzF₂, hf, hne, heq⟩
      rw [h_y_hi_coe] at heq
      rcases hf with ⟨_, hz_le, _⟩ | ⟨_, hz_ge, _⟩
      · exfalso
        have h_z_lt_y_hi : (z : ℝ) < (2 : ℝ)^(e + 2) := lt_of_le_of_lt hz_le h_x_lt_y_hi
        have h_z_bnd := h_F₂_lt_y_hi_bound z hzF₂ h_z_lt_y_hi
        rw [abs_of_neg (by rw [hx_def]; linarith : x_val - (2 : ℝ)^(e + 2) < 0), neg_sub] at heq
        rw [abs_of_nonneg (by rw [hx_def]; linarith : (0 : ℝ) ≤ x_val - (z : ℝ))] at heq
        rw [h_2f_split] at h_z_bnd
        rw [hx_def] at heq
        linarith
      · exfalso
        have h_z_ge_y_hi := h_F₂_ge_x_to_ge_y_hi z hzF₂ hz_ge
        have h_z_ne_y_hi : (z : ℝ) ≠ (2 : ℝ)^(e + 2) := by
          intro h_eq
          apply hne
          apply Subtype.ext
          rw [h_y_hi_coe]; exact h_eq
        have h_z_gt_y_hi : (2 : ℝ)^(e + 2) < (z : ℝ) :=
          lt_of_le_of_ne h_z_ge_y_hi (Ne.symm h_z_ne_y_hi)
        have h_z_ge_y_hi_plus : (2 : ℝ)^(e + 2) + (2 : ℝ)^f₂ ≤ (z : ℝ) := by
          obtain ⟨_, hq, _⟩ := hzF₂
          rw [hF₂_exp, Dyadic.quantumAtLeast_coe] at hq
          obtain ⟨c, hc⟩ := hq
          rw [hc] at h_z_gt_y_hi ⊢
          rw [h_2e2_eq] at h_z_gt_y_hi
          have hc_gt : ((2 : ℤ)^n : ℝ) < (c : ℝ) :=
            lt_of_mul_lt_mul_right h_z_gt_y_hi h_2f_pos.le
          have hc_int_gt : (2 : ℤ)^n < c := by exact_mod_cast hc_gt
          have hc_int_ge : (2 : ℤ)^n + 1 ≤ c := by omega
          have hc_real_ge : ((2 : ℤ)^n : ℝ) + 1 ≤ (c : ℝ) := by
            have h1 : (((2 : ℤ)^n + 1 : ℤ) : ℝ) ≤ ((c : ℤ) : ℝ) := by exact_mod_cast hc_int_ge
            push_cast at h1; exact h1
          have h_mul : (((2 : ℤ)^n : ℝ) + 1) * (2 : ℝ)^f₂ ≤ (c : ℝ) * (2 : ℝ)^f₂ :=
            mul_le_mul_of_nonneg_right hc_real_ge h_2f_pos.le
          rw [h_2e2_eq]
          linarith
        rw [abs_of_neg (by rw [hx_def]; linarith : x_val - (2 : ℝ)^(e + 2) < 0), neg_sub] at heq
        rw [abs_of_nonpos (by linarith : x_val - (z : ℝ) ≤ 0), neg_sub] at heq
        rw [hx_def] at heq; linarith
  · refine ⟨h_y_hi_in_F₁, ?_, ?_⟩
    · left
      refine ⟨h_y_hi_in_F₁, le_refl _, ?_⟩
      intro z _ hz_le; exact hz_le
    · intro h_ne; exfalso; exact h_ne rfl
  · intro hr
    obtain ⟨_, _, h_parity⟩ := hr
    have h_x_ne_y_hi : x_val ≠ ((y_hi_g e : Dyadic) : ℝ) := by
      rw [h_y_hi_coe, hx_def]; linarith
    exact notIsOdd_F₁_g_y_hi p hp_ge_2 e (h_parity h_x_ne_y_hi)

/-- **Counterexample to `rndRTZ_RTO`.**

Witness `x = 4·2^e + 2^(f₂−2)` lies just above the F₁-element
`y_hi = 4·2^e`, inside F₂'s downward-truncation zone for `y_hi`
(F₂'s next grid point above `y_hi` is `y_hi + 2^f₂ > x`). F₂-RTZ
truncates `x` *down* to `y_hi`; F₁-RTO on `y_hi` keeps it (vacuous
parity). But direct F₁-RTO on `x` would force `IsOdd F₁ y_hi`,
contradicting `IsEven`. -/
theorem no_rndRTZ_RTO
    (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ)
    (F₂ : AbstractFormat) (hsub : F₁_g p hp_ge_2 e ⊆ F₂)
    (hF₂_exp_fin : F₂.exp ≠ ⊥) :
    ∃ (x : ℝ) (z w : Dyadic),
      Rounds F₂ .ToZero x z ∧
      Rounds (F₁_g p hp_ge_2 e) .ToOdd (z : ℝ) w ∧
      ¬ Rounds (F₁_g p hp_ge_2 e) .ToOdd x w := by
  obtain ⟨f₂, hf₂_eq⟩ := WithBot.ne_bot_iff_exists.mp hF₂_exp_fin
  have hF₂_exp : F₂.exp = (f₂ : WithBot ℤ) := hf₂_eq.symm
  have h_y_hi_in_F₁ := y_hi_mem_F₁_g p hp_ge_2 e
  have h_y_hi_in_F₂ : y_hi_g e ∈ F₂ := hsub _ h_y_hi_in_F₁
  have hf₂_le_e : f₂ ≤ e := f₂_le_e_of_F₁_g_subset p hp_ge_2 e F₂ hsub hF₂_exp
  have hf₂_le_e2 : f₂ ≤ e + 2 := by omega
  set x_val : ℝ := (2 : ℝ)^(e + 2) + (2 : ℝ)^(f₂ - 2) with hx_def
  have h_2e2_pos : (0 : ℝ) < (2 : ℝ)^(e + 2) := zpow_pos (by norm_num) _
  have h_2f2_pos : (0 : ℝ) < (2 : ℝ)^(f₂ - 2) := zpow_pos (by norm_num) _
  have h_2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
  have h_x_pos : 0 < x_val := by rw [hx_def]; linarith
  have h_x_gt_y_hi : (2 : ℝ)^(e + 2) < x_val := by rw [hx_def]; linarith
  have h_y_hi_coe : ((y_hi_g e : Dyadic) : ℝ) = (2 : ℝ)^(e + 2) := coe_y_hi_g e
  set n : ℕ := (e + 2 - f₂).toNat with hn_def
  have h_2e2_eq : (2 : ℝ)^(e + 2) = ((2 : ℤ)^n : ℝ) * (2 : ℝ)^f₂ :=
    two_zpow_split (e + 2) f₂ hf₂_le_e2
  -- Any z ∈ F₂ with z ≤ x has z ≤ y_hi (no F₂ grid point strictly between y_hi and x).
  have h_F₂_le_x_to_le_y_hi : ∀ z ∈ F₂, ((z : Dyadic) : ℝ) ≤ x_val →
      ((z : Dyadic) : ℝ) ≤ (2 : ℝ)^(e + 2) := by
    intro z hz hz_le
    obtain ⟨_, hq, _⟩ := hz
    rw [hF₂_exp, Dyadic.quantumAtLeast_coe] at hq
    obtain ⟨c, hc⟩ := hq
    rw [hc] at hz_le ⊢
    by_contra h_gt
    push Not at h_gt
    rw [h_2e2_eq] at h_gt
    have hc_gt : ((2 : ℤ)^n : ℝ) < (c : ℝ) :=
      lt_of_mul_lt_mul_right h_gt h_2f_pos.le
    have hc_int_gt : (2 : ℤ)^n < c := by exact_mod_cast hc_gt
    have hc_int_ge : (2 : ℤ)^n + 1 ≤ c := by omega
    have hc_real_ge : ((2 : ℤ)^n : ℝ) + 1 ≤ (c : ℝ) := by
      have h1 : (((2 : ℤ)^n + 1 : ℤ) : ℝ) ≤ ((c : ℤ) : ℝ) := by exact_mod_cast hc_int_ge
      push_cast at h1; exact h1
    have h_mul : (((2 : ℤ)^n : ℝ) + 1) * (2 : ℝ)^f₂ ≤ (c : ℝ) * (2 : ℝ)^f₂ :=
      mul_le_mul_of_nonneg_right hc_real_ge h_2f_pos.le
    have h_2f2_lt_2f : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^f₂ :=
      zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < f₂)
    rw [hx_def, h_2e2_eq] at hz_le
    linarith
  refine ⟨x_val, y_hi_g e, y_hi_g e, ?_, ?_, ?_⟩
  · refine ⟨h_y_hi_in_F₂, ?_, ?_, ?_⟩
    · rw [h_y_hi_coe, abs_of_pos h_2e2_pos, abs_of_pos h_x_pos]; linarith
    · rw [h_y_hi_coe]; positivity
    · intro z hz hz_bnd hz_sign
      have h_z_nn : 0 ≤ ((z : Dyadic) : ℝ) := by
        rcases le_or_gt 0 ((z : Dyadic) : ℝ) with h | h
        · exact h
        · exfalso; nlinarith
      rw [abs_of_nonneg h_z_nn, abs_of_pos h_x_pos] at hz_bnd
      rw [h_y_hi_coe, abs_of_pos h_2e2_pos, abs_of_nonneg h_z_nn]
      exact h_F₂_le_x_to_le_y_hi z hz hz_bnd
  · refine ⟨h_y_hi_in_F₁, ?_, ?_⟩
    · left
      refine ⟨h_y_hi_in_F₁, le_refl _, ?_⟩
      intro z _ hz_le; exact hz_le
    · intro h_ne; exfalso; exact h_ne rfl
  · intro hr
    obtain ⟨_, _, h_parity⟩ := hr
    have h_x_ne_y_hi : x_val ≠ ((y_hi_g e : Dyadic) : ℝ) := by
      rw [h_y_hi_coe, hx_def]; linarith
    exact notIsOdd_F₁_g_y_hi p hp_ge_2 e (h_parity h_x_ne_y_hi)

/-- **Counterexample to `rndRAZ_RNE`.**

Requires `m_g e = 7·2^(e−1) ∈ F₂` (the F₁-midpoint between `y_lo` and
`y_hi`; it has quantum `e−1`, so it is *not* in `F₁_g`, and the
hypothesis `hsub : F₁_g ⊆ F₂` alone does not place it in `F₂`).
Witness `x = m − 2^(f₂−2)` lies just below `m`, inside F₂'s upper
Voronoi cell of `m` (F₂'s predecessor `m − 2^f₂ < x`). F₂-RAZ rounds
*up* to `m`. F₁-RNE at the midpoint breaks the tie to the even
neighbor `y_hi = 4·2^e`. But direct F₁-RNE on `x` is closer to
`y_lo = 3·2^e` (distance `2^(e−1) − 2^(f₂−2)`) than to `y_hi`
(distance `2^(e−1) + 2^(f₂−2)`), so direct F₁-RNE returns `y_lo`. -/
theorem no_rndRAZ_RNE
    (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ)
    (F₂ : AbstractFormat) (hm_in_F₂ : m_g e ∈ F₂)
    (hF₂_exp_fin : F₂.exp ≠ ⊥) :
    ∃ (x : ℝ) (z w : Dyadic),
      Rounds F₂ .AwayZero x z ∧
      Rounds (F₁_g p hp_ge_2 e) (.Nearest .ToEven) (z : ℝ) w ∧
      ¬ Rounds (F₁_g p hp_ge_2 e) (.Nearest .ToEven) x w := by
  obtain ⟨f₂, hf₂_eq⟩ := WithBot.ne_bot_iff_exists.mp hF₂_exp_fin
  have hF₂_exp : F₂.exp = (f₂ : WithBot ℤ) := hf₂_eq.symm
  -- m has quantum e - 1, so m ∈ F₂ forces f₂ ≤ e - 1.
  have hf₂_le_e1 : f₂ ≤ e - 1 := by
    obtain ⟨_, hq, _⟩ := hm_in_F₂
    rw [hF₂_exp, Dyadic.quantumAtLeast_coe] at hq
    obtain ⟨c, hc⟩ := hq
    have h_m_coe : ((m_g e : Dyadic) : ℝ) = 7 * (2 : ℝ)^(e - 1) := coe_m_g e
    -- 7·2^(e-1) = c·2^f₂. If f₂ > e - 1, divide both sides by 2^(e-1) to get
    -- 7 = c·2^(f₂-(e-1)) with positive exponent, forcing c even, but 7 odd.
    by_contra h_gt
    push Not at h_gt
    rw [h_m_coe] at hc
    set k : ℕ := (f₂ - (e - 1)).toNat with hk_def
    have h_kn : (k : ℤ) = f₂ - (e - 1) := Int.toNat_of_nonneg (by omega)
    have h_k_pos : 1 ≤ k := by
      have : (1 : ℤ) ≤ (k : ℤ) := by rw [h_kn]; omega
      exact_mod_cast this
    have h_2e1_ne : (2 : ℝ)^(e - 1) ≠ 0 := ne_of_gt (zpow_pos (by norm_num) _)
    have h_split : (2 : ℝ)^f₂ = (2 : ℝ)^(k : ℤ) * (2 : ℝ)^(e - 1) := by
      rw [show (f₂ : ℤ) = (k : ℤ) + (e - 1) from by linarith [h_kn],
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [h_split, ← mul_assoc, zpow_natCast] at hc
    have h_eq : (7 : ℝ) = (c : ℝ) * (2 : ℝ)^k :=
      mul_right_cancel₀ h_2e1_ne hc
    have h_int : (7 : ℤ) = c * (2 : ℤ)^k := by
      have h1 : ((7 : ℤ) : ℝ) = ((c * (2 : ℤ)^k : ℤ) : ℝ) := by
        push_cast; exact h_eq
      exact_mod_cast h1
    have h_even : Even (7 : ℤ) := by
      rw [h_int, show k = (k - 1) + 1 from by omega, pow_succ]
      refine ⟨c * 2^(k - 1), ?_⟩; ring
    exact (Int.not_even_iff_odd.mpr (by decide : Odd (7 : ℤ))) h_even
  have h_y_lo_in_F₁ := y_lo_mem_F₁_g p hp_ge_2 e
  have h_y_hi_in_F₁ := y_hi_mem_F₁_g p hp_ge_2 e
  set m : Dyadic := m_g e with hm_def
  have h_m_in_F₂ : m ∈ F₂ := hm_in_F₂
  have h_m_coe : (m : ℝ) = 7 * (2 : ℝ)^(e - 1) := coe_m_g e
  have h_2e1_pos : (0 : ℝ) < (2 : ℝ)^(e - 1) := zpow_pos (by norm_num) _
  have h_m_pos : 0 < (m : ℝ) := by rw [h_m_coe]; nlinarith
  -- Setup remaining quantities.
  set x_val : ℝ := (m : ℝ) - (2 : ℝ)^(f₂ - 2) with hx_def
  have h_2f2_pos : (0 : ℝ) < (2 : ℝ)^(f₂ - 2) := zpow_pos (by norm_num) _
  have h_2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
  have h_2f2_lt_2e1 : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^(e - 1) :=
    zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < e - 1)
  have h_2f2_lt_2f : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^f₂ :=
    zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < f₂)
  have h_x_lt_m : x_val < (m : ℝ) := by rw [hx_def]; linarith
  have h_x_pos : 0 < x_val := by
    rw [hx_def, h_m_coe]; nlinarith
  -- f₂-quantum grid: m = 7·2^(e-1-f₂) · 2^f₂.
  set n : ℕ := (e - 1 - f₂).toNat with hn_def
  have h_m_grid : (m : ℝ) = ((7 * (2 : ℤ)^n : ℤ) : ℝ) * (2 : ℝ)^f₂ := by
    have h_split : (2 : ℝ)^(e - 1) = ((2 : ℤ)^n : ℝ) * (2 : ℝ)^f₂ :=
      two_zpow_split (e - 1) f₂ hf₂_le_e1
    rw [h_m_coe, h_split]; push_cast; ring
  -- Any z ∈ F₂ with z < m satisfies z ≤ m - 2^f₂.
  have h_F₂_lt_m_bound : ∀ z ∈ F₂, ((z : Dyadic) : ℝ) < (m : ℝ) →
      ((z : Dyadic) : ℝ) ≤ (m : ℝ) - (2 : ℝ)^f₂ := by
    intro z hz hz_lt
    obtain ⟨_, hq, _⟩ := hz
    rw [hF₂_exp, Dyadic.quantumAtLeast_coe] at hq
    obtain ⟨c, hc⟩ := hq
    rw [hc] at hz_lt ⊢
    rw [h_m_grid] at hz_lt
    have hc_lt : (c : ℝ) < ((7 * (2 : ℤ)^n : ℤ) : ℝ) :=
      lt_of_mul_lt_mul_right hz_lt h_2f_pos.le
    have hc_int_lt : c < 7 * (2 : ℤ)^n := by exact_mod_cast hc_lt
    have hc_int_le : c + 1 ≤ 7 * (2 : ℤ)^n := by omega
    have hc_real_le : (c : ℝ) + 1 ≤ ((7 * (2 : ℤ)^n : ℤ) : ℝ) := by
      have h1 : ((c + 1 : ℤ) : ℝ) ≤ ((7 * (2 : ℤ)^n : ℤ) : ℝ) := by exact_mod_cast hc_int_le
      push_cast at h1 ⊢; linarith
    have h_mul : ((c : ℝ) + 1) * (2 : ℝ)^f₂ ≤ ((7 * (2 : ℤ)^n : ℤ) : ℝ) * (2 : ℝ)^f₂ :=
      mul_le_mul_of_nonneg_right hc_real_le h_2f_pos.le
    rw [h_m_grid]
    linarith
  -- y_lo and y_hi relations to m.
  have h_y_lo_coe : ((y_lo_g e : Dyadic) : ℝ) = 3 * (2 : ℝ)^e := coe_y_lo_g e
  have h_y_hi_coe : ((y_hi_g e : Dyadic) : ℝ) = (2 : ℝ)^(e + 2) := coe_y_hi_g e
  have h_y_lo_eq : ((y_lo_g e : Dyadic) : ℝ) = (m : ℝ) - (2 : ℝ)^(e - 1) := by
    rw [h_y_lo_coe, h_m_coe]
    have h_split : (2 : ℝ)^e = (2 : ℝ)^(e - 1) * (2 : ℝ)^(1 : ℤ) := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
    rw [h_split, show (2 : ℝ)^(1 : ℤ) = 2 by norm_num]; ring
  have h_y_hi_eq : ((y_hi_g e : Dyadic) : ℝ) = (m : ℝ) + (2 : ℝ)^(e - 1) := by
    rw [h_y_hi_coe, h_m_coe]
    rw [show e + 2 = (e - 1) + 3 by ring, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [show (2 : ℝ)^(3 : ℤ) = 8 by norm_num]; ring
  refine ⟨x_val, m, y_hi_g e, ?_, ?_, ?_⟩
  · -- Rounds F₂ RAZ x m.
    refine ⟨h_m_in_F₂, ?_, ?_, ?_⟩
    · rw [abs_of_pos h_m_pos, abs_of_pos h_x_pos]; linarith
    · positivity
    · intro z hz hz_bnd hz_sign
      have h_z_nn : 0 ≤ ((z : Dyadic) : ℝ) := by
        rcases le_or_gt 0 ((z : Dyadic) : ℝ) with h | h
        · exact h
        · exfalso; nlinarith
      rw [abs_of_nonneg h_z_nn, abs_of_pos h_x_pos] at hz_bnd
      rw [abs_of_pos h_m_pos, abs_of_nonneg h_z_nn]
      by_contra h_lt
      push Not at h_lt
      have h_z_pred := h_F₂_lt_m_bound z hz h_lt
      rw [hx_def] at hz_bnd
      linarith
  · -- Rounds F₁_g RNE m y_hi.
    exact rounds_F₁_g_RNE_m_y_hi p hp_ge_2 e
  · -- ¬ Rounds F₁_g RNE x y_hi: y_lo is faithful and strictly closer.
    intro hr
    obtain ⟨_, _, h_close, _⟩ := hr
    have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
    have h_y_lo_faith : IsFaithfulRound (F₁_g p hp_ge_2 e) x_val (y_lo_g e) := by
      left
      refine ⟨h_y_lo_in_F₁, ?_, ?_⟩
      · rw [h_y_lo_eq, hx_def]; linarith
      · intro z hz hz_le
        obtain ⟨c', hc'⟩ := F₁_g_quantum p hp_ge_2 e hz
        have h_z_lt_m : (z : ℝ) < (m : ℝ) := lt_of_le_of_lt hz_le h_x_lt_m
        rw [hc', h_m_coe] at h_z_lt_m
        have h_7_2 : (7 : ℝ) * (2 : ℝ)^(e-1) = (7/2) * (2 : ℝ)^e := by
          rw [show (e-1 : ℤ) = e + (-1 : ℤ) from by ring,
              zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          rw [show (2 : ℝ)^(-1 : ℤ) = 1/2 by
            rw [show ((-1 : ℤ)) = -(1 : ℤ) from by ring, zpow_neg]; norm_num]
          ring
        rw [h_7_2] at h_z_lt_m
        have hc'_r_lt : (c' : ℝ) < 7/2 := lt_of_mul_lt_mul_right h_z_lt_m h_2e_pos.le
        have hc'_lt_4 : (c' : ℝ) < 4 := by linarith
        have : c' < 4 := by exact_mod_cast hc'_lt_4
        have hc'_le_3 : c' ≤ 3 := by omega
        change (z : ℝ) ≤ ((y_lo_g e : Dyadic) : ℝ)
        rw [hc', h_y_lo_coe]
        have : (c' : ℝ) ≤ 3 := by exact_mod_cast hc'_le_3
        nlinarith
    have h_close_lo := h_close (y_lo_g e) h_y_lo_in_F₁ h_y_lo_faith
    -- |x − y_hi| = 2^(e−1) + 2^(f₂−2), |x − y_lo| = 2^(e−1) − 2^(f₂−2).
    rw [h_y_hi_eq, h_y_lo_eq, hx_def] at h_close_lo
    have h_abs_hi : |((m : ℝ) - (2 : ℝ)^(f₂ - 2)) - ((m : ℝ) + (2 : ℝ)^(e - 1))| =
        (2 : ℝ)^(e - 1) + (2 : ℝ)^(f₂ - 2) := by
      rw [show (m : ℝ) - (2 : ℝ)^(f₂ - 2) - ((m : ℝ) + (2 : ℝ)^(e - 1)) =
          -((2 : ℝ)^(e - 1) + (2 : ℝ)^(f₂ - 2)) from by ring]
      rw [abs_neg, abs_of_pos (by linarith : 0 < (2 : ℝ)^(e - 1) + (2 : ℝ)^(f₂ - 2))]
    have h_abs_lo : |((m : ℝ) - (2 : ℝ)^(f₂ - 2)) - ((m : ℝ) - (2 : ℝ)^(e - 1))| =
        (2 : ℝ)^(e - 1) - (2 : ℝ)^(f₂ - 2) := by
      rw [show (m : ℝ) - (2 : ℝ)^(f₂ - 2) - ((m : ℝ) - (2 : ℝ)^(e - 1)) =
          (2 : ℝ)^(e - 1) - (2 : ℝ)^(f₂ - 2) from by ring]
      exact abs_of_pos (by linarith)
    rw [h_abs_hi, h_abs_lo] at h_close_lo
    linarith

/-- **Counterexample to `rndRTZ_RNE`.**

Uses the lower-even F-adjacent pair `(y_lo_low, y_lo_g) = (2·2^e,
3·2^e)` and their midpoint `m_low = 5·2^(e−1)`. Requires
`m_low ∈ F₂` (since `m_low ∉ F₁_g`). Witness `x = m_low + 2^(f₂−2)`
lies just above `m_low`, inside F₂'s downward-truncation zone for
`m_low` (F₂'s next grid point above `m_low` is `m_low + 2^f₂ > x`).
F₂-RTZ truncates `x` *down* to `m_low`. F₁-RNE at the midpoint
breaks the tie to the even neighbor `y_lo_low = 2·2^e`. But direct
F₁-RNE on `x` is closer to `y_lo_g = 3·2^e` (distance
`2^(e−1) − 2^(f₂−2)`) than to `y_lo_low` (distance
`2^(e−1) + 2^(f₂−2)`), so direct F₁-RNE returns `y_lo_g`. -/
theorem no_rndRTZ_RNE
    (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ)
    (F₂ : AbstractFormat) (hm_low_in_F₂ : m_low_g e ∈ F₂)
    (hF₂_exp_fin : F₂.exp ≠ ⊥) :
    ∃ (x : ℝ) (z w : Dyadic),
      Rounds F₂ .ToZero x z ∧
      Rounds (F₁_g p hp_ge_2 e) (.Nearest .ToEven) (z : ℝ) w ∧
      ¬ Rounds (F₁_g p hp_ge_2 e) (.Nearest .ToEven) x w := by
  obtain ⟨f₂, hf₂_eq⟩ := WithBot.ne_bot_iff_exists.mp hF₂_exp_fin
  have hF₂_exp : F₂.exp = (f₂ : WithBot ℤ) := hf₂_eq.symm
  -- m_low has quantum e - 1, so m_low ∈ F₂ forces f₂ ≤ e - 1 (same parity argument
  -- as in `no_rndRAZ_RNE`, applied to the odd integer `5`).
  have hf₂_le_e1 : f₂ ≤ e - 1 := by
    obtain ⟨_, hq, _⟩ := hm_low_in_F₂
    rw [hF₂_exp, Dyadic.quantumAtLeast_coe] at hq
    obtain ⟨c, hc⟩ := hq
    have h_m_coe : ((m_low_g e : Dyadic) : ℝ) = 5 * (2 : ℝ)^(e - 1) := coe_m_low_g e
    by_contra h_gt
    push Not at h_gt
    rw [h_m_coe] at hc
    set k : ℕ := (f₂ - (e - 1)).toNat with hk_def
    have h_kn : (k : ℤ) = f₂ - (e - 1) := Int.toNat_of_nonneg (by omega)
    have h_k_pos : 1 ≤ k := by
      have : (1 : ℤ) ≤ (k : ℤ) := by rw [h_kn]; omega
      exact_mod_cast this
    have h_2e1_ne : (2 : ℝ)^(e - 1) ≠ 0 := ne_of_gt (zpow_pos (by norm_num) _)
    have h_split : (2 : ℝ)^f₂ = (2 : ℝ)^(k : ℤ) * (2 : ℝ)^(e - 1) := by
      rw [show (f₂ : ℤ) = (k : ℤ) + (e - 1) from by linarith [h_kn],
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [h_split, ← mul_assoc, zpow_natCast] at hc
    have h_eq : (5 : ℝ) = (c : ℝ) * (2 : ℝ)^k :=
      mul_right_cancel₀ h_2e1_ne hc
    have h_int : (5 : ℤ) = c * (2 : ℤ)^k := by
      have h1 : ((5 : ℤ) : ℝ) = ((c * (2 : ℤ)^k : ℤ) : ℝ) := by push_cast; exact h_eq
      exact_mod_cast h1
    have h_even : Even (5 : ℤ) := by
      rw [h_int, show k = (k - 1) + 1 from by omega, pow_succ]
      refine ⟨c * 2^(k - 1), ?_⟩; ring
    exact (Int.not_even_iff_odd.mpr (by decide : Odd (5 : ℤ))) h_even
  have h_y_lo_low_in_F₁ := y_lo_low_mem_F₁_g p hp_ge_2 e
  have h_y_lo_in_F₁ := y_lo_mem_F₁_g p hp_ge_2 e
  set m_low : Dyadic := m_low_g e with hm_low_def
  have h_m_low_in_F₂ : m_low ∈ F₂ := hm_low_in_F₂
  have h_m_low_coe : (m_low : ℝ) = 5 * (2 : ℝ)^(e - 1) := coe_m_low_g e
  have h_2e1_pos : (0 : ℝ) < (2 : ℝ)^(e - 1) := zpow_pos (by norm_num) _
  have h_m_low_pos : 0 < (m_low : ℝ) := by rw [h_m_low_coe]; nlinarith
  set x_val : ℝ := (m_low : ℝ) + (2 : ℝ)^(f₂ - 2) with hx_def
  have h_2f2_pos : (0 : ℝ) < (2 : ℝ)^(f₂ - 2) := zpow_pos (by norm_num) _
  have h_2f_pos : (0 : ℝ) < (2 : ℝ)^f₂ := zpow_pos (by norm_num) _
  have h_2f2_lt_2e1 : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^(e - 1) :=
    zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < e - 1)
  have h_2f2_lt_2f : (2 : ℝ)^(f₂ - 2) < (2 : ℝ)^f₂ :=
    zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : f₂ - 2 < f₂)
  have h_x_gt_m_low : (m_low : ℝ) < x_val := by rw [hx_def]; linarith
  have h_x_pos : 0 < x_val := by linarith
  -- f₂-quantum grid: m_low = 5·2^(e-1-f₂) · 2^f₂.
  set n : ℕ := (e - 1 - f₂).toNat with hn_def
  have h_m_low_grid : (m_low : ℝ) = ((5 * (2 : ℤ)^n : ℤ) : ℝ) * (2 : ℝ)^f₂ := by
    have h_split : (2 : ℝ)^(e - 1) = ((2 : ℤ)^n : ℝ) * (2 : ℝ)^f₂ :=
      two_zpow_split (e - 1) f₂ hf₂_le_e1
    rw [h_m_low_coe, h_split]; push_cast; ring
  -- Any z ∈ F₂ with z ≤ x has z ≤ m_low (no F₂ grid point strictly between m_low and x).
  have h_F₂_le_x_to_le_m_low : ∀ z ∈ F₂, ((z : Dyadic) : ℝ) ≤ x_val →
      ((z : Dyadic) : ℝ) ≤ (m_low : ℝ) := by
    intro z hz hz_le
    obtain ⟨_, hq, _⟩ := hz
    rw [hF₂_exp, Dyadic.quantumAtLeast_coe] at hq
    obtain ⟨c, hc⟩ := hq
    rw [hc] at hz_le ⊢
    by_contra h_gt
    push Not at h_gt
    rw [h_m_low_grid] at h_gt
    have hc_gt : ((5 * (2 : ℤ)^n : ℤ) : ℝ) < (c : ℝ) :=
      lt_of_mul_lt_mul_right h_gt h_2f_pos.le
    have hc_int_gt : 5 * (2 : ℤ)^n < c := by exact_mod_cast hc_gt
    have hc_int_ge : 5 * (2 : ℤ)^n + 1 ≤ c := by omega
    have hc_real_ge : ((5 * (2 : ℤ)^n : ℤ) : ℝ) + 1 ≤ (c : ℝ) := by
      have h1 : ((5 * (2 : ℤ)^n + 1 : ℤ) : ℝ) ≤ ((c : ℤ) : ℝ) := by exact_mod_cast hc_int_ge
      push_cast at h1 ⊢; linarith
    have h_mul : (((5 * (2 : ℤ)^n : ℤ) : ℝ) + 1) * (2 : ℝ)^f₂ ≤ (c : ℝ) * (2 : ℝ)^f₂ :=
      mul_le_mul_of_nonneg_right hc_real_ge h_2f_pos.le
    rw [hx_def, h_m_low_grid] at hz_le
    linarith
  -- y_lo_low and y_lo_g relations to m_low.
  have h_y_lo_low_coe : ((y_lo_low_g e : Dyadic) : ℝ) = 2 * (2 : ℝ)^e := coe_y_lo_low_g e
  have h_y_lo_coe : ((y_lo_g e : Dyadic) : ℝ) = 3 * (2 : ℝ)^e := coe_y_lo_g e
  have h_y_lo_low_eq : ((y_lo_low_g e : Dyadic) : ℝ) = (m_low : ℝ) - (2 : ℝ)^(e - 1) := by
    rw [h_y_lo_low_coe, h_m_low_coe]
    have h_split : (2 : ℝ)^e = (2 : ℝ)^(e - 1) * (2 : ℝ)^(1 : ℤ) := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
    rw [h_split, show (2 : ℝ)^(1 : ℤ) = 2 by norm_num]; ring
  have h_y_lo_eq : ((y_lo_g e : Dyadic) : ℝ) = (m_low : ℝ) + (2 : ℝ)^(e - 1) := by
    rw [h_y_lo_coe, h_m_low_coe]
    have h_split : (2 : ℝ)^e = (2 : ℝ)^(e - 1) * (2 : ℝ)^(1 : ℤ) := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; ring
    rw [h_split, show (2 : ℝ)^(1 : ℤ) = 2 by norm_num]; ring
  refine ⟨x_val, m_low, y_lo_low_g e, ?_, ?_, ?_⟩
  · -- Rounds F₂ RTZ x m_low.
    refine ⟨h_m_low_in_F₂, ?_, ?_, ?_⟩
    · rw [abs_of_pos h_m_low_pos, abs_of_pos h_x_pos]; linarith
    · positivity
    · intro z hz hz_bnd hz_sign
      have h_z_nn : 0 ≤ ((z : Dyadic) : ℝ) := by
        rcases le_or_gt 0 ((z : Dyadic) : ℝ) with h | h
        · exact h
        · exfalso; nlinarith
      rw [abs_of_nonneg h_z_nn, abs_of_pos h_x_pos] at hz_bnd
      rw [abs_of_pos h_m_low_pos, abs_of_nonneg h_z_nn]
      exact h_F₂_le_x_to_le_m_low z hz hz_bnd
  · -- Rounds F₁_g RNE m_low y_lo_low.
    exact rounds_F₁_g_RNE_m_low_y_lo_low p hp_ge_2 e
  · -- ¬ Rounds F₁_g RNE x y_lo_low: y_lo_g is faithful and strictly closer.
    intro hr
    obtain ⟨_, _, h_close, _⟩ := hr
    have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
    have h_y_lo_faith : IsFaithfulRound (F₁_g p hp_ge_2 e) x_val (y_lo_g e) := by
      right
      refine ⟨h_y_lo_in_F₁, ?_, ?_⟩
      · rw [h_y_lo_eq, hx_def]; linarith
      · intro z hz hz_ge
        obtain ⟨c', hc'⟩ := F₁_g_quantum p hp_ge_2 e hz
        have h_z_gt_m_low : (m_low : ℝ) < (z : ℝ) := lt_of_lt_of_le h_x_gt_m_low hz_ge
        rw [hc', h_m_low_coe] at h_z_gt_m_low
        have h_5_2 : (5 : ℝ) * (2 : ℝ)^(e-1) = (5/2) * (2 : ℝ)^e := by
          rw [show (e-1 : ℤ) = e + (-1 : ℤ) from by ring,
              zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          rw [show (2 : ℝ)^(-1 : ℤ) = 1/2 by
            rw [show ((-1 : ℤ)) = -(1 : ℤ) from by ring, zpow_neg]; norm_num]
          ring
        rw [h_5_2] at h_z_gt_m_low
        have hc'_r_gt : (5/2 : ℝ) < (c' : ℝ) := lt_of_mul_lt_mul_right h_z_gt_m_low h_2e_pos.le
        have hc'_gt_2 : (2 : ℝ) < (c' : ℝ) := by linarith
        have : 2 < c' := by exact_mod_cast hc'_gt_2
        have hc'_ge_3 : 3 ≤ c' := by omega
        change ((y_lo_g e : Dyadic) : ℝ) ≤ (z : ℝ)
        rw [hc', h_y_lo_coe]
        have : (3 : ℝ) ≤ (c' : ℝ) := by exact_mod_cast hc'_ge_3
        nlinarith
    have h_close_lo := h_close (y_lo_g e) h_y_lo_in_F₁ h_y_lo_faith
    -- |x − y_lo_low| = 2^(e−1) + 2^(f₂−2), |x − y_lo_g| = 2^(e−1) − 2^(f₂−2).
    rw [h_y_lo_low_eq, h_y_lo_eq, hx_def] at h_close_lo
    have h_abs_low : |((m_low : ℝ) + (2 : ℝ)^(f₂ - 2)) - ((m_low : ℝ) - (2 : ℝ)^(e - 1))| =
        (2 : ℝ)^(e - 1) + (2 : ℝ)^(f₂ - 2) := by
      rw [show (m_low : ℝ) + (2 : ℝ)^(f₂ - 2) - ((m_low : ℝ) - (2 : ℝ)^(e - 1)) =
          (2 : ℝ)^(e - 1) + (2 : ℝ)^(f₂ - 2) from by ring]
      exact abs_of_pos (by linarith)
    have h_abs_hi : |((m_low : ℝ) + (2 : ℝ)^(f₂ - 2)) - ((m_low : ℝ) + (2 : ℝ)^(e - 1))| =
        (2 : ℝ)^(e - 1) - (2 : ℝ)^(f₂ - 2) := by
      rw [show (m_low : ℝ) + (2 : ℝ)^(f₂ - 2) - ((m_low : ℝ) + (2 : ℝ)^(e - 1)) =
          -((2 : ℝ)^(e - 1) - (2 : ℝ)^(f₂ - 2)) from by ring]
      rw [abs_neg]; exact abs_of_pos (by linarith)
    rw [h_abs_low, h_abs_hi] at h_close_lo
    linarith

end AbstractFormat

end Mpfx
