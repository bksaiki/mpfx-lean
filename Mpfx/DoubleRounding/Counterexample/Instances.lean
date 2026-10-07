import Mpfx.DoubleRounding.Counterexample.Neighborhood

/-!
# Double-rounding counterexamples: neighborhood instances

One `AnchorNeighborhood` per target-format shape: integer grid (quantum and
full precision), floating, and single precision.
-/

namespace Mpfx

namespace Cex

/-! ## The shared integer-grid neighborhood

Both integer-grid formats (`F₁_g p e = 𝒜(p, e, ⊤)` and `F₁t_g e = 𝒜(⊤, e, ⊤)`)
have quantum `2^e` and full base, so their `AnchorNeighborhood` is built from the
same anchors `(2·2^e, 3·2^e, 4·2^e)`, midpoint `7·2^(e−1)`, and gap dispatch. The
only format-specific inputs are the quantum extraction, the anchor
membership/parity witnesses, and the single-extra-digit midpoint proof. -/

private noncomputable def integerNeighborhood (F₁ : ParityFormat) (e : ℤ)
    (hquant : ∀ v ∈ F₁.toFormat, ∃ c : ℤ, (v : ℝ) = (c : ℝ) * (2 : ℝ) ^ e)
    (two_e_mem : two_e_g e ∈ F₁.toFormat)
    (y_lo_low_mem : y_lo_low_g e ∈ F₁.toFormat)
    (y_lo_mem : y_lo_g e ∈ F₁.toFormat)
    (y_hi_mem : y_hi_g e ∈ F₁.toFormat)
    (h_even_lo2 : F₁.IsEven (y_lo_low_g e))
    (h_even_hi : F₁.IsEven (y_hi_g e))
    (h_not_odd_hi : ¬ F₁.IsOdd (y_hi_g e))
    (h_mid_mem_ext1 : m_g e ∈ ((F₁.toFiniteFormat.extend 1).toFormat)) :
    AnchorNeighborhood F₁ where
  t := e
  s := e
  lo2 := y_lo_low_g e
  lo := y_lo_g e
  hi := y_hi_g e
  mid := m_g e
  lo2_pos := by
    rw [coe_y_lo_low_g]
    have : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
    linarith
  coe_lo := by rw [coe_y_lo_g, coe_y_lo_low_g]; ring
  coe_hi := by
    rw [coe_y_hi_g, coe_y_lo_g]
    have h := two_zpow_add_two e
    linarith
  coe_mid := by
    rw [coe_m_g, coe_y_lo_g]
    have h := two_zpow_succ (e - 1)
    rw [show e - 1 + 1 = e by ring] at h
    linarith
  mem_lo2 := y_lo_low_mem
  mem_lo := y_lo_mem
  mem_hi := y_hi_mem
  even_lo2 := h_even_lo2
  even_hi := h_even_hi
  not_odd_hi := h_not_odd_hi
  f1_floor_lo := by
    intro v hv hv_lt
    obtain ⟨c, hc⟩ := hquant v hv
    have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
    rw [hc, coe_y_lo_g] at hv_lt
    rw [hc, coe_y_lo_low_g]
    have hc_lt : (c : ℝ) < 3 := lt_of_mul_lt_mul_right hv_lt h_2e_pos.le
    have hc_int : c < 3 := by exact_mod_cast hc_lt
    have hc_le : (c : ℝ) ≤ 2 := by exact_mod_cast (by omega : c ≤ 2)
    nlinarith
  f1_ceil_lo2 := by
    intro v hv hv_gt
    obtain ⟨c, hc⟩ := hquant v hv
    have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
    rw [hc, coe_y_lo_low_g] at hv_gt
    rw [hc, coe_y_lo_g]
    have hc_gt : (2 : ℝ) < (c : ℝ) := lt_of_mul_lt_mul_right hv_gt h_2e_pos.le
    have hc_int : 2 < c := by exact_mod_cast hc_gt
    have hc_ge : (3 : ℝ) ≤ (c : ℝ) := by exact_mod_cast (by omega : 3 ≤ c)
    nlinarith
  f1_floor_hi := by
    intro v hv hv_lt
    obtain ⟨c, hc⟩ := hquant v hv
    have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
    have h4 := two_zpow_add_two e
    rw [hc, coe_y_hi_g] at hv_lt
    rw [h4] at hv_lt
    rw [hc, coe_y_lo_g]
    have hc_lt : (c : ℝ) < 4 := lt_of_mul_lt_mul_right hv_lt h_2e_pos.le
    have hc_int : c < 4 := by exact_mod_cast hc_lt
    have hc_le : (c : ℝ) ≤ 3 := by exact_mod_cast (by omega : c ≤ 3)
    nlinarith
  f1_ceil_hi := by
    intro v hv hv_gt
    obtain ⟨c, hc⟩ := hquant v hv
    have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
    have h4 := two_zpow_add_two e
    rw [hc, coe_y_lo_g] at hv_gt
    rw [hc, coe_y_hi_g, h4]
    have hc_gt : (3 : ℝ) < (c : ℝ) := lt_of_mul_lt_mul_right hv_gt h_2e_pos.le
    have hc_int : 3 < c := by exact_mod_cast hc_gt
    have hc_ge : (4 : ℝ) ≤ (c : ℝ) := by exact_mod_cast (by omega : 4 ≤ c)
    nlinarith
  mid_mem_ext1 := h_mid_mem_ext1
  f2_below_hi := by
    intro F₂ hsub
    obtain ⟨K', hK'_le, h⟩ := gap_below_pow F₂ (E := e + 2)
      (fun g hg => by
        have hb := f₂_le_e_of_two_e_mem (hsub _ two_e_mem) hg
        omega)
    refine ⟨min K' e, min_le_right _ _, ?_⟩
    intro z hz hz_lt
    rw [coe_y_hi_g] at hz_lt
    have h1 := h z hz hz_lt
    have h_mono : (2 : ℝ) ^ (min K' e) ≤ (2 : ℝ) ^ K' :=
      zpow_le_zpow_right₀ (by norm_num) (min_le_left _ _)
    rw [coe_y_hi_g]
    linarith
  f2_above_hi := by
    intro F₂ hsub
    obtain ⟨K', hK'_le, h⟩ := gap_above_pow F₂ (E := e + 2)
      (fun g hg => by
        have hb := f₂_le_e_of_two_e_mem (hsub _ two_e_mem) hg
        omega)
    refine ⟨min K' e, min_le_right _ _, ?_⟩
    intro z hz hz_gt
    rw [coe_y_hi_g] at hz_gt
    have h1 := h z hz hz_gt
    have h_mono : (2 : ℝ) ^ (min K' e) ≤ (2 : ℝ) ^ K' :=
      zpow_le_zpow_right₀ (by norm_num) (min_le_left _ _)
    rw [coe_y_hi_g]
    linarith
  f2_mid_lo := by
    intro F₂ hsub
    obtain ⟨K, hK_le, h_below, h_above⟩ :=
      gap_around_mid F₂ (a := 5) (by norm_num) (by norm_num)
        (fun g hg => f₂_le_e_of_two_e_mem (hsub _ two_e_mem) hg)
        (p_ge2_of_y_lo_mem (hsub _ y_lo_mem))
    have h_A : ((5 : ℤ) : ℝ) * (2 : ℝ) ^ (e - 1)
        = ((y_lo_low_g e : Dyadic) : ℝ) + (2 : ℝ) ^ (e - 1) := by
      rw [coe_y_lo_low_g]
      have h := two_zpow_succ (e - 1)
      rw [show e - 1 + 1 = e by ring] at h
      push_cast
      linarith
    exact ⟨K, hK_le, rebase_gap h_A h_below h_above⟩
  f2_mid_hi := by
    intro F₂ hsub
    obtain ⟨K, hK_le, h_below, h_above⟩ :=
      gap_around_mid F₂ (a := 7) (by norm_num) (by norm_num)
        (fun g hg => f₂_le_e_of_two_e_mem (hsub _ two_e_mem) hg)
        (p_ge2_of_y_lo_mem (hsub _ y_lo_mem))
    have h_A : ((7 : ℤ) : ℝ) * (2 : ℝ) ^ (e - 1)
        = ((y_lo_g e : Dyadic) : ℝ) + (2 : ℝ) ^ (e - 1) := by
      rw [coe_y_lo_g]
      have h := two_zpow_succ (e - 1)
      rw [show e - 1 + 1 = e by ring] at h
      push_cast
      linarith
    exact ⟨K, hK_le, rebase_gap h_A h_below h_above⟩
  f2_mem_mid := by
    intro F₂ hm
    obtain ⟨K, hK_le, h_below, h_above⟩ := gap_around_m_mem F₂ hm
    have h_A : (7 : ℝ) * (2 : ℝ) ^ (e - 1) = ((m_g e : Dyadic) : ℝ) :=
      (coe_m_g e).symm
    exact ⟨K, hK_le, rebase_gap h_A h_below h_above⟩

/-! ## The quantum-format neighborhood

`AnchorNeighborhood` for `F₁_g p e = 𝒜(p, e, ⊤)`: step `2^e`, anchors
`(2·2^e, 3·2^e, 4·2^e)`, midpoint `7·2^(e−1)`. -/

noncomputable def quantumNeighborhood (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ) :
    AnchorNeighborhood (F₁_g p hp_ge_2 e) :=
  integerNeighborhood (F₁_g p hp_ge_2 e) e
    (fun _ hv => F₁_g_quantum p hp_ge_2 e hv)
    (two_e_mem_F₁_g p hp_ge_2 e)
    (y_lo_low_mem_F₁_g p hp_ge_2 e)
    (y_lo_mem_F₁_g p hp_ge_2 e)
    (y_hi_mem_F₁_g p hp_ge_2 e)
    (isEven_F₁_g_y_lo_low p hp_ge_2 e)
    (isEven_F₁_g_y_hi p hp_ge_2 e)
    (notIsOdd_F₁_g_y_hi p hp_ge_2 e)
    (by
      have h_ext_p : ((F₁_g p hp_ge_2 e).toFiniteFormat.extend 1).p
          = ((p + 1 : ℕ) : Prec) := by
        change (F₁_g p hp_ge_2 e).p + ((1 : ℕ) : Prec) = _
        rw [F₁_g_p, ← Nat.cast_add]
      refine ⟨?_, ?_, trivial⟩
      · rw [h_ext_p, Dyadic.precisionAtMost_coe_real]
        refine ⟨7, e - 1, ?_, ?_⟩
        · rw [coe_m_g]; push_cast; ring
        · have h_pow : (8 : ℤ) ≤ (2 : ℤ) ^ (p + 1) :=
            calc (8 : ℤ) = (2 : ℤ) ^ 3 := by norm_num
              _ ≤ (2 : ℤ) ^ (p + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
          have h_abs : |(7 : ℤ)| = 7 := by decide
          omega
      · change Dyadic.quantumAtLeast ((F₁_g p hp_ge_2 e).exp.map (· - (1 : ℤ))) (m_g e)
        rw [F₁_g_exp, WithBot.map_coe, Dyadic.quantumAtLeast_coe_real]
        exact ⟨7, by rw [coe_m_g]; push_cast; ring⟩)

/-! ## The full-precision target format `F₁t_g = 𝒜(⊤, e, ⊤)`

When `F₁.p = ⊤` the `FiniteFormat` invariant forces a finite quantum, and
`F₁` is the full integer grid of step `2^e`. The quantum-format anchors
`2·2^e < 3·2^e < 4·2^e` work verbatim: the precision constraint is
trivial, and parity reads the full integer coefficient
(`numDigits = log₂|x| − e + 1`). -/

def F₁t_g (e : ℤ) : ParityFormat where
  toFiniteFormat :=
    { toFormat := { p := ⊤, exp := (e : QExp), b := ⊤ }
      finite := Or.inr WithBot.coe_ne_bot
      pos := by simp }
  parity := Or.inr WithBot.coe_ne_bot

@[simp] private theorem F₁t_g_p (e : ℤ) : (F₁t_g e).p = ⊤ := rfl

@[simp] private theorem F₁t_g_exp (e : ℤ) :
    (F₁t_g e).exp = (e : QExp) := rfl

@[simp] private theorem F₁t_g_b (e : ℤ) : (F₁t_g e).b = ⊤ := rfl

/-- Membership in the integer-grid format: only the quantum matters. -/
private theorem mem_F₁t_g (e : ℤ) {v : Dyadic} (c : ℤ)
    (hv : ((v : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ) ^ e) :
    v ∈ (F₁t_g e).toFormat := by
  refine ⟨trivial, ?_, trivial⟩
  change Dyadic.quantumAtLeast (e : QExp) v
  rw [Dyadic.quantumAtLeast_coe_real]
  exact ⟨c, hv⟩

private theorem y_lo_mem_F₁t_g (e : ℤ) : y_lo_g e ∈ (F₁t_g e).toFormat :=
  mem_F₁t_g e 3 (by rw [coe_y_lo_g]; push_cast; ring)

private theorem y_lo_low_mem_F₁t_g (e : ℤ) :
    y_lo_low_g e ∈ (F₁t_g e).toFormat :=
  mem_F₁t_g e 2 (by rw [coe_y_lo_low_g]; push_cast; ring)

private theorem y_hi_mem_F₁t_g (e : ℤ) : y_hi_g e ∈ (F₁t_g e).toFormat :=
  mem_F₁t_g e 4 (by
    rw [coe_y_hi_g, two_zpow_add_two]
    push_cast
    ring)

private theorem two_e_mem_F₁t_g (e : ℤ) : two_e_g e ∈ (F₁t_g e).toFormat :=
  mem_F₁t_g e 1 (by rw [coe_two_e_g]; push_cast; ring)

/-- Quantum extraction: every `z ∈ F₁t_g` is `c · 2^e` for some `c : ℤ`. -/
private theorem F₁t_g_quantum (e : ℤ) {z : Dyadic}
    (hz : z ∈ (F₁t_g e).toFormat) :
    ∃ c : ℤ, (z : ℝ) = (c : ℝ) * (2 : ℝ) ^ e := by
  have hq : Dyadic.quantumAtLeast (e : QExp) z := hz.2.1
  rw [Dyadic.quantumAtLeast_coe_real] at hq
  exact hq

private theorem F₁t_g_p_ne_1 (e : ℤ) :
    (F₁t_g e).p ≠ ((1 : ℕ) : Prec) := by
  rw [F₁t_g_p]
  exact WithTop.top_ne_coe

/-- `numDigits` of an anchor `x = 2^N` in the integer grid `F₁t_g` is
`N − e + 1` (no precision cap since `p = ⊤`). -/
private theorem F₁t_g_numDigits (e : ℤ) {x : ℝ} {N : ℤ} (hx : x = (2 : ℝ) ^ N) :
    (F₁t_g e).toFiniteFormat.numDigits x = N - e + 1 := by
  have h_pos : (0 : ℝ) < (2 : ℝ) ^ N := zpow_pos (by norm_num) _
  have h_ne : x ≠ 0 := by rw [hx]; exact ne_of_gt h_pos
  rw [(F₁t_g e).toFiniteFormat.numDigits_top_coe h_ne
    (F₁t_g_exp e) (F₁t_g_p e), hx, abs_of_pos h_pos, log_two_zpow]

/-- `IsEven F₁t_g (4·2^e)`: at `numDigits = 3`, the canonical significand
is `4`. -/
private theorem isEven_F₁t_g_y_hi (e : ℤ) : (F₁t_g e).IsEven (y_hi_g e) := by
  have h_coe_rat : ((y_hi_g e : Dyadic) : ℚ) = (2 : ℚ)^(e + 2) := by
    change ((Dyadic.ofIntZpow 1 (e + 2) : Dyadic) : ℚ) = _
    rw [Dyadic.coe_rat_ofIntZpow]; push_cast; ring
  have h_nd_toNat : ((F₁t_g e).toFiniteFormat.numDigits
      ((y_hi_g e : Dyadic) : ℝ)).toNat = 3 := by
    rw [F₁t_g_numDigits e (coe_y_hi_g e)]; omega
  right
  refine ⟨4, e, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [h_coe_rat, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
    rw [show (2 : ℚ)^(2 : ℤ) = 4 by norm_num]
    push_cast; ring
  · rw [h_nd_toNat]; decide
  · rw [h_nd_toNat]; decide
  · rw [if_neg (F₁t_g_p_ne_1 e)]; decide

/-- `IsEven F₁t_g (2·2^e)`: at `numDigits = 2`, the canonical significand
is `2`. -/
private theorem isEven_F₁t_g_y_lo_low (e : ℤ) :
    (F₁t_g e).IsEven (y_lo_low_g e) := by
  have h_coe_rat : ((y_lo_low_g e : Dyadic) : ℚ) = 2 * (2 : ℚ)^e := by
    change ((Dyadic.ofIntZpow 2 e : Dyadic) : ℚ) = _
    rw [Dyadic.coe_rat_ofIntZpow]; push_cast; ring
  have h_y_eq_2e1 : ((y_lo_low_g e : Dyadic) : ℝ) = (2 : ℝ)^(e + 1) := by
    rw [coe_y_lo_low_g, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [show (2 : ℝ)^(1 : ℤ) = 2 by norm_num]; ring
  have h_nd_toNat : ((F₁t_g e).toFiniteFormat.numDigits
      ((y_lo_low_g e : Dyadic) : ℝ)).toNat = 2 := by
    rw [F₁t_g_numDigits e h_y_eq_2e1]; omega
  right
  refine ⟨2, e, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [h_coe_rat]; push_cast; ring
  · rw [h_nd_toNat]; decide
  · rw [h_nd_toNat]; decide
  · rw [if_neg (F₁t_g_p_ne_1 e)]; decide

/-- `y_hi = 4·2^e` is not odd in `F₁t_g`: its true precision is 1, below
`numDigits = 3`. -/
private theorem notIsOdd_F₁t_g_y_hi (e : ℤ) : ¬ (F₁t_g e).IsOdd (y_hi_g e) := by
  have h_coe_rat : ((y_hi_g e : Dyadic) : ℚ) = (2 : ℚ)^(e + 2) := by
    change ((Dyadic.ofIntZpow 1 (e + 2) : Dyadic) : ℚ) = _
    rw [Dyadic.coe_rat_ofIntZpow]; push_cast; ring
  have h_prec : Dyadic.precisionAtMost ((1 : ℕ) : Prec) (y_hi_g e) := by
    rw [Dyadic.precisionAtMost_coe]
    refine ⟨1, e + 2, ?_, ?_⟩
    · rw [h_coe_rat]; push_cast; ring
    · decide
  have h_gt : ((1 : ℕ) : ℤ) < (F₁t_g e).toFiniteFormat.numDigits
      ((y_hi_g e : Dyadic) : ℝ) := by
    rw [F₁t_g_numDigits e (coe_y_hi_g e)]
    have h1 : ((1 : ℕ) : ℤ) = 1 := by decide
    rw [h1]; omega
  exact (F₁t_g e).precisionAtMost_not_IsOdd Nat.one_pos h_gt h_prec

/-! ## The full-precision neighborhood

The same anchors as the quantum case, on the integer grid `F₁t_g e`. -/

noncomputable def topNeighborhood (e : ℤ) :
    AnchorNeighborhood (F₁t_g e) :=
  integerNeighborhood (F₁t_g e) e
    (fun _ hv => F₁t_g_quantum e hv)
    (two_e_mem_F₁t_g e)
    (y_lo_low_mem_F₁t_g e)
    (y_lo_mem_F₁t_g e)
    (y_hi_mem_F₁t_g e)
    (isEven_F₁t_g_y_lo_low e)
    (isEven_F₁t_g_y_hi e)
    (notIsOdd_F₁t_g_y_hi e)
    (by
      refine ⟨trivial, ?_, trivial⟩
      change Dyadic.quantumAtLeast ((F₁t_g e).exp.map (· - (1 : ℤ))) (m_g e)
      rw [F₁t_g_exp, WithBot.map_coe, Dyadic.quantumAtLeast_coe_real]
      exact ⟨7, by rw [coe_m_g]; push_cast; ring⟩)


/-! ## The floating target format `F₁f_g = 𝒜(q, ⊥, ⊤)`

Finite precision `q ≥ 2`, *no minimum quantum*, unbounded magnitude.
Containing it forces `F₂.exp = ⊥` (it has elements of arbitrarily fine
quantum) and hence a finite `F₂.p = q₂ ≥ q`, so the `F₂`-side gap
dispatch reduces to binade quantization at precision `q₂`. -/

/-- The floating target format `𝒜(q, ⊥, ⊤)` with precision `q ≥ 2`. -/
def F₁f_g (q : ℕ) (hq_ge_2 : 2 ≤ q) : ParityFormat where
  toFiniteFormat :=
    { toFormat := { p := (q : Prec), exp := ⊥, b := ⊤ }
      finite := Or.inl WithTop.coe_ne_top
      pos := by simp; omega }
  parity := Or.inl (by
    intro h
    have h' : (q : Prec) = ((1 : ℕ) : Prec) := h
    have h1 : q = (1 : ℕ) := by exact_mod_cast h'
    omega)

@[simp] private theorem F₁f_g_p q (hq : 2 ≤ q) :
    (F₁f_g q hq).p = (q : Prec) := rfl

@[simp] private theorem F₁f_g_exp q (hq : 2 ≤ q) :
    (F₁f_g q hq).exp = ⊥ := rfl

@[simp] private theorem F₁f_g_b q (hq : 2 ≤ q) :
    (F₁f_g q hq).b = ⊤ := rfl

/-- Membership in the floating format: only the precision matters (the
quantum constraint is `⊥` and the bound is `⊤`). -/
private theorem mem_F₁f_g (q : ℕ) (hq : 2 ≤ q) {v : Dyadic} (c k : ℤ)
    (hv : (v : ℚ) = (c : ℚ) * (2 : ℚ) ^ k) (hc : |c| ≤ 2 ^ q) :
    v ∈ (F₁f_g q hq).toFormat := by
  refine ⟨?_, trivial, trivial⟩
  exact Dyadic.precisionAtMost_of_abs_le (by omega) c k hv hc

/-- `numDigits` of the floating format is constantly `q` on nonzero reals. -/
private theorem F₁f_g_numDigits (q : ℕ) (hq : 2 ≤ q) {x : ℝ}
    (hx : x ≠ 0) :
    (F₁f_g q hq).toFiniteFormat.numDigits x = (q : ℤ) := by
  rw [(F₁f_g q hq).toFiniteFormat.numDigits_coe_bot hx rfl rfl]

/-- `F₁f_g.p ≠ 1`, the precision branch of the parity invariant. -/
private theorem F₁f_g_p_ne_1 (q : ℕ) (hq : 2 ≤ q) :
    (F₁f_g q hq).p ≠ ((1 : ℕ) : Prec) := by
  rw [F₁f_g_p]
  intro h
  have h1 : q = (1 : ℕ) := by exact_mod_cast h
  omega

/-- `2^N ∈ F₁f_g` for **any** `N`: the format has no minimum quantum, so it
contains arbitrarily small and arbitrarily large powers of two. -/
private theorem zpow_mem_F₁f_g (q : ℕ) (hq : 2 ≤ q) (N : ℤ) :
    Dyadic.ofIntZpow 1 N ∈ (F₁f_g q hq).toFormat :=
  mem_F₁f_g q hq 1 N (Dyadic.coe_rat_ofIntZpow 1 N) (by
    have h_pow : (2 : ℤ) ≤ (2 : ℤ) ^ q :=
      calc (2 : ℤ) = (2 : ℤ) ^ 1 := by norm_num
        _ ≤ (2 : ℤ) ^ q := pow_le_pow_right₀ (by norm_num) (by omega)
    have h_abs : |(1 : ℤ)| = 1 := by decide
    omega)

/-! ### Anchors of the floating neighborhood

Significand base `s := 2^(q−1)`: the smallest significand of the binade.
The anchors are `lo2 = s·2^t < lo = (s+1)·2^t < hi = (s+2)·2^t`, with
midpoint `mid = (2s+3)·2^(t−1)` of `(lo, hi)`. -/

/-- Significand base `s = 2^(q−1)`. -/
private def fs (q : ℕ) : ℤ := 2 ^ (q - 1)

private theorem fs_pos (q : ℕ) : 0 < fs q := pow_pos (by norm_num) _

private theorem fs_ge_2 (q : ℕ) (hq : 2 ≤ q) : 2 ≤ fs q := by
  have h : (2 : ℤ) ^ 1 ≤ 2 ^ (q - 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hfs : fs q = 2 ^ (q - 1) := rfl
  norm_num at h
  omega

/-- `2s = 2^q`: the binade's upper significand boundary. -/
private theorem two_fs (q : ℕ) (hq : 0 < q) : 2 * fs q = 2 ^ q := by
  have h : (2 : ℤ) ^ ((q - 1) + 1) = 2 ^ (q - 1) * 2 := pow_succ 2 _
  rw [show (q - 1) + 1 = q by omega] at h
  have hfs : fs q = 2 ^ (q - 1) := rfl
  omega

private theorem fs_even (q : ℕ) (hq : 2 ≤ q) : Even (fs q) := by
  have hfs : fs q = 2 ^ (q - 1) := rfl
  rw [hfs]
  exact (Int.even_pow).mpr ⟨even_two, by omega⟩

private theorem fs_lt (q : ℕ) (hq : 0 < q) : fs q < 2 ^ q := by
  have h1 := two_fs q hq
  have h2 := fs_pos q
  omega

/-- The four anchors at step exponent `t`. -/
private noncomputable def flo2 (q : ℕ) (t : ℤ) : Dyadic :=
  Dyadic.ofIntZpow (fs q) t
private noncomputable def flo (q : ℕ) (t : ℤ) : Dyadic :=
  Dyadic.ofIntZpow (fs q + 1) t
private noncomputable def fhi (q : ℕ) (t : ℤ) : Dyadic :=
  Dyadic.ofIntZpow (fs q + 2) t
private noncomputable def fmid (q : ℕ) (t : ℤ) : Dyadic :=
  Dyadic.ofIntZpow (2 * fs q + 3) (t - 1)

private theorem coe_flo2 (q : ℕ) (t : ℤ) :
    ((flo2 q t : Dyadic) : ℝ) = (fs q : ℝ) * (2 : ℝ) ^ t := by
  rw [flo2, Dyadic.coe_ofIntZpow]

private theorem coe_flo (q : ℕ) (t : ℤ) :
    ((flo q t : Dyadic) : ℝ) = ((fs q : ℝ) + 1) * (2 : ℝ) ^ t := by
  rw [flo, Dyadic.coe_ofIntZpow]; push_cast; ring

private theorem coe_fhi (q : ℕ) (t : ℤ) :
    ((fhi q t : Dyadic) : ℝ) = ((fs q : ℝ) + 2) * (2 : ℝ) ^ t := by
  rw [fhi, Dyadic.coe_ofIntZpow]; push_cast; ring

private theorem coe_fmid (q : ℕ) (t : ℤ) :
    ((fmid q t : Dyadic) : ℝ) = (2 * (fs q : ℝ) + 3) * (2 : ℝ) ^ (t - 1) := by
  rw [fmid, Dyadic.coe_ofIntZpow]; push_cast; ring

private theorem mem_flo2 (q : ℕ) (hq : 2 ≤ q) (t : ℤ) :
    flo2 q t ∈ (F₁f_g q hq).toFormat :=
  mem_F₁f_g q hq (fs q) t (Dyadic.coe_rat_ofIntZpow (fs q) t) (by
    have h1 := fs_pos q
    have h2 := two_fs q (by omega)
    rw [abs_of_pos h1]
    omega)

private theorem mem_flo (q : ℕ) (hq : 2 ≤ q) (t : ℤ) :
    flo q t ∈ (F₁f_g q hq).toFormat :=
  mem_F₁f_g q hq (fs q + 1) t (Dyadic.coe_rat_ofIntZpow (fs q + 1) t) (by
    have h1 := fs_ge_2 q hq
    have h2 := two_fs q (by omega)
    rw [abs_of_pos (by omega)]
    omega)

private theorem mem_fhi (q : ℕ) (hq : 2 ≤ q) (t : ℤ) :
    fhi q t ∈ (F₁f_g q hq).toFormat :=
  mem_F₁f_g q hq (fs q + 2) t (Dyadic.coe_rat_ofIntZpow (fs q + 2) t) (by
    have h1 := fs_ge_2 q hq
    have h2 := two_fs q (by omega)
    rw [abs_of_pos (by omega)]
    omega)

private theorem flo2_pos_real (q : ℕ) (t : ℤ) :
    (0 : ℝ) < ((flo2 q t : Dyadic) : ℝ) := by
  rw [coe_flo2]
  have h1 : (0 : ℝ) < (fs q : ℝ) := by exact_mod_cast fs_pos q
  have h2 : (0 : ℝ) < (2 : ℝ) ^ t := zpow_pos (by norm_num) _
  exact mul_pos h1 h2

private theorem fhi_pos_real (q : ℕ) (t : ℤ) :
    (0 : ℝ) < ((fhi q t : Dyadic) : ℝ) := by
  rw [coe_fhi]
  have h1 : (0 : ℝ) < (fs q : ℝ) := by exact_mod_cast fs_pos q
  have h2 : (0 : ℝ) < (2 : ℝ) ^ t := zpow_pos (by norm_num) _
  nlinarith

/-! ### Parity of the floating anchors -/

/-- `IsEven` of `lo2 = 2^(q−1)·2^t`: the canonical significand at
`numDigits = q` is `2^(q−1)`, even since `q ≥ 2`. -/
private theorem even_flo2 (q : ℕ) (hq : 2 ≤ q) (t : ℤ) :
    (F₁f_g q hq).IsEven (flo2 q t) := by
  have h_ne : ((flo2 q t : Dyadic) : ℝ) ≠ 0 := ne_of_gt (flo2_pos_real q t)
  have h_nd_toNat : ((F₁f_g q hq).toFiniteFormat.numDigits
      ((flo2 q t : Dyadic) : ℝ)).toNat = q := by
    rw [F₁f_g_numDigits q hq h_ne]
    omega
  right
  refine ⟨fs q, t, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact Dyadic.coe_rat_ofIntZpow (fs q) t
  · rw [h_nd_toNat, abs_of_pos (fs_pos q)]
    exact le_refl _
  · rw [h_nd_toNat, abs_of_pos (fs_pos q)]
    exact fs_lt q (by omega)
  · rw [if_neg (F₁f_g_p_ne_1 q hq)]
    exact fs_even q hq

/-- `IsEven` of `hi = (2^(q−1)+2)·2^t`. For `q = 2` the value renormalizes
to `2·2^(t+1)` (significand `2`); for `q ≥ 3` the canonical significand is
`2^(q−1)+2` itself, even. -/
private theorem even_fhi (q : ℕ) (hq : 2 ≤ q) (t : ℤ) :
    (F₁f_g q hq).IsEven (fhi q t) := by
  have h_ne : ((fhi q t : Dyadic) : ℝ) ≠ 0 := ne_of_gt (fhi_pos_real q t)
  have h_nd_toNat : ((F₁f_g q hq).toFiniteFormat.numDigits
      ((fhi q t : Dyadic) : ℝ)).toNat = q := by
    rw [F₁f_g_numDigits q hq h_ne]
    omega
  right
  rcases eq_or_lt_of_le hq with hq2 | hq3
  · -- `q = 2`: `hi = 4·2^t = 2·2^(t+1)`, canonical significand `2`.
    have h_fs2 : fs q = 2 := by
      change (2 : ℤ) ^ (q - 1) = 2
      rw [show q - 1 = 1 by omega]
      norm_num
    refine ⟨2, t + 1, ⟨?_, ?_, ?_⟩, ?_⟩
    · change ((Dyadic.ofIntZpow (fs q + 2) t : Dyadic) : ℚ) = _
      rw [Dyadic.coe_rat_ofIntZpow, h_fs2,
          show (2 : ℚ) ^ (t + 1) = 2 * (2 : ℚ) ^ t from by
            rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_one]; ring]
      push_cast
      ring
    · rw [h_nd_toNat, ← hq2]; decide
    · rw [h_nd_toNat, ← hq2]; decide
    · rw [if_neg (F₁f_g_p_ne_1 q hq)]; decide
  · -- `q ≥ 3`: canonical significand `2^(q−1)+2` directly.
    have hfs : fs q = 2 ^ (q - 1) := rfl
    have h2fs := two_fs q (by omega)
    have h4fs : 4 ≤ fs q := by
      have h4 : (2 : ℤ) ^ 2 ≤ 2 ^ (q - 1) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      norm_num at h4
      omega
    refine ⟨fs q + 2, t, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact Dyadic.coe_rat_ofIntZpow (fs q + 2) t
    · rw [h_nd_toNat, abs_of_pos (by omega : (0 : ℤ) < fs q + 2)]
      omega
    · rw [h_nd_toNat, abs_of_pos (by omega : (0 : ℤ) < fs q + 2)]
      omega
    · rw [if_neg (F₁f_g_p_ne_1 q hq)]
      exact (fs_even q hq).add even_two

/-- `hi = (2^(q−1)+2)·2^t = (2^(q−2)+1)·2^(t+1)` has true precision at most
`q − 1 < q = numDigits`, so it is not odd in the floating format. -/
private theorem not_odd_fhi (q : ℕ) (hq : 2 ≤ q) (t : ℤ) :
    ¬ (F₁f_g q hq).IsOdd (fhi q t) := by
  have h_ne : ((fhi q t : Dyadic) : ℝ) ≠ 0 := ne_of_gt (fhi_pos_real q t)
  have h_w_pos : 0 < q - 1 := by omega
  have hcoef : fs q + 2 = 2 * (2 ^ (q - 2) + 1) := by
    have h : fs q = 2 * 2 ^ (q - 2) := by
      change (2 : ℤ) ^ (q - 1) = 2 * 2 ^ (q - 2)
      rw [show q - 1 = (q - 2) + 1 by omega, pow_succ]
      ring
    omega
  have h_gt : ((q - 1 : ℕ) : ℤ)
      < (F₁f_g q hq).toFiniteFormat.numDigits ((fhi q t : Dyadic) : ℝ) := by
    rw [F₁f_g_numDigits q hq h_ne]
    omega
  refine (F₁f_g q hq).precisionAtMost_not_IsOdd h_w_pos h_gt ?_
  refine Dyadic.precisionAtMost_of_abs_le (by omega) (2 ^ (q - 2) + 1) (t + 1) ?_ ?_
  · change ((Dyadic.ofIntZpow (fs q + 2) t : Dyadic) : ℚ) = _
    rw [Dyadic.coe_rat_ofIntZpow, hcoef,
        show (2 : ℚ) ^ (t + 1) = 2 * (2 : ℚ) ^ t from by
          rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_one]; ring]
    push_cast
    ring
  · have h_pow_pos : (0 : ℤ) < 2 ^ (q - 2) := pow_pos (by norm_num) _
    change |2 ^ (q - 2) + 1| ≤ (2 : ℤ) ^ (q - 1)
    rw [abs_of_pos (by omega)]
    have h_split : (2 : ℤ) ^ (q - 1) = 2 * 2 ^ (q - 2) := by
      rw [show q - 1 = (q - 2) + 1 by omega, pow_succ]
      ring
    omega

/-! ### `F₁f_g`-adjacency -/

/-- Every floating-format element in the window `[s·2^t, 2s·2^t)` is an
integer multiple of `2^t` (binade quantization at precision `q`). -/
private theorem F₁f_window_quantum (q : ℕ) (hq : 2 ≤ q) (t : ℤ)
    {v : Dyadic} (hv : v ∈ (F₁f_g q hq).toFormat)
    (h_lo : (fs q : ℝ) * (2 : ℝ) ^ t ≤ ((v : Dyadic) : ℝ))
    (h_hi : ((v : Dyadic) : ℝ) < 2 * (fs q : ℝ) * (2 : ℝ) ^ t) :
    ∃ c : ℤ, ((v : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ) ^ t := by
  have h_2E : (2 : ℝ) ^ (t + (q : ℤ) - 1) = (fs q : ℝ) * (2 : ℝ) ^ t := by
    have h := two_zpow_split (t + (q : ℤ) - 1) t (by omega)
    rw [show (t + (q : ℤ) - 1 - t).toNat = q - 1 by omega] at h
    rw [h]
    have hfs : fs q = 2 ^ (q - 1) := rfl
    rw [hfs]
    push_cast
    ring
  have h_2E1 : (2 : ℝ) ^ (t + (q : ℤ) - 1 + 1)
      = 2 * (fs q : ℝ) * (2 : ℝ) ^ t := by
    have h := two_zpow_succ (t + (q : ℤ) - 1)
    rw [h, h_2E]
    ring
  obtain ⟨c, hc⟩ := binade_quantum (F₂ := (F₁f_g q hq).toFiniteFormat)
    (q₂ := q) rfl hv (by rw [h_2E]; exact h_lo) (by rw [h_2E1]; exact h_hi)
  rw [show t + (q : ℤ) - 1 - (q : ℤ) + 1 = t by ring] at hc
  exact ⟨c, hc⟩

/-- No floating-format element lies strictly between consecutive multiples
`d·2^t < (d+1)·2^t` inside the binade window. -/
private theorem no_F₁f_between (q : ℕ) (hq : 2 ≤ q) (t : ℤ)
    {d : ℤ} (hd_lo : fs q ≤ d) (hd_hi : d + 1 ≤ 2 * fs q)
    {v : Dyadic} (hv : v ∈ (F₁f_g q hq).toFormat)
    (h_above : (d : ℝ) * (2 : ℝ) ^ t < ((v : Dyadic) : ℝ))
    (h_below : ((v : Dyadic) : ℝ) < ((d : ℝ) + 1) * (2 : ℝ) ^ t) : False := by
  have h2t_pos : (0 : ℝ) < (2 : ℝ) ^ t := zpow_pos (by norm_num) _
  have hd_lo_r : (fs q : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd_lo
  have hd_hi_r : (d : ℝ) + 1 ≤ 2 * (fs q : ℝ) := by
    have h : ((d + 1 : ℤ) : ℝ) ≤ ((2 * fs q : ℤ) : ℝ) := by exact_mod_cast hd_hi
    push_cast at h
    linarith
  obtain ⟨c, hc⟩ := F₁f_window_quantum q hq t hv
    (by nlinarith) (by nlinarith)
  rw [hc] at h_above h_below
  have h1 : (d : ℝ) < (c : ℝ) := lt_of_mul_lt_mul_right h_above h2t_pos.le
  have h2 : (c : ℝ) < (d : ℝ) + 1 := lt_of_mul_lt_mul_right h_below h2t_pos.le
  have h1' : d < c := by exact_mod_cast h1
  have h2' : c < d + 1 := by
    have h : (c : ℝ) < ((d + 1 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast h
  omega

/-! ### Containment data and the floating `F₂`-side dispatch -/

/-- Containing the floating format pins down `F₂`'s shape: `F₂.exp = ⊥`
(else `2^(f₂−1) ∈ F₂` fails the quantum), hence `F₂.p = q₂` finite (by the
`FiniteFormat` invariant) with `q₂ ≥ q` (an odd coefficient of size
`2^(q−1)+1` is visible to the precision). -/
private theorem float_sub_data (q : ℕ) (hq : 2 ≤ q)
    (F₂ : FiniteFormat) (hsub : (F₁f_g q hq).toFormat ⊆ F₂.toFormat) :
    ∃ q₂ : ℕ, F₂.p = (q₂ : Prec) ∧ q ≤ q₂
      ∧ F₂.exp = ⊥ := by
  have h_exp_bot : F₂.exp = ⊥ := by
    by_contra h_ne
    obtain ⟨f₂, hf₂⟩ := WithBot.ne_bot_iff_exists.mp h_ne
    have h_mem : Dyadic.ofIntZpow 1 (f₂ - 1) ∈ F₂.toFormat :=
      hsub _ (zpow_mem_F₁f_g q hq (f₂ - 1))
    have hquant : Dyadic.quantumAtLeast F₂.exp (Dyadic.ofIntZpow 1 (f₂ - 1)) :=
      h_mem.2.1
    rw [← hf₂, Dyadic.quantumAtLeast_coe_real] at hquant
    obtain ⟨c, hc⟩ := hquant
    rw [Dyadic.coe_ofIntZpow] at hc
    have h_ulp : (2 : ℝ) ^ f₂ = 2 * (2 : ℝ) ^ (f₂ - 1) := by
      have h := two_zpow_succ (f₂ - 1)
      rwa [show f₂ - 1 + 1 = f₂ by ring] at h
    rw [h_ulp] at hc
    have h2_pos : (0 : ℝ) < (2 : ℝ) ^ (f₂ - 1) := zpow_pos (by norm_num) _
    have h_eq : ((1 : ℤ) : ℝ) = ((2 * c : ℤ) : ℝ) := by
      apply mul_right_cancel₀ (ne_of_gt h2_pos)
      push_cast
      push_cast at hc
      linarith
    have h_int : (1 : ℤ) = 2 * c := by exact_mod_cast h_eq
    omega
  have hp_ne : F₂.p ≠ ⊤ := by
    rcases F₂.finite with h | h
    · exact h
    · exact absurd h_exp_bot h
  obtain ⟨q₂, hq₂⟩ := WithTop.ne_top_iff_exists.mp hp_ne
  refine ⟨q₂, hq₂.symm, ?_, h_exp_bot⟩
  have h_flo_mem : flo q 0 ∈ F₂.toFormat := hsub _ (mem_flo q hq 0)
  have h_even := fs_even q hq
  have h_odd : Odd (fs q + 1) := by
    obtain ⟨r, hr⟩ := h_even
    exact ⟨r, by omega⟩
  have h_fs_pos := fs_pos q
  have h_flo_eq : ((flo q 0 : Dyadic) : ℝ)
      = ((fs q + 1 : ℤ) : ℝ) * (2 : ℝ) ^ (0 : ℤ) := by
    rw [coe_flo]
    push_cast
    ring
  have h_lt := coeff_lt_of_odd_mem hq₂.symm h_odd (by omega) h_flo_mem h_flo_eq
  by_contra h_gt
  push Not at h_gt
  have h_le : (2 : ℤ) ^ q₂ ≤ 2 ^ (q - 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hfs : fs q = 2 ^ (q - 1) := rfl
  omega

/-- Shift an integer power-of-two factor into the exponent. -/
private theorem int_mul_pow_shift (b : ℤ) (m : ℕ) (J : ℤ) :
    ((b * 2 ^ m : ℤ) : ℝ) * (2 : ℝ) ^ J = (b : ℝ) * (2 : ℝ) ^ (J + m) := by
  have h := two_zpow_split (J + m) J (by omega)
  rw [show (J + (m : ℤ) - J).toNat = m by omega] at h
  rw [h]
  push_cast
  ring

/-- Every `F₂`-element in the three-binade window
`[2^(E−1), 2^(E+2))` around `E := J + q₂` is an integer multiple of `2^J`
(by binade quantization in each of the three binades). -/
private theorem float_window_ulp (F₂ : FiniteFormat) {q₂ : ℕ}
    (hp : F₂.p = (q₂ : Prec)) {J : ℤ} {z : Dyadic}
    (hz : z ∈ F₂.toFormat)
    (h_lo : (2 : ℝ) ^ (J + (q₂ : ℤ) - 1) ≤ ((z : Dyadic) : ℝ))
    (h_hi : ((z : Dyadic) : ℝ) < (2 : ℝ) ^ (J + (q₂ : ℤ) + 2)) :
    ∃ m : ℤ, ((z : Dyadic) : ℝ) = (m : ℝ) * (2 : ℝ) ^ J := by
  rcases lt_or_ge ((z : Dyadic) : ℝ) ((2 : ℝ) ^ (J + (q₂ : ℤ))) with h1 | h1
  · -- binade `[2^(E−1), 2^E)`: step `2^J` exactly.
    obtain ⟨c, hc⟩ := binade_quantum (E := J + (q₂ : ℤ) - 1) hp hz h_lo
      (by rw [show J + (q₂ : ℤ) - 1 + 1 = J + (q₂ : ℤ) by ring]
          exact h1)
    rw [show J + (q₂ : ℤ) - 1 - (q₂ : ℤ) + 1 = J by ring] at hc
    exact ⟨c, hc⟩
  · rcases lt_or_ge ((z : Dyadic) : ℝ) ((2 : ℝ) ^ (J + (q₂ : ℤ) + 1))
      with h2 | h2
    · -- binade `[2^E, 2^(E+1))`: step `2^(J+1)`.
      obtain ⟨c, hc⟩ := binade_quantum (E := J + (q₂ : ℤ)) hp hz h1 h2
      rw [show J + (q₂ : ℤ) - (q₂ : ℤ) + 1 = J + 1 by ring,
          two_zpow_succ J] at hc
      exact ⟨2 * c, by rw [hc]; push_cast; ring⟩
    · -- binade `[2^(E+1), 2^(E+2))`: step `2^(J+2)`.
      obtain ⟨c, hc⟩ := binade_quantum (E := J + (q₂ : ℤ) + 1) hp hz h2
        (by rw [show J + (q₂ : ℤ) + 1 + 1 = J + (q₂ : ℤ) + 2 by ring]
            exact h_hi)
      rw [show J + (q₂ : ℤ) + 1 - (q₂ : ℤ) + 1 = J + 2 by ring,
          two_zpow_add_two J] at hc
      exact ⟨4 * c, by rw [hc]; push_cast; ring⟩

/-- **Floating local-grid gap.** In a format with finite precision `q₂`,
every element on either side of an anchor `a·2^J` with
`2^q₂ ≤ a ≤ 2^(q₂+1)` is at least the local step `2^J` away. -/
private theorem float_gap (F₂ : FiniteFormat) {q₂ : ℕ}
    (hp : F₂.p = (q₂ : Prec)) {J a : ℤ}
    (ha_lo : 2 ^ q₂ ≤ a) (ha_hi : a ≤ 2 ^ (q₂ + 1)) :
    (∀ z ∈ F₂.toFormat, ((z : Dyadic) : ℝ) < (a : ℝ) * (2 : ℝ) ^ J →
      ((z : Dyadic) : ℝ) ≤ (a : ℝ) * (2 : ℝ) ^ J - (2 : ℝ) ^ J) ∧
    (∀ z ∈ F₂.toFormat, (a : ℝ) * (2 : ℝ) ^ J < ((z : Dyadic) : ℝ) →
      (a : ℝ) * (2 : ℝ) ^ J + (2 : ℝ) ^ J ≤ ((z : Dyadic) : ℝ)) := by
  have h2J_pos : (0 : ℝ) < (2 : ℝ) ^ J := zpow_pos (by norm_num) _
  have hq2_1 : 1 ≤ q₂ := F₂.p_pos hp
  have hE : (2 : ℝ) ^ (J + (q₂ : ℤ))
      = (((2 : ℤ) ^ q₂ : ℤ) : ℝ) * (2 : ℝ) ^ J := by
    have h := two_zpow_split (J + (q₂ : ℤ)) J (by omega)
    rw [show (J + (q₂ : ℤ) - J).toNat = q₂ by omega] at h
    rw [h]
    push_cast
    ring
  have hE1 : (2 : ℝ) ^ (J + (q₂ : ℤ) + 1)
      = (((2 : ℤ) ^ (q₂ + 1) : ℤ) : ℝ) * (2 : ℝ) ^ J := by
    have h := two_zpow_split (J + (q₂ : ℤ) + 1) J (by omega)
    rw [show (J + (q₂ : ℤ) + 1 - J).toNat = q₂ + 1 by omega] at h
    rw [h]
    push_cast
    ring
  have ha_lo_r : (((2 : ℤ) ^ q₂ : ℤ) : ℝ) ≤ (a : ℝ) := by
    exact_mod_cast ha_lo
  have ha_hi_r : (a : ℝ) ≤ (((2 : ℤ) ^ (q₂ + 1) : ℤ) : ℝ) := by
    exact_mod_cast ha_hi
  have hA_ge : (2 : ℝ) ^ (J + (q₂ : ℤ)) ≤ (a : ℝ) * (2 : ℝ) ^ J := by
    rw [hE]
    exact mul_le_mul_of_nonneg_right ha_lo_r h2J_pos.le
  have hA_le : (a : ℝ) * (2 : ℝ) ^ J ≤ (2 : ℝ) ^ (J + (q₂ : ℤ) + 1) := by
    rw [hE1]
    exact mul_le_mul_of_nonneg_right ha_hi_r h2J_pos.le
  have h_pow_lo : (2 : ℝ) ^ J ≤ (2 : ℝ) ^ (J + (q₂ : ℤ) - 1) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have h_sum_lo : (2 : ℝ) ^ (J + (q₂ : ℤ) - 1)
        + (2 : ℝ) ^ (J + (q₂ : ℤ) - 1)
      = (2 : ℝ) ^ (J + (q₂ : ℤ)) := by
    have h := two_zpow_succ (J + (q₂ : ℤ) - 1)
    rw [show J + (q₂ : ℤ) - 1 + 1 = J + (q₂ : ℤ) by ring] at h
    linarith
  have h_pow_hi : (2 : ℝ) ^ J ≤ (2 : ℝ) ^ (J + (q₂ : ℤ) + 1) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have h_sum_hi : (2 : ℝ) ^ (J + (q₂ : ℤ) + 1)
        + (2 : ℝ) ^ (J + (q₂ : ℤ) + 1)
      = (2 : ℝ) ^ (J + (q₂ : ℤ) + 2) := by
    have h := two_zpow_succ (J + (q₂ : ℤ) + 1)
    rw [show J + (q₂ : ℤ) + 1 + 1 = J + (q₂ : ℤ) + 2 by ring] at h
    linarith
  constructor
  · intro z hz hz_lt
    rcases lt_or_ge ((z : Dyadic) : ℝ) ((2 : ℝ) ^ (J + (q₂ : ℤ) - 1))
      with hcase | hcase
    · -- Far below the binade: the anchor is at least `2^(E−1)` higher.
      linarith
    · -- On the local grid: integer-coefficient floor.
      obtain ⟨m, hm⟩ := float_window_ulp F₂ hp hz hcase (by
        have h12 : (2 : ℝ) ^ (J + (q₂ : ℤ) + 1)
            ≤ (2 : ℝ) ^ (J + (q₂ : ℤ) + 2) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
        linarith)
      rw [hm] at hz_lt ⊢
      have hm_lt : (m : ℝ) < (a : ℝ) := lt_of_mul_lt_mul_right hz_lt h2J_pos.le
      have hm_int : m < a := by exact_mod_cast hm_lt
      have hm_le : (m : ℝ) ≤ (a : ℝ) - 1 := by
        have h : (m : ℝ) ≤ ((a - 1 : ℤ) : ℝ) := by
          exact_mod_cast (by omega : m ≤ a - 1)
        push_cast at h
        linarith
      have h_mul := mul_le_mul_of_nonneg_right hm_le h2J_pos.le
      have h_ring : ((a : ℝ) - 1) * (2 : ℝ) ^ J
          = (a : ℝ) * (2 : ℝ) ^ J - (2 : ℝ) ^ J := by ring
      linarith
  · intro z hz hz_gt
    rcases lt_or_ge ((z : Dyadic) : ℝ) ((2 : ℝ) ^ (J + (q₂ : ℤ) + 2))
      with hcase | hcase
    · -- On the local grid: integer-coefficient ceiling.
      obtain ⟨m, hm⟩ := float_window_ulp F₂ hp hz (by
        have h01 : (2 : ℝ) ^ (J + (q₂ : ℤ) - 1)
            ≤ (2 : ℝ) ^ (J + (q₂ : ℤ)) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
        linarith) hcase
      rw [hm] at hz_gt ⊢
      have hm_gt : (a : ℝ) < (m : ℝ) := lt_of_mul_lt_mul_right hz_gt h2J_pos.le
      have hm_int : a < m := by exact_mod_cast hm_gt
      have hm_ge : (a : ℝ) + 1 ≤ (m : ℝ) := by
        have h : ((a + 1 : ℤ) : ℝ) ≤ (m : ℝ) := by
          exact_mod_cast (by omega : a + 1 ≤ m)
        push_cast at h
        linarith
      have h_mul := mul_le_mul_of_nonneg_right hm_ge h2J_pos.le
      have h_ring : ((a : ℝ) + 1) * (2 : ℝ) ^ J
          = (a : ℝ) * (2 : ℝ) ^ J + (2 : ℝ) ^ J := by ring
      linarith
    · -- Far above: `z ≥ 2^(E+2) ≥ A + 2^J`.
      linarith

/-- Anchor-friendly wrapper for `float_gap`: an anchor `b·2^t'` with
`2^n ≤ b ≤ 2^(n+1)` (`n ≤ q₂`) rescales to coefficient `b·2^(q₂−n)` at the
local step `2^K`, `K = t' + n − q₂`. -/
private theorem float_anchor_gap (F₂ : FiniteFormat) {q₂ : ℕ}
    (hp : F₂.p = (q₂ : Prec)) {b t' : ℤ} {n : ℕ}
    (hn_le : n ≤ q₂)
    (hb_lo : 2 ^ n ≤ b) (hb_hi : b ≤ 2 ^ (n + 1)) :
    ∃ K : ℤ, K ≤ t' + (n : ℤ) - (q₂ : ℤ) ∧
      (∀ z ∈ F₂.toFormat, ((z : Dyadic) : ℝ) < (b : ℝ) * (2 : ℝ) ^ t' →
        ((z : Dyadic) : ℝ) ≤ (b : ℝ) * (2 : ℝ) ^ t' - (2 : ℝ) ^ K) ∧
      (∀ z ∈ F₂.toFormat, (b : ℝ) * (2 : ℝ) ^ t' < ((z : Dyadic) : ℝ) →
        (b : ℝ) * (2 : ℝ) ^ t' + (2 : ℝ) ^ K ≤ ((z : Dyadic) : ℝ)) := by
  have h_pow_pos : (0 : ℤ) < 2 ^ (q₂ - n) := pow_pos (by norm_num) _
  have ha_lo' : (2 : ℤ) ^ q₂ ≤ b * 2 ^ (q₂ - n) := by
    have h : (2 : ℤ) ^ q₂ = 2 ^ n * 2 ^ (q₂ - n) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h]
    exact mul_le_mul_of_nonneg_right hb_lo h_pow_pos.le
  have ha_hi' : b * 2 ^ (q₂ - n) ≤ (2 : ℤ) ^ (q₂ + 1) := by
    have h : (2 : ℤ) ^ (q₂ + 1) = 2 ^ (n + 1) * 2 ^ (q₂ - n) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h]
    exact mul_le_mul_of_nonneg_right hb_hi h_pow_pos.le
  obtain ⟨h_below, h_above⟩ :=
    float_gap F₂ hp (J := t' - ((q₂ - n : ℕ) : ℤ)) ha_lo' ha_hi'
  have h_anchor : ((b * 2 ^ (q₂ - n) : ℤ) : ℝ)
        * (2 : ℝ) ^ (t' - ((q₂ - n : ℕ) : ℤ))
      = (b : ℝ) * (2 : ℝ) ^ t' := by
    rw [int_mul_pow_shift,
        show t' - ((q₂ - n : ℕ) : ℤ) + ((q₂ - n : ℕ) : ℤ) = t'
          by ring]
  refine ⟨t' - ((q₂ - n : ℕ) : ℤ), by omega, ?_, ?_⟩
  · intro z hz hz_lt
    have h := h_below z hz (by rw [h_anchor]; exact hz_lt)
    rw [h_anchor] at h
    exact h
  · intro z hz hz_gt
    have h := h_above z hz (by rw [h_anchor]; exact hz_gt)
    rw [h_anchor] at h
    exact h

/-- The floating-format anchor neighborhood: anchors `2^(q−1)·2^t`,
`(2^(q−1)+1)·2^t`, `(2^(q−1)+2)·2^t` at an arbitrary step exponent `t`. -/
noncomputable def floatingNeighborhood (q : ℕ) (hq : 2 ≤ q) (t : ℤ) :
    AnchorNeighborhood (F₁f_g q hq) where
  t := t
  s := t
  lo2 := flo2 q t
  lo := flo q t
  hi := fhi q t
  mid := fmid q t
  lo2_pos := flo2_pos_real q t
  coe_lo := by rw [coe_flo, coe_flo2]; ring
  coe_hi := by rw [coe_fhi, coe_flo]; ring
  coe_mid := by
    have h_ulp : (2 : ℝ) ^ t = 2 * (2 : ℝ) ^ (t - 1) := by
      have h := two_zpow_succ (t - 1)
      rwa [show t - 1 + 1 = t by ring] at h
    rw [coe_fmid, coe_flo, h_ulp]
    ring
  mem_lo2 := mem_flo2 q hq t
  mem_lo := mem_flo q hq t
  mem_hi := mem_fhi q hq t
  even_lo2 := even_flo2 q hq t
  even_hi := even_fhi q hq t
  not_odd_hi := not_odd_fhi q hq t
  f1_floor_lo := by
    intro v hv hv_lt
    rcases le_or_gt ((v : Dyadic) : ℝ) ((flo2 q t : Dyadic) : ℝ) with h | h
    · exact h
    · exfalso
      have hfs2 := fs_ge_2 q hq
      refine no_F₁f_between q hq t (d := fs q) le_rfl (by omega) hv ?_ ?_
      · rw [coe_flo2] at h; exact h
      · rw [coe_flo] at hv_lt; exact hv_lt
  f1_ceil_lo2 := by
    intro v hv hv_gt
    rcases le_or_gt ((flo q t : Dyadic) : ℝ) ((v : Dyadic) : ℝ) with h | h
    · exact h
    · exfalso
      have hfs2 := fs_ge_2 q hq
      refine no_F₁f_between q hq t (d := fs q) le_rfl (by omega) hv ?_ ?_
      · rw [coe_flo2] at hv_gt; exact hv_gt
      · rw [coe_flo] at h; exact h
  f1_floor_hi := by
    intro v hv hv_lt
    rcases le_or_gt ((v : Dyadic) : ℝ) ((flo q t : Dyadic) : ℝ) with h | h
    · exact h
    · exfalso
      have hfs2 := fs_ge_2 q hq
      refine no_F₁f_between q hq t (d := fs q + 1) (by omega) (by omega) hv ?_ ?_
      · rw [coe_flo] at h; push_cast; linarith
      · rw [coe_fhi] at hv_lt; push_cast; linarith
  f1_ceil_hi := by
    intro v hv hv_gt
    rcases le_or_gt ((fhi q t : Dyadic) : ℝ) ((v : Dyadic) : ℝ) with h | h
    · exact h
    · exfalso
      have hfs2 := fs_ge_2 q hq
      refine no_F₁f_between q hq t (d := fs q + 1) (by omega) (by omega) hv ?_ ?_
      · rw [coe_flo] at hv_gt; push_cast; linarith
      · rw [coe_fhi] at h; push_cast; linarith
  mid_mem_ext1 := by
    have h_ext_p : ((F₁f_g q hq).toFiniteFormat.extend 1).p
        = ((q + 1 : ℕ) : Prec) := by
      change (F₁f_g q hq).p + ((1 : ℕ) : Prec) = _
      rw [F₁f_g_p, ← Nat.cast_add]
    refine ⟨?_, ?_, trivial⟩
    · rw [h_ext_p, Dyadic.precisionAtMost_coe_real]
      refine ⟨2 * fs q + 3, t - 1, ?_, ?_⟩
      · rw [coe_fmid]; push_cast; ring
      · have h2fs := two_fs q (by omega)
        have hfs2 := fs_ge_2 q hq
        have hpow1 : (2 : ℤ) ^ (q + 1) = 2 * 2 ^ q := by
          rw [pow_succ]; ring
        rw [abs_of_pos (by omega)]
        omega
    · change Dyadic.quantumAtLeast ((F₁f_g q hq).exp.map (· - (1 : ℤ))) (fmid q t)
      exact trivial
  f2_below_hi := by
    intro F₂ hsub
    obtain ⟨q₂, hp, hq_le, _⟩ := float_sub_data q hq F₂ hsub
    have hfs : fs q = 2 ^ (q - 1) := rfl
    have h2fs := two_fs q (by omega)
    have hfs2 := fs_ge_2 q hq
    have hpow : (2 : ℤ) ^ ((q - 1) + 1) = 2 ^ q := by
      rw [show (q - 1) + 1 = q by omega]
    obtain ⟨K, hK_le, h_below, _⟩ := float_anchor_gap F₂ hp (b := fs q + 2)
      (t' := t) (n := q - 1) (by omega) (by omega) (by omega)
    refine ⟨K, by omega, ?_⟩
    intro z hz hz_lt
    rw [coe_fhi] at hz_lt
    have h := h_below z hz (by push_cast; linarith)
    rw [coe_fhi]
    push_cast at h
    linarith
  f2_above_hi := by
    intro F₂ hsub
    obtain ⟨q₂, hp, hq_le, _⟩ := float_sub_data q hq F₂ hsub
    have hfs : fs q = 2 ^ (q - 1) := rfl
    have h2fs := two_fs q (by omega)
    have hfs2 := fs_ge_2 q hq
    have hpow : (2 : ℤ) ^ ((q - 1) + 1) = 2 ^ q := by
      rw [show (q - 1) + 1 = q by omega]
    obtain ⟨K, hK_le, _, h_above⟩ := float_anchor_gap F₂ hp (b := fs q + 2)
      (t' := t) (n := q - 1) (by omega) (by omega) (by omega)
    refine ⟨K, by omega, ?_⟩
    intro z hz hz_gt
    rw [coe_fhi] at hz_gt
    have h := h_above z hz (by push_cast; linarith)
    rw [coe_fhi]
    push_cast at h
    linarith
  f2_mid_lo := by
    intro F₂ hsub
    obtain ⟨q₂, hp, hq_le, _⟩ := float_sub_data q hq F₂ hsub
    have h2fs := two_fs q (by omega)
    have hfs2 := fs_ge_2 q hq
    have hpow1 : (2 : ℤ) ^ (q + 1) = 2 * 2 ^ q := by
      rw [pow_succ]; ring
    obtain ⟨K, hK_le, h_below, h_above⟩ := float_anchor_gap F₂ hp
      (b := 2 * fs q + 1) (t' := t - 1) (n := q) hq_le
      (by omega) (by omega)
    have h_ulp : (2 : ℝ) ^ t = 2 * (2 : ℝ) ^ (t - 1) := by
      have h := two_zpow_succ (t - 1)
      rwa [show t - 1 + 1 = t by ring] at h
    have h_A : ((2 * fs q + 1 : ℤ) : ℝ) * (2 : ℝ) ^ (t - 1)
        = ((flo2 q t : Dyadic) : ℝ) + (2 : ℝ) ^ (t - 1) := by
      rw [coe_flo2, h_ulp]
      push_cast
      ring
    refine ⟨K + 1, by omega, ?_⟩
    rw [show K + 1 - 1 = K by ring]
    exact rebase_gap h_A h_below h_above
  f2_mid_hi := by
    intro F₂ hsub
    obtain ⟨q₂, hp, hq_le, _⟩ := float_sub_data q hq F₂ hsub
    have h2fs := two_fs q (by omega)
    have hfs2 := fs_ge_2 q hq
    have hpow1 : (2 : ℤ) ^ (q + 1) = 2 * 2 ^ q := by
      rw [pow_succ]; ring
    obtain ⟨K, hK_le, h_below, h_above⟩ := float_anchor_gap F₂ hp
      (b := 2 * fs q + 3) (t' := t - 1) (n := q) hq_le
      (by omega) (by omega)
    have h_ulp : (2 : ℝ) ^ t = 2 * (2 : ℝ) ^ (t - 1) := by
      have h := two_zpow_succ (t - 1)
      rwa [show t - 1 + 1 = t by ring] at h
    have h_A : ((2 * fs q + 3 : ℤ) : ℝ) * (2 : ℝ) ^ (t - 1)
        = ((flo q t : Dyadic) : ℝ) + (2 : ℝ) ^ (t - 1) := by
      rw [coe_flo, h_ulp]
      push_cast
      ring
    refine ⟨K + 1, by omega, ?_⟩
    rw [show K + 1 - 1 = K by ring]
    exact rebase_gap h_A h_below h_above
  f2_mem_mid := by
    intro F₂ hmem
    have h_even := fs_even q hq
    have h_odd : Odd (2 * fs q + 3) := ⟨fs q + 1, by ring⟩
    have h_mid_real : ((fmid q t : Dyadic) : ℝ)
        = ((2 * fs q + 3 : ℤ) : ℝ) * (2 : ℝ) ^ (t - 1) := by
      rw [coe_fmid]
      push_cast
      ring
    rcases hexp_eq : F₂.exp with _ | f₂
    · -- `F₂.exp = ⊥`: finite precision `q₂ > q` is forced, and the mid sits
      -- on the binade grid of step `2^(t−1+q−q₂)`.
      have hp_ne : F₂.p ≠ ⊤ := by
        rcases F₂.finite with h | h
        · exact h
        · exact absurd hexp_eq h
      obtain ⟨q₂, hq₂⟩ := WithTop.ne_top_iff_exists.mp hp_ne
      have hp : F₂.p = (q₂ : Prec) := hq₂.symm
      have h2fs := two_fs q (by omega)
      have hfs2 := fs_ge_2 q hq
      have h_lt := coeff_lt_of_odd_mem hp h_odd (by omega) hmem h_mid_real
      have hq_lt : q < q₂ := by
        by_contra h_ge
        push Not at h_ge
        have h_le : (2 : ℤ) ^ q₂ ≤ 2 ^ q :=
          pow_le_pow_right₀ (by norm_num) h_ge
        omega
      have hpow1 : (2 : ℤ) ^ (q + 1) = 2 * 2 ^ q := by
        rw [pow_succ]; ring
      obtain ⟨K, hK_le, h_below, h_above⟩ := float_anchor_gap F₂ hp
        (b := 2 * fs q + 3) (t' := t - 1) (n := q) (by omega)
        (by omega) (by omega)
      refine ⟨K, by omega, ?_, ?_⟩
      · intro z hz hz_lt
        rw [h_mid_real] at hz_lt ⊢
        exact h_below z hz hz_lt
      · intro z hz hz_gt
        rw [h_mid_real] at hz_gt ⊢
        exact h_above z hz hz_gt
    · -- `F₂.exp = f₂` finite: the mid is on the global grid, `f₂ ≤ t − 1`.
      have hexpc : F₂.exp = (f₂ : QExp) := hexp_eq
      have h_f₂_le : f₂ ≤ t - 1 :=
        f₂_le_e_sub_one_of_odd_in_F₂ (e := t) hexpc hmem h_odd h_mid_real
      have hquant : Dyadic.quantumAtLeast F₂.exp (fmid q t) := hmem.2.1
      rw [hexpc, Dyadic.quantumAtLeast_coe_real] at hquant
      obtain ⟨c_t, hc_t⟩ := hquant
      have h2f₂_pos : (0 : ℝ) < (2 : ℝ) ^ f₂ := zpow_pos (by norm_num) _
      have h_target_lo : ((fmid q t : Dyadic) : ℝ) - (2 : ℝ) ^ f₂
          = ((c_t - 1 : ℤ) : ℝ) * (2 : ℝ) ^ f₂ := by
        rw [hc_t]
        push_cast
        ring
      have h_target_hi : ((fmid q t : Dyadic) : ℝ) + (2 : ℝ) ^ f₂
          = ((c_t + 1 : ℤ) : ℝ) * (2 : ℝ) ^ f₂ := by
        rw [hc_t]
        push_cast
        ring
      refine ⟨f₂, by omega, ?_, ?_⟩
      · intro z hz hz_lt
        have h := F₂_quantum_floor hexpc h_target_lo z hz (by linarith)
        linarith
      · intro z hz hz_gt
        have h := F₂_quantum_ceil hexpc h_target_hi z hz (by linarith)
        linarith

/-! ## The single-precision target format `F₁p_g = 𝒜(1, e, ⊤)`

The remaining shape: precision `p = 1`. Its representable values are the
powers of two `±2^k` (`k ≥ e`); parity is read from the *exponent* rather
than the significand (`2^k` is even iff `k − e + 1` is even). The anchors
are three powers of two `2^(e+1) < 2^(e+2) < 2^(e+3)` — geometric, not
arithmetic, so the lower gap `2^(e+1)` is half the upper gap `2^(e+2)`. The
midpoints `3·2^e` and `3·2^(e+1)` are the `a = 3` case of the gap
dispatch. -/

def F₁p_g (e : ℤ) : ParityFormat where
  toFiniteFormat :=
    { toFormat := { p := ((1 : ℕ) : Prec), exp := (e : QExp), b := ⊤ }
      finite := Or.inr WithBot.coe_ne_bot
      pos := by simp }
  parity := Or.inr WithBot.coe_ne_bot

@[simp] private theorem F₁p_g_p (e : ℤ) : (F₁p_g e).p = ((1 : ℕ) : Prec) := rfl

@[simp] private theorem F₁p_g_exp (e : ℤ) : (F₁p_g e).exp = (e : QExp) := rfl

@[simp] private theorem F₁p_g_b (e : ℤ) : (F₁p_g e).b = ⊤ := rfl

/-- Membership of the power of two `2^N` (`N ≥ e`): precision `1`, quantum `N ≥ e`. -/
private theorem mem_F₁p_g (e : ℤ) {N : ℤ} (hN : e ≤ N) :
    Dyadic.ofIntZpow 1 N ∈ (F₁p_g e).toFormat := by
  have h_real : ((Dyadic.ofIntZpow 1 N : Dyadic) : ℝ) = (2 : ℝ)^N := by
    rw [Dyadic.coe_ofIntZpow]; push_cast; ring
  refine ⟨?_, ?_, trivial⟩
  · change Dyadic.precisionAtMost ((1 : ℕ) : Prec) _
    rw [Dyadic.precisionAtMost_coe_real]
    exact ⟨1, N, by rw [h_real]; push_cast; ring, by decide⟩
  · change Dyadic.quantumAtLeast (e : QExp) _
    rw [Dyadic.quantumAtLeast_coe_real]
    refine ⟨(2 : ℤ)^(N - e).toNat, ?_⟩
    rw [h_real, two_zpow_split N e hN]; push_cast; ring

private theorem two_e_mem_F₁p_g (e : ℤ) : two_e_g e ∈ (F₁p_g e).toFormat :=
  mem_F₁p_g e (le_refl e)

/-- Every positive `F₁p_g`-element is a power of two `2^k` with `k ≥ e`. -/
private theorem F₁p_g_pow (e : ℤ) {v : Dyadic} (hv : v ∈ (F₁p_g e).toFormat)
    (hpos : (0 : ℝ) < ((v : Dyadic) : ℝ)) :
    ∃ k : ℤ, ((v : Dyadic) : ℝ) = (2 : ℝ)^k ∧ e ≤ k := by
  have hprec : Dyadic.precisionAtMost ((1 : ℕ) : Prec) v := hv.1
  rw [Dyadic.precisionAtMost_coe_real] at hprec
  obtain ⟨c, k, hck, hc_lt⟩ := hprec
  simp only [pow_one] at hc_lt
  have h2k_pos : (0 : ℝ) < (2 : ℝ)^k := zpow_pos (by norm_num) _
  have hc_pos : 0 < c := by
    rcases lt_trichotomy c 0 with h | h | h
    · exfalso
      have hcr : (c : ℝ) < 0 := by exact_mod_cast h
      nlinarith [hck, h2k_pos, hpos]
    · exfalso
      rw [hck, h] at hpos; simp at hpos
    · exact h
  rw [abs_of_pos hc_pos] at hc_lt
  have hc1 : c = 1 := by omega
  have h_v_eq : ((v : Dyadic) : ℝ) = (2 : ℝ)^k := by rw [hck, hc1]; push_cast; ring
  refine ⟨k, h_v_eq, ?_⟩
  have hq : Dyadic.quantumAtLeast (e : QExp) v := hv.2.1
  rw [Dyadic.quantumAtLeast_coe_real] at hq
  obtain ⟨d, hd⟩ := hq
  rw [h_v_eq] at hd
  have h2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
  have hd_ge1 : (1 : ℝ) ≤ (d : ℝ) := by
    have hd_pos : 0 < d := by
      have : (0 : ℝ) < (d : ℝ) := by nlinarith [hd, h2k_pos, h2e_pos]
      exact_mod_cast this
    exact_mod_cast hd_pos
  have h_ge : (2 : ℝ)^e ≤ (2 : ℝ)^k := by nlinarith [hd, hd_ge1, h2e_pos]
  by_contra h_lt
  push Not at h_lt
  have : (2 : ℝ)^k < (2 : ℝ)^e := zpow_lt_zpow_right₀ (by norm_num) h_lt
  linarith

/-- `numDigits` of a power of two `2^j` (`j ≥ e`) is `1`. -/
private theorem F₁p_g_numDigits_pow (e : ℤ) {j : ℤ} (hj : e ≤ j) :
    (F₁p_g e).toFiniteFormat.numDigits ((Dyadic.ofIntZpow 1 j : Dyadic) : ℝ) = 1 := by
  have h_real : ((Dyadic.ofIntZpow 1 j : Dyadic) : ℝ) = (2 : ℝ)^j := by
    rw [Dyadic.coe_ofIntZpow]; push_cast; ring
  have h_pos : (0 : ℝ) < (2 : ℝ)^j := zpow_pos (by norm_num) _
  have h_ne : ((Dyadic.ofIntZpow 1 j : Dyadic) : ℝ) ≠ 0 := by rw [h_real]; exact ne_of_gt h_pos
  have h_log : Int.log 2 |((Dyadic.ofIntZpow 1 j : Dyadic) : ℝ)| = j := by
    rw [h_real, abs_of_pos h_pos]; exact log_two_zpow j
  rw [(F₁p_g e).toFiniteFormat.numDigits_coe_coe h_ne (F₁p_g_p e) (F₁p_g_exp e), h_log]
  simp only [Nat.cast_one]
  omega

/-- `IsEven` of `2^j` (`j ≥ e`) when `j − e + 1` is even (exponent parity). -/
private theorem isEven_F₁p_g_pow (e : ℤ) {j : ℤ} (hj : e ≤ j)
    (hpar : Even (j - e + 1)) :
    (F₁p_g e).IsEven (Dyadic.ofIntZpow 1 j) := by
  have h_nd : ((F₁p_g e).toFiniteFormat.numDigits
      ((Dyadic.ofIntZpow 1 j : Dyadic) : ℝ)).toNat = 1 := by
    rw [F₁p_g_numDigits_pow e hj]; exact Int.toNat_one
  right
  refine ⟨1, j, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [Dyadic.coe_rat_ofIntZpow]
  · rw [h_nd]; norm_num
  · rw [h_nd]; norm_num
  · rw [if_pos (F₁p_g_p e), F₁p_g_exp e, WithBot.unbotD_coe]; exact hpar

/-- `2^j` (`j ≥ e`) is not odd when `j − e + 1` is even. -/
private theorem notIsOdd_F₁p_g_pow (e : ℤ) {j : ℤ} (hj : e ≤ j)
    (hpar : Even (j - e + 1)) :
    ¬ (F₁p_g e).IsOdd (Dyadic.ofIntZpow 1 j) := by
  intro hodd
  obtain ⟨c, e', ⟨hrep, hlow, hhigh⟩, hp_check⟩ := hodd
  have h_nd : ((F₁p_g e).toFiniteFormat.numDigits
      ((Dyadic.ofIntZpow 1 j : Dyadic) : ℝ)).toNat = 1 := by
    rw [F₁p_g_numDigits_pow e hj]; exact Int.toNat_one
  rw [h_nd] at hlow hhigh
  norm_num at hlow hhigh
  rw [Dyadic.coe_rat_ofIntZpow] at hrep
  have h_real : (2 : ℝ)^j = (c : ℝ) * (2 : ℝ)^e' := by
    have h2 : (((1 : ℤ) * (2 : ℚ)^j : ℚ) : ℝ) = (((c : ℚ) * (2 : ℚ)^e' : ℚ) : ℝ) := by
      exact_mod_cast hrep
    push_cast at h2; linarith
  have h2e'_pos : (0 : ℝ) < (2 : ℝ)^e' := zpow_pos (by norm_num) _
  have h2j_pos : (0 : ℝ) < (2 : ℝ)^j := zpow_pos (by norm_num) _
  have hc_pos : 0 < c := by
    rcases lt_trichotomy c 0 with h | h | h
    · exfalso
      have hcr : (c : ℝ) < 0 := by exact_mod_cast h
      nlinarith
    · exfalso; rw [h] at h_real; simp at h_real; linarith
    · exact h
  rw [abs_of_pos hc_pos] at hlow hhigh
  have hc_eq : c = 1 := by omega
  rw [hc_eq] at h_real
  have he' : e' = j := by
    have h2 : (2 : ℝ)^e' = (2 : ℝ)^j := by push_cast at h_real; linarith
    have l1 := log_two_zpow e'
    rw [h2, log_two_zpow j] at l1
    exact l1.symm
  rw [if_pos (F₁p_g_p e), F₁p_g_exp e, WithBot.unbotD_coe, he'] at hp_check
  exact (Int.not_even_iff_odd.mpr hp_check) hpar

private theorem coe_p_lo2 (e : ℤ) :
    ((Dyadic.ofIntZpow 1 (e + 1) : Dyadic) : ℝ) = (2 : ℝ)^(e + 1) := by
  rw [Dyadic.coe_ofIntZpow]; push_cast; ring
private theorem coe_p_lo (e : ℤ) :
    ((Dyadic.ofIntZpow 1 (e + 2) : Dyadic) : ℝ) = (2 : ℝ)^(e + 2) := by
  rw [Dyadic.coe_ofIntZpow]; push_cast; ring
private theorem coe_p_hi (e : ℤ) :
    ((Dyadic.ofIntZpow 1 (e + 3) : Dyadic) : ℝ) = (2 : ℝ)^(e + 3) := by
  rw [Dyadic.coe_ofIntZpow]; push_cast; ring
private theorem coe_p_mid (e : ℤ) :
    ((Dyadic.ofIntZpow 3 (e + 1) : Dyadic) : ℝ) = (3 : ℝ) * (2 : ℝ)^(e + 1) := by
  rw [Dyadic.coe_ofIntZpow]; push_cast; ring

/-! ## The single-precision neighborhood

`AnchorNeighborhood` for `F₁p_g e = 𝒜(1, e, ⊤)`: power-of-two anchors
`2^(e+1) < 2^(e+2) < 2^(e+3)`, with geometric (not arithmetic) spacing
(`s = e+1`, `t = e+2`) and midpoints `3·2^e`, `3·2^(e+1)`. -/
noncomputable def powerOfTwoNeighborhood (e : ℤ) :
    AnchorNeighborhood (F₁p_g e) where
  t := e + 2
  s := e + 1
  lo2 := Dyadic.ofIntZpow 1 (e + 1)
  lo := Dyadic.ofIntZpow 1 (e + 2)
  hi := Dyadic.ofIntZpow 1 (e + 3)
  mid := Dyadic.ofIntZpow 3 (e + 1)
  lo2_pos := by rw [coe_p_lo2]; exact zpow_pos (by norm_num) _
  coe_lo := by
    rw [coe_p_lo, coe_p_lo2]
    have h := two_zpow_succ (e + 1)
    rw [show e + 1 + 1 = e + 2 by ring] at h
    linarith
  coe_hi := by
    rw [coe_p_hi, coe_p_lo]
    have h := two_zpow_succ (e + 2)
    rw [show e + 2 + 1 = e + 3 by ring] at h
    linarith
  coe_mid := by
    rw [coe_p_mid, coe_p_lo, show e + 2 - 1 = e + 1 by ring]
    have h := two_zpow_succ (e + 1)
    rw [show e + 1 + 1 = e + 2 by ring] at h
    linarith
  mem_lo2 := mem_F₁p_g e (by omega)
  mem_lo := mem_F₁p_g e (by omega)
  mem_hi := mem_F₁p_g e (by omega)
  even_lo2 := isEven_F₁p_g_pow e (by omega) ⟨1, by ring⟩
  even_hi := isEven_F₁p_g_pow e (by omega) ⟨2, by ring⟩
  not_odd_hi := notIsOdd_F₁p_g_pow e (by omega) ⟨2, by ring⟩
  f1_floor_lo := by
    intro v hv hv_lt
    rw [coe_p_lo] at hv_lt
    rw [coe_p_lo2]
    rcases le_or_gt ((v : Dyadic) : ℝ) 0 with h0 | h0
    · have : (0 : ℝ) < (2 : ℝ)^(e + 1) := zpow_pos (by norm_num) _
      linarith
    · obtain ⟨k, hk_eq, _⟩ := F₁p_g_pow e hv h0
      rw [hk_eq] at hv_lt ⊢
      have hk_lt : k < e + 2 := by
        by_contra h; push Not at h
        have : (2 : ℝ)^(e + 2) ≤ (2 : ℝ)^k := zpow_le_zpow_right₀ (by norm_num) h
        linarith
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  f1_ceil_lo2 := by
    intro v hv hv_gt
    rw [coe_p_lo2] at hv_gt
    rw [coe_p_lo]
    obtain ⟨k, hk_eq, hk_ge⟩ := F₁p_g_pow e hv (by
      have : (0 : ℝ) < (2 : ℝ)^(e + 1) := zpow_pos (by norm_num) _
      linarith)
    rw [hk_eq] at hv_gt ⊢
    have hk_gt : e + 1 < k := by
      by_contra h; push Not at h
      have : (2 : ℝ)^k ≤ (2 : ℝ)^(e + 1) := zpow_le_zpow_right₀ (by norm_num) h
      linarith
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  f1_floor_hi := by
    intro v hv hv_lt
    rw [coe_p_hi] at hv_lt
    rw [coe_p_lo]
    rcases le_or_gt ((v : Dyadic) : ℝ) 0 with h0 | h0
    · have : (0 : ℝ) < (2 : ℝ)^(e + 2) := zpow_pos (by norm_num) _
      linarith
    · obtain ⟨k, hk_eq, _⟩ := F₁p_g_pow e hv h0
      rw [hk_eq] at hv_lt ⊢
      have hk_lt : k < e + 3 := by
        by_contra h; push Not at h
        have : (2 : ℝ)^(e + 3) ≤ (2 : ℝ)^k := zpow_le_zpow_right₀ (by norm_num) h
        linarith
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  f1_ceil_hi := by
    intro v hv hv_gt
    rw [coe_p_lo] at hv_gt
    rw [coe_p_hi]
    obtain ⟨k, hk_eq, hk_ge⟩ := F₁p_g_pow e hv (by
      have : (0 : ℝ) < (2 : ℝ)^(e + 2) := zpow_pos (by norm_num) _
      linarith)
    rw [hk_eq] at hv_gt ⊢
    have hk_gt : e + 2 < k := by
      by_contra h; push Not at h
      have : (2 : ℝ)^k ≤ (2 : ℝ)^(e + 2) := zpow_le_zpow_right₀ (by norm_num) h
      linarith
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  mid_mem_ext1 := by
    have h_ext_p : ((F₁p_g e).toFiniteFormat.extend 1).p
        = ((1 + 1 : ℕ) : Prec) := by
      change (F₁p_g e).p + ((1 : ℕ) : Prec) = _
      rw [F₁p_g_p, ← Nat.cast_add]
    refine ⟨?_, ?_, trivial⟩
    · rw [h_ext_p, Dyadic.precisionAtMost_coe_real]
      refine ⟨3, e + 1, ?_, ?_⟩
      · rw [coe_p_mid]; push_cast; ring
      · have h2 : ((1 + 1 : ℕ) : ℕ) = 2 := by decide
        rw [h2]; decide
    · change Dyadic.quantumAtLeast ((F₁p_g e).exp.map (· - (1 : ℤ))) _
      rw [F₁p_g_exp, WithBot.map_coe, Dyadic.quantumAtLeast_coe_real]
      refine ⟨3 * 2 ^ (e + 1 - (e - 1)).toNat, ?_⟩
      rw [coe_p_mid, two_zpow_split (e + 1) (e - 1) (by omega)]
      push_cast; ring
  f2_below_hi := by
    intro F₂ hsub
    obtain ⟨K', hK'_le, h⟩ := gap_below_pow F₂ (E := e + 3)
      (fun g hg => by
        have hb := f₂_le_e_of_two_e_mem (hsub _ (two_e_mem_F₁p_g e)) hg
        omega)
    refine ⟨min K' (e + 2), min_le_right _ _, ?_⟩
    intro z hz hz_lt
    rw [coe_p_hi] at hz_lt
    have h1 := h z hz hz_lt
    have h_mono : (2 : ℝ)^(min K' (e + 2)) ≤ (2 : ℝ)^K' :=
      zpow_le_zpow_right₀ (by norm_num) (min_le_left _ _)
    rw [coe_p_hi]
    linarith
  f2_above_hi := by
    intro F₂ hsub
    obtain ⟨K', hK'_le, h⟩ := gap_above_pow F₂ (E := e + 3)
      (fun g hg => by
        have hb := f₂_le_e_of_two_e_mem (hsub _ (two_e_mem_F₁p_g e)) hg
        omega)
    refine ⟨min K' (e + 2), min_le_right _ _, ?_⟩
    intro z hz hz_gt
    rw [coe_p_hi] at hz_gt
    have h1 := h z hz hz_gt
    have h_mono : (2 : ℝ)^(min K' (e + 2)) ≤ (2 : ℝ)^K' :=
      zpow_le_zpow_right₀ (by norm_num) (min_le_left _ _)
    rw [coe_p_hi]
    linarith
  f2_mid_lo := by
    intro F₂ hsub
    obtain ⟨K, hK_le, h_below, h_above⟩ := gap_around_mid3 F₂ (E := e + 1)
      (fun g hg => by
        have hb := f₂_le_e_of_two_e_mem (hsub _ (two_e_mem_F₁p_g e)) hg
        omega)
    have h_A : (3 : ℝ) * (2 : ℝ)^((e + 1) - 1)
        = ((Dyadic.ofIntZpow 1 (e + 1) : Dyadic) : ℝ) + (2 : ℝ)^((e + 1) - 1) := by
      rw [coe_p_lo2, show (e : ℤ) + 1 - 1 = e by ring]
      have h := two_zpow_succ e
      rw [show e + 1 = e + 1 by ring] at h
      linarith
    exact ⟨K, hK_le, rebase_gap h_A h_below h_above⟩
  f2_mid_hi := by
    intro F₂ hsub
    obtain ⟨K, hK_le, h_below, h_above⟩ := gap_around_mid3 F₂ (E := e + 2)
      (fun g hg => by
        have hb := f₂_le_e_of_two_e_mem (hsub _ (two_e_mem_F₁p_g e)) hg
        omega)
    have h_A : (3 : ℝ) * (2 : ℝ)^((e + 2) - 1)
        = ((Dyadic.ofIntZpow 1 (e + 2) : Dyadic) : ℝ) + (2 : ℝ)^((e + 2) - 1) := by
      rw [coe_p_lo, show (e : ℤ) + 2 - 1 = e + 1 by ring]
      have h := two_zpow_succ (e + 1)
      rw [show e + 1 + 1 = e + 2 by ring] at h
      linarith
    exact ⟨K, hK_le, rebase_gap h_A h_below h_above⟩
  f2_mem_mid := by
    intro F₂ hm
    obtain ⟨K, hK_le, h_below, h_above⟩ := gap_around_mid3_mem F₂ (E := e + 2)
      (by rw [show (e : ℤ) + 2 - 1 = e + 1 by ring]; exact hm)
    have h_A : (3 : ℝ) * (2 : ℝ)^((e + 2) - 1) = ((Dyadic.ofIntZpow 3 (e + 1) : Dyadic) : ℝ) := by
      rw [coe_p_mid, show (e : ℤ) + 2 - 1 = e + 1 by ring]
    exact ⟨K, by omega, rebase_gap h_A h_below h_above⟩

end Cex

end Mpfx
