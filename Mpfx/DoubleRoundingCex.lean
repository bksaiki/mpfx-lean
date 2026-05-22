import Mpfx.Rounding

/-!
# Counterexample to RN-RN correct double rounding

This file proves that round-to-nearest-even followed by round-to-nearest-even
is *not* a correctly-double-rounding pair in general. For every `F₁` of the
form `𝒜(p, e, ⊤)` with `p ≥ 2` and every sufficiently fine `F₂` containing
`F₁.extend 2`, there is a real `x` whose chained RNE-RNE rounding via `F₂`
disagrees with the direct RNE rounding in `F₁`. The same construction
adapts to the other unlisted pairings (RNA-RNA, RTZ-RAZ, …).

The conceptually distinct positive results — the seven *correctly* double
rounding rules from §5.2 — live in `Mpfx/DoubleRounding.lean`. This file
only depends on the rounding-relation infrastructure (`Mpfx.Rounding`) and
the F-adjacency lemmas in `Mpfx.Format`, not on those positive theorems.

The user-facing theorem is `no_rndRNE_RNE_general`. The core proof is in
`no_rndRNE_RNE_arbitrary_F₂`, which takes the structural parameters of
`F₂` explicitly; the wrapper takes only the containment plus finiteness.
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

private theorem coe_y_lo_g (e : ℤ) : ((y_lo_g e : Dyadic) : ℝ) = 3 * (2 : ℝ)^e := by
  change ((Dyadic.ofIntZpow 3 e : Dyadic) : ℝ) = _
  rw [Dyadic.coe_ofIntZpow]; push_cast; ring

private theorem coe_y_hi_g (e : ℤ) :
    ((y_hi_g e : Dyadic) : ℝ) = (2 : ℝ)^(e + 2) := by
  change ((Dyadic.ofIntZpow 1 (e + 2) : Dyadic) : ℝ) = _
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

private theorem F₁_g_quantum (p : ℕ) (hp_ge_2 : 2 ≤ p) (e : ℤ)
    {z : Dyadic} (hz : z ∈ F₁_g p hp_ge_2 e) :
    ∃ c : ℤ, (z : ℝ) = (c : ℝ) * (2 : ℝ)^e := hz.2.1

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
public-facing version is `no_rndRNE_RNE_general`, which takes only
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
    · -- IsFaithfulRound: RoundUp.
      right
      refine ⟨h_m_mem_F₂, le_of_lt h_x_lt_m, ?_⟩
      intro z hzF₂ hx_le_z
      -- Need m ≤ z. If z < m, then z ≤ pred (by h_pred_max), but pred < x ≤ z, contra.
      by_contra h_z_lt_m
      push Not at h_z_lt_m
      have h_z_le_pred := h_pred_max z hzF₂ h_z_lt_m
      linarith
    · -- Closeness: ∀ z ∈ F₂ faithful for x, |x - m| ≤ |x - z|.
      intro z hzF₂ hf
      -- Faithful z: RoundDown (= pred) or RoundUp (= m).
      rcases hf with ⟨_, hz_le, hz_max⟩ | ⟨_, hx_le_z, hz_min⟩
      · -- RoundDown: z ≤ x. z ≤ x < m, so z < m, so z ≤ pred.
        have h_z_lt_m : (z : ℝ) < (m : ℝ) := lt_of_le_of_lt hz_le h_x_lt_m
        have h_z_le_pred := h_pred_max z hzF₂ h_z_lt_m
        -- z ≤ pred ⇒ |x - z| ≥ x - pred = 3·2^k/4 ≥ 2^k/4 = |x - m|.
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
      · -- RoundUp: x ≤ z ≤ m (by min property). Either z = m (trivial) or
        -- z < m forces z ≤ pred via F-adjacency, contradicting pred < x ≤ z.
        have h_z_le_m : (z : ℝ) ≤ (m : ℝ) :=
          hz_min m h_m_mem_F₂ (le_of_lt h_x_lt_m)
        -- Need 2^k/4 ≤ z - x, but z ≤ m gives z - x ≤ 2^k/4. So z = m.
        -- Hmm we'd need to verify z = m here.
        have h_z_eq_m : (z : ℝ) = (m : ℝ) := by
          -- If z < m: by adjacency, z ≤ pred. But z ≥ x > pred. Contra.
          by_contra h_z_ne_m
          have h_z_lt_m : (z : ℝ) < (m : ℝ) := lt_of_le_of_ne h_z_le_m h_z_ne_m
          have h_z_le_pred := h_pred_max z hzF₂ h_z_lt_m
          linarith
        rw [h_z_eq_m]
    · -- No-tie.
      rintro ⟨z, hzF₂, hf, hne, heq⟩
      -- z faithful, z ≠ m, equal distance. Then z = pred (the only other faithful).
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
      · -- RoundUp: z ≥ x. We've shown z = m. But hne says z ≠ m. Contradiction.
        exfalso
        apply hne
        apply Subtype.ext
        have h_z_le_m : (z : ℝ) ≤ (m : ℝ) := hz_min m h_m_mem_F₂ (le_of_lt h_x_lt_m)
        by_contra h_z_ne_m
        have h_z_lt_m : (z : ℝ) < (m : ℝ) := lt_of_le_of_ne h_z_le_m h_z_ne_m
        have h_z_le_pred := h_pred_max z hzF₂ h_z_lt_m
        linarith
  · -- Rounds F₁ RNE m y_hi.
    exact rounds_F₁_g_RNE_m_y_hi p hp_ge_2 e
  · -- ¬ Rounds F₁ RNE x y_hi.
    intro hr
    obtain ⟨_, _, h_close, _⟩ := hr
    have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
    -- y_lo is a faithful F₁-RoundDown of x.
    have h_y_lo_faith : IsFaithfulRound (F₁_g p hp_ge_2 e) x_val y_lo := by
      left
      refine ⟨y_lo_mem_F₁_g p hp_ge_2 e, ?_, ?_⟩
      · -- y_lo ≤ x = m - 2^k/4. y_lo = m - 2^(e-1). Need 2^k/4 ≤ 2^(e-1).
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
    -- Apply closeness.
    have h_close_lo := h_close y_lo (y_lo_mem_F₁_g p hp_ge_2 e) h_y_lo_faith
    -- |x - y_hi| = 2^(e-1) + 2^k/4. |x - y_lo| = 2^(e-1) - 2^k/4.
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
theorem no_rndRNE_RNE_general
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


end AbstractFormat

end Mpfx
