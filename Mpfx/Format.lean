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

/-- Replace `F`'s bound with `b'`, keeping precision, quantum, and the
structural invariants. The caller provides the non-negativity witness for
the new bound (matching the `b_nn` invariant on `AbstractFormat`).

Used together with `extend` to express the paper's RTO double-rounding
hypotheses, e.g., `((F.extend 1).withBound (F.next F.b) hb) ⊆ F₂` for
`rnd-RTO-RTZ`. -/
def withBound (F : AbstractFormat) (b' : WithTop Dyadic)
    (hb' : ∀ d : Dyadic, b' = ↑d → 0 ≤ (d : ℝ)) : AbstractFormat where
  p := F.p
  exp := F.exp
  b := b'
  p_pos := F.p_pos
  not_degenerate := F.not_degenerate
  b_nn := hb'

@[simp] theorem withBound_p (F : AbstractFormat) (b' : WithTop Dyadic) (hb' :
    ∀ d : Dyadic, b' = ↑d → 0 ≤ (d : ℝ)) :
    (F.withBound b' hb').p = F.p := rfl

@[simp] theorem withBound_exp (F : AbstractFormat) (b' : WithTop Dyadic) (hb' :
    ∀ d : Dyadic, b' = ↑d → 0 ≤ (d : ℝ)) :
    (F.withBound b' hb').exp = F.exp := rfl

@[simp] theorem withBound_b (F : AbstractFormat) (b' : WithTop Dyadic) (hb' :
    ∀ d : Dyadic, b' = ↑d → 0 ≤ (d : ℝ)) :
    (F.withBound b' hb').b = b' := rfl

/-- The paper's `next_{F.p, F.exp}(b)` from §5.2 / Fig. 9: the smallest Dyadic
in the grid `A(F.p, F.exp, ∞)` strictly above `b`. Used to express the bound
condition in the RTO double-rounding hypotheses (e.g.,
`A(p₁+1, exp₁-1, next(b₁)) ⊆ F₂` for `rnd-RTO-RTZ`).

For `b ≥ 0` with finite `(F.p, F.exp)`, computed as `b + step` where the grid
step depends on `b`'s magnitude:
- **Subnormal regime** (`|b| < 2^(F.exp + F.p − 1)`): step = `2^F.exp`.
- **Normal regime**: step = `2^(⌊log₂ b⌋ − F.p + 1)` (binade-dependent).
- Unified: step exponent = `max(F.exp, ⌊log₂ b⌋ − F.p + 1)`.

For `F.p = ⊤` and `F.exp = (e : ℤ)`: `A(⊤, e, ∞)` is all dyadics with quantum
≥ e, so the smallest value strictly above `b` is `b + 2^e`.

For `F.exp = ⊥` (degenerate corner: any precision allowed but no quantum bound,
so no smallest value > b exists): returns `b + 1` as a placeholder; not used
by the paper's RTO rules. -/
noncomputable def next (F : AbstractFormat) (b : Dyadic) : Dyadic :=
  match F.exp, F.p with
  | (e : ℤ), ((p : ℕ) : ℕ∞) =>
    if (b : ℝ) ≤ 0 then
      Dyadic.ofIntZpow 1 e
    else
      let logB : ℤ := Int.log 2 ((b : Dyadic) : ℝ)
      let stepExp : ℤ := max e (logB - (p : ℤ) + 1)
      b + Dyadic.ofIntZpow 1 stepExp
  | (e : ℤ), ⊤ => b + Dyadic.ofIntZpow 1 e
  | ⊥, _ => b + 1

/-- `F.next b > b` for finite `(F.p, F.exp)` and `b ≥ 0`. -/
theorem lt_next_of_finite (F : AbstractFormat) {e : ℤ} {p : ℕ}
    (he : F.exp = (e : WithBot ℤ)) (hp : F.p = ((p : ℕ) : ℕ∞)) (b : Dyadic)
    (hb : 0 ≤ ((b : Dyadic) : ℝ)) :
    (b : ℝ) < (F.next b : ℝ) := by
  have h_step_pos : ∀ k : ℤ, (0 : ℝ) < ((Dyadic.ofIntZpow 1 k : Dyadic) : ℝ) := by
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
    exact h_step_pos e
  · rw [if_neg h]
    push_cast
    have := h_step_pos (max e (Int.log 2 ((b : Dyadic) : ℝ) - (p : ℤ) + 1))
    linarith

/-- `F.next b > b` for `F.p = ⊤` and `F.exp = (e : ℤ)`. -/
theorem lt_next_of_p_top (F : AbstractFormat) {e : ℤ}
    (he : F.exp = (e : WithBot ℤ)) (hp : F.p = ⊤) (b : Dyadic) :
    (b : ℝ) < (F.next b : ℝ) := by
  have h_step_pos : (0 : ℝ) < ((Dyadic.ofIntZpow 1 e : Dyadic) : ℝ) := by
    rw [Dyadic.coe_ofIntZpow]
    have h2 : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
    push_cast; linarith
  have h_next_eq : F.next b = b + Dyadic.ofIntZpow 1 e := by
    -- After unfolding `next` and rewriting via `he, hp`, the goal contains
    -- `match (some e), ⊤ with ...`. The match doesn't auto-reduce because
    -- `⊤ : ℕ∞` doesn't syntactically match the `none` constructor. We rewrite
    -- `⊤` to `none` explicitly via the `Top` instance.
    have hp' : F.p = (none : WithTop ℕ) := hp
    unfold next
    rw [he, hp']
  rw [h_next_eq]; push_cast; linarith

/-- `F.next b ≥ 0` for `b ≥ 0`. Combines all four `(F.p, F.exp)` shapes:
finite-finite via `lt_next_of_finite`; `F.p = ⊤` finite-exp via
`lt_next_of_p_top`; `F.exp = ⊥` corner uses fallback `b + 1`. -/
theorem next_nonneg (F : AbstractFormat) (b : Dyadic) (hb : 0 ≤ ((b : Dyadic) : ℝ)) :
    0 ≤ ((F.next b : Dyadic) : ℝ) := by
  rcases hF_exp : F.exp with _ | e
  · -- F.exp = ⊥. next = b + 1.
    have : F.next b = b + 1 := by unfold next; rw [hF_exp]
    rw [this]; push_cast; linarith
  · rcases hF_p : F.p with _ | p
    · -- F.p = ⊤, F.exp finite. Use lt_next_of_p_top.
      have hlt := lt_next_of_p_top F hF_exp hF_p b
      linarith
    · -- Both finite. Use lt_next_of_finite.
      have hlt := lt_next_of_finite F hF_exp hF_p b hb
      linarith

/-- Computed form of `next` for `F.exp = (e : ℤ), F.p = (p : ℕ), b > 0`. -/
theorem next_eq_finite_pos (F : AbstractFormat) {e : ℤ} {p : ℕ}
    (he : F.exp = (e : WithBot ℤ)) (hp : F.p = ((p : ℕ) : ℕ∞))
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
theorem next_eq_p_top (F : AbstractFormat) {e : ℤ}
    (he : F.exp = (e : WithBot ℤ)) (hp : F.p = ⊤) (b : Dyadic) :
    F.next b = b + Dyadic.ofIntZpow 1 e := by
  have hp' : F.p = (none : WithTop ℕ) := hp
  unfold next
  rw [he, hp']

/-- `b ≤ F.next b` for `b ≥ 0`. Combines all four `(F.p, F.exp)` shapes via
case-split: finite-finite via `lt_next_of_finite`; `F.p = ⊤` finite-exp via
`lt_next_of_p_top`; `F.exp = ⊥` corner via the fallback `b + 1`. -/
theorem self_le_next (F : AbstractFormat) (b : Dyadic)
    (hb : 0 ≤ ((b : Dyadic) : ℝ)) :
    ((b : Dyadic) : ℝ) ≤ ((F.next b : Dyadic) : ℝ) := by
  rcases hF_exp : F.exp with _ | e
  · -- F.exp = ⊥. next = b + 1.
    have : F.next b = b + 1 := by unfold next; rw [hF_exp]
    rw [this]; push_cast; linarith
  · rcases hF_p : F.p with _ | p
    · -- F.p = ⊤, F.exp finite. lt_next_of_p_top.
      have := lt_next_of_p_top F hF_exp hF_p b; linarith
    · -- Both finite. lt_next_of_finite.
      have := lt_next_of_finite F hF_exp hF_p b hb; linarith

/-- For a finite-precision finite-exp format `F` with `F.p = (p : ℕ)`,
`F.exp = (exp : ℤ)`, and a positive value `y ∈ F`, there exist `k : ℤ` with
`k ≥ exp` and an integer `c` with `|c| < 2^p` such that `y = c·2^k`. The
exponent `k` is the F-grid step exponent at `y`: `max(exp, ⌊log₂ y⌋ - p + 1)`.

This is the key structural lemma underlying the F-adjacent midpoint analysis:
F-adjacent values at this `k` differ by exactly `2^k`. -/
theorem exists_grid_rep (F : AbstractFormat) {p : ℕ} {exp : ℤ}
    (hp : F.p = (p : ℕ∞)) (he : F.exp = (exp : WithBot ℤ))
    {y : Dyadic} (hp_y_full : Dyadic.precisionAtMost F.p y)
    (hq_y_full : Dyadic.quantumAtLeast F.exp y)
    (hy_pos : 0 < ((y : Dyadic) : ℝ)) :
    ∃ (k : ℤ) (c : ℤ),
      k ≥ exp ∧ |c| < (2 : ℤ)^p ∧
      ((y : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ)^k ∧
      k = max exp (Int.log 2 ((y : Dyadic) : ℝ) - (p : ℤ) + 1) := by
  let k : ℤ := max exp (Int.log 2 ((y : Dyadic) : ℝ) - (p : ℤ) + 1)
  -- Get canonical (c_can, e_can) for y.
  have hy_ne : ((y : Dyadic) : ℝ) ≠ 0 := ne_of_gt hy_pos
  have hp_y : Dyadic.precisionAtMost (p : ℕ∞) y := hp ▸ hp_y_full
  obtain ⟨c_can, e_can, hy_eq, h_odd, hc_can_lt⟩ :=
    Dyadic.exists_odd_canonical_of_precisionAtMost hp_y hy_ne
  -- Need e_can ≥ k. From canonical form constraints.
  have h_e_can_ge_exp : e_can ≥ exp := by
    have hq : Dyadic.quantumAtLeast F.exp y := hq_y_full
    rw [he, Dyadic.quantumAtLeast_coe] at hq
    obtain ⟨c', hc'_eq⟩ := hq
    -- y = c'·2^exp. Compare with canonical (c_can, e_can): c_can·2^e_can = c'·2^exp.
    -- If e_can < exp: by uniqueness, contradiction with c_can odd.
    by_contra h_lt
    push Not at h_lt
    have h_e_can_lt : e_can < exp := h_lt
    -- We have c_can·2^e_can = c'·2^exp with e_can < exp.
    -- Apply uniqueness: c' must be odd factor times 2^(exp - e_can), but c_can is odd.
    -- Equivalent: c'·2^(exp - e_can) = c_can/something... actually let's just
    -- manipulate: c_can = c' · 2^(exp - e_can), so c_can has factor 2^(exp - e_can) ≥ 2.
    have h_diff : c_can = c' * (2 : ℤ)^(exp - e_can).toNat := by
      have hd_pos : 0 < exp - e_can := by omega
      have hd_nn : 0 ≤ exp - e_can := le_of_lt hd_pos
      have : (c_can : ℝ) * (2 : ℝ)^e_can = (c' : ℝ) * (2 : ℝ)^exp := hy_eq.symm.trans hc'_eq
      have h_2_ne : (2 : ℝ) ≠ 0 := by norm_num
      have h_2e_can_ne : (2 : ℝ)^e_can ≠ 0 := zpow_ne_zero _ h_2_ne
      have h_eq2 : (c_can : ℝ) * (2 : ℝ)^e_can =
          ((c' : ℝ) * (2 : ℝ)^(exp - e_can)) * (2 : ℝ)^e_can := by
        have h_split :
            (c' : ℝ) * (2 : ℝ)^(exp - e_can) * (2 : ℝ)^e_can = (c' : ℝ) * (2 : ℝ)^exp := by
          rw [mul_assoc, ← zpow_add₀ h_2_ne]
          congr 2; omega
        rw [h_split]; exact this
      have h_c_eq : (c_can : ℝ) = (c' : ℝ) * (2 : ℝ)^(exp - e_can) :=
        mul_right_cancel₀ h_2e_can_ne h_eq2
      lift (exp - e_can) to ℕ using hd_nn with d hd
      rw [zpow_natCast] at h_c_eq
      have : ((c_can : ℝ)) = ((c' * (2 : ℤ)^d : ℤ) : ℝ) := by
        rw [h_c_eq]; push_cast; ring
      exact_mod_cast this
    have h_2_dvd_c_can : (2 : ℤ) ∣ c_can := by
      rw [h_diff]
      have hd_pos_nat : 0 < (exp - e_can).toNat := by
        have : 0 < exp - e_can := by omega
        omega
      exact dvd_mul_of_dvd_right (dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hd_pos_nat)) _
    exact (Int.not_even_iff_odd.mpr h_odd) (even_iff_two_dvd.mpr h_2_dvd_c_can)
  -- Now derive: e_can ≥ k. Need ⌊log₂ y⌋ - p + 1 ≤ e_can.
  have h_log_y : Int.log 2 ((y : Dyadic) : ℝ) ≤ e_can + p - 1 := by
    -- y = c_can · 2^e_can, |c_can| < 2^p, so y < 2^p · 2^e_can = 2^(e_can + p).
    -- Hence Int.log 2 y ≤ e_can + p - 1.
    have h_c_can_ne : c_can ≠ 0 := by
      intro h
      rw [h] at hy_eq; push_cast at hy_eq
      rw [zero_mul] at hy_eq
      exact hy_ne hy_eq
    have h_c_can_pos_int : 0 < c_can := by
      rcases lt_trichotomy c_can 0 with hc | hc | hc
      · exfalso
        have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e_can := zpow_pos (by norm_num) _
        have h_neg : ((c_can : ℝ)) < 0 := by exact_mod_cast hc
        have : ((y : Dyadic) : ℝ) < 0 := by
          rw [hy_eq]; exact mul_neg_of_neg_of_pos h_neg h_2e_pos
        linarith
      · exfalso
        rw [hc] at hy_eq; push_cast at hy_eq
        rw [zero_mul] at hy_eq; linarith
      · exact hc
    have h_y_lt : ((y : Dyadic) : ℝ) < (2 : ℝ)^(e_can + (p : ℤ)) := by
      have h_y_eq' : ((y : Dyadic) : ℝ) = (c_can : ℝ) * (2 : ℝ)^e_can := hy_eq
      rw [h_y_eq']
      have h_c_abs : (c_can : ℝ) < (2 : ℝ)^(p : ℤ) := by
        have h_c_abs_int : c_can < (2 : ℤ)^p := by
          have habs : |c_can| = c_can := abs_of_pos h_c_can_pos_int
          rw [← habs]; exact hc_can_lt
        have : ((c_can : ℤ) : ℝ) < (((2 : ℤ)^p : ℤ) : ℝ) := by exact_mod_cast h_c_abs_int
        rw [show (((2 : ℤ)^p : ℤ) : ℝ) = (2 : ℝ)^(p : ℤ) from by push_cast; rfl] at this
        exact this
      have h_2e_pos : (0 : ℝ) < (2 : ℝ)^e_can := zpow_pos (by norm_num) _
      calc (c_can : ℝ) * (2 : ℝ)^e_can
          < (2 : ℝ)^(p : ℤ) * (2 : ℝ)^e_can :=
              mul_lt_mul_of_pos_right h_c_abs h_2e_pos
        _ = (2 : ℝ)^(e_can + (p : ℤ)) := by
              rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; ring_nf
    have h_y_lt' : ((y : Dyadic) : ℝ) < ((2 : ℕ) : ℝ)^(e_can + (p : ℤ)) := by
      rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) from by push_cast; rfl]
      exact h_y_lt
    have h_log_lt : Int.log 2 ((y : Dyadic) : ℝ) < e_can + (p : ℤ) :=
      (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) hy_pos).mp h_y_lt'
    omega
  -- So k = max(exp, log_y - p + 1) ≤ max(exp, e_can - 1 + 1 - 1 + 1) = ... hmm
  -- Actually k ≤ max(exp, e_can + p - 1 - p + 1) = max(exp, e_can). With e_can ≥ exp, k ≤ e_can.
  have h_k_le_e_can : k ≤ e_can := by
    change max exp (Int.log 2 ((y : Dyadic) : ℝ) - (p : ℤ) + 1) ≤ e_can
    have h1 : exp ≤ e_can := h_e_can_ge_exp
    have h2 : Int.log 2 ((y : Dyadic) : ℝ) - (p : ℤ) + 1 ≤ e_can := by omega
    exact max_le h1 h2
  have h_k_ge_exp : k ≥ exp := le_max_left _ _
  -- Now y at quantum k: y = c_can · 2^(e_can - k) · 2^k = (c_can · 2^(e_can - k)) · 2^k.
  refine ⟨k, c_can * (2 : ℤ)^(e_can - k).toNat, h_k_ge_exp, ?_, ?_, rfl⟩
  · -- |d| < 2^p, where d = c_can · 2^(e_can - k).toNat.
    set d : ℤ := c_can * (2 : ℤ)^(e_can - k).toNat with hd_def
    have h_y_eq_d : ((y : Dyadic) : ℝ) = (d : ℝ) * (2 : ℝ)^k := by
      rw [hy_eq, hd_def]
      have h_diff_nn : 0 ≤ e_can - k := by omega
      have h_split :
          (c_can : ℝ) * (2 : ℝ)^e_can = (c_can : ℝ) * (2 : ℝ)^(e_can - k) * (2 : ℝ)^k := by
        rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        congr 2; omega
      rw [h_split]
      have h_eq_zpow : (2 : ℝ)^(e_can - k) = (2 : ℝ)^((e_can - k).toNat : ℤ) := by
        rw [Int.toNat_of_nonneg h_diff_nn]
      rw [h_eq_zpow, zpow_natCast]
      push_cast; ring
    have h_y_lt : ((y : Dyadic) : ℝ) < (2 : ℝ)^(k + (p : ℤ)) := by
      have h_log_lt : Int.log 2 ((y : Dyadic) : ℝ) < k + (p : ℤ) := by
        have hk_ge : Int.log 2 ((y : Dyadic) : ℝ) - (p : ℤ) + 1 ≤ k := le_max_right _ _
        omega
      have := (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) hy_pos).mpr h_log_lt
      exact_mod_cast this
    have h_2k_pos : (0 : ℝ) < (2 : ℝ)^k := zpow_pos (by norm_num) _
    have h_d_pos : 0 < d := by
      have h_d_real_pos : (0 : ℝ) < (d : ℝ) := by
        have : (d : ℝ) * (2 : ℝ)^k > 0 := h_y_eq_d ▸ hy_pos
        exact pos_of_mul_pos_left (by linarith [this, h_2k_pos]) (le_of_lt h_2k_pos)
      exact_mod_cast h_d_real_pos
    have h_d_real_lt : (d : ℝ) < (2 : ℝ)^(p : ℤ) := by
      have h_calc : (d : ℝ) * (2 : ℝ)^k < (2 : ℝ)^(k + (p : ℤ)) := h_y_eq_d ▸ h_y_lt
      have h_kp_eq : (2 : ℝ)^(k + (p : ℤ)) = (2 : ℝ)^(p : ℤ) * (2 : ℝ)^k := by
        rw [add_comm, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      rw [h_kp_eq] at h_calc
      exact lt_of_mul_lt_mul_right h_calc (le_of_lt h_2k_pos)
    have h_d_lt : d < (2 : ℤ)^p := by
      have : ((d : ℤ) : ℝ) < (((2 : ℤ)^p : ℤ) : ℝ) := by
        rw [show (((2 : ℤ)^p : ℤ) : ℝ) = (2 : ℝ)^(p : ℤ) from by push_cast; rfl]
        exact h_d_real_lt
      exact_mod_cast this
    have h_abs : |d| = d := abs_of_pos h_d_pos
    rw [h_abs]
    exact h_d_lt
  · -- y = d · 2^k.
    rw [hy_eq]
    have h_diff_nn : 0 ≤ e_can - k := by omega
    have h_split :
        (c_can : ℝ) * (2 : ℝ)^e_can = (c_can : ℝ) * (2 : ℝ)^(e_can - k) * (2 : ℝ)^k := by
      rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 2; omega
    rw [h_split]
    have h_toNat : (e_can - k).toNat = (e_can - k).toNat := rfl
    have h_eq_zpow : (2 : ℝ)^(e_can - k) = (2 : ℝ)^((e_can - k).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg h_diff_nn]
    rw [h_eq_zpow, zpow_natCast]
    push_cast; ring

/-- For a representation `y = c·2^k` with `y > 0`, the integer `c > 0`. -/
private theorem grid_rep_c_pos {y : Dyadic} (hy_pos : 0 < ((y : Dyadic) : ℝ))
    {k c : ℤ}
    (h : ((y : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ) ^ k) :
    0 < c := by
  have h_2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
  have h_c_real_pos : (0 : ℝ) < (c : ℝ) := by
    have : (c : ℝ) * (2 : ℝ) ^ k > 0 := h ▸ hy_pos
    exact pos_of_mul_pos_left (by linarith) (le_of_lt h_2k_pos)
  exact_mod_cast h_c_real_pos

/-- F-grid representation for `F.exp = ⊥`. Same as `exists_grid_rep` but
`k = ⌊log₂ y⌋ - p + 1` (no `max` with exp). -/
theorem exists_grid_rep_exp_bot (F : AbstractFormat) {p : ℕ}
    (hp : F.p = (p : ℕ∞))
    {y : Dyadic} (hp_y_full : Dyadic.precisionAtMost F.p y)
    (hy_pos : 0 < ((y : Dyadic) : ℝ)) :
    ∃ (k : ℤ) (c : ℤ),
      |c| < (2 : ℤ) ^ p ∧
      ((y : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ) ^ k ∧
      k = Int.log 2 ((y : Dyadic) : ℝ) - (p : ℤ) + 1 := by
  let k : ℤ := Int.log 2 ((y : Dyadic) : ℝ) - (p : ℤ) + 1
  have hy_ne : ((y : Dyadic) : ℝ) ≠ 0 := ne_of_gt hy_pos
  have hp_y : Dyadic.precisionAtMost (p : ℕ∞) y := hp ▸ hp_y_full
  obtain ⟨c_can, e_can, hy_eq, h_odd, hc_can_lt⟩ :=
    Dyadic.exists_odd_canonical_of_precisionAtMost hp_y hy_ne
  have h_c_can_ne : c_can ≠ 0 := by
    intro h
    rw [h] at hy_eq; push_cast at hy_eq
    rw [zero_mul] at hy_eq
    exact hy_ne hy_eq
  have h_c_can_pos_int : 0 < c_can := by
    rcases lt_trichotomy c_can 0 with hc | hc | hc
    · exfalso
      have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e_can := zpow_pos (by norm_num) _
      have h_neg : ((c_can : ℝ)) < 0 := by exact_mod_cast hc
      have : ((y : Dyadic) : ℝ) < 0 := by
        rw [hy_eq]; exact mul_neg_of_neg_of_pos h_neg h_2e_pos
      linarith
    · exfalso; exact h_c_can_ne hc
    · exact hc
  have h_log_y : Int.log 2 ((y : Dyadic) : ℝ) ≤ e_can + (p : ℤ) - 1 := by
    have h_y_lt : ((y : Dyadic) : ℝ) < (2 : ℝ) ^ (e_can + (p : ℤ)) := by
      rw [hy_eq]
      have h_c_abs : (c_can : ℝ) < (2 : ℝ) ^ (p : ℤ) := by
        have h_c_abs_int : c_can < (2 : ℤ) ^ p := by
          have habs : |c_can| = c_can := abs_of_pos h_c_can_pos_int
          rw [← habs]; exact hc_can_lt
        have : ((c_can : ℤ) : ℝ) < (((2 : ℤ) ^ p : ℤ) : ℝ) := by exact_mod_cast h_c_abs_int
        rw [show (((2 : ℤ) ^ p : ℤ) : ℝ) = (2 : ℝ) ^ (p : ℤ) from by push_cast; rfl] at this
        exact this
      have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e_can := zpow_pos (by norm_num) _
      calc (c_can : ℝ) * (2 : ℝ) ^ e_can
          < (2 : ℝ) ^ (p : ℤ) * (2 : ℝ) ^ e_can :=
              mul_lt_mul_of_pos_right h_c_abs h_2e_pos
        _ = (2 : ℝ) ^ (e_can + (p : ℤ)) := by
              rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; ring_nf
    have h_y_lt_nat : ((y : Dyadic) : ℝ) < ((2 : ℕ) : ℝ) ^ (e_can + (p : ℤ)) := by
      rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) from by push_cast; rfl]
      exact h_y_lt
    have : Int.log 2 ((y : Dyadic) : ℝ) < e_can + (p : ℤ) :=
      (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) hy_pos).mp h_y_lt_nat
    omega
  have h_k_le_e_can : k ≤ e_can := by
    change Int.log 2 ((y : Dyadic) : ℝ) - (p : ℤ) + 1 ≤ e_can
    omega
  refine ⟨k, c_can * (2 : ℤ) ^ (e_can - k).toNat, ?_, ?_, rfl⟩
  · set d : ℤ := c_can * (2 : ℤ) ^ (e_can - k).toNat with hd_def
    have h_y_eq_d : ((y : Dyadic) : ℝ) = (d : ℝ) * (2 : ℝ) ^ k := by
      rw [hy_eq, hd_def]
      have h_diff_nn : 0 ≤ e_can - k := by omega
      have h_split :
          (c_can : ℝ) * (2 : ℝ) ^ e_can
            = (c_can : ℝ) * (2 : ℝ) ^ (e_can - k) * (2 : ℝ) ^ k := by
        rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        congr 2; omega
      rw [h_split]
      have h_eq_zpow : (2 : ℝ) ^ (e_can - k) = (2 : ℝ) ^ ((e_can - k).toNat : ℤ) := by
        rw [Int.toNat_of_nonneg h_diff_nn]
      rw [h_eq_zpow, zpow_natCast]
      push_cast; ring
    have h_y_lt : ((y : Dyadic) : ℝ) < (2 : ℝ) ^ (k + (p : ℤ)) := by
      have h_log_lt : Int.log 2 ((y : Dyadic) : ℝ) < k + (p : ℤ) := by
        have hk_def : k = Int.log 2 ((y : Dyadic) : ℝ) - (p : ℤ) + 1 := rfl
        omega
      have := (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) hy_pos).mpr h_log_lt
      exact_mod_cast this
    have h_2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
    have h_d_pos : 0 < d := by
      have h_d_real_pos : (0 : ℝ) < (d : ℝ) := by
        have : (d : ℝ) * (2 : ℝ) ^ k > 0 := h_y_eq_d ▸ hy_pos
        exact pos_of_mul_pos_left (by linarith) (le_of_lt h_2k_pos)
      exact_mod_cast h_d_real_pos
    have h_d_real_lt : (d : ℝ) < (2 : ℝ) ^ (p : ℤ) := by
      have h_calc : (d : ℝ) * (2 : ℝ) ^ k < (2 : ℝ) ^ (k + (p : ℤ)) := h_y_eq_d ▸ h_y_lt
      have h_kp_eq : (2 : ℝ) ^ (k + (p : ℤ)) = (2 : ℝ) ^ (p : ℤ) * (2 : ℝ) ^ k := by
        rw [add_comm, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      rw [h_kp_eq] at h_calc
      exact lt_of_mul_lt_mul_right h_calc (le_of_lt h_2k_pos)
    have h_d_lt : d < (2 : ℤ) ^ p := by
      have : ((d : ℤ) : ℝ) < (((2 : ℤ) ^ p : ℤ) : ℝ) := by
        rw [show (((2 : ℤ) ^ p : ℤ) : ℝ) = (2 : ℝ) ^ (p : ℤ) from by push_cast; rfl]
        exact h_d_real_lt
      exact_mod_cast this
    have h_abs : |d| = d := abs_of_pos h_d_pos
    rw [h_abs]; exact h_d_lt
  · rw [hy_eq]
    have h_diff_nn : 0 ≤ e_can - k := by omega
    have h_split :
        (c_can : ℝ) * (2 : ℝ) ^ e_can
          = (c_can : ℝ) * (2 : ℝ) ^ (e_can - k) * (2 : ℝ) ^ k := by
      rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 2; omega
    rw [h_split]
    have h_eq_zpow : (2 : ℝ) ^ (e_can - k) = (2 : ℝ) ^ ((e_can - k).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg h_diff_nn]
    rw [h_eq_zpow, zpow_natCast]
    push_cast; ring

/-- No F element lies strictly in the open interval `(c·2^k, (c+1)·2^k)` when
`k = max(exp, ⌊log₂(c·2^k)⌋ - p + 1)` is the F-grid step exponent at `c·2^k`.
This is the key F-adjacency lemma: applying `exists_grid_rep` to a putative
`y ∈ F` strictly in the interval forces `y` to have grid-exp `k' = k`, making
`y/2^k` an integer strictly between `c` and `c+1`, a contradiction. -/
private theorem no_F_element_in_step_interval (F : AbstractFormat) {p : ℕ} {exp : ℤ}
    (hp : F.p = (p : ℕ∞)) (he : F.exp = (exp : WithBot ℤ))
    {c : ℤ} (hc_pos : 0 < c) (hc_lt : c < (2 : ℤ) ^ p)
    {k : ℤ} (hk : k ≥ exp)
    (hk_max : k = max exp (Int.log 2 ((c : ℝ) * (2 : ℝ) ^ k) - (p : ℤ) + 1))
    {y : Dyadic}
    (hp_y : Dyadic.precisionAtMost F.p y) (hq_y : Dyadic.quantumAtLeast F.exp y)
    (h_lb : ((c : ℝ)) * (2 : ℝ) ^ k < ((y : Dyadic) : ℝ))
    (h_ub : ((y : Dyadic) : ℝ) < (((c + 1 : ℤ) : ℝ)) * (2 : ℝ) ^ k) :
    False := by
  have h_2k_pos : (0 : ℝ) < (2 : ℝ)^k := zpow_pos (by norm_num) _
  have h_c_real_pos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc_pos
  have h_cxk_pos : (0 : ℝ) < (c : ℝ) * (2 : ℝ)^k := mul_pos h_c_real_pos h_2k_pos
  have hy_pos : 0 < ((y : Dyadic) : ℝ) := by linarith
  obtain ⟨k', c', hk'_ge, hc'_lt, hy_eq, hk'_max⟩ :=
    exists_grid_rep F hp he hp_y hq_y hy_pos
  -- Bound: log y ≤ k + p - 1.
  have h_y_lt_2pk : ((y : Dyadic) : ℝ) < (2 : ℝ)^(k + (p : ℤ)) := by
    have h_c1_le : ((c + 1 : ℤ) : ℝ) ≤ (2 : ℝ)^(p : ℤ) := by
      have h_int : c + 1 ≤ (2 : ℤ)^p := by omega
      have h_cast : ((c + 1 : ℤ) : ℝ) ≤ (((2 : ℤ)^p : ℤ) : ℝ) := by exact_mod_cast h_int
      rw [show (((2 : ℤ)^p : ℤ) : ℝ) = (2 : ℝ)^(p : ℤ) from by push_cast; rfl] at h_cast
      exact h_cast
    calc ((y : Dyadic) : ℝ)
        < ((c + 1 : ℤ) : ℝ) * (2 : ℝ)^k := h_ub
      _ ≤ (2 : ℝ)^(p : ℤ) * (2 : ℝ)^k :=
            mul_le_mul_of_nonneg_right h_c1_le (le_of_lt h_2k_pos)
      _ = (2 : ℝ)^(k + (p : ℤ)) := by
            rw [add_comm, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have h_log_y_le : Int.log 2 ((y : Dyadic) : ℝ) ≤ k + (p : ℤ) - 1 := by
    have h_y_lt_nat : ((y : Dyadic) : ℝ) < ((2 : ℕ) : ℝ)^(k + (p : ℤ)) := by
      rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) from by push_cast; rfl]
      exact h_y_lt_2pk
    have : Int.log 2 ((y : Dyadic) : ℝ) < k + (p : ℤ) :=
      (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) hy_pos).mp h_y_lt_nat
    omega
  have h_k'_le_k : k' ≤ k := by
    rw [hk'_max]
    exact max_le hk (by omega)
  -- Lower bound: log y ≥ log(c·2^k) ≥ k.
  have h_2k_le_cxk : ((2 : ℕ) : ℝ)^k ≤ (c : ℝ) * (2 : ℝ)^k := by
    rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) from by push_cast; rfl]
    have h_c_ge_1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc_pos
    calc (2 : ℝ)^k = 1 * (2 : ℝ)^k := by ring
      _ ≤ (c : ℝ) * (2 : ℝ)^k :=
            mul_le_mul_of_nonneg_right h_c_ge_1 (le_of_lt h_2k_pos)
  have h_log_cxk_ge_k : k ≤ Int.log 2 ((c : ℝ) * (2 : ℝ)^k) :=
    (Int.zpow_le_iff_le_log (by norm_num : 1 < (2 : ℕ)) h_cxk_pos).mp h_2k_le_cxk
  have h_log_y_ge : Int.log 2 ((c : ℝ) * (2 : ℝ)^k) ≤ Int.log 2 ((y : Dyadic) : ℝ) :=
    Int.log_mono_right h_cxk_pos (le_of_lt h_lb)
  have h_k'_ge_k : k' ≥ k := by
    rw [hk'_max]
    rcases eq_or_lt_of_le hk with hke | hke
    · rw [← hke]; exact le_max_left _ _
    · -- k > exp. From hk_max, k = log(c·2^k) - p + 1.
      have h_hk_form : k = Int.log 2 ((c : ℝ) * (2 : ℝ)^k) - (p : ℤ) + 1 := by
        by_cases h : exp ≤ Int.log 2 ((c : ℝ) * (2 : ℝ)^k) - (p : ℤ) + 1
        · have h_max_eq : max exp (Int.log 2 ((c : ℝ) * (2 : ℝ)^k) - (p : ℤ) + 1)
              = Int.log 2 ((c : ℝ) * (2 : ℝ)^k) - (p : ℤ) + 1 := max_eq_right h
          rw [h_max_eq] at hk_max
          exact hk_max
        · push Not at h
          have h_max_eq : max exp (Int.log 2 ((c : ℝ) * (2 : ℝ)^k) - (p : ℤ) + 1) = exp :=
            max_eq_left (le_of_lt h)
          rw [h_max_eq] at hk_max
          exact absurd hk_max.symm (ne_of_lt hke)
      -- log y ≥ log(c·2^k) = k + p - 1, so log y - p + 1 ≥ k.
      apply le_max_of_le_right
      omega
  have h_k'_eq : k' = k := le_antisymm h_k'_le_k h_k'_ge_k
  rw [h_k'_eq] at hy_eq
  -- y = c'·2^k. Combined with h_lb, h_ub: c < c' < c+1.
  have h_c'_gt_c : (c : ℝ) < (c' : ℝ) := by
    have : (c : ℝ) * (2 : ℝ)^k < (c' : ℝ) * (2 : ℝ)^k := hy_eq ▸ h_lb
    exact lt_of_mul_lt_mul_right this (le_of_lt h_2k_pos)
  have h_c'_lt_c1 : (c' : ℝ) < ((c + 1 : ℤ) : ℝ) := by
    have : (c' : ℝ) * (2 : ℝ)^k < ((c + 1 : ℤ) : ℝ) * (2 : ℝ)^k := hy_eq ▸ h_ub
    exact lt_of_mul_lt_mul_right this (le_of_lt h_2k_pos)
  have h_c'_int_gt : c < c' := by exact_mod_cast h_c'_gt_c
  have h_c'_int_lt : c' < c + 1 := by exact_mod_cast h_c'_lt_c1
  omega

/-- No F element lies strictly in `(c·2^k, (c+1)·2^k)` for the F.exp = ⊥ case.
Same argument as the finite-exp version, but k = log(c·2^k) - p + 1 (no max). -/
private theorem no_F_element_in_step_interval_exp_bot (F : AbstractFormat) {p : ℕ}
    (hp : F.p = (p : ℕ∞))
    {c : ℤ} (hc_pos : 0 < c) (hc_lt : c < (2 : ℤ) ^ p)
    {k : ℤ}
    (hk_eq : k = Int.log 2 ((c : ℝ) * (2 : ℝ) ^ k) - (p : ℤ) + 1)
    {y : Dyadic}
    (hp_y : Dyadic.precisionAtMost F.p y)
    (h_lb : ((c : ℝ)) * (2 : ℝ) ^ k < ((y : Dyadic) : ℝ))
    (h_ub : ((y : Dyadic) : ℝ) < (((c + 1 : ℤ) : ℝ)) * (2 : ℝ) ^ k) :
    False := by
  have h_2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
  have h_c_real_pos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc_pos
  have h_cxk_pos : (0 : ℝ) < (c : ℝ) * (2 : ℝ) ^ k := mul_pos h_c_real_pos h_2k_pos
  have hy_pos : 0 < ((y : Dyadic) : ℝ) := by linarith
  obtain ⟨k', c', hc'_lt, hy_eq, hk'_eq⟩ :=
    exists_grid_rep_exp_bot F hp hp_y hy_pos
  have h_y_lt_2pk : ((y : Dyadic) : ℝ) < (2 : ℝ) ^ (k + (p : ℤ)) := by
    have h_c1_le : ((c + 1 : ℤ) : ℝ) ≤ (2 : ℝ) ^ (p : ℤ) := by
      have h_int : c + 1 ≤ (2 : ℤ) ^ p := by omega
      have h_cast : ((c + 1 : ℤ) : ℝ) ≤ (((2 : ℤ) ^ p : ℤ) : ℝ) := by exact_mod_cast h_int
      rw [show (((2 : ℤ) ^ p : ℤ) : ℝ) = (2 : ℝ) ^ (p : ℤ) from by push_cast; rfl] at h_cast
      exact h_cast
    calc ((y : Dyadic) : ℝ)
        < ((c + 1 : ℤ) : ℝ) * (2 : ℝ) ^ k := h_ub
      _ ≤ (2 : ℝ) ^ (p : ℤ) * (2 : ℝ) ^ k :=
            mul_le_mul_of_nonneg_right h_c1_le (le_of_lt h_2k_pos)
      _ = (2 : ℝ) ^ (k + (p : ℤ)) := by
            rw [add_comm, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have h_log_y_le : Int.log 2 ((y : Dyadic) : ℝ) ≤ k + (p : ℤ) - 1 := by
    have h_y_lt_nat : ((y : Dyadic) : ℝ) < ((2 : ℕ) : ℝ) ^ (k + (p : ℤ)) := by
      rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) from by push_cast; rfl]
      exact h_y_lt_2pk
    have : Int.log 2 ((y : Dyadic) : ℝ) < k + (p : ℤ) :=
      (Int.lt_zpow_iff_log_lt (by norm_num : 1 < (2 : ℕ)) hy_pos).mp h_y_lt_nat
    omega
  have h_2k_le_cxk : ((2 : ℕ) : ℝ) ^ k ≤ (c : ℝ) * (2 : ℝ) ^ k := by
    rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) from by push_cast; rfl]
    have h_c_ge_1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc_pos
    calc (2 : ℝ) ^ k = 1 * (2 : ℝ) ^ k := by ring
      _ ≤ (c : ℝ) * (2 : ℝ) ^ k :=
            mul_le_mul_of_nonneg_right h_c_ge_1 (le_of_lt h_2k_pos)
  have h_log_cxk_ge_k : k ≤ Int.log 2 ((c : ℝ) * (2 : ℝ) ^ k) :=
    (Int.zpow_le_iff_le_log (by norm_num : 1 < (2 : ℕ)) h_cxk_pos).mp h_2k_le_cxk
  have h_log_y_ge : Int.log 2 ((c : ℝ) * (2 : ℝ) ^ k) ≤ Int.log 2 ((y : Dyadic) : ℝ) :=
    Int.log_mono_right h_cxk_pos (le_of_lt h_lb)
  -- k' = log y - p + 1.
  -- We have log(c·2^k) ≤ log y ≤ k+p-1, and log(c·2^k) = k+p-1 (from hk_eq).
  -- So log y = k+p-1, k' = k.
  have h_log_cxk_eq : Int.log 2 ((c : ℝ) * (2 : ℝ) ^ k) = k + (p : ℤ) - 1 := by
    omega
  have h_log_y_eq : Int.log 2 ((y : Dyadic) : ℝ) = k + (p : ℤ) - 1 := by
    omega
  have h_k'_eq : k' = k := by
    rw [hk'_eq]; omega
  rw [h_k'_eq] at hy_eq
  have h_c'_gt_c : (c : ℝ) < (c' : ℝ) := by
    have : (c : ℝ) * (2 : ℝ) ^ k < (c' : ℝ) * (2 : ℝ) ^ k := hy_eq ▸ h_lb
    exact lt_of_mul_lt_mul_right this (le_of_lt h_2k_pos)
  have h_c'_lt_c1 : (c' : ℝ) < ((c + 1 : ℤ) : ℝ) := by
    have : (c' : ℝ) * (2 : ℝ) ^ k < ((c + 1 : ℤ) : ℝ) * (2 : ℝ) ^ k := hy_eq ▸ h_ub
    exact lt_of_mul_lt_mul_right this (le_of_lt h_2k_pos)
  have h_c'_int_gt : c < c' := by exact_mod_cast h_c'_gt_c
  have h_c'_int_lt : c' < c + 1 := by exact_mod_cast h_c'_lt_c1
  omega

/-- The bound for the paper's `F⁺` containment: `next(F.b)` lifted to
`WithTop Dyadic`. Returns `⊤` when `F.b = ⊤`, otherwise `(F.next b : Dyadic)`. -/
noncomputable def boundAfterNext (F : AbstractFormat) : WithTop Dyadic :=
  match F.b with
  | ⊤ => ⊤
  | (b : Dyadic) => ((F.next b : Dyadic) : WithTop Dyadic)

/-- `b_nn` invariant for `F.boundAfterNext`: when finite, the bound is
non-negative, derived from `next_nonneg` and `F.b_nn`. -/
theorem boundAfterNext_nn (F : AbstractFormat) :
    ∀ d : Dyadic, F.boundAfterNext = ↑d → 0 ≤ ((d : Dyadic) : ℝ) := by
  intro d hd
  cases hF_b : F.b with
  | top =>
    -- F.b = ⊤ ⇒ boundAfterNext = ⊤. But hd says boundAfterNext = ↑d (finite).
    -- Contradiction.
    have : F.boundAfterNext = ⊤ := by unfold boundAfterNext; rw [hF_b]
    rw [this] at hd
    exact absurd hd (by simp)
  | coe b =>
    -- F.b = ↑b. boundAfterNext = ↑(F.next b). hd: ↑(F.next b) = ↑d ⇒ d = F.next b.
    have h_eq : F.boundAfterNext = ((F.next b : Dyadic) : WithTop Dyadic) := by
      unfold boundAfterNext; rw [hF_b]
    rw [h_eq] at hd
    have hd_eq : d = F.next b := by exact_mod_cast hd.symm
    rw [hd_eq]
    -- Need 0 ≤ F.next b. Use next_nonneg with hb : 0 ≤ b from F.b_nn.
    have hb : 0 ≤ ((b : Dyadic) : ℝ) := F.b_nn b hF_b
    exact next_nonneg F b hb

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

/-- F-adjacent step form: F-adjacent positive `y₁ < y₂ ∈ F` have
`y₁ = c·2^k`, `y₂ = (c+1)·2^k` where `(c, k)` is `y₁`'s grid rep. The exponent
`k = max(exp, ⌊log₂ y₁⌋ - p + 1)` is the F-grid step exponent at `y₁`. -/
theorem F_adjacent_step_form (F : AbstractFormat) {p : ℕ} {exp : ℤ}
    (hp : F.p = (p : ℕ∞)) (he : F.exp = (exp : WithBot ℤ))
    (hp_ge_1 : 1 ≤ p)
    {y₁ y₂ : Dyadic} (hy₁F : y₁ ∈ F) (hy₂F : y₂ ∈ F)
    (h_pos : 0 < ((y₁ : Dyadic) : ℝ))
    (h_lt : ((y₁ : Dyadic) : ℝ) < ((y₂ : Dyadic) : ℝ))
    (h_adj : ∀ y : Dyadic, y ∈ F →
              ((y₁ : Dyadic) : ℝ) < ((y : Dyadic) : ℝ) →
              ((y₂ : Dyadic) : ℝ) ≤ ((y : Dyadic) : ℝ)) :
    ∃ (k : ℤ) (c : ℤ),
      k ≥ exp ∧ 0 < c ∧ c < (2 : ℤ)^p ∧
      ((y₁ : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ)^k ∧
      ((y₂ : Dyadic) : ℝ) = ((c + 1 : ℤ) : ℝ) * (2 : ℝ)^k := by
  obtain ⟨hp_y₁, hq_y₁, hb_y₁⟩ := hy₁F
  obtain ⟨hp_y₂, hq_y₂, hb_y₂⟩ := hy₂F
  obtain ⟨k, c, hk, hc_lt, hy₁_eq, hk_max⟩ :=
    exists_grid_rep F hp he hp_y₁ hq_y₁ h_pos
  have hc_pos : 0 < c := grid_rep_c_pos h_pos hy₁_eq
  have hc_lt_int : c < (2 : ℤ)^p := by
    have habs : |c| = c := abs_of_pos hc_pos
    rw [← habs]; exact hc_lt
  refine ⟨k, c, hk, hc_pos, hc_lt_int, hy₁_eq, ?_⟩
  have h_2k_pos : (0 : ℝ) < (2 : ℝ)^k := zpow_pos (by norm_num) _
  have hk_max' : k = max exp (Int.log 2 ((c : ℝ) * (2 : ℝ)^k) - (p : ℤ) + 1) := by
    have h_log_eq : Int.log 2 ((y₁ : Dyadic) : ℝ) = Int.log 2 ((c : ℝ) * (2 : ℝ)^k) := by
      rw [hy₁_eq]
    rw [← h_log_eq]; exact hk_max
  -- Step 1: (c+1)·2^k ≤ y₂.
  have h_y₂_ge : ((c + 1 : ℤ) : ℝ) * (2 : ℝ)^k ≤ ((y₂ : Dyadic) : ℝ) := by
    by_contra h_lt2
    push Not at h_lt2
    have h_y₁_lt' : (c : ℝ) * (2 : ℝ)^k < ((y₂ : Dyadic) : ℝ) := hy₁_eq ▸ h_lt
    exact no_F_element_in_step_interval F hp he hc_pos hc_lt_int hk hk_max'
      hp_y₂ hq_y₂ h_y₁_lt' h_lt2
  -- Step 2: construct z = (c+1)·2^k as a Dyadic in F.
  set z : Dyadic := Dyadic.ofIntZpow (c + 1) k with hz_def
  have hz_eq : ((z : Dyadic) : ℝ) = ((c + 1 : ℤ) : ℝ) * (2 : ℝ)^k := by
    change ((Dyadic.ofIntZpow (c + 1) k : Dyadic) : ℝ) = _
    rw [Dyadic.coe_ofIntZpow]
  have hz_p : Dyadic.precisionAtMost F.p z := by
    rw [hp]
    apply Dyadic.precisionAtMost_of_abs_le hp_ge_1 (c + 1) k hz_eq
    have h_c1_pos : 0 < c + 1 := by omega
    rw [abs_of_pos h_c1_pos]
    omega
  have hz_q : Dyadic.quantumAtLeast F.exp z := by
    rw [he]
    rw [Dyadic.quantumAtLeast_coe]
    refine ⟨(c + 1) * (2 : ℤ)^(k - exp).toNat, ?_⟩
    rw [hz_eq]
    have h_diff_nn : 0 ≤ k - exp := by omega
    have h_eq_zpow : (2 : ℝ)^k = (2 : ℝ)^((k - exp).toNat : ℤ) * (2 : ℝ)^exp := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1
      rw [Int.toNat_of_nonneg h_diff_nn]; ring
    rw [h_eq_zpow, zpow_natCast]
    push_cast; ring
  have hz_b : boundOK F.b z := by
    cases hF_b : F.b with
    | top => trivial
    | coe b =>
      change |((z : Dyadic) : ℝ)| ≤ ((b : Dyadic) : ℝ)
      change boundOK F.b y₂ at hb_y₂
      rw [hF_b] at hb_y₂
      have hy₂_le_b : |((y₂ : Dyadic) : ℝ)| ≤ ((b : Dyadic) : ℝ) := hb_y₂
      have hz_pos : 0 < ((z : Dyadic) : ℝ) := by
        rw [hz_eq]
        have h_c1_pos : (0 : ℝ) < ((c + 1 : ℤ) : ℝ) := by
          have : 0 < c + 1 := by omega
          exact_mod_cast this
        exact mul_pos h_c1_pos h_2k_pos
      have hy₂_pos : 0 < ((y₂ : Dyadic) : ℝ) := lt_trans h_pos h_lt
      rw [abs_of_pos hz_pos]
      rw [abs_of_pos hy₂_pos] at hy₂_le_b
      have hz_le_y₂ : ((z : Dyadic) : ℝ) ≤ ((y₂ : Dyadic) : ℝ) := by
        rw [hz_eq]; exact h_y₂_ge
      linarith
  have hzF : z ∈ F := ⟨hz_p, hz_q, hz_b⟩
  -- Step 3: F-adjacency gives y₂ ≤ z = (c+1)·2^k.
  have h_z_gt_y₁ : ((y₁ : Dyadic) : ℝ) < ((z : Dyadic) : ℝ) := by
    rw [hy₁_eq, hz_eq]
    have : (c : ℝ) < ((c + 1 : ℤ) : ℝ) := by push_cast; linarith
    have h_2k_pos' : (0 : ℝ) < (2 : ℝ)^k := h_2k_pos
    nlinarith
  have h_y₂_le_z : ((y₂ : Dyadic) : ℝ) ≤ ((z : Dyadic) : ℝ) :=
    h_adj z hzF h_z_gt_y₁
  rw [hz_eq] at h_y₂_le_z
  linarith

/-- F-adjacent step form for `F.exp = ⊥`: F-adjacent positive `y₁ < y₂ ∈ F`
have `y₁ = c·2^k`, `y₂ = (c+1)·2^k` where `(c, k)` is `y₁`'s grid rep
(`k = ⌊log₂ y₁⌋ - p + 1`). -/
theorem F_adjacent_step_form_exp_bot (F : AbstractFormat) {p : ℕ}
    (hp : F.p = (p : ℕ∞)) (he : F.exp = ⊥)
    (hp_ge_1 : 1 ≤ p)
    {y₁ y₂ : Dyadic} (hy₁F : y₁ ∈ F) (hy₂F : y₂ ∈ F)
    (h_pos : 0 < ((y₁ : Dyadic) : ℝ))
    (h_lt : ((y₁ : Dyadic) : ℝ) < ((y₂ : Dyadic) : ℝ))
    (h_adj : ∀ y : Dyadic, y ∈ F →
              ((y₁ : Dyadic) : ℝ) < ((y : Dyadic) : ℝ) →
              ((y₂ : Dyadic) : ℝ) ≤ ((y : Dyadic) : ℝ)) :
    ∃ (k : ℤ) (c : ℤ),
      0 < c ∧ c < (2 : ℤ) ^ p ∧
      ((y₁ : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ) ^ k ∧
      ((y₂ : Dyadic) : ℝ) = ((c + 1 : ℤ) : ℝ) * (2 : ℝ) ^ k := by
  obtain ⟨hp_y₁, hq_y₁, hb_y₁⟩ := hy₁F
  obtain ⟨hp_y₂, hq_y₂, hb_y₂⟩ := hy₂F
  obtain ⟨k, c, hc_lt, hy₁_eq, hk_eq⟩ :=
    exists_grid_rep_exp_bot F hp hp_y₁ h_pos
  have hc_pos : 0 < c := grid_rep_c_pos h_pos hy₁_eq
  have hc_lt_int : c < (2 : ℤ) ^ p := by
    have habs : |c| = c := abs_of_pos hc_pos
    rw [← habs]; exact hc_lt
  refine ⟨k, c, hc_pos, hc_lt_int, hy₁_eq, ?_⟩
  have h_2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
  -- hk_eq has y₁ in it; convert to c·2^k.
  have hk_eq' : k = Int.log 2 ((c : ℝ) * (2 : ℝ) ^ k) - (p : ℤ) + 1 := by
    have h_log_eq : Int.log 2 ((y₁ : Dyadic) : ℝ) = Int.log 2 ((c : ℝ) * (2 : ℝ) ^ k) := by
      rw [hy₁_eq]
    rw [← h_log_eq]; exact hk_eq
  have h_y₂_ge : ((c + 1 : ℤ) : ℝ) * (2 : ℝ) ^ k ≤ ((y₂ : Dyadic) : ℝ) := by
    by_contra h_lt2
    push Not at h_lt2
    have h_y₁_lt' : (c : ℝ) * (2 : ℝ) ^ k < ((y₂ : Dyadic) : ℝ) := hy₁_eq ▸ h_lt
    exact no_F_element_in_step_interval_exp_bot F hp hc_pos hc_lt_int hk_eq'
      hp_y₂ h_y₁_lt' h_lt2
  set z : Dyadic := Dyadic.ofIntZpow (c + 1) k with hz_def
  have hz_eq : ((z : Dyadic) : ℝ) = ((c + 1 : ℤ) : ℝ) * (2 : ℝ) ^ k := by
    change ((Dyadic.ofIntZpow (c + 1) k : Dyadic) : ℝ) = _
    rw [Dyadic.coe_ofIntZpow]
  have hz_p : Dyadic.precisionAtMost F.p z := by
    rw [hp]
    apply Dyadic.precisionAtMost_of_abs_le hp_ge_1 (c + 1) k hz_eq
    have h_c1_pos : 0 < c + 1 := by omega
    rw [abs_of_pos h_c1_pos]; omega
  have hz_q : Dyadic.quantumAtLeast F.exp z := by
    rw [he]; trivial
  have hz_b : boundOK F.b z := by
    cases hF_b : F.b with
    | top => trivial
    | coe b =>
      change |((z : Dyadic) : ℝ)| ≤ ((b : Dyadic) : ℝ)
      change boundOK F.b y₂ at hb_y₂
      rw [hF_b] at hb_y₂
      have hy₂_le_b : |((y₂ : Dyadic) : ℝ)| ≤ ((b : Dyadic) : ℝ) := hb_y₂
      have hz_pos : 0 < ((z : Dyadic) : ℝ) := by
        rw [hz_eq]
        have h_c1_pos : (0 : ℝ) < ((c + 1 : ℤ) : ℝ) := by
          have : 0 < c + 1 := by omega
          exact_mod_cast this
        exact mul_pos h_c1_pos h_2k_pos
      have hy₂_pos : 0 < ((y₂ : Dyadic) : ℝ) := lt_trans h_pos h_lt
      rw [abs_of_pos hz_pos]
      rw [abs_of_pos hy₂_pos] at hy₂_le_b
      have hz_le_y₂ : ((z : Dyadic) : ℝ) ≤ ((y₂ : Dyadic) : ℝ) := by
        rw [hz_eq]; exact h_y₂_ge
      linarith
  have hzF : z ∈ F := ⟨hz_p, hz_q, hz_b⟩
  have h_z_gt_y₁ : ((y₁ : Dyadic) : ℝ) < ((z : Dyadic) : ℝ) := by
    rw [hy₁_eq, hz_eq]
    have : (c : ℝ) < ((c + 1 : ℤ) : ℝ) := by push_cast; linarith
    nlinarith
  have h_y₂_le_z : ((y₂ : Dyadic) : ℝ) ≤ ((z : Dyadic) : ℝ) :=
    h_adj z hzF h_z_gt_y₁
  rw [hz_eq] at h_y₂_le_z
  linarith

/-- Midpoint of F-adjacent values lies in `F.extend 1`. The midpoint computes
to `(2c+1)·2^(k-1)` where `(c, k)` is `y₁`'s grid rep and `y₂ = (c+1)·2^k`,
giving `|2c+1| < 2^(p+1)`, hence precision ≤ `p+1`. -/
theorem midpoint_mem_extend_one_of_F_adjacent_pos (F : AbstractFormat)
    {p : ℕ} {exp : ℤ}
    (hp : F.p = (p : ℕ∞)) (he : F.exp = (exp : WithBot ℤ))
    (hp_ge_1 : 1 ≤ p)
    {y₁ y₂ : Dyadic} (hy₁F : y₁ ∈ F) (hy₂F : y₂ ∈ F)
    (h_pos : 0 < ((y₁ : Dyadic) : ℝ))
    (h_lt : ((y₁ : Dyadic) : ℝ) < ((y₂ : Dyadic) : ℝ))
    (h_adj : ∀ y : Dyadic, y ∈ F →
              ((y₁ : Dyadic) : ℝ) < ((y : Dyadic) : ℝ) →
              ((y₂ : Dyadic) : ℝ) ≤ ((y : Dyadic) : ℝ)) :
    Dyadic.midpoint y₁ y₂ ∈ F.extend 1 := by
  obtain ⟨k, c, hk_ge_exp, hc_pos, hc_lt, hy₁_eq, hy₂_eq⟩ :=
    F_adjacent_step_form F hp he hp_ge_1 hy₁F hy₂F h_pos h_lt h_adj
  have h_2_ne : (2 : ℝ) ≠ 0 := by norm_num
  have h_2k_pos : (0 : ℝ) < (2 : ℝ)^k := zpow_pos (by norm_num) _
  have h_mid_eq : ((Dyadic.midpoint y₁ y₂ : Dyadic) : ℝ)
      = ((2*c + 1 : ℤ) : ℝ) * (2 : ℝ)^(k - 1) := by
    rw [Dyadic.coe_midpoint, hy₁_eq, hy₂_eq, zpow_sub₀ h_2_ne]
    push_cast; field_simp; ring
  refine ⟨?_, ?_, ?_⟩
  · -- precisionAtMost (F.p + 1) midpoint
    have h_p_extend : (F.extend 1).p = (((p + 1 : ℕ)) : ℕ∞) := by
      change F.p + 1 = _
      rw [hp]; push_cast; rfl
    rw [h_p_extend]
    apply Dyadic.precisionAtMost_of_abs_le (by omega : 1 ≤ p + 1) (2*c + 1) (k - 1)
        h_mid_eq
    have h_c1_pos : 0 < 2*c + 1 := by omega
    rw [abs_of_pos h_c1_pos]
    have h_pow : (2 : ℤ)^(p + 1) = 2 * (2 : ℤ)^p := by
      rw [pow_succ]; ring
    omega
  · -- quantumAtLeast (F.exp - 1) midpoint
    have h_exp_extend : (F.extend 1).exp = (((exp - 1 : ℤ)) : WithBot ℤ) := by
      change F.exp.map (· - (1 : ℤ)) = _
      rw [he]; rfl
    rw [h_exp_extend]
    change Dyadic.quantumAtLeast _ _
    rw [Dyadic.quantumAtLeast_coe]
    refine ⟨(2*c + 1) * (2 : ℤ)^(k - 1 - (exp - 1)).toNat, ?_⟩
    rw [h_mid_eq]
    have h_diff_nn : 0 ≤ k - 1 - (exp - 1) := by omega
    have h_eq_zpow : (2 : ℝ)^(k - 1) =
        (2 : ℝ)^((k - 1 - (exp - 1)).toNat : ℤ) * (2 : ℝ)^(exp - 1) := by
      rw [Int.toNat_of_nonneg h_diff_nn, ← zpow_add₀ h_2_ne]
      congr 1; omega
    rw [h_eq_zpow, zpow_natCast]; push_cast; ring
  · -- bound: |midpoint| ≤ b.
    change boundOK (F.extend 1).b _
    have h_b : (F.extend 1).b = F.b := rfl
    rw [h_b]
    cases hF_b : F.b with
    | top => trivial
    | coe b =>
      change |((Dyadic.midpoint y₁ y₂ : Dyadic) : ℝ)| ≤ ((b : Dyadic) : ℝ)
      rw [Dyadic.coe_midpoint]
      have hy₁_b := hy₁F.2.2
      have hy₂_b := hy₂F.2.2
      change boundOK F.b y₁ at hy₁_b
      change boundOK F.b y₂ at hy₂_b
      rw [hF_b] at hy₁_b hy₂_b
      have h1 : |((y₁ : Dyadic) : ℝ)| ≤ ((b : Dyadic) : ℝ) := hy₁_b
      have h2 : |((y₂ : Dyadic) : ℝ)| ≤ ((b : Dyadic) : ℝ) := hy₂_b
      have h_tri : |((y₁ : Dyadic) : ℝ) + ((y₂ : Dyadic) : ℝ)|
          ≤ |((y₁ : Dyadic) : ℝ)| + |((y₂ : Dyadic) : ℝ)| :=
        abs_add_le _ _
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith

/-- Midpoint lemma for F.exp = ⊥, positive case. Same as the finite-exp version
but quantum check is trivial. -/
theorem midpoint_mem_extend_one_of_F_adjacent_pos_exp_bot (F : AbstractFormat) {p : ℕ}
    (hp : F.p = (p : ℕ∞)) (he : F.exp = ⊥)
    (hp_ge_1 : 1 ≤ p)
    {y₁ y₂ : Dyadic} (hy₁F : y₁ ∈ F) (hy₂F : y₂ ∈ F)
    (h_pos : 0 < ((y₁ : Dyadic) : ℝ))
    (h_lt : ((y₁ : Dyadic) : ℝ) < ((y₂ : Dyadic) : ℝ))
    (h_adj : ∀ y : Dyadic, y ∈ F →
              ((y₁ : Dyadic) : ℝ) < ((y : Dyadic) : ℝ) →
              ((y₂ : Dyadic) : ℝ) ≤ ((y : Dyadic) : ℝ)) :
    Dyadic.midpoint y₁ y₂ ∈ F.extend 1 := by
  obtain ⟨k, c, hc_pos, hc_lt, hy₁_eq, hy₂_eq⟩ :=
    F_adjacent_step_form_exp_bot F hp he hp_ge_1 hy₁F hy₂F h_pos h_lt h_adj
  have h_2_ne : (2 : ℝ) ≠ 0 := by norm_num
  have h_2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
  have h_mid_eq : ((Dyadic.midpoint y₁ y₂ : Dyadic) : ℝ)
      = ((2 * c + 1 : ℤ) : ℝ) * (2 : ℝ) ^ (k - 1) := by
    rw [Dyadic.coe_midpoint, hy₁_eq, hy₂_eq, zpow_sub₀ h_2_ne]
    push_cast; field_simp; ring
  refine ⟨?_, ?_, ?_⟩
  · have h_p_extend : (F.extend 1).p = (((p + 1 : ℕ)) : ℕ∞) := by
      change F.p + 1 = _
      rw [hp]; push_cast; rfl
    rw [h_p_extend]
    apply Dyadic.precisionAtMost_of_abs_le (by omega : 1 ≤ p + 1) (2 * c + 1) (k - 1)
        h_mid_eq
    have h_c1_pos : 0 < 2 * c + 1 := by omega
    rw [abs_of_pos h_c1_pos]
    have h_pow : (2 : ℤ) ^ (p + 1) = 2 * (2 : ℤ) ^ p := by
      rw [pow_succ]; ring
    omega
  · -- F.extend 1 .exp = ⊥ (since F.exp = ⊥). Quantum trivial.
    change Dyadic.quantumAtLeast (F.exp.map (· - (1 : ℤ))) _
    rw [he]; trivial
  · change boundOK (F.extend 1).b _
    have h_b : (F.extend 1).b = F.b := rfl
    rw [h_b]
    cases hF_b : F.b with
    | top => trivial
    | coe b =>
      change |((Dyadic.midpoint y₁ y₂ : Dyadic) : ℝ)| ≤ ((b : Dyadic) : ℝ)
      rw [Dyadic.coe_midpoint]
      have hy₁_b := hy₁F.2.2
      have hy₂_b := hy₂F.2.2
      change boundOK F.b y₁ at hy₁_b
      change boundOK F.b y₂ at hy₂_b
      rw [hF_b] at hy₁_b hy₂_b
      have h1 : |((y₁ : Dyadic) : ℝ)| ≤ ((b : Dyadic) : ℝ) := hy₁_b
      have h2 : |((y₂ : Dyadic) : ℝ)| ≤ ((b : Dyadic) : ℝ) := hy₂_b
      have h_tri : |((y₁ : Dyadic) : ℝ) + ((y₂ : Dyadic) : ℝ)|
          ≤ |((y₁ : Dyadic) : ℝ)| + |((y₂ : Dyadic) : ℝ)| :=
        abs_add_le _ _
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith

/-- For `y ∈ F` (any F shape), `midpoint(0, y) = y/2 ∈ F.extend 1`.
Handles both `F.exp = ⊥` and `F.exp = (e : ℤ)` cases. -/
theorem half_mem_extend_one (F : AbstractFormat) {p : ℕ}
    (hp : F.p = (p : ℕ∞))
    {y : Dyadic} (hyF : y ∈ F) :
    (Dyadic.midpoint 0 y : Dyadic) ∈ F.extend 1 := by
  obtain ⟨hp_y, hq_y, hb_y⟩ := hyF
  have h_mid_eq : ((Dyadic.midpoint 0 y : Dyadic) : ℝ) = ((y : Dyadic) : ℝ) / 2 := by
    rw [Dyadic.coe_midpoint]
    push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · -- precisionAtMost (F.p + 1).
    change Dyadic.precisionAtMost (F.p + 1) _
    have h_p_le : F.p ≤ F.p + 1 := by
      cases F.p with
      | top => simp
      | coe n => exact WithTop.coe_le_coe.mpr (Nat.le_succ n)
    apply Dyadic.precisionAtMost_mono h_p_le
    rw [hp]
    rw [hp] at hp_y
    rw [Dyadic.precisionAtMost_coe] at hp_y ⊢
    obtain ⟨c, e, hy_eq, hc_lt⟩ := hp_y
    refine ⟨c, e - 1, ?_, hc_lt⟩
    rw [h_mid_eq, hy_eq, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    field_simp
  · -- quantumAtLeast ((F.exp).map (· - 1)).
    change Dyadic.quantumAtLeast ((F.exp).map (· - 1)) _
    cases hF_exp : F.exp with
    | bot =>
      -- F.exp = ⊥ ⟹ map result is ⊥. Trivial.
      simp [Dyadic.quantumAtLeast]
    | coe e =>
      change Dyadic.quantumAtLeast ((e - 1 : ℤ) : WithBot ℤ) _
      rw [Dyadic.quantumAtLeast_coe]
      rw [hF_exp] at hq_y
      rw [Dyadic.quantumAtLeast_coe] at hq_y
      obtain ⟨c, hy_eq⟩ := hq_y
      refine ⟨c, ?_⟩
      rw [h_mid_eq, hy_eq, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
      field_simp
  · -- bound: |y/2| ≤ b.
    change boundOK (F.extend 1).b _
    have h_b : (F.extend 1).b = F.b := rfl
    rw [h_b]
    cases hF_b : F.b with
    | top => trivial
    | coe b =>
      change |((Dyadic.midpoint 0 y : Dyadic) : ℝ)| ≤ ((b : Dyadic) : ℝ)
      rw [h_mid_eq]
      change boundOK F.b y at hb_y
      rw [hF_b] at hb_y
      have h_b_nn : 0 ≤ ((b : Dyadic) : ℝ) := F.b_nn b hF_b
      have hy_le : |((y : Dyadic) : ℝ)| ≤ ((b : Dyadic) : ℝ) := hb_y
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith

/-- Midpoint of F-adjacent values (general — both signs handled).

For `y₁ < y₂` F-adjacent in `F`, `midpoint y₁ y₂ ∈ F.extend 1`. The proof
case-splits on the sign of `y₁`:
- `y₁ > 0`: positive case (`midpoint_mem_extend_one_of_F_adjacent_pos`).
- `y₁ = 0`: midpoint is `y₂/2`, handled by `half_mem_extend_one`.
- `y₁ < 0` and `y₂ ≤ 0`: negate, apply positive case to `(-y₂, -y₁)`, then negate back.
- `y₁ < 0 < y₂`: ruled out by F-adjacency since `0 ∈ F`. -/
theorem midpoint_mem_extend_one_of_F_adjacent (F : AbstractFormat) {p : ℕ} {exp : ℤ}
    (hp : F.p = (p : ℕ∞)) (he : F.exp = (exp : WithBot ℤ))
    (hp_ge_1 : 1 ≤ p)
    {y₁ y₂ : Dyadic} (hy₁F : y₁ ∈ F) (hy₂F : y₂ ∈ F)
    (h_lt : ((y₁ : Dyadic) : ℝ) < ((y₂ : Dyadic) : ℝ))
    (h_adj : ∀ y : Dyadic, y ∈ F →
              ((y₁ : Dyadic) : ℝ) < ((y : Dyadic) : ℝ) →
              ((y₂ : Dyadic) : ℝ) ≤ ((y : Dyadic) : ℝ)) :
    Dyadic.midpoint y₁ y₂ ∈ F.extend 1 := by
  rcases lt_trichotomy ((y₁ : Dyadic) : ℝ) 0 with hy₁_neg | hy₁_zero | hy₁_pos
  · -- y₁ < 0. Either y₂ < 0 or y₂ = 0 or y₂ > 0.
    rcases lt_trichotomy ((y₂ : Dyadic) : ℝ) 0 with hy₂_neg | hy₂_zero | hy₂_pos
    · -- Both negative. Apply positive case to (-y₂, -y₁).
      have h_neg_y₁_pos : 0 < ((-y₁ : Dyadic) : ℝ) := by push_cast; linarith
      have h_neg_y₂_pos : 0 < ((-y₂ : Dyadic) : ℝ) := by push_cast; linarith
      have h_lt' : ((-y₂ : Dyadic) : ℝ) < ((-y₁ : Dyadic) : ℝ) := by
        push_cast; linarith
      have h_adj' : ∀ y : Dyadic, y ∈ F →
          ((-y₂ : Dyadic) : ℝ) < ((y : Dyadic) : ℝ) →
          ((-y₁ : Dyadic) : ℝ) ≤ ((y : Dyadic) : ℝ) := by
        intro y hyF hyg
        by_contra h_lt_neg
        push Not at h_lt_neg
        have h_neg_yF : -y ∈ F := F.neg_mem hyF
        have h_y_gt_y₁ : ((y₁ : Dyadic) : ℝ) < ((-y : Dyadic) : ℝ) := by
          push_cast at h_lt_neg ⊢; linarith
        have h_y_le_y₂ := h_adj (-y) h_neg_yF h_y_gt_y₁
        push_cast at hyg h_y_le_y₂
        linarith
      have h_neg_in_extend := midpoint_mem_extend_one_of_F_adjacent_pos
        F hp he hp_ge_1 (F.neg_mem hy₂F) (F.neg_mem hy₁F) h_neg_y₂_pos h_lt' h_adj'
      -- midpoint(-y₂, -y₁) = -midpoint(y₁, y₂).
      have h_mid_neg : Dyadic.midpoint (-y₂) (-y₁) = -(Dyadic.midpoint y₁ y₂) := by
        apply Subtype.ext
        change ((Dyadic.midpoint (-y₂) (-y₁) : Dyadic) : ℝ) =
          ((-(Dyadic.midpoint y₁ y₂) : Dyadic) : ℝ)
        rw [Dyadic.coe_midpoint]
        push_cast
        rw [Dyadic.coe_midpoint]
        ring
      rw [h_mid_neg] at h_neg_in_extend
      have := (F.extend 1).neg_mem h_neg_in_extend
      rw [neg_neg] at this
      exact this
    · -- y₂ = 0. midpoint(y₁, 0) = y₁/2. Apply half_mem_extend_one to -y₁.
      have h_y₂_eq_0 : y₂ = 0 := Subtype.ext (by rw [hy₂_zero]; rfl)
      rw [h_y₂_eq_0]
      -- midpoint y₁ 0 = -(midpoint 0 (-y₁))
      have h_mid_eq : Dyadic.midpoint y₁ 0 = -(Dyadic.midpoint 0 (-y₁)) := by
        apply Subtype.ext
        rw [Dyadic.coe_midpoint]
        push_cast
        rw [Dyadic.coe_midpoint]
        push_cast; ring
      rw [h_mid_eq]
      have h_neg_y₁F : -y₁ ∈ F := F.neg_mem hy₁F
      have h_half := half_mem_extend_one F hp h_neg_y₁F
      have := (F.extend 1).neg_mem h_half
      exact this
    · -- y₁ < 0 < y₂: F-adjacency violated since 0 ∈ F.
      exfalso
      have h_0_F : (0 : Dyadic) ∈ F := F.zero_mem
      have h_0_gt : ((y₁ : Dyadic) : ℝ) < ((0 : Dyadic) : ℝ) := by
        rw [show ((0 : Dyadic) : ℝ) = 0 from rfl]; exact hy₁_neg
      have h_y₂_le : ((y₂ : Dyadic) : ℝ) ≤ ((0 : Dyadic) : ℝ) :=
        h_adj 0 h_0_F h_0_gt
      rw [show ((0 : Dyadic) : ℝ) = 0 from rfl] at h_y₂_le
      linarith
  · -- y₁ = 0. midpoint = y₂/2 = midpoint 0 y₂.
    have h_y₁_eq_0 : y₁ = 0 := by
      apply Subtype.ext
      rw [hy₁_zero]; rfl
    rw [h_y₁_eq_0]
    exact half_mem_extend_one F hp hy₂F
  · -- y₁ > 0.
    exact midpoint_mem_extend_one_of_F_adjacent_pos
      F hp he hp_ge_1 hy₁F hy₂F hy₁_pos h_lt h_adj

/-- General signed midpoint lemma for F.exp = ⊥, F.p finite. Same dispatch
structure as `midpoint_mem_extend_one_of_F_adjacent` but using the
`_exp_bot` positive case. -/
theorem midpoint_mem_extend_one_of_F_adjacent_exp_bot (F : AbstractFormat) {p : ℕ}
    (hp : F.p = (p : ℕ∞)) (he : F.exp = ⊥)
    (hp_ge_1 : 1 ≤ p)
    {y₁ y₂ : Dyadic} (hy₁F : y₁ ∈ F) (hy₂F : y₂ ∈ F)
    (h_lt : ((y₁ : Dyadic) : ℝ) < ((y₂ : Dyadic) : ℝ))
    (h_adj : ∀ y : Dyadic, y ∈ F →
              ((y₁ : Dyadic) : ℝ) < ((y : Dyadic) : ℝ) →
              ((y₂ : Dyadic) : ℝ) ≤ ((y : Dyadic) : ℝ)) :
    Dyadic.midpoint y₁ y₂ ∈ F.extend 1 := by
  rcases lt_trichotomy ((y₁ : Dyadic) : ℝ) 0 with hy₁_neg | hy₁_zero | hy₁_pos
  · rcases lt_trichotomy ((y₂ : Dyadic) : ℝ) 0 with hy₂_neg | hy₂_zero | hy₂_pos
    · have h_neg_y₁_pos : 0 < ((-y₁ : Dyadic) : ℝ) := by push_cast; linarith
      have h_neg_y₂_pos : 0 < ((-y₂ : Dyadic) : ℝ) := by push_cast; linarith
      have h_lt' : ((-y₂ : Dyadic) : ℝ) < ((-y₁ : Dyadic) : ℝ) := by
        push_cast; linarith
      have h_adj' : ∀ y : Dyadic, y ∈ F →
          ((-y₂ : Dyadic) : ℝ) < ((y : Dyadic) : ℝ) →
          ((-y₁ : Dyadic) : ℝ) ≤ ((y : Dyadic) : ℝ) := by
        intro y hyF hyg
        by_contra h_lt_neg
        push Not at h_lt_neg
        have h_neg_yF : -y ∈ F := F.neg_mem hyF
        have h_y_gt_y₁ : ((y₁ : Dyadic) : ℝ) < ((-y : Dyadic) : ℝ) := by
          push_cast at h_lt_neg ⊢; linarith
        have h_y_le_y₂ := h_adj (-y) h_neg_yF h_y_gt_y₁
        push_cast at hyg h_y_le_y₂
        linarith
      have h_neg_in_extend := midpoint_mem_extend_one_of_F_adjacent_pos_exp_bot
        F hp he hp_ge_1 (F.neg_mem hy₂F) (F.neg_mem hy₁F) h_neg_y₂_pos h_lt' h_adj'
      have h_mid_neg : Dyadic.midpoint (-y₂) (-y₁) = -(Dyadic.midpoint y₁ y₂) := by
        apply Subtype.ext
        change ((Dyadic.midpoint (-y₂) (-y₁) : Dyadic) : ℝ) =
          ((-(Dyadic.midpoint y₁ y₂) : Dyadic) : ℝ)
        rw [Dyadic.coe_midpoint]
        push_cast
        rw [Dyadic.coe_midpoint]
        ring
      rw [h_mid_neg] at h_neg_in_extend
      have := (F.extend 1).neg_mem h_neg_in_extend
      rw [neg_neg] at this
      exact this
    · have h_y₂_eq_0 : y₂ = 0 := Subtype.ext (by rw [hy₂_zero]; rfl)
      rw [h_y₂_eq_0]
      have h_mid_eq : Dyadic.midpoint y₁ 0 = -(Dyadic.midpoint 0 (-y₁)) := by
        apply Subtype.ext
        rw [Dyadic.coe_midpoint]
        push_cast
        rw [Dyadic.coe_midpoint]
        push_cast; ring
      rw [h_mid_eq]
      have h_neg_y₁F : -y₁ ∈ F := F.neg_mem hy₁F
      have h_half := half_mem_extend_one F hp h_neg_y₁F
      have := (F.extend 1).neg_mem h_half
      exact this
    · exfalso
      have h_0_F : (0 : Dyadic) ∈ F := F.zero_mem
      have h_0_gt : ((y₁ : Dyadic) : ℝ) < ((0 : Dyadic) : ℝ) := by
        rw [show ((0 : Dyadic) : ℝ) = 0 from rfl]; exact hy₁_neg
      have h_y₂_le : ((y₂ : Dyadic) : ℝ) ≤ ((0 : Dyadic) : ℝ) :=
        h_adj 0 h_0_F h_0_gt
      rw [show ((0 : Dyadic) : ℝ) = 0 from rfl] at h_y₂_le
      linarith
  · have h_y₁_eq_0 : y₁ = 0 := by
      apply Subtype.ext
      rw [hy₁_zero]; rfl
    rw [h_y₁_eq_0]
    exact half_mem_extend_one F hp hy₂F
  · exact midpoint_mem_extend_one_of_F_adjacent_pos_exp_bot
      F hp he hp_ge_1 hy₁F hy₂F hy₁_pos h_lt h_adj

/-- For `F.p = ⊤` and `F.exp` finite, midpoint of any two F-elements lies in
`F.extend 1`. F-adjacency isn't required since precision is unrestricted. -/
theorem midpoint_mem_extend_one_of_p_top (F : AbstractFormat) {exp : ℤ}
    (hp : F.p = ⊤) (he : F.exp = (exp : WithBot ℤ))
    {y₁ y₂ : Dyadic} (hy₁F : y₁ ∈ F) (hy₂F : y₂ ∈ F) :
    Dyadic.midpoint y₁ y₂ ∈ F.extend 1 := by
  obtain ⟨_, hq_y₁, hb_y₁⟩ := hy₁F
  obtain ⟨_, hq_y₂, hb_y₂⟩ := hy₂F
  refine ⟨?_, ?_, ?_⟩
  · -- precision: F.extend 1.p = ⊤. Trivial.
    change Dyadic.precisionAtMost (F.p + 1) _
    have h_p_top : F.p + 1 = ⊤ := by rw [hp]; rfl
    rw [h_p_top]; trivial
  · -- quantum: midpoint at quantum exp - 1.
    change Dyadic.quantumAtLeast ((F.exp).map (· - 1)) _
    have h_exp_map : F.exp.map (· - (1 : ℤ)) = ((exp - 1 : ℤ) : WithBot ℤ) := by
      rw [he]; rfl
    rw [h_exp_map]
    change Dyadic.quantumAtLeast _ _
    rw [Dyadic.quantumAtLeast_coe]
    rw [he, Dyadic.quantumAtLeast_coe] at hq_y₁ hq_y₂
    obtain ⟨c₁, hc₁⟩ := hq_y₁
    obtain ⟨c₂, hc₂⟩ := hq_y₂
    refine ⟨c₁ + c₂, ?_⟩
    rw [Dyadic.coe_midpoint, hc₁, hc₂]
    have h_2_ne : (2 : ℝ) ≠ 0 := by norm_num
    push_cast
    rw [zpow_sub₀ h_2_ne]
    field_simp
  · -- bound: |midpoint| ≤ b.
    change boundOK (F.extend 1).b _
    have h_b : (F.extend 1).b = F.b := rfl
    rw [h_b]
    cases hF_b : F.b with
    | top => trivial
    | coe b =>
      change |((Dyadic.midpoint y₁ y₂ : Dyadic) : ℝ)| ≤ ((b : Dyadic) : ℝ)
      rw [Dyadic.coe_midpoint]
      change boundOK F.b y₁ at hb_y₁
      change boundOK F.b y₂ at hb_y₂
      rw [hF_b] at hb_y₁ hb_y₂
      have h1 : |((y₁ : Dyadic) : ℝ)| ≤ ((b : Dyadic) : ℝ) := hb_y₁
      have h2 : |((y₂ : Dyadic) : ℝ)| ≤ ((b : Dyadic) : ℝ) := hb_y₂
      have h_tri : |((y₁ : Dyadic) : ℝ) + ((y₂ : Dyadic) : ℝ)|
          ≤ |((y₁ : Dyadic) : ℝ)| + |((y₂ : Dyadic) : ℝ)| := abs_add_le _ _
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith

end AbstractFormat

end Mpfx
