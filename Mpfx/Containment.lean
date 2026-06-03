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

/-- `(F.extend 1).extend 1 ⊆ F.extend 2` via precision/quantum equivalence.
The core is `(p+1)+1 = p+2`, `(exp-1)-1 = exp-2`, same bound. -/
theorem extend_one_extend_one_subset_extend_two (F : Format) :
    (F.extend 1).extend 1 ⊆ F.extend 2 := by
  intro y hy
  obtain ⟨hp, hq, hb⟩ := hy
  refine ⟨?_, ?_, hb⟩
  · -- precisionAtMost ((F.p.map (·+1)).map (·+1)) y → precisionAtMost (F.p.map (·+2)) y.
    change Dyadic.precisionAtMost (F.p.map (· + (2 : ℕ+))) y
    change Dyadic.precisionAtMost ((F.p.map (· + (1 : ℕ+))).map (· + (1 : ℕ+))) y at hp
    have h_eq : (F.p.map (· + (1 : ℕ+))).map (· + (1 : ℕ+)) = F.p.map (· + (2 : ℕ+)) := by
      cases F.p with
      | top => rfl
      | coe n =>
        rw [WithTop.map_coe, WithTop.map_coe, WithTop.map_coe]
        rw [show n + 1 + 1 = n + 2 from PNat.coe_injective (by push_cast; ring)]
    rw [h_eq] at hp; exact hp
  · -- quantumAtLeast ((F.exp.map (·-1)).map (·-1)) y → quantumAtLeast (F.exp.map (·-2)) y.
    change Dyadic.quantumAtLeast (F.exp.map (· - (2 : ℤ))) y
    change Dyadic.quantumAtLeast ((F.exp.map (· - (1 : ℤ))).map (· - (1 : ℤ))) y at hq
    have h_eq : (F.exp.map (· - (1 : ℤ))).map (· - (1 : ℤ)) = F.exp.map (· - (2 : ℤ)) := by
      cases F.exp with
      | bot => rfl
      | coe e =>
        rw [WithBot.map_coe, WithBot.map_coe, WithBot.map_coe]
        congr 1
        ring
    rw [h_eq] at hq; exact hq

/-- A `Dyadic` not representable in 1 bit cannot live in a format with
`F.p = 1`. Combined with `ℕ+`'s positivity, having a precision-2 witness in
`F` forces `F.p ≥ 2`. -/
theorem two_le_p_of_precision_two_witness {F : Format} {v : Dyadic}
    (hvF : v ∈ F) (hv_not_p1 : ¬ Dyadic.precisionAtMost ((1 : ℕ+) : WithTop ℕ+) v) :
    ((2 : ℕ+) : WithTop ℕ+) ≤ F.p := by
  by_contra h_p_lt
  push Not at h_p_lt
  have h_F_p_eq_1 : F.p = ((1 : ℕ+) : WithTop ℕ+) := by
    rcases hpf : F.p with _ | n
    · exfalso; rw [hpf] at h_p_lt; exact not_top_lt h_p_lt
    · rw [hpf] at h_p_lt
      have hn_lt : n < (2 : ℕ+) := WithTop.coe_lt_coe.mp h_p_lt
      have hn_eq : n = (1 : ℕ+) := by
        have h2 : (n : ℕ) < 2 := by exact_mod_cast hn_lt
        have h3 : (1 : ℕ) ≤ (n : ℕ) := n.one_le
        apply PNat.coe_injective
        rw [PNat.one_coe]; omega
      rw [hn_eq]; rfl
  have hv_p_F : Dyadic.precisionAtMost F.p v := hvF.1
  rw [h_F_p_eq_1] at hv_p_F
  exact hv_not_p1 hv_p_F

/-! ### Bound replacement and the `next` operator

`F.withBound b'` swaps out `F`'s magnitude bound for `b'`. `F.next b` is the
paper's `next_{F.p, F.exp}(b)` from §5.2 / Fig. 9: the smallest Dyadic in the
grid `A(F.p, F.exp, ∞)` strictly above `b`. -/

/-- Replace `F`'s bound with `b'`, keeping precision and quantum. No
non-negativity witness is needed: `NonNegDyadic` already carries `0 ≤ d`. -/
def withBound (F : Format) (b' : WithTop NonNegDyadic) : Format := { F with b := b' }

@[simp] theorem withBound_p (F : Format) (b' : WithTop NonNegDyadic) :
    (F.withBound b').p = F.p := rfl

@[simp] theorem withBound_exp (F : Format) (b' : WithTop NonNegDyadic) :
    (F.withBound b').exp = F.exp := rfl

@[simp] theorem withBound_b (F : Format) (b' : WithTop NonNegDyadic) :
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

For `F.exp = ⊥` with `F.p = (p : ℕ+)` and `b > 0`: there is no quantum, so
the step is purely binade-dependent: `2^(⌊log₂ b⌋ − F.p + 1)`. For `b ≤ 0`
the grid has positive elements of arbitrarily small magnitude, so no
successor exists; `b + 1` is returned as a junk value (only the `b > 0`
case is meaningful). The doubly-unbounded `(⊤, ⊥)` arm is excluded by
`FiniteFormat`. -/
noncomputable def next (F : Format) (b : Dyadic) : Dyadic :=
  match F.exp, F.p with
  | (e : ℤ), ((p : ℕ+) : WithTop ℕ+) =>
    if (b : ℝ) ≤ 0 then
      Dyadic.ofIntZpow 1 e
    else
      let logB : ℤ := Int.log 2 ((b : Dyadic) : ℝ)
      let stepExp : ℤ := max e (logB - ((p : ℕ) : ℤ) + 1)
      b + Dyadic.ofIntZpow 1 stepExp
  | (e : ℤ), ⊤ => b + Dyadic.ofIntZpow 1 e
  | ⊥, ((p : ℕ+) : WithTop ℕ+) =>
    if (b : ℝ) ≤ 0 then
      b + 1
    else
      b + Dyadic.ofIntZpow 1 (Int.log 2 ((b : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1)
  | ⊥, ⊤ => b + 1

/-- `F.next b > b` for finite `(F.p, F.exp)` and `b ≥ 0`. -/
theorem lt_next_of_finite (F : Format) {e : ℤ} {p : ℕ+}
    (he : F.exp = (e : WithBot ℤ)) (hp : F.p = ((p : ℕ+) : WithTop ℕ+)) (b : Dyadic)
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
      else b + Dyadic.ofIntZpow 1 (max e (Int.log 2 ((b : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1)) := by
    unfold next; rw [he, hp]
  rw [h_next_eq]
  by_cases h : ((b : Dyadic) : ℝ) ≤ 0
  · rw [if_pos h]
    have hb_zero : ((b : Dyadic) : ℝ) = 0 := le_antisymm h hb
    rw [hb_zero]
    exact h_step_pos e
  · rw [if_neg h]
    push_cast
    have := h_step_pos (max e (Int.log 2 ((b : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1))
    linarith

/-- `F.next b > b` for `F.p = ⊤` and `F.exp = (e : ℤ)`. -/
theorem lt_next_of_p_top (F : Format) {e : ℤ}
    (he : F.exp = (e : WithBot ℤ)) (hp : F.p = ⊤) (b : Dyadic) :
    (b : ℝ) < (F.next b : ℝ) := by
  have h_step_pos : (0 : ℝ) < ((Dyadic.ofIntZpow 1 e : Dyadic) : ℝ) := by
    rw [Dyadic.coe_ofIntZpow]
    have h2 : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
    push_cast; linarith
  have h_next_eq : F.next b = b + Dyadic.ofIntZpow 1 e := by
    -- After unfolding `next` and rewriting via `he, hp`, the goal contains
    -- `match (some e), ⊤ with ...`. The match doesn't auto-reduce because
    -- `⊤ : WithTop ℕ+` doesn't syntactically match the `none` constructor. We
    -- rewrite `⊤` to `none` explicitly via the `Top` instance.
    have hp' : F.p = (none : WithTop ℕ+) := hp
    unfold next
    rw [he, hp']
  rw [h_next_eq]; push_cast; linarith

/-- Computed form of `next` for `F.exp = ⊥, F.p = ⊤` (junk arm: excluded by
`FiniteFormat`). -/
theorem next_eq_bot_p_top' (F : Format) (he : F.exp = ⊥) (hp : F.p = ⊤)
    (b : Dyadic) : F.next b = b + 1 := by
  have hp' : F.p = (none : WithTop ℕ+) := hp
  unfold next
  rw [he, hp']

/-- Computed form of `next` for `F.exp = ⊥, b ≤ 0` (junk arm: no grid
successor exists). -/
theorem next_eq_bot_nonpos (F : Format) (he : F.exp = ⊥) {b : Dyadic}
    (hb : ((b : Dyadic) : ℝ) ≤ 0) : F.next b = b + 1 := by
  cases hp : F.p with
  | top => exact next_eq_bot_p_top' F he hp b
  | coe p =>
    have h_eq : F.next b =
        if ((b : Dyadic) : ℝ) ≤ 0 then b + 1
        else b + Dyadic.ofIntZpow 1
          (Int.log 2 ((b : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1) := by
      unfold next; rw [he, hp]
    rw [h_eq, if_pos hb]

/-- Computed form of `next` for `F.exp = ⊥, F.p = (p : ℕ+), b > 0`: the
step is purely binade-dependent. -/
theorem next_eq_bot_pos (F : Format) {p : ℕ+} (he : F.exp = ⊥)
    (hp : F.p = ((p : ℕ+) : WithTop ℕ+)) {b : Dyadic}
    (hb_pos : 0 < ((b : Dyadic) : ℝ)) :
    F.next b
      = b + Dyadic.ofIntZpow 1 (Int.log 2 ((b : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1) := by
  have h_eq : F.next b =
      if ((b : Dyadic) : ℝ) ≤ 0 then b + 1
      else b + Dyadic.ofIntZpow 1
        (Int.log 2 ((b : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1) := by
    unfold next; rw [he, hp]
  rw [h_eq, if_neg (not_le.mpr hb_pos)]

/-- `F.next b > b` for `F.exp = ⊥` (all `F.p` shapes, any `b`). -/
theorem lt_next_of_bot (F : Format) (he : F.exp = ⊥) (b : Dyadic) :
    ((b : Dyadic) : ℝ) < ((F.next b : Dyadic) : ℝ) := by
  cases hp : F.p with
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
      have h2 : (0 : ℝ) < (2 : ℝ) ^ (Int.log 2 ((b : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1) :=
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

/-- Computed form of `next` for `F.exp = (e : ℤ), F.p = (p : ℕ+), b > 0`. -/
theorem next_eq_finite_pos (F : Format) {e : ℤ} {p : ℕ+}
    (he : F.exp = (e : WithBot ℤ)) (hp : F.p = ((p : ℕ+) : WithTop ℕ+))
    {b : Dyadic} (hb_pos : 0 < ((b : Dyadic) : ℝ)) :
    F.next b =
      b + Dyadic.ofIntZpow 1
        (max e (Int.log 2 ((b : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1)) := by
  have h_eq : F.next b =
      if ((b : Dyadic) : ℝ) ≤ 0 then Dyadic.ofIntZpow 1 e
      else b + Dyadic.ofIntZpow 1
        (max e (Int.log 2 ((b : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1)) := by
    unfold next; rw [he, hp]
  rw [h_eq, if_neg (not_le.mpr hb_pos)]

/-- Computed form of `next` for `F.exp = (e : ℤ), F.p = ⊤`. -/
theorem next_eq_p_top (F : Format) {e : ℤ}
    (he : F.exp = (e : WithBot ℤ)) (hp : F.p = ⊤) (b : Dyadic) :
    F.next b = b + Dyadic.ofIntZpow 1 e := by
  have hp' : F.p = (none : WithTop ℕ+) := hp
  unfold next
  rw [he, hp']

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

`next(F.b)` lifted to `WithTop NonNegDyadic`. Returns `⊤` when `F.b = ⊤`,
otherwise `(F.next b : NonNegDyadic)`. The non-negativity witness is carried by
`NonNegDyadic` itself (no separate obligation), and `withBound` takes only the
bound. -/

/-- The bound for the paper's `F⁺` containment: `next(F.b)` lifted to
`WithTop NonNegDyadic`. -/
noncomputable def boundAfterNext (F : Format) : WithTop NonNegDyadic :=
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
theorem boundAfterNext_coe {F : Format} {b : NonNegDyadic} (hF : F.b = (b : WithTop NonNegDyadic)) :
    ∃ h, F.boundAfterNext = ((⟨F.next b.val, h⟩ : NonNegDyadic) : WithTop NonNegDyadic) := by
  unfold boundAfterNext; rw [hF]; exact ⟨_, rfl⟩

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
      change F.p.map (· + k) ≠ ⊤
      cases hF : F.p with
      | top => exact absurd hF hp
      | coe n => rw [WithTop.map_coe]; exact WithTop.coe_ne_top
    · right
      change F.exp.map (· - (k : ℤ)) ≠ ⊥
      cases hF : F.exp with
      | bot => exact absurd hF he
      | coe e => rw [WithBot.map_coe]; exact WithBot.coe_ne_bot

@[simp] theorem extend_toFormat (F : FiniteFormat) (k : ℕ+) :
    (F.extend k).toFormat = F.toFormat.extend k := rfl

/-- **Lemma 5.2**: extending `F` by `k` increases the digit count of every
nonzero `x` by exactly `k`. -/
theorem numDigits_extend (F : FiniteFormat) (k : ℕ+) {x : ℝ} (hx : x ≠ 0) :
    (F.extend k).numDigits x = F.numDigits x + k := by
  have hp_ext : (F.extend k).p = F.p.map (· + k) := rfl
  have he_ext : (F.extend k).exp = F.exp.map (· - (k : ℤ)) := rfl
  cases hp : F.p with
  | top =>
    cases hexp : F.exp with
    | bot =>
      exfalso; rcases F.finite with h | h
      · exact h hp
      · exact h hexp
    | coe e' =>
      have hpe : (F.extend k).p = ⊤ := by rw [hp_ext, hp]; rfl
      have hee : (F.extend k).exp = ((e' - (k : ℤ) : ℤ) : WithBot ℤ) := by
        rw [he_ext, hexp, WithBot.map_coe]
      rw [F.numDigits_top_coe hx hexp hp,
          (F.extend k).numDigits_top_coe hx hee hpe]
      ring
  | coe n =>
    cases hexp : F.exp with
    | bot =>
      have hpe : (F.extend k).p = (((n + k : ℕ+)) : WithTop ℕ+) := by
        rw [hp_ext, hp, WithTop.map_coe]
      have hee : (F.extend k).exp = ⊥ := by rw [he_ext, hexp]; rfl
      rw [F.numDigits_coe_bot hx hp hexp,
          (F.extend k).numDigits_coe_bot hx hpe hee]
      push_cast; ring
    | coe e' =>
      have hpe : (F.extend k).p = (((n + k : ℕ+)) : WithTop ℕ+) := by
        rw [hp_ext, hp, WithTop.map_coe]
      have hee : (F.extend k).exp = ((e' - (k : ℤ) : ℤ) : WithBot ℤ) := by
        rw [he_ext, hexp, WithBot.map_coe]
      rw [F.numDigits_coe_coe hx hp hexp,
          (F.extend k).numDigits_coe_coe hx hpe hee]
      have hnk : (((n + k : ℕ+) : ℕ) : ℤ) = (n : ℤ) + (k : ℤ) := by push_cast; ring
      rw [hnk]
      have hlog : Int.log 2 |x| - (e' - (k : ℤ)) + 1
          = Int.log 2 |x| - e' + 1 + (k : ℤ) := by ring
      rw [hlog]; omega

end FiniteFormat


/-! ### Grid lemmas for `next`: closure, minimality, monotonicity,
midpoints, and the paper containment formats -/

/-- `b < F.next b` for finite `exp` (any `p`), `b ≥ 0`. -/
private theorem lt_next' {F : Format} {e : ℤ} (he : F.exp = (e : WithBot ℤ))
    (b : Dyadic) (hb : 0 ≤ ((b : Dyadic) : ℝ)) :
    ((b : Dyadic) : ℝ) < ((F.next b : Dyadic) : ℝ) := by
  rcases hp : F.p with _ | p
  · exact Format.lt_next_of_p_top F he hp b
  · exact Format.lt_next_of_finite F he hp b hb

/-- `b < F.next b` for `b ≥ 0`, any `(p, exp)` shape. -/
theorem lt_next'' {F : Format} (b : Dyadic)
    (hb : 0 ≤ ((b : Dyadic) : ℝ)) :
    ((b : Dyadic) : ℝ) < ((F.next b : Dyadic) : ℝ) := by
  cases he : F.exp with
  | bot => exact Format.lt_next_of_bot F he b
  | coe e => exact lt_next' he b hb

/-- **Grid closure of `next`**, finite-`exp` case: if `b` lies on the
`(p, exp)` grid, then `F.next b` does as well. -/
private theorem next_mem_unbounded {F : FiniteFormat} {e : ℤ}
    (he : F.exp = (e : WithBot ℤ)) {b : Dyadic}
    (hb_mem : b ∈ F.unbounded) :
    F.toFormat.next b ∈ F.unbounded := by
  obtain ⟨hb_p, hb_q, -⟩ := hb_mem
  have hb_q' : ∃ m : ℤ, ((b : Dyadic) : ℝ) = (m : ℝ) * (2 : ℝ) ^ e := by
    rw [← Dyadic.quantumAtLeast_coe_real, ← he]; exact hb_q
  obtain ⟨m, hm⟩ := hb_q'
  cases hF_p : F.p with
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
              (max e (Int.log 2 ((b : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1)) := by
          unfold Format.next; rw [he, hF_p]
        rw [h_eq, if_pos hb0]
      refine ⟨?_, ?_, trivial⟩
      · change Dyadic.precisionAtMost F.p _
        rw [hF_p, h_next]
        exact precisionAtMost_one_zpow e
      · change Dyadic.quantumAtLeast F.exp _
        rw [he, Dyadic.quantumAtLeast_coe_real]
        exact ⟨1, by rw [h_next, Dyadic.coe_ofIntZpow]⟩
    · -- `b > 0`: the main case.
      push Not at hb0
      have hb_p' : Dyadic.precisionAtMost ((p : ℕ+) : WithTop ℕ+) b := by
        rw [← hF_p]; exact hb_p
      obtain ⟨c, q, hc_eq, hc_odd, hc_pos, -, -, hlog_lt⟩ :=
        exists_odd_canonical_pos hb_p' hb0
      -- `e ≤ q`: an odd significand cannot absorb a coarser quantum.
      have hqe : e ≤ q := quantum_le_of_odd_rep (he ▸ hb_q) hc_odd hc_eq
      have h_next := Format.next_eq_finite_pos F.toFormat he hF_p hb0
      set logB := Int.log 2 ((b : Dyadic) : ℝ) with hlogB_def
      -- step exponent `s`, with `e ≤ s ≤ q`.
      set s := max e (logB - ((p : ℕ) : ℤ) + 1) with hs_def
      have hs_le_q : s ≤ q := max_le hqe (by omega)
      have he_le_s : e ≤ s := le_max_left _ _
      have h2s_pos : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
      have h2q_split : (2 : ℝ) ^ q = (2 : ℝ) ^ ((q - s).toNat) * (2 : ℝ) ^ s :=
        two_zpow_split_toNat hs_le_q
      have h_val : ((F.toFormat.next b : Dyadic) : ℝ)
          = ((c * 2 ^ ((q - s).toNat) + 1 : ℤ) : ℝ) * (2 : ℝ) ^ s := by
        rw [h_next, Dyadic.coe_real_add, coe_real_ofIntZpow_one s, hc_eq, h2q_split]
        push_cast; ring
      -- `c·2^(q−s) < 2^p`, hence the new significand is at most `2^p`.
      have hck_lt : c * 2 ^ ((q - s).toNat) < 2 ^ (p : ℕ) := by
        have hb_ub : ((b : Dyadic) : ℝ) < (2 : ℝ) ^ (logB + 1) :=
          Int.lt_zpow_succ_log_self (by norm_num) _
        have h3 : (c : ℝ) * (2 : ℝ) ^ ((q - s).toNat) * (2 : ℝ) ^ s
            < (2 : ℝ) ^ ((p : ℕ) : ℤ) * (2 : ℝ) ^ s := by
          have h4 : (c : ℝ) * (2 : ℝ) ^ ((q - s).toNat) * (2 : ℝ) ^ s
              = (c : ℝ) * (2 : ℝ) ^ q := by rw [h2q_split]; ring
          have h5 : (2 : ℝ) ^ (((p : ℕ) : ℤ) + s)
              = (2 : ℝ) ^ ((p : ℕ) : ℤ) * (2 : ℝ) ^ s := by
            rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          rw [h4, ← h5]
          calc (c : ℝ) * (2 : ℝ) ^ q = ((b : Dyadic) : ℝ) := hc_eq.symm
            _ < (2 : ℝ) ^ (logB + 1) := hb_ub
            _ ≤ (2 : ℝ) ^ (((p : ℕ) : ℤ) + s) :=
                zpow_le_zpow_right₀ (by norm_num) (by omega)
        have h6 : (c : ℝ) * (2 : ℝ) ^ ((q - s).toNat) < (2 : ℝ) ^ ((p : ℕ) : ℤ) :=
          lt_of_mul_lt_mul_right (by linarith [h3]) h2s_pos.le
        have h7 : (c : ℝ) * (2 : ℝ) ^ ((q - s).toNat) < (2 : ℝ) ^ (p : ℕ) := by
          rw [← zpow_natCast (2 : ℝ) (p : ℕ)]; exact h6
        exact_mod_cast h7
      have hc₁_pos : 0 < c * 2 ^ ((q - s).toNat) + 1 := by
        have h2k : (0 : ℤ) < 2 ^ ((q - s).toNat) := pow_pos (by norm_num) _
        have := mul_pos hc_pos h2k
        omega
      rcases lt_or_eq_of_le (Int.add_one_le_iff.mpr hck_lt) with hc₁_lt | hc₁_eq
      · -- Normal case: representation `(c·2^(q−s) + 1, s)`.
        refine ⟨?_, ?_, trivial⟩
        · change Dyadic.precisionAtMost F.p _
          rw [hF_p, Dyadic.precisionAtMost_coe_real]
          exact ⟨c * 2 ^ ((q - s).toNat) + 1, s, h_val, by rwa [abs_of_pos hc₁_pos]⟩
        · change Dyadic.quantumAtLeast F.exp _
          rw [he, Dyadic.quantumAtLeast_coe_real]
          refine ⟨(c * 2 ^ ((q - s).toNat) + 1) * 2 ^ ((s - e).toNat), ?_⟩
          rw [h_val, two_zpow_split_toNat he_le_s]
          push_cast; ring
      · -- Carry case: `next b = 2^(p + s)`, representation `(1, p + s)`.
        have h_val' : ((F.toFormat.next b : Dyadic) : ℝ)
            = (2 : ℝ) ^ (((p : ℕ) : ℤ) + s) := by
          rw [h_val, hc₁_eq, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
          push_cast; ring
        refine ⟨?_, ?_, trivial⟩
        · change Dyadic.precisionAtMost F.p _
          rw [hF_p, Dyadic.precisionAtMost_coe_real]
          refine ⟨1, ((p : ℕ) : ℤ) + s, by rw [h_val']; push_cast; ring, ?_⟩
          have hp1 : 1 ≤ (p : ℕ) := p.pos
          have h2 : (2 : ℤ) ^ 1 ≤ (2 : ℤ) ^ (p : ℕ) := pow_le_pow_right₀ (by norm_num) hp1
          simp only [abs_one]
          omega
        · change Dyadic.quantumAtLeast F.exp _
          rw [he, Dyadic.quantumAtLeast_coe_real]
          refine ⟨2 ^ ((((p : ℕ) : ℤ) + s - e).toNat), ?_⟩
          rw [h_val', two_zpow_split_toNat (show e ≤ ((p : ℕ) : ℤ) + s by omega)]
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
      refine ⟨1, 0, by push_cast; norm_num, abs_one_lt_two_pow p⟩
    · change Dyadic.quantumAtLeast F.exp (1 : Dyadic)
      rw [he]
      trivial
  · -- `b > 0`: the binade-dependent step; mirrors the finite-`exp` case
    -- with `s := logB − p + 1` (no `max`, and the quantum is trivial).
    push Not at hb0
    have hb_p' : Dyadic.precisionAtMost ((p : ℕ+) : WithTop ℕ+) b := by
      rw [← hF_p]; exact hb_p
    obtain ⟨c, q, hc_eq, -, hc_pos, -, -, hlog_lt⟩ :=
      exists_odd_canonical_pos hb_p' hb0
    have h_next := Format.next_eq_bot_pos F.toFormat he hF_p hb0
    set logB := Int.log 2 ((b : Dyadic) : ℝ) with hlogB_def
    set s := logB - ((p : ℕ) : ℤ) + 1 with hs_def
    have hs_le_q : s ≤ q := by omega
    have h2s_pos : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
    have h2q_split : (2 : ℝ) ^ q = (2 : ℝ) ^ ((q - s).toNat) * (2 : ℝ) ^ s :=
      two_zpow_split_toNat hs_le_q
    have h_val : ((F.toFormat.next b : Dyadic) : ℝ)
        = ((c * 2 ^ ((q - s).toNat) + 1 : ℤ) : ℝ) * (2 : ℝ) ^ s := by
      rw [h_next, Dyadic.coe_real_add, coe_real_ofIntZpow_one s, hc_eq, h2q_split]
      push_cast; ring
    have hck_lt : c * 2 ^ ((q - s).toNat) < 2 ^ (p : ℕ) := by
      have hb_ub : ((b : Dyadic) : ℝ) < (2 : ℝ) ^ (logB + 1) :=
        Int.lt_zpow_succ_log_self (by norm_num) _
      have h3 : (c : ℝ) * (2 : ℝ) ^ ((q - s).toNat) * (2 : ℝ) ^ s
          < (2 : ℝ) ^ ((p : ℕ) : ℤ) * (2 : ℝ) ^ s := by
        have h4 : (c : ℝ) * (2 : ℝ) ^ ((q - s).toNat) * (2 : ℝ) ^ s
            = (c : ℝ) * (2 : ℝ) ^ q := by rw [h2q_split]; ring
        have h5 : (2 : ℝ) ^ (((p : ℕ) : ℤ) + s)
            = (2 : ℝ) ^ ((p : ℕ) : ℤ) * (2 : ℝ) ^ s := by
          rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        rw [h4, ← h5]
        calc (c : ℝ) * (2 : ℝ) ^ q = ((b : Dyadic) : ℝ) := hc_eq.symm
          _ < (2 : ℝ) ^ (logB + 1) := hb_ub
          _ ≤ (2 : ℝ) ^ (((p : ℕ) : ℤ) + s) :=
              zpow_le_zpow_right₀ (by norm_num) (by omega)
      have h6 : (c : ℝ) * (2 : ℝ) ^ ((q - s).toNat) < (2 : ℝ) ^ ((p : ℕ) : ℤ) :=
        lt_of_mul_lt_mul_right (by linarith [h3]) h2s_pos.le
      have h7 : (c : ℝ) * (2 : ℝ) ^ ((q - s).toNat) < (2 : ℝ) ^ (p : ℕ) := by
        rw [← zpow_natCast (2 : ℝ) (p : ℕ)]; exact h6
      exact_mod_cast h7
    have hc₁_pos : 0 < c * 2 ^ ((q - s).toNat) + 1 := by
      have h2k : (0 : ℤ) < 2 ^ ((q - s).toNat) := pow_pos (by norm_num) _
      have := mul_pos hc_pos h2k
      omega
    rcases lt_or_eq_of_le (Int.add_one_le_iff.mpr hck_lt) with hc₁_lt | hc₁_eq
    · refine ⟨?_, ?_, trivial⟩
      · change Dyadic.precisionAtMost F.p _
        rw [hF_p, Dyadic.precisionAtMost_coe_real]
        exact ⟨c * 2 ^ ((q - s).toNat) + 1, s, h_val, by rwa [abs_of_pos hc₁_pos]⟩
      · change Dyadic.quantumAtLeast F.exp _
        rw [he]
        trivial
    · have h_val' : ((F.toFormat.next b : Dyadic) : ℝ)
          = (2 : ℝ) ^ (((p : ℕ) : ℤ) + s) := by
        rw [h_val, hc₁_eq]
        rw [show (2 : ℝ) ^ (((p : ℕ) : ℤ) + s)
            = (2 : ℝ) ^ ((p : ℕ) : ℤ) * (2 : ℝ) ^ s from
          zpow_add₀ (by norm_num) _ _, zpow_natCast]
        push_cast; ring
      refine ⟨?_, ?_, trivial⟩
      · change Dyadic.precisionAtMost F.p _
        rw [hF_p, Dyadic.precisionAtMost_coe_real]
        refine ⟨1, ((p : ℕ) : ℤ) + s, by rw [h_val']; push_cast; ring, abs_one_lt_two_pow p⟩
      · change Dyadic.quantumAtLeast F.exp _
        rw [he]
        trivial

/-- Grid closure of `next`, any `exp`. -/
theorem next_mem_unbounded' {F : FiniteFormat} {b : Dyadic}
    (hb_mem : b ∈ F.unbounded) (hb_nn : 0 ≤ ((b : Dyadic) : ℝ)) :
    F.toFormat.next b ∈ F.unbounded := by
  cases he : F.exp with
  | bot => exact next_mem_unbounded_bot he hb_mem hb_nn
  | coe e => exact next_mem_unbounded he hb_mem

/-- **Grid minimality of `next`**: for `b ≥ 0` on the grid and finite `exp`,
any grid point strictly above `b` is at least `F.next b` — i.e. the grid has
no point in `(b, next b)`. -/
private theorem next_min {F : FiniteFormat} {e : ℤ}
    (he : F.exp = (e : WithBot ℤ)) {b g : Dyadic}
    (hb_mem : b ∈ F.unbounded) (hg_mem : g ∈ F.unbounded)
    (hb_nn : 0 ≤ ((b : Dyadic) : ℝ))
    (hbg : ((b : Dyadic) : ℝ) < ((g : Dyadic) : ℝ)) :
    ((F.toFormat.next b : Dyadic) : ℝ) ≤ ((g : Dyadic) : ℝ) := by
  obtain ⟨hb_p, hb_q, -⟩ := hb_mem
  obtain ⟨hg_p, hg_q, -⟩ := hg_mem
  have h2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  cases hF_p : F.p with
  | top =>
    -- Both are multiples of `2^e`; a strict increase is at least one step.
    have h_next : F.toFormat.next b = b + Dyadic.ofIntZpow 1 e :=
      Format.next_eq_p_top F.toFormat he hF_p b
    obtain ⟨mb, hmb⟩ : ∃ m : ℤ, ((b : Dyadic) : ℝ) = (m : ℝ) * (2 : ℝ) ^ e := by
      rw [← Dyadic.quantumAtLeast_coe_real, ← he]; exact hb_q
    obtain ⟨mg, hmg⟩ : ∃ m : ℤ, ((g : Dyadic) : ℝ) = (m : ℝ) * (2 : ℝ) ^ e := by
      rw [← Dyadic.quantumAtLeast_coe_real, ← he]; exact hg_q
    have hm_lt : mb < mg := by
      have h1 : (mb : ℝ) < (mg : ℝ) := by
        rw [hmb, hmg] at hbg
        exact lt_of_mul_lt_mul_right hbg h2e_pos.le
      exact_mod_cast h1
    rw [h_next, Dyadic.coe_real_add, coe_real_ofIntZpow_one e, hmb, hmg]
    have h1 : (mb : ℝ) + 1 ≤ (mg : ℝ) := by exact_mod_cast hm_lt
    nlinarith
  | coe p =>
    have hg_pos : 0 < ((g : Dyadic) : ℝ) := lt_of_le_of_lt hb_nn hbg
    have hg_p' : Dyadic.precisionAtMost ((p : ℕ+) : WithTop ℕ+) g := by
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
              (max e (Int.log 2 ((b : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1)) := by
          unfold Format.next; rw [he, hF_p]
        rw [h_eq, if_pos hb0]
      rw [h_next, coe_real_ofIntZpow_one e]
      have h1 : (2 : ℝ) ^ e ≤ (2 : ℝ) ^ qg :=
        zpow_le_zpow_right₀ (by norm_num) he_qg
      linarith
    · -- `b > 0`: both are multiples of the step `2^s`.
      push Not at hb0
      have hb_p' : Dyadic.precisionAtMost ((p : ℕ+) : WithTop ℕ+) b := by
        rw [← hF_p]; exact hb_p
      obtain ⟨cb, qb, hb_eq, hb_odd, -, -, -, hb_log_lt⟩ :=
        exists_odd_canonical_pos hb_p' hb0
      have he_qb : e ≤ qb := quantum_le_of_odd_rep (he ▸ hb_q) hb_odd hb_eq
      have h_next := Format.next_eq_finite_pos F.toFormat he hF_p hb0
      have hlog_qg' : Int.log 2 ((b : Dyadic) : ℝ) < qg + ((p : ℕ) : ℤ) :=
        lt_of_le_of_lt (Int.log_mono_right hb0 hbg.le) hg_log_lt
      set logB := Int.log 2 ((b : Dyadic) : ℝ) with hlogB_def
      set s := max e (logB - ((p : ℕ) : ℤ) + 1) with hs_def
      have hs_le_qb : s ≤ qb := max_le he_qb (by omega)
      have hs_le_qg : s ≤ qg := max_le he_qg (by omega)
      have h2s_pos : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
      -- both as multiples of `2^s`
      have hkb : ((b : Dyadic) : ℝ) = ((cb * 2 ^ ((qb - s).toNat) : ℤ) : ℝ) * (2 : ℝ) ^ s := by
        rw [hb_eq, two_zpow_split_toNat hs_le_qb]
        push_cast; ring
      have hkg : ((g : Dyadic) : ℝ) = ((cg * 2 ^ ((qg - s).toNat) : ℤ) : ℝ) * (2 : ℝ) ^ s := by
        rw [hg_eq, two_zpow_split_toNat hs_le_qg]
        push_cast; ring
      have hk_lt : cb * 2 ^ ((qb - s).toNat) < cg * 2 ^ ((qg - s).toNat) := by
        have h1 : ((cb * 2 ^ ((qb - s).toNat) : ℤ) : ℝ)
            < ((cg * 2 ^ ((qg - s).toNat) : ℤ) : ℝ) := by
          rw [hkb, hkg] at hbg
          exact lt_of_mul_lt_mul_right hbg h2s_pos.le
        exact_mod_cast h1
      rw [h_next, Dyadic.coe_real_add, coe_real_ofIntZpow_one s, hkb, hkg]
      have h1 : ((cb * 2 ^ ((qb - s).toNat) : ℤ) : ℝ) + 1
          ≤ ((cg * 2 ^ ((qg - s).toNat) : ℤ) : ℝ) := by
        exact_mod_cast Int.add_one_le_iff.mpr hk_lt
      nlinarith

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
  have hg_p' : Dyadic.precisionAtMost ((p : ℕ+) : WithTop ℕ+) g := by
    rw [← hF_p]; exact hg_p
  have hb_p' : Dyadic.precisionAtMost ((p : ℕ+) : WithTop ℕ+) b := by
    rw [← hF_p]; exact hb_p
  obtain ⟨cg, qg, hg_eq, -, -, -, -, hg_log_lt⟩ :=
    exists_odd_canonical_pos hg_p' hg_pos
  obtain ⟨cb, qb, hb_eq, -, -, -, -, hb_log_lt⟩ :=
    exists_odd_canonical_pos hb_p' hb_pos
  have h_next := Format.next_eq_bot_pos F.toFormat he hF_p hb_pos
  have hlog_qg' : Int.log 2 ((b : Dyadic) : ℝ) < qg + ((p : ℕ) : ℤ) :=
    lt_of_le_of_lt (Int.log_mono_right hb_pos hbg.le) hg_log_lt
  set logB := Int.log 2 ((b : Dyadic) : ℝ) with hlogB_def
  set s := logB - ((p : ℕ) : ℤ) + 1 with hs_def
  have hs_le_qb : s ≤ qb := by omega
  have hs_le_qg : s ≤ qg := by omega
  have h2s_pos : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  have hkb : ((b : Dyadic) : ℝ) = ((cb * 2 ^ ((qb - s).toNat) : ℤ) : ℝ) * (2 : ℝ) ^ s := by
    rw [hb_eq, two_zpow_split_toNat hs_le_qb]
    push_cast; ring
  have hkg : ((g : Dyadic) : ℝ) = ((cg * 2 ^ ((qg - s).toNat) : ℤ) : ℝ) * (2 : ℝ) ^ s := by
    rw [hg_eq, two_zpow_split_toNat hs_le_qg]
    push_cast; ring
  have hk_lt : cb * 2 ^ ((qb - s).toNat) < cg * 2 ^ ((qg - s).toNat) := by
    have h1 : ((cb * 2 ^ ((qb - s).toNat) : ℤ) : ℝ)
        < ((cg * 2 ^ ((qg - s).toNat) : ℤ) : ℝ) := by
      rw [hkb, hkg] at hbg
      exact lt_of_mul_lt_mul_right hbg h2s_pos.le
    exact_mod_cast h1
  rw [h_next, Dyadic.coe_real_add, coe_real_ofIntZpow_one s, hkb, hkg]
  have h1 : ((cb * 2 ^ ((qb - s).toNat) : ℤ) : ℝ) + 1
      ≤ ((cg * 2 ^ ((qg - s).toNat) : ℤ) : ℝ) := by
    exact_mod_cast Int.add_one_le_iff.mpr hk_lt
  nlinarith

/-- Grid minimality of `next`, any `exp` (for `exp = ⊥` the base point must
be positive). -/
theorem next_min' {F : FiniteFormat} {b g : Dyadic}
    (hb_mem : b ∈ F.unbounded) (hg_mem : g ∈ F.unbounded)
    (hb_nn : 0 ≤ ((b : Dyadic) : ℝ))
    (hguard : F.exp = ⊥ → 0 < ((b : Dyadic) : ℝ))
    (hbg : ((b : Dyadic) : ℝ) < ((g : Dyadic) : ℝ)) :
    ((F.toFormat.next b : Dyadic) : ℝ) ≤ ((g : Dyadic) : ℝ) := by
  cases he : F.exp with
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
  cases he : F.exp with
  | bot =>
    have hd_pos := hguard he
    have hb_pos : 0 < ((b : Dyadic) : ℝ) := lt_of_lt_of_le hd_pos hdb
    cases hp : F.p with
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
      have hzp : (2 : ℝ) ^ (Int.log 2 ((d : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1)
          ≤ (2 : ℝ) ^ (Int.log 2 ((b : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      push_cast
      linarith
  | coe e =>
    cases hp : F.p with
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
                (max e (Int.log 2 ((d : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1)) := by
            unfold Format.next; rw [he, hp]
          rw [h_eq, if_pos hd0]
        by_cases hb0 : ((b : Dyadic) : ℝ) ≤ 0
        · have h_eqb : F.next b = Dyadic.ofIntZpow 1 e := by
            have h_eq : F.next b =
                if ((b : Dyadic) : ℝ) ≤ 0 then Dyadic.ofIntZpow 1 e
                else b + Dyadic.ofIntZpow 1
                  (max e (Int.log 2 ((b : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1)) := by
              unfold Format.next; rw [he, hp]
            rw [h_eq, if_pos hb0]
          rw [h_eqd, h_eqb]
        · push Not at hb0
          rw [h_eqd, Format.next_eq_finite_pos F he hp hb0, Dyadic.coe_real_add,
            Dyadic.coe_ofIntZpow, Dyadic.coe_ofIntZpow]
          have h1 : (2 : ℝ) ^ e
              ≤ (2 : ℝ) ^ (max e (Int.log 2 ((b : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1)) :=
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
        have hzp : (2 : ℝ) ^ (max e (Int.log 2 ((d : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1))
            ≤ (2 : ℝ) ^ (max e (Int.log 2 ((b : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1)) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
        push_cast
        linarith

/-- An extension with `exp = ⊥` comes from a base with `exp = ⊥`. -/
theorem exp_bot_of_extend_bot {F₁ : FiniteFormat} {k : ℕ+}
    (h : (F₁.extend k).toFormat.exp = ⊥) : F₁.exp = ⊥ := by
  cases hc : F₁.exp with
  | bot => rfl
  | coe e =>
    exfalso
    have h' : F₁.exp.map (· - (k : ℤ)) = ⊥ := h
    rw [hc] at h'
    exact absurd h' (by simp)

/-- `next` on `F₁.extend 1` lands exactly on the midpoint of `b` and
`F₁.next b`: extending by one bit halves the grid step. -/
private theorem next_extend_midpoint {F₁ : FiniteFormat} {e₁ : ℤ}
    (he₁ : F₁.exp = (e₁ : WithBot ℤ)) {b : Dyadic}
    (hb_nn : 0 ≤ ((b : Dyadic) : ℝ)) :
    (((F₁.extend 1).toFormat.next b : Dyadic) : ℝ)
      = (((b : Dyadic) : ℝ) + ((F₁.toFormat.next b : Dyadic) : ℝ)) / 2 := by
  have he₁x : (F₁.extend 1).toFormat.exp = ((e₁ - 1 : ℤ) : WithBot ℤ) := by
    change F₁.exp.map (· - ((1 : ℕ+) : ℤ)) = _
    rw [he₁]
    rfl
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  cases hp : F₁.p with
  | top =>
    have hpx : (F₁.extend 1).toFormat.p = ⊤ := by
      change F₁.p.map (· + (1 : ℕ+)) = ⊤
      rw [hp]
      rfl
    rw [Format.next_eq_p_top F₁.toFormat he₁ hp b,
      Format.next_eq_p_top (F₁.extend 1).toFormat he₁x hpx b,
      Dyadic.coe_real_add, Dyadic.coe_real_add, coe_real_ofIntZpow_one, coe_real_ofIntZpow_one,
      zpow_sub_one₀ h2]
    ring
  | coe p =>
    have hpx : (F₁.extend 1).toFormat.p = ((p + 1 : ℕ+) : WithTop ℕ+) := by
      change F₁.p.map (· + (1 : ℕ+)) = _
      rw [hp]
      rfl
    by_cases hb0 : ((b : Dyadic) : ℝ) ≤ 0
    · -- `b = 0`: both `next`s are pure powers of two.
      have h_next : F₁.toFormat.next b = Dyadic.ofIntZpow 1 e₁ := by
        have h_eq : F₁.toFormat.next b =
            if ((b : Dyadic) : ℝ) ≤ 0 then Dyadic.ofIntZpow 1 e₁
            else b + Dyadic.ofIntZpow 1
              (max e₁ (Int.log 2 ((b : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1)) := by
          unfold Format.next; rw [he₁, hp]
        rw [h_eq, if_pos hb0]
      have h_nextx : (F₁.extend 1).toFormat.next b = Dyadic.ofIntZpow 1 (e₁ - 1) := by
        have h_eq : (F₁.extend 1).toFormat.next b =
            if ((b : Dyadic) : ℝ) ≤ 0 then Dyadic.ofIntZpow 1 (e₁ - 1)
            else b + Dyadic.ofIntZpow 1
              (max (e₁ - 1)
                (Int.log 2 ((b : Dyadic) : ℝ) - (((p + 1 : ℕ+) : ℕ) : ℤ) + 1)) := by
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
            (Int.log 2 ((b : Dyadic) : ℝ) - (((p + 1 : ℕ+) : ℕ) : ℤ) + 1)
          = max e₁ (Int.log 2 ((b : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1) - 1 := by
        have hcast : (((p + 1 : ℕ+) : ℕ) : ℤ) = ((p : ℕ) : ℤ) + 1 := by
          push_cast; ring
        rw [hcast]
        omega
      rw [h_next, h_nextx, h_max, Dyadic.coe_real_add, Dyadic.coe_real_add,
        coe_real_ofIntZpow_one, coe_real_ofIntZpow_one, zpow_sub_one₀ h2]
      ring

/-- `next` on `F₁.extend 1`, `exp = ⊥` case: the binade step still halves.
Requires `b > 0`. -/
private theorem next_extend_midpoint_bot {F₁ : FiniteFormat} (he₁ : F₁.exp = ⊥)
    {b : Dyadic} (hb_pos : 0 < ((b : Dyadic) : ℝ)) :
    (((F₁.extend 1).toFormat.next b : Dyadic) : ℝ)
      = (((b : Dyadic) : ℝ) + ((F₁.toFormat.next b : Dyadic) : ℝ)) / 2 := by
  have he₁x : (F₁.extend 1).toFormat.exp = ⊥ := by
    change F₁.exp.map (· - ((1 : ℕ+) : ℤ)) = ⊥
    rw [he₁]
    rfl
  obtain ⟨p, hF_p⟩ := exists_p_coe_of_exp_bot (he₁ : F₁.exp = ⊥)
  have hpx : (F₁.extend 1).toFormat.p = ((p + 1 : ℕ+) : WithTop ℕ+) := by
    change F₁.p.map (· + (1 : ℕ+)) = _
    rw [hF_p]
    rfl
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  rw [Format.next_eq_bot_pos F₁.toFormat he₁ hF_p hb_pos,
    Format.next_eq_bot_pos (F₁.extend 1).toFormat he₁x hpx hb_pos]
  have h_idx : Int.log 2 ((b : Dyadic) : ℝ) - (((p + 1 : ℕ+) : ℕ) : ℤ) + 1
      = (Int.log 2 ((b : Dyadic) : ℝ) - ((p : ℕ) : ℤ) + 1) - 1 := by
    have hcast : (((p + 1 : ℕ+) : ℕ) : ℤ) = ((p : ℕ) : ℤ) + 1 := by
      push_cast; ring
    omega
  rw [h_idx, Dyadic.coe_real_add, Dyadic.coe_real_add, coe_real_ofIntZpow_one,
    coe_real_ofIntZpow_one, zpow_sub_one₀ h2]
  ring

/-- `next` on `F₁.extend 1` is the midpoint, any `exp` (for `exp = ⊥` the
base point must be positive). -/
theorem next_extend_midpoint' {F₁ : FiniteFormat} {b : Dyadic}
    (hb_nn : 0 ≤ ((b : Dyadic) : ℝ))
    (hguard : F₁.exp = ⊥ → 0 < ((b : Dyadic) : ℝ)) :
    (((F₁.extend 1).toFormat.next b : Dyadic) : ℝ)
      = (((b : Dyadic) : ℝ) + ((F₁.toFormat.next b : Dyadic) : ℝ)) / 2 := by
  cases he : F₁.exp with
  | bot => exact next_extend_midpoint_bot he (hguard he)
  | coe e => exact next_extend_midpoint he hb_nn

/-- `F.withBound B`, packaged as a `FiniteFormat` (`p`/`exp` unchanged). -/
def FiniteFormat.withBoundFF (F : FiniteFormat) (B : WithTop NonNegDyadic) :
    FiniteFormat :=
  ⟨F.toFormat.withBound B, F.finite⟩

/-- `next(b₁)` satisfies the relaxed bound `boundAfterNext`. -/
theorem boundOK_boundAfterNext_next {F₁ : FiniteFormat} {b₁ : NonNegDyadic}
    (hF₁b : F₁.b = (b₁ : WithTop NonNegDyadic))
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
  cases hF_b : F₁.b with
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
  obtain ⟨b₂, hb₂⟩ : ∃ b₂ : NonNegDyadic, F₂.b = (b₂ : WithTop NonNegDyadic) := by
    cases hc : F₂.b with
    | top => exact absurd hc h
    | coe b₂ => exact ⟨b₂, rfl⟩
  set E := WithBot.unbotD 0 F₁.exp with hE_def
  set K := max E (Int.log 2 ((b₂.val : Dyadic) : ℚ) + 1) with hK_def
  set w := Dyadic.ofIntZpow 1 K with hw_def
  have hw_mem : w ∈ (F₁.toFormat.withBound ⊤) := by
    refine ⟨?_, ?_, ?_⟩
    · change Dyadic.precisionAtMost F₁.p w
      exact precisionAtMost_one_zpow K
    · change Dyadic.quantumAtLeast F₁.exp w
      cases hexp : F₁.exp with
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
    · change Format.boundOK (⊤ : WithTop NonNegDyadic) w
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
