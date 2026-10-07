import Mpfx.Format.Containment

/-!
# Bound replacement and the `next` operator

`withBound`, the successor bound `next` (on `Format` and `FiniteFormat`),
`boundAfterNext` for the paper's `F⁺` containment, the `next` grid lemmas, and
the paper-form containment lemmas the §5.2 rules take.
-/

namespace Mpfx

namespace Format

/-! ### Bound replacement and the `next` operator

`F.withBound b'` swaps out `F`'s magnitude bound for `b'`. `F.next b` is the
paper's `next_{F.p, F.exp}(b)` from §5.2: the smallest Dyadic in the
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

/-- The paper's `next_{F.p, F.exp}(b)` from §5.2: the smallest Dyadic
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
private theorem lt_next_of_finite (F : Format) {e : ℤ} {p : ℕ}
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
private theorem lt_next_of_p_top (F : Format) {e : ℤ}
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
private theorem next_eq_bot_p_top' (F : Format) (he : F.exp = ⊥) (hp : F.p = ⊤)
    (b : Dyadic) : F.next b = b + 1 := by
  unfold next
  rw [he, hp]; rfl

/-- Computed form of `next` for `F.exp = ⊥, b ≤ 0` (junk arm: no grid
successor exists). -/
private theorem next_eq_bot_nonpos (F : Format) (he : F.exp = ⊥) {b : Dyadic}
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
private theorem next_eq_bot_pos (F : Format) {p : ℕ} (he : F.exp = ⊥)
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
private theorem lt_next_of_bot (F : Format) (he : F.exp = ⊥) (b : Dyadic) :
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

/-- `b < F.next b` for `b ≥ 0`, any `(p, exp)` shape. -/
theorem lt_next {F : Format} (b : Dyadic) (hb : 0 ≤ ((b : Dyadic) : ℝ)) :
    ((b : Dyadic) : ℝ) < ((F.next b : Dyadic) : ℝ) := by
  cases he : F.exp using QExp.recBotCoe with
  | bot => exact lt_next_of_bot F he b
  | coe e =>
    rcases hp : F.p with _ | p
    · exact lt_next_of_p_top F he hp b
    · exact lt_next_of_finite F he hp b hb

/-- `b ≤ F.next b` for `b ≥ 0`. -/
theorem self_le_next (F : Format) (b : Dyadic)
    (hb : 0 ≤ ((b : Dyadic) : ℝ)) :
    ((b : Dyadic) : ℝ) ≤ ((F.next b : Dyadic) : ℝ) :=
  (lt_next (F := F) b hb).le

/-- `F.next b ≥ 0` for `b ≥ 0`. -/
theorem next_nonneg (F : Format) (b : Dyadic) (hb : 0 ≤ ((b : Dyadic) : ℝ)) :
    0 ≤ ((F.next b : Dyadic) : ℝ) :=
  hb.trans (self_le_next F b hb)

/-- Computed form of `next` for `F.exp = (e : ℤ), F.p = p, b > 0`. -/
private theorem next_eq_finite_pos (F : Format) {e : ℤ} {p : ℕ}
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
private theorem next_eq_p_top (F : Format) {e : ℤ}
    (he : F.exp = (e : QExp)) (hp : F.p = ⊤) (b : Dyadic) :
    F.next b = b + Dyadic.ofIntZpow 1 e := by
  unfold next
  rw [he, hp]; rfl

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
private theorem boundAfterNext_coe {F : Format} {b : NonNegDyadic} (hF : F.b = (b : Bound)) :
    ∃ h, F.boundAfterNext = ((⟨F.next b.val, h⟩ : NonNegDyadic) : Bound) := by
  unfold boundAfterNext; rw [hF]; exact ⟨_, rfl⟩

end Format

namespace FiniteFormat

/-- The next representable value at or above a non-negative `b` — the `Dyadic`
counterpart of `succ`, whose real value it carries (`next_coe`).

Unlike `Format.next` this has no junk branches: without a minimum quantum `0`
has no successor, and `next F 0 = 0` records that rather than inventing one. -/
noncomputable def next (F : FiniteFormat) (b : Dyadic) : Dyadic :=
  if ((b : Dyadic) : ℝ) = 0 ∧ F.exp = ⊥ then b
  else b + Dyadic.ofIntZpow 1 (F.canonicalExp ((b : Dyadic) : ℝ))

private theorem next_of_ne (F : FiniteFormat) {b : Dyadic}
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

/-- The step of `Format.next` at a positive `b` is `2 ^ canonicalExp b`, in both
exponent regimes — this is what lets the grid lemmas below avoid a case split. -/
private theorem next_pos_eq (F : FiniteFormat) {b : Dyadic} (hb : 0 < ((b : Dyadic) : ℝ)) :
    F.toFormat.next b = b + Dyadic.ofIntZpow 1 (F.canonicalExp ((b : Dyadic) : ℝ)) := by
  rw [FiniteFormat.next_eq_format_next F hb,
    FiniteFormat.next_of_ne F (by simp [ne_of_gt hb])]

/-- A positive grid point is an integer multiple of its own step `2 ^ cexp b`. -/
private theorem exists_step_rep {F : FiniteFormat} {b : Dyadic}
    (hb_p : Dyadic.precisionAtMost F.p b) (hb_q : Dyadic.quantumAtLeast F.exp b)
    (hb0 : 0 < ((b : Dyadic) : ℝ)) :
    ∃ m : ℤ, ((b : Dyadic) : ℝ)
      = (m : ℝ) * (2 : ℝ) ^ F.canonicalExp ((b : Dyadic) : ℝ) := by
  cases hp : F.p using ENat.recTopCoe with
  | top =>
    cases he : F.exp using QExp.recBotCoe with
    | bot => exact (F.finite.elim (fun h => h hp) (fun h => h he)).elim
    | coe e =>
      have hc : F.canonicalExp ((b : Dyadic) : ℝ) = e := by
        unfold FiniteFormat.canonicalExp; rw [hp, he]; rfl
      rw [hc]
      exact (Dyadic.quantumAtLeast_coe_real e b).mp (he ▸ hb_q)
  | coe p =>
    obtain ⟨c, q, hc_eq, hc_odd, -, -, -, hlog_lt⟩ :=
      exists_odd_canonical_pos (show Dyadic.precisionAtMost (p : Prec) b from hp ▸ hb_p) hb0
    set s := F.canonicalExp ((b : Dyadic) : ℝ) with hs
    have hsq : s ≤ q := by
      rw [hs]
      unfold FiniteFormat.canonicalExp
      cases he : F.exp using QExp.recBotCoe with
      | bot => simp only [hp, if_neg (ne_of_gt hb0), abs_of_pos hb0]; omega
      | coe e =>
        simp only [hp, if_neg (ne_of_gt hb0), abs_of_pos hb0]
        exact max_le (by omega) (quantum_le_of_odd_rep (he ▸ hb_q) hc_odd hc_eq)
    exact ⟨c * 2 ^ ((q - s).toNat), by
      rw [hc_eq, two_zpow_split_toNat hsq]; push_cast; ring⟩

/-- …and hence of any coarser-or-equal step. -/
private theorem exists_step_rep_le {F : FiniteFormat} {g : Dyadic}
    (hg_p : Dyadic.precisionAtMost F.p g) (hg_q : Dyadic.quantumAtLeast F.exp g)
    (hg0 : 0 < ((g : Dyadic) : ℝ)) {s : ℤ}
    (hs : s ≤ F.canonicalExp ((g : Dyadic) : ℝ)) :
    ∃ m : ℤ, ((g : Dyadic) : ℝ) = (m : ℝ) * (2 : ℝ) ^ s := by
  set t := F.canonicalExp ((g : Dyadic) : ℝ) with ht
  obtain ⟨m, hm⟩ := exists_step_rep hg_p hg_q hg0
  exact ⟨m * 2 ^ ((t - s).toNat), by
    rw [hm, two_zpow_split_toNat hs]; push_cast; ring⟩

/-- **Grid closure of `next`**: if `b ≥ 0` lies on the `(p, exp)` grid, so does
`F.next b`. -/
theorem next_mem_unbounded' {F : FiniteFormat} {b : Dyadic}
    (hb_mem : b ∈ F.unbounded) (hb_nn : 0 ≤ ((b : Dyadic) : ℝ)) :
    F.toFormat.next b ∈ F.unbounded := by
  obtain ⟨hb_p, hb_q, -⟩ := hb_mem
  rcases eq_or_lt_of_le hb_nn with hb0 | hb0
  · -- `b = 0`: the step is the format's own quantum, or `1` when it has none
    have hbz : b = 0 :=
      (Dyadic.coe_real_inj b 0).mp (by rw [Dyadic.coe_real_zero]; exact hb0.symm)
    cases he : F.exp using QExp.recBotCoe with
    | bot =>
      obtain ⟨p, hF_p⟩ := exists_p_coe_of_exp_bot he
      rw [Format.next_eq_bot_nonpos F.toFormat he (le_of_eq hb0.symm), hbz, zero_add]
      refine ⟨?_, by change Dyadic.quantumAtLeast F.exp _; rw [he]; trivial, trivial⟩
      change Dyadic.precisionAtMost F.p (1 : Dyadic)
      rw [hF_p, Dyadic.precisionAtMost_coe]
      exact ⟨1, 0, by push_cast; norm_num, abs_one_lt_two_pow (F.p_pos hF_p)⟩
    | coe e =>
      have h_next : F.toFormat.next b = Dyadic.ofIntZpow 1 e := by
        cases hp : F.p using ENat.recTopCoe with
        | top => rw [Format.next_eq_p_top F.toFormat he hp, hbz, zero_add]
        | coe p =>
          have h_eq : F.toFormat.next b =
              if ((b : Dyadic) : ℝ) ≤ 0 then Dyadic.ofIntZpow 1 e
              else b + Dyadic.ofIntZpow 1
                (max e (Int.log 2 ((b : Dyadic) : ℝ) - (p : ℤ) + 1)) := by
            unfold Format.next; rw [he, hp]
          rw [h_eq, if_pos (le_of_eq hb0.symm)]
      rw [h_next]
      refine ⟨?_, ?_, trivial⟩
      · change Dyadic.precisionAtMost F.p _
        cases hp : F.p using ENat.recTopCoe with
        | top => trivial
        | coe p => exact precisionAtMost_one_zpow (by simpa using (F.p_pos hp).ne') e
      · change Dyadic.quantumAtLeast F.exp _
        rw [he, Dyadic.quantumAtLeast_coe_real]
        exact ⟨1, by rw [Dyadic.coe_ofIntZpow]⟩
  · -- `b > 0`: one step of `2 ^ cexp b`, which both clauses can absorb
    have hbne : ((b : Dyadic) : ℝ) ≠ 0 := ne_of_gt hb0
    have h_next := next_pos_eq F hb0
    refine ⟨?_, ?_, trivial⟩
    · change Dyadic.precisionAtMost F.p _
      cases hp : F.p using ENat.recTopCoe with
      | top => trivial
      | coe p =>
        obtain ⟨m, hm⟩ := exists_step_rep (F := F) hb_p hb_q hb0
        exact (next_ulp_precision (F := F.toFormat) (p := p) (F.p_pos hp) hb0 hm
          (by have := F.log_sub_p_le_canonicalExp hbne hp
              rw [abs_of_pos hb0] at this; omega) h_next).1
    · change Dyadic.quantumAtLeast F.exp _
      cases he : F.exp using QExp.recBotCoe with
      | bot => trivial
      | coe e =>
        rw [Dyadic.quantumAtLeast_coe_real]
        obtain ⟨m, hm⟩ := (Dyadic.quantumAtLeast_coe_real e b).mp (he ▸ hb_q)
        refine ⟨m + 2 ^ ((F.canonicalExp ((b : Dyadic) : ℝ) - e).toNat), ?_⟩
        rw [h_next, Dyadic.coe_real_add, coe_real_ofIntZpow_one, hm,
          two_zpow_split_toNat (F.exp_le_canonicalExp _ he)]
        push_cast; ring

/-- **Grid minimality of `next`**: for `b ≥ 0` on the grid, any grid point
strictly above `b` is at least `F.next b` — the grid has no point in
`(b, next b)`. Without a minimum quantum the base point must be positive, since
`0` has no successor there. -/
theorem next_min' {F : FiniteFormat} {b g : Dyadic}
    (hb_mem : b ∈ F.unbounded) (hg_mem : g ∈ F.unbounded)
    (hb_nn : 0 ≤ ((b : Dyadic) : ℝ))
    (hguard : F.exp = ⊥ → 0 < ((b : Dyadic) : ℝ))
    (hbg : ((b : Dyadic) : ℝ) < ((g : Dyadic) : ℝ)) :
    ((F.toFormat.next b : Dyadic) : ℝ) ≤ ((g : Dyadic) : ℝ) := by
  obtain ⟨hb_p, hb_q, -⟩ := hb_mem
  obtain ⟨hg_p, hg_q, -⟩ := hg_mem
  have hg_pos : 0 < ((g : Dyadic) : ℝ) := lt_of_le_of_lt hb_nn hbg
  rcases eq_or_lt_of_le hb_nn with hb0 | hb0
  · -- `b = 0`: the step is the quantum `2 ^ e`, and `g` is a positive multiple of it
    have hbz : b = 0 :=
      (Dyadic.coe_real_inj b 0).mp (by rw [Dyadic.coe_real_zero]; exact hb0.symm)
    cases he : F.exp using QExp.recBotCoe with
    | bot => exact absurd (hguard he) (by rw [← hb0]; exact lt_irrefl 0)
    | coe e =>
      have h_next : F.toFormat.next b = Dyadic.ofIntZpow 1 e := by
        cases hp : F.p using ENat.recTopCoe with
        | top => rw [Format.next_eq_p_top F.toFormat he hp, hbz, zero_add]
        | coe p =>
          have h_eq : F.toFormat.next b =
              if ((b : Dyadic) : ℝ) ≤ 0 then Dyadic.ofIntZpow 1 e
              else b + Dyadic.ofIntZpow 1
                (max e (Int.log 2 ((b : Dyadic) : ℝ) - (p : ℤ) + 1)) := by
            unfold Format.next; rw [he, hp]
          rw [h_eq, if_pos (le_of_eq hb0.symm)]
      obtain ⟨m, hm⟩ := (Dyadic.quantumAtLeast_coe_real e g).mp (he ▸ hg_q)
      have h2e : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
        have : (0 : ℤ) < m := by
          by_contra hc
          push Not at hc
          have : (m : ℝ) ≤ 0 := by exact_mod_cast hc
          nlinarith [hm ▸ hg_pos]
        exact_mod_cast this
      rw [h_next, coe_real_ofIntZpow_one e, hm]
      nlinarith
  · -- `b > 0`: both are multiples of the step `2 ^ cexp b`
    have h_next := next_pos_eq F hb0
    have hmono : F.canonicalExp ((b : Dyadic) : ℝ) ≤ F.canonicalExp ((g : Dyadic) : ℝ) :=
      FiniteFormat.canonicalExp_mono F (ne_of_gt hb0)
        (by rw [abs_of_pos hb0, abs_of_pos hg_pos]; linarith)
    obtain ⟨mb, hmb⟩ := exists_step_rep_le (F := F) hb_p hb_q hb0 le_rfl
    obtain ⟨mg, hmg⟩ := exists_step_rep_le (F := F) hg_p hg_q hg_pos hmono
    exact next_ulp_min hmb hmg hbg h_next

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
    Format.lt_next b₁.val hb₁_nn
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

/-- Extending by one bit halves the step: `cexp` drops by exactly one, in both
exponent regimes (`p ↦ p+1` and `exp ↦ exp−1` each contribute `−1` to the
`max`). -/
private theorem extend_one_canonicalExp (F : FiniteFormat) {x : ℝ} (hx : x ≠ 0) :
    (F.extend 1).canonicalExp x = F.canonicalExp x - 1 := by
  unfold FiniteFormat.canonicalExp
  cases hpF : F.p using ENat.recTopCoe with
  | top =>
    have hxp : (F.extend 1).p = ⊤ := by
      change F.p + ((1 : ℕ) : Prec) = ⊤; rw [hpF]; rfl
    cases heF : F.exp using QExp.recBotCoe with
    | bot => exact (F.finite.elim (fun h => h hpF) (fun h => h heF)).elim
    | coe e =>
      have hxe : (F.extend 1).exp = ((e - 1 : ℤ) : QExp) := by
        change F.exp.map (· - ((1 : ℕ) : ℤ)) = _; rw [heF]; rfl
      rw [hxp, hxe]; rfl
  | coe p =>
    have hxp : (F.extend 1).p = ((p + 1 : ℕ) : Prec) := by
      change F.p + ((1 : ℕ) : Prec) = _; rw [hpF, ← Nat.cast_add]
    cases heF : F.exp using QExp.recBotCoe with
    | bot =>
      have hxe : (F.extend 1).exp = ⊥ := by
        change F.exp.map (· - ((1 : ℕ) : ℤ)) = ⊥; rw [heF]; rfl
      rw [hxp, hxe]
      simp only [if_neg hx]
      push_cast; ring
    | coe e =>
      have hxe : (F.extend 1).exp = ((e - 1 : ℤ) : QExp) := by
        change F.exp.map (· - ((1 : ℕ) : ℤ)) = _; rw [heF]; rfl
      rw [hxp, hxe]
      simp only [if_neg hx]
      push_cast; omega

/-- **`next` on `F₁.extend 1` is the midpoint**: extending by one bit halves the
step, so the finer successor lands halfway to the coarser one. Without a minimum
quantum the base point must be positive. -/
theorem next_extend_midpoint' {F₁ : FiniteFormat} {b : Dyadic}
    (hb_nn : 0 ≤ ((b : Dyadic) : ℝ))
    (hguard : F₁.exp = ⊥ → 0 < ((b : Dyadic) : ℝ)) :
    (((F₁.extend 1).toFormat.next b : Dyadic) : ℝ)
      = (((b : Dyadic) : ℝ) + ((F₁.toFormat.next b : Dyadic) : ℝ)) / 2 := by
  rcases eq_or_lt_of_le hb_nn with hb0 | hb0
  · -- `b = 0`: both steps are pure powers of two, one bit apart
    have hbz : b = 0 :=
      (Dyadic.coe_real_inj b 0).mp (by rw [Dyadic.coe_real_zero]; exact hb0.symm)
    cases he : F₁.exp using QExp.recBotCoe with
    | bot => exact absurd (hguard he) (by rw [← hb0]; exact lt_irrefl 0)
    | coe e =>
      have hex : (F₁.extend 1).exp = ((e - 1 : ℤ) : QExp) := by
        change F₁.exp.map (· - ((1 : ℕ) : ℤ)) = _; rw [he]; rfl
      have hzero : ∀ (G : FiniteFormat) {q : ℤ}, G.exp = (q : QExp) →
          G.toFormat.next b = Dyadic.ofIntZpow 1 q := by
        intro G q hq
        cases hp : G.p using ENat.recTopCoe with
        | top => rw [Format.next_eq_p_top G.toFormat hq hp, hbz, zero_add]
        | coe n =>
          have h_eq : G.toFormat.next b =
              if ((b : Dyadic) : ℝ) ≤ 0 then Dyadic.ofIntZpow 1 q
              else b + Dyadic.ofIntZpow 1
                (max q (Int.log 2 ((b : Dyadic) : ℝ) - (n : ℤ) + 1)) := by
            unfold Format.next; rw [hq, hp]
          rw [h_eq, if_pos (le_of_eq hb0.symm)]
      rw [hzero (F₁.extend 1) hex, hzero F₁ he, coe_real_ofIntZpow_one,
        coe_real_ofIntZpow_one, ← hb0, zpow_sub_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
      ring
  · -- `b > 0`: the step exponent drops by exactly one
    rw [next_pos_eq (F₁.extend 1) hb0, next_pos_eq F₁ hb0,
      extend_one_canonicalExp F₁ (ne_of_gt hb0)]
    exact coe_add_ulp_halves _

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
theorem mem_extend_one_withBound_of_mem {F₁ : FiniteFormat} {d : Dyadic} (hd : d ∈ F₁) :
    d ∈ ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) := by
  have hd' : d ∈ (F₁.extend 1) := Format.self_subset_extend F₁.toFormat 1 d hd
  exact ⟨hd'.1, hd'.2.1, boundOK_boundAfterNext_of_boundOK hd.2.2⟩

/-- Unbounded grid membership plus the relaxed bound gives membership in the
paper containment format `(F₁.extend 1).withBound F₁.boundAfterNext`. -/
theorem mem_extend_one_withBound_of_mem_unbounded {F₁ : FiniteFormat} {d : Dyadic}
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
theorem b_eq_top_of_withBound_subset {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hb_top : F₁.b = ⊤) : F₂.b = ⊤ := by
  rw [Format.boundAfterNext_top hb_top] at hsub
  exact bound_top_of_withBound_top_subset hsub

/-! ### Containment with a relaxed bound

The §5.2 rules take a single containment hypothesis
`(F₁.extend k).withBound next(…) ⊆ F₂`. These lemmas derive the weaker
`F₁.extend k ⊆ F₂` and the auxiliary `2 ≤ F₂.p` from it. -/

/-- `(F.extend 1).extend 1` and `F.extend 2` agree on precision and quantum
(`(n+1)+1 = n+2`, `(e-1)-1 = e-2`); their bounds are both `F.b`. Used to bridge
the RN lemmas (stated over `F₁.extend 2`) to the generic ones (stated over an
arbitrary base extended once). -/
private theorem extend_one_extend_one_p_exp (F : FiniteFormat) :
    ((F.extend 1).extend 1).p = (F.extend 2).p ∧
    ((F.extend 1).extend 1).exp = (F.extend 2).exp := by
  refine ⟨?_, ?_⟩
  · change F.p + ((1 : ℕ) : Prec) + ((1 : ℕ) : Prec) = F.p + ((2 : ℕ) : Prec)
    rw [add_assoc]; norm_num
  · change (F.exp.map (· - (1 : ℤ))).map (· - (1 : ℤ)) = F.exp.map (· - (2 : ℤ))
    cases hF : F.exp using QExp.recBotCoe with
    | bot => rfl
    | coe e => rw [WithBot.map_coe, WithBot.map_coe, WithBot.map_coe]; congr 1; ring

/-- `(F₁.extend 1).withBound F₁.boundAfterNext ⊆ F₂` implies
`F₁.extend 1 ⊆ F₂`, since `next(b₁) ≥ b₁`. -/
theorem extend_one_subset_of_withBound_subset {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat) :
    (F₁.extend 1).toFormat ⊆ F₂.toFormat := by
  intro y hy
  apply hsub
  obtain ⟨hp_y, hq_y, hb_y⟩ := hy
  refine ⟨hp_y, hq_y, ?_⟩
  -- goal: boundOK F₁.boundAfterNext y (withBound replaces only the bound).
  change Format.boundOK F₁.toFormat.boundAfterNext y
  cases hF_b : F₁.b using Bound.recTopCoe with
  | top =>
    rw [Format.boundAfterNext_top hF_b]; trivial
  | coe b =>
    obtain ⟨h_nn, h_after⟩ := Format.boundAfterNext_coe hF_b
    rw [h_after]
    -- goal: |(y : ℚ)| ≤ ((F₁.next b.val : Dyadic) : ℚ).
    change |((y : Dyadic) : ℚ)| ≤ (((F₁.toFormat.next b.val : Dyadic)) : ℚ)
    -- y's own bound: |y| ≤ b.val (over ℚ), since (extend 1).b = F₁.b.
    change Format.boundOK (F₁.extend 1).b y at hb_y
    rw [show (F₁.extend 1).b = F₁.b from rfl, hF_b] at hb_y
    -- b ≤ next(b) over ℝ; bridge to ℚ.
    have hb_nn : 0 ≤ ((b.val : Dyadic) : ℝ) := nonneg_coe_real b
    have h_le_next : ((b.val : Dyadic) : ℝ) ≤ ((F₁.toFormat.next b.val : Dyadic) : ℝ) :=
      Format.self_le_next F₁.toFormat b.val hb_nn
    have h_le_next_q : ((b.val : Dyadic) : ℚ) ≤ ((F₁.toFormat.next b.val : Dyadic) : ℚ) := by
      rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast] at h_le_next
      exact_mod_cast h_le_next
    exact le_trans hb_y h_le_next_q

/-- From the paper-aligned containment
`(F₁.extend 1).withBound F₁.boundAfterNext ⊆ F₂`, either `F₂.p ≥ 2` (the
auxiliary needed for the RTO-padding lemma) or `F₁` contains only `0`. The proof either
constructs a precision-2 witness `v = 3·2^k` lying in
`(F₁.extend 1).withBound F₁.boundAfterNext` (forcing `F₂.p ≥ 2` via
`two_le_p_of_precision_two_witness`), or shows `F₁` is trivial. The witness
exists exactly when `F₁` contains some nonzero element. -/
theorem two_le_p_or_trivial_of_extend_one_withBound_subset {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat) :
    ((2 : ℕ) : Prec) ≤ F₂.p ∨ ∀ d : Dyadic, d ∈ F₁ → (d : ℝ) = 0 := by
  by_contra h
  push Not at h
  obtain ⟨h_p_lt, ⟨d, hd_mem, hd_ne⟩⟩ := h
  -- F₁⁺.p = F₁.p + 1 ≥ 2 since F₁.p ≥ 1 (ℕ values are ≥ 1).
  have h_F₁ext_p_ge_2 :
      ((2 : ℕ) : Prec) ≤ (F₁.extend 1).p := by
    change ((2 : ℕ) : Prec) ≤ F₁.p + ((1 : ℕ) : Prec)
    cases hp : F₁.p using ENat.recTopCoe with
    | top => simp
    | coe n =>
      rw [← Nat.cast_add]
      exact_mod_cast Nat.succ_le_succ (F₁.p_pos hp)
  -- Reduce to producing a precision-2 witness.
  suffices h_witness : ∃ v : Dyadic,
      v ∈ ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ∧
      ¬ Dyadic.precisionAtMost ((1 : ℕ) : Prec) v by
    obtain ⟨v, hv_mem, hv_not_p1⟩ := h_witness
    exact absurd (Format.two_le_p_of_precision_two_witness (hsub v hv_mem) hv_not_p1)
      (not_le.mpr h_p_lt)
  -- Reusable builder: from quantum + bound for v, package full membership.
  have h_mk_member : ∀ k : ℤ,
      Dyadic.quantumAtLeast (F₁.exp.map (· - (1 : ℤ))) (Dyadic.ofIntZpow 3 k) →
      Format.boundOK F₁.toFormat.boundAfterNext (Dyadic.ofIntZpow 3 k) →
      Dyadic.ofIntZpow 3 k ∈
        ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) := by
    intro k hq hb
    refine ⟨?_, ?_, ?_⟩
    · -- precisionAtMost (F₁.p + 1) (ofIntZpow 3 k)
      change Dyadic.precisionAtMost (F₁.extend 1).p _
      exact Dyadic.precisionAtMost_mono h_F₁ext_p_ge_2
        (Dyadic.precisionAtMost_two_three_zpow k)
    · -- quantumAtLeast — withBound preserves exp = (extend 1).exp = F₁.exp.map (· - 1).
      change Dyadic.quantumAtLeast (F₁.extend 1).exp _
      exact hq
    · -- boundOK — withBound's b = F₁.boundAfterNext.
      change Format.boundOK F₁.toFormat.boundAfterNext _
      exact hb
  rcases hF_exp : F₁.exp with _ | e
  · -- F₁.exp = ⊥. F₁⁺.exp = ⊥ ⇒ quantumAtLeast trivial.
    have h_q_triv : ∀ k : ℤ, Dyadic.quantumAtLeast (F₁.exp.map (· - (1 : ℤ)))
        (Dyadic.ofIntZpow 3 k) := by
      intro k; rw [hF_exp]; exact trivial
    rcases hF_b : F₁.b with _ | b
    · -- F₁.b = ⊤. Witness 3·2^0 = 3.
      refine ⟨Dyadic.ofIntZpow 3 0, h_mk_member 0 (h_q_triv 0) ?_,
        Dyadic.not_precisionAtMost_one_three_zpow 0⟩
      rw [Format.boundAfterNext_top hF_b]; trivial
    · -- F₁.b = (b : NonNegDyadic). Pick the witness scale by cases on `b`.
      have hb_nn_r : 0 ≤ ((b.val : Dyadic) : ℝ) := nonneg_coe_real b
      by_cases hb0 : ((b.val : Dyadic) : ℝ) ≤ 0
      · -- `b = 0`: `next b = b + 1 ≥ 1`. Witness 3·2^(-2) = 3/4 ≤ 1.
        refine ⟨Dyadic.ofIntZpow 3 (-2), h_mk_member (-2) (h_q_triv (-2)) ?_,
          Dyadic.not_precisionAtMost_one_three_zpow (-2)⟩
        obtain ⟨_, h_bAfter⟩ := Format.boundAfterNext_coe hF_b
        rw [h_bAfter]
        change |((Dyadic.ofIntZpow 3 (-2) : Dyadic) : ℚ)| ≤ ((F₁.toFormat.next b.val : Dyadic) : ℚ)
        have h_next_eq : F₁.toFormat.next b.val = b.val + 1 :=
          Format.next_eq_bot_nonpos F₁.toFormat hF_exp hb0
        rw [h_next_eq]
        have hb_nn : (0 : ℚ) ≤ ((b.val : Dyadic) : ℚ) := b.2
        rw [Dyadic.coe_rat_ofIntZpow]
        push_cast
        have h_v_eq : (3 : ℚ) * (2 : ℚ) ^ (-2 : ℤ) = 3/4 := by norm_num
        rw [h_v_eq, abs_of_nonneg (by linarith : (0 : ℚ) ≤ 3/4)]
        linarith
      · -- `b > 0`: witness 3·2^(⌊log₂ b⌋ − 2) = (3/4)·2^⌊log₂ b⌋ ≤ b ≤ next b.
        push Not at hb0
        set K := Int.log 2 ((b.val : Dyadic) : ℝ) - 2 with hK_def
        refine ⟨Dyadic.ofIntZpow 3 K, h_mk_member K (h_q_triv K) ?_,
          Dyadic.not_precisionAtMost_one_three_zpow K⟩
        obtain ⟨_, h_bAfter⟩ := Format.boundAfterNext_coe hF_b
        rw [h_bAfter]
        change |((Dyadic.ofIntZpow 3 K : Dyadic) : ℚ)| ≤ ((F₁.toFormat.next b.val : Dyadic) : ℚ)
        suffices h_real : |((Dyadic.ofIntZpow 3 K : Dyadic) : ℝ)|
            ≤ ((F₁.toFormat.next b.val : Dyadic) : ℝ) by
          rw [Dyadic.coe_real_eq_ratCast, ← Rat.cast_abs] at h_real
          rw [Dyadic.coe_real_eq_ratCast] at h_real
          exact_mod_cast h_real
        have h_v_eq : ((Dyadic.ofIntZpow 3 K : Dyadic) : ℝ) = (3 : ℝ) * (2 : ℝ) ^ K := by
          rw [Dyadic.coe_ofIntZpow]; push_cast; ring
        rw [h_v_eq, abs_of_pos (by positivity : (0 : ℝ) < (3 : ℝ) * (2 : ℝ) ^ K)]
        have h_log : (2 : ℝ) ^ (Int.log 2 ((b.val : Dyadic) : ℝ)) ≤ ((b.val : Dyadic) : ℝ) :=
          Int.zpow_log_le_self (by norm_num) hb0
        have h_le_next : ((b.val : Dyadic) : ℝ) ≤ ((F₁.toFormat.next b.val : Dyadic) : ℝ) :=
          Format.self_le_next F₁.toFormat b.val hb_nn_r
        have h_split : (3 : ℝ) * (2 : ℝ) ^ K
            = (3 / 4) * (2 : ℝ) ^ (Int.log 2 ((b.val : Dyadic) : ℝ)) := by
          rw [hK_def, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0),
            (by norm_num : (2 : ℝ) ^ (2 : ℤ) = 4)]
          ring
        rw [h_split]
        linarith
  · -- F₁.exp = (e : ℤ). Use d ≠ 0 to derive |d| ≥ 2^e.
    have h_q_d : Dyadic.quantumAtLeast (F₁.exp) d := hd_mem.2.1
    rw [hF_exp] at h_q_d
    have hd_abs_ge : (2 : ℝ)^e ≤ |(d : ℝ)| :=
      Dyadic.abs_ge_two_zpow_of_quantum h_q_d hd_ne
    have h_q_v : ∀ k : ℤ, k ≥ e - 1 →
        Dyadic.quantumAtLeast (F₁.exp.map (· - (1 : ℤ))) (Dyadic.ofIntZpow 3 k) := by
      intro k hk
      rw [hF_exp]
      change Dyadic.quantumAtLeast (((e - 1 : ℤ) : QExp)) _
      rw [Dyadic.quantumAtLeast_coe]
      refine ⟨3 * 2 ^ (k - (e - 1)).toNat, ?_⟩
      rw [Dyadic.coe_rat_ofIntZpow]
      -- ℚ split: 2^k = 2^(k-(e-1)).toNat * 2^(e-1).
      have h2 : (2 : ℚ) ≠ 0 := by norm_num
      have hsub : ((k - (e - 1)).toNat : ℤ) = k - (e - 1) := Int.toNat_of_nonneg (by omega)
      have h_split : (2 : ℚ) ^ k = (2 : ℚ) ^ (k - (e - 1)).toNat * (2 : ℚ) ^ (e - 1) := by
        rw [show ((2 : ℚ) ^ (k - (e - 1)).toNat : ℚ) = (2 : ℚ) ^ ((k - (e - 1)).toNat : ℤ) from
            (zpow_natCast _ _).symm, ← zpow_add₀ h2, hsub]
        congr 1; ring
      push_cast
      rw [h_split]
      ring
    rcases hF_b : F₁.b with _ | b
    · -- F₁.b = ⊤. Witness 3·2^(e-1).
      refine ⟨Dyadic.ofIntZpow 3 (e - 1), h_mk_member (e - 1) (h_q_v (e - 1) (by omega)) ?_,
        Dyadic.not_precisionAtMost_one_three_zpow (e - 1)⟩
      rw [Format.boundAfterNext_top hF_b]; trivial
    · -- F₁.b = (b : NonNegDyadic). |d| ≤ b. With |d| ≥ 2^e: b ≥ 2^e.
      have hd_le_b_q : |((d : Dyadic) : ℚ)| ≤ ((b.val : Dyadic) : ℚ) := by
        have hb_OK : Format.boundOK F₁.b d := hd_mem.2.2
        rw [hF_b] at hb_OK; exact hb_OK
      have hd_le_b : |((d : Dyadic) : ℝ)| ≤ ((b.val : Dyadic) : ℝ) := by
        rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast, ← Rat.cast_abs]
        exact_mod_cast hd_le_b_q
      have hb_ge : (2 : ℝ)^e ≤ ((b.val : Dyadic) : ℝ) := le_trans hd_abs_ge hd_le_b
      have h2e_pos : (0 : ℝ) < (2 : ℝ)^e := zpow_pos (by norm_num) _
      have hb_pos : 0 < ((b.val : Dyadic) : ℝ) := lt_of_lt_of_le h2e_pos hb_ge
      refine ⟨Dyadic.ofIntZpow 3 (e - 1), h_mk_member (e - 1) (h_q_v (e - 1) (by omega)) ?_,
        Dyadic.not_precisionAtMost_one_three_zpow (e - 1)⟩
      obtain ⟨_, h_bAfter⟩ := Format.boundAfterNext_coe hF_b
      rw [h_bAfter]
      change |((Dyadic.ofIntZpow 3 (e - 1) : Dyadic) : ℚ)| ≤ ((F₁.toFormat.next b.val : Dyadic) : ℚ)
      -- Prove the bound over ℝ, then cast to ℚ.
      suffices h_real : |((Dyadic.ofIntZpow 3 (e - 1) : Dyadic) : ℝ)|
          ≤ ((F₁.toFormat.next b.val : Dyadic) : ℝ) by
        rw [Dyadic.coe_real_eq_ratCast, ← Rat.cast_abs] at h_real
        rw [Dyadic.coe_real_eq_ratCast] at h_real
        exact_mod_cast h_real
      -- |3·2^(e-1)| = 1.5·2^e ≤ next(b) (≥ b + step ≥ 2·2^e ≥ 1.5·2^e).
      have h_v_eq : ((Dyadic.ofIntZpow 3 (e - 1) : Dyadic) : ℝ) = (3 : ℝ) * (2 : ℝ)^(e - 1) := by
        rw [Dyadic.coe_ofIntZpow]; push_cast; ring
      have h_v_pos : (0 : ℝ) ≤ (3 : ℝ) * (2 : ℝ)^(e - 1) := by positivity
      have h_v_split : (3 : ℝ) * (2 : ℝ)^(e - 1) = (2 : ℝ)^e + (2 : ℝ)^(e - 1) := by
        rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]; field_simp; ring
      have h_e1_le_e : (2 : ℝ)^(e - 1) ≤ (2 : ℝ)^e :=
        zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
      rcases hF_p : F₁.p with _ | p
      · -- F₁.p = ⊤. F₁.next b = b + 2^e.
        have h_next_eq : F₁.toFormat.next b.val = b.val + Dyadic.ofIntZpow 1 e :=
          Format.next_eq_p_top F₁.toFormat hF_exp hF_p b.val
        rw [h_next_eq, h_v_eq, abs_of_nonneg h_v_pos, h_v_split]
        push_cast
        rw [Dyadic.coe_ofIntZpow]; push_cast
        linarith
      · -- F₁.p = p. Step ≥ 2^e.
        have h_next_eq : F₁.toFormat.next b.val = b.val + Dyadic.ofIntZpow 1
            (max e (Int.log 2 ((b.val : Dyadic) : ℝ) - (p : ℤ) + 1)) :=
          Format.next_eq_finite_pos F₁.toFormat hF_exp hF_p hb_pos
        rw [h_next_eq, h_v_eq, abs_of_nonneg h_v_pos, h_v_split]
        push_cast
        rw [Dyadic.coe_ofIntZpow]; push_cast
        have h_ulp_pow : (2 : ℝ)^e ≤
            (2 : ℝ)^(max e (Int.log 2 ((b.val : Dyadic) : ℝ) - (p : ℤ) + 1)) :=
          zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (le_max_left _ _)
        linarith

/-- A nonzero member of `F₁` refutes the trivial branch of
`two_le_p_or_trivial_of_extend_one_withBound_subset`: the paper containment
then forces `2 ≤ F₂.p`. -/
theorem two_le_p_of_nontrivial {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial) : ((2 : ℕ) : Prec) ≤ F₂.p := by
  rcases two_le_p_or_trivial_of_extend_one_withBound_subset hsub with h | htriv
  · exact h
  · obtain ⟨d, hd, hne⟩ := hnt
    exact absurd (eq_zero_of_coe_real_zero (htriv d hd)) hne

/-- RN analog (`k = 2` case) of `extend_one_subset_of_withBound_subset`: from the
paper-aligned containment `((F₁.extend 2).withBound (F₁.extend 1).boundAfterNext)
⊆ F₂`, derive the weaker `F₁.extend 2 ⊆ F₂` form. Obtained from the generic
`extend_one_subset_of_withBound_subset` at base `F₁.extend 1`, bridging the
`(F₁.extend 1).extend 1` / `F₁.extend 2` mismatch via `extend_one_extend_one_p_exp`. -/
theorem extend_two_subset_of_withBound_subset {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
              ⊆ F₂.toFormat) :
    (F₁.extend 2).toFormat ⊆ F₂.toFormat := by
  obtain ⟨he_p, he_exp⟩ := extend_one_extend_one_p_exp F₁
  have hsub' : (((F₁.extend 1).extend 1).toFormat.withBound
      (F₁.extend 1).toFormat.boundAfterNext) ⊆ F₂.toFormat := by
    intro y hy
    obtain ⟨hp, hq, hb⟩ := hy
    apply hsub
    refine ⟨?_, ?_, hb⟩
    · rw [Format.withBound_p] at hp ⊢; rwa [he_p] at hp
    · rw [Format.withBound_exp] at hq ⊢; rwa [he_exp] at hq
  intro y hy
  refine extend_one_subset_of_withBound_subset hsub' y ?_
  obtain ⟨hp, hq, hb⟩ := hy
  exact ⟨by rwa [he_p], by rwa [he_exp], hb⟩

/-- RN analog (`k = 2` case) of `two_le_p_or_trivial_of_extend_one_withBound_subset`.
From the paper-aligned RN
containment `((F₁.extend 2).withBound (F₁.extend 1).boundAfterNext) ⊆ F₂`, either
`F₂.p ≥ 2` or `F₁` contains only `0`. Obtained from the generic
`two_le_p_or_trivial_of_extend_one_withBound_subset` at base `F₁.extend 1`: the hypothesis
is bridged from
`F₁.extend 2` to `(F₁.extend 1).extend 1` via `extend_one_extend_one_p_exp`, and
`F₁.extend 1` trivial (the conclusion at that base) implies `F₁` trivial since
`F₁ ⊆ F₁.extend 1`. -/
theorem two_le_p_or_trivial_of_extend_two_withBound_subset {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
              ⊆ F₂.toFormat) :
    ((2 : ℕ) : Prec) ≤ F₂.p ∨ ∀ d : Dyadic, d ∈ F₁ → (d : ℝ) = 0 := by
  obtain ⟨he_p, he_exp⟩ := extend_one_extend_one_p_exp F₁
  have hsub' : (((F₁.extend 1).extend 1).toFormat.withBound
      (F₁.extend 1).toFormat.boundAfterNext) ⊆ F₂.toFormat := by
    intro y hy
    obtain ⟨hp, hq, hb⟩ := hy
    apply hsub
    refine ⟨?_, ?_, hb⟩
    · rw [Format.withBound_p] at hp ⊢; rwa [he_p] at hp
    · rw [Format.withBound_exp] at hq ⊢; rwa [he_exp] at hq
  rcases two_le_p_or_trivial_of_extend_one_withBound_subset hsub' with h | htriv
  · exact Or.inl h
  · exact Or.inr fun d hd => htriv d (Format.self_subset_extend F₁.toFormat 1 d hd)

/-- RN variant of `two_le_p_of_nontrivial`. -/
theorem two_le_p_of_nontrivial_extend_two {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
      ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial) : ((2 : ℕ) : Prec) ≤ F₂.p := by
  rcases two_le_p_or_trivial_of_extend_two_withBound_subset hsub with h | htriv
  · exact h
  · obtain ⟨d, hd, hne⟩ := hnt
    exact absurd (eq_zero_of_coe_real_zero (htriv d hd)) hne

end Mpfx
