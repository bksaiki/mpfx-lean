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
@[simp] theorem withBound_specials (F : Format) (b' : Bound) :
    (F.withBound b').specials = F.specials := rfl

/-- Relaxing the bound enlarges the format. -/
theorem withBound_mono (F : Format) {b b' : Bound} (h : ∀ v, boundOK b v → boundOK b' v) :
    F.withBound b ⊆ F.withBound b' :=
  subset_of_mem subset_rfl fun v hv => ⟨hv.1, hv.2.1, h v hv.2.2⟩

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

/-- Computed form of `next` for `F.exp = (e : ℤ), F.p = ⊤`. -/
private theorem next_eq_p_top (F : Format) {e : ℤ}
    (he : F.exp = (e : QExp)) (hp : F.p = ⊤) (b : Dyadic) :
    F.next b = b + Dyadic.ofIntZpow 1 e := by
  unfold next
  rw [he, hp]; rfl

/-- With a minimum quantum, the successor of `0` is that quantum. -/
theorem next_zero (F : Format) {e : ℤ} (he : F.exp = (e : QExp)) :
    F.next 0 = Dyadic.ofIntZpow 1 e := by
  cases hp : F.p using ENat.recTopCoe with
  | top => rw [next_eq_p_top F he hp, zero_add]
  | coe p => unfold next; rw [he, hp]; simp

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
          exact_mod_cast b.2
        have h_next_nn : 0 ≤ ((F.next b.val : Dyadic) : ℝ) := next_nonneg F b.val hb
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

/-- The next representable value above a non-negative `b`: `b + 2^canonicalExp b`.

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

/-- On a finite format, `Format.next b` is `b + 2^canonicalExp b` for `b ≥ 0`
(positive when there is no minimum quantum, where `next 0` is junk). -/
theorem format_next_eq (F : FiniteFormat) {b : Dyadic} (hb : 0 ≤ ((b : Dyadic) : ℝ))
    (hguard : F.exp = ⊥ → 0 < ((b : Dyadic) : ℝ)) :
    F.toFormat.next b = b + Dyadic.ofIntZpow 1 (F.canonicalExp ((b : Dyadic) : ℝ)) := by
  rcases hb.lt_or_eq with hb0 | hb0
  · rw [next_eq_format_next F hb0, next_of_ne F (by simp [hb0.ne'])]
  · cases he : F.exp using QExp.recBotCoe with
    | bot => exact absurd (hguard he) (by rw [← hb0]; exact lt_irrefl 0)
    | coe e =>
      obtain rfl : b = 0 := Dyadic.ext_real (by rw [← hb0, Dyadic.coe_real_zero])
      rw [Format.next_zero _ he, Dyadic.coe_real_zero, canonicalExp_zero F he, zero_add]

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
  rw [hmb, hmg] at hbg
  have hm_lt := int_mul_two_zpow_lt_iff.mp hbg
  rw [h_next, Dyadic.coe_real_add, coe_real_ofIntZpow_one s, hmb, hmg]
  have h := int_mul_two_zpow_le_iff (k := s).mpr (show mb + 1 ≤ mg by omega)
  push_cast at h
  linarith

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

/-- A value is a multiple of `2^s` for every `s` at most its canonical exponent. -/
private theorem exists_step_rep_le {F : FiniteFormat} {g : Dyadic}
    (hg_p : Dyadic.precisionAtMost F.p g) (hg_q : Dyadic.quantumAtLeast F.exp g) {s : ℤ}
    (hs : s ≤ F.canonicalExp ((g : Dyadic) : ℝ)) :
    ∃ m : ℤ, ((g : Dyadic) : ℝ) = (m : ℝ) * (2 : ℝ) ^ s := by
  set t := F.canonicalExp ((g : Dyadic) : ℝ) with ht
  obtain ⟨m, hm⟩ := F.exists_mul_zpow_canonicalExp ⟨hg_p, hg_q, trivial⟩
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
        rw [hbz]; exact Format.next_zero _ he
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
        obtain ⟨m, hm⟩ := F.exists_mul_zpow_canonicalExp ⟨hb_p, hb_q, trivial⟩
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
        rw [hbz]; exact Format.next_zero _ he
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
    obtain ⟨mb, hmb⟩ := exists_step_rep_le (F := F) hb_p hb_q le_rfl
    obtain ⟨mg, hmg⟩ := exists_step_rep_le (F := F) hg_p hg_q hmono
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
positive, since `next` is junk at `0` there): the step `2^canonicalExp` grows
with the base. -/
theorem next_mono {F : FiniteFormat} {d b : Dyadic} (hd : 0 ≤ ((d : Dyadic) : ℝ))
    (hdb : ((d : Dyadic) : ℝ) ≤ ((b : Dyadic) : ℝ))
    (hguard : F.exp = ⊥ → 0 < ((d : Dyadic) : ℝ)) :
    ((F.toFormat.next d : Dyadic) : ℝ) ≤ ((F.toFormat.next b : Dyadic) : ℝ) := by
  have hb : 0 ≤ ((b : Dyadic) : ℝ) := hd.trans hdb
  have hexp : F.canonicalExp ((d : Dyadic) : ℝ) ≤ F.canonicalExp ((b : Dyadic) : ℝ) := by
    rcases hd.lt_or_eq with hd0 | hd0
    · exact F.canonicalExp_mono hd0.ne' (by rwa [abs_of_pos hd0, abs_of_nonneg hb])
    · cases he : F.exp using QExp.recBotCoe with
      | bot => exact absurd (hguard he) (by rw [← hd0]; exact lt_irrefl 0)
      | coe e => rw [← hd0, canonicalExp_zero F he]; exact F.exp_le_canonicalExp _ he
  rw [F.format_next_eq hd hguard, F.format_next_eq hb fun he => (hguard he).trans_le hdb,
    Dyadic.coe_real_add, Dyadic.coe_real_add, coe_real_ofIntZpow_one, coe_real_ofIntZpow_one]
  linarith [zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexp]

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
      have hex : (F₁.extend 1).exp = ((e - 1 : ℤ) : QExp) := Format.extend_exp_coe he 1
      have hzero : ∀ (G : FiniteFormat) {q : ℤ}, G.exp = (q : QExp) →
          G.toFormat.next b = Dyadic.ofIntZpow 1 q := by
        intro G q hq
        rw [hbz]; exact Format.next_zero _ hq
      rw [hzero (F₁.extend 1) hex, hzero F₁ he, coe_real_ofIntZpow_one,
        coe_real_ofIntZpow_one, ← hb0, zpow_sub_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
      ring
  · -- `b > 0`: the step exponent drops by exactly one
    rw [next_pos_eq (F₁.extend 1) hb0, next_pos_eq F₁ hb0,
      F₁.canonicalExp_extend 1 (ne_of_gt hb0)]
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
      exact_mod_cast h
    change |(d : ℚ)| ≤ ((F₁.toFormat.next b.val : Dyadic) : ℚ)
    linarith

/-- `F ⊆ F.withBound next(b)`. -/
theorem FiniteFormat.subset_withBound_boundAfterNext (F : FiniteFormat) :
    F.toFormat ⊆ F.toFormat.withBound F.toFormat.boundAfterNext :=
  Format.withBound_mono F.toFormat (b := F.b) fun _ => boundOK_boundAfterNext_of_boundOK

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
  obtain ⟨b₂, hb₂⟩ := WithTop.ne_top_iff_exists.mp h
  obtain ⟨k, hk, hgt⟩ := Format.exists_zpow_gt ((b₂.val : Dyadic) : ℝ) F₁.exp
  have hv := (hsub _ (Format.ofIntZpow_mem (precisionAtMost_one_zpow F₁.pos k) hk trivial)).2.2
  rw [← hb₂] at hv
  have := abs_coe_real_le_of_boundOK hv
  rw [coe_real_ofIntZpow_one, abs_of_pos (zpow_pos (by norm_num) k)] at this
  exact absurd this (not_le_of_gt hgt)

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
private theorem extend_one_extend_one_toFormat (F : FiniteFormat) :
    ((F.extend 1).extend 1).toFormat = (F.extend 2).toFormat :=
  Format.extend_extend F.toFormat 1 1

/-- `(F₁.extend 1).withBound F₁.boundAfterNext ⊆ F₂` implies
`F₁.extend 1 ⊆ F₂`, since `next(b₁) ≥ b₁`. -/
theorem extend_one_subset_of_withBound_subset {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat) :
    (F₁.extend 1).toFormat ⊆ F₂.toFormat :=
  (Format.withBound_mono _ (b := F₁.b) fun _ => boundOK_boundAfterNext_of_boundOK).trans hsub

/-- From the paper-aligned containment
`(F₁.extend 1).withBound F₁.boundAfterNext ⊆ F₂`, either `F₂.p ≥ 2` (the
auxiliary needed for the RTO-padding lemma) or `F₁` contains only `0`. A positive
`d ∈ F₁` gives the precision-2 witness `3 · 2^(cexp d − 1)`: it is a value of
`F₁.extend 1`, and at most `next d ≤ next b`, so `F₂` must hold it
(`two_le_p_of_precision_two_witness`). -/
theorem two_le_p_or_trivial_of_extend_one_withBound_subset {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat) :
    ((2 : ℕ) : Prec) ≤ F₂.p ∨ ∀ d : Dyadic, d ∈ F₁ → (d : ℝ) = 0 := by
  by_contra h
  push Not at h
  obtain ⟨h_p_lt, ⟨d₀, hd₀_mem, hd₀_ne⟩⟩ := h
  obtain ⟨d, hd_mem, hd_pos⟩ : ∃ d : Dyadic, d ∈ F₁ ∧ (0 : ℝ) < d := by
    rcases hd₀_ne.lt_or_gt with h | h
    · exact ⟨-d₀, FiniteFormat.neg_mem hd₀_mem, by rw [Dyadic.coe_real_neg]; linarith⟩
    · exact ⟨d₀, hd₀_mem, h⟩
  set c := F₁.canonicalExp (d : ℝ)
  -- `d = m · 2^c` with `m ≥ 1`, so `2^c ≤ d`.
  obtain ⟨m, hm⟩ := F₁.exists_mul_zpow_canonicalExp (mem_unbounded_of_mem hd_mem)
  have h2c : (0 : ℝ) < (2 : ℝ) ^ c := zpow_pos two_pos c
  have hd_ge : (2 : ℝ) ^ c ≤ d := by
    have hm0 : (0 : ℝ) < m := pos_of_mul_pos_left (hm ▸ hd_pos) h2c.le
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show (0 : ℤ) < m by exact_mod_cast hm0)
    rw [hm]; nlinarith
  have hp_ext : ((2 : ℕ) : Prec) ≤ (F₁.extend 1).p := by
    change ((2 : ℕ) : Prec) ≤ F₁.p + ((1 : ℕ) : Prec)
    cases hp : F₁.p using ENat.recTopCoe with
    | top => simp
    | coe n => rw [← Nat.cast_add]; exact_mod_cast Nat.succ_le_succ (F₁.p_pos hp)
  refine absurd (Format.two_le_p_of_precision_two_witness (hsub (Dyadic.ofIntZpow 3 (c - 1))
    ⟨Dyadic.precisionAtMost_mono hp_ext (Dyadic.precisionAtMost_two_three_zpow _),
      Dyadic.quantumAtLeast_ofIntZpow ?_, ?_⟩)
    (Dyadic.not_precisionAtMost_one_three_zpow _)) (not_le.mpr h_p_lt)
  · change (F₁.toFormat.extend 1).exp ≤ _
    cases he : F₁.exp using QExp.recBotCoe with
    | bot => rw [Format.extend_exp_bot he]; exact bot_le
    | coe e =>
      rw [Format.extend_exp_coe he]
      exact WithBot.coe_le_coe.mpr (by have := F₁.exp_le_canonicalExp (d : ℝ) he; omega)
  · change Format.boundOK F₁.toFormat.boundAfterNext _
    rcases hF_b : F₁.b with _ | b
    · rw [Format.boundAfterNext_top hF_b]; trivial
    obtain ⟨_, h_bAfter⟩ := Format.boundAfterNext_coe hF_b
    rw [h_bAfter]
    refine boundOK_coe_of_abs_le ?_
    -- `|3 · 2^(c−1)| ≤ 2^c + 2^c ≤ d + 2^c = next d ≤ next b`.
    have hdb : (d : ℝ) ≤ (b.val : ℝ) := by
      have h := hd_mem.2.2
      rw [hF_b] at h
      exact (le_abs_self _).trans (abs_coe_real_le_of_boundOK h)
    have hmono := next_mono (F := F₁) hd_pos.le hdb fun _ => hd_pos
    rw [F₁.format_next_eq hd_pos.le fun _ => hd_pos, Dyadic.coe_real_add,
      coe_real_ofIntZpow_one] at hmono
    have hc1 : (2 : ℝ) ^ (c - 1) ≤ (2 : ℝ) ^ c := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hv : ((Dyadic.ofIntZpow 3 (c - 1) : Dyadic) : ℝ) = (2 : ℝ) ^ c + (2 : ℝ) ^ (c - 1) := by
      rw [Dyadic.coe_ofIntZpow, zpow_sub_one₀ two_ne_zero]; push_cast; ring
    rw [hv, abs_of_pos (by positivity)]
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

/-- The RN containment, restated at base `F₁.extend 1`. -/
private theorem extend_one_extend_one_withBound_subset {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
              ⊆ F₂.toFormat) :
    (((F₁.extend 1).extend 1).toFormat.withBound
      (F₁.extend 1).toFormat.boundAfterNext) ⊆ F₂.toFormat := by
  rwa [extend_one_extend_one_toFormat]

/-- RN analog (`k = 2` case) of `extend_one_subset_of_withBound_subset`: from the
paper-aligned containment `((F₁.extend 2).withBound (F₁.extend 1).boundAfterNext)
⊆ F₂`, derive the weaker `F₁.extend 2 ⊆ F₂` form. Obtained from the generic
`extend_one_subset_of_withBound_subset` at base `F₁.extend 1`, bridging the
`(F₁.extend 1).extend 1` / `F₁.extend 2` mismatch via `Format.extend_extend`. -/
theorem extend_two_subset_of_withBound_subset {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
              ⊆ F₂.toFormat) :
    (F₁.extend 2).toFormat ⊆ F₂.toFormat := by
  have h := extend_one_subset_of_withBound_subset (extend_one_extend_one_withBound_subset hsub)
  rwa [extend_one_extend_one_toFormat] at h

/-- RN analog (`k = 2` case) of `two_le_p_or_trivial_of_extend_one_withBound_subset`.
From the paper-aligned RN
containment `((F₁.extend 2).withBound (F₁.extend 1).boundAfterNext) ⊆ F₂`, either
`F₂.p ≥ 2` or `F₁` contains only `0`. Obtained from the generic
`two_le_p_or_trivial_of_extend_one_withBound_subset` at base `F₁.extend 1`: the hypothesis
is bridged from
`F₁.extend 2` to `(F₁.extend 1).extend 1` via `Format.extend_extend`, and
`F₁.extend 1` trivial (the conclusion at that base) implies `F₁` trivial since
`F₁ ⊆ F₁.extend 1`. -/
theorem two_le_p_or_trivial_of_extend_two_withBound_subset {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
              ⊆ F₂.toFormat) :
    ((2 : ℕ) : Prec) ≤ F₂.p ∨ ∀ d : Dyadic, d ∈ F₁ → (d : ℝ) = 0 := by
  have hsub' := extend_one_extend_one_withBound_subset hsub
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
