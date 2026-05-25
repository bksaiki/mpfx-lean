import Mpfx2.Dyadic
import Mathlib.Data.Int.Log

namespace Mpfx2

/-- The abstract number format `𝒜(p, exp, b)`.

* `p : WithTop ℕ+` — maximum precision (in binary digits). `ℕ+` enforces
  `p ≥ 1`; `⊤` denotes "no precision constraint" (the format is fixed-point).
* `exp : WithBot ℤ` — exponent of the minimum quantum. `⊥` denotes "no quantum
  constraint" (the format is unbounded floating-point).
* `b : WithTop NonNegDyadic` — non-negative magnitude bound. `NonNegDyadic` enforces
  `b ≥ 0`; `⊤` denotes "unbounded".

Defined in §4.2.
-/
structure Format where
  p : WithTop ℕ+
  exp : WithBot ℤ
  b : WithTop NonNegDyadic

namespace Format

/-- `|d|` satisfies the magnitude bound `b`. `⊤` (unbounded) accepts anything;
a finite `b` is interpreted as `|d.val| ≤ b.val`. -/
def boundOK : WithTop NonNegDyadic → Dyadic → Prop
  | ⊤, _ => True
  | (b : NonNegDyadic), d => |(d : ℝ)| ≤ ((b.val : Dyadic) : ℝ)

/-- Membership of `d : Dyadic` in `F : Format`: `d` satisfies all three
constraints (precision, quantum, bound). -/
def Mem (F : Format) (d : Dyadic) : Prop :=
  Dyadic.precisionAtMost F.p d ∧
  Dyadic.quantumAtLeast F.exp d ∧
  boundOK F.b d

/-- `F` with the magnitude bound removed (`b := ⊤`). Used by the
rounding spec to express "round without the bound, then check the
bound separately" — the IEEE-style overflow semantics. -/
def unbounded (F : Format) : Format := { F with b := ⊤ }

@[simp] theorem unbounded_p (F : Format) : F.unbounded.p = F.p := rfl
@[simp] theorem unbounded_exp (F : Format) : F.unbounded.exp = F.exp := rfl
@[simp] theorem unbounded_b (F : Format) : F.unbounded.b = ⊤ := rfl
@[simp] theorem unbounded_unbounded (F : Format) :
    F.unbounded.unbounded = F.unbounded := rfl

end Format

instance : Membership Dyadic Format := ⟨Format.Mem⟩

namespace Format

/-- Zero is in every format. -/
theorem zero_mem (F : Format) : (0 : Dyadic) ∈ F := by
  refine ⟨?_, ?_, ?_⟩
  · change Dyadic.precisionAtMost F.p (0 : Dyadic)
    cases F.p with
    | top => trivial
    | coe p => exact ⟨0, 0, by simp, by simp⟩
  · change Dyadic.quantumAtLeast F.exp (0 : Dyadic)
    cases F.exp with
    | bot => trivial
    | coe e => exact ⟨0, by simp⟩
  · change boundOK F.b (0 : Dyadic)
    cases F.b with
    | top => trivial
    | coe b =>
      change |((0 : Dyadic) : ℝ)| ≤ ((b.val : Dyadic) : ℝ)
      simpa using b.property

end Format

/-! ### Subtype hierarchy

Two stronger tiers stack on top of `Format`, each adding exactly one
invariant required by a downstream API:

* `FiniteFormat` — rules out the *doubly-unbounded* case `(⊤, ⊥)`. At
  least one of `p`, `exp` is finite. This is the minimum needed for
  `rnd` to compute a canonical exponent for nonzero `x`, since
  dyadics are dense in `ℝ` but not closed under limits.
* `ParityFormat` — adds the *parity-anchor* invariant: `p ≠ 1` whenever
  `exp = ⊥`. Combined with `FiniteFormat`, this is `(p ≠ ⊤ ∧ p ≠ 1) ∨
  exp = ⊥`. Required for `IsOdd` / `IsEven` (and hence `rnd .toOdd`,
  `rnd (.nearest _)`) to be semantically meaningful — without it, the
  exponent-parity fallback for `p = 1` has no anchor (since the
  format has no quantum to count indices from).

State theorems on the *weakest* tier whose proof actually destructures
the invariant. Promote only when needed. -/

/-- A `Format` where `rnd` is well-defined for directed modes: at least
one of `p`, `exp` is finite. Equivalently `¬ (p = ⊤ ∧ exp = ⊥)`. -/
structure FiniteFormat extends Format where
  finite : toFormat.p ≠ ⊤ ∨ toFormat.exp ≠ ⊥

namespace FiniteFormat

/-- **Lemma 5.1**: number of binary digits the format rounds `x` to.
Case analysis on `(F.p, F.exp)`:

- `(⊤, e')`: fixed-point with quantum `2^e'`. Digits = `⌊log₂|x|⌋ − e' + 1`.
- `(p, ⊥)`: floating-point with precision `p` and no quantum. Digits = `p`.
- `(p, e')`: floating-point with precision `p` and min quantum `2^e'`.
  Digits = `min(p, ⌊log₂|x|⌋ − e' + 1)`.

The `(⊤, ⊥)` case is ruled out by `FiniteFormat.finite`, so a total
function on `FiniteFormat` is well-defined (no junk-valued branch).

For `x = 0` returns `0` by convention. -/
noncomputable def numDigits (F : FiniteFormat) (x : ℝ) : ℤ :=
  if x = 0 then 0
  else
    let e : ℤ := Int.log 2 |x|
    match F.toFormat.p, F.toFormat.exp with
    | ⊤, ⊥ => 0  -- unreachable by `F.finite`, but pattern-match must be total
    | ⊤, ((e' : ℤ) : WithBot ℤ) => e - e' + 1
    | ((p : ℕ+) : WithTop ℕ+), ⊥ => (p : ℤ)
    | ((p : ℕ+) : WithTop ℕ+), ((e' : ℤ) : WithBot ℤ) => min ((p : ℕ) : ℤ) (e - e' + 1)

@[simp] theorem numDigits_zero (F : FiniteFormat) : F.numDigits 0 = 0 := by
  unfold numDigits; simp

theorem numDigits_neg (F : FiniteFormat) (x : ℝ) :
    F.numDigits (-x) = F.numDigits x := by
  unfold numDigits
  by_cases hx : x = 0
  · subst hx; simp
  · have hxne' : -x ≠ 0 := neg_ne_zero.mpr hx
    have habs : |(-x)| = |x| := abs_neg x
    simp only [hx, hxne', ↓reduceIte, habs]

/-- `numDigits` evaluator: `F.p = ⊤`, `F.exp = (e' : ℤ)`, `x ≠ 0`. -/
theorem numDigits_top_coe (F : FiniteFormat) {x : ℝ} (hx : x ≠ 0) {e' : ℤ}
    (hexp : F.toFormat.exp = (e' : WithBot ℤ)) (hp : F.toFormat.p = ⊤) :
    F.numDigits x = Int.log 2 |x| - e' + 1 := by
  unfold numDigits
  simp only [hx, ↓reduceIte, hp, hexp]

/-- `numDigits` evaluator: `F.p = (p : ℕ+)`, `F.exp = ⊥`, `x ≠ 0`. -/
theorem numDigits_coe_bot (F : FiniteFormat) {x : ℝ} (hx : x ≠ 0) {p : ℕ+}
    (hp : F.toFormat.p = ((p : ℕ+) : WithTop ℕ+)) (hexp : F.toFormat.exp = ⊥) :
    F.numDigits x = (p : ℤ) := by
  unfold numDigits
  simp only [hx, ↓reduceIte, hp, hexp]

/-- `numDigits` evaluator: `F.p = (p : ℕ+)`, `F.exp = (e' : ℤ)`, `x ≠ 0`. -/
theorem numDigits_coe_coe (F : FiniteFormat) {x : ℝ} (hx : x ≠ 0) {p : ℕ+} {e' : ℤ}
    (hp : F.toFormat.p = ((p : ℕ+) : WithTop ℕ+))
    (hexp : F.toFormat.exp = (e' : WithBot ℤ)) :
    F.numDigits x = min ((p : ℕ) : ℤ) (Int.log 2 |x| - e' + 1) := by
  unfold numDigits
  simp only [hx, ↓reduceIte, hp, hexp]

/-- Extract `y = c · 2^e'` from `quantumAtLeast (e' : ℤ)`, handling both
the `(e' : WithBot ℤ)` and `some e'` displayed forms. -/
private theorem quantumAtLeast_extract {y : Dyadic} {e' : ℤ}
    (hQ : Dyadic.quantumAtLeast (e' : WithBot ℤ) y) :
    ∃ c : ℤ, (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ e' := hQ

/-- Extract precisionAtMost witness from `(p : WithTop ℕ+)` form. -/
private theorem precisionAtMost_extract {y : Dyadic} {p : ℕ+}
    (hP : Dyadic.precisionAtMost ((p : ℕ+) : WithTop ℕ+) y) :
    ∃ c e : ℤ, (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ e ∧ |c| < (2 : ℤ) ^ (p : ℕ) := hP

/-- For nonzero `y ≠ 0` with `y = c · 2^e'` and `c ≠ 0`, we have `e' ≤ log|y|`. -/
private theorem quantum_exp_le_log {y : Dyadic} {e' : ℤ} {c : ℤ}
    (hy_ne : (y : ℝ) ≠ 0) (hyeq : (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ e') :
    e' ≤ Int.log 2 |(y : ℝ)| := by
  have hc_ne : c ≠ 0 := by
    intro hc0; rw [hc0] at hyeq; push_cast at hyeq
    rw [zero_mul] at hyeq; exact hy_ne hyeq
  have hc_abs_ge : (1 : ℤ) ≤ |c| := Int.one_le_abs hc_ne
  have habs_lo : (2 : ℝ) ^ e' ≤ |(y : ℝ)| := by
    rw [hyeq, abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)]
    calc (2 : ℝ) ^ e'
        = 1 * (2 : ℝ) ^ e' := (one_mul _).symm
      _ ≤ |(c : ℝ)| * (2 : ℝ) ^ e' := by
          apply mul_le_mul_of_nonneg_right _ (zpow_pos (by norm_num) _).le
          exact_mod_cast hc_abs_ge
  have he_y_hi : |(y : ℝ)| < (2 : ℝ) ^ (Int.log 2 |(y : ℝ)| + 1) :=
    Int.lt_zpow_succ_log_self (by norm_num : (1 : ℕ) < 2) _
  by_contra h_lt
  push Not at h_lt
  have h_step : Int.log 2 |(y : ℝ)| + 1 ≤ e' := by omega
  have h_pow_le : (2 : ℝ) ^ (Int.log 2 |(y : ℝ)| + 1) ≤ (2 : ℝ) ^ e' :=
    zpow_le_zpow_right₀ (by norm_num) h_step
  linarith

/-- `numDigits` is non-negative for nonzero `y ∈ F`. -/
theorem numDigits_nonneg (F : FiniteFormat) (y : Dyadic) (hy : y ∈ F.toFormat)
    (hy_ne : (y : ℝ) ≠ 0) : 1 ≤ F.numDigits (y : ℝ) := by
  obtain ⟨hP, hQ, _⟩ := hy
  cases hp : F.toFormat.p with
  | top =>
    cases hexp : F.toFormat.exp with
    | bot =>
      exfalso; rcases F.finite with h_p_ne | h_exp_ne
      · exact h_p_ne hp
      · exact h_exp_ne hexp
    | coe e' =>
      rw [numDigits_top_coe F hy_ne hexp hp]
      rw [hexp] at hQ
      obtain ⟨c, hyeq⟩ := quantumAtLeast_extract hQ
      have h_log_ge := quantum_exp_le_log hy_ne hyeq
      omega
  | coe p =>
    cases hexp : F.toFormat.exp with
    | bot =>
      rw [numDigits_coe_bot F hy_ne hp hexp]
      exact_mod_cast p.pos
    | coe e' =>
      rw [numDigits_coe_coe F hy_ne hp hexp]
      rw [hexp] at hQ
      obtain ⟨c, hyeq⟩ := quantumAtLeast_extract hQ
      have h_log_ge := quantum_exp_le_log hy_ne hyeq
      have hpp : 1 ≤ ((p : ℕ) : ℤ) := by exact_mod_cast p.pos
      exact le_min hpp (by omega)

/-- The key existence lemma: for nonzero `y ∈ F`, there exist `(c, e)`
representing `y` with `|c| < 2^numDigits F y`. Combined with the analogous
lower-bound argument (`mem_imp_isRepresentableAtP_numDigits`, future), this
pins down the canonical form. -/
theorem mem_imp_precisionAtMost_numDigits {F : FiniteFormat} {y : Dyadic}
    (hy : y ∈ F.toFormat) (hy_ne : (y : ℝ) ≠ 0) :
    ∃ c e : ℤ, (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ e ∧
                |c| < (2 : ℤ) ^ (F.numDigits (y : ℝ)).toNat := by
  obtain ⟨hP, hQ, _⟩ := hy
  change Dyadic.precisionAtMost F.toFormat.p y at hP
  change Dyadic.quantumAtLeast F.toFormat.exp y at hQ
  set e_y : ℤ := Int.log 2 |(y : ℝ)| with he_y_def
  have habs_pos : 0 < |(y : ℝ)| := abs_pos.mpr hy_ne
  have he_y_hi : |(y : ℝ)| < (2 : ℝ) ^ (e_y + 1) :=
    Int.lt_zpow_succ_log_self (by norm_num : (1 : ℕ) < 2) _
  -- "Quantum case": from y = c·2^e' (with e' ≤ e_y), derive |c| < 2^(e_y - e' + 1).
  have quantum_case : ∀ e' : ℤ,
      (∃ c : ℤ, (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ e') →
      e' ≤ e_y →
      ∃ c : ℤ, (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ e' ∧
                |c| < (2 : ℤ) ^ (e_y - e' + 1).toNat := by
    intro e' ⟨c, hyeq⟩ he_y_ge
    refine ⟨c, hyeq, ?_⟩
    have h_real : (|c| : ℝ) < (2 : ℝ) ^ (e_y - e' + 1) := by
      have h_y_eq : |(y : ℝ)| = |(c : ℝ)| * (2 : ℝ) ^ e' := by
        rw [hyeq, abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)]
      have hsplit : (2 : ℝ) ^ (e_y + 1) =
          (2 : ℝ) ^ (e_y - e' + 1) * (2 : ℝ) ^ e' := by
        rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        congr 1; ring
      have key : |(c : ℝ)| * (2 : ℝ) ^ e' < (2 : ℝ) ^ (e_y - e' + 1) * (2 : ℝ) ^ e' := by
        rw [← hsplit, ← h_y_eq]; exact he_y_hi
      exact lt_of_mul_lt_mul_right key (le_of_lt (zpow_pos (by norm_num) _))
    have h_nat : ((e_y - e' + 1).toNat : ℤ) = e_y - e' + 1 :=
      Int.toNat_of_nonneg (by omega)
    have h_cast : ((2 : ℤ) ^ (e_y - e' + 1).toNat : ℝ) =
        (2 : ℝ) ^ (e_y - e' + 1) := by
      rw [show ((2 : ℤ) ^ (e_y - e' + 1).toNat : ℝ) =
          (2 : ℝ) ^ ((e_y - e' + 1).toNat : ℤ) from by push_cast; rfl, h_nat]
    have : (|c| : ℝ) < ((2 : ℤ) ^ (e_y - e' + 1).toNat : ℝ) := by
      rw [h_cast]; exact h_real
    exact_mod_cast this
  -- For any e' with y = c·2^e' (c ≠ 0), we have e' ≤ e_y.
  have e'_le_e_y : ∀ e' : ℤ,
      (∃ c : ℤ, (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ e') → e' ≤ e_y := by
    intro e' ⟨c, hyeq⟩
    have hc_ne : c ≠ 0 := by
      intro hc0; rw [hc0] at hyeq; push_cast at hyeq
      rw [zero_mul] at hyeq; exact hy_ne hyeq
    have hc_abs_ge : (1 : ℤ) ≤ |c| := Int.one_le_abs hc_ne
    have habs_lo : (2 : ℝ) ^ e' ≤ |(y : ℝ)| := by
      rw [hyeq, abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)]
      calc (2 : ℝ) ^ e'
          = 1 * (2 : ℝ) ^ e' := (one_mul _).symm
        _ ≤ |(c : ℝ)| * (2 : ℝ) ^ e' := by
            apply mul_le_mul_of_nonneg_right _ (zpow_pos (by norm_num) _).le
            exact_mod_cast hc_abs_ge
    by_contra h_lt
    push Not at h_lt
    have h_step : e_y + 1 ≤ e' := by omega
    have h_pow_le : (2 : ℝ) ^ (e_y + 1) ≤ (2 : ℝ) ^ e' :=
      zpow_le_zpow_right₀ (by norm_num) h_step
    linarith [habs_lo, he_y_hi]
  -- Case analysis on (F.p, F.exp).
  cases hp : F.toFormat.p with
  | top =>
    cases hexp : F.toFormat.exp with
    | bot =>
      exfalso; rcases F.finite with h_p_ne | h_exp_ne
      · exact h_p_ne hp
      · exact h_exp_ne hexp
    | coe e' =>
      rw [numDigits_top_coe F hy_ne hexp hp]
      rw [hexp] at hQ
      obtain ⟨c, hyeq, hc_lt⟩ :=
        quantum_case e' (quantumAtLeast_extract hQ)
          (e'_le_e_y e' (quantumAtLeast_extract hQ))
      exact ⟨c, e', hyeq, hc_lt⟩
  | coe p =>
    cases hexp : F.toFormat.exp with
    | bot =>
      rw [numDigits_coe_bot F hy_ne hp hexp]
      rw [hp] at hP
      obtain ⟨c, e, hyeq, hc_lt⟩ := precisionAtMost_extract hP
      refine ⟨c, e, hyeq, ?_⟩
      have h_toNat : ((p : ℕ+) : ℤ).toNat = (p : ℕ) := by simp
      rw [h_toNat]
      exact hc_lt
    | coe e' =>
      rw [numDigits_coe_coe F hy_ne hp hexp]
      rw [hp] at hP
      rw [hexp] at hQ
      rcases le_or_gt ((p : ℕ+) : ℤ) (e_y - e' + 1) with hcase | hcase
      · rw [show min (((p : ℕ+) : ℕ) : ℤ) (e_y - e' + 1) = ((p : ℕ+) : ℤ) from
              min_eq_left hcase]
        have h_toNat : ((p : ℕ+) : ℤ).toNat = (p : ℕ) := by simp
        rw [h_toNat]
        exact precisionAtMost_extract hP
      · rw [show min (((p : ℕ+) : ℕ) : ℤ) (e_y - e' + 1)
              = e_y - e' + 1 from min_eq_right (le_of_lt hcase)]
        obtain ⟨c, hyeq, hc_lt⟩ :=
          quantum_case e' (quantumAtLeast_extract hQ)
            (e'_le_e_y e' (quantumAtLeast_extract hQ))
        exact ⟨c, e', hyeq, hc_lt⟩

end FiniteFormat

/-- A `FiniteFormat` where parity is well-defined: `p ≠ 1` whenever
`exp = ⊥`. Combined with `FiniteFormat.finite`, this is
`(p ≠ ⊤ ∧ p ≠ 1) ∨ exp ≠ ⊥`. Required for `IsOdd` / `IsEven`. -/
structure ParityFormat extends FiniteFormat where
  parity : toFormat.p ≠ 1 ∨ toFormat.exp ≠ ⊥

namespace ParityFormat

/-- Conjunction of `FiniteFormat.finite` and `ParityFormat.parity`,
recovering the original `non-degenerate` invariant. -/
theorem nondegenerate (F : ParityFormat) :
    (F.toFormat.p ≠ ⊤ ∧ F.toFormat.p ≠ 1) ∨ F.toFormat.exp ≠ ⊥ := by
  rcases F.parity with hp1 | hexp
  · rcases F.finite with hpT | hexp
    · exact Or.inl ⟨hpT, hp1⟩
    · exact Or.inr hexp
  · exact Or.inr hexp

/-- A nonzero `y` is *odd* in `F` if its canonical `(c, e)` representation
at the format's rounding precision has odd significand `c`. When `F.p = 1`
the significand is constant (`±1`), and parity is read off the *exponent*
`e` instead. `ParityFormat`'s `parity` invariant ensures the exponent has
an anchor (either via a finite quantum, or via `p > 1` making the
significand case the relevant one). -/
def IsOdd (F : ParityFormat) (y : Dyadic) : Prop :=
  ∃ c e : ℤ,
    Dyadic.IsRepresentableAtP (F.toFiniteFormat.numDigits (y : ℝ)).toNat c e y ∧
    (if F.toFormat.p = ((1 : ℕ+) : WithTop ℕ+) then
        Odd (e - WithBot.unbotD 0 F.toFormat.exp + 1)
      else
        Odd c)

/-- Even-parity dual of `IsOdd`. Convention: `0` is even in every format. -/
def IsEven (F : ParityFormat) (y : Dyadic) : Prop :=
  y = 0 ∨ ∃ c e : ℤ,
    Dyadic.IsRepresentableAtP (F.toFiniteFormat.numDigits (y : ℝ)).toNat c e y ∧
    (if F.toFormat.p = ((1 : ℕ+) : WithTop ℕ+) then
        Even (e - WithBot.unbotD 0 F.toFormat.exp + 1)
      else
        Even c)

@[simp] theorem isEven_zero (F : ParityFormat) : IsEven F 0 := Or.inl rfl

/-- `IsOdd` is invariant under negation. -/
theorem IsOdd.neg {F : ParityFormat} {y : Dyadic} (h : IsOdd F y) :
    IsOdd F (-y) := by
  obtain ⟨c, e, ⟨hyeq, hlow, hhigh⟩, hp⟩ := h
  have h_nd : F.toFiniteFormat.numDigits ((-y : Dyadic) : ℝ) =
      F.toFiniteFormat.numDigits (y : ℝ) := by
    change F.toFiniteFormat.numDigits (-(y : ℝ)) = _
    exact F.toFiniteFormat.numDigits_neg (y : ℝ)
  refine ⟨-c, e, ⟨?_, ?_, ?_⟩, ?_⟩
  · change ((-y : Dyadic) : ℝ) = _
    push_cast
    rw [hyeq]; ring
  · rw [h_nd]; simpa using hlow
  · rw [h_nd]; simpa using hhigh
  · by_cases hp1 : F.toFormat.p = ((1 : ℕ+) : WithTop ℕ+)
    · rw [if_pos hp1]; rw [if_pos hp1] at hp; exact hp
    · rw [if_neg hp1]; rw [if_neg hp1] at hp; exact Odd.neg hp

/-- `IsEven` is invariant under negation. -/
theorem IsEven.neg {F : ParityFormat} {y : Dyadic} (h : IsEven F y) :
    IsEven F (-y) := by
  rcases h with hy0 | ⟨c, e, ⟨hyeq, hlow, hhigh⟩, hp⟩
  · left; rw [hy0]; simp
  · right
    have h_nd : F.toFiniteFormat.numDigits ((-y : Dyadic) : ℝ) =
        F.toFiniteFormat.numDigits (y : ℝ) := by
      change F.toFiniteFormat.numDigits (-(y : ℝ)) = _
      exact F.toFiniteFormat.numDigits_neg (y : ℝ)
    refine ⟨-c, e, ⟨?_, ?_, ?_⟩, ?_⟩
    · change ((-y : Dyadic) : ℝ) = _
      push_cast
      rw [hyeq]; ring
    · rw [h_nd]; simpa using hlow
    · rw [h_nd]; simpa using hhigh
    · by_cases hp1 : F.toFormat.p = ((1 : ℕ+) : WithTop ℕ+)
      · rw [if_pos hp1]; rw [if_pos hp1] at hp; exact hp
      · rw [if_neg hp1]; rw [if_neg hp1] at hp; exact Even.neg hp

/-- `IsOdd F y` implies `numDigits ≥ 1`. -/
theorem IsOdd.numDigits_pos {F : ParityFormat} {y : Dyadic} (h : IsOdd F y) :
    0 < F.toFiniteFormat.numDigits (y : ℝ) := by
  obtain ⟨c, _, ⟨_, hlow, hhigh⟩, _⟩ := h
  by_contra h_le
  push Not at h_le
  have h_toNat : (F.toFiniteFormat.numDigits ((y : Dyadic) : ℝ)).toNat = 0 :=
    Int.toNat_of_nonpos h_le
  rw [h_toNat] at hlow hhigh
  have h1 : (1 : ℤ) ≤ |c| := by simpa using hlow
  have h2 : |c| < (1 : ℤ) := by simpa using hhigh
  omega

/-- An `IsOdd` value is nonzero. -/
theorem IsOdd.ne_zero {F : ParityFormat} {y : Dyadic} (h : IsOdd F y) :
    y ≠ 0 := by
  intro hy0
  obtain ⟨c, e, ⟨hyeq, hlow, _⟩, _⟩ := h
  rw [hy0] at hyeq
  have h2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have hc_zero : (c : ℝ) = 0 := by
    push_cast at hyeq
    rcases mul_eq_zero.mp hyeq.symm with h | h
    · exact h
    · linarith
  have hc_zero_int : c = 0 := by exact_mod_cast hc_zero
  rw [hc_zero_int, abs_zero] at hlow
  have : (1 : ℤ) ≤ (2 : ℤ) ^ ((F.toFiniteFormat.numDigits ((y : Dyadic) : ℝ)).toNat - 1) :=
    one_le_pow₀ (by norm_num)
  linarith

/-- If `(c, e)` is a canonical-form representation at `F`'s `numDigits y`
precision and `F.p ≠ 1`, then `F.IsOdd y ↔ Odd c`. The forward direction
uses `IsRepresentableAtP.unique` to pin the canonical form, then reads off
the parity. -/
theorem isOdd_iff_odd_of_canonical {F : ParityFormat} {y : Dyadic}
    {c e : ℤ}
    (h_rep : Dyadic.IsRepresentableAtP (F.toFiniteFormat.numDigits (y : ℝ)).toNat
      c e y)
    (hp_ne_1 : F.toFormat.p ≠ ((1 : ℕ+) : WithTop ℕ+)) :
    F.IsOdd y ↔ Odd c := by
  constructor
  · rintro ⟨c', e', h_rep', h_odd⟩
    rw [if_neg hp_ne_1] at h_odd
    obtain ⟨h_c, _⟩ := h_rep'.unique h_rep
    rw [← h_c]; exact h_odd
  · intro h_odd
    exact ⟨c, e, h_rep, by rw [if_neg hp_ne_1]; exact h_odd⟩

/-- Dual of `isOdd_iff_odd_of_canonical` for `IsEven`. -/
theorem isEven_iff_even_of_canonical {F : ParityFormat} {y : Dyadic}
    {c e : ℤ}
    (h_rep : Dyadic.IsRepresentableAtP (F.toFiniteFormat.numDigits (y : ℝ)).toNat
      c e y)
    (hp_ne_1 : F.toFormat.p ≠ ((1 : ℕ+) : WithTop ℕ+)) :
    F.IsEven y ↔ Even c := by
  constructor
  · rintro (rfl | ⟨c', e', h_rep', h_even⟩)
    · -- y = 0: IsRepresentableAtP at any precision forces |c| ≥ 1,
      -- but y = 0 forces c = 0. Contradiction.
      obtain ⟨hyeq, h_lo, _⟩ := h_rep
      have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
      have hc_zero : (c : ℝ) = 0 := by
        push_cast at hyeq
        rcases mul_eq_zero.mp hyeq.symm with h | h
        · exact h
        · linarith
      have hc_zero_int : c = 0 := by exact_mod_cast hc_zero
      rw [hc_zero_int]
      exact Even.zero
    · rw [if_neg hp_ne_1] at h_even
      obtain ⟨h_c, _⟩ := h_rep'.unique h_rep
      rw [← h_c]; exact h_even
  · intro h_even
    right; exact ⟨c, e, h_rep, by rw [if_neg hp_ne_1]; exact h_even⟩

/-- Parity dichotomy: for `y` with a canonical representation,
`IsEven y ↔ ¬ IsOdd y`. Combines the two characterizations through integer
parity, handling both `p = 1` (exponent parity) and `p ≠ 1` (significand
parity). -/
theorem isEven_iff_not_isOdd_of_canonical {F : ParityFormat} {y : Dyadic}
    {c e : ℤ}
    (h_rep : Dyadic.IsRepresentableAtP (F.toFiniteFormat.numDigits (y : ℝ)).toNat
      c e y) :
    F.IsEven y ↔ ¬ F.IsOdd y := by
  have hy_ne : (y : ℝ) ≠ 0 := h_rep.ne_zero
  by_cases hp1 : F.toFormat.p = ((1 : ℕ+) : WithTop ℕ+)
  · constructor
    · rintro (h_y0 | ⟨c', e', h_rep', h_par⟩) ⟨c'', e'', h_rep'', h_par_odd⟩
      · exact hy_ne (congrArg Subtype.val h_y0)
      · rw [if_pos hp1] at h_par h_par_odd
        obtain ⟨_, h_e_eq⟩ := h_rep'.unique h_rep''
        rw [← h_e_eq] at h_par_odd
        exact (Int.not_odd_iff_even.mpr h_par) h_par_odd
    · intro h_not_odd
      right
      refine ⟨c, e, h_rep, ?_⟩
      rw [if_pos hp1]
      by_contra h_not_even
      apply h_not_odd
      refine ⟨c, e, h_rep, ?_⟩
      rw [if_pos hp1]
      exact Int.not_even_iff_odd.mp h_not_even
  · rw [isEven_iff_even_of_canonical h_rep hp1]
    rw [isOdd_iff_odd_of_canonical h_rep hp1]
    constructor
    · exact Int.not_odd_iff_even.mpr
    · exact Int.not_odd_iff_even.mp

/-- Floating-point characterization (non-saturation): when `F.p = (p:ℕ+)`,
`F.p ≠ 1`, `F.exp = ⊥`, and `|k| ∈ [2^(p-1), 2^p)`, then
`F.IsOdd (Dyadic.ofIntZpow k e) ↔ Odd k`. -/
theorem isOdd_iff_odd_at_canonical_floating {F : ParityFormat}
    {p : ℕ+} (hp_eq : F.toFormat.p = ((p : ℕ+) : WithTop ℕ+))
    (hp_ne_1 : F.toFormat.p ≠ ((1 : ℕ+) : WithTop ℕ+))
    (hexp_bot : F.toFormat.exp = ⊥) {k e : ℤ}
    (hk_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |k|)
    (hk_hi : |k| < (2 : ℤ) ^ (p : ℕ)) :
    F.IsOdd (Dyadic.ofIntZpow k e) ↔ Odd k := by
  set y : Dyadic := Dyadic.ofIntZpow k e
  have h_y_real : (y : ℝ) = (k : ℝ) * (2 : ℝ) ^ e := Dyadic.coe_ofIntZpow k e
  have hk_ne : k ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hk_lo
    have hpos : (1 : ℤ) ≤ (2 : ℤ) ^ ((p : ℕ) - 1) := one_le_pow₀ (by norm_num)
    linarith
  have h_y_ne : (y : ℝ) ≠ 0 := by
    rw [h_y_real]
    have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
    exact mul_ne_zero (Int.cast_ne_zero.mpr hk_ne) (ne_of_gt h_2e_pos)
  have h_nd_toNat : (F.toFiniteFormat.numDigits (y : ℝ)).toNat = (p : ℕ) := by
    rw [F.toFiniteFormat.numDigits_coe_bot h_y_ne hp_eq hexp_bot]; simp
  have h_rep : Dyadic.IsRepresentableAtP
      (F.toFiniteFormat.numDigits (y : ℝ)).toNat k e y := by
    rw [h_nd_toNat]
    exact Dyadic.isRepresentableAtP_of_bounds h_y_real hk_lo hk_hi
  exact isOdd_iff_odd_of_canonical h_rep hp_ne_1

/-- Floating-point saturation case: `|k| = 2^p` forces `F.IsOdd (k·2^e) = False`
(via renormalization, the canonical significand is `±2^(p-1)`, which is even). -/
theorem not_isOdd_at_saturation {F : ParityFormat}
    {p : ℕ+} (hp_eq : F.toFormat.p = ((p : ℕ+) : WithTop ℕ+))
    (hp_ne_1 : F.toFormat.p ≠ ((1 : ℕ+) : WithTop ℕ+))
    (hexp_bot : F.toFormat.exp = ⊥) {k e : ℤ}
    (hk_eq : |k| = (2 : ℤ) ^ (p : ℕ)) :
    ¬ F.IsOdd (Dyadic.ofIntZpow k e) := by
  set y : Dyadic := Dyadic.ofIntZpow k e
  have h_y_real : (y : ℝ) = (k : ℝ) * (2 : ℝ) ^ e := Dyadic.coe_ofIntZpow k e
  have hp_pos : 1 ≤ (p : ℕ) := p.pos
  have hp_ge_2 : 2 ≤ (p : ℕ) := by
    by_contra h_neg
    push Not at h_neg
    have hp_one : (p : ℕ) = 1 := by omega
    have : p = 1 := Subtype.ext hp_one
    exact hp_ne_1 (by rw [hp_eq, this])
  have hk_ne : k ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hk_eq
    have hpos : (1 : ℤ) ≤ (2 : ℤ) ^ (p : ℕ) := one_le_pow₀ (by norm_num)
    linarith
  have h_y_ne : (y : ℝ) ≠ 0 := by
    rw [h_y_real]
    have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
    exact mul_ne_zero (Int.cast_ne_zero.mpr hk_ne) (ne_of_gt h_2e_pos)
  have h_nd_toNat : (F.toFiniteFormat.numDigits (y : ℝ)).toNat = (p : ℕ) := by
    rw [F.toFiniteFormat.numDigits_coe_bot h_y_ne hp_eq hexp_bot]; simp
  have h_rep : Dyadic.IsRepresentableAtP
      (F.toFiniteFormat.numDigits (y : ℝ)).toNat (k / 2) (e + 1) y := by
    rw [h_nd_toNat]
    exact Dyadic.isRepresentableAtP_of_saturation hp_pos h_y_real hk_eq
  rw [isOdd_iff_odd_of_canonical h_rep hp_ne_1]
  -- Need: ¬ Odd (k/2). k/2 = ±2^(p-1), and p-1 ≥ 1, so 2 ∣ 2^(p-1).
  intro h_odd
  have h_4_dvd_k : (4 : ℤ) ∣ k := by
    have h4 : (4 : ℤ) = (2 : ℤ) ^ 2 := by norm_num
    rw [h4]
    rcases (abs_eq (by positivity : (0 : ℤ) ≤ (2 : ℤ) ^ (p : ℕ))).mp hk_eq
      with hk | hk
    · rw [hk]; exact pow_dvd_pow 2 hp_ge_2
    · rw [hk]; exact Dvd.dvd.neg_right (pow_dvd_pow 2 hp_ge_2)
  obtain ⟨c, hc⟩ := h_4_dvd_k
  have h_k_div_2 : k / 2 = 2 * c := by
    rw [hc, show (4 : ℤ) * c = 2 * (2 * c) by ring,
        Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]
  rw [h_k_div_2] at h_odd
  obtain ⟨m, hm⟩ := h_odd
  omega

/-- `Int.log 2 |k · 2^e'| = Int.log 2 |k| + e'` for nonzero integer `k`. The
"log distributes through multiplication by powers of 2" identity. -/
theorem log_abs_mul_zpow {k : ℤ} (hk_ne : k ≠ 0) (e' : ℤ) :
    Int.log 2 |(k : ℝ) * (2 : ℝ) ^ e'| = Int.log 2 (|k| : ℝ) + e' := by
  have h_2_ne : (2 : ℝ) ≠ 0 := by norm_num
  have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e' := zpow_pos (by norm_num) _
  have h_abs_k_pos : (0 : ℝ) < (|k| : ℝ) := by
    have h1 : (1 : ℤ) ≤ |k| := Int.one_le_abs hk_ne
    have h2 : (1 : ℝ) ≤ (|k| : ℝ) := by exact_mod_cast h1
    linarith
  have h_abs_y : |(k : ℝ) * (2 : ℝ) ^ e'| = (|k| : ℝ) * (2 : ℝ) ^ e' := by
    rw [abs_mul, abs_of_pos h_2e_pos]
  rw [h_abs_y]
  have h_y_pos : (0 : ℝ) < (|k| : ℝ) * (2 : ℝ) ^ e' := mul_pos h_abs_k_pos h_2e_pos
  have h_lb_k : (2 : ℝ) ^ (Int.log 2 (|k| : ℝ)) ≤ (|k| : ℝ) :=
    Int.zpow_log_le_self (by norm_num : (1 : ℕ) < 2) h_abs_k_pos
  have h_ub_k : (|k| : ℝ) < (2 : ℝ) ^ (Int.log 2 (|k| : ℝ) + 1) :=
    Int.lt_zpow_succ_log_self (by norm_num : (1 : ℕ) < 2) _
  have h_lb : (2 : ℝ) ^ (Int.log 2 (|k| : ℝ) + e') ≤ (|k| : ℝ) * (2 : ℝ) ^ e' := by
    rw [zpow_add₀ h_2_ne]
    exact mul_le_mul_of_nonneg_right h_lb_k h_2e_pos.le
  have h_ub : (|k| : ℝ) * (2 : ℝ) ^ e' < (2 : ℝ) ^ (Int.log 2 (|k| : ℝ) + e' + 1) := by
    rw [show Int.log 2 (|k| : ℝ) + e' + 1 = (Int.log 2 (|k| : ℝ) + 1) + e' by ring,
        zpow_add₀ h_2_ne]
    exact mul_lt_mul_of_pos_right h_ub_k h_2e_pos
  have h_le : Int.log 2 (|k| : ℝ) + e' ≤ Int.log 2 ((|k| : ℝ) * (2 : ℝ) ^ e') :=
    (Int.zpow_le_iff_le_log (by norm_num : (1 : ℕ) < 2) h_y_pos).mp h_lb
  have h_lt : Int.log 2 ((|k| : ℝ) * (2 : ℝ) ^ e') < Int.log 2 (|k| : ℝ) + e' + 1 :=
    (Int.lt_zpow_iff_log_lt (by norm_num : (1 : ℕ) < 2) h_y_pos).mp h_ub
  omega

/-- Mixed normal regime characterization. `numDigits y = p` when
`log|y| - e' + 1 ≥ p` (the precision branch of min wins). Then IsOdd ↔ Odd k
via canonical IsRepresentableAtP at p bits. -/
theorem isOdd_iff_odd_at_canonical_mixed_normal {F : ParityFormat}
    {p : ℕ+} (hp_eq : F.toFormat.p = ((p : ℕ+) : WithTop ℕ+))
    (hp_ne_1 : F.toFormat.p ≠ ((1 : ℕ+) : WithTop ℕ+))
    {e' : ℤ} (hexp : F.toFormat.exp = (e' : WithBot ℤ))
    {y : Dyadic} (hy_ne : (y : ℝ) ≠ 0)
    (h_log_y_ge : ((p : ℕ) : ℤ) ≤ Int.log 2 |(y : ℝ)| - e' + 1)
    {k e_c : ℤ} (h_y_eq : (y : ℝ) = (k : ℝ) * (2 : ℝ) ^ e_c)
    (hk_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |k|)
    (hk_hi : |k| < (2 : ℤ) ^ (p : ℕ)) :
    F.IsOdd y ↔ Odd k := by
  have h_nd_eq : F.toFiniteFormat.numDigits (y : ℝ) = ((p : ℕ) : ℤ) := by
    rw [F.toFiniteFormat.numDigits_coe_coe hy_ne hp_eq hexp]
    exact min_eq_left h_log_y_ge
  have h_nd_toNat : (F.toFiniteFormat.numDigits (y : ℝ)).toNat = (p : ℕ) := by
    rw [h_nd_eq]; simp
  have h_rep : Dyadic.IsRepresentableAtP
      (F.toFiniteFormat.numDigits (y : ℝ)).toNat k e_c y := by
    rw [h_nd_toNat]
    exact ⟨h_y_eq, hk_lo, hk_hi⟩
  exact isOdd_iff_odd_of_canonical h_rep hp_ne_1

/-- Mixed subnormal regime characterization. `numDigits y = log|y| - e' + 1`
when `p > log|y| - e' + 1` (the quantum branch of min wins). For
`y = k · 2^e'` with `k ≠ 0`, IsOdd ↔ Odd k (via canonical `(k, e')` form). -/
theorem isOdd_iff_odd_at_canonical_mixed_subnormal {F : ParityFormat}
    {p : ℕ+} (hp_eq : F.toFormat.p = ((p : ℕ+) : WithTop ℕ+))
    (hp_ne_1 : F.toFormat.p ≠ ((1 : ℕ+) : WithTop ℕ+))
    {e' : ℤ} (hexp : F.toFormat.exp = (e' : WithBot ℤ))
    {k : ℤ} (hk_ne : k ≠ 0)
    (h_log_k_lt_p : Int.log 2 (|k| : ℝ) + 1 ≤ ((p : ℕ) : ℤ)) :
    F.IsOdd (Dyadic.ofIntZpow k e') ↔ Odd k := by
  set y : Dyadic := Dyadic.ofIntZpow k e'
  have h_y_real : (y : ℝ) = (k : ℝ) * (2 : ℝ) ^ e' := Dyadic.coe_ofIntZpow k e'
  have h_y_ne : (y : ℝ) ≠ 0 := by
    rw [h_y_real]
    exact mul_ne_zero (Int.cast_ne_zero.mpr hk_ne)
      (ne_of_gt (zpow_pos (by norm_num) _))
  have h_abs_k_pos : (0 : ℝ) < (|k| : ℝ) := by
    have h1 : (1 : ℤ) ≤ |k| := Int.one_le_abs hk_ne
    have h2 : (1 : ℝ) ≤ (|k| : ℝ) := by exact_mod_cast h1
    linarith
  have h_log_k_nn : 0 ≤ Int.log 2 (|k| : ℝ) := by
    have h_one_le : (1 : ℝ) ≤ (|k| : ℝ) := by
      have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk_ne
      exact_mod_cast this
    rw [show (0 : ℤ) = Int.log 2 (1 : ℝ) by simp [Int.log_one_right]]
    exact Int.log_mono_right (by linarith) h_one_le
  have h_log_eq : Int.log 2 |(y : ℝ)| = Int.log 2 (|k| : ℝ) + e' := by
    rw [h_y_real]; exact log_abs_mul_zpow hk_ne e'
  -- numDigits y = min(p, log|y| - e' + 1) = log|y| - e' + 1 (subnormal: ≤ p).
  have h_nd_eq : F.toFiniteFormat.numDigits (y : ℝ) = Int.log 2 (|k| : ℝ) + 1 := by
    rw [F.toFiniteFormat.numDigits_coe_coe h_y_ne hp_eq hexp]
    have h_log_y_eq : Int.log 2 |(y : ℝ)| - e' + 1 = Int.log 2 (|k| : ℝ) + 1 := by
      linarith [h_log_eq]
    rw [h_log_y_eq]
    exact min_eq_right h_log_k_lt_p
  have h_nd_toNat : (F.toFiniteFormat.numDigits (y : ℝ)).toNat =
      (Int.log 2 (|k| : ℝ)).toNat + 1 := by
    rw [h_nd_eq]
    have h1 : ((Int.log 2 (|k| : ℝ)).toNat : ℤ) = Int.log 2 (|k| : ℝ) :=
      Int.toNat_of_nonneg h_log_k_nn
    omega
  have h_rep : Dyadic.IsRepresentableAtP
      (F.toFiniteFormat.numDigits (y : ℝ)).toNat k e' y := by
    rw [h_nd_toNat]
    refine ⟨h_y_real, ?_, ?_⟩
    · have h_simp : (Int.log 2 (|k| : ℝ)).toNat + 1 - 1 = (Int.log 2 (|k| : ℝ)).toNat := by
        omega
      rw [h_simp]
      have h_2pow_le : (2 : ℝ) ^ (Int.log 2 (|k| : ℝ)) ≤ (|k| : ℝ) :=
        Int.zpow_log_le_self (by norm_num : (1 : ℕ) < 2) h_abs_k_pos
      have h_log_nat_eq : ((Int.log 2 (|k| : ℝ)).toNat : ℤ) = Int.log 2 (|k| : ℝ) :=
        Int.toNat_of_nonneg h_log_k_nn
      have h_cast : ((2 : ℤ) ^ (Int.log 2 (|k| : ℝ)).toNat : ℝ) =
          (2 : ℝ) ^ (Int.log 2 (|k| : ℝ)) := by
        rw [show (Int.log 2 (|k| : ℝ)) = ((Int.log 2 (|k| : ℝ)).toNat : ℤ) from
              h_log_nat_eq.symm, zpow_natCast]
        push_cast; rfl
      have h_real_le : ((2 : ℤ) ^ (Int.log 2 (|k| : ℝ)).toNat : ℝ) ≤ (|k| : ℝ) := by
        rw [h_cast]; exact h_2pow_le
      exact_mod_cast h_real_le
    · have h_2pow_gt : (|k| : ℝ) < (2 : ℝ) ^ (Int.log 2 (|k| : ℝ) + 1) :=
        Int.lt_zpow_succ_log_self (by norm_num : (1 : ℕ) < 2) _
      have h_cast : ((2 : ℤ) ^ ((Int.log 2 (|k| : ℝ)).toNat + 1) : ℝ) =
          (2 : ℝ) ^ (Int.log 2 (|k| : ℝ) + 1) := by
        push_cast
        rw [← zpow_natCast (2 : ℝ) ((Int.log 2 (|k| : ℝ)).toNat + 1)]
        congr 1
        push_cast
        omega
      have h_real_lt : (|k| : ℝ) < ((2 : ℤ) ^ ((Int.log 2 (|k| : ℝ)).toNat + 1) : ℝ) := by
        rw [h_cast]; exact h_2pow_gt
      exact_mod_cast h_real_lt
  exact isOdd_iff_odd_of_canonical h_rep hp_ne_1

/-- Mixed-normal saturation: when `|k| = 2^p`, IsOdd is false (canonical
form renormalizes to `(k/2, e_c+1)` with `|k/2| = 2^(p-1)`, which is even
for `p ≥ 2`). -/
theorem not_isOdd_at_saturation_mixed_normal {F : ParityFormat}
    {p : ℕ+} (hp_eq : F.toFormat.p = ((p : ℕ+) : WithTop ℕ+))
    (hp_ne_1 : F.toFormat.p ≠ ((1 : ℕ+) : WithTop ℕ+))
    {e' : ℤ} (hexp : F.toFormat.exp = (e' : WithBot ℤ))
    {y : Dyadic} (hy_ne : (y : ℝ) ≠ 0)
    (h_log_y_ge : ((p : ℕ) : ℤ) ≤ Int.log 2 |(y : ℝ)| - e' + 1)
    {k e_c : ℤ} (h_y_eq : (y : ℝ) = (k : ℝ) * (2 : ℝ) ^ e_c)
    (hk_eq : |k| = (2 : ℤ) ^ (p : ℕ)) :
    ¬ F.IsOdd y := by
  have hp_pos : 1 ≤ (p : ℕ) := p.pos
  have hp_ge_2 : 2 ≤ (p : ℕ) := by
    by_contra h_neg
    push Not at h_neg
    have hp_one : (p : ℕ) = 1 := by omega
    have : p = 1 := Subtype.ext hp_one
    exact hp_ne_1 (by rw [hp_eq, this])
  have h_nd_eq : F.toFiniteFormat.numDigits (y : ℝ) = ((p : ℕ) : ℤ) := by
    rw [F.toFiniteFormat.numDigits_coe_coe hy_ne hp_eq hexp]
    exact min_eq_left h_log_y_ge
  have h_nd_toNat : (F.toFiniteFormat.numDigits (y : ℝ)).toNat = (p : ℕ) := by
    rw [h_nd_eq]; simp
  have h_rep : Dyadic.IsRepresentableAtP
      (F.toFiniteFormat.numDigits (y : ℝ)).toNat (k / 2) (e_c + 1) y := by
    rw [h_nd_toNat]
    exact Dyadic.isRepresentableAtP_of_saturation hp_pos h_y_eq hk_eq
  rw [isOdd_iff_odd_of_canonical h_rep hp_ne_1]
  intro h_odd
  have h_4_dvd_k : (4 : ℤ) ∣ k := by
    have h4 : (4 : ℤ) = (2 : ℤ) ^ 2 := by norm_num
    rw [h4]
    rcases (abs_eq (by positivity : (0 : ℤ) ≤ (2 : ℤ) ^ (p : ℕ))).mp hk_eq
      with hk | hk
    · rw [hk]; exact pow_dvd_pow 2 hp_ge_2
    · rw [hk]; exact Dvd.dvd.neg_right (pow_dvd_pow 2 hp_ge_2)
  obtain ⟨c, hc⟩ := h_4_dvd_k
  have h_k_div_2 : k / 2 = 2 * c := by
    rw [hc, show (4 : ℤ) * c = 2 * (2 * c) by ring,
        Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]
  rw [h_k_div_2] at h_odd
  obtain ⟨m, hm⟩ := h_odd
  omega

/-- Alternating parity in the mixed-normal regime (`p ≠ 1`). Mirror of
`alternating_parity_floating`, with saturation handled by the mixed-normal
characterization + saturation lemma. -/
theorem alternating_parity_mixed_normal_pne1 {F : ParityFormat}
    {p : ℕ+} (hp_eq : F.toFormat.p = ((p : ℕ+) : WithTop ℕ+))
    (hp_ne_1 : F.toFormat.p ≠ ((1 : ℕ+) : WithTop ℕ+))
    {e' : ℤ} (hexp : F.toFormat.exp = (e' : WithBot ℤ))
    {y_lo y_hi : Dyadic} (h_y_lo_ne : (y_lo : ℝ) ≠ 0) (h_y_hi_ne : (y_hi : ℝ) ≠ 0)
    (h_log_lo : ((p : ℕ) : ℤ) ≤ Int.log 2 |(y_lo : ℝ)| - e' + 1)
    (h_log_hi : ((p : ℕ) : ℤ) ≤ Int.log 2 |(y_hi : ℝ)| - e' + 1)
    {lo : ℤ} {e : ℤ}
    (h_y_lo_eq : (y_lo : ℝ) = (lo : ℝ) * (2 : ℝ) ^ e)
    (h_y_hi_eq : (y_hi : ℝ) = ((lo + 1 : ℤ) : ℝ) * (2 : ℝ) ^ e)
    (hlo_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo|)
    (hlo_hi : |lo| ≤ (2 : ℤ) ^ (p : ℕ))
    (hlop1_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo + 1|)
    (hlop1_hi : |lo + 1| ≤ (2 : ℤ) ^ (p : ℕ)) :
    ¬ F.IsOdd y_lo → F.IsOdd y_hi := by
  intro h_not_odd
  rcases lt_or_eq_of_le hlo_hi with hlo_lt | hlo_sat
  · rw [isOdd_iff_odd_at_canonical_mixed_normal hp_eq hp_ne_1 hexp h_y_lo_ne
      h_log_lo h_y_lo_eq hlo_lo hlo_lt] at h_not_odd
    have h_even_lo : Even lo := Int.not_odd_iff_even.mp h_not_odd
    have h_odd_lop1 : Odd (lo + 1) := Even.add_one h_even_lo
    rcases lt_or_eq_of_le hlop1_hi with hlop1_lt | hlop1_sat
    · rw [isOdd_iff_odd_at_canonical_mixed_normal hp_eq hp_ne_1 hexp h_y_hi_ne
        h_log_hi h_y_hi_eq hlop1_lo hlop1_lt]
      exact h_odd_lop1
    · exfalso
      have h_even_lop1 : Even (lo + 1) := by
        have h2p_nn : (0 : ℤ) ≤ (2 : ℤ) ^ (p : ℕ) := by positivity
        rcases (abs_eq h2p_nn).mp hlop1_sat with h | h
        · rw [h]
          refine ⟨(2 : ℤ) ^ ((p : ℕ) - 1), ?_⟩
          have := Dyadic.two_pow_succ_pred p.pos
          linarith
        · rw [h]
          refine ⟨-((2 : ℤ) ^ ((p : ℕ) - 1)), ?_⟩
          have := Dyadic.two_pow_succ_pred p.pos
          linarith
      exact (Int.not_odd_iff_even.mpr h_even_lop1) h_odd_lop1
  · -- lo saturated: |lo| = 2^p. From canonical-exponent properties, this forces
    -- a specific sign (depends on x's sign).
    -- For our use case: hlop1_hi says |lo+1| ≤ 2^p. lo = 2^p ⟹ lo+1 = 2^p+1
    -- contradicts hlop1_hi. So lo = -2^p, lo+1 = -2^p+1 (non-saturated).
    have h2p_nn : (0 : ℤ) ≤ (2 : ℤ) ^ (p : ℕ) := by positivity
    rcases (abs_eq h2p_nn).mp hlo_sat with hlo_pos | hlo_neg
    · -- lo = 2^p: lo + 1 = 2^p + 1, |lo+1| = 2^p+1 > 2^p, contradicting hlop1_hi.
      exfalso
      rw [hlo_pos] at hlop1_hi
      have : (2 : ℤ) ^ (p : ℕ) + 1 > 0 := by positivity
      have h_abs : |(2 : ℤ) ^ (p : ℕ) + 1| = (2 : ℤ) ^ (p : ℕ) + 1 := abs_of_pos this
      linarith
    · -- lo = -2^p: lo + 1 = -(2^p - 1), |lo+1| = 2^p - 1 < 2^p (non-sat).
      have h_lop1_lt : |lo + 1| < (2 : ℤ) ^ (p : ℕ) := by
        rw [hlo_neg]
        have h_pos_inner : (0 : ℤ) < (2 : ℤ) ^ (p : ℕ) - 1 := by
          have : (1 : ℤ) ≤ (2 : ℤ) ^ (p : ℕ) := one_le_pow₀ (by norm_num)
          have h_two_le : (2 : ℤ) ≤ (2 : ℤ) ^ (p : ℕ) := by
            calc (2 : ℤ) = (2 : ℤ) ^ 1 := by ring
              _ ≤ (2 : ℤ) ^ (p : ℕ) := pow_le_pow_right₀ (by norm_num) p.pos
          linarith
        have h_eq : -((2 : ℤ) ^ (p : ℕ)) + 1 = -((2 : ℤ) ^ (p : ℕ) - 1) := by ring
        rw [h_eq, abs_neg, abs_of_pos h_pos_inner]
        linarith
      rw [isOdd_iff_odd_at_canonical_mixed_normal hp_eq hp_ne_1 hexp h_y_hi_ne
        h_log_hi h_y_hi_eq hlop1_lo h_lop1_lt]
      rw [hlo_neg]
      have h_2p_even : Even ((2 : ℤ) ^ (p : ℕ)) := by
        refine ⟨(2 : ℤ) ^ ((p : ℕ) - 1), ?_⟩
        have := Dyadic.two_pow_succ_pred p.pos
        linarith
      have h_neg_2p_even : Even (-((2 : ℤ) ^ (p : ℕ))) := h_2p_even.neg
      exact h_neg_2p_even.add_one

/-- Alternating parity in the mixed-subnormal regime (`p ≠ 1`). When both
`|lo|` and `|lo + 1|` fit in `log + 1 ≤ p` bits, IsOdd ↔ Odd k reduces to
the standard alternating-parity argument. Edge cases: `lo = 0` (dlo = 0,
trivially `¬IsOdd`) and `lo = -1` (vacuously ruled out by `¬IsOdd dlo`). -/
theorem alternating_parity_mixed_subnormal_pne1 {F : ParityFormat}
    {p : ℕ+} (hp_eq : F.toFormat.p = ((p : ℕ+) : WithTop ℕ+))
    (hp_ne_1 : F.toFormat.p ≠ ((1 : ℕ+) : WithTop ℕ+))
    {e' : ℤ} (hexp : F.toFormat.exp = (e' : WithBot ℤ))
    {lo : ℤ} (h_lo_lt : Int.log 2 (|lo| : ℝ) + 1 ≤ ((p : ℕ) : ℤ))
    (h_lop1_lt : Int.log 2 (|lo + 1| : ℝ) + 1 ≤ ((p : ℕ) : ℤ)) :
    ¬ F.IsOdd (Dyadic.ofIntZpow lo e') →
    F.IsOdd (Dyadic.ofIntZpow (lo + 1) e') := by
  intro h_not_odd
  by_cases hlo_zero : lo = 0
  · subst hlo_zero
    rw [show (0 : ℤ) + 1 = 1 from by ring]
    rw [isOdd_iff_odd_at_canonical_mixed_subnormal hp_eq hp_ne_1 hexp
        (by norm_num : (1 : ℤ) ≠ 0) ?_]
    · exact ⟨0, by ring⟩
    · -- log 2 |1| + 1 = log 2 1 + 1 = 0 + 1 = 1 ≤ p.
      simp [show |(1 : ℤ)| = 1 from rfl, Int.log_one_right]
      exact_mod_cast p.pos
  · rw [isOdd_iff_odd_at_canonical_mixed_subnormal hp_eq hp_ne_1 hexp
        hlo_zero h_lo_lt] at h_not_odd
    have h_even : Even lo := Int.not_odd_iff_even.mp h_not_odd
    have h_odd_lop1 : Odd (lo + 1) := Even.add_one h_even
    have h_lop1_ne : lo + 1 ≠ 0 := by
      intro h
      have : lo = -1 := by omega
      subst this
      exact absurd h_even (by decide)
    have h_lop1_lt' : Int.log 2 (|((lo + 1 : ℤ) : ℝ)|) + 1 ≤ ((p : ℕ) : ℤ) := by
      have h_cast : ((lo + 1 : ℤ) : ℝ) = (lo : ℝ) + 1 := by push_cast; ring
      rw [h_cast]
      exact h_lop1_lt
    rw [isOdd_iff_odd_at_canonical_mixed_subnormal hp_eq hp_ne_1 hexp
        h_lop1_ne h_lop1_lt']
    exact h_odd_lop1

/-- Mixed case characterization at `p = 1`. Given `y = k · 2^e_c` with
`|k| = 1` (so the 1-bit canonical form is `(k, e_c)`) and `e_c ≥ e'`,
`F.IsOdd y ↔ Odd (e_c - e' + 1)`. -/
theorem isOdd_p1_iff_at_canonical_mixed {F : ParityFormat}
    (hp_eq : F.toFormat.p = ((1 : ℕ+) : WithTop ℕ+))
    {e' : ℤ} (hexp : F.toFormat.exp = (e' : WithBot ℤ))
    {k e_c : ℤ} (hk_eq : |k| = 1) (h_ec_ge : e' ≤ e_c) :
    F.IsOdd (Dyadic.ofIntZpow k e_c) ↔ Odd (e_c - e' + 1) := by
  set y : Dyadic := Dyadic.ofIntZpow k e_c
  have hk_ne : k ≠ 0 := by
    intro h0; rw [h0] at hk_eq; simp at hk_eq
  have h_y_real : (y : ℝ) = (k : ℝ) * (2 : ℝ) ^ e_c := Dyadic.coe_ofIntZpow k e_c
  have h_y_ne : (y : ℝ) ≠ 0 := by
    rw [h_y_real]
    exact mul_ne_zero (Int.cast_ne_zero.mpr hk_ne)
      (ne_of_gt (zpow_pos (by norm_num) _))
  -- log|y| = e_c (since |k| = 1).
  have h_log_eq : Int.log 2 |(y : ℝ)| = e_c := by
    rw [h_y_real]
    rw [log_abs_mul_zpow hk_ne e_c]
    have h_abs_k_one : (|k| : ℝ) = 1 := by exact_mod_cast hk_eq
    rw [h_abs_k_one]
    simp [Int.log_one_right]
  -- numDigits y = min(1, e_c - e' + 1) = 1 (since e_c ≥ e').
  have h_nd_eq : F.toFiniteFormat.numDigits (y : ℝ) = 1 := by
    rw [F.toFiniteFormat.numDigits_coe_coe h_y_ne hp_eq hexp]
    rw [h_log_eq]
    have h1 : (1 : ℤ) ≤ e_c - e' + 1 := by linarith
    exact min_eq_left h1
  have h_nd_toNat : (F.toFiniteFormat.numDigits (y : ℝ)).toNat = 1 := by
    rw [h_nd_eq]; rfl
  -- Canonical form (k, e_c) at 1-bit precision.
  have h_rep : Dyadic.IsRepresentableAtP
      (F.toFiniteFormat.numDigits (y : ℝ)).toNat k e_c y := by
    rw [h_nd_toNat]
    refine ⟨h_y_real, ?_, ?_⟩
    · simp; rw [hk_eq]
    · rw [hk_eq]; norm_num
  -- Apply the IsOdd definition.
  unfold IsOdd
  constructor
  · rintro ⟨c', e'', h_rep', h_par⟩
    rw [if_pos hp_eq] at h_par
    -- By uniqueness, (c', e'') = (k, e_c).
    obtain ⟨_, h_e_eq⟩ := h_rep'.unique h_rep
    rw [← h_e_eq]
    have h_unbot : WithBot.unbotD 0 F.toFormat.exp = e' := by
      rw [hexp]; rfl
    rw [h_unbot] at h_par
    exact h_par
  · intro h_odd
    refine ⟨k, e_c, h_rep, ?_⟩
    rw [if_pos hp_eq]
    have h_unbot : WithBot.unbotD 0 F.toFormat.exp = e' := by
      rw [hexp]; rfl
    rw [h_unbot]
    exact h_odd

/-- Alternating parity at `p = 1` mixed-subnormal (`e = e'`).
For `|lo|, |lo+1| ≤ 2`: if dlo is not IsOdd, then dhi is. -/
theorem alternating_parity_mixed_subnormal_p1 {F : ParityFormat}
    (hp_eq : F.toFormat.p = ((1 : ℕ+) : WithTop ℕ+))
    {e' : ℤ} (hexp : F.toFormat.exp = (e' : WithBot ℤ))
    {lo : ℤ} (hlo_hi : |lo| ≤ 2) (hlop1_hi : |lo + 1| ≤ 2) :
    ¬ F.IsOdd (Dyadic.ofIntZpow lo e') →
    F.IsOdd (Dyadic.ofIntZpow (lo + 1) e') := by
  intro hodd
  have h_lo_ge : -2 ≤ lo := (abs_le.mp hlo_hi).1
  have h_lop1_le : lo + 1 ≤ 2 := (abs_le.mp hlop1_hi).2
  have h_lo_le_1 : lo ≤ 1 := by linarith
  interval_cases lo
  · -- lo = -2: dlo = -2·2^e' = -1·2^(e'+1).
    have h_dlo_canon : Dyadic.ofIntZpow (-2 : ℤ) e' =
        Dyadic.ofIntZpow (-1 : ℤ) (e' + 1) := by
      apply Subtype.ext
      rw [Dyadic.coe_ofIntZpow, Dyadic.coe_ofIntZpow,
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
      push_cast; ring
    rw [h_dlo_canon] at hodd
    rw [isOdd_p1_iff_at_canonical_mixed hp_eq hexp (k := -1) (e_c := e' + 1)
        (by decide) (by linarith)] at hodd
    rw [show ((-2 : ℤ) + 1) = (-1 : ℤ) by ring]
    rw [isOdd_p1_iff_at_canonical_mixed hp_eq hexp (k := -1) (e_c := e')
        (by decide) (le_refl _)]
    exact ⟨0, by ring⟩
  · -- lo = -1: hodd is False (IsOdd dlo = Odd 1 = True).
    exfalso; apply hodd
    rw [isOdd_p1_iff_at_canonical_mixed hp_eq hexp (k := -1) (e_c := e')
        (by decide) (le_refl _)]
    exact ⟨0, by ring⟩
  · -- lo = 0: dlo = 0, vacuous. dhi = 1·2^e'.
    rw [show ((0 : ℤ) + 1) = (1 : ℤ) by ring]
    rw [isOdd_p1_iff_at_canonical_mixed hp_eq hexp (k := 1) (e_c := e')
        (by decide) (le_refl _)]
    exact ⟨0, by ring⟩
  · -- lo = 1: hodd is False.
    exfalso; apply hodd
    rw [isOdd_p1_iff_at_canonical_mixed hp_eq hexp (k := 1) (e_c := e')
        (by decide) (le_refl _)]
    exact ⟨0, by ring⟩

/-- Alternating parity at `p = 1` mixed-normal (`e > e'`, `|lo|, |lo+1| ≥ 1`).
-/
theorem alternating_parity_mixed_normal_p1 {F : ParityFormat}
    (hp_eq : F.toFormat.p = ((1 : ℕ+) : WithTop ℕ+))
    {e' : ℤ} (hexp : F.toFormat.exp = (e' : WithBot ℤ))
    {lo e : ℤ} (h_e_ge : e' ≤ e)
    (hlo_lo : 1 ≤ |lo|) (hlo_hi : |lo| ≤ 2)
    (hlop1_lo : 1 ≤ |lo + 1|) (hlop1_hi : |lo + 1| ≤ 2) :
    ¬ F.IsOdd (Dyadic.ofIntZpow lo e) →
    F.IsOdd (Dyadic.ofIntZpow (lo + 1) e) := by
  intro hodd
  have h_lo_ge : -2 ≤ lo := (abs_le.mp hlo_hi).1
  have h_lop1_le : lo + 1 ≤ 2 := (abs_le.mp hlop1_hi).2
  have h_lo_le_1 : lo ≤ 1 := by linarith
  have h_lo_ne_neg1 : lo ≠ -1 := by
    intro h_eq
    rw [h_eq] at hlop1_lo
    rw [show ((-1 : ℤ) + 1) = 0 by ring] at hlop1_lo
    simp at hlop1_lo
  have h_lo_ne_0 : lo ≠ 0 := by
    intro h_eq; rw [h_eq] at hlo_lo; simp at hlo_lo
  interval_cases lo
  · -- lo = -2.
    have h_dlo_canon : Dyadic.ofIntZpow (-2 : ℤ) e =
        Dyadic.ofIntZpow (-1 : ℤ) (e + 1) := by
      apply Subtype.ext
      rw [Dyadic.coe_ofIntZpow, Dyadic.coe_ofIntZpow,
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
      push_cast; ring
    rw [h_dlo_canon] at hodd
    rw [isOdd_p1_iff_at_canonical_mixed hp_eq hexp (k := -1) (e_c := e + 1)
        (by decide) (by linarith)] at hodd
    rw [show ((-2 : ℤ) + 1) = (-1 : ℤ) by ring]
    rw [isOdd_p1_iff_at_canonical_mixed hp_eq hexp (k := -1) (e_c := e)
        (by decide) h_e_ge]
    have h_even : Even (e + 1 - e' + 1) := Int.not_odd_iff_even.mp hodd
    obtain ⟨m, hm⟩ := h_even
    exact ⟨m - 1, by omega⟩
  · exact absurd rfl h_lo_ne_neg1
  · exact absurd rfl h_lo_ne_0
  · -- lo = 1.
    rw [isOdd_p1_iff_at_canonical_mixed hp_eq hexp (k := 1) (e_c := e)
        (by decide) h_e_ge] at hodd
    rw [show ((1 : ℤ) + 1) = (2 : ℤ) by ring]
    have h_dhi_canon : Dyadic.ofIntZpow (2 : ℤ) e =
        Dyadic.ofIntZpow (1 : ℤ) (e + 1) := by
      apply Subtype.ext
      rw [Dyadic.coe_ofIntZpow, Dyadic.coe_ofIntZpow,
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
      push_cast; ring
    rw [h_dhi_canon]
    rw [isOdd_p1_iff_at_canonical_mixed hp_eq hexp (k := 1) (e_c := e + 1)
        (by decide) (by linarith)]
    have h_even : Even (e - e' + 1) := Int.not_odd_iff_even.mp hodd
    obtain ⟨m, hm⟩ := h_even
    exact ⟨m, by omega⟩

/-- Anti-alternating parity at `p = 1` mixed-subnormal. -/
theorem not_both_isOdd_mixed_subnormal_p1 {F : ParityFormat}
    (hp_eq : F.toFormat.p = ((1 : ℕ+) : WithTop ℕ+))
    {e' : ℤ} (hexp : F.toFormat.exp = (e' : WithBot ℤ))
    {lo : ℤ} (hlo_hi : |lo| ≤ 2) (hlop1_hi : |lo + 1| ≤ 2) :
    ¬ (F.IsOdd (Dyadic.ofIntZpow lo e') ∧
       F.IsOdd (Dyadic.ofIntZpow (lo + 1) e')) := by
  rintro ⟨h1, h2⟩
  have h_lo_ge : -2 ≤ lo := (abs_le.mp hlo_hi).1
  have h_lop1_le : lo + 1 ≤ 2 := (abs_le.mp hlop1_hi).2
  have h_lo_le_1 : lo ≤ 1 := by linarith
  have h_2_even : Even ((2 : ℤ)) := ⟨1, by ring⟩
  have h_not_odd_2 : ¬ Odd ((2 : ℤ)) := Int.not_odd_iff_even.mpr h_2_even
  have h_zero_eq : ∀ (e_c : ℤ), Dyadic.ofIntZpow (0 : ℤ) e_c = 0 := fun e_c =>
    Subtype.ext (by rw [Dyadic.coe_ofIntZpow]; simp)
  interval_cases lo
  · -- lo = -2: dlo = -1·2^(e'+1). IsOdd dlo ↔ Odd 2 = False.
    have h_dlo_canon : Dyadic.ofIntZpow (-2 : ℤ) e' =
        Dyadic.ofIntZpow (-1 : ℤ) (e' + 1) := by
      apply Subtype.ext
      rw [Dyadic.coe_ofIntZpow, Dyadic.coe_ofIntZpow,
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
      push_cast; ring
    rw [h_dlo_canon] at h1
    rw [isOdd_p1_iff_at_canonical_mixed hp_eq hexp (k := -1) (e_c := e' + 1)
        (by decide) (by linarith)] at h1
    apply h_not_odd_2
    have h_eq : e' + 1 - e' + 1 = 2 := by ring
    rw [← h_eq]; exact h1
  · -- lo = -1: dhi = 0. IsOdd 0 = False.
    rw [show ((-1 : ℤ) + 1) = (0 : ℤ) by ring] at h2
    rw [h_zero_eq] at h2
    exact IsOdd.ne_zero h2 rfl
  · -- lo = 0: dlo = 0.
    rw [h_zero_eq] at h1
    exact IsOdd.ne_zero h1 rfl
  · -- lo = 1: dhi = 2·2^e' = 1·2^(e'+1). IsOdd dhi ↔ Odd 2 = False.
    rw [show ((1 : ℤ) + 1) = (2 : ℤ) by ring] at h2
    have h_dhi_canon : Dyadic.ofIntZpow (2 : ℤ) e' =
        Dyadic.ofIntZpow (1 : ℤ) (e' + 1) := by
      apply Subtype.ext
      rw [Dyadic.coe_ofIntZpow, Dyadic.coe_ofIntZpow,
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
      push_cast; ring
    rw [h_dhi_canon] at h2
    rw [isOdd_p1_iff_at_canonical_mixed hp_eq hexp (k := 1) (e_c := e' + 1)
        (by decide) (by linarith)] at h2
    apply h_not_odd_2
    have h_eq : e' + 1 - e' + 1 = 2 := by ring
    rw [← h_eq]; exact h2

/-- Anti-alternating parity at `p = 1` mixed-normal. -/
theorem not_both_isOdd_mixed_normal_p1 {F : ParityFormat}
    (hp_eq : F.toFormat.p = ((1 : ℕ+) : WithTop ℕ+))
    {e' : ℤ} (hexp : F.toFormat.exp = (e' : WithBot ℤ))
    {lo e : ℤ} (h_e_ge : e' ≤ e)
    (hlo_lo : 1 ≤ |lo|) (hlo_hi : |lo| ≤ 2)
    (hlop1_lo : 1 ≤ |lo + 1|) (hlop1_hi : |lo + 1| ≤ 2) :
    ¬ (F.IsOdd (Dyadic.ofIntZpow lo e) ∧
       F.IsOdd (Dyadic.ofIntZpow (lo + 1) e)) := by
  rintro ⟨h1, h2⟩
  have h_lo_ge : -2 ≤ lo := (abs_le.mp hlo_hi).1
  have h_lop1_le : lo + 1 ≤ 2 := (abs_le.mp hlop1_hi).2
  have h_lo_le_1 : lo ≤ 1 := by linarith
  have h_lo_ne_neg1 : lo ≠ -1 := by
    intro h_eq
    rw [h_eq] at hlop1_lo
    rw [show ((-1 : ℤ) + 1) = 0 by ring] at hlop1_lo
    simp at hlop1_lo
  have h_lo_ne_0 : lo ≠ 0 := by
    intro h_eq; rw [h_eq] at hlo_lo; simp at hlo_lo
  interval_cases lo
  · -- lo = -2.
    have h_dlo_canon : Dyadic.ofIntZpow (-2 : ℤ) e =
        Dyadic.ofIntZpow (-1 : ℤ) (e + 1) := by
      apply Subtype.ext
      rw [Dyadic.coe_ofIntZpow, Dyadic.coe_ofIntZpow,
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
      push_cast; ring
    rw [h_dlo_canon] at h1
    rw [isOdd_p1_iff_at_canonical_mixed hp_eq hexp (k := -1) (e_c := e + 1)
        (by decide) (by linarith)] at h1
    rw [show ((-2 : ℤ) + 1) = (-1 : ℤ) by ring] at h2
    rw [isOdd_p1_iff_at_canonical_mixed hp_eq hexp (k := -1) (e_c := e)
        (by decide) h_e_ge] at h2
    -- h1 : Odd(e+1 - e' + 1) = Odd(e-e'+2). h2 : Odd(e-e'+1). Both odd → impossible.
    obtain ⟨m1, hm1⟩ := h1
    obtain ⟨m2, hm2⟩ := h2
    omega
  · exact absurd rfl h_lo_ne_neg1
  · exact absurd rfl h_lo_ne_0
  · -- lo = 1.
    rw [isOdd_p1_iff_at_canonical_mixed hp_eq hexp (k := 1) (e_c := e)
        (by decide) h_e_ge] at h1
    rw [show ((1 : ℤ) + 1) = (2 : ℤ) by ring] at h2
    have h_dhi_canon : Dyadic.ofIntZpow (2 : ℤ) e =
        Dyadic.ofIntZpow (1 : ℤ) (e + 1) := by
      apply Subtype.ext
      rw [Dyadic.coe_ofIntZpow, Dyadic.coe_ofIntZpow,
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
      push_cast; ring
    rw [h_dhi_canon] at h2
    rw [isOdd_p1_iff_at_canonical_mixed hp_eq hexp (k := 1) (e_c := e + 1)
        (by decide) (by linarith)] at h2
    obtain ⟨m1, hm1⟩ := h1
    obtain ⟨m2, hm2⟩ := h2
    omega

/-- Anti-alternating parity (mixed-subnormal, `p ≠ 1`). Not both `dlo` and
`dhi` can be `IsOdd`. -/
theorem not_both_isOdd_mixed_subnormal_pne1 {F : ParityFormat}
    {p : ℕ+} (hp_eq : F.toFormat.p = ((p : ℕ+) : WithTop ℕ+))
    (hp_ne_1 : F.toFormat.p ≠ ((1 : ℕ+) : WithTop ℕ+))
    {e' : ℤ} (hexp : F.toFormat.exp = (e' : WithBot ℤ))
    {lo : ℤ}
    (h_lo_lt : Int.log 2 (|lo| : ℝ) + 1 ≤ ((p : ℕ) : ℤ))
    (h_lop1_lt : Int.log 2 (|lo + 1| : ℝ) + 1 ≤ ((p : ℕ) : ℤ)) :
    ¬ (F.IsOdd (Dyadic.ofIntZpow lo e') ∧
       F.IsOdd (Dyadic.ofIntZpow (lo + 1) e')) := by
  rintro ⟨h1, h2⟩
  have h_lo_ne : lo ≠ 0 := by
    intro hlo0
    subst hlo0
    have h_zero : Dyadic.ofIntZpow (0 : ℤ) e' = 0 :=
      Subtype.ext (by rw [Dyadic.coe_ofIntZpow]; simp)
    exact IsOdd.ne_zero h1 h_zero
  have h_lop1_ne : lo + 1 ≠ 0 := by
    intro hlop1_0
    have h_zero : Dyadic.ofIntZpow (lo + 1 : ℤ) e' = 0 :=
      Subtype.ext (by rw [Dyadic.coe_ofIntZpow, hlop1_0]; simp)
    exact IsOdd.ne_zero h2 h_zero
  rw [isOdd_iff_odd_at_canonical_mixed_subnormal hp_eq hp_ne_1 hexp h_lo_ne h_lo_lt] at h1
  have h_lop1_lt' : Int.log 2 (|((lo + 1 : ℤ) : ℝ)|) + 1 ≤ ((p : ℕ) : ℤ) := by
    have h_cast : ((lo + 1 : ℤ) : ℝ) = (lo : ℝ) + 1 := by push_cast; ring
    rw [h_cast]; exact h_lop1_lt
  rw [isOdd_iff_odd_at_canonical_mixed_subnormal hp_eq hp_ne_1 hexp
      h_lop1_ne h_lop1_lt'] at h2
  obtain ⟨m1, hm1⟩ := h1
  obtain ⟨m2, hm2⟩ := h2
  omega

/-- Anti-alternating parity (mixed-normal, `p ≠ 1`). Not both `dlo` and
`dhi` can be `IsOdd`. -/
theorem not_both_isOdd_mixed_normal_pne1 {F : ParityFormat}
    {p : ℕ+} (hp_eq : F.toFormat.p = ((p : ℕ+) : WithTop ℕ+))
    (hp_ne_1 : F.toFormat.p ≠ ((1 : ℕ+) : WithTop ℕ+))
    {e' : ℤ} (hexp : F.toFormat.exp = (e' : WithBot ℤ))
    {y_lo y_hi : Dyadic} (h_y_lo_ne : (y_lo : ℝ) ≠ 0) (h_y_hi_ne : (y_hi : ℝ) ≠ 0)
    (h_log_lo : ((p : ℕ) : ℤ) ≤ Int.log 2 |(y_lo : ℝ)| - e' + 1)
    (h_log_hi : ((p : ℕ) : ℤ) ≤ Int.log 2 |(y_hi : ℝ)| - e' + 1)
    {lo : ℤ} {e : ℤ}
    (h_y_lo_eq : (y_lo : ℝ) = (lo : ℝ) * (2 : ℝ) ^ e)
    (h_y_hi_eq : (y_hi : ℝ) = ((lo + 1 : ℤ) : ℝ) * (2 : ℝ) ^ e)
    (hlo_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo|)
    (hlo_hi : |lo| ≤ (2 : ℤ) ^ (p : ℕ))
    (hlop1_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo + 1|)
    (hlop1_hi : |lo + 1| ≤ (2 : ℤ) ^ (p : ℕ)) :
    ¬ (F.IsOdd y_lo ∧ F.IsOdd y_hi) := by
  rintro ⟨h1, h2⟩
  rcases lt_or_eq_of_le hlo_hi with hlo_lt | hlo_sat
  · rw [isOdd_iff_odd_at_canonical_mixed_normal hp_eq hp_ne_1 hexp h_y_lo_ne
      h_log_lo h_y_lo_eq hlo_lo hlo_lt] at h1
    rcases lt_or_eq_of_le hlop1_hi with hlop1_lt | hlop1_sat
    · rw [isOdd_iff_odd_at_canonical_mixed_normal hp_eq hp_ne_1 hexp h_y_hi_ne
        h_log_hi h_y_hi_eq hlop1_lo hlop1_lt] at h2
      obtain ⟨m1, hm1⟩ := h1
      obtain ⟨m2, hm2⟩ := h2
      omega
    · exact (not_isOdd_at_saturation_mixed_normal hp_eq hp_ne_1 hexp h_y_hi_ne
        h_log_hi h_y_hi_eq hlop1_sat) h2
  · exact (not_isOdd_at_saturation_mixed_normal hp_eq hp_ne_1 hexp h_y_lo_ne
      h_log_lo h_y_lo_eq hlo_sat) h1

/-- Saturation in floating-point implies `IsEven`. At `|k| = 2^p`,
canonical form is `(±2^(p-1), e+1)` with `c = ±2^(p-1)` even for `p ≥ 2`. -/
theorem isEven_at_saturation_floating {F : ParityFormat}
    {p : ℕ+} (hp_eq : F.toFormat.p = ((p : ℕ+) : WithTop ℕ+))
    (hp_ne_1 : F.toFormat.p ≠ ((1 : ℕ+) : WithTop ℕ+))
    (hexp_bot : F.toFormat.exp = ⊥) {k e : ℤ}
    (hk_eq : |k| = (2 : ℤ) ^ (p : ℕ)) :
    F.IsEven (Dyadic.ofIntZpow k e) := by
  set y : Dyadic := Dyadic.ofIntZpow k e
  have h_y_real : (y : ℝ) = (k : ℝ) * (2 : ℝ) ^ e := Dyadic.coe_ofIntZpow k e
  have hp_pos : 1 ≤ (p : ℕ) := p.pos
  have hp_ge_2 : 2 ≤ (p : ℕ) := by
    by_contra h_neg
    push Not at h_neg
    have hp_one : (p : ℕ) = 1 := by omega
    have : p = 1 := Subtype.ext hp_one
    exact hp_ne_1 (by rw [hp_eq, this])
  have hk_ne : k ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hk_eq
    have hpos : (1 : ℤ) ≤ (2 : ℤ) ^ (p : ℕ) := one_le_pow₀ (by norm_num)
    linarith
  have h_y_ne : (y : ℝ) ≠ 0 := by
    rw [h_y_real]
    have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
    exact mul_ne_zero (Int.cast_ne_zero.mpr hk_ne) (ne_of_gt h_2e_pos)
  have h_nd_toNat : (F.toFiniteFormat.numDigits (y : ℝ)).toNat = (p : ℕ) := by
    rw [F.toFiniteFormat.numDigits_coe_bot h_y_ne hp_eq hexp_bot]; simp
  have h_rep : Dyadic.IsRepresentableAtP
      (F.toFiniteFormat.numDigits (y : ℝ)).toNat (k / 2) (e + 1) y := by
    rw [h_nd_toNat]
    exact Dyadic.isRepresentableAtP_of_saturation hp_pos h_y_real hk_eq
  rw [isEven_iff_even_of_canonical h_rep hp_ne_1]
  -- k = ±2^p ⟹ k/2 = ±2^(p-1) which is even for p ≥ 2.
  have h2p_nonneg : (0 : ℤ) ≤ (2 : ℤ) ^ (p : ℕ) := by positivity
  have h_2pm2_pow : (2 : ℤ) ^ ((p : ℕ) - 1) = 2 * 2 ^ ((p : ℕ) - 2) := by
    have h_eq : (p : ℕ) - 2 + 1 = (p : ℕ) - 1 := by omega
    rw [← h_eq, pow_succ]; ring
  have h_div_2p : (2 : ℤ) ^ (p : ℕ) / 2 = 2 ^ ((p : ℕ) - 1) := by
    have h_eq : (p : ℕ) - 1 + 1 = (p : ℕ) := by omega
    rw [← h_eq, pow_succ]
    exact Int.mul_ediv_cancel _ (by norm_num : (2 : ℤ) ≠ 0)
  rcases (abs_eq h2p_nonneg).mp hk_eq with hk_pos | hk_neg
  · refine ⟨(2 : ℤ) ^ ((p : ℕ) - 2), ?_⟩
    rw [hk_pos, h_div_2p, h_2pm2_pow]; ring
  · refine ⟨-((2 : ℤ) ^ ((p : ℕ) - 2)), ?_⟩
    rw [hk_neg]
    have h_div_neg_2p : (-(2 : ℤ) ^ (p : ℕ)) / 2 = -((2 : ℤ) ^ ((p : ℕ) - 1)) := by
      have h_2p_factor : (2 : ℤ) ^ (p : ℕ) = 2 ^ ((p : ℕ) - 1) * 2 := by
        conv_lhs => rw [show (p : ℕ) = ((p : ℕ) - 1) + 1 from by omega]
        rw [pow_succ]
      have h_factor : -(2 : ℤ) ^ (p : ℕ) = 2 * (-(2 : ℤ) ^ ((p : ℕ) - 1)) := by
        rw [h_2p_factor]; ring
      rw [h_factor, Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]
    rw [h_div_neg_2p, h_2pm2_pow]; ring

/-- Canonical h_rep construction for fixed-point: for `k ≠ 0`,
the (k, e') pair is the canonical representation of `ofIntZpow k e'` at
`numDigits`-precision. -/
private theorem canonical_rep_fixedpoint {F : ParityFormat}
    (hp_top : F.toFormat.p = ⊤) {e' : ℤ}
    (hexp : F.toFormat.exp = (e' : WithBot ℤ)) {k : ℤ} (hk_ne : k ≠ 0) :
    Dyadic.IsRepresentableAtP
      (F.toFiniteFormat.numDigits ((Dyadic.ofIntZpow k e' : Dyadic) : ℝ)).toNat
      k e' (Dyadic.ofIntZpow k e') := by
  set y : Dyadic := Dyadic.ofIntZpow k e'
  have h_y_real : (y : ℝ) = (k : ℝ) * (2 : ℝ) ^ e' := Dyadic.coe_ofIntZpow k e'
  have h_y_ne : (y : ℝ) ≠ 0 := by
    rw [h_y_real]
    exact mul_ne_zero (Int.cast_ne_zero.mpr hk_ne)
      (ne_of_gt (zpow_pos (by norm_num) _))
  have h_abs_pos : (0 : ℝ) < (|k| : ℝ) := by
    have h1 : (1 : ℤ) ≤ |k| := Int.one_le_abs hk_ne
    have h2 : (1 : ℝ) ≤ (|k| : ℝ) := by exact_mod_cast h1
    linarith
  have h_log_nn : 0 ≤ Int.log 2 (|k| : ℝ) := by
    have h_one_le : (1 : ℝ) ≤ (|k| : ℝ) := by
      have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk_ne
      exact_mod_cast this
    rw [show (0 : ℤ) = Int.log 2 (1 : ℝ) by simp [Int.log_one_right]]
    exact Int.log_mono_right (by linarith) h_one_le
  have h_log_eq : Int.log 2 |(y : ℝ)| = Int.log 2 (|k| : ℝ) + e' := by
    rw [h_y_real]; exact log_abs_mul_zpow hk_ne e'
  have h_nd_eq : F.toFiniteFormat.numDigits (y : ℝ) = Int.log 2 (|k| : ℝ) + 1 := by
    rw [F.toFiniteFormat.numDigits_top_coe h_y_ne hexp hp_top]
    linarith
  have h_nd_toNat : (F.toFiniteFormat.numDigits (y : ℝ)).toNat =
      (Int.log 2 (|k| : ℝ)).toNat + 1 := by
    rw [h_nd_eq]
    have h1 : ((Int.log 2 (|k| : ℝ)).toNat : ℤ) = Int.log 2 (|k| : ℝ) :=
      Int.toNat_of_nonneg h_log_nn
    omega
  rw [h_nd_toNat]
  refine ⟨h_y_real, ?_, ?_⟩
  · have h_simp : (Int.log 2 (|k| : ℝ)).toNat + 1 - 1 =
        (Int.log 2 (|k| : ℝ)).toNat := by omega
    rw [h_simp]
    have h_2pow_le : (2 : ℝ) ^ (Int.log 2 (|k| : ℝ)) ≤ (|k| : ℝ) :=
      Int.zpow_log_le_self (by norm_num : (1 : ℕ) < 2) h_abs_pos
    have h_nat : ((Int.log 2 (|k| : ℝ)).toNat : ℤ) = Int.log 2 (|k| : ℝ) :=
      Int.toNat_of_nonneg h_log_nn
    have h_cast : ((2 : ℤ) ^ (Int.log 2 (|k| : ℝ)).toNat : ℝ) =
        (2 : ℝ) ^ (Int.log 2 (|k| : ℝ)) := by
      rw [show (Int.log 2 (|k| : ℝ)) = ((Int.log 2 (|k| : ℝ)).toNat : ℤ) from
        h_nat.symm, zpow_natCast]
      push_cast; rfl
    have h_real_le : ((2 : ℤ) ^ (Int.log 2 (|k| : ℝ)).toNat : ℝ) ≤ (|k| : ℝ) := by
      rw [h_cast]; exact h_2pow_le
    exact_mod_cast h_real_le
  · have h_2pow_gt : (|k| : ℝ) < (2 : ℝ) ^ (Int.log 2 (|k| : ℝ) + 1) :=
      Int.lt_zpow_succ_log_self (by norm_num : (1 : ℕ) < 2) _
    have h_cast : ((2 : ℤ) ^ ((Int.log 2 (|k| : ℝ)).toNat + 1) : ℝ) =
        (2 : ℝ) ^ (Int.log 2 (|k| : ℝ) + 1) := by
      push_cast
      rw [← zpow_natCast (2 : ℝ) ((Int.log 2 (|k| : ℝ)).toNat + 1)]
      congr 1; push_cast; omega
    have h_real_lt : (|k| : ℝ) <
        ((2 : ℤ) ^ ((Int.log 2 (|k| : ℝ)).toNat + 1) : ℝ) := by
      rw [h_cast]; exact h_2pow_gt
    exact_mod_cast h_real_lt

/-- Alternating `IsEven` (fixed-point). -/
theorem alternating_isEven_fixedpoint {F : ParityFormat}
    (hp_top : F.toFormat.p = ⊤) {e' : ℤ}
    (hexp : F.toFormat.exp = (e' : WithBot ℤ)) {lo : ℤ} :
    ¬ F.IsEven (Dyadic.ofIntZpow lo e') →
    F.IsEven (Dyadic.ofIntZpow (lo + 1) e') := by
  intro h_not_even
  have hp_ne_1 : F.toFormat.p ≠ ((1 : ℕ+) : WithTop ℕ+) := by rw [hp_top]; decide
  by_cases hlo_z : lo = 0
  · exfalso; apply h_not_even
    rw [hlo_z, show Dyadic.ofIntZpow (0 : ℤ) e' = 0 from
      Subtype.ext (by rw [Dyadic.coe_ofIntZpow]; simp)]
    exact isEven_zero F
  by_cases hlop1_z : lo + 1 = 0
  · rw [show Dyadic.ofIntZpow (lo + 1) e' = 0 from
      Subtype.ext (by rw [Dyadic.coe_ofIntZpow, hlop1_z]; push_cast; ring)]
    exact isEven_zero F
  · have h_rep_dlo := canonical_rep_fixedpoint hp_top hexp hlo_z
    have h_rep_dhi := canonical_rep_fixedpoint hp_top hexp hlop1_z
    rw [isEven_iff_not_isOdd_of_canonical h_rep_dlo] at h_not_even
    push Not at h_not_even
    rw [isOdd_iff_odd_of_canonical h_rep_dlo hp_ne_1] at h_not_even
    have h_even_lop1 : Even (lo + 1) := Odd.add_one h_not_even
    rw [isEven_iff_not_isOdd_of_canonical h_rep_dhi]
    rw [isOdd_iff_odd_of_canonical h_rep_dhi hp_ne_1]
    exact Int.not_odd_iff_even.mpr h_even_lop1

/-- Alternating parity for `IsEven` (floating). If `dlo` is not `IsEven`,
then `dhi` is. -/
theorem alternating_isEven_floating {F : ParityFormat}
    {p : ℕ+} (hp_eq : F.toFormat.p = ((p : ℕ+) : WithTop ℕ+))
    (hp_ne_1 : F.toFormat.p ≠ ((1 : ℕ+) : WithTop ℕ+))
    (hexp_bot : F.toFormat.exp = ⊥) {lo e : ℤ}
    (hlo_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo|)
    (hlo_hi : |lo| ≤ (2 : ℤ) ^ (p : ℕ))
    (hlop1_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo + 1|)
    (hlop1_hi : |lo + 1| ≤ (2 : ℤ) ^ (p : ℕ)) :
    ¬ F.IsEven (Dyadic.ofIntZpow lo e) →
    F.IsEven (Dyadic.ofIntZpow (lo + 1) e) := by
  intro h_not_even
  rcases lt_or_eq_of_le hlo_hi with hlo_lt | hlo_sat
  · -- dlo non-sat: characterization applies. ¬IsEven dlo ↔ ¬Even lo (for lo ≠ 0).
    have hlo_ne : lo ≠ 0 := by
      intro h; rw [h, abs_zero] at hlo_lo
      have : (1 : ℤ) ≤ (2 : ℤ) ^ ((p : ℕ) - 1) := one_le_pow₀ (by norm_num)
      linarith
    -- Construct h_rep for dlo.
    set dlo : Dyadic := Dyadic.ofIntZpow lo e
    have h_dlo_real : (dlo : ℝ) = (lo : ℝ) * (2 : ℝ) ^ e := Dyadic.coe_ofIntZpow lo e
    have h_dlo_ne : (dlo : ℝ) ≠ 0 := by
      rw [h_dlo_real]
      exact mul_ne_zero (Int.cast_ne_zero.mpr hlo_ne)
        (ne_of_gt (zpow_pos (by norm_num) _))
    have h_nd_dlo : (F.toFiniteFormat.numDigits (dlo : ℝ)).toNat = (p : ℕ) := by
      rw [F.toFiniteFormat.numDigits_coe_bot h_dlo_ne hp_eq hexp_bot]; simp
    have h_rep_dlo : Dyadic.IsRepresentableAtP
        (F.toFiniteFormat.numDigits (dlo : ℝ)).toNat lo e dlo := by
      rw [h_nd_dlo]
      exact Dyadic.isRepresentableAtP_of_bounds h_dlo_real hlo_lo hlo_lt
    rw [isEven_iff_even_of_canonical h_rep_dlo hp_ne_1] at h_not_even
    have h_odd_lo : Odd lo := Int.not_even_iff_odd.mp h_not_even
    have h_even_lop1 : Even (lo + 1) := Odd.add_one h_odd_lo
    -- Case on dhi sat.
    rcases lt_or_eq_of_le hlop1_hi with hlop1_lt | hlop1_sat
    · -- dhi non-sat. Apply isEven_iff_even_of_canonical for dhi.
      have hlop1_ne : lo + 1 ≠ 0 := by
        intro h; rw [h, abs_zero] at hlop1_lo
        have : (1 : ℤ) ≤ (2 : ℤ) ^ ((p : ℕ) - 1) := one_le_pow₀ (by norm_num)
        linarith
      set dhi : Dyadic := Dyadic.ofIntZpow (lo + 1) e
      have h_dhi_real : (dhi : ℝ) = ((lo + 1 : ℤ) : ℝ) * (2 : ℝ) ^ e :=
        Dyadic.coe_ofIntZpow (lo + 1) e
      have h_dhi_ne : (dhi : ℝ) ≠ 0 := by
        rw [h_dhi_real]
        exact mul_ne_zero (Int.cast_ne_zero.mpr hlop1_ne)
          (ne_of_gt (zpow_pos (by norm_num) _))
      have h_nd_dhi : (F.toFiniteFormat.numDigits (dhi : ℝ)).toNat = (p : ℕ) := by
        rw [F.toFiniteFormat.numDigits_coe_bot h_dhi_ne hp_eq hexp_bot]; simp
      have h_rep_dhi : Dyadic.IsRepresentableAtP
          (F.toFiniteFormat.numDigits (dhi : ℝ)).toNat (lo + 1) e dhi := by
        rw [h_nd_dhi]
        exact Dyadic.isRepresentableAtP_of_bounds h_dhi_real hlop1_lo hlop1_lt
      rw [isEven_iff_even_of_canonical h_rep_dhi hp_ne_1]
      exact h_even_lop1
    · -- dhi sat: IsEven via saturation.
      exact isEven_at_saturation_floating hp_eq hp_ne_1 hexp_bot hlop1_sat
  · -- dlo sat: IsEven dlo by isEven_at_saturation_floating. Contradicts ¬IsEven dlo.
    exfalso; apply h_not_even
    exact isEven_at_saturation_floating hp_eq hp_ne_1 hexp_bot hlo_sat

/-- `IsOdd` depends only on `toFormat`: two `ParityFormat`s with equal `toFormat`
agree on `IsOdd`. Uses Lean's proof irrelevance for the `finite`/`parity`
Prop fields. -/
theorem IsOdd_iff_of_toFormat_eq {F1 F2 : ParityFormat}
    (h : F1.toFormat = F2.toFormat) (y : Dyadic) :
    F1.IsOdd y ↔ F2.IsOdd y := by
  rcases F1 with ⟨⟨FF1, fin1⟩, par1⟩
  rcases F2 with ⟨⟨FF2, fin2⟩, par2⟩
  cases h
  rfl

/-- Dual of `IsOdd_iff_of_toFormat_eq` for `IsEven`. -/
theorem IsEven_iff_of_toFormat_eq {F1 F2 : ParityFormat}
    (h : F1.toFormat = F2.toFormat) (y : Dyadic) :
    F1.IsEven y ↔ F2.IsEven y := by
  rcases F1 with ⟨⟨FF1, fin1⟩, par1⟩
  rcases F2 with ⟨⟨FF2, fin2⟩, par2⟩
  cases h
  rfl

/-- Fixed-point characterization (`F.p = ⊤, F.exp = (e' : ℤ)`):
`F.IsOdd (Dyadic.ofIntZpow k e') ↔ Odd k`, for `k ≠ 0`. No saturation
since `numDigits` adapts to `log|k| + 1`. -/
theorem isOdd_iff_odd_at_canonical_fixedpoint {F : ParityFormat}
    (hp_top : F.toFormat.p = ⊤) {e' : ℤ}
    (hexp : F.toFormat.exp = (e' : WithBot ℤ)) {k : ℤ} (hk_ne : k ≠ 0) :
    F.IsOdd (Dyadic.ofIntZpow k e') ↔ Odd k := by
  set y : Dyadic := Dyadic.ofIntZpow k e'
  have h_y_real : (y : ℝ) = (k : ℝ) * (2 : ℝ) ^ e' := Dyadic.coe_ofIntZpow k e'
  have h_y_ne : (y : ℝ) ≠ 0 := by
    rw [h_y_real]
    exact mul_ne_zero (Int.cast_ne_zero.mpr hk_ne)
      (ne_of_gt (zpow_pos (by norm_num) _))
  have hp_ne_1 : F.toFormat.p ≠ ((1 : ℕ+) : WithTop ℕ+) := by rw [hp_top]; decide
  have h_abs_k_pos : (0 : ℝ) < (|k| : ℝ) := by
    have h1 : (1 : ℤ) ≤ |k| := Int.one_le_abs hk_ne
    have h2 : (1 : ℝ) ≤ (|k| : ℝ) := by exact_mod_cast h1
    linarith
  have h_log_k_nn : 0 ≤ Int.log 2 (|k| : ℝ) := by
    have h_one_le : (1 : ℝ) ≤ (|k| : ℝ) := by
      have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk_ne
      exact_mod_cast this
    rw [show (0 : ℤ) = Int.log 2 (1 : ℝ) by
      simp [Int.log_one_right]]
    exact Int.log_mono_right (by linarith) h_one_le
  -- numDigits y = log|k| + 1.
  have h_log_eq : Int.log 2 |(y : ℝ)| = Int.log 2 (|k| : ℝ) + e' := by
    rw [h_y_real]; exact log_abs_mul_zpow hk_ne e'
  have h_nd_eq : F.toFiniteFormat.numDigits (y : ℝ) = Int.log 2 (|k| : ℝ) + 1 := by
    rw [F.toFiniteFormat.numDigits_top_coe h_y_ne hexp hp_top]
    linarith
  have h_nd_toNat : (F.toFiniteFormat.numDigits (y : ℝ)).toNat =
      (Int.log 2 (|k| : ℝ)).toNat + 1 := by
    rw [h_nd_eq]
    have h1 : ((Int.log 2 (|k| : ℝ)).toNat : ℤ) = Int.log 2 (|k| : ℝ) :=
      Int.toNat_of_nonneg h_log_k_nn
    omega
  -- (k, e') is canonical IsRepresentableAtP at numDigits bits.
  have h_rep : Dyadic.IsRepresentableAtP
      (F.toFiniteFormat.numDigits (y : ℝ)).toNat k e' y := by
    rw [h_nd_toNat]
    refine ⟨h_y_real, ?_, ?_⟩
    · -- 2^((log|k|).toNat + 1 - 1) = 2^(log|k|).toNat ≤ |k|.
      have h_simp : (Int.log 2 (|k| : ℝ)).toNat + 1 - 1 = (Int.log 2 (|k| : ℝ)).toNat := by
        omega
      rw [h_simp]
      have h_2pow_le : (2 : ℝ) ^ (Int.log 2 (|k| : ℝ)) ≤ (|k| : ℝ) :=
        Int.zpow_log_le_self (by norm_num : (1 : ℕ) < 2) h_abs_k_pos
      have h_log_nat_eq : ((Int.log 2 (|k| : ℝ)).toNat : ℤ) = Int.log 2 (|k| : ℝ) :=
        Int.toNat_of_nonneg h_log_k_nn
      have h_cast : ((2 : ℤ) ^ (Int.log 2 (|k| : ℝ)).toNat : ℝ) =
          (2 : ℝ) ^ (Int.log 2 (|k| : ℝ)) := by
        rw [show (Int.log 2 (|k| : ℝ)) = ((Int.log 2 (|k| : ℝ)).toNat : ℤ) from
              h_log_nat_eq.symm, zpow_natCast]
        push_cast; rfl
      have h_real_le : ((2 : ℤ) ^ (Int.log 2 (|k| : ℝ)).toNat : ℝ) ≤ (|k| : ℝ) := by
        rw [h_cast]; exact h_2pow_le
      exact_mod_cast h_real_le
    · have h_2pow_gt : (|k| : ℝ) < (2 : ℝ) ^ (Int.log 2 (|k| : ℝ) + 1) :=
        Int.lt_zpow_succ_log_self (by norm_num : (1 : ℕ) < 2) _
      have h_log_nat_eq : ((Int.log 2 (|k| : ℝ)).toNat : ℤ) = Int.log 2 (|k| : ℝ) :=
        Int.toNat_of_nonneg h_log_k_nn
      have h_cast : ((2 : ℤ) ^ ((Int.log 2 (|k| : ℝ)).toNat + 1) : ℝ) =
          (2 : ℝ) ^ (Int.log 2 (|k| : ℝ) + 1) := by
        push_cast
        rw [← zpow_natCast (2 : ℝ) ((Int.log 2 (|k| : ℝ)).toNat + 1)]
        congr 1
        push_cast
        omega
      have h_real_lt : (|k| : ℝ) < ((2 : ℤ) ^ ((Int.log 2 (|k| : ℝ)).toNat + 1) : ℝ) := by
        rw [h_cast]; exact h_2pow_gt
      exact_mod_cast h_real_lt
  exact isOdd_iff_odd_of_canonical h_rep hp_ne_1

/-- Alternating parity (fixed-point): `¬ IsOdd dlo → IsOdd dhi` at canonical
exponent `e'`. Handles the edge cases `lo = 0` and `lo = -1` directly. -/
theorem alternating_parity_fixedpoint {F : ParityFormat}
    (hp_top : F.toFormat.p = ⊤) {e' : ℤ}
    (hexp : F.toFormat.exp = (e' : WithBot ℤ)) {lo : ℤ} :
    ¬ F.IsOdd (Dyadic.ofIntZpow lo e') →
    F.IsOdd (Dyadic.ofIntZpow (lo + 1) e') := by
  intro h_not_odd
  by_cases hlo_zero : lo = 0
  · subst hlo_zero
    -- dlo = 0, dhi = 1 · 2^e'. IsOdd (1 · 2^e') ↔ Odd 1 = True.
    rw [show (0 : ℤ) + 1 = 1 from by ring]
    rw [isOdd_iff_odd_at_canonical_fixedpoint hp_top hexp (by norm_num : (1 : ℤ) ≠ 0)]
    exact ⟨0, by ring⟩
  · rw [isOdd_iff_odd_at_canonical_fixedpoint hp_top hexp hlo_zero] at h_not_odd
    have h_even_lo : Even lo := Int.not_odd_iff_even.mp h_not_odd
    have h_odd_lop1 : Odd (lo + 1) := Even.add_one h_even_lo
    have hlop1_ne : lo + 1 ≠ 0 := by
      intro h
      have : lo = -1 := by omega
      subst this
      exact absurd h_even_lo (by decide)
    rw [isOdd_iff_odd_at_canonical_fixedpoint hp_top hexp hlop1_ne]
    exact h_odd_lop1

/-- Anti-alternating parity (fixed-point): not both `dlo` and `dhi` can be
`IsOdd`. -/
theorem not_both_isOdd_fixedpoint {F : ParityFormat}
    (hp_top : F.toFormat.p = ⊤) {e' : ℤ}
    (hexp : F.toFormat.exp = (e' : WithBot ℤ)) {lo : ℤ} :
    ¬ (F.IsOdd (Dyadic.ofIntZpow lo e') ∧
       F.IsOdd (Dyadic.ofIntZpow (lo + 1) e')) := by
  rintro ⟨h1, h2⟩
  -- lo = 0 ⟹ IsOdd 0 = False ⟹ contradiction with h1.
  by_cases hlo_zero : lo = 0
  · subst hlo_zero
    -- h1 : F.IsOdd (Dyadic.ofIntZpow 0 e'). But ofIntZpow 0 e' = 0.
    have h_zero : (Dyadic.ofIntZpow 0 e' : ℝ) = 0 := by
      rw [Dyadic.coe_ofIntZpow]; ring
    exact (IsOdd.ne_zero h1) (by apply Subtype.ext; exact h_zero)
  by_cases hlop1_zero : lo + 1 = 0
  · -- lo + 1 = 0 ⟹ IsOdd 0 = False for h2.
    have h_zero : (Dyadic.ofIntZpow (lo + 1) e' : ℝ) = 0 := by
      rw [Dyadic.coe_ofIntZpow, hlop1_zero]; push_cast; ring
    exact (IsOdd.ne_zero h2) (by apply Subtype.ext; exact h_zero)
  rw [isOdd_iff_odd_at_canonical_fixedpoint hp_top hexp hlo_zero] at h1
  rw [isOdd_iff_odd_at_canonical_fixedpoint hp_top hexp hlop1_zero] at h2
  obtain ⟨m₁, hm₁⟩ := h1
  obtain ⟨m₂, hm₂⟩ := h2
  omega

/-- Anti-alternating parity (floating-point): not both `dlo` and `dhi` can be
`IsOdd`. Direct from `lo` and `lo+1` having opposite parity (in non-sat
case), or from saturation forcing one side Even. -/
theorem not_both_isOdd_floating {F : ParityFormat}
    {p : ℕ+} (hp_eq : F.toFormat.p = ((p : ℕ+) : WithTop ℕ+))
    (hp_ne_1 : F.toFormat.p ≠ ((1 : ℕ+) : WithTop ℕ+))
    (hexp_bot : F.toFormat.exp = ⊥) {lo e : ℤ}
    (hlo_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo|)
    (hlo_hi : |lo| ≤ (2 : ℤ) ^ (p : ℕ))
    (hlop1_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo + 1|)
    (hlop1_hi : |lo + 1| ≤ (2 : ℤ) ^ (p : ℕ)) :
    ¬ (F.IsOdd (Dyadic.ofIntZpow lo e) ∧
       F.IsOdd (Dyadic.ofIntZpow (lo + 1) e)) := by
  rintro ⟨h1, h2⟩
  rcases lt_or_eq_of_le hlo_hi with hlo_lt | hlo_sat
  · rw [isOdd_iff_odd_at_canonical_floating hp_eq hp_ne_1 hexp_bot hlo_lo hlo_lt] at h1
    rcases lt_or_eq_of_le hlop1_hi with hlop1_lt | hlop1_sat
    · rw [isOdd_iff_odd_at_canonical_floating hp_eq hp_ne_1 hexp_bot hlop1_lo hlop1_lt] at h2
      obtain ⟨m₁, hm₁⟩ := h1
      obtain ⟨m₂, hm₂⟩ := h2
      omega
    · exact (not_isOdd_at_saturation hp_eq hp_ne_1 hexp_bot hlop1_sat) h2
  · exact (not_isOdd_at_saturation hp_eq hp_ne_1 hexp_bot hlo_sat) h1

/-- Alternating parity at the canonical exponent (floating-point case):
if `dlo = lo · 2^e` is not `F.IsOdd`, then `dhi = (lo+1) · 2^e` is.
Requires `lo` and `lo+1` to both lie in the canonical mantissa range
`[2^(p-1), 2^p]`. -/
theorem alternating_parity_floating {F : ParityFormat}
    {p : ℕ+} (hp_eq : F.toFormat.p = ((p : ℕ+) : WithTop ℕ+))
    (hp_ne_1 : F.toFormat.p ≠ ((1 : ℕ+) : WithTop ℕ+))
    (hexp_bot : F.toFormat.exp = ⊥) {lo e : ℤ}
    (hlo_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo|)
    (hlo_hi : |lo| ≤ (2 : ℤ) ^ (p : ℕ))
    (hlop1_lo : (2 : ℤ) ^ ((p : ℕ) - 1) ≤ |lo + 1|)
    (hlop1_hi : |lo + 1| ≤ (2 : ℤ) ^ (p : ℕ)) :
    ¬ F.IsOdd (Dyadic.ofIntZpow lo e) →
    F.IsOdd (Dyadic.ofIntZpow (lo + 1) e) := by
  intro h_not_odd
  have h2p_nn : (0 : ℤ) ≤ (2 : ℤ) ^ (p : ℕ) := by positivity
  -- Case on dlo's saturation.
  rcases lt_or_eq_of_le hlo_hi with hlo_lt | hlo_sat
  · -- dlo non-saturated.
    rw [isOdd_iff_odd_at_canonical_floating hp_eq hp_ne_1 hexp_bot hlo_lo hlo_lt]
      at h_not_odd
    have h_even_lo : Even lo := Int.not_odd_iff_even.mp h_not_odd
    have h_odd_lop1 : Odd (lo + 1) := Even.add_one h_even_lo
    -- Case on dhi's saturation.
    rcases lt_or_eq_of_le hlop1_hi with hlop1_lt | hlop1_sat
    · rw [isOdd_iff_odd_at_canonical_floating hp_eq hp_ne_1 hexp_bot hlop1_lo hlop1_lt]
      exact h_odd_lop1
    · -- |lo+1| = 2^p: 2^p is even, so lo+1 is even, contradicting h_odd_lop1.
      exfalso
      have h_even_lop1 : Even (lo + 1) := by
        rcases (abs_eq h2p_nn).mp hlop1_sat with h | h
        · rw [h]
          refine ⟨(2 : ℤ) ^ ((p : ℕ) - 1), ?_⟩
          have := Dyadic.two_pow_succ_pred p.pos
          linarith
        · rw [h]
          refine ⟨-((2 : ℤ) ^ ((p : ℕ) - 1)), ?_⟩
          have := Dyadic.two_pow_succ_pred p.pos
          linarith
      exact (Int.not_odd_iff_even.mpr h_even_lop1) h_odd_lop1
  · -- dlo saturated: |lo| = 2^p. Need IsOdd dhi.
    -- lo = ±2^p. lo + 1 = ±2^p + 1.
    rcases (abs_eq h2p_nn).mp hlo_sat with hlo_pos | hlo_neg
    · -- lo = 2^p: lo + 1 = 2^p + 1, |lo+1| = 2^p+1, but hlop1_hi says ≤ 2^p. Contradiction.
      exfalso
      rw [hlo_pos] at hlop1_hi
      have : (2 : ℤ) ^ (p : ℕ) + 1 > 0 := by positivity
      have h_abs : |(2 : ℤ) ^ (p : ℕ) + 1| = (2 : ℤ) ^ (p : ℕ) + 1 :=
        abs_of_pos this
      linarith
    · -- lo = -2^p: lo + 1 = -2^p + 1 = -(2^p - 1). |lo+1| = 2^p - 1.
      have h_lop1_lt : |lo + 1| < (2 : ℤ) ^ (p : ℕ) := by
        rw [hlo_neg]
        have h_pos_inner : (0 : ℤ) < (2 : ℤ) ^ (p : ℕ) - 1 := by
          have : (1 : ℤ) ≤ (2 : ℤ) ^ (p : ℕ) := one_le_pow₀ (by norm_num)
          have h_two_le : (2 : ℤ) ≤ (2 : ℤ) ^ (p : ℕ) := by
            calc (2 : ℤ) = (2 : ℤ) ^ 1 := by ring
              _ ≤ (2 : ℤ) ^ (p : ℕ) := pow_le_pow_right₀ (by norm_num) p.pos
          linarith
        have h_eq : -((2 : ℤ) ^ (p : ℕ)) + 1 = -((2 : ℤ) ^ (p : ℕ) - 1) := by ring
        rw [h_eq, abs_neg, abs_of_pos h_pos_inner]
        linarith
      rw [isOdd_iff_odd_at_canonical_floating hp_eq hp_ne_1 hexp_bot hlop1_lo h_lop1_lt]
      -- Show Odd (lo + 1) = Odd (-2^p + 1).
      rw [hlo_neg]
      -- -2^p + 1: 2^p is even, -2^p is even, -2^p + 1 is odd.
      have h_2p_even : Even ((2 : ℤ) ^ (p : ℕ)) := by
        refine ⟨(2 : ℤ) ^ ((p : ℕ) - 1), ?_⟩
        have := Dyadic.two_pow_succ_pred p.pos
        linarith
      have h_neg_2p_even : Even (-((2 : ℤ) ^ (p : ℕ))) := h_2p_even.neg
      exact h_neg_2p_even.add_one

end ParityFormat

end Mpfx2
