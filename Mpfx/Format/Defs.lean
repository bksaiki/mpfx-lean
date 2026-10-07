import Mpfx.Dyadic
import Mathlib.Data.Int.Log

/-!
# Abstract number formats (§4.2)

`Format` (`𝒜(p, exp, b)`) and its membership relation, the `FiniteFormat`
subtype, its canonical exponent, and the digit count `numDigits`.
-/

namespace Mpfx

/-- The abstract number format `𝒜(p, exp, b)`.

* `p : Prec` — maximum precision (in binary digits). `p = 0` is the trivial
  format `{0}`; `⊤` denotes "no precision constraint" (the format is
  fixed-point). `FiniteFormat` rules out `p = 0`, since rounding into `{0}`
  has no canonical representation.
* `exp : QExp` — exponent of the minimum quantum. `⊥` denotes "no quantum
  constraint" (the format is unbounded floating-point).
* `b : Bound` — non-negative magnitude bound. `NonNegDyadic` enforces
  `b ≥ 0`; `⊤` denotes "unbounded".
-/
structure Format where
  p : Prec
  exp : QExp
  b : Bound

namespace Format

/-- `|d|` satisfies the magnitude bound `b`. `⊤` (unbounded) accepts anything;
a finite `b` is interpreted as `|d.val| ≤ b.val`. -/
def boundOK : Bound → Dyadic → Prop
  | ⊤, _ => True
  | (b : NonNegDyadic), d => |(d : ℚ)| ≤ ((b.val : Dyadic) : ℚ)

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

/-- Zero satisfies any magnitude bound. -/
@[simp] theorem boundOK_zero (b : Bound) :
    boundOK b (0 : Dyadic) := by
  cases b using Bound.recTopCoe with
  | top => trivial
  | coe b =>
    change |((0 : Dyadic) : ℚ)| ≤ _
    simpa using b.property

/-- The bound `|·| ≤ b` is symmetric under negation. -/
theorem boundOK_neg {b : Bound} {d : Dyadic} (h : boundOK b d) :
    boundOK b (-d) := by
  cases b using Bound.recTopCoe with
  | top => trivial
  | coe b =>
    change |((-d : Dyadic) : ℚ)| ≤ _
    rw [Subring.coe_neg, abs_neg]
    exact h

@[simp] theorem boundOK_neg_iff (b : Bound) (d : Dyadic) :
    boundOK b (-d) ↔ boundOK b d :=
  ⟨fun h => by simpa using boundOK_neg h, boundOK_neg⟩

/-- Format membership is closed under negation. -/
theorem neg_mem {F : Format} {d : Dyadic} (h : d ∈ F) : (-d) ∈ F := by
  obtain ⟨hp, he, hb⟩ := h
  exact ⟨Dyadic.precisionAtMost_neg hp, Dyadic.quantumAtLeast_neg he, boundOK_neg hb⟩

theorem mem_neg_iff (F : Format) (d : Dyadic) : (-d) ∈ F ↔ d ∈ F :=
  ⟨fun h => by simpa using neg_mem h, neg_mem⟩

/-- `F` contains at least one nonzero value. §4.2's non-triviality restriction. -/
def Nontrivial (F : Format) : Prop :=
  ∃ d : Dyadic, d ∈ F ∧ d ≠ 0

/-- A nonzero value needs at least one digit, so a nontrivial format has
positive precision. -/
theorem Nontrivial.p_ne_zero {F : Format} (h : F.Nontrivial) : F.p ≠ 0 := by
  obtain ⟨d, hd, hd_ne⟩ := h
  intro h0
  have hp := hd.1
  rw [h0] at hp
  exact hd_ne (Dyadic.precisionAtMost_zero_iff_eq_zero.mp hp)

/-- §4.2's restriction on the magnitude bound: `b ∈ 𝒜(p, exp, ∞) ∪ {∞}`, i.e. a
finite bound is itself representable. -/
def BoundRep (F : Format) : Prop :=
  ∀ bv : NonNegDyadic, F.b = (bv : Bound) →
    bv.val ∈ F.unbounded

/-- `c · 2^k` lies in `F` once the three constraints are checked. -/
theorem ofIntZpow_mem {F : Format} {c k : ℤ}
    (hp : Dyadic.precisionAtMost F.p (Dyadic.ofIntZpow c k))
    (he : F.exp ≤ (k : QExp)) (hb : boundOK F.b (Dyadic.ofIntZpow c k)) :
    Dyadic.ofIntZpow c k ∈ F :=
  ⟨hp, Dyadic.quantumAtLeast_anti he ⟨c, by rw [Dyadic.coe_rat_ofIntZpow]⟩, hb⟩

/-- A `BoundRep` format's finite bound is one of its values. -/
theorem bound_mem {F : Format} (hb : BoundRep F) {bv : NonNegDyadic}
    (hF : F.b = (bv : Bound)) : bv.val ∈ F := by
  obtain ⟨hp, hq, -⟩ := hb bv hF
  refine ⟨hp, hq, ?_⟩
  rw [hF]
  change |((bv.val : Dyadic) : ℚ)| ≤ ((bv.val : Dyadic) : ℚ)
  rw [abs_of_nonneg bv.property]

/-- Zero is in every format. -/
theorem zero_mem (F : Format) : (0 : Dyadic) ∈ F := by
  refine ⟨?_, ?_, ?_⟩
  · change Dyadic.precisionAtMost F.p (0 : Dyadic)
    cases F.p using ENat.recTopCoe with
    | top => trivial
    | coe p => exact ⟨0, 0, by simp, by simp⟩
  · change Dyadic.quantumAtLeast F.exp (0 : Dyadic)
    cases F.exp using QExp.recBotCoe with
    | bot => trivial
    | coe e => exact ⟨0, by simp⟩
  · change boundOK F.b (0 : Dyadic)
    cases F.b using Bound.recTopCoe with
    | top => trivial
    | coe b =>
      change |((0 : Dyadic) : ℚ)| ≤ ((b.val : Dyadic) : ℚ)
      simpa using b.property

end Format

/-! ### Subtype hierarchy

Two stronger tiers stack on top of `Format`, each adding exactly one
invariant required by a downstream API:

* `FiniteFormat` — rules out the *doubly-unbounded* case `(⊤, ⊥)`. At
  least one of `p`, `exp` is finite. This is the minimum needed for
  `rnd` to compute a canonical exponent for nonzero `x`, since
  dyadics are dense in `ℝ` but not closed under limits.
* `ParityFormat` (`Mpfx/Format/Parity.lean`) — adds the *parity-anchor*
  invariant: `p ≠ 1` whenever `exp = ⊥`. Combined with `FiniteFormat`, this
  is `(p ≠ ⊤ ∧ p ≠ 1) ∨ exp ≠ ⊥`. Required for `IsOdd` / `IsEven` (and hence
  `rnd .toOdd`, `rnd (.nearest _)`) to be semantically meaningful — without
  it, the exponent-parity fallback for `p = 1` has no anchor (since the
  format has no quantum to count indices from).

State theorems on the *weakest* tier whose proof actually destructures
the invariant. Promote only when needed. -/

/-- A `Format` where `rnd` is well-defined for directed modes: at least
one of `p`, `exp` is finite (equivalently `¬ (p = ⊤ ∧ exp = ⊥)`), and the
precision is nonzero — `p = 0` admits only `0`, which has no canonical
`(c, e)` representation to round to. -/
structure FiniteFormat extends Format where
  finite : toFormat.p ≠ ⊤ ∨ toFormat.exp ≠ ⊥
  pos : toFormat.p ≠ 0

instance : Membership Dyadic FiniteFormat := ⟨fun F d => d ∈ F.toFormat⟩

namespace FiniteFormat

/-- `F.pos` at a finite precision: the witness `p` in `F.p = ↑p` is positive. -/
theorem p_pos {F : FiniteFormat} {p : ℕ} (hp : F.p = (p : Prec)) : 0 < p := by
  rcases Nat.eq_zero_or_pos p with rfl | h
  · exact absurd hp F.pos
  · exact h

/-- Zero is in every (finite) format. -/
theorem zero_mem (F : FiniteFormat) : (0 : Dyadic) ∈ F := Format.zero_mem F.toFormat

/-- (Finite-)format membership is closed under negation. -/
theorem neg_mem {F : FiniteFormat} {d : Dyadic} (h : d ∈ F) : (-d) ∈ F :=
  Format.neg_mem (F := F.toFormat) h

theorem mem_neg_iff (F : FiniteFormat) (d : Dyadic) : (-d) ∈ F ↔ d ∈ F :=
  Format.mem_neg_iff F.toFormat d

/-- Canonical exponent for representing `x` in `F`. The `(⊤, ⊥)` branch is
unreachable by `F.finite`; we list it to make the `match` total. -/
noncomputable def canonicalExp (F : FiniteFormat) (x : ℝ) : ℤ :=
  match F.p, F.exp with
  | ⊤, ⊥ => 0  -- unreachable by `F.finite`
  | ⊤, (e : ℤ) => e
  | (p : ℕ), ⊥ =>
      if x = 0 then 0 else Int.log 2 |x| + 1 - (p : ℤ)
  | (p : ℕ), (e : ℤ) =>
      if x = 0 then e
      else max (Int.log 2 |x| + 1 - (p : ℤ)) e

/-- The canonical exponent dominates `F.exp` whenever `F.exp` is finite.
Needed to discharge `quantumAtLeast F.exp` for the rounded value. -/
theorem exp_le_canonicalExp (F : FiniteFormat) (x : ℝ)
    {e' : ℤ} (hexp : F.exp = (e' : QExp)) :
    e' ≤ F.canonicalExp x := by
  unfold canonicalExp
  cases hp : F.p using ENat.recTopCoe with
  | top => rw [hexp]; exact le_refl _
  | coe p =>
    simp only [hexp]
    split_ifs
    · exact le_refl _
    · exact le_max_right _ _

/-- The canonical exponent dominates `Int.log 2 |x| + 1 - p` whenever
`F.p` is finite and `x ≠ 0`. Needed to bound `|⌊x · 2^(-e)⌋| ≤ 2^p`. -/
theorem log_sub_p_le_canonicalExp (F : FiniteFormat) {x : ℝ} (hx : x ≠ 0)
    {p : ℕ} (hp : F.p = (p : Prec)) :
    Int.log 2 |x| + 1 - (p : ℤ) ≤ F.canonicalExp x := by
  unfold canonicalExp
  cases F.exp using QExp.recBotCoe with
  | bot => simp [hp, hx]
  | coe e' => simp [hp, hx]

/-- **`x` is above `F`'s coarsest step** (Flocq's `Exp_not_FTZ`, localized at
`x`): the canonical exponent does not exceed `x`'s binade. Equivalently, for
`x ≠ 0`, `F.exp ≤ ⌊log₂ |x|⌋` — the precision term `⌊log₂ |x|⌋ + 1 − p` is never
the binding one — and equivalently again, `x` does not round down to `0`
(`rndDown_pos_iff`). Reducible, so arithmetic tactics see through it. -/
abbrev IsAboveQuantum (F : FiniteFormat) (x : ℝ) : Prop :=
  F.canonicalExp x ≤ Int.log 2 |x|

/-- On the positive side the absolute value drops out. -/
theorem IsAboveQuantum.le_log {F : FiniteFormat} {x : ℝ} (h : F.IsAboveQuantum x)
    (hx : 0 < x) : F.canonicalExp x ≤ Int.log 2 x := by
  have h' : F.canonicalExp x ≤ Int.log 2 |x| := h
  rwa [abs_of_pos hx] at h'

theorem isAboveQuantum_of_le_log {F : FiniteFormat} {x : ℝ} (hx : 0 < x)
    (h : F.canonicalExp x ≤ Int.log 2 x) : F.IsAboveQuantum x := by
  have : Int.log 2 |x| = Int.log 2 x := by rw [abs_of_pos hx]
  omega

/-- `F.exp ≤ ⌊log₂ |x|⌋` is the whole content of `IsAboveQuantum`. -/
theorem isAboveQuantum_of_exp_le (F : FiniteFormat) {x : ℝ} (hx : x ≠ 0)
    (hexp : ∀ e : ℤ, F.exp = (e : QExp) → e ≤ Int.log 2 |x|) : F.IsAboveQuantum x := by
  unfold IsAboveQuantum canonicalExp
  cases hp : F.p using ENat.recTopCoe with
  | top =>
    cases hexp' : F.exp using QExp.recBotCoe with
    | bot => exact (F.finite.elim (fun h => h hp) (fun h => h hexp')).elim
    | coe e => exact hexp e hexp'
  | coe p =>
    have hpp : 0 < p := F.p_pos hp
    cases hexp' : F.exp using QExp.recBotCoe with
    | bot => simp only [if_neg hx]; omega
    | coe e => simp only [if_neg hx]; exact max_le (by omega) (hexp e hexp')

/-- `canonicalExp` is monotone in magnitude. -/
theorem canonicalExp_mono (F : FiniteFormat) {y z : ℝ} (hy : y ≠ 0)
    (hyz : |y| ≤ |z|) : F.canonicalExp y ≤ F.canonicalExp z := by
  have hy_pos : 0 < |y| := abs_pos.mpr hy
  have hz : z ≠ 0 := by
    rintro rfl; rw [abs_zero] at hyz; exact absurd hyz (not_le.mpr hy_pos)
  have hlog : Int.log 2 |y| ≤ Int.log 2 |z| := Int.log_mono_right hy_pos hyz
  unfold FiniteFormat.canonicalExp
  cases F.p using ENat.recTopCoe with
  | top => cases F.exp using QExp.recBotCoe <;> simp <;> rfl
  | coe p =>
    cases F.exp using QExp.recBotCoe with
    | bot => simp only [hy, hz, if_false]; omega
    | coe e => simp only [hy, hz, if_false]; omega

/-- `F` with the magnitude bound removed (`b := ⊤`). Used by
`Rounds`/`RoundsFinite` to define the unbounded rounding. The `finite` invariant
depends only on `(p, exp)`, so it's preserved. -/
def unbounded (F : FiniteFormat) : FiniteFormat where
  toFormat := F.toFormat.unbounded
  finite := F.finite
  pos := F.pos

@[simp] theorem unbounded_toFormat (F : FiniteFormat) :
    F.unbounded.toFormat = F.toFormat.unbounded := rfl
@[simp] theorem unbounded_p (F : FiniteFormat) : F.unbounded.p = F.p := rfl
@[simp] theorem unbounded_canonicalExp (F : FiniteFormat) (x : ℝ) :
    F.unbounded.canonicalExp x = F.canonicalExp x := rfl
@[simp] theorem unbounded_exp (F : FiniteFormat) : F.unbounded.exp = F.exp := rfl
@[simp] theorem unbounded_b (F : FiniteFormat) : F.unbounded.b = ⊤ := rfl
@[simp] theorem unbounded_unbounded (F : FiniteFormat) :
    F.unbounded.unbounded = F.unbounded := rfl

/-- Number of binary digits the format rounds `x` to. Case analysis on `(F.p, F.exp)`:

- `(⊤, e')`: fixed-point with quantum `2^e'`. Digits = `⌊log₂|x|⌋ − e' + 1`.
- `(p, ⊥)`: floating-point with precision `p` and no quantum. Digits = `p`.
- `(p, e')`: floating-point with precision `p` and min quantum `2^e'`.
  Digits = `min(p, ⌊log₂|x|⌋ − e' + 1)`.

The `(⊤, ⊥)` branch is unreachable by `FiniteFormat.finite`.

For `x = 0` returns `0` by convention. -/
noncomputable def numDigits (F : FiniteFormat) (x : ℝ) : ℤ :=
  if x = 0 then 0
  else
    let e : ℤ := Int.log 2 |x|
    match F.p, F.exp with
    | ⊤, ⊥ => 0  -- unreachable by `F.finite`, but pattern-match must be total
    | ⊤, (e' : ℤ) => e - e' + 1
    | (p : ℕ), ⊥ => (p : ℤ)
    | (p : ℕ), (e' : ℤ) => min (p : ℤ) (e - e' + 1)

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
    (hexp : F.exp = (e' : QExp)) (hp : F.p = ⊤) :
    F.numDigits x = Int.log 2 |x| - e' + 1 := by
  unfold numDigits
  simp only [hx, ↓reduceIte, hp, hexp]
  rfl

/-- `numDigits` evaluator: `F.p = p`, `F.exp = ⊥`, `x ≠ 0`. -/
theorem numDigits_coe_bot (F : FiniteFormat) {x : ℝ} (hx : x ≠ 0) {p : ℕ}
    (hp : F.p = (p : Prec)) (hexp : F.exp = ⊥) :
    F.numDigits x = (p : ℤ) := by
  unfold numDigits
  simp only [hx, ↓reduceIte, hp, hexp]

/-- `numDigits` evaluator: `F.p = p`, `F.exp = (e' : ℤ)`, `x ≠ 0`. -/
theorem numDigits_coe_coe (F : FiniteFormat) {x : ℝ} (hx : x ≠ 0) {p : ℕ} {e' : ℤ}
    (hp : F.p = (p : Prec))
    (hexp : F.exp = (e' : QExp)) :
    F.numDigits x = min (p : ℤ) (Int.log 2 |x| - e' + 1) := by
  unfold numDigits
  simp only [hx, ↓reduceIte, hp, hexp]

end FiniteFormat

/-! ### Bound checks and `unbounded` membership -/

/-- If `|g| ≤ |h|` (over ℝ) and `h` is in-bound, so is `g`. -/
theorem boundOK_of_abs_le {b : Bound} {g h : Dyadic}
    (hle : |(g : ℝ)| ≤ |(h : ℝ)|) (hb : Format.boundOK b h) :
    Format.boundOK b g := by
  cases b using Bound.recTopCoe with
  | top => trivial
  | coe b =>
    have hle' : |(g : ℚ)| ≤ |(h : ℚ)| := by
      rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast,
        ← Rat.cast_abs, ← Rat.cast_abs] at hle
      exact_mod_cast hle
    have hb' : |(h : ℚ)| ≤ ((b.val : Dyadic) : ℚ) := hb
    change |(g : ℚ)| ≤ ((b.val : Dyadic) : ℚ)
    linarith

/-- A bound check against a finite bound, transferred to an absolute-value
bound over `ℝ`. -/
theorem abs_coe_real_le_of_boundOK {b₁ : NonNegDyadic} {y : Dyadic}
    (h : Format.boundOK ((b₁ : Bound)) y) :
    |(y : ℝ)| ≤ ((b₁.val : Dyadic) : ℝ) := by
  rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast, ← Rat.cast_abs]
  exact_mod_cast h

/-- Converse of `abs_coe_real_le_of_boundOK`. -/
theorem boundOK_coe_of_abs_le {b : NonNegDyadic} {y : Dyadic}
    (h : |(y : ℝ)| ≤ ((b.val : Dyadic) : ℝ)) :
    Format.boundOK ((b : Bound)) y := by
  change |(y : ℚ)| ≤ ((b.val : Dyadic) : ℚ)
  rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast, ← Rat.cast_abs] at h
  exact_mod_cast h

/-- A failed bound check, transferred to a strict absolute-value bound
over `ℝ`. -/
theorem lt_abs_coe_real_of_not_boundOK {b₁ : NonNegDyadic} {y : Dyadic}
    (h : ¬ Format.boundOK ((b₁ : Bound)) y) :
    ((b₁.val : Dyadic) : ℝ) < |(y : ℝ)| := by
  have h1 : ¬ |(y : ℚ)| ≤ ((b₁.val : Dyadic) : ℚ) := h
  push Not at h1
  rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast, ← Rat.cast_abs]
  exact_mod_cast h1

/-- A dyadic between two in-bound dyadics is in-bound. -/
theorem boundOK_of_between {b : Bound} {lo hi g : Dyadic}
    (hblo : Format.boundOK b lo) (hbhi : Format.boundOK b hi)
    (h1 : (lo : ℝ) ≤ (g : ℝ)) (h2 : (g : ℝ) ≤ (hi : ℝ)) :
    Format.boundOK b g := by
  cases b using Bound.recTopCoe with
  | top => trivial
  | coe b =>
    have h1' : (lo : ℚ) ≤ (g : ℚ) := by
      rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast] at h1
      exact_mod_cast h1
    have h2' : (g : ℚ) ≤ (hi : ℚ) := by
      rw [Dyadic.coe_real_eq_ratCast, Dyadic.coe_real_eq_ratCast] at h2
      exact_mod_cast h2
    change |(g : ℚ)| ≤ ((b.val : Dyadic) : ℚ)
    exact abs_le.mpr ⟨by linarith [(abs_le.mp hblo).1], by linarith [(abs_le.mp hbhi).2]⟩

/-- Bounded membership weakens to unbounded membership (drop the bound check). -/
theorem mem_unbounded_of_mem {F : FiniteFormat} {d : Dyadic}
    (h : d ∈ F) : d ∈ F.unbounded :=
  ⟨h.1, h.2.1, trivial⟩

/-- Unbounded membership plus an explicit bound check gives bounded membership. -/
theorem mem_of_mem_unbounded_of_boundOK {F : FiniteFormat} {d : Dyadic}
    (h : d ∈ F.unbounded) (hb : Format.boundOK F.b d) : d ∈ F :=
  ⟨h.1, h.2.1, hb⟩

/-- A `FiniteFormat` with `exp = ⊥` has finite precision. -/
theorem exists_p_coe_of_exp_bot {F : FiniteFormat} (he : F.exp = ⊥) :
    ∃ p : ℕ, F.p = (p : Prec) := by
  cases hc : F.p using ENat.recTopCoe with
  | top => exact absurd F.finite (by push Not; exact ⟨hc, he⟩)
  | coe p => exact ⟨p, rfl⟩

/-- `numDigits` only reads `(p, exp)`. -/
theorem numDigits_congr {F G : FiniteFormat} (hp : F.p = G.p)
    (he : F.exp = G.exp) (x : ℝ) : F.numDigits x = G.numDigits x := by
  unfold FiniteFormat.numDigits
  rw [hp, he]

end Mpfx
