import Mpfx.Dyadic
import Mathlib.Data.Int.Log

/-!
# Abstract number formats (§4.2)

`Format` (`𝒜(p, exp, b, S)`) and its membership relation, the special values
`Special` / `WithSpecial`, the `FiniteFormat` subtype, its canonical exponent,
and the digit count `numDigits`.
-/

namespace Mpfx

/-- A non-numeric value: an infinity or NaN. -/
inductive Special where
  | inf (negative : Bool)
  | nan
deriving DecidableEq, Repr

/-- `α` extended with the special values. -/
inductive WithSpecial (α : Type) where
  | finite (a : α)
  | special (s : Special)
deriving DecidableEq, Repr

/-- Negation of a special value: infinities flip sign, NaN is fixed. -/
def Special.neg : Special → Special
  | .inf negative => .inf !negative
  | .nan => .nan

@[simp] theorem Special.neg_neg (s : Special) : s.neg.neg = s := by
  cases s <;> simp [Special.neg]

/-- Negation through `WithSpecial`. -/
def WithSpecial.neg {α : Type} [Neg α] : WithSpecial α → WithSpecial α
  | .finite a => .finite (-a)
  | .special s => .special s.neg

@[simp] theorem WithSpecial.neg_finite {α : Type} [Neg α] (a : α) :
    (WithSpecial.finite a).neg = .finite (-a) := rfl

@[simp] theorem WithSpecial.neg_special {α : Type} [Neg α] (s : Special) :
    (WithSpecial.special s : WithSpecial α).neg = .special s.neg := rfl

@[simp] theorem WithSpecial.neg_neg {α : Type} [InvolutiveNeg α] (v : WithSpecial α) :
    v.neg.neg = v := by
  cases v <;> simp

/-- A dyadic value read as a real one. -/
def WithSpecial.toReal : WithSpecial Dyadic → WithSpecial ℝ
  | .finite d => .finite d
  | .special s => .special s

@[simp] theorem WithSpecial.toReal_finite (d : Dyadic) :
    (WithSpecial.finite d).toReal = .finite (d : ℝ) := rfl

@[simp] theorem WithSpecial.toReal_special (s : Special) :
    (WithSpecial.special s : WithSpecial Dyadic).toReal = .special s := rfl

/-- The abstract number format `𝒜(p, exp, b, S)`.

* `p : Prec` — maximum precision (in binary digits). `p = 0` is the trivial
  format `{0}`; `⊤` denotes "no precision constraint" (the format is
  fixed-point). `FiniteFormat` rules out `p = 0`, since rounding into `{0}`
  has no canonical representation.
* `exp : QExp` — exponent of the minimum quantum. `⊥` denotes "no quantum
  constraint" (the format is unbounded floating-point).
* `b : Bound` — non-negative magnitude bound. `NonNegDyadic` enforces
  `b ≥ 0`; `⊤` denotes "unbounded".
* `specials : Set Special` — the special values the format represents.
-/
structure Format where
  p : Prec
  exp : QExp
  b : Bound
  specials : Set Special

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
@[simp] theorem unbounded_specials (F : Format) : F.unbounded.specials = F.specials := rfl
@[simp] theorem unbounded_unbounded (F : Format) :
    F.unbounded.unbounded = F.unbounded := rfl

end Format

instance : Membership Dyadic Format := ⟨Format.Mem⟩

/-- The values of `F`, numeric and special. Not a `Membership` instance: a second
instance on `Format` would clash with `Membership Dyadic Format`. -/
def Format.values (F : Format) : Set (WithSpecial Dyadic)
  | .finite d => d ∈ F
  | .special s => s ∈ F.specials

@[simp] theorem Format.finite_mem_values {F : Format} {d : Dyadic} :
    WithSpecial.finite d ∈ F.values ↔ d ∈ F := Iff.rfl

@[simp] theorem Format.special_mem_values {F : Format} {s : Special} :
    WithSpecial.special s ∈ F.values ↔ s ∈ F.specials := Iff.rfl

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

/-- `Dyadic.abs x ∈ F` whenever `x ∈ F`. -/
theorem abs_mem {F : Format} {x : Dyadic} (hx : x ∈ F) :
    Dyadic.abs x ∈ F := by
  unfold Dyadic.abs
  by_cases h : 0 ≤ (x : ℚ)
  · rw [if_pos h]; exact hx
  · rw [if_neg h]; exact neg_mem hx

/-- `F`'s specials are closed under negation. -/
def NegClosed (F : Format) : Prop := ∀ s ∈ F.specials, s.neg ∈ F.specials

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

/-- `F` has at least `n` positive values: a strictly increasing `n`-tuple of
them. One positive value is `Nontrivial` (`hasPositive_one_iff`). -/
def HasPositive (F : Format) (n : ℕ) : Prop :=
  ∃ f : Fin n → Dyadic, StrictMono (fun i => (f i : ℝ)) ∧ ∀ i, f i ∈ F ∧ (0 : ℝ) < f i

/-- A nonzero value or its negation is positive. -/
theorem hasPositive_one_iff {F : Format} : F.HasPositive 1 ↔ F.Nontrivial := by
  refine ⟨fun ⟨f, _, hf⟩ => ⟨f 0, (hf 0).1, fun h => ?_⟩, fun ⟨d, hd, hne⟩ => ?_⟩
  · have := (hf 0).2
    rw [h, Dyadic.coe_real_zero] at this
    exact lt_irrefl _ this
  · have hne' : (d : ℝ) ≠ 0 := fun h => hne (Dyadic.ext_real (by rw [h, Dyadic.coe_real_zero]))
    rcases hne'.lt_or_gt with hneg | hpos
    · exact ⟨fun _ => -d, Subsingleton.strictMono _,
        fun _ => ⟨neg_mem hd, by rw [Dyadic.coe_real_neg]; linarith⟩⟩
    · exact ⟨fun _ => d, Subsingleton.strictMono _, fun _ => ⟨hd, hpos⟩⟩

/-- A nontrivial format has a nonzero value of either sign: a positive value
or its negation. -/
theorem Nontrivial.exists_sign {F : Format} (h : F.Nontrivial) (b : Bool) :
    ∃ y : Dyadic, y ∈ F ∧ y ≠ 0 ∧ decide ((y : ℚ) < 0) = b := by
  obtain ⟨f, -, hf⟩ := hasPositive_one_iff.mpr h
  obtain ⟨ha, ha_pos⟩ := hf 0
  have hq : (0 : ℚ) < (f 0 : ℚ) := by
    exact_mod_cast ha_pos
  have hne : f 0 ≠ 0 := fun h => by rw [h] at hq; simp at hq
  cases b
  · exact ⟨f 0, ha, hne, by simpa using hq.le⟩
  · exact ⟨-f 0, neg_mem ha, neg_ne_zero.mpr hne, by simpa using hq⟩

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
  ⟨hp, Dyadic.quantumAtLeast_ofIntZpow he, hb⟩

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
  · exact boundOK_zero F.b

end Format

/-! ### Subtype hierarchy

Two stronger tiers stack on top of `Format`, each adding exactly one
invariant required by a downstream API:

* `FiniteFormat` — rules out the *doubly-unbounded* case `(⊤, ⊥)`. At
  least one of `p`, `exp` is finite. This is the minimum needed for
  `rnd` to compute a canonical exponent for nonzero `x`, since
  dyadics are dense in `ℝ` but not closed under limits.
* `ParityFormat` (`Mpfx/Format/Parity.lean`) — adds `p ≠ 1` whenever
  `exp = ⊥`, the formats where `rnd .toOdd` and `rnd (.nearest .toEven)` are
  defined. Combined with `FiniteFormat`, this is `(p ≠ ⊤ ∧ p ≠ 1) ∨ exp ≠ ⊥`.
  `IsOdd` / `IsEven` are on `FiniteFormat`; at `(1, ⊥)` they count exponents
  from `0`, and the parity modes are undefined there by convention. -/

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

/-- Quantifying over `F` is quantifying over its negations: two predicates that
agree up to negation hold for all of `F` together. -/
theorem forall_mem_congr_neg (F : FiniteFormat) {P Q : Dyadic → Prop}
    (h : ∀ z, P z ↔ Q (-z)) : (∀ z, z ∈ F → P z) ↔ ∀ z, z ∈ F → Q z :=
  ⟨fun hP z hz => by simpa using (h (-z)).mp (hP _ (neg_mem hz)),
    fun hQ z hz => (h z).mpr (hQ _ (neg_mem hz))⟩

/-- The `∃` twin of `forall_mem_congr_neg`. -/
theorem exists_mem_congr_neg (F : FiniteFormat) {P Q : Dyadic → Prop}
    (h : ∀ z, P z ↔ Q (-z)) : (∃ z, z ∈ F ∧ P z) ↔ ∃ z, z ∈ F ∧ Q z :=
  ⟨fun ⟨z, hz, hP⟩ => ⟨-z, neg_mem hz, (h z).mp hP⟩,
    fun ⟨z, hz, hQ⟩ => ⟨-z, neg_mem hz, (h (-z)).mpr (by simpa using hQ)⟩⟩

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

/-- **Upper bounds on `canonicalExp`.** Away from `0`, `canonicalExp x ≤ k` says
exactly that both constraints the format imposes — the precision exponent
`⌊log₂|x|⌋ + 1 − p` and the minimum quantum — are at most `k`. -/
theorem canonicalExp_le_iff (F : FiniteFormat) {x : ℝ} (hx : x ≠ 0) {k : ℤ} :
    F.canonicalExp x ≤ k ↔
      (∀ p : ℕ, F.p = p → Int.log 2 |x| + 1 - p ≤ k) ∧ (∀ e : ℤ, F.exp = e → e ≤ k) := by
  unfold canonicalExp
  cases hp : F.p using ENat.recTopCoe with
  | top =>
    cases he : F.exp using QExp.recBotCoe with
    | bot => exact (F.finite.elim (· hp) (· he)).elim
    | coe e =>
      refine ⟨fun h => ⟨fun _ hp' => absurd hp' (by simp), fun e' he' => ?_⟩, fun h => h.2 e rfl⟩
      cases WithBot.coe_injective he'; exact h
  | coe p =>
    cases he : F.exp using QExp.recBotCoe with
    | bot => simp [hx]
    | coe e => simp [hx]

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
(`rndDown_pos_of_isAboveQuantum`, `isAboveQuantum_of_rndDown_pos`). Reducible,
so arithmetic tactics see through it. -/
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

/-- `canonicalExp` is monotone in magnitude. -/
theorem canonicalExp_mono (F : FiniteFormat) {y z : ℝ} (hy : y ≠ 0)
    (hyz : |y| ≤ |z|) : F.canonicalExp y ≤ F.canonicalExp z := by
  have hy_pos : 0 < |y| := abs_pos.mpr hy
  have hz : z ≠ 0 := by
    rintro rfl; rw [abs_zero] at hyz; exact absurd hyz (not_le.mpr hy_pos)
  have hlog : Int.log 2 |y| ≤ Int.log 2 |z| := Int.log_mono_right hy_pos hyz
  refine (F.canonicalExp_le_iff hy).mpr ⟨fun p hp => ?_, fun e he => F.exp_le_canonicalExp z he⟩
  have := F.log_sub_p_le_canonicalExp hz hp
  omega

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

end FiniteFormat

/-! ### Closed forms of `canonicalExp` -/

/-- **Closed form of `canonicalExp` in the normal range**, uniform over both
exponent regimes. When `v` is nonzero and its precision exponent
`log₂|v| + 1 − p` is at least `F.exp` (the *normal* regime — vacuous for
`exp = ⊥`), `canonicalExp` takes that form. -/
theorem canonicalExp_closed {F : FiniteFormat} {p : ℕ}
    (hp : F.p = (p : Prec)) {v : ℝ} (hv : v ≠ 0)
    (hnorm : F.exp ≤ ((Int.log 2 |v| + 1 - (p : ℤ) : ℤ) : QExp)) :
    F.canonicalExp v = Int.log 2 |v| + 1 - (p : ℤ) := by
  unfold FiniteFormat.canonicalExp
  cases hexp : F.exp using QExp.recBotCoe with
  | bot => simp only [hp, hv, if_false]
  | coe e =>
    simp only [hp, hv, if_false]
    rw [hexp] at hnorm
    exact max_eq_left (by exact_mod_cast hnorm)

/-- Closed form of `canonicalExp` with no minimum quantum (`exp = ⊥`):
`log₂|v| + 1 − p` (the vacuous-normality case of `canonicalExp_closed`). -/
theorem canonicalExp_expBot {F : FiniteFormat} {p : ℕ}
    (hp : F.p = (p : Prec)) (hexp : F.exp = ⊥)
    {v : ℝ} (hv : v ≠ 0) : F.canonicalExp v = Int.log 2 |v| + 1 - (p : ℤ) :=
  canonicalExp_closed hp hv (by rw [hexp]; exact bot_le)

/-- Closed form of `canonicalExp` with a minimum quantum (`exp = emin` finite):
`max(log₂|v| + 1 − p, emin)`. -/
theorem canonicalExp_expFinite {F : FiniteFormat} {p : ℕ} {emin : ℤ}
    (hp : F.p = (p : Prec)) (hexp : F.exp = (emin : QExp))
    {v : ℝ} (hv : v ≠ 0) :
    F.canonicalExp v = max (Int.log 2 |v| + 1 - (p : ℤ)) emin := by
  unfold FiniteFormat.canonicalExp; simp only [hp, hexp, hv, if_false]

/-- `F.exp ≤ (F.canonicalExp x : QExp)`, uniformly over `exp = ⊥`/finite. -/
theorem exp_le_canonicalExp_coe (F : FiniteFormat) (x : ℝ) :
    F.exp ≤ ((F.canonicalExp x : ℤ) : QExp) := by
  cases hexp : F.exp using QExp.recBotCoe with
  | bot => exact bot_le
  | coe e => exact_mod_cast F.exp_le_canonicalExp x hexp

/-- Closed form with unrestricted precision: `canonicalExp` is the quantum
everywhere (`F.finite` rules out `exp = ⊥` here). -/
theorem canonicalExp_pTop {F : FiniteFormat} {emin : ℤ}
    (hp : F.p = ⊤) (hexp : F.exp = (emin : QExp)) (v : ℝ) : F.canonicalExp v = emin := by
  unfold FiniteFormat.canonicalExp; rw [hp, hexp]; rfl

/-- Closed form in the **subnormal** range: when the precision exponent falls
below the quantum, `canonicalExp` *is* the quantum. -/
theorem canonicalExp_subnormal {F : FiniteFormat} {p : ℕ} {emin : ℤ}
    (hp : F.p = (p : Prec)) (hexp : F.exp = (emin : QExp)) {v : ℝ} (hv : v ≠ 0)
    (h : Int.log 2 |v| + 1 - (p : ℤ) ≤ emin) : F.canonicalExp v = emin := by
  rw [canonicalExp_expFinite hp hexp hv]; exact max_eq_right h

/-- `canonicalExp` depends only on the binade `Int.log 2 |·|` (away from `0`):
equal logs give equal canonical exponents. -/
theorem canonicalExp_eq_of_log_eq (F : FiniteFormat) {y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0)
    (h : Int.log 2 |y| = Int.log 2 |z|) : F.canonicalExp y = F.canonicalExp z := by
  unfold FiniteFormat.canonicalExp
  cases F.p <;> cases F.exp <;> simp only [if_neg hy, if_neg hz, h]

/-- `canonicalExp` depends only on `|·|`, hence is negation-invariant. -/
theorem canonicalExp_neg (F : FiniteFormat) (x : ℝ) :
    F.canonicalExp (-x) = F.canonicalExp x := by
  unfold FiniteFormat.canonicalExp
  cases F.p <;> cases F.exp <;> simp only [abs_neg, neg_eq_zero]

/-- A positive `F`-value is at least the format's quantum, so `F.exp ≤ ⌊log₂ z⌋`. -/
theorem exp_le_log_of_mem (F : FiniteFormat) {e : ℤ} (hexp : F.exp = (e : QExp))
    {z : Dyadic} (hz : z ∈ F.unbounded) (hz0 : 0 < ((z : Dyadic) : ℝ)) :
    e ≤ Int.log 2 ((z : Dyadic) : ℝ) := by
  obtain ⟨-, hq, -⟩ := hz
  rw [FiniteFormat.unbounded_exp, hexp] at hq
  simpa [abs_of_pos hz0] using Dyadic.le_log_of_quantum hq hz0.ne'

/-- With a minimum quantum, `canonicalExp` at `0` is that quantum. -/
theorem canonicalExp_zero (F : FiniteFormat) {e : ℤ} (hexp : F.exp = (e : QExp)) :
    F.canonicalExp 0 = e := by
  unfold FiniteFormat.canonicalExp
  cases F.p using ENat.recTopCoe with
  | top => simp only [hexp]; rfl
  | coe p => simp [hexp]

/-- **Every value is a multiple of `2^canonicalExp`**: `z = m · 2^cexp z`.
Each constraint of the format makes `z` a multiple of its own exponent — the
precision term `⌊log₂|z|⌋ + 1 − p` and the minimum quantum — and `canonicalExp`
is the larger of the two. -/
theorem FiniteFormat.exists_mul_zpow_canonicalExp (F : FiniteFormat) {z : Dyadic}
    (hz : z ∈ F.unbounded) : ∃ m : ℤ, (z : ℝ) = m * (2 : ℝ) ^ F.canonicalExp z := by
  by_cases hz0 : (z : ℝ) = 0
  · exact ⟨0, by simp [hz0]⟩
  have hquant : ∀ e : ℤ, F.exp = e → ∃ m : ℤ, (z : ℝ) = m * (2 : ℝ) ^ e := fun e he =>
    (Dyadic.quantumAtLeast_coe_real e z).mp (he ▸ hz.2.1)
  have hprec : ∀ p : ℕ, F.p = p →
      ∃ m : ℤ, (z : ℝ) = m * (2 : ℝ) ^ (Int.log 2 |(z : ℝ)| + 1 - p) := fun p hp => by
    obtain ⟨c, e, hce, hc⟩ := (Dyadic.precisionAtMost_coe_real p z).mp (hp ▸ hz.1)
    -- `2^⌊log₂|z|⌋ ≤ |z| = |c|·2^e < 2^(p+e)`, so the precision term is at most `e`.
    have hlo : (2 : ℝ) ^ Int.log 2 |(z : ℝ)| ≤ |(z : ℝ)| := by
      have := Int.zpow_log_le_self (b := 2) (by norm_num) (abs_pos.mpr hz0)
      exact_mod_cast this
    have hhi : |(z : ℝ)| < (2 : ℝ) ^ ((p : ℤ) + e) := by
      rw [hce, abs_mul_two_zpow, zpow_add₀ two_ne_zero, zpow_natCast]
      exact mul_lt_mul_of_pos_right (by exact_mod_cast hc) (zpow_pos two_pos e)
    have hle : Int.log 2 |(z : ℝ)| + 1 - p ≤ e := by
      have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp (hlo.trans_lt hhi)
      omega
    exact ⟨_, hce.trans (two_zpow_shift c hle)⟩
  cases hp : F.p using ENat.recTopCoe with
  | top =>
    cases he : F.exp using QExp.recBotCoe with
    | bot => exact (F.finite.elim (· hp) (· he)).elim
    | coe e => rw [canonicalExp_pTop hp he]; exact hquant e he
  | coe p =>
    cases he : F.exp using QExp.recBotCoe with
    | bot => rw [canonicalExp_expBot hp he hz0]; exact hprec p hp
    | coe e =>
      rw [canonicalExp_expFinite hp he hz0]
      rcases le_total (Int.log 2 |(z : ℝ)| + 1 - p) e with h | h
      · rw [max_eq_right h]; exact hquant e he
      · rw [max_eq_left h]; exact hprec p hp

/-- A multiple `m · 2^canonicalExp x` of a nonzero `x` has `|m| < 2^p`:
`|x| < 2^(⌊log₂|x|⌋ + 1) ≤ 2^(p + canonicalExp x)`. -/
theorem FiniteFormat.abs_lt_of_mul_zpow_canonicalExp (F : FiniteFormat) {p : ℕ}
    (hp : F.p = (p : Prec)) {x : ℝ} (hx : x ≠ 0) {m : ℤ}
    (h : x = m * (2 : ℝ) ^ F.canonicalExp x) : |m| < 2 ^ p := by
  have hc := F.log_sub_p_le_canonicalExp hx hp
  have hlt : |x| < (2 : ℝ) ^ (Int.log 2 |x| + 1) := Int.lt_zpow_succ_log_self (by norm_num) _
  have h1 : |(m : ℝ)| * (2 : ℝ) ^ F.canonicalExp x
      < (2 : ℝ) ^ (p : ℤ) * (2 : ℝ) ^ F.canonicalExp x := by
    rw [← abs_mul_two_zpow, ← h, ← zpow_add₀ two_ne_zero]
    exact hlt.trans_le (zpow_le_zpow_right₀ (by norm_num) (by omega))
  have h2 := lt_of_mul_lt_mul_right h1 (zpow_pos two_pos _).le
  rw [zpow_natCast] at h2
  exact_mod_cast h2

/-- Conversely, a multiple of `2^canonicalExp x` is a value of `F`: the step
meets the minimum quantum, and the coefficient fits the precision. -/
theorem FiniteFormat.mem_unbounded_of_mul_zpow_canonicalExp (F : FiniteFormat) {x : Dyadic}
    {m : ℤ} (h : (x : ℝ) = m * (2 : ℝ) ^ F.canonicalExp x) : x ∈ F.unbounded := by
  refine ⟨?_, ?_, trivial⟩
  · change Dyadic.precisionAtMost F.p x
    cases hp : F.p using ENat.recTopCoe with
    | top => trivial
    | coe p =>
      by_cases hx : (x : ℝ) = 0
      · exact (Dyadic.precisionAtMost_coe_real p x).mpr ⟨0, 0, by simp [hx], by simp⟩
      exact (Dyadic.precisionAtMost_coe_real p x).mpr
        ⟨m, _, h, F.abs_lt_of_mul_zpow_canonicalExp hp hx h⟩
  · change Dyadic.quantumAtLeast F.exp x
    cases he : F.exp using QExp.recBotCoe with
    | bot => trivial
    | coe e =>
      exact (Dyadic.quantumAtLeast_coe_real e x).mpr
        ⟨_, h.trans (two_zpow_shift m (F.exp_le_canonicalExp _ he))⟩

namespace FiniteFormat

/-- Number of binary digits `F` keeps for `x`: from `x`'s leading bit down to its
canonical exponent, `⌊log₂|x|⌋ + 1 − canonicalExp x`, and `0` at `x = 0`. The
precision at which `IsOdd` reads the significand. -/
noncomputable def numDigits (F : FiniteFormat) (x : ℝ) : ℤ :=
  if x = 0 then 0 else Int.log 2 |x| + 1 - F.canonicalExp x

theorem numDigits_neg (F : FiniteFormat) (x : ℝ) :
    F.numDigits (-x) = F.numDigits x := by
  simp [numDigits, canonicalExp_neg]

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
      exact_mod_cast hle
    have hb' : |(h : ℚ)| ≤ ((b.val : Dyadic) : ℚ) := hb
    change |(g : ℚ)| ≤ ((b.val : Dyadic) : ℚ)
    linarith

/-- A bound check against a finite bound, transferred to an absolute-value
bound over `ℝ`. -/
theorem abs_coe_real_le_of_boundOK {b₁ : NonNegDyadic} {y : Dyadic}
    (h : Format.boundOK ((b₁ : Bound)) y) :
    |(y : ℝ)| ≤ ((b₁.val : Dyadic) : ℝ) := by
  exact_mod_cast h

/-- Converse of `abs_coe_real_le_of_boundOK`. -/
theorem boundOK_coe_of_abs_le {b : NonNegDyadic} {y : Dyadic}
    (h : |(y : ℝ)| ≤ ((b.val : Dyadic) : ℝ)) :
    Format.boundOK ((b : Bound)) y := by
  change |(y : ℚ)| ≤ ((b.val : Dyadic) : ℚ)
  exact_mod_cast h

/-- A dyadic between two in-bound dyadics is in-bound. -/
theorem boundOK_of_between {b : Bound} {lo hi g : Dyadic}
    (hblo : Format.boundOK b lo) (hbhi : Format.boundOK b hi)
    (h1 : (lo : ℝ) ≤ (g : ℝ)) (h2 : (g : ℝ) ≤ (hi : ℝ)) :
    Format.boundOK b g := by
  cases b using Bound.recTopCoe with
  | top => trivial
  | coe b =>
    have h1' : (lo : ℚ) ≤ (g : ℚ) := by
      exact_mod_cast h1
    have h2' : (g : ℚ) ≤ (hi : ℚ) := by
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

/-- Without a bound, a format has every number of positive values: the powers
of two from its minimum quantum up. -/
theorem FiniteFormat.hasPositive_of_b_top {F : FiniteFormat} (hb : F.b = ⊤) (n : ℕ) :
    F.toFormat.HasPositive n := by
  set e₀ : ℤ := F.exp.unbotD 0
  refine ⟨fun i => Dyadic.ofIntZpow 1 (e₀ + i), fun i j hij => ?_, fun i => ⟨?_, ?_⟩⟩
  · simp only [coe_real_ofIntZpow_one]
    exact zpow_lt_zpow_right₀ (by norm_num) (by simpa using hij)
  · refine Format.ofIntZpow_mem (precisionAtMost_one_zpow F.pos _) ?_ (by rw [hb]; trivial)
    cases he : F.exp using QExp.recBotCoe with
    | bot => exact bot_le
    | coe e =>
      have : e₀ = e := by simp [e₀, he]
      exact WithBot.coe_le_coe.mpr (by omega)
  · rw [coe_real_ofIntZpow_one]; exact zpow_pos (by norm_num) _

/-- A `FiniteFormat` with `exp = ⊥` has finite precision. -/
theorem exists_p_coe_of_exp_bot {F : FiniteFormat} (he : F.exp = ⊥) :
    ∃ p : ℕ, F.p = (p : Prec) := by
  cases hc : F.p using ENat.recTopCoe with
  | top => exact absurd F.finite (by push Not; exact ⟨hc, he⟩)
  | coe p => exact ⟨p, rfl⟩

end Mpfx
