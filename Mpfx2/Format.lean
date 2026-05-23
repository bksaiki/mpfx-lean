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

end Format

instance : Membership Dyadic Format := ⟨Format.Mem⟩

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

end ParityFormat

end Mpfx2
