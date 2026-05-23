import Mpfx2.Dyadic

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

/-- A non-degenerate `Format`. Imposes the structural invariant that rules out
the two pathological doubly-unbounded cases:

* `𝒜(⊤, ⊥, b)` — entirely unconstrained.
* `𝒜(1, ⊥, b)` — precision `1` with no quantum has no anchor for parity, so
  `IsOdd` would be meaningless.

Most theorems should be stated on the looser `Format` type and only promoted
to `FiniteFormat` when their proof actually destructures `wf`. -/
structure FiniteFormat extends Format where
  wf : (toFormat.p ≠ ⊤ ∧ toFormat.p ≠ 1) ∨ toFormat.exp ≠ ⊥

namespace FiniteFormat

end FiniteFormat

end Mpfx2
