import Fpy.Syntax
import Mpfx.Rounding.Op

/-!
# The FPy signature

The operators of Table 1 with IEEE 754 special-value rules over `Num`, and
contexts that round with `Mpfx.rnd`. There is no signed zero, so `0` carries no
sign. The record layout of a context is left to a decoding: `fpy decode` reads
the record `fs` as the rounding context `decode fs`.
-/

namespace Fpy

open Mpfx

namespace Num

/-- IEEE 754 addition of exact values. -/
noncomputable def add : Num → Num → Num
  | .finite x, .finite y => .finite (x + y)
  | .special .nan, _ | _, .special .nan => .special .nan
  | .special (.inf a), .special (.inf b) => if a = b then .special (.inf a) else .special .nan
  | .special (.inf a), .finite _ | .finite _, .special (.inf a) => .special (.inf a)

/-- IEEE 754 multiplication of exact values. -/
noncomputable def mul : Num → Num → Num
  | .finite x, .finite y => .finite (x * y)
  | .special .nan, _ | _, .special .nan => .special .nan
  | .special (.inf a), .special (.inf b) => .special (.inf (xor a b))
  | .special (.inf a), .finite y | .finite y, .special (.inf a) =>
      if y = 0 then .special .nan else .special (.inf (xor a (decide (y < 0))))

def neg : Num → Num := WithSpecial.neg

noncomputable def sub (u v : Num) : Num := add u (neg v)

/-- IEEE 754 division. A nonzero value over `0` is an infinity of its sign. -/
noncomputable def div : Num → Num → Num
  | .finite x, .finite y =>
      if y = 0 then (if x = 0 then .special .nan else .special (.inf (decide (x < 0))))
      else .finite (x / y)
  | .special .nan, _ | _, .special .nan => .special .nan
  | .special (.inf _), .special (.inf _) => .special .nan
  | .special (.inf a), .finite y => .special (.inf (xor a (decide (y < 0))))
  | .finite _, .special (.inf _) => .finite 0

noncomputable def sqrt : Num → Num
  | .finite x => if x < 0 then .special .nan else .finite (Real.sqrt x)
  | .special (.inf false) => .special (.inf false)
  | .special _ => .special .nan

/-- Fused multiply-add: `u × v + w` with one rounding. -/
noncomputable def fma (u v w : Num) : Num := add (mul u v) w

noncomputable def abs : Num → Num
  | .finite x => .finite |x|
  | .special (.inf _) => .special (.inf false)
  | .special .nan => .special .nan

/-- `logb x = ⌊log₂ |x|⌋`; `logb 0 = −∞` and `logb (±∞) = +∞`, as IEEE 754
`logB`. -/
noncomputable def logb : Num → Num
  | .finite x => if x = 0 then .special (.inf true) else .finite (Int.log 2 |x|)
  | .special (.inf _) => .special (.inf false)
  | .special .nan => .special .nan

/-- `2ˣ`; `2^(−∞) = 0`. -/
noncomputable def exp2 : Num → Num
  | .finite x => .finite ((2 : ℝ) ^ x)
  | .special (.inf false) => .special (.inf false)
  | .special (.inf true) => .finite 0
  | .special .nan => .special .nan

/-- The minimum, with NaN propagating (IEEE 754-2019 `minimum`). -/
noncomputable def min : Num → Num → Num
  | .special .nan, _ | _, .special .nan => .special .nan
  | .special (.inf true), _ | _, .special (.inf true) => .special (.inf true)
  | .special (.inf false), v | v, .special (.inf false) => v
  | .finite x, .finite y => .finite (Min.min x y)

/-- The maximum, with NaN propagating (IEEE 754-2019 `maximum`). -/
noncomputable def max : Num → Num → Num
  | .special .nan, _ | _, .special .nan => .special .nan
  | .special (.inf false), _ | _, .special (.inf false) => .special (.inf false)
  | .special (.inf true), v | v, .special (.inf true) => v
  | .finite x, .finite y => .finite (Max.max x y)

/-- `u = v`; NaN equals nothing. -/
noncomputable def eq : Num → Num → Bool
  | .finite x, .finite y => decide (x = y)
  | .special (.inf a), .special (.inf b) => a == b
  | _, _ => false

/-- `u < v`; false when either is NaN. -/
noncomputable def lt : Num → Num → Bool
  | .finite x, .finite y => decide (x < y)
  | .special (.inf true), .finite _ | .special (.inf true), .special (.inf false)
  | .finite _, .special (.inf false) => true
  | _, _ => false

noncomputable def le (u v : Num) : Bool := lt u v || eq u v

def isNaN : Num → Bool
  | .special .nan => true
  | _ => false

def isInf : Num → Bool
  | .special (.inf _) => true
  | _ => false

end Num

/-- The rounded operators of FPy. -/
inductive ArithOp where
  | add | sub | mul | div | sqrt | fma | neg | abs | logb | exp2 | min | max | round | cast
deriving DecidableEq

/-- The unrounded operators of FPy. -/
inductive ExactOp where
  | lt | le | eq | len | isNaN | isInf | and | or | not
deriving DecidableEq

/-- The exact result of a rounded operator. `round` and `cast` compute the
identity; the context does the rounding. -/
noncomputable def ArithOp.eval : ArithOp → List Num → Option Num
  | .add, [u, v] => some (Num.add u v)
  | .sub, [u, v] => some (Num.sub u v)
  | .mul, [u, v] => some (Num.mul u v)
  | .div, [u, v] => some (Num.div u v)
  | .sqrt, [u] => some (Num.sqrt u)
  | .fma, [u, v, w] => some (Num.fma u v w)
  | .neg, [u] => some (Num.neg u)
  | .abs, [u] => some (Num.abs u)
  | .logb, [u] => some (Num.logb u)
  | .exp2, [u] => some (Num.exp2 u)
  | .min, [u, v] => some (Num.min u v)
  | .max, [u, v] => some (Num.max u v)
  | .round, [u] | .cast, [u] => some u
  | _, _ => none

noncomputable def ExactOp.eval : ExactOp → List Val → Option Val
  | .lt, [.num u, .num v] => some (.bool (Num.lt u v))
  | .le, [.num u, .num v] => some (.bool (Num.le u v))
  | .eq, [.num u, .num v] => some (.bool (Num.eq u v))
  | .len, [.list vs] => some (.num (.finite vs.length))
  | .isNaN, [.num u] => some (.bool (Num.isNaN u))
  | .isInf, [.num u] => some (.bool (Num.isInf u))
  | .and, [.bool a, .bool b] => some (.bool (a && b))
  | .or, [.bool a, .bool b] => some (.bool (a || b))
  | .not, [.bool a] => some (.bool !a)
  | _, _ => none

/-! ## Rounding contexts -/

/-- A rounding context of Mpfx: rounding into `F` under `rm`, with special
inputs sent through `S` and overflow through `O`. -/
structure RoundCtx where
  F : FiniteFormat
  S : SpecialMap F.toFormat
  O : OverflowMap F.toFormat
  rm : RoundingMode
  defined : ¬ F.IsUndefined rm

/-- `rnd` under a context, read back as a number. -/
noncomputable def RoundCtx.round (c : RoundCtx) (n : Num) : Num :=
  match rnd c.F c.S c.O c.rm n with
  | .value v => v.toReal
  | .undefined => n

theorem RoundCtx.exists_rnd_eq (c : RoundCtx) (n : Num) :
    ∃ w, rnd c.F c.S c.O c.rm n = .value w ∧ c.round n = w.toReal := by
  cases n with
  | special s => exact ⟨_, rnd_special .., rfl⟩
  | finite x =>
    simp only [RoundCtx.round, rnd, dif_neg c.defined]
    split_ifs <;> exact ⟨_, rfl, rfl⟩

namespace RoundCtx

theorem round_special (c : RoundCtx) (s : Special) : c.round (.special s) = (c.S.map s).toReal :=
  rfl

open Classical in
theorem round_finite (c : RoundCtx) (y : ℝ) :
    c.round (.finite y) =
      if Format.boundOK c.F.b (rndUnbounded c.F c.rm y c.defined) then
        .finite ((rndUnbounded c.F c.rm y c.defined : Mpfx.Dyadic) : ℝ)
      else
        (c.O.map (decide ((rndUnbounded c.F c.rm y c.defined : ℚ) < 0))).toReal := by
  simp only [RoundCtx.round, rnd, dif_neg c.defined]
  split_ifs <;> rfl

theorem round_zero (c : RoundCtx) : c.round (.finite 0) = .finite 0 := by
  have h0 : rndUnbounded c.F c.rm 0 c.defined = 0 :=
    RoundsFinite.eq_zero_of_zero (rndUnbounded_satisfies _ _ _ _)
  rw [round_finite, h0, if_pos (Format.boundOK_zero _)]
  simp

end RoundCtx

/-- The FPy signature. `decode` reads a record as a rounding context;
records it rejects are outside `dom(ρ)`. -/
noncomputable def fpy (decode : List (Label × Val) → Option RoundCtx) : Signature where
  ArithOp := ArithOp
  ExactOp := ExactOp
  arith := ArithOp.eval
  exact := ExactOp.eval
  ρ fs := (decode fs).map RoundCtx.round

end Fpy
