import Mpfx.Format.Defs

/-!
# FPy syntax (Figure 2)

Expressions, statements and programs of the core language, and its values
(Figure 10). The operators are left abstract: a `Signature` names the
rounded (`Arith`) and unrounded (`Exact`) operators, gives their meaning, and
gives the map `ρ` from records to rounding functions. Each theorem about FPy
holds for every signature.
-/

namespace Fpy

open Mpfx

/-- Numbers: the extended reals `ℝ ∪ {±∞, NaN}`. -/
abbrev Num := WithSpecial ℝ

abbrev Var := String
abbrev Fn := String
abbrev Label := String

/-- Values. `real` is the real context `R`, and `ctx fs` is the context built
from the record with fields `fs`. -/
inductive Val where
  | bool (b : Bool)
  | num (n : Num)
  | list (vs : List Val)
  | record (fs : List (Label × Val))
  | real
  | ctx (fs : List (Label × Val))

/-- The operators of FPy and the rounding functions of its contexts. -/
structure Signature where
  /-- Operators that round under the current context. -/
  ArithOp : Type
  /-- Operators that never round. -/
  ExactOp : Type
  /-- The exact result `[[op(n₁, …, nₖ)]]` of a rounded operator. -/
  arith : ArithOp → List Num → Option Num
  /-- The result of an unrounded operator. -/
  exact : ExactOp → List Val → Option Val
  /-- The rounding function of the context built from a record; `none` off
  `dom(ρ)`. -/
  ρ : List (Label × Val) → Option (Num → Num)

variable (L : Signature)

inductive Expr where
  | bool (b : Bool)
  | num (n : Num)
  | var (x : Var)
  | arith (op : L.ArithOp) (args : List Expr)
  | exact (op : L.ExactOp) (args : List Expr)
  | list (es : List Expr)
  | index (e₁ e₂ : Expr)
  | record (fs : List (Label × Expr))
  | proj (e : Expr) (l : Label)
  | call (f : Fn) (e : Expr)
  /-- The real context `R`. -/
  | real
  /-- The context constructor `ctx e`. -/
  | ctx (e : Expr)

inductive Stmt where
  | assign (x : Var) (e : Expr L)
  | seq (s₁ s₂ : Stmt)
  | ite (e : Expr L) (s₁ s₂ : Stmt)
  | whileDo (e : Expr L) (s : Stmt)
  | ret (e : Expr L)
  | assert (e : Expr L)
  | skip
  /-- The context statement `with e in s`. -/
  | withCtx (e : Expr L) (s : Stmt)

/-- A program `Φ` maps each function to its parameter and body. -/
abbrev Program := Fn → Option (Var × Stmt L)

end Fpy
