import Fpy.Value

/-!
# FPy syntax (Figure 2)

Expressions, statements and programs of the core language. The operators are
left abstract: a `Signature` names the rounded (`Arith`) and unrounded
(`Exact`) operators, gives their meaning, and gives the map `ρ` from records to
rounding functions. Each theorem about FPy holds for every signature.
-/

namespace Fpy

abbrev Var := String
abbrev Fn := String

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

/-! ## Well-formedness

A program is well formed when every record literal in it has distinct labels.
The theorems that need this assume it. -/

variable {L}

mutual

def Expr.WF : Expr L → Prop
  | .arith _ es | .exact _ es | .list es => Expr.WFList es
  | .index e₁ e₂ => e₁.WF ∧ e₂.WF
  | .record fs => (fs.map Prod.fst).Nodup ∧ Expr.WFFields fs
  | .proj e _ | .call _ e | .ctx e => e.WF
  | .bool _ | .num _ | .var _ | .real => True

def Expr.WFList : List (Expr L) → Prop
  | [] => True
  | e :: es => e.WF ∧ Expr.WFList es

def Expr.WFFields : List (Label × Expr L) → Prop
  | [] => True
  | (_, e) :: fs => e.WF ∧ Expr.WFFields fs

end

def Stmt.WF : Stmt L → Prop
  | .assign _ e | .ret e | .assert e => e.WF
  | .seq s₁ s₂ => s₁.WF ∧ s₂.WF
  | .ite e s₁ s₂ => e.WF ∧ s₁.WF ∧ s₂.WF
  | .whileDo e s | .withCtx e s => e.WF ∧ s.WF
  | .skip => True

def Program.WF (Φ : Program L) : Prop := ∀ f y s, Φ f = some (y, s) → s.WF

end Fpy
