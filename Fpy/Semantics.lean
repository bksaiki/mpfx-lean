import Fpy.Syntax

/-!
# FPy semantics (Figure 10)

Big-step semantics: under store `σ` and current context `C`, `Eval Φ σ C e v`
is `⟨σ, C, e⟩ ⇓ v` and `Exec Φ σ C s o` is `⟨σ, C, s⟩ ⇓ₛ o`. `EvalList` and
`EvalFields` evaluate the arguments of an operator and the fields of a record.
-/

namespace Fpy

variable {L : Signature}

abbrev Store := Var → Option Val

/-- The store `[y ↦ v]`. -/
def Store.single (y : Var) (v : Val) : Store := fun x => if x = y then some v else none

/-- The store `σ[x ↦ v]`. -/
def Store.update (σ : Store) (x : Var) (v : Val) : Store := Function.update σ x (some v)

inductive Outcome where
  | normal (σ : Store)
  | ret (v : Val)

/-- The rounding function `C(·)` of a context: the identity for `R`, `ρ` of
the record for `ctx`. Other values are not contexts. -/
def Val.rnd (L : Signature) : Val → Option (Num → Num)
  | .real => some id
  | .ctx fs => L.ρ fs
  | _ => none

variable (Φ : Program L)

mutual

inductive Eval : Store → Val → Expr L → Val → Prop
  | bool {σ C b} : Eval σ C (.bool b) (.bool b)
  | num {σ C n} : Eval σ C (.num n) (.num n)
  | real {σ C} : Eval σ C .real .real
  | var {σ C x v} : σ x = some v → Eval σ C (.var x) v
  | list {σ C es vs} : EvalList σ C es vs → Eval σ C (.list es) (.list vs)
  | index {σ C e₁ e₂ vs v} {k : ℕ} :
      Eval σ C e₁ (.list vs) → Eval σ C e₂ (.num (.finite k)) → vs[k]? = some v →
      Eval σ C (.index e₁ e₂) v
  | record {σ C fs vs} : EvalFields σ C fs vs → Eval σ C (.record fs) (.record vs)
  | proj {σ C e fs l v} : Eval σ C e (.record fs) → fs.lookup l = some v →
      Eval σ C (.proj e l) v
  | ctx {σ C e fs} : Eval σ C e (.record fs) → (L.ρ fs).isSome →
      Eval σ C (.ctx e) (.ctx fs)
  | arith {σ C op es ns n r} : EvalList σ C es (ns.map .num) → L.arith op ns = some n →
      C.rnd L = some r → Eval σ C (.arith op es) (.num (r n))
  | exact {σ C op es vs v} : EvalList σ C es vs → L.exact op vs = some v →
      Eval σ C (.exact op es) v
  | call {σ C f e y s v v'} : Φ f = some (y, s) → Eval σ C e v →
      Exec (.single y v) C s (.ret v') → Eval σ C (.call f e) v'

inductive EvalList : Store → Val → List (Expr L) → List Val → Prop
  | nil {σ C} : EvalList σ C [] []
  | cons {σ C e es v vs} : Eval σ C e v → EvalList σ C es vs → EvalList σ C (e :: es) (v :: vs)

inductive EvalFields : Store → Val → List (Label × Expr L) → List (Label × Val) → Prop
  | nil {σ C} : EvalFields σ C [] []
  | cons {σ C l e fs v vs} : Eval σ C e v → EvalFields σ C fs vs →
      EvalFields σ C ((l, e) :: fs) ((l, v) :: vs)

inductive Exec : Store → Val → Stmt L → Outcome → Prop
  | assign {σ C x e v} : Eval σ C e v → Exec σ C (.assign x e) (.normal (σ.update x v))
  | skip {σ C} : Exec σ C .skip (.normal σ)
  | ret {σ C e v} : Eval σ C e v → Exec σ C (.ret e) (.ret v)
  | assert {σ C e} : Eval σ C e (.bool true) → Exec σ C (.assert e) (.normal σ)
  | seqNormal {σ C s₁ s₂ σ' o} : Exec σ C s₁ (.normal σ') → Exec σ' C s₂ o →
      Exec σ C (.seq s₁ s₂) o
  | seqRet {σ C s₁ s₂ v} : Exec σ C s₁ (.ret v) → Exec σ C (.seq s₁ s₂) (.ret v)
  | iteTrue {σ C e s₁ s₂ o} : Eval σ C e (.bool true) → Exec σ C s₁ o →
      Exec σ C (.ite e s₁ s₂) o
  | iteFalse {σ C e s₁ s₂ o} : Eval σ C e (.bool false) → Exec σ C s₂ o →
      Exec σ C (.ite e s₁ s₂) o
  | whileFalse {σ C e s} : Eval σ C e (.bool false) → Exec σ C (.whileDo e s) (.normal σ)
  | whileTrue {σ C e s o} : Eval σ C e (.bool true) → Exec σ C (.seq s (.whileDo e s)) o →
      Exec σ C (.whileDo e s) o
  | withCtx {σ C e C' s o} : Eval σ .real e C' → Exec σ C' s o → Exec σ C (.withCtx e s) o

end

/-- `(Φ, f)(v) ⇓ v'`: the entry function `f`, called on `v` under `R`, returns `v'`. -/
def Run (f : Fn) (v v' : Val) : Prop :=
  ∃ y s, Φ f = some (y, s) ∧ Exec Φ (.single y v) .real s (.ret v')

end Fpy
