import Fpy.Ops
import Fpy.Semantics
import Mathlib.Order.WithBotTop

/-!
# Digit-bound analysis (§4.3, Figure 12)

The positions of a value's least and most significant digits, `lsbOf` and
`msbOf`, are extended integers: `0` has no digits, so its interval is
`[+∞, −∞]` (the draft's `∅`); an infinity has `[+∞, +∞]`; a value with
infinitely many digits has least significant digit `−∞`. NaN lies in every
interval. A symbolic value is a term for an integer value, matched through
`numOfE`, so `logb 0 = −∞ = msb(0)`.

The analysis introduces fresh integer variables above a counter it threads
(`n₀ → n₁`), and bounds each by one constraint (`Con`). Every operator and
rounding transfer is a semantic premise (`ArithOK`), and the joins are an order
with fresh variables (`DVal.Le`, `DEnv.Le`): Table 2's rows and the draft's
joins are instances. D-While takes an invariant, as A-While. The rules for
integer values (D-Linear, D-Neg, D-Logb, D-Max, D-Min) are under `R`.
-/

namespace Fpy.DigitBound

open Mpfx

/-! ## Digit positions -/

/-- Negation of an extended integer. -/
def negE (z : EInt) : EInt :=
  WithBotTop.rec (motive := fun _ => EInt) ⊤ (fun k => ((-k : ℤ) : EInt)) ⊥ z

/-- An extended integer as a number. -/
def numOfE (z : EInt) : Num :=
  WithBotTop.rec (motive := fun _ => Num) (.special (.inf true)) (fun k : ℤ => .finite (k : ℝ))
    (.special (.inf false)) z

/-- `x` is `c · 2ᵏ` with `c` odd: its least significant digit is at `k`. -/
def LsbAt (x : ℝ) (k : ℤ) : Prop := ∃ c : ℤ, Odd c ∧ x = c * 2 ^ k

open Classical in
/-- The position of a number's least significant digit (`min digits`): `+∞`
for `0` and the infinities, `−∞` for a value with infinitely many digits. -/
noncomputable def lsbOf : Num → EInt
  | .finite x => if x = 0 then ⊤ else if h : ∃ k, LsbAt x k then (Classical.choose h : ℤ) else ⊥
  | .special _ => ⊤

open Classical in
/-- The position of a number's most significant digit (`max digits`): `−∞` for
`0`, `+∞` for the infinities. -/
noncomputable def msbOf : Num → EInt
  | .finite x => if x = 0 then ⊥ else (Int.log 2 |x| : ℤ)
  | .special _ => ⊤

/-! ## Terms and constraints -/

/-- An integer assignment `ι`. -/
abbrev Asgn := ℕ → EInt

inductive Term where
  | const (z : EInt)
  | var (x : ℕ)
  | add (a b : Term)
  | neg (a : Term)

def Term.eval (ι : Asgn) : Term → EInt
  | .const z => z
  | .var x => ι x
  | .add a b => a.eval ι + b.eval ι
  | .neg a => negE (a.eval ι)

/-- Every variable of `t` is below `n`. -/
def Term.Below (n : ℕ) : Term → Prop
  | .const _ => True
  | .var x => x < n
  | .add a b => a.Below n ∧ b.Below n
  | .neg a => a.Below n

theorem Term.eval_congr {n : ℕ} {ι ι' : Asgn} (h : ∀ x < n, ι x = ι' x) :
    ∀ {t : Term}, t.Below n → t.eval ι = t.eval ι'
  | .const _, _ => rfl
  | .var x, hx => h x hx
  | .add _ _, ⟨ha, hb⟩ => congrArg₂ (· + ·) (Term.eval_congr h ha) (Term.eval_congr h hb)
  | .neg _, ha => congrArg negE (Term.eval_congr h ha)

/-- `ι` and `ι'` agree below `n`. -/
def Agree (n : ℕ) (ι ι' : Asgn) : Prop := ∀ x < n, ι x = ι' x

/-- `ι'` differs from `ι` only on `[n₀, n₁)`. -/
def AgreeOut (n₀ n₁ : ℕ) (ι ι' : Asgn) : Prop := ∀ x, x < n₀ ∨ n₁ ≤ x → ι' x = ι x

/-- A constraint bounding the fresh variable `head`. It depends only on
variables up to `head`, and some value of `head` satisfies it whatever the
others are. -/
structure Con where
  head : ℕ
  P : Asgn → Prop
  dep : ∀ {ι ι' : Asgn}, (∀ x ≤ head, ι x = ι' x) → P ι → P ι'
  sat : ∀ ι : Asgn, ∃ z, P (Function.update ι head z)

/-- `ι ⊨ Ψ`. -/
def Sat (ι : Asgn) (Ψ : List Con) : Prop := ∀ c ∈ Ψ, c.P ι

/-- `Ψ` bounds distinct fresh variables in `[n₀, n₁)`. -/
def Fresh (n₀ n₁ : ℕ) (Ψ : List Con) : Prop :=
  n₀ ≤ n₁ ∧ (Ψ.map Con.head).Nodup ∧ ∀ c ∈ Ψ, n₀ ≤ c.head ∧ c.head < n₁

/-! ## Abstract values -/

/-- A symbolic context (`ctx♮`): `R`, or the context of a record whose integer
fields are terms. -/
inductive SCtx where
  | real
  | record (fs : List (Label × Term))

/-- `ι(C)` admits the context `v`: `R` is `R`, and a record context's fields
are its terms' values, or NaN. -/
def SCtx.Admits (ι : Asgn) : SCtx → Val → Prop
  | .real, v => v = .real
  | .record fs, v => ∃ vs, v = .ctx vs ∧ List.Forall₂ (fun (f : Label × Term) (w : Label × Val) =>
      f.1 = w.1 ∧ (w.2 = .num (numOfE (f.2.eval ι)) ∨ w.2 = .num (.special .nan))) fs vs

def SCtx.Below (n : ℕ) : SCtx → Prop
  | .real => True
  | .record fs => ∀ f ∈ fs, f.2.Below n

/-- Abstract values: `num l m τ` is `⟨[l, m], τ⟩`, a list's elements share one
abstract value, `other` is `•`, and `ctx C` a symbolic context. -/
inductive DVal where
  | num (l m : Term) (τ : Option Term)
  | list (d : DVal)
  | record (fs : List (Label × DVal))
  | other
  | ctx (C : SCtx)

/-- `n` has digits `[l, m]` and value `τ` under `ι`; NaN lies in every interval. -/
def NumIn (ι : Asgn) (l m : Term) (τ : Option Term) (n : Num) : Prop :=
  n = .special .nan ∨
    (lsbOf n = l.eval ι ∧ msbOf n = m.eval ι ∧ ∀ t ∈ τ, n = numOfE (t.eval ι))

mutual

/-- `v ∈ γ_ι(d)`. A list's elements are each described under their own
assignment. -/
inductive Describes : Asgn → DVal → Val → Prop
  | num {ι l m τ n} : NumIn ι l m τ n → Describes ι (.num l m τ) (.num n)
  | list {ι d vs} : DescribesAll d vs → Describes ι (.list d) (.list vs)
  | record {ι afs fs} : DescribesFields ι afs fs → Describes ι (.record afs) (.record fs)
  | bool {ι b} : Describes ι .other (.bool b)
  | real {ι} : Describes ι .other .real
  | ctxv {ι fs} : Describes ι .other (.ctx fs)
  | sctx {ι C v} : C.Admits ι v → Describes ι (.ctx C) v

inductive DescribesAll : DVal → List Val → Prop
  | nil {d} : DescribesAll d []
  | cons {ι d v vs} : Describes ι d v → DescribesAll d vs → DescribesAll d (v :: vs)

inductive DescribesFields : Asgn → List (Label × DVal) → List (Label × Val) → Prop
  | nil {ι} : DescribesFields ι [] []
  | cons {ι l a v afs fs} : Describes ι a v → DescribesFields ι afs fs →
      DescribesFields ι ((l, a) :: afs) ((l, v) :: fs)

end

mutual

def DVal.Below (n : ℕ) : DVal → Prop
  | .num l m τ => l.Below n ∧ m.Below n ∧ ∀ t ∈ τ, t.Below n
  | .list _ => True
  | .record fs => DVal.BelowFields n fs
  | .other => True
  | .ctx C => C.Below n

def DVal.BelowFields (n : ℕ) : List (Label × DVal) → Prop
  | [] => True
  | (_, d) :: fs => d.Below n ∧ DVal.BelowFields n fs

end

/-- The return bound of a statement: `none` (`⊥`) bounds no value. -/
def RetBelow (n : ℕ) (a : Option DVal) : Prop := ∀ d ∈ a, d.Below n

/-- A digit environment `Δ`. -/
abbrev DEnv := Var → Option DVal

def DEnv.Holds (Δ : DEnv) (ι : Asgn) (σ : Store) : Prop :=
  ∀ x d, Δ x = some d → ∃ v, σ x = some v ∧ Describes ι d v

def DEnv.Below (n : ℕ) (Δ : DEnv) : Prop := ∀ x d, Δ x = some d → d.Below n

def DEnv.single (y : Var) (d : DVal) : DEnv := fun x => if x = y then some d else none

def DEnv.update (Δ : DEnv) (x : Var) (d : DVal) : DEnv := Function.update Δ x (some d)

def CtxBelow (n : ℕ) (κ : Option SCtx) : Prop := ∀ C ∈ κ, C.Below n

/-! ## Joins and transfers -/

/-- `d ⊑ d'`, with the fresh variables `[n₀, n₁)` of `d'` bounded by `Ψ`:
whatever `d` describes, `d'` describes once those variables are re-chosen. -/
def DVal.Le (n₀ n₁ : ℕ) (Ψ : List Con) (d d' : DVal) : Prop :=
  ∀ ι v, Describes ι d v → ∃ ι', AgreeOut n₀ n₁ ι ι' ∧ Sat ι' Ψ ∧ Describes ι' d' v

def RetLe (n₀ n₁ : ℕ) (Ψ : List Con) (a a' : Option DVal) : Prop :=
  ∀ d ∈ a, ∃ d' ∈ a', DVal.Le n₀ n₁ Ψ d d'

def DEnv.Le (n₀ n₁ : ℕ) (Ψ : List Con) (Δ Δ' : DEnv) : Prop :=
  ∀ ι σ, Δ.Holds ι σ → ∃ ι', AgreeOut n₀ n₁ ι ι' ∧ Sat ι' Ψ ∧ Δ'.Holds ι' σ

/-- A list element's abstract value `d`, copied to `d'` with fresh variables:
whatever `d` describes under any assignment, `d'` describes. -/
def DVal.Copy (n₀ n₁ : ℕ) (Ψ : List Con) (d d' : DVal) : Prop :=
  ∀ ι₀ ι v, Describes ι₀ d v → ∃ ι', AgreeOut n₀ n₁ ι ι' ∧ Sat ι' Ψ ∧ Describes ι' d' v

variable {decode : List (Label × Val) → Option RoundCtx}

variable (decode) in
/-- `rnd♮_κ(op♮(Is))`: the interval `[l, m]`, with fresh variables `[n₀, n₁)`
bounded by `Ψ`, bounds `op` on values with digits `Is`, rounded under any
context `κ` admits. -/
def ArithOK (κ : Option SCtx) (op : ArithOp) (Is : List (Term × Term)) (n₀ n₁ : ℕ)
    (Ψ : List Con) (l m : Term) : Prop :=
  ∀ ι ns u C r, List.Forall₂ (fun (I : Term × Term) n => NumIn ι I.1 I.2 none n) Is ns →
    op.eval ns = some u → (∀ K ∈ κ, K.Admits ι C) → C.rnd (fpy decode) = some r →
    ∃ ι', AgreeOut n₀ n₁ ι ι' ∧ Sat ι' Ψ ∧ NumIn ι' l m none (r u)

/-- The symbolic context a record's abstract value gives, when its fields all
have symbolic values. -/
def ctxOfFields : List (Label × DVal) → Option (List (Label × Term))
  | [] => some []
  | (l, .num _ _ (some t)) :: fs => (ctxOfFields fs).map ((l, t) :: ·)
  | _ => none

def ctxOf : DVal → Option SCtx
  | .record fs => (ctxOfFields fs).map .record
  | _ => none

/-- The bound `max`/`min` place on the fresh variable `v`: `v ≥ τ₁, τ₂`
(`ge = true`) or `v ≤ τ₁, τ₂`. -/
def Con.ext (v : ℕ) (ge : Bool) (τ₁ τ₂ : Term) (h₁ : τ₁.Below v) (h₂ : τ₂.Below v) : Con where
  head := v
  P ι := if ge then τ₁.eval ι ≤ ι v ∧ τ₂.eval ι ≤ ι v else ι v ≤ τ₁.eval ι ∧ ι v ≤ τ₂.eval ι
  dep {ι ι'} h hP := by
    have e₁ : τ₁.eval ι = τ₁.eval ι' := Term.eval_congr (fun x hx => h x hx.le) h₁
    have e₂ : τ₂.eval ι = τ₂.eval ι' := Term.eval_congr (fun x hx => h x hx.le) h₂
    rw [← e₁, ← e₂, ← h v le_rfl]
    exact hP
  sat ι := by
    refine ⟨if ge then ⊤ else ⊥, ?_⟩
    have e₁ : τ₁.eval (Function.update ι v (if ge then ⊤ else ⊥)) = τ₁.eval ι :=
      (Term.eval_congr (fun x hx => Function.update_of_ne hx.ne _ _) h₁)
    have e₂ : τ₂.eval (Function.update ι v (if ge then ⊤ else ⊥)) = τ₂.eval ι :=
      (Term.eval_congr (fun x hx => Function.update_of_ne hx.ne _ _) h₂)
    rw [e₁, e₂, Function.update_self]
    cases ge <;> simp

/-! ## The analysis -/

variable (decode) (Φ : Program (fpy decode))

mutual

/-- `Δ, κ ⊢♮ e : d`, with fresh variables `[n₀, n₁)` bounded by `Ψ`. -/
inductive DEval : DEnv → Option SCtx → ℕ → Expr (fpy decode) → DVal → List Con → ℕ → Prop
  | const {Δ κ n₀ n τ} : (∀ t ∈ τ, ∃ z, t = .const z ∧ n = numOfE z) →
      DEval Δ κ n₀ (.num n) (.num (.const (lsbOf n)) (.const (msbOf n)) τ) [] n₀
  | bool {Δ κ n₀ b} : DEval Δ κ n₀ (.bool b) .other [] n₀
  | real {Δ κ n₀} : DEval Δ κ n₀ .real (.ctx .real) [] n₀
  | var {Δ κ n₀ x d} : Δ x = some d → DEval Δ κ n₀ (.var x) d [] n₀
  | list {Δ κ n₀ es ds Ψ n₁ d Ψ' n₂} : DEvalList Δ κ n₀ es ds Ψ n₁ →
      (∀ d' ∈ ds, DVal.Le n₁ n₂ Ψ' d' d) → Fresh n₁ n₂ Ψ' →
      DEval Δ κ n₀ (.list es) (.list d) (Ψ ++ Ψ') n₂
  | index {Δ κ n₀ e₁ e₂ d Ψ₁ n₁ d₂ Ψ₂ n₂ d' Ψ' n₃} : DEval Δ κ n₀ e₁ (.list d) Ψ₁ n₁ →
      DEval Δ κ n₁ e₂ d₂ Ψ₂ n₂ → DVal.Copy n₂ n₃ Ψ' d d' → Fresh n₂ n₃ Ψ' → d'.Below n₃ →
      DEval Δ κ n₀ (.index e₁ e₂) d' (Ψ₁ ++ Ψ₂ ++ Ψ') n₃
  | record {Δ κ n₀ fs afs Ψ n₁} : DEvalFields Δ κ n₀ fs afs Ψ n₁ →
      DEval Δ κ n₀ (.record fs) (.record afs) Ψ n₁
  | proj {Δ κ n₀ e afs Ψ n₁ l d} : DEval Δ κ n₀ e (.record afs) Ψ n₁ → afs.lookup l = some d →
      DEval Δ κ n₀ (.proj e l) d Ψ n₁
  | ctx {Δ κ n₀ e d Ψ n₁} : DEval Δ κ n₀ e d Ψ n₁ →
      DEval Δ κ n₀ (.ctx e) ((ctxOf d).elim .other .ctx) Ψ n₁
  | arith {Δ κ n₀ op es Ψ n₁ Ψ' n₂ l m} {Is : List (Term × Term × Option Term)} :
      DEvalList Δ κ n₀ es (Is.map fun I => .num I.1 I.2.1 I.2.2) Ψ n₁ →
      ArithOK decode κ op (Is.map fun I => (I.1, I.2.1)) n₁ n₂ Ψ' l m → Fresh n₁ n₂ Ψ' →
      l.Below n₂ → m.Below n₂ → DEval Δ κ n₀ (.arith op es) (.num l m none) (Ψ ++ Ψ') n₂
  /-- D-Linear, under `R`. -/
  | linear {Δ n₀ op e₁ e₂ l₁ m₁ τ₁ l₂ m₂ τ₂ Ψ n₁ Ψ' n₂ l m} (hop : op = .add ∨ op = .sub) :
      DEvalList Δ (some .real) n₀ [e₁, e₂] [.num l₁ m₁ (some τ₁), .num l₂ m₂ (some τ₂)] Ψ n₁ →
      ArithOK decode (some .real) op [(l₁, m₁), (l₂, m₂)] n₁ n₂ Ψ' l m → Fresh n₁ n₂ Ψ' →
      l.Below n₂ → m.Below n₂ →
      DEval Δ (some .real) n₀ (.arith op [e₁, e₂])
        (.num l m (some (if op = .add then .add τ₁ τ₂ else .add τ₁ (.neg τ₂)))) (Ψ ++ Ψ') n₂
  /-- D-Neg, under `R`. -/
  | neg {Δ n₀ e l₁ m₁ τ Ψ n₁ Ψ' n₂ l m} :
      DEvalList Δ (some .real) n₀ [e] [.num l₁ m₁ (some τ)] Ψ n₁ →
      ArithOK decode (some .real) .neg [(l₁, m₁)] n₁ n₂ Ψ' l m → Fresh n₁ n₂ Ψ' →
      l.Below n₂ → m.Below n₂ →
      DEval Δ (some .real) n₀ (.arith .neg [e]) (.num l m (some (.neg τ))) (Ψ ++ Ψ') n₂
  /-- D-Logb, under `R`: the value is the argument's most significant digit. -/
  | logb {Δ n₀ e l₁ m₁ τ Ψ n₁ Ψ' n₂ l m} :
      DEvalList Δ (some .real) n₀ [e] [.num l₁ m₁ τ] Ψ n₁ →
      ArithOK decode (some .real) .logb [(l₁, m₁)] n₁ n₂ Ψ' l m → Fresh n₁ n₂ Ψ' →
      l.Below n₂ → m.Below n₂ →
      DEval Δ (some .real) n₀ (.arith .logb [e]) (.num l m (some m₁)) (Ψ ++ Ψ') n₂
  /-- D-Max (`ge = true`, `op = max`) and D-Min, under `R`: a fresh `val(e)`
  bounded by the arguments' values. -/
  | ext {Δ n₀ op ge e₁ e₂ l₁ m₁ τ₁ l₂ m₂ τ₂ Ψ n₁ Ψ' n₂ l m}
      (hop : op = (if ge then .max else .min)) (h₁ : τ₁.Below n₂) (h₂ : τ₂.Below n₂) :
      DEvalList Δ (some .real) n₀ [e₁, e₂] [.num l₁ m₁ (some τ₁), .num l₂ m₂ (some τ₂)] Ψ n₁ →
      ArithOK decode (some .real) op [(l₁, m₁), (l₂, m₂)] n₁ n₂ Ψ' l m → Fresh n₁ n₂ Ψ' →
      l.Below n₂ → m.Below n₂ →
      DEval Δ (some .real) n₀ (.arith op [e₁, e₂]) (.num l m (some (.var n₂)))
        (Ψ ++ Ψ' ++ [Con.ext n₂ ge τ₁ τ₂ h₁ h₂]) (n₂ + 1)
  | exact {Δ κ n₀ op es ds Ψ n₁} : DEvalList Δ κ n₀ es ds Ψ n₁ → op ≠ .len →
      DEval Δ κ n₀ (.exact op es) .other Ψ n₁
  | len {Δ κ n₀ es ds Ψ n₁} : DEvalList Δ κ n₀ es ds Ψ n₁ →
      DEval Δ κ n₀ (.exact .len es) (.num (.var n₁) (.var (n₁ + 1)) none) Ψ (n₁ + 2)
  | call {Δ κ n₀ f e y s d Ψ n₁ Δ' a Ψ' n₂} : Φ f = some (y, s) → DEval Δ κ n₀ e d Ψ n₁ →
      DExec (.single y d) κ n₁ s Δ' (some a) Ψ' n₂ → DEval Δ κ n₀ (.call f e) a (Ψ ++ Ψ') n₂

inductive DEvalList : DEnv → Option SCtx → ℕ → List (Expr (fpy decode)) → List DVal →
    List Con → ℕ → Prop
  | nil {Δ κ n₀} : DEvalList Δ κ n₀ [] [] [] n₀
  | cons {Δ κ n₀ e es d ds Ψ n₁ Ψ' n₂} : DEval Δ κ n₀ e d Ψ n₁ → DEvalList Δ κ n₁ es ds Ψ' n₂ →
      DEvalList Δ κ n₀ (e :: es) (d :: ds) (Ψ ++ Ψ') n₂

inductive DEvalFields : DEnv → Option SCtx → ℕ → List (Label × Expr (fpy decode)) →
    List (Label × DVal) → List Con → ℕ → Prop
  | nil {Δ κ n₀} : DEvalFields Δ κ n₀ [] [] [] n₀
  | cons {Δ κ n₀ l e fs d afs Ψ n₁ Ψ' n₂} : DEval Δ κ n₀ e d Ψ n₁ →
      DEvalFields Δ κ n₁ fs afs Ψ' n₂ →
      DEvalFields Δ κ n₀ ((l, e) :: fs) ((l, d) :: afs) (Ψ ++ Ψ') n₂

/-- `Δ, κ ⊢♮ s : ⟨Δ', a⟩`, with fresh variables `[n₀, n₁)` bounded by `Ψ`. -/
inductive DExec : DEnv → Option SCtx → ℕ → Stmt (fpy decode) → DEnv → Option DVal → List Con →
    ℕ → Prop
  | assign {Δ κ n₀ x e d Ψ n₁} : DEval Δ κ n₀ e d Ψ n₁ →
      DExec Δ κ n₀ (.assign x e) (Δ.update x d) none Ψ n₁
  | skip {Δ κ n₀} : DExec Δ κ n₀ .skip Δ none [] n₀
  | ret {Δ κ n₀ e d Ψ n₁} : DEval Δ κ n₀ e d Ψ n₁ → DExec Δ κ n₀ (.ret e) Δ (some d) Ψ n₁
  | assert {Δ κ n₀ e d Ψ n₁} : DEval Δ κ n₀ e d Ψ n₁ → DExec Δ κ n₀ (.assert e) Δ none Ψ n₁
  | seq {Δ κ n₀ s₁ s₂ Δ₁ a₁ Ψ₁ n₁ Δ₂ a₂ Ψ₂ n₂ a Ψ' n₃} : DExec Δ κ n₀ s₁ Δ₁ a₁ Ψ₁ n₁ →
      DExec Δ₁ κ n₁ s₂ Δ₂ a₂ Ψ₂ n₂ → RetLe n₂ n₃ Ψ' a₁ a → RetLe n₂ n₃ Ψ' a₂ a →
      Fresh n₂ n₃ Ψ' → RetBelow n₃ a → DExec Δ κ n₀ (.seq s₁ s₂) Δ₂ a (Ψ₁ ++ Ψ₂ ++ Ψ') n₃
  | ite {Δ κ n₀ e s₁ s₂ Δ₁ a₁ Ψ₁ n₁ Δ₂ a₂ Ψ₂ n₂ Δ' a Ψ' n₃} : DExec Δ κ n₀ s₁ Δ₁ a₁ Ψ₁ n₁ →
      DExec Δ κ n₁ s₂ Δ₂ a₂ Ψ₂ n₂ → DEnv.Le n₂ n₃ Ψ' Δ₁ Δ' → DEnv.Le n₂ n₃ Ψ' Δ₂ Δ' →
      RetLe n₂ n₃ Ψ' a₁ a → RetLe n₂ n₃ Ψ' a₂ a → Fresh n₂ n₃ Ψ' → Δ'.Below n₃ →
      RetBelow n₃ a → DExec Δ κ n₀ (.ite e s₁ s₂) Δ' a (Ψ₁ ++ Ψ₂ ++ Ψ') n₃
  /-- D-While with an invariant `Δᵢ`, as A-While. -/
  | whileDo {Δ κ n₀ e s Δᵢ Ψᵢ n₁ Δ' a Ψ n₂} : DEnv.Le n₀ n₁ Ψᵢ Δ Δᵢ → Fresh n₀ n₁ Ψᵢ →
      Δᵢ.Below n₁ → DExec Δᵢ κ n₁ s Δ' a Ψ n₂ → DEnv.Le n₀ n₁ Ψᵢ Δ' Δᵢ →
      DExec Δ κ n₀ (.whileDo e s) Δᵢ a (Ψᵢ ++ Ψ) n₂
  | withCtx {Δ κ n₀ e C Ψ n₁ s Δ' a Ψ' n₂} : DEval Δ (some .real) n₀ e (.ctx C) Ψ n₁ →
      DExec Δ (some C) n₁ s Δ' a Ψ' n₂ → DExec Δ κ n₀ (.withCtx e s) Δ' a (Ψ ++ Ψ') n₂
  | withUnknown {Δ κ n₀ e d Ψ n₁ s Δ' a Ψ' n₂} : DEval Δ (some .real) n₀ e d Ψ n₁ →
      DExec Δ none n₁ s Δ' a Ψ' n₂ → DExec Δ κ n₀ (.withCtx e s) Δ' a (Ψ ++ Ψ') n₂

end

end Fpy.DigitBound
