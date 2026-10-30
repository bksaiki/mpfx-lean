import Fpy.FormatInference.Defs
import Fpy.Ops
import Mathlib.Order.WithBotTop

/-!
# Digit-bound analysis (§4.3, Figure 12)

Digit positions (`lsbOf`, `msbOf`) are extended integers: `0` has `[+∞, −∞]`,
an infinity `[+∞, +∞]`, a value with infinitely many digits lsb `−∞`; NaN lies
in every interval. Symbolic values are terms, matched through `numOfE`. Fresh
variables are numbered from a threaded counter (`n₀ → n₁`), each bounded by one
`Con`, a conjunction of atoms `t ≤ t'`. Transfers are a semantic premise
(`ArithOK`) and joins an order with fresh variables (`DVal.Le`, `DEnv.Le`). The
judgment carries format inference's `Γ` and context for D-Int and D-Fmt.
-/

namespace Fpy.DigitBound

open Mpfx

/-! ## Digit positions -/

/-- Negation of an extended integer. -/
def negE (z : EInt) : EInt :=
  WithBotTop.rec (motive := fun _ => EInt) ⊤ (fun k => ((-k : ℤ) : EInt)) ⊥ z

/-- `c · z` for an extended integer `z`, with `0 · ±∞ = 0`. -/
def smulE (c : ℤ) (z : EInt) : EInt :=
  WithBotTop.rec (motive := fun _ => EInt) (if 0 < c then ⊥ else if c < 0 then ⊤ else 0)
    (fun k => ((c * k : ℤ) : EInt)) (if 0 < c then ⊤ else if c < 0 then ⊥ else 0) z

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

/-- Terms (the paper's `τ`): constants in `ℤ ∪ {±∞}`, integer variables, `+`,
`−`, scaling by an integer `c`, `max` and `min`. -/
inductive Term where
  | const (z : EInt)
  | var (x : ℕ)
  | add (a b : Term)
  | neg (a : Term)
  | smul (c : ℤ) (a : Term)
  | max (a b : Term)
  | min (a b : Term)

def Term.eval (ι : Asgn) : Term → EInt
  | .const z => z
  | .var x => ι x
  | .add a b => a.eval ι + b.eval ι
  | .neg a => negE (a.eval ι)
  | .smul c a => smulE c (a.eval ι)
  | .max a b => Max.max (a.eval ι) (b.eval ι)
  | .min a b => Min.min (a.eval ι) (b.eval ι)

/-- Every variable of `t` is below `n`. -/
def Term.Below (n : ℕ) : Term → Prop
  | .const _ => True
  | .var x => x < n
  | .add a b => a.Below n ∧ b.Below n
  | .neg a => a.Below n
  | .smul _ a => a.Below n
  | .max a b => a.Below n ∧ b.Below n
  | .min a b => a.Below n ∧ b.Below n

theorem Term.Below.mono {n n' : ℕ} (h : n ≤ n') : ∀ {t : Term}, t.Below n → t.Below n'
  | .const _, _ => trivial
  | .var _, hx => lt_of_lt_of_le hx h
  | .add a b, ⟨ha, hb⟩ => ⟨Term.Below.mono (t := a) h ha, Term.Below.mono (t := b) h hb⟩
  | .neg a, ha => Term.Below.mono (t := a) h ha
  | .smul _ a, ha => Term.Below.mono (t := a) h ha
  | .max a b, ⟨ha, hb⟩ => ⟨Term.Below.mono (t := a) h ha, Term.Below.mono (t := b) h hb⟩
  | .min a b, ⟨ha, hb⟩ => ⟨Term.Below.mono (t := a) h ha, Term.Below.mono (t := b) h hb⟩

theorem Term.eval_congr {n : ℕ} {ι ι' : Asgn} (h : ∀ x < n, ι x = ι' x) :
    ∀ {t : Term}, t.Below n → t.eval ι = t.eval ι'
  | .const _, _ => rfl
  | .var x, hx => h x hx
  | .add _ _, ⟨ha, hb⟩ => congrArg₂ (· + ·) (Term.eval_congr h ha) (Term.eval_congr h hb)
  | .neg _, ha => congrArg negE (Term.eval_congr h ha)
  | .smul c _, ha => congrArg (smulE c) (Term.eval_congr h ha)
  | .max _ _, ⟨ha, hb⟩ => congrArg₂ Max.max (Term.eval_congr h ha) (Term.eval_congr h hb)
  | .min _ _, ⟨ha, hb⟩ => congrArg₂ Min.min (Term.eval_congr h ha) (Term.eval_congr h hb)

/-- `ι` and `ι'` agree below `n`. -/
def Agree (n : ℕ) (ι ι' : Asgn) : Prop := ∀ x < n, ι x = ι' x

/-- `ι'` differs from `ι` only on `[n₀, n₁)`. -/
def AgreeOut (n₀ n₁ : ℕ) (ι ι' : Asgn) : Prop := ∀ x, x < n₀ ∨ n₁ ≤ x → ι' x = ι x

/-- An atomic constraint `lhs ≤ rhs` (the paper's `φ`). -/
structure Atom where
  lhs : Term
  rhs : Term

def Atom.Holds (ι : Asgn) (a : Atom) : Prop := a.lhs.eval ι ≤ a.rhs.eval ι

/-- A constraint bounding the fresh variable `head`: a conjunction of atoms over
variables up to `head`, which some value of `head` satisfies whatever the
others are. -/
structure Con where
  head : ℕ
  atoms : List Atom
  below : ∀ a ∈ atoms, a.lhs.Below (head + 1) ∧ a.rhs.Below (head + 1)
  sat : ∀ ι : Asgn, ∃ z, ∀ a ∈ atoms, a.Holds (Function.update ι head z)

def Con.P (c : Con) (ι : Asgn) : Prop := ∀ a ∈ c.atoms, a.Holds ι

theorem Con.dep (c : Con) {ι ι' : Asgn} (h : ∀ x ≤ c.head, ι x = ι' x) (hP : c.P ι) :
    c.P ι' := fun a ha => by
  have h' : ∀ x < c.head + 1, ι x = ι' x := fun x hx => h x (Nat.lt_succ_iff.mp hx)
  have hb := c.below a ha
  have := hP a ha
  rwa [Atom.Holds, Term.eval_congr h' hb.1, Term.eval_congr h' hb.2] at this

/-- `ι ⊨ Ψ`. -/
def Sat (ι : Asgn) (Ψ : List Con) : Prop := ∀ c ∈ Ψ, c.P ι

/-- `Ψ` bounds only variables below `n`. -/
def Before (n : ℕ) (Ψ : List Con) : Prop := ∀ c ∈ Ψ, c.head < n

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

/-- Abstract values: `num l m τ` is `⟨[l, m], τ⟩`, `list d a` a list whose
elements share the abstract value `d`, with the variables from `a` on re-chosen
per element, `other` is `•`, and `ctx C` a symbolic context. -/
inductive DVal where
  | num (l m : Term) (τ : Option Term)
  | list (d : DVal) (a : ℕ)
  | record (fs : List (Label × DVal))
  | other
  | ctx (C : SCtx)

/-- `n` has digits `[l, m]` and value `τ` under `ι`; NaN lies in every interval. -/
def NumIn (ι : Asgn) (l m : Term) (τ : Option Term) (n : Num) : Prop :=
  n = .special .nan ∨
    (lsbOf n = l.eval ι ∧ msbOf n = m.eval ι ∧ ∀ t ∈ τ, n = numOfE (t.eval ι))

mutual

/-- `v ∈ γ_ι(d)` under the constraints `Ψ`. A list `list d a` describes each
element under its own assignment, which satisfies `Ψ` and agrees with `ι` below
`a`. -/
inductive Describes (Ψ : List Con) : Asgn → DVal → Val → Prop
  | num {ι l m τ n} : NumIn ι l m τ n → Describes Ψ ι (.num l m τ) (.num n)
  | list {ι d a vs} : DescribesAll Ψ ι d a vs → Describes Ψ ι (.list d a) (.list vs)
  | record {ι afs fs} : DescribesFields Ψ ι afs fs → Describes Ψ ι (.record afs) (.record fs)
  | bool {ι b} : Describes Ψ ι .other (.bool b)
  | real {ι} : Describes Ψ ι .other .real
  | ctxv {ι fs} : Describes Ψ ι .other (.ctx fs)
  | sctx {ι C v} : C.Admits ι v → Describes Ψ ι (.ctx C) v

inductive DescribesAll (Ψ : List Con) : Asgn → DVal → ℕ → List Val → Prop
  | nil {ι d a} : DescribesAll Ψ ι d a []
  | cons {ι ι' d a v vs} : Agree a ι ι' → Sat ι' Ψ → Describes Ψ ι' d v →
      DescribesAll Ψ ι d a vs → DescribesAll Ψ ι d a (v :: vs)

inductive DescribesFields (Ψ : List Con) : Asgn → List (Label × DVal) → List (Label × Val) → Prop
  | nil {ι} : DescribesFields Ψ ι [] []
  | cons {ι l a v afs fs} : Describes Ψ ι a v → DescribesFields Ψ ι afs fs →
      DescribesFields Ψ ι ((l, a) :: afs) ((l, v) :: fs)

end

mutual

def DVal.Below (n : ℕ) : DVal → Prop
  | .num l m τ => l.Below n ∧ m.Below n ∧ ∀ t ∈ τ, t.Below n
  | .list d a => a ≤ n ∧ DVal.Below n d
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

def DEnv.Holds (Δ : DEnv) (Ψ : List Con) (ι : Asgn) (σ : Store) : Prop :=
  ∀ x d, Δ x = some d → ∃ v, σ x = some v ∧ Describes Ψ ι d v

def DEnv.Below (n : ℕ) (Δ : DEnv) : Prop := ∀ x d, Δ x = some d → d.Below n

def DEnv.single (y : Var) (d : DVal) : DEnv := fun x => if x = y then some d else none

def DEnv.update (Δ : DEnv) (x : Var) (d : DVal) : DEnv := Function.update Δ x (some d)

def CtxBelow (n : ℕ) (κ : Option SCtx) : Prop := ∀ C ∈ κ, C.Below n

/-! ## Joins and transfers -/

/-- `d ⊑ d'` under the constraints `Ψg` so far, with the fresh variables
`[n₀, n₁)` of `d'` bounded by `Ψ`: whatever `d` describes, `d'` describes once
those variables are re-chosen. -/
def DVal.Le (n₀ n₁ : ℕ) (Ψg Ψ : List Con) (d d' : DVal) : Prop :=
  Before n₀ Ψg → ∀ ι v, Sat ι Ψg → Describes Ψg ι d v →
    ∃ ι', AgreeOut n₀ n₁ ι ι' ∧ Sat ι' Ψ ∧ Describes (Ψg ++ Ψ) ι' d' v

def RetLe (n₀ n₁ : ℕ) (Ψg Ψ : List Con) (a a' : Option DVal) : Prop :=
  ∀ d ∈ a, ∃ d' ∈ a', DVal.Le n₀ n₁ Ψg Ψ d d'

def DEnv.Le (n₀ n₁ : ℕ) (Ψg Ψ : List Con) (Δ Δ' : DEnv) : Prop :=
  Before n₀ Ψg → ∀ ι σ, Sat ι Ψg → Δ.Holds Ψg ι σ →
    ∃ ι', AgreeOut n₀ n₁ ι ι' ∧ Sat ι' Ψ ∧ Δ'.Holds (Ψg ++ Ψ) ι' σ

/-- The abstract value `d` of a list's elements, re-chosen from `a` on, copied
to `d'` with fresh variables, under the constraints `Ψg` so far: whatever `d`
describes under an element's assignment, `d'` describes. -/
def DVal.Copy (n₀ n₁ : ℕ) (Ψg Ψ : List Con) (d : DVal) (a : ℕ) (d' : DVal) : Prop :=
  Before n₀ Ψg → ∀ ι ι₀ v, Sat ι Ψg → Agree a ι ι₀ → Sat ι₀ Ψg → Describes Ψg ι₀ d v →
    ∃ ι', AgreeOut n₀ n₁ ι ι' ∧ Sat ι' Ψ ∧ Describes (Ψg ++ Ψ) ι' d' v

variable {decode : List (Label × Val) → Option RoundCtx}

variable (decode) in
/-- `rnd♮_κ(op♮(Is))`: the interval `[l, m]`, with fresh variables `[n₀, n₁)`
bounded by `Ψ`, bounds `op` on values with digits `Is`, rounded under any
context `κ` admits. -/
def ArithOK (κ : Option SCtx) (op : ArithOp) (Is : List (Term × Term × Option Term))
    (n₀ n₁ : ℕ) (Ψ : List Con) (l m : Term) : Prop :=
  ∀ ι ns u C r, List.Forall₂ (fun (I : Term × Term × Option Term) n => NumIn ι I.1 I.2.1 I.2.2 n)
    Is ns →
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
  atoms := if ge then [⟨τ₁, .var v⟩, ⟨τ₂, .var v⟩] else [⟨.var v, τ₁⟩, ⟨.var v, τ₂⟩]
  below e ha := by
    have := h₁.mono (Nat.le_succ v)
    have := h₂.mono (Nat.le_succ v)
    have : (Term.var v).Below (v + 1) := Nat.lt_succ_self v
    cases ge <;> simp only [Bool.false_eq_true, if_true, if_false, List.mem_cons,
      List.not_mem_nil, or_false] at ha <;> rcases ha with rfl | rfl <;>
      exact ⟨by assumption, by assumption⟩
  sat ι := ⟨if ge then ⊤ else ⊥, by cases ge <;> simp [Atom.Holds, Term.eval]⟩

theorem Con.P_ext {v : ℕ} {ge : Bool} {τ₁ τ₂ : Term} {h₁ : τ₁.Below v} {h₂ : τ₂.Below v}
    {ι : Asgn} : (Con.ext v ge τ₁ τ₂ h₁ h₂).P ι ↔
      if ge then τ₁.eval ι ≤ ι v ∧ τ₂.eval ι ≤ ι v else ι v ≤ τ₁.eval ι ∧ ι v ≤ τ₂.eval ι := by
  cases ge <;> simp [Con.P, Con.ext, Atom.Holds, Term.eval]

/-- `t ≤ v`. -/
def Con.lower (v : ℕ) (t : Term) (h : t.Below v) : Con where
  head := v
  atoms := [⟨t, .var v⟩]
  below e ha := by
    obtain rfl := List.mem_singleton.mp ha
    exact ⟨h.mono (Nat.le_succ v), Nat.lt_succ_self v⟩
  sat _ := ⟨⊤, by simp [Atom.Holds, Term.eval]⟩

theorem Con.P_lower {v : ℕ} {t : Term} {h : t.Below v} {ι : Asgn} :
    (Con.lower v t h).P ι ↔ t.eval ι ≤ ι v := by
  simp [Con.P, Con.lower, Atom.Holds, Term.eval]

/-- `v ≤ t`. -/
def Con.upper (v : ℕ) (t : Term) (h : t.Below v) : Con where
  head := v
  atoms := [⟨.var v, t⟩]
  below e ha := by
    obtain rfl := List.mem_singleton.mp ha
    exact ⟨Nat.lt_succ_self v, h.mono (Nat.le_succ v)⟩
  sat _ := ⟨⊥, by simp [Atom.Holds, Term.eval]⟩

theorem Con.P_upper {v : ℕ} {t : Term} {h : t.Below v} {ι : Asgn} :
    (Con.upper v t h).P ι ↔ ι v ≤ t.eval ι := by
  simp [Con.P, Con.upper, Atom.Holds, Term.eval]

/-- The constraints of a fresh interval `[n + 1, n]`: `Lo ≤ n + 1`, `n ≤ Hi`. -/
def bounds (n : ℕ) (Lo Hi : Term) (hLo : Lo.Below (n + 1)) (hHi : Hi.Below n) : List Con :=
  [Con.upper n Hi hHi, Con.lower (n + 1) Lo hLo]

/-- `a ≤ v ≤ b`. -/
def Con.between (v : ℕ) (a b : ℤ) (h : a ≤ b) : Con where
  head := v
  atoms := [⟨.const a, .var v⟩, ⟨.var v, .const b⟩]
  below e ha := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact ⟨trivial, Nat.lt_succ_self v⟩
    · exact ⟨Nat.lt_succ_self v, trivial⟩
  sat _ := ⟨a, by simpa [Atom.Holds, Term.eval] using h⟩

theorem Con.P_between {v : ℕ} {a b : ℤ} {h : a ≤ b} {ι : Asgn} :
    (Con.between v a b h).P ι ↔ (a : EInt) ≤ ι v ∧ ι v ≤ b := by
  simp [Con.P, Con.between, Atom.Holds, Term.eval]

local notation "nan" => (WithSpecial.special Special.nan : Num)

/-- `w` has digits in `[lo, hi]`; NaN lies in every interval. -/
def InRange (lo hi : EInt) (w : Num) : Prop := w = nan ∨ (lo ≤ lsbOf w ∧ msbOf w ≤ hi)

/-- The context a format-inference abstract value determines, if known. -/
def knownCtx {D : FormatDomain} : AVal D → Option Val
  | .known C => some C
  | _ => none

/-- `Δ` without the variables `X`. -/
def DEnv.without (Δ : DEnv) (X : List Var) : DEnv := fun x => if x ∈ X then none else Δ x

/-- D-While's premise: every store in `Γᵢ` whose variables outside `X` are
described by `Δ` is described by `Δᵢ`, once the fresh variables `[n₀, n₁)`
bounded by `Ψ` are re-chosen. -/
def Covers {D : FormatDomain} (n₀ n₁ : ℕ) (Ψg Ψ : List Con) (X : List Var) (Γᵢ : AEnv D)
    (Δ Δᵢ : DEnv) : Prop :=
  Before n₀ Ψg → ∀ ι σ, Sat ι Ψg → Γᵢ.Holds σ → (Δ.without X).Holds Ψg ι σ →
    ∃ ι', AgreeOut n₀ n₁ ι ι' ∧ Sat ι' Ψ ∧ Δᵢ.Holds (Ψg ++ Ψ) ι' σ

/-! ## The analysis -/

variable (decode) (Φ : Program (fpy decode)) {D : FormatDomain} (A : Analysis (fpy decode) D)

mutual

/-- `Δ, κ ⊢♮ e : d` after the constraints `Ψg`, with fresh variables `[n₀, n₁)`
bounded by `Ψ`. Format inference's environment `Γ` and context `χ` at `e` give
`fmt(e)` (D-Int, D-Fmt). -/
inductive DEval : DEnv → AEnv D → Option SCtx → Option Val → List Con → ℕ → Expr (fpy decode) →
    DVal → List Con → ℕ → Prop
  | const {Δ Γ κ χ Ψg n₀ n τ} : (∀ t ∈ τ, ∃ z, t = .const z ∧ n = numOfE z) →
      DEval Δ Γ κ χ Ψg n₀ (.num n) (.num (.const (lsbOf n)) (.const (msbOf n)) τ) [] n₀
  | bool {Δ Γ κ χ Ψg n₀ b} : DEval Δ Γ κ χ Ψg n₀ (.bool b) .other [] n₀
  | real {Δ Γ κ χ Ψg n₀} : DEval Δ Γ κ χ Ψg n₀ .real (.ctx .real) [] n₀
  | var {Δ Γ κ χ Ψg n₀ x d} : Δ x = some d → DEval Δ Γ κ χ Ψg n₀ (.var x) d [] n₀
  | list {Δ Γ κ χ Ψg n₀ es ds Ψ n₁ d Ψ' n₂} : DEvalList Δ Γ κ χ Ψg n₀ es ds Ψ n₁ →
      (∀ d' ∈ ds, DVal.Le n₁ n₂ (Ψg ++ Ψ) Ψ' d' d) → Fresh n₁ n₂ Ψ' → d.Below n₂ →
      DEval Δ Γ κ χ Ψg n₀ (.list es) (.list d n₁) (Ψ ++ Ψ') n₂
  | index {Δ Γ κ χ Ψg n₀ e₁ e₂ d a Ψ₁ n₁ d₂ Ψ₂ n₂ d' Ψ' n₃} :
      DEval Δ Γ κ χ Ψg n₀ e₁ (.list d a) Ψ₁ n₁ → DEval Δ Γ κ χ (Ψg ++ Ψ₁) n₁ e₂ d₂ Ψ₂ n₂ →
      DVal.Copy n₂ n₃ (Ψg ++ Ψ₁ ++ Ψ₂) Ψ' d a d' → Fresh n₂ n₃ Ψ' → d'.Below n₃ →
      DEval Δ Γ κ χ Ψg n₀ (.index e₁ e₂) d' (Ψ₁ ++ Ψ₂ ++ Ψ') n₃
  | record {Δ Γ κ χ Ψg n₀ fs afs Ψ n₁} : DEvalFields Δ Γ κ χ Ψg n₀ fs afs Ψ n₁ →
      DEval Δ Γ κ χ Ψg n₀ (.record fs) (.record afs) Ψ n₁
  | proj {Δ Γ κ χ Ψg n₀ e afs Ψ n₁ l d} : DEval Δ Γ κ χ Ψg n₀ e (.record afs) Ψ n₁ →
      afs.lookup l = some d → DEval Δ Γ κ χ Ψg n₀ (.proj e l) d Ψ n₁
  | ctx {Δ Γ κ χ Ψg n₀ e d Ψ n₁} : DEval Δ Γ κ χ Ψg n₀ e d Ψ n₁ →
      DEval Δ Γ κ χ Ψg n₀ (.ctx e) ((ctxOf d).elim .other .ctx) Ψ n₁
  | arith {Δ Γ κ χ Ψg n₀ op es Ψ n₁ Ψ' n₂ l m} {Is : List (Term × Term × Option Term)} :
      DEvalList Δ Γ κ χ Ψg n₀ es (Is.map fun I => .num I.1 I.2.1 I.2.2) Ψ n₁ →
      ArithOK decode κ op Is n₁ n₂ Ψ' l m → Fresh n₁ n₂ Ψ' →
      l.Below n₂ → m.Below n₂ → DEval Δ Γ κ χ Ψg n₀ (.arith op es) (.num l m none) (Ψ ++ Ψ') n₂
  /-- D-Linear, under `R`. -/
  | linear {Δ Γ χ Ψg n₀ op e₁ e₂ l₁ m₁ τ₁ l₂ m₂ τ₂ Ψ n₁ Ψ' n₂ l m}
      (hop : op = .add ∨ op = .sub) :
      DEvalList Δ Γ (some .real) χ Ψg n₀ [e₁, e₂]
        [.num l₁ m₁ (some τ₁), .num l₂ m₂ (some τ₂)] Ψ n₁ →
      ArithOK decode (some .real) op [(l₁, m₁, some τ₁), (l₂, m₂, some τ₂)] n₁ n₂ Ψ' l m →
      Fresh n₁ n₂ Ψ' → l.Below n₂ → m.Below n₂ →
      DEval Δ Γ (some .real) χ Ψg n₀ (.arith op [e₁, e₂])
        (.num l m (some (if op = .add then .add τ₁ τ₂ else .add τ₁ (.neg τ₂)))) (Ψ ++ Ψ') n₂
  /-- D-Neg, under `R`. -/
  | neg {Δ Γ χ Ψg n₀ e l₁ m₁ τ Ψ n₁ Ψ' n₂ l m} :
      DEvalList Δ Γ (some .real) χ Ψg n₀ [e] [.num l₁ m₁ (some τ)] Ψ n₁ →
      ArithOK decode (some .real) .neg [(l₁, m₁, some τ)] n₁ n₂ Ψ' l m → Fresh n₁ n₂ Ψ' →
      l.Below n₂ → m.Below n₂ →
      DEval Δ Γ (some .real) χ Ψg n₀ (.arith .neg [e]) (.num l m (some (.neg τ))) (Ψ ++ Ψ') n₂
  /-- D-Logb, under `R`: the value is the argument's most significant digit. -/
  | logb {Δ Γ χ Ψg n₀ e l₁ m₁ τ Ψ n₁ Ψ' n₂ l m} :
      DEvalList Δ Γ (some .real) χ Ψg n₀ [e] [.num l₁ m₁ τ] Ψ n₁ →
      ArithOK decode (some .real) .logb [(l₁, m₁, τ)] n₁ n₂ Ψ' l m → Fresh n₁ n₂ Ψ' →
      l.Below n₂ → m.Below n₂ →
      DEval Δ Γ (some .real) χ Ψg n₀ (.arith .logb [e]) (.num l m (some m₁)) (Ψ ++ Ψ') n₂
  /-- D-Max (`ge = true`, `op = max`) and D-Min, under `R`: a fresh `val(e)`
  bounded by the arguments' values. -/
  | ext {Δ Γ χ Ψg n₀ op ge e₁ e₂ l₁ m₁ τ₁ l₂ m₂ τ₂ Ψ n₁ Ψ' n₂ l m}
      (hop : op = (if ge then .max else .min)) (h₁ : τ₁.Below n₂) (h₂ : τ₂.Below n₂) :
      DEvalList Δ Γ (some .real) χ Ψg n₀ [e₁, e₂]
        [.num l₁ m₁ (some τ₁), .num l₂ m₂ (some τ₂)] Ψ n₁ →
      ArithOK decode (some .real) op [(l₁, m₁, some τ₁), (l₂, m₂, some τ₂)] n₁ n₂ Ψ' l m →
      Fresh n₁ n₂ Ψ' → l.Below n₂ → m.Below n₂ →
      DEval Δ Γ (some .real) χ Ψg n₀ (.arith op [e₁, e₂]) (.num l m (some (.var n₂)))
        (Ψ ++ Ψ' ++ [Con.ext n₂ ge τ₁ τ₂ h₁ h₂]) (n₂ + 1)
  | exact {Δ Γ κ χ Ψg n₀ op es ds Ψ n₁} : DEvalList Δ Γ κ χ Ψg n₀ es ds Ψ n₁ → op ≠ .len →
      DEval Δ Γ κ χ Ψg n₀ (.exact op es) .other Ψ n₁
  | len {Δ Γ κ χ Ψg n₀ es ds Ψ n₁} : DEvalList Δ Γ κ χ Ψg n₀ es ds Ψ n₁ →
      DEval Δ Γ κ χ Ψg n₀ (.exact .len es) (.num (.var n₁) (.var (n₁ + 1)) none) Ψ (n₁ + 2)
  | call {Δ Γ κ χ Ψg n₀ f e y s d a Ψ n₁ Δ' d' Ψ' n₂} : Φ f = some (y, s) →
      DEval Δ Γ κ χ Ψg n₀ e d Ψ n₁ → AEval A Φ Γ χ e a →
      DExec (.single y d) (.single y a) κ χ (Ψg ++ Ψ) n₁ s Δ' (some d') Ψ' n₂ →
      DEval Δ Γ κ χ Ψg n₀ (.call f e) d' (Ψ ++ Ψ') n₂
  /-- D-Int: `fmt(e) ⊆ ℤ ∩ [a, b]` gives `e` a fresh value `a ≤ val(e) ≤ b`. -/
  | int {Δ Γ κ χ Ψg n₀ e l m Ψ n₁ a₀ a b} (hab : a ≤ b) :
      DEval Δ Γ κ χ Ψg n₀ e (.num l m none) Ψ n₁ → AEval A Φ Γ χ e a₀ →
      (∀ w, Fpy.Describes a₀ (.num w) → ∃ k : ℤ, w = .finite k ∧ a ≤ k ∧ k ≤ b) →
      DEval Δ Γ κ χ Ψg n₀ e (.num l m (some (.var n₁))) (Ψ ++ [Con.between n₁ a b hab]) (n₁ + 1)
  /-- D-Fmt: `e`'s interval lies within the digits `[lo, hi]` of `fmt(e)`. -/
  | fmt {Δ Γ κ χ Ψg n₀ e l m τ Ψ n₁ a₀ lo hi} : DEval Δ Γ κ χ Ψg n₀ e (.num l m τ) Ψ n₁ →
      (hl : l.Below n₁) → (hm : m.Below n₁) → AEval A Φ Γ χ e a₀ →
      (∀ w, Fpy.Describes a₀ (.num w) → InRange lo hi w) →
      DEval Δ Γ κ χ Ψg n₀ e (.num (.var (n₁ + 1)) (.var n₁) τ)
        (Ψ ++ bounds n₁ (.max l (.const lo)) (.min m (.const hi))
          ⟨hl.mono (Nat.le_succ n₁), trivial⟩ ⟨hm, trivial⟩) (n₁ + 2)

inductive DEvalList : DEnv → AEnv D → Option SCtx → Option Val → List Con → ℕ →
    List (Expr (fpy decode)) → List DVal → List Con → ℕ → Prop
  | nil {Δ Γ κ χ Ψg n₀} : DEvalList Δ Γ κ χ Ψg n₀ [] [] [] n₀
  | cons {Δ Γ κ χ Ψg n₀ e es d ds Ψ n₁ Ψ' n₂} : DEval Δ Γ κ χ Ψg n₀ e d Ψ n₁ →
      DEvalList Δ Γ κ χ (Ψg ++ Ψ) n₁ es ds Ψ' n₂ →
      DEvalList Δ Γ κ χ Ψg n₀ (e :: es) (d :: ds) (Ψ ++ Ψ') n₂

inductive DEvalFields : DEnv → AEnv D → Option SCtx → Option Val → List Con → ℕ →
    List (Label × Expr (fpy decode)) → List (Label × DVal) → List Con → ℕ → Prop
  | nil {Δ Γ κ χ Ψg n₀} : DEvalFields Δ Γ κ χ Ψg n₀ [] [] [] n₀
  | cons {Δ Γ κ χ Ψg n₀ l e fs d afs Ψ n₁ Ψ' n₂} : DEval Δ Γ κ χ Ψg n₀ e d Ψ n₁ →
      DEvalFields Δ Γ κ χ (Ψg ++ Ψ) n₁ fs afs Ψ' n₂ →
      DEvalFields Δ Γ κ χ Ψg n₀ ((l, e) :: fs) ((l, d) :: afs) (Ψ ++ Ψ') n₂

/-- `Δ, κ ⊢♮ s : ⟨Δ', a⟩` after the constraints `Ψg`, with fresh variables
`[n₀, n₁)` bounded by `Ψ`. `Γ` and `χ` follow format inference: through `s₁`
in D-Seq, refined by the guard in D-If, by an invariant in D-While, and by the
context in D-Context. -/
inductive DExec : DEnv → AEnv D → Option SCtx → Option Val → List Con → ℕ → Stmt (fpy decode) →
    DEnv → Option DVal → List Con → ℕ → Prop
  | assign {Δ Γ κ χ Ψg n₀ x e d Ψ n₁} : DEval Δ Γ κ χ Ψg n₀ e d Ψ n₁ →
      DExec Δ Γ κ χ Ψg n₀ (.assign x e) (Δ.update x d) none Ψ n₁
  | skip {Δ Γ κ χ Ψg n₀} : DExec Δ Γ κ χ Ψg n₀ .skip Δ none [] n₀
  | ret {Δ Γ κ χ Ψg n₀ e d Ψ n₁} : DEval Δ Γ κ χ Ψg n₀ e d Ψ n₁ →
      DExec Δ Γ κ χ Ψg n₀ (.ret e) Δ (some d) Ψ n₁
  | assert {Δ Γ κ χ Ψg n₀ e d Ψ n₁} : DEval Δ Γ κ χ Ψg n₀ e d Ψ n₁ →
      DExec Δ Γ κ χ Ψg n₀ (.assert e) Δ none Ψ n₁
  | seq {Δ Γ κ χ Ψg n₀ s₁ s₂ Δ₁ a₁ Ψ₁ n₁ Γ₁ b₁ Δ₂ a₂ Ψ₂ n₂ a Ψ' n₃} :
      DExec Δ Γ κ χ Ψg n₀ s₁ Δ₁ a₁ Ψ₁ n₁ → AExec A Φ Γ χ s₁ Γ₁ b₁ →
      DExec Δ₁ Γ₁ κ χ (Ψg ++ Ψ₁) n₁ s₂ Δ₂ a₂ Ψ₂ n₂ →
      RetLe n₂ n₃ (Ψg ++ Ψ₁ ++ Ψ₂) Ψ' a₁ a → RetLe n₂ n₃ (Ψg ++ Ψ₁ ++ Ψ₂) Ψ' a₂ a →
      Fresh n₂ n₃ Ψ' → RetBelow n₃ a →
      DExec Δ Γ κ χ Ψg n₀ (.seq s₁ s₂) Δ₂ a (Ψ₁ ++ Ψ₂ ++ Ψ') n₃
  | ite {Δ Γ κ χ Ψg n₀ e s₁ s₂ Δ₁ a₁ Ψ₁ n₁ Δ₂ a₂ Ψ₂ n₂ Δ' a Ψ' n₃} :
      DExec Δ (A.refine χ e true Γ) κ χ Ψg n₀ s₁ Δ₁ a₁ Ψ₁ n₁ →
      DExec Δ (A.refine χ e false Γ) κ χ (Ψg ++ Ψ₁) n₁ s₂ Δ₂ a₂ Ψ₂ n₂ →
      DEnv.Le n₂ n₃ (Ψg ++ Ψ₁ ++ Ψ₂) Ψ' Δ₁ Δ' → DEnv.Le n₂ n₃ (Ψg ++ Ψ₁ ++ Ψ₂) Ψ' Δ₂ Δ' →
      RetLe n₂ n₃ (Ψg ++ Ψ₁ ++ Ψ₂) Ψ' a₁ a → RetLe n₂ n₃ (Ψg ++ Ψ₁ ++ Ψ₂) Ψ' a₂ a →
      Fresh n₂ n₃ Ψ' → Δ'.Below n₃ → RetBelow n₃ a →
      DExec Δ Γ κ χ Ψg n₀ (.ite e s₁ s₂) Δ' a (Ψ₁ ++ Ψ₂ ++ Ψ') n₃
  /-- D-While: each iteration starts from `Δᵢ`, which format inference's
  invariant `Γᵢ` covers (`Covers`); no back edge. -/
  | whileDo {Δ Γ κ χ Ψg n₀ e s Δᵢ Ψᵢ n₁ Γᵢ Γ' b Δ' a Ψ n₂} :
      Covers n₀ n₁ Ψg Ψᵢ s.assigned Γᵢ Δ Δᵢ → Fresh n₀ n₁ Ψᵢ → Δᵢ.Below n₁ → Γ.Le Γᵢ →
      AExec A Φ (A.refine χ e true Γᵢ) χ s Γ' b → Γ'.Le Γᵢ →
      DExec Δᵢ (A.refine χ e true Γᵢ) κ χ (Ψg ++ Ψᵢ) n₁ s Δ' a Ψ n₂ →
      DExec Δ Γ κ χ Ψg n₀ (.whileDo e s) Δᵢ a (Ψᵢ ++ Ψ) n₂
  | withCtx {Δ Γ κ χ Ψg n₀ e C Ψ n₁ a₀ s Δ' a Ψ' n₂} :
      DEval Δ Γ (some .real) (some .real) Ψg n₀ e (.ctx C) Ψ n₁ →
      AEval A Φ Γ (some .real) e a₀ →
      DExec Δ Γ (some C) (knownCtx a₀) (Ψg ++ Ψ) n₁ s Δ' a Ψ' n₂ →
      DExec Δ Γ κ χ Ψg n₀ (.withCtx e s) Δ' a (Ψ ++ Ψ') n₂
  | withUnknown {Δ Γ κ χ Ψg n₀ e d Ψ n₁ a₀ s Δ' a Ψ' n₂} :
      DEval Δ Γ (some .real) (some .real) Ψg n₀ e d Ψ n₁ →
      AEval A Φ Γ (some .real) e a₀ → DExec Δ Γ none (knownCtx a₀) (Ψg ++ Ψ) n₁ s Δ' a Ψ' n₂ →
      DExec Δ Γ κ χ Ψg n₀ (.withCtx e s) Δ' a (Ψ ++ Ψ') n₂

end

end Fpy.DigitBound
