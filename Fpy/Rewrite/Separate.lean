import Fpy.Rewrite
import Fpy.FormatInference.Domain
import Mpfx.DoubleRounding.Special

/-!
# Separating arithmetic from rounding (§5.1)

The rewrites of §5.1 on an operation `x = op(y₁, …, yₖ)` over variables:

* **Elim**: `[C] x = op(y⃗) ⇝ with R in x = op(y⃗)` if `op♯(fmt(y⃗)) ⊆ F_C`;
* **Insert**: `[R] x = op(y⃗) ⇝ with C' in x = op(y⃗)` if `op♯(fmt(y⃗)) ⊆ F_{C'}`;
* **Split**: `[C] x = op(y⃗) ⇝ with C' in t = op(y⃗); x = round(t)` if
  `C(C'(v)) = C(v)` for every `v`;
* **SplitOp**: the same, if each `fmt(yᵢ) ⊆ F_C` and `C(C'(v)) = C(v)` for
  every `v = op(u⃗)` with `uᵢ ∈ F_C`.

Each is an `Equiv` (`equiv_elim`, `equiv_insert`, `equiv_split`,
`equiv_splitOp`), from two cores with semantic conditions (`equiv_reround`,
`equiv_split_of`). `C'` is written by any expression that denotes it.

For FPy's contexts, `RoundCtx.round_round` turns each total double-rounding
rule (`rndRTO_RN`, …) into Split's condition, and `splitOp_add`, `splitOp_mul`,
`splitOp_div` and `splitOp_sqrt` turn Roux's rules (`rndAdd`, `rndMul_*`,
`rndDiv_*`, `rndSqrt_*`) into SplitOp's.
-/

namespace Fpy

open Mpfx

variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}

/-- `c` evaluates under `R` in `σ` to `C` and nothing else. -/
def DenotesAt (Φ : Program L) (σ : Store) (c : Expr L) (C : Val) : Prop :=
  ∀ v, Eval Φ σ .real c v ↔ v = C

/-- `c` evaluates under `R`, in every store, to `C` and nothing else. -/
def Denotes (Φ : Program L) (c : Expr L) (C : Val) : Prop := ∀ σ, DenotesAt Φ σ c C

theorem denotes_real : Denotes Φ .real .real :=
  fun _ _ => ⟨fun h => by cases h; rfl, fun h => by subst h; exact .real⟩

theorem evalList_vars {σ : Store} {C : Val} : ∀ {ys : List Var} {vs : List Val},
    EvalList Φ σ C (ys.map .var) vs ↔ List.Forall₂ (fun y v => σ y = some v) ys vs
  | [], _ => ⟨fun h => by cases h; exact .nil, fun h => by cases h; exact .nil⟩
  | _ :: _, _ =>
    ⟨fun h => by
      cases h with
      | cons hv hs => cases hv with
        | var hx => exact .cons hx (evalList_vars.mp hs),
     fun h => by
      cases h with
      | cons hx hs => exact .cons (.var hx) (evalList_vars.mpr hs)⟩

/-- The numbers the variables `ys` hold in `σ`. -/
theorem forall₂_of_evalList {σ : Store} {C : Val} {ys : List Var} {ns : List Num}
    (h : EvalList Φ σ C (ys.map .var) (ns.map .num)) :
    List.Forall₂ (fun y n => σ y = some (.num n)) ys ns :=
  (List.forall₂_map_right_iff (R := fun y v => σ y = some v) (f := Val.num)).mp (evalList_vars.mp h)

theorem AEnv.Holds.describes {Γ : AEnv D} {σ : Store} (hΓ : Γ.Holds σ) {ys : List Var}
    {as : List (AVal D)} {ns : List Num} (has : List.Forall₂ (fun y a => Γ y = some a) ys as)
    (hns : List.Forall₂ (fun y n => σ y = some (.num n)) ys ns) :
    List.Forall₂ (fun a n => Describes a (.num n)) as ns := by
  induction has generalizing ns with
  | nil => cases hns; exact .nil
  | cons ha _ ih =>
    cases hns with
    | cons hn hns =>
      obtain ⟨v, hv, hd⟩ := hΓ _ _ ha
      exact .cons ((Option.some.inj (hv.symm.trans hn)) ▸ hd) (ih hns)

theorem forall₂_mem_toFmt {as : List (AVal D)} {ns : List Num}
    (h : List.Forall₂ (fun a n => Describes a (.num n)) as ns) :
    List.Forall₂ (fun n F => n ∈ D.γ F) ns (as.map AVal.toFmt) :=
  List.forall₂_map_right_iff.mpr (h.imp fun _ _ h => h.mem_toFmt).flip

theorem mem_of_forall₂ {S : Set Num} : ∀ {as : List (AVal D)} {ns : List Num},
    List.Forall₂ (fun a n => Describes a (.num n)) as ns → (∀ a ∈ as, D.γ a.toFmt ⊆ S) →
      ∀ u ∈ ns, u ∈ S
  | _, _, .nil, _, _, hu => absurd hu List.not_mem_nil
  | _, _, .cons hd tl, hS, _, hu => (List.mem_cons.mp hu).elim
      (fun h => h ▸ hS _ (List.mem_cons_self ..) hd.mem_toFmt)
      (mem_of_forall₂ tl (fun a ha => hS a (List.mem_cons_of_mem _ ha)) _)

/-! ## Rounding under another context -/

/-- Rounding `op(y⃗)` under `C'` (denoted by `c`) instead of `C`: correct when
both round each exact result the same way, for the values of `y⃗` in `Γ`. -/
theorem equiv_reround {Γ : AEnv D} {C C' : Val} {r r' : Num → Num} {c : Expr L} {x : Var}
    {op : L.ArithOp} {ys : List Var} (hc : Denotes Φ c C') (hr : C.rnd L = some r)
    (hr' : C'.rnd L = some r')
    (h : ∀ σ ns n, Γ.Holds σ → List.Forall₂ (fun y n => σ y = some (.num n)) ys ns →
      L.arith op ns = some n → r n = r' n) :
    Equiv Φ X Γ (some C) (.assign x (.arith op (ys.map .var)))
      (.withCtx c (.assign x (.arith op (ys.map .var)))) := by
  intro σ C₀ hΓ hκ
  obtain rfl := hκ C rfl
  refine ⟨fun o hs => ?_, fun o hs => ?_⟩
  · cases hs with
    | assign he =>
      cases he with
      | arith hl hop hr₀ =>
        obtain rfl := Option.some.inj (hr₀.symm.trans hr)
        refine ⟨_, .withCtx ((hc σ C').mpr rfl)
          (.assign (.arith (evalList_vars.mpr (evalList_vars.mp hl)) hop hr')), ?_⟩
        rw [h σ _ _ hΓ (forall₂_of_evalList hl) hop]
        exact Store.Agree.refl _
  · cases hs with
    | withCtx hc' hs =>
      obtain rfl := (hc σ _).mp hc'
      cases hs with
      | assign he =>
        cases he with
        | arith hl hop hr₀ =>
          obtain rfl := Option.some.inj (hr₀.symm.trans hr')
          refine ⟨_, .assign (.arith (evalList_vars.mpr (evalList_vars.mp hl)) hop hr), ?_⟩
          rw [h σ _ _ hΓ (forall₂_of_evalList hl) hop]
          exact Store.Agree.refl _

variable {A : Analysis L D}

/-- **Elim**: `[C] x = op(y⃗) ⇝ with R in x = op(y⃗)` if `op♯(fmt(y⃗)) ⊆ F_C`. -/
theorem equiv_elim (hA : A.Sound Φ) {Γ : AEnv D} {C : Val} {r : Num → Num} {FC : D.Fmt}
    {x : Var} {op : L.ArithOp} {ys : List Var} {as : List (AVal D)}
    (hr : C.rnd L = some r) (hFC : A.ctxFmt C = some FC)
    (has : List.Forall₂ (fun y a => Γ y = some a) ys as)
    (hsub : D.γ (A.arith op (as.map AVal.toFmt)) ⊆ D.γ FC) :
    Equiv Φ X Γ (some C) (.assign x (.arith op (ys.map .var)))
      (.withCtx .real (.assign x (.arith op (ys.map .var)))) :=
  equiv_reround denotes_real hr rfl fun _ _ n hΓ hns hop =>
    (hA.ctxFmt hFC hr).2 n (hsub (hA.arith (forall₂_mem_toFmt (hΓ.describes has hns)) hop))

/-- **Insert**: `[R] x = op(y⃗) ⇝ with C' in x = op(y⃗)` if `op♯(fmt(y⃗)) ⊆ F_{C'}`. -/
theorem equiv_insert (hA : A.Sound Φ) {Γ : AEnv D} {C' : Val} {r' : Num → Num} {FC : D.Fmt}
    {c : Expr L} {x : Var} {op : L.ArithOp} {ys : List Var} {as : List (AVal D)}
    (hc : Denotes Φ c C') (hr' : C'.rnd L = some r') (hFC : A.ctxFmt C' = some FC)
    (has : List.Forall₂ (fun y a => Γ y = some a) ys as)
    (hsub : D.γ (A.arith op (as.map AVal.toFmt)) ⊆ D.γ FC) :
    Equiv Φ X Γ (some .real) (.assign x (.arith op (ys.map .var)))
      (.withCtx c (.assign x (.arith op (ys.map .var)))) :=
  equiv_reround hc rfl hr' fun _ _ n hΓ hns hop =>
    ((hA.ctxFmt hFC hr').2 n (hsub (hA.arith (forall₂_mem_toFmt (hΓ.describes has hns)) hop))).symm

/-! ## Splitting a rounding -/

/-- Rounding `op(y⃗)` under `C'` (denoted by `c`) into a fresh `t`, then
`round(t)` under `C`: correct when `C ∘ C'` agrees with `C` on each exact result,
for the values of `y⃗` in `Γ`. `rd` is any operator computing the identity. -/
theorem equiv_split_of {Γ : AEnv D} {C C' : Val} {r r' : Num → Num} {c : Expr L} {x t : Var}
    {op rd : L.ArithOp} {ys : List Var} (hc : Denotes Φ c C') (hr : C.rnd L = some r)
    (hr' : C'.rnd L = some r') (hrd : ∀ u, L.arith rd [u] = some u)
    (h : ∀ σ ns n, Γ.Holds σ → List.Forall₂ (fun y n => σ y = some (.num n)) ys ns →
      L.arith op ns = some n → r (r' n) = r n) :
    Equiv Φ {t} Γ (some C) (.assign x (.arith op (ys.map .var)))
      (.seq (.withCtx c (.assign t (.arith op (ys.map .var))))
        (.assign x (.arith rd [.var t]))) := by
  intro σ C₀ hΓ hκ
  obtain rfl := hκ C rfl
  refine ⟨fun o hs => ?_, fun o hs => ?_⟩
  · cases hs with
    | assign he =>
      cases he with
      | @arith _ _ _ _ _ n _ hl hop hr₀ =>
        obtain rfl := Option.some.inj (hr₀.symm.trans hr)
        refine ⟨_, .seqNormal (.withCtx ((hc σ C').mpr rfl)
          (.assign (.arith (evalList_vars.mpr (evalList_vars.mp hl)) hop hr')))
          (.assign (.arith (ns := [r' n]) (.cons (.var (by simp [Store.update])) .nil) (hrd _) hr)),
          ?_⟩
        rw [h σ _ _ hΓ (forall₂_of_evalList hl) hop]
        exact Store.Agree.update_fresh _ _ _
  · cases hs with
    | seqRet h₁ => cases h₁ with | withCtx _ h₁ => cases h₁
    | seqNormal h₁ h₂ =>
      cases h₁ with
      | withCtx hc' h₁ =>
        obtain rfl := (hc σ _).mp hc'
        cases h₁ with
        | assign he =>
          cases he with
          | @arith _ _ _ _ _ n _ hl hop hr₀ =>
            obtain rfl := Option.some.inj (hr₀.symm.trans hr')
            cases h₂ with
            | assign he₂ =>
              cases he₂ with
              | @arith _ _ _ _ ns₂ m _ hl₂ hop₂ hr₂ =>
                obtain rfl := Option.some.inj (hr₂.symm.trans hr)
                rcases ns₂ with _ | ⟨u, _ | ⟨_, _⟩⟩
                · cases hl₂
                · cases hl₂ with
                  | cons hv _ =>
                    cases hv with
                    | var hx =>
                      simp only [Store.update, Function.update_self, Option.some.injEq,
                        Val.num.injEq] at hx
                      subst hx
                      obtain rfl := Option.some.inj (hop₂.symm.trans (hrd _))
                      refine ⟨_, .assign (.arith (evalList_vars.mpr (evalList_vars.mp hl)) hop hr),
                        ?_⟩
                      rw [h σ _ _ hΓ (forall₂_of_evalList hl) hop]
                      exact Store.Agree.update_fresh _ _ _
                · cases hl₂ with | cons _ hl => cases hl

/-- **Split**: `[C] x = op(y⃗) ⇝ with C' in t = op(y⃗); x = round(t)` if
`C(C'(v)) = C(v)` for every `v`. -/
theorem equiv_split {Γ : AEnv D} {C C' : Val} {r r' : Num → Num} {c : Expr L} {x t : Var}
    {op rd : L.ArithOp} {ys : List Var} (hc : Denotes Φ c C') (hr : C.rnd L = some r)
    (hr' : C'.rnd L = some r') (hrd : ∀ u, L.arith rd [u] = some u)
    (h : ∀ n, r (r' n) = r n) :
    Equiv Φ {t} Γ (some C) (.assign x (.arith op (ys.map .var)))
      (.seq (.withCtx c (.assign t (.arith op (ys.map .var))))
        (.assign x (.arith rd [.var t]))) :=
  equiv_split_of hc hr hr' hrd fun _ _ n _ _ _ => h n

/-- **SplitOp**: `[C] x = op(y⃗) ⇝ with C' in t = op(y⃗); x = round(t)` if each
`fmt(yᵢ) ⊆ S` and `C(C'(v)) = C(v)` for every `v = op(u⃗)` with `uᵢ ∈ S`. The
draft takes `S = F_C`. -/
theorem equiv_splitOp {Γ : AEnv D} {C C' : Val} {r r' : Num → Num} {c : Expr L} {x t : Var}
    {op rd : L.ArithOp} {ys : List Var} {as : List (AVal D)} {S : Set Num}
    (hc : Denotes Φ c C') (hr : C.rnd L = some r) (hr' : C'.rnd L = some r')
    (hrd : ∀ u, L.arith rd [u] = some u) (has : List.Forall₂ (fun y a => Γ y = some a) ys as)
    (hS : ∀ a ∈ as, D.γ a.toFmt ⊆ S)
    (h : ∀ us n, (∀ u ∈ us, u ∈ S) → L.arith op us = some n → r (r' n) = r n) :
    Equiv Φ {t} Γ (some C) (.assign x (.arith op (ys.map .var)))
      (.seq (.withCtx c (.assign t (.arith op (ys.map .var))))
        (.assign x (.arith rd [.var t]))) :=
  equiv_split_of hc hr hr' hrd fun _ ns n hΓ hns hop =>
    h ns n (mem_of_forall₂ (hΓ.describes has hns) hS) hop

/-! ## Well-formedness -/

theorem wfList_vars (ys : List Var) : Expr.WFList (L := L) (ys.map .var) := by
  induction ys <;> simp_all [Expr.WFList, Expr.WF]

theorem wf_reround {c : Expr L} (hc : c.WF) (x : Var) (op : L.ArithOp) (ys : List Var) :
    (Stmt.withCtx c (.assign x (.arith op (ys.map .var)))).WF := by
  simp [Stmt.WF, Expr.WF, hc, wfList_vars]

theorem wf_split {c : Expr L} (hc : c.WF) (x t : Var) (op rd : L.ArithOp) (ys : List Var) :
    (Stmt.seq (.withCtx c (.assign t (.arith op (ys.map .var))))
      (.assign x (.arith rd [.var t]))).WF := by
  simp [Stmt.WF, Expr.WF, Expr.WFList, hc, wfList_vars]

/-! ## FPy's contexts -/

variable {decode : List (Label × Val) → Option RoundCtx}

theorem fpy_rnd_ctx {fs : List (Label × Val)} {c : RoundCtx} (h : decode fs = some c) :
    (Val.ctx fs).rnd (fpy decode) = some c.round := by
  simp [Val.rnd, fpy, h]

theorem fpy_round (u : Num) : (fpy decode).arith (show ArithOp from .round) [u] = some u := rfl

theorem RoundCtx.round_round_of_rnd {c₁ c₂ : RoundCtx} {n : Num}
    (h : ∀ u, rnd c₂.F c₂.S c₂.O c₂.rm n = .value u →
      rnd c₁.F c₁.S c₁.O c₁.rm u.toReal = rnd c₁.F c₁.S c₁.O c₁.rm n) :
    c₁.round (c₂.round n) = c₁.round n := by
  obtain ⟨u, hu, hn⟩ := c₂.exists_rnd_eq n
  obtain ⟨w, hw, hw'⟩ := c₁.exists_rnd_eq n
  obtain ⟨w', hw'', he⟩ := c₁.exists_rnd_eq u.toReal
  rw [h u hu, hw] at hw''
  rw [hn, he, hw', RoundResult.value.inj hw'']

/-- A total double-rounding rule (`rndRTO_RN`, …) gives Split's condition. -/
theorem RoundCtx.round_round {c₁ c₂ : RoundCtx}
    (h : ∀ v u, rnd c₂.F c₂.S c₂.O c₂.rm v = .value u →
      rnd c₁.F c₁.S c₁.O c₁.rm u.toReal = rnd c₁.F c₁.S c₁.O c₁.rm v) (n : Num) :
    c₁.round (c₂.round n) = c₁.round n :=
  round_round_of_rnd (h n)

/-- Double rounding at one input: a special through composing maps, and a
finite `x` that `F₂` keeps in bound and on which the finite rule holds. -/
theorem RoundCtx.round_round_of {c₁ c₂ : RoundCtx} (hS : c₂.S.Composes c₁.S c₁.O c₁.rm)
    {n : Num} (hn : ∀ x, n = .finite x → ∀ z, RoundsFinite c₂.F.unbounded c₂.rm x z →
      Format.boundOK c₂.F.b z ∧
        ∀ w, RoundsFinite c₁.F.unbounded c₁.rm z w → RoundsFinite c₁.F.unbounded c₁.rm x w) :
    c₁.round (c₂.round n) = c₁.round n := by
  refine round_round_of_rnd fun u hu => ?_
  cases n with
  | special s =>
    rw [rnd_special] at hu
    obtain rfl := RoundResult.value.inj hu
    rw [hS s, rnd_special]
  | finite x =>
    have hz := rndUnbounded_satisfies c₂.F c₂.rm x c₂.defined
    generalize rndUnbounded c₂.F c₂.rm x c₂.defined = z at hz
    obtain ⟨hb, hdr⟩ := hn x rfl z hz
    rw [rnd_finite_of_roundsFinite c₂.defined hz, if_pos hb] at hu
    obtain rfl := RoundResult.value.inj hu
    have hw := rndUnbounded_satisfies c₁.F c₁.rm (z : ℝ) c₁.defined
    rw [WithSpecial.toReal_finite, rnd_finite_of_roundsFinite c₁.defined hw,
      rnd_finite_of_roundsFinite c₁.defined (hdr _ hw)]

theorem reals_finite {F : Format} {u : Num} {a : ℝ} (hu : u ∈ F.reals) (h : u = .finite a) :
    ∃ d ∈ F, (d : ℝ) = a := by
  obtain ⟨w, hw, rfl⟩ := hu
  cases w with
  | finite d => exact ⟨d, hw, WithSpecial.finite.inj h⟩
  | special => cases h

theorem Num.add_eq_finite {u v : Num} {x : ℝ} (h : Num.add u v = .finite x) :
    ∃ a b, u = .finite a ∧ v = .finite b ∧ x = a + b := by
  rcases u with a | (_ | _) <;> rcases v with b | (_ | _) <;>
    simp only [Num.add, reduceCtorEq] at h
  all_goals first
    | exact ⟨a, b, rfl, rfl, (WithSpecial.finite.inj h).symm⟩
    | split_ifs at h

theorem Num.mul_eq_finite {u v : Num} {x : ℝ} (h : Num.mul u v = .finite x) :
    ∃ a b, u = .finite a ∧ v = .finite b ∧ x = a * b := by
  rcases u with a | (_ | _) <;> rcases v with b | (_ | _) <;>
    simp only [Num.mul, reduceCtorEq] at h
  all_goals first
    | exact ⟨a, b, rfl, rfl, (WithSpecial.finite.inj h).symm⟩
    | split_ifs at h

theorem Num.div_eq_finite {u v : Num} {x : ℝ} (h : Num.div u v = .finite x) :
    (∃ a b, u = .finite a ∧ v = .finite b ∧ b ≠ 0 ∧ x = a / b) ∨
      (∃ a s, u = .finite a ∧ v = .special (.inf s) ∧ x = 0) := by
  rcases u with a | (_ | _) <;> rcases v with b | (_ | _) <;>
    simp only [Num.div, reduceCtorEq] at h
  · split_ifs at h
    exact .inl ⟨a, b, rfl, rfl, ‹_›, (WithSpecial.finite.inj h).symm⟩
  · exact .inr ⟨a, _, rfl, rfl, (WithSpecial.finite.inj h).symm⟩

theorem Num.sqrt_eq_finite {u : Num} {x : ℝ} (h : Num.sqrt u = .finite x) :
    ∃ a, u = .finite a ∧ 0 ≤ a ∧ x = Real.sqrt a := by
  rcases u with a | ((_ | _) | _) <;> simp only [Num.sqrt, reduceCtorEq] at h
  split_ifs at h with ha
  exact ⟨a, rfl, not_lt.mp ha, (WithSpecial.finite.inj h).symm⟩

section SplitOp

variable {c₁ c₂ : RoundCtx} (hS : c₂.S.Composes c₁.S c₁.O c₁.rm) (hb : c₂.F.b = ⊤)
include hS hb

/-- SplitOp's condition for `+` from Roux's rule (`rndAdd`), when `F₂` is unbounded. -/
theorem splitOp_add
    (hrule : ∀ {a b : Mpfx.Dyadic}, a ∈ c₁.F → b ∈ c₁.F → ∀ {z w : Mpfx.Dyadic},
      RoundsFinite c₂.F.unbounded c₂.rm ((a + b : Mpfx.Dyadic) : ℝ) z →
      RoundsFinite c₁.F.unbounded c₁.rm (z : ℝ) w →
      RoundsFinite c₁.F.unbounded c₁.rm ((a + b : Mpfx.Dyadic) : ℝ) w)
    (us : List Num) (n : Num) (hus : ∀ u ∈ us, u ∈ c₁.F.reals)
    (hop : (fpy decode).arith (show ArithOp from .add) us = some n) :
    c₁.round (c₂.round n) = c₁.round n := by
  rcases us with _ | ⟨u, _ | ⟨v, _ | _⟩⟩ <;> simp only [fpy, ArithOp.eval, reduceCtorEq,
    Option.some.injEq] at hop
  subst hop
  refine RoundCtx.round_round_of hS fun x hx z hz => ⟨by rw [hb]; trivial, fun w hw => ?_⟩
  obtain ⟨a, b, rfl, rfl, rfl⟩ := Num.add_eq_finite hx
  obtain ⟨d₁, hd₁, rfl⟩ := reals_finite (hus (.finite a) (by simp)) rfl
  obtain ⟨d₂, hd₂, rfl⟩ := reals_finite (hus (.finite b) (by simp)) rfl
  rw [← Dyadic.coe_real_add] at hz ⊢
  exact hrule hd₁ hd₂ hz hw

/-- SplitOp's condition for `×` from Roux's rules (`rndMul_*`), when `F₂` is
unbounded. -/
theorem splitOp_mul
    (hrule : ∀ {a b : Mpfx.Dyadic}, a ∈ c₁.F → b ∈ c₁.F → ∀ {z w : Mpfx.Dyadic},
      RoundsFinite c₂.F.unbounded c₂.rm ((a * b : Mpfx.Dyadic) : ℝ) z →
      RoundsFinite c₁.F.unbounded c₁.rm (z : ℝ) w →
      RoundsFinite c₁.F.unbounded c₁.rm ((a * b : Mpfx.Dyadic) : ℝ) w)
    (us : List Num) (n : Num) (hus : ∀ u ∈ us, u ∈ c₁.F.reals)
    (hop : (fpy decode).arith (show ArithOp from .mul) us = some n) :
    c₁.round (c₂.round n) = c₁.round n := by
  rcases us with _ | ⟨u, _ | ⟨v, _ | _⟩⟩ <;> simp only [fpy, ArithOp.eval, reduceCtorEq,
    Option.some.injEq] at hop
  subst hop
  refine RoundCtx.round_round_of hS fun x hx z hz => ⟨by rw [hb]; trivial, fun w hw => ?_⟩
  obtain ⟨a, b, rfl, rfl, rfl⟩ := Num.mul_eq_finite hx
  obtain ⟨d₁, hd₁, rfl⟩ := reals_finite (hus (.finite a) (by simp)) rfl
  obtain ⟨d₂, hd₂, rfl⟩ := reals_finite (hus (.finite b) (by simp)) rfl
  rw [← Dyadic.coe_real_mul] at hz ⊢
  exact hrule hd₁ hd₂ hz hw

/-- SplitOp's condition for `÷` from Roux's rules (`rndDiv_*`), when `F₂` is
unbounded. -/
theorem splitOp_div
    (hrule : ∀ {a b : Mpfx.Dyadic}, a ∈ c₁.F → b ∈ c₁.F → (b : ℝ) ≠ 0 → ∀ {z w : Mpfx.Dyadic},
      RoundsFinite c₂.F.unbounded c₂.rm ((a : ℝ) / (b : ℝ)) z →
      RoundsFinite c₁.F.unbounded c₁.rm (z : ℝ) w →
      RoundsFinite c₁.F.unbounded c₁.rm ((a : ℝ) / (b : ℝ)) w)
    (us : List Num) (n : Num) (hus : ∀ u ∈ us, u ∈ c₁.F.reals)
    (hop : (fpy decode).arith (show ArithOp from .div) us = some n) :
    c₁.round (c₂.round n) = c₁.round n := by
  rcases us with _ | ⟨u, _ | ⟨v, _ | _⟩⟩ <;> simp only [fpy, ArithOp.eval, reduceCtorEq,
    Option.some.injEq] at hop
  subst hop
  refine RoundCtx.round_round_of hS fun x hx z hz => ⟨by rw [hb]; trivial, fun w hw => ?_⟩
  rcases Num.div_eq_finite hx with ⟨a, b, rfl, rfl, hb0, rfl⟩ | ⟨_, _, _, _, rfl⟩
  · obtain ⟨d₁, hd₁, rfl⟩ := reals_finite (hus (.finite a) (by simp)) rfl
    obtain ⟨d₂, hd₂, rfl⟩ := reals_finite (hus (.finite b) (by simp)) rfl
    exact hrule hd₁ hd₂ hb0 hz hw
  · obtain rfl := RoundsFinite.eq_zero_of_zero hz
    simpa using hw

/-- SplitOp's condition for `√` from Roux's rules (`rndSqrt_*`), when `F₂` is
unbounded. -/
theorem splitOp_sqrt
    (hrule : ∀ {a : Mpfx.Dyadic}, a ∈ c₁.F → 0 ≤ (a : ℝ) → ∀ {z w : Mpfx.Dyadic},
      RoundsFinite c₂.F.unbounded c₂.rm (Real.sqrt (a : ℝ)) z →
      RoundsFinite c₁.F.unbounded c₁.rm (z : ℝ) w →
      RoundsFinite c₁.F.unbounded c₁.rm (Real.sqrt (a : ℝ)) w)
    (us : List Num) (n : Num) (hus : ∀ u ∈ us, u ∈ c₁.F.reals)
    (hop : (fpy decode).arith (show ArithOp from .sqrt) us = some n) :
    c₁.round (c₂.round n) = c₁.round n := by
  rcases us with _ | ⟨u, _ | _⟩ <;> simp only [fpy, ArithOp.eval, reduceCtorEq,
    Option.some.injEq] at hop
  subst hop
  refine RoundCtx.round_round_of hS fun x hx z hz => ⟨by rw [hb]; trivial, fun w hw => ?_⟩
  obtain ⟨a, rfl, ha, rfl⟩ := Num.sqrt_eq_finite hx
  obtain ⟨d, hd, rfl⟩ := reals_finite (hus (.finite a) (by simp)) rfl
  exact hrule hd ha hz hw

end SplitOp

end Fpy
