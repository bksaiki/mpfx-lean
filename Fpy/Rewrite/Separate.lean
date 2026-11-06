import Fpy.Rewrite.Basic
import Fpy.FormatInference.Domain
import Mpfx.DoubleRounding.Special

/-!
# Separating arithmetic from rounding (§5.1)

Fig. 12's rewrites of `x = op(es)` first bind `es` under `C` to fresh `ts`
(`equiv_bind`), so each is stated on `x = op(ts)`. §5.1's are Elim, Insert and
Split (`equiv_elim`, `equiv_insert`, `equiv_split`). `C'` is written by any
expression that denotes it.

For FPy's contexts, `RoundCtx.round_round` turns each total double-rounding
rule (`rndRTO_RN`, …) into Split's condition, and `split_add`, `split_mul`,
`split_div` and `split_sqrt` turn Roux's rules (`rndAdd`, `rndMul_*`,
`rndDiv_*`, `rndSqrt_*`) into it when the inputs lie in `F_C`.
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

/-- `fmt(yᵢ) ⊆ Fᵢ`. -/
def FmtsIn (Γ : AEnv D) (ys : List Var) (Fs : List D.Fmt) : Prop :=
  List.Forall₂ (fun y F => ∃ a, Γ y = some a ∧ D.γ a.toFmt ⊆ D.γ F) ys Fs

/-- If `fmt(yᵢ) ⊆ Fᵢ`, the value of each `yᵢ` lies in `Fᵢ`. -/
theorem AEnv.Holds.mem {Γ : AEnv D} {σ : Store} (hΓ : Γ.Holds σ) :
    ∀ {ys : List Var} {Fs : List D.Fmt} {ns : List Num}, FmtsIn Γ ys Fs →
      List.Forall₂ (fun y n => σ y = some (.num n)) ys ns →
      List.Forall₂ (fun n F => n ∈ D.γ F) ns Fs
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons ⟨_, ha, hF⟩ hs, .cons hn hns => by
    obtain ⟨_, hv, hd⟩ := hΓ _ _ ha
    obtain rfl := Option.some.inj (hv.symm.trans hn)
    exact .cons (hF hd.mem_toFmt) (hΓ.mem hs hns)

/-! ## Binding the operands -/

/-- `f[t₁ ↦ x₁, …, tₖ ↦ xₖ]`, for stores and format environments. -/
def updates {α : Type} (f : Var → Option α) : List Var → List α → Var → Option α
  | t :: ts, x :: xs => updates (Function.update f t (some x)) ts xs
  | _, _ => f

theorem updates_of_not_mem {α : Type} {y : Var} :
    ∀ {f : Var → Option α} {ts : List Var} {xs : List α}, y ∉ ts → updates f ts xs y = f y
  | _, [], _, _ | _, _ :: _, [], _ => rfl
  | _, _ :: _, _ :: _, h => by
    rw [updates, updates_of_not_mem (List.not_mem_of_not_mem_cons h),
      Function.update_of_ne (List.ne_of_not_mem_cons h)]

theorem forall₂_updates {α : Type} :
    ∀ {f : Var → Option α} {ts : List Var} {xs : List α}, ts.Nodup → ts.length = xs.length →
      List.Forall₂ (fun t x => updates f ts xs t = some x) ts xs
  | _, [], [], _, _ => .nil
  | _, _ :: _, _ :: _, h, hl => by
    obtain ⟨ht, hts⟩ := List.nodup_cons.mp h
    exact .cons (by rw [updates, updates_of_not_mem ht, Function.update_self])
      (forall₂_updates hts (Nat.succ.inj hl))

theorem Store.agree_updates : ∀ (σ : Store) {ts : List Var} (vs : List Val),
    (∀ t ∈ ts, t ∈ X) → σ.Agree X (updates σ ts vs)
  | _, [], _, _ | _, _ :: _, [], _ => Store.Agree.refl _
  | σ, _ :: _, _ :: _, h => (σ.agree_update_of_mem (h _ (List.mem_cons_self ..)) _).trans
      (Store.agree_updates _ _ fun t ht => h t (List.mem_cons_of_mem _ ht))

theorem AEnv.Holds.updates {Γ : AEnv D} {σ : Store} (hΓ : Γ.Holds σ) :
    ∀ {ts : List Var} {as : List (AVal D)} {vs : List Val}, List.Forall₂ Describes as vs →
      AEnv.Holds (Fpy.updates Γ ts as) (Fpy.updates σ ts vs)
  | [], _, _, _ | _ :: _, _, _, .nil => hΓ
  | _ :: _, _, _, .cons hd hs => (hΓ.update _ hd).updates hs

/-- `t₁ = e₁; …; tₖ = eₖ; s`. -/
def Stmt.binds : List Var → List (Expr L) → Stmt L → Stmt L
  | t :: ts, e :: es, s => .seq (.assign t e) (Stmt.binds ts es s)
  | _, _, s => s

/-- Binding `es` to `ts` avoided by `es` evaluates `es` in the first store. -/
theorem exec_binds {C : Val} {s : Stmt L} {o : Outcome} :
    ∀ {σ : Store} {ts : List Var} {es : List (Expr L)}, ts.length = es.length →
      (∀ t ∈ ts, t ∈ X) → (∀ e ∈ es, Avoids X e) →
      (Exec Φ σ C (Stmt.binds ts es s) o ↔
        ∃ vs, EvalList Φ σ C es vs ∧ Exec Φ (updates σ ts vs) C s o)
  | _, [], [], _, _, _ =>
    ⟨fun h => ⟨[], .nil, h⟩, fun ⟨_, hl, h⟩ => by cases hl; exact h⟩
  | σ, t :: ts, e :: es, hl, hX, ha => by
    have hX' := fun t ht => hX t (List.mem_cons_of_mem _ ht)
    have ha' := fun e he => ha e (List.mem_cons_of_mem _ he)
    have hagree := fun v => σ.agree_update_of_mem (hX t (List.mem_cons_self ..)) v
    constructor
    · intro h
      cases h with
      | seqNormal h₁ h₂ =>
        cases h₁ with
        | assign he =>
          obtain ⟨vs, hl', h⟩ := (exec_binds (Nat.succ.inj hl) hX' ha').mp h₂
          exact ⟨_ :: vs, .cons he (hl'.agree (hagree _).symm ha'), h⟩
      | seqRet h₁ => cases h₁
    · rintro ⟨_, hl', h⟩
      cases hl' with
      | cons he hl' =>
        exact .seqNormal (.assign he)
          ((exec_binds (Nat.succ.inj hl) hX' ha').mpr ⟨_, hl'.agree (hagree _) ha', h⟩)

variable {A : Analysis L D}

/-- Binding `es` under `C` to fresh `ts`, as each rewrite of Fig. 12 does first:
a rewrite of `x = op(ts)` under `Γ[ts ↦ fmt(es)]` is one of `x = op(es)`. -/
theorem equiv_bind (hA : A.Sound Φ) {Γ : AEnv D} {κ : Option Val} {x : Var} {op : L.ArithOp}
    {es : List (Expr L)} {ts : List Var} {as : List (AVal D)} {s' : Stmt L}
    (hts : ts.Nodup) (hl : ts.length = es.length) (hX : ∀ t ∈ ts, t ∈ X)
    (hes : ∀ e ∈ es, Avoids X e) (has : AEvalList A Φ Γ κ es as)
    (h : Equiv Φ X (updates Γ ts as) κ (.assign x (.arith op (ts.map .var))) s') :
    Equiv Φ X Γ κ (.assign x (.arith op es)) (Stmt.binds ts es s') := by
  have hvs {σ C vs} (hl' : EvalList Φ σ C es vs) :
      EvalList Φ (updates σ ts vs) C (ts.map .var) vs :=
    evalList_vars.mpr (forall₂_updates hts (hl.trans hl'.length_eq))
  refine Equiv.of_fwd (fun σ C o hΓ hκ hs => ?_) (fun σ C o' hΓ hκ hs => ?_)
  · cases hs with
    | assign he =>
      cases he with
      | arith hl' hop hr =>
        obtain ⟨o', hs', hag⟩ := (h (hΓ.updates (evalList_sound hA hl' hΓ hκ has)) hκ).1 _
          (.assign (.arith (hvs hl') hop hr))
        exact ⟨o', (exec_binds hl hX hes).mpr ⟨_, hl', hs'⟩,
          Outcome.Agree.trans (o₂ := .normal _) ((σ.agree_updates _ hX).update _ _) hag⟩
  · obtain ⟨vs, hl', hs'⟩ := (exec_binds hl hX hes).mp hs
    obtain ⟨_, ho, -⟩ := (h (hΓ.updates (evalList_sound hA hl' hΓ hκ has)) hκ).2 o' hs'
    cases ho with
    | assign he =>
      cases he with
      | arith hl'' hop hr =>
        obtain rfl := EvalList.det _ (hvs hl') hl''
        exact ⟨_, .assign (.arith hl' hop hr)⟩

/-! ## Rounding under another context -/

/-- Rounding `op(ys)` under `C'` (denoted by `c`) instead of `C`: correct when
both round each exact result the same way, for the values of `ys` in `Γ`. -/
theorem equiv_reround {Γ : AEnv D} {C C' : Val} {r r' : Num → Num} {c : Expr L} {x : Var}
    {op : L.ArithOp} {ys : List Var} (hc : Denotes Φ c C') (hr : C.rnd L = some r)
    (hr' : C'.rnd L = some r')
    (h : ∀ σ ns n, Γ.Holds σ → List.Forall₂ (fun y n => σ y = some (.num n)) ys ns →
      L.arith op ns = some n → r n = r' n) :
    Equiv Φ X Γ (some C) (.assign x (.arith op (ys.map .var)))
      (.withCtx c (.assign x (.arith op (ys.map .var)))) := by
  refine Equiv.of_fwd (fun σ C₀ o hΓ hκ hs => ?_) (fun σ C₀ _ _ hκ hs => ?_) <;>
    obtain rfl := hκ C rfl
  · cases hs with
    | assign he =>
      cases he with
      | arith hl hop hr₀ =>
        obtain rfl := Option.some.inj (hr₀.symm.trans hr)
        refine ⟨_, .withCtx ((hc σ C').mpr rfl) (Val.isCtx_of_rnd hr')
          (.assign (.arith (evalList_vars.mpr (evalList_vars.mp hl)) hop hr')), ?_⟩
        rw [h σ _ _ hΓ (forall₂_of_evalList hl) hop]
        exact Store.Agree.refl _
  · obtain ⟨_, _, he⟩ := hs.withCtx_assign
    cases he with
    | arith hl hop _ => exact ⟨_, .assign (.arith (evalList_vars.mpr (evalList_vars.mp hl)) hop hr)⟩

/-- **Elim**: `[C] x = op(ts) ⇝ with R in x = op(ts)` if `fmt(tᵢ) ⊆ Fᵢ` and
`op♯(Fs) ⊆ F_C`. -/
theorem equiv_elim (hA : A.Sound Φ) {Γ : AEnv D} {C : Val} {r : Num → Num} {FC : D.Fmt}
    {x : Var} {op : L.ArithOp} {ts : List Var} {Fs : List D.Fmt}
    (hr : C.rnd L = some r) (hFC : A.ctxFmt C = some FC) (hF : FmtsIn Γ ts Fs)
    (hsub : D.γ (A.arith op Fs) ⊆ D.γ FC) :
    Equiv Φ X Γ (some C) (.assign x (.arith op (ts.map .var)))
      (.withCtx .real (.assign x (.arith op (ts.map .var)))) :=
  equiv_reround denotes_real hr rfl fun _ _ n hΓ hns hop =>
    (hA.ctxFmt hFC hr).2 n (hsub (hA.arith (hΓ.mem hF hns) hop))

/-- **Insert**: `[R] x = op(ts) ⇝ with C' in x = op(ts)` if `fmt(tᵢ) ⊆ Fᵢ` and
`op♯(Fs) ⊆ F_{C'}`. -/
theorem equiv_insert (hA : A.Sound Φ) {Γ : AEnv D} {C' : Val} {r' : Num → Num} {FC : D.Fmt}
    {c : Expr L} {x : Var} {op : L.ArithOp} {ts : List Var} {Fs : List D.Fmt}
    (hc : Denotes Φ c C') (hr' : C'.rnd L = some r') (hFC : A.ctxFmt C' = some FC)
    (hF : FmtsIn Γ ts Fs) (hsub : D.γ (A.arith op Fs) ⊆ D.γ FC) :
    Equiv Φ X Γ (some .real) (.assign x (.arith op (ts.map .var)))
      (.withCtx c (.assign x (.arith op (ts.map .var)))) :=
  equiv_reround hc rfl hr' fun _ _ n hΓ hns hop =>
    ((hA.ctxFmt hFC hr').2 n (hsub (hA.arith (hΓ.mem hF hns) hop))).symm

/-! ## Splitting a rounding -/

/-- **Split**: `[C] x = op(ts) ⇝ with C' in r = op(ts); x = round(r)` if
`fmt(tᵢ) ⊆ Fᵢ` and `C(C'(v)) = C(v)` on `op(Fs)`, the exact results of `op` on
inputs `uᵢ ∈ Fᵢ`. `rd` is any operator computing the identity. -/
theorem equiv_split {Γ : AEnv D} {C C' : Val} {rC rC' : Num → Num} {c : Expr L} {x r : Var}
    {op rd : L.ArithOp} {ts : List Var} {Fs : List D.Fmt} (hc : Denotes Φ c C')
    (hr : C.rnd L = some rC) (hr' : C'.rnd L = some rC') (hrd : ∀ u, L.arith rd [u] = some u)
    (hF : FmtsIn Γ ts Fs)
    (h : ∀ us n, List.Forall₂ (fun u F => u ∈ D.γ F) us Fs → L.arith op us = some n →
      rC (rC' n) = rC n) :
    Equiv Φ {r} Γ (some C) (.assign x (.arith op (ts.map .var)))
      (.seq (.withCtx c (.assign r (.arith op (ts.map .var))))
        (.assign x (.arith rd [.var r]))) := by
  refine Equiv.of_fwd (fun σ C₀ o hΓ hκ hs => ?_) (fun σ C₀ _ _ hκ hs => ?_) <;>
    obtain rfl := hκ C rfl
  · cases hs with
    | assign he =>
      cases he with
      | @arith _ _ _ _ _ n _ hl hop hr₀ =>
        obtain rfl := Option.some.inj (hr₀.symm.trans hr)
        refine ⟨_, .seqNormal (.withCtx ((hc σ C').mpr rfl) (Val.isCtx_of_rnd hr')
          (.assign (.arith (evalList_vars.mpr (evalList_vars.mp hl)) hop hr')))
          (.assign (.arith (ns := [rC' n]) (.cons (.var (by simp [Store.update])) .nil) (hrd _)
            hr)), ?_⟩
        rw [h _ n (hΓ.mem hF (forall₂_of_evalList hl)) hop]
        exact Store.Agree.update_fresh _ _ _
  · obtain ⟨_, h₁⟩ := hs.seq_left
    obtain ⟨_, _, he⟩ := h₁.withCtx_assign
    cases he with
    | arith hl hop _ => exact ⟨_, .assign (.arith (evalList_vars.mpr (evalList_vars.mp hl)) hop hr)⟩

/-- Inputs in `Fᵢ ⊆ S` lie in `S`. -/
theorem forall_mem_of_forall₂ {S : Set Num} :
    ∀ {us : List Num} {Fs : List D.Fmt}, List.Forall₂ (fun u F => u ∈ D.γ F) us Fs →
      (∀ F ∈ Fs, D.γ F ⊆ S) → ∀ u ∈ us, u ∈ S
  | _, _, .nil, _, _, hu => absurd hu List.not_mem_nil
  | _, _, .cons hu hs, hS, _, hu' => (List.mem_cons.mp hu').elim
      (fun h => h ▸ hS _ (List.mem_cons_self ..) hu)
      (forall_mem_of_forall₂ hs (fun F hF => hS F (List.mem_cons_of_mem _ hF)) _)

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

section Split

variable {c₁ c₂ : RoundCtx} (hS : c₂.S.Composes c₁.S c₁.O c₁.rm) (hb : c₂.F.b = ⊤)
include hS hb

/-- Split's condition for `+` from Roux's rule (`rndAdd`), when `F₂` is unbounded. -/
theorem split_add
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

/-- Split's condition for `×` from Roux's rules (`rndMul_*`), when `F₂` is
unbounded. -/
theorem split_mul
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

/-- Split's condition for `÷` from Roux's rules (`rndDiv_*`), when `F₂` is
unbounded. -/
theorem split_div
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

/-- Split's condition for `√` from Roux's rules (`rndSqrt_*`), when `F₂` is
unbounded. -/
theorem split_sqrt
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

end Split

end Fpy
