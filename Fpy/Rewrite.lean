import Fpy.FormatInference.Sound

/-!
# Rewriting (§5)

A rewrite `[C] s ⇝ s' if φ` replaces `s` by `s'` where the current context is
`C`. `Equiv Φ X Γ κ s s'` is its correctness: from every store in `Γ`, under
every context `κ` admits, `s` and `s'` reach the same outcomes up to the fresh
variables `X`.

`Rw` places rewrites in a program. It follows format inference through each
statement, so each site is checked against the `Γ` and `κ` the analysis assigns
it, and a callee's body is checked at every call the analysis visits. `Rw.sim`
is the congruence theorem, and `run_iff_of_rw` the whole-program theorem:
rewriting preserves `Run`.
-/

namespace Fpy

variable {L : Signature} {D : FormatDomain}

/-! ## Agreement outside the fresh variables -/

/-- `σ` and `σ'` agree outside `X`. -/
def Store.Agree (X : Set Var) (σ σ' : Store) : Prop := ∀ x ∉ X, σ x = σ' x

/-- Equal returns, or normal ends in stores that agree outside `X`. -/
def Outcome.Agree (X : Set Var) : Outcome → Outcome → Prop
  | .normal σ, .normal σ' => σ.Agree X σ'
  | .ret v, .ret v' => v = v'
  | _, _ => False

/-- The correctness of a rewrite `[C] s ⇝ s'`: under `Φ`, from every store in
`Γ` and under every context `κ` admits, `s` and `s'` reach outcomes that agree
outside the fresh variables `X`. -/
def Equiv (Φ : Program L) (X : Set Var) (Γ : AEnv D) (κ : Option Val) (s s' : Stmt L) :
    Prop :=
  ∀ ⦃σ C⦄, Γ.Holds σ → Admits κ C →
    (∀ o, Exec Φ σ C s o → ∃ o', Exec Φ σ C s' o' ∧ o.Agree X o') ∧
    (∀ o', Exec Φ σ C s' o' → ∃ o, Exec Φ σ C s o ∧ o.Agree X o')

/-- `s` under `Φ` and `s'` under `Φ'` reach agreeing outcomes from stores that
agree outside `X`, the first in `Γ`, under every context `κ` admits. -/
def Sim (Φ Φ' : Program L) (X : Set Var) (Γ : AEnv D) (κ : Option Val) (s s' : Stmt L) :
    Prop :=
  ∀ ⦃σ σ' C⦄, Γ.Holds σ → σ.Agree X σ' → Admits κ C →
    (∀ o, Exec Φ σ C s o → ∃ o', Exec Φ' σ' C s' o' ∧ o.Agree X o') ∧
    (∀ o', Exec Φ' σ' C s' o' → ∃ o, Exec Φ σ C s o ∧ o.Agree X o')

section Agree

variable {X : Set Var}

theorem Store.Agree.refl (σ : Store) : σ.Agree X σ := fun _ _ => rfl

theorem Store.Agree.trans {σ₁ σ₂ σ₃ : Store} (h₁ : σ₁.Agree X σ₂) (h₂ : σ₂.Agree X σ₃) :
    σ₁.Agree X σ₃ := fun x hx => (h₁ x hx).trans (h₂ x hx)

theorem Store.Agree.update {σ σ' : Store} (h : σ.Agree X σ') (x : Var) (v : Val) :
    (σ.update x v).Agree X (σ'.update x v) := by
  intro z hz
  simp only [Store.update, Function.update_apply]
  split_ifs
  · rfl
  · exact h z hz

/-- Writing a fresh `t` before `x` changes nothing outside `t`. -/
theorem Store.Agree.update_fresh (σ : Store) {x t : Var} (v w : Val) :
    (σ.update x v).Agree {t} ((σ.update t w).update x v) := by
  intro z hz
  simp only [Set.mem_singleton_iff] at hz
  simp [Store.update, Function.update_apply, hz]

/-- Writing a variable of `X` changes nothing outside `X`. -/
theorem Store.agree_update_of_mem (σ : Store) {u : Var} (hu : u ∈ X) (w : Val) :
    σ.Agree X (σ.update u w) := fun z hz => by
  simp [Store.update, show z ≠ u from fun h => hz (h ▸ hu)]

theorem Outcome.Agree.trans {o₁ o₂ o₃ : Outcome} (h₁ : o₁.Agree X o₂) (h₂ : o₂.Agree X o₃) :
    o₁.Agree X o₃ := by
  cases o₁ <;> cases o₂ <;> cases o₃ <;> simp only [Outcome.Agree] at *
  all_goals exact h₁.trans h₂

theorem Outcome.Agree.normal_left {σ : Store} {o : Outcome} (h : (Outcome.normal σ).Agree X o) :
    ∃ σ', o = .normal σ' ∧ σ.Agree X σ' := by
  cases o with
  | normal σ' => exact ⟨σ', rfl, h⟩
  | ret _ => exact False.elim h

theorem Outcome.Agree.normal_right {σ' : Store} {o : Outcome}
    (h : o.Agree X (.normal σ')) : ∃ σ, o = .normal σ ∧ σ.Agree X σ' := by
  cases o with
  | normal σ => exact ⟨σ, rfl, h⟩
  | ret _ => exact False.elim h

theorem Outcome.Agree.ret_left {v : Val} {o : Outcome} (h : (Outcome.ret v).Agree X o) :
    o = .ret v := by
  cases o with
  | ret v' => exact congrArg _ h.symm
  | normal _ => exact False.elim h

theorem Outcome.Agree.ret_right {v : Val} {o : Outcome} (h : o.Agree X (.ret v)) :
    o = .ret v := by
  cases o with
  | ret v' => exact congrArg _ h
  | normal _ => exact False.elim h

/-- A store agreeing with one in `Γ` outside `X` is in `Γ`, if `Γ` binds nothing in `X`. -/
theorem AEnv.Holds.agree {Γ : AEnv D} {σ σ' : Store} (hΓ : Γ.Holds σ) (hσ : σ.Agree X σ')
    (hX : ∀ x ∈ X, Γ x = none) : Γ.Holds σ' := by
  intro x a hx
  have hx' : x ∉ X := fun h => by simp [hX x h] at hx
  rw [← hσ x hx']
  exact hΓ x a hx

end Agree

/-- An `Equiv` from one direction: by determinism, it suffices that `s'` runs
only where `s` does. -/
theorem Equiv.of_fwd {Φ : Program L} {X : Set Var} {Γ : AEnv D} {κ : Option Val}
    {s s' : Stmt L}
    (hfwd : ∀ σ C o, Γ.Holds σ → Admits κ C → Exec Φ σ C s o →
      ∃ o', Exec Φ σ C s' o' ∧ o.Agree X o')
    (hrun : ∀ σ C o', Γ.Holds σ → Admits κ C → Exec Φ σ C s' o' → ∃ o, Exec Φ σ C s o) :
    Equiv Φ X Γ κ s s' := fun σ C hΓ hκ =>
  ⟨fun o hs => hfwd σ C o hΓ hκ hs, fun o' hs' => by
    obtain ⟨o, hs⟩ := hrun σ C o' hΓ hκ hs'
    obtain ⟨o₂, hs₂, hag⟩ := hfwd σ C o hΓ hκ hs
    exact ⟨o, hs, Exec.det _ hs₂ hs' ▸ hag⟩⟩

/-! ## Rewriting a program -/

variable (A : Analysis L D) (Φ Φ' : Program L) (X : Set Var)

mutual

/-- `e` reads no variable of `X`, and each function it calls has its body under
`Φ` rewritten to its body under `Φ'`, for the argument's abstract value at that
call. -/
inductive RwExpr : AEnv D → Option Val → Expr L → Prop
  | bool {Γ κ b} : RwExpr Γ κ (.bool b)
  | num {Γ κ n} : RwExpr Γ κ (.num n)
  | real {Γ κ} : RwExpr Γ κ .real
  | var {Γ κ x} : x ∉ X → RwExpr Γ κ (.var x)
  | list {Γ κ es} : (∀ e ∈ es, RwExpr Γ κ e) → RwExpr Γ κ (.list es)
  | index {Γ κ e₁ e₂} : RwExpr Γ κ e₁ → RwExpr Γ κ e₂ → RwExpr Γ κ (.index e₁ e₂)
  | record {Γ κ fs} : (∀ p ∈ fs, RwExpr Γ κ p.2) → RwExpr Γ κ (.record fs)
  | proj {Γ κ e l} : RwExpr Γ κ e → RwExpr Γ κ (.proj e l)
  | ctx {Γ κ e} : RwExpr Γ κ e → RwExpr Γ κ (.ctx e)
  | arith {Γ κ op es} : (∀ e ∈ es, RwExpr Γ κ e) → RwExpr Γ κ (.arith op es)
  | exact {Γ κ op es} : (∀ e ∈ es, RwExpr Γ κ e) → RwExpr Γ κ (.exact op es)
  | call {Γ κ f e y s s' a} : Φ f = some (y, s) → Φ' f = some (y, s') → RwExpr Γ κ e →
      AEval A Φ Γ κ e a → Rw (.single y a) κ s s' → RwExpr Γ κ (.call f e)

/-- `Γ, κ ⊢ s ⇝ s'`: `s'` is `s` with rewrites at sites, each checked against
the `Γ` and `κ` format inference assigns it. -/
inductive Rw : AEnv D → Option Val → Stmt L → Stmt L → Prop
  | assign {Γ κ x e} : RwExpr Γ κ e → Rw Γ κ (.assign x e) (.assign x e)
  | skip {Γ κ} : Rw Γ κ .skip .skip
  | ret {Γ κ e} : RwExpr Γ κ e → Rw Γ κ (.ret e) (.ret e)
  | assert {Γ κ e} : RwExpr Γ κ e → Rw Γ κ (.assert e) (.assert e)
  | seq {Γ κ s₁ s₂ s₁' s₂' Γ₁ a₁} : AExec A Φ Γ κ s₁ Γ₁ a₁ → Rw Γ κ s₁ s₁' →
      Rw Γ₁ κ s₂ s₂' → Rw Γ κ (.seq s₁ s₂) (.seq s₁' s₂')
  | ite {Γ κ e s₁ s₂ s₁' s₂'} : RwExpr Γ κ e → Rw (A.refine κ e true Γ) κ s₁ s₁' →
      Rw (A.refine κ e false Γ) κ s₂ s₂' → Rw Γ κ (.ite e s₁ s₂) (.ite e s₁' s₂')
  | whileDo {Γ κ e s s' Γᵢ Γ' a} : Γ.Le Γᵢ → RwExpr Γᵢ κ e →
      AExec A Φ (A.refine κ e true Γᵢ) κ s Γ' a → Γ'.Le Γᵢ →
      Rw (A.refine κ e true Γᵢ) κ s s' → Rw Γ κ (.whileDo e s) (.whileDo e s')
  | withCtx {Γ κ e C s s'} : RwExpr Γ (some .real) e → AEval A Φ Γ (some .real) e (.known C) →
      Rw Γ (some C) s s' → Rw Γ κ (.withCtx e s) (.withCtx e s')
  | withUnknown {Γ κ e s s'} : RwExpr Γ (some .real) e → Rw Γ none s s' →
      Rw Γ κ (.withCtx e s) (.withCtx e s')
  /-- A rewrite site. -/
  | site {Γ κ s s'} : Sim Φ Φ' X Γ κ s s' → Rw Γ κ s s'

end

/-! ## Congruence -/

variable {A Φ Φ' X}

mutual

theorem eval_fwd (hA : A.Sound Φ) {σ : Store} {C : Val} {e : Expr L} {v : Val} :
    Eval Φ σ C e v → ∀ {Γ κ σ'}, Γ.Holds σ → σ.Agree X σ' → Admits κ C →
      RwExpr A Φ Φ' X Γ κ e → Eval Φ' σ' C e v
  | .bool, _, _, _, _, _, _, .bool => .bool
  | .num, _, _, _, _, _, _, .num => .num
  | .real, _, _, _, _, _, _, .real => .real
  | .var hx, _, _, _, _, hσ, _, .var hX => .var ((hσ _ hX).symm.trans hx)
  | .list hl, _, _, _, hΓ, hσ, hκ, .list hr => .list (evalList_fwd hA hl hΓ hσ hκ hr)
  | .index h₁ h₂ hk, _, _, _, hΓ, hσ, hκ, .index r₁ r₂ =>
      .index (eval_fwd hA h₁ hΓ hσ hκ r₁) (eval_fwd hA h₂ hΓ hσ hκ r₂) hk
  | .record hf, _, _, _, hΓ, hσ, hκ, .record hr => .record (evalFields_fwd hA hf hΓ hσ hκ hr)
  | .proj h hl, _, _, _, hΓ, hσ, hκ, .proj r => .proj (eval_fwd hA h hΓ hσ hκ r) hl
  | .ctx h hρ, _, _, _, hΓ, hσ, hκ, .ctx r => .ctx (eval_fwd hA h hΓ hσ hκ r) hρ
  | .arith hl hop hr, _, _, _, hΓ, hσ, hκ, .arith r =>
      .arith (evalList_fwd hA hl hΓ hσ hκ r) hop hr
  | .exact hl hop, _, _, _, hΓ, hσ, hκ, .exact r => .exact (evalList_fwd hA hl hΓ hσ hκ r) hop
  | .call hΦ he hs, _, _, _, hΓ, hσ, hκ, .call hΦ₁ hΦ' re ha rs => by
      rw [hΦ] at hΦ₁
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hΦ₁)
      obtain ⟨_, hs', hag⟩ := exec_fwd hA hs (AEnv.holds_single (eval_sound hA he hΓ hκ ha))
        (Store.Agree.refl _) hκ rs
      obtain rfl := hag.ret_left
      exact .call hΦ' (eval_fwd hA he hΓ hσ hκ re) hs'

theorem evalList_fwd (hA : A.Sound Φ) {σ : Store} {C : Val} {es : List (Expr L)}
    {vs : List Val} :
    EvalList Φ σ C es vs → ∀ {Γ κ σ'}, Γ.Holds σ → σ.Agree X σ' → Admits κ C →
      (∀ e ∈ es, RwExpr A Φ Φ' X Γ κ e) → EvalList Φ' σ' C es vs
  | .nil, _, _, _, _, _, _, _ => .nil
  | .cons h hs, _, _, _, hΓ, hσ, hκ, hr =>
      .cons (eval_fwd hA h hΓ hσ hκ (hr _ (List.mem_cons_self ..)))
        (evalList_fwd hA hs hΓ hσ hκ fun e he => hr e (List.mem_cons_of_mem _ he))

theorem evalFields_fwd (hA : A.Sound Φ) {σ : Store} {C : Val} {fs : List (Label × Expr L)}
    {vs : List (Label × Val)} :
    EvalFields Φ σ C fs vs → ∀ {Γ κ σ'}, Γ.Holds σ → σ.Agree X σ' → Admits κ C →
      (∀ p ∈ fs, RwExpr A Φ Φ' X Γ κ p.2) → EvalFields Φ' σ' C fs vs
  | .nil, _, _, _, _, _, _, _ => .nil
  | .cons h hs, _, _, _, hΓ, hσ, hκ, hr =>
      .cons (eval_fwd hA h hΓ hσ hκ (hr _ (List.mem_cons_self ..)))
        (evalFields_fwd hA hs hΓ hσ hκ fun p hp => hr p (List.mem_cons_of_mem _ hp))

theorem exec_fwd (hA : A.Sound Φ) {σ : Store} {C : Val} {s : Stmt L} {o : Outcome} :
    Exec Φ σ C s o → ∀ {Γ κ σ' s'}, Γ.Holds σ → σ.Agree X σ' → Admits κ C →
      Rw A Φ Φ' X Γ κ s s' → ∃ o', Exec Φ' σ' C s' o' ∧ o.Agree X o'
  | h, _, _, _, _, hΓ, hσ, hκ, .site hs => (hs hΓ hσ hκ).1 _ h
  | .assign he, _, _, _, _, hΓ, hσ, hκ, .assign r =>
      ⟨_, .assign (eval_fwd hA he hΓ hσ hκ r), hσ.update _ _⟩
  | .skip, _, _, _, _, _, hσ, _, .skip => ⟨_, .skip, hσ⟩
  | .ret he, _, _, _, _, hΓ, hσ, hκ, .ret r => ⟨_, .ret (eval_fwd hA he hΓ hσ hκ r), rfl⟩
  | .assert he, _, _, _, _, hΓ, hσ, hκ, .assert r =>
      ⟨_, .assert (eval_fwd hA he hΓ hσ hκ r), hσ⟩
  | .seqNormal h₁ h₂, _, _, _, _, hΓ, hσ, hκ, .seq ha r₁ r₂ => by
      obtain ⟨_, h₁', hag⟩ := exec_fwd hA h₁ hΓ hσ hκ r₁
      obtain ⟨_, rfl, hσ₁⟩ := hag.normal_left
      obtain ⟨o', h₂', hag'⟩ := exec_fwd hA h₂ (exec_sound hA h₁ hΓ hκ ha) hσ₁ hκ r₂
      exact ⟨o', .seqNormal h₁' h₂', hag'⟩
  | .seqRet h₁, _, _, _, _, hΓ, hσ, hκ, .seq _ r₁ _ => by
      obtain ⟨_, h₁', hag⟩ := exec_fwd hA h₁ hΓ hσ hκ r₁
      obtain rfl := hag.ret_left
      exact ⟨_, .seqRet h₁', rfl⟩
  | .iteTrue he h₁, _, _, _, _, hΓ, hσ, hκ, .ite r r₁ _ => by
      obtain ⟨o', h₁', hag⟩ := exec_fwd hA h₁ (hA.refine hΓ hκ he) hσ hκ r₁
      exact ⟨o', .iteTrue (eval_fwd hA he hΓ hσ hκ r) h₁', hag⟩
  | .iteFalse he h₂, _, _, _, _, hΓ, hσ, hκ, .ite r _ r₂ => by
      obtain ⟨o', h₂', hag⟩ := exec_fwd hA h₂ (hA.refine hΓ hκ he) hσ hκ r₂
      exact ⟨o', .iteFalse (eval_fwd hA he hΓ hσ hκ r) h₂', hag⟩
  | .whileFalse he, _, _, _, _, hΓ, hσ, hκ, .whileDo hle r _ _ _ =>
      ⟨_, .whileFalse (eval_fwd hA he (hle _ hΓ) hσ hκ r), hσ⟩
  | .whileTrue he (.seqNormal hs hw), _, _, _, _, hΓ, hσ, hκ, .whileDo hle r ha hle' rb => by
      have hΓᵢ := hA.refine (hle _ hΓ) hκ he
      obtain ⟨_, hs', hag⟩ := exec_fwd hA hs hΓᵢ hσ hκ rb
      obtain ⟨_, rfl, hσ₁⟩ := hag.normal_left
      obtain ⟨o', hw', hag'⟩ := exec_fwd hA hw (exec_sound hA hs hΓᵢ hκ ha) hσ₁ hκ
        (.whileDo hle' r ha hle' rb)
      exact ⟨o', .whileTrue (eval_fwd hA he (hle _ hΓ) hσ hκ r) (.seqNormal hs' hw'), hag'⟩
  | .whileTrue he (.seqRet hs), _, _, _, _, hΓ, hσ, hκ, .whileDo hle r _ _ rb => by
      obtain ⟨_, hs', hag⟩ := exec_fwd hA hs (hA.refine (hle _ hΓ) hκ he) hσ hκ rb
      obtain rfl := hag.ret_left
      exact ⟨_, .whileTrue (eval_fwd hA he (hle _ hΓ) hσ hκ r) (.seqRet hs'), rfl⟩
  | .withCtx he hs, _, _, _, _, hΓ, hσ, _, .withCtx r ha rb => by
      cases eval_sound hA he hΓ (admits_some _) ha with
      | known =>
        obtain ⟨o', hs', hag⟩ := exec_fwd hA hs hΓ hσ (admits_some _) rb
        exact ⟨o', .withCtx (eval_fwd hA he hΓ hσ (admits_some _) r) hs', hag⟩
  | .withCtx he hs, _, _, _, _, hΓ, hσ, _, .withUnknown r rb => by
      obtain ⟨o', hs', hag⟩ := exec_fwd hA hs hΓ hσ (admits_none _) rb
      exact ⟨o', .withCtx (eval_fwd hA he hΓ hσ (admits_some _) r) hs', hag⟩

end

mutual

theorem eval_bwd (hA : A.Sound Φ) {σ' : Store} {C : Val} {e : Expr L} {v : Val} :
    Eval Φ' σ' C e v → ∀ {Γ κ σ}, Γ.Holds σ → σ.Agree X σ' → Admits κ C →
      RwExpr A Φ Φ' X Γ κ e → Eval Φ σ C e v
  | .bool, _, _, _, _, _, _, .bool => .bool
  | .num, _, _, _, _, _, _, .num => .num
  | .real, _, _, _, _, _, _, .real => .real
  | .var hx, _, _, _, _, hσ, _, .var hX => .var ((hσ _ hX).trans hx)
  | .list hl, _, _, _, hΓ, hσ, hκ, .list hr => .list (evalList_bwd hA hl hΓ hσ hκ hr)
  | .index h₁ h₂ hk, _, _, _, hΓ, hσ, hκ, .index r₁ r₂ =>
      .index (eval_bwd hA h₁ hΓ hσ hκ r₁) (eval_bwd hA h₂ hΓ hσ hκ r₂) hk
  | .record hf, _, _, _, hΓ, hσ, hκ, .record hr => .record (evalFields_bwd hA hf hΓ hσ hκ hr)
  | .proj h hl, _, _, _, hΓ, hσ, hκ, .proj r => .proj (eval_bwd hA h hΓ hσ hκ r) hl
  | .ctx h hρ, _, _, _, hΓ, hσ, hκ, .ctx r => .ctx (eval_bwd hA h hΓ hσ hκ r) hρ
  | .arith hl hop hr, _, _, _, hΓ, hσ, hκ, .arith r =>
      .arith (evalList_bwd hA hl hΓ hσ hκ r) hop hr
  | .exact hl hop, _, _, _, hΓ, hσ, hκ, .exact r => .exact (evalList_bwd hA hl hΓ hσ hκ r) hop
  | .call hΦ' he hs, _, _, _, hΓ, hσ, hκ, .call hΦ hΦ₁ re ha rs => by
      rw [hΦ'] at hΦ₁
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hΦ₁)
      have he₀ := eval_bwd hA he hΓ hσ hκ re
      obtain ⟨_, hs₀, hag⟩ := exec_bwd hA hs (AEnv.holds_single (eval_sound hA he₀ hΓ hκ ha))
        (Store.Agree.refl _) hκ rs
      obtain rfl := hag.ret_right
      exact .call hΦ he₀ hs₀

theorem evalList_bwd (hA : A.Sound Φ) {σ' : Store} {C : Val} {es : List (Expr L)}
    {vs : List Val} :
    EvalList Φ' σ' C es vs → ∀ {Γ κ σ}, Γ.Holds σ → σ.Agree X σ' → Admits κ C →
      (∀ e ∈ es, RwExpr A Φ Φ' X Γ κ e) → EvalList Φ σ C es vs
  | .nil, _, _, _, _, _, _, _ => .nil
  | .cons h hs, _, _, _, hΓ, hσ, hκ, hr =>
      .cons (eval_bwd hA h hΓ hσ hκ (hr _ (List.mem_cons_self ..)))
        (evalList_bwd hA hs hΓ hσ hκ fun e he => hr e (List.mem_cons_of_mem _ he))

theorem evalFields_bwd (hA : A.Sound Φ) {σ' : Store} {C : Val} {fs : List (Label × Expr L)}
    {vs : List (Label × Val)} :
    EvalFields Φ' σ' C fs vs → ∀ {Γ κ σ}, Γ.Holds σ → σ.Agree X σ' → Admits κ C →
      (∀ p ∈ fs, RwExpr A Φ Φ' X Γ κ p.2) → EvalFields Φ σ C fs vs
  | .nil, _, _, _, _, _, _, _ => .nil
  | .cons h hs, _, _, _, hΓ, hσ, hκ, hr =>
      .cons (eval_bwd hA h hΓ hσ hκ (hr _ (List.mem_cons_self ..)))
        (evalFields_bwd hA hs hΓ hσ hκ fun p hp => hr p (List.mem_cons_of_mem _ hp))

theorem exec_bwd (hA : A.Sound Φ) {σ' : Store} {C : Val} {s' : Stmt L} {o' : Outcome} :
    Exec Φ' σ' C s' o' → ∀ {Γ κ σ s}, Γ.Holds σ → σ.Agree X σ' → Admits κ C →
      Rw A Φ Φ' X Γ κ s s' → ∃ o, Exec Φ σ C s o ∧ o.Agree X o'
  | h, _, _, _, _, hΓ, hσ, hκ, .site hs => (hs hΓ hσ hκ).2 _ h
  | .assign he, _, _, _, _, hΓ, hσ, hκ, .assign r =>
      ⟨_, .assign (eval_bwd hA he hΓ hσ hκ r), hσ.update _ _⟩
  | .skip, _, _, _, _, _, hσ, _, .skip => ⟨_, .skip, hσ⟩
  | .ret he, _, _, _, _, hΓ, hσ, hκ, .ret r => ⟨_, .ret (eval_bwd hA he hΓ hσ hκ r), rfl⟩
  | .assert he, _, _, _, _, hΓ, hσ, hκ, .assert r =>
      ⟨_, .assert (eval_bwd hA he hΓ hσ hκ r), hσ⟩
  | .seqNormal h₁ h₂, _, _, _, _, hΓ, hσ, hκ, .seq ha r₁ r₂ => by
      obtain ⟨_, h₁₀, hag⟩ := exec_bwd hA h₁ hΓ hσ hκ r₁
      obtain ⟨_, rfl, hσ₁⟩ := hag.normal_right
      obtain ⟨o, h₂₀, hag'⟩ := exec_bwd hA h₂ (exec_sound hA h₁₀ hΓ hκ ha) hσ₁ hκ r₂
      exact ⟨o, .seqNormal h₁₀ h₂₀, hag'⟩
  | .seqRet h₁, _, _, _, _, hΓ, hσ, hκ, .seq _ r₁ _ => by
      obtain ⟨_, h₁₀, hag⟩ := exec_bwd hA h₁ hΓ hσ hκ r₁
      obtain rfl := hag.ret_right
      exact ⟨_, .seqRet h₁₀, rfl⟩
  | .iteTrue he h₁, _, _, _, _, hΓ, hσ, hκ, .ite r r₁ _ => by
      have he₀ := eval_bwd hA he hΓ hσ hκ r
      obtain ⟨o, h₁₀, hag⟩ := exec_bwd hA h₁ (hA.refine hΓ hκ he₀) hσ hκ r₁
      exact ⟨o, .iteTrue he₀ h₁₀, hag⟩
  | .iteFalse he h₂, _, _, _, _, hΓ, hσ, hκ, .ite r _ r₂ => by
      have he₀ := eval_bwd hA he hΓ hσ hκ r
      obtain ⟨o, h₂₀, hag⟩ := exec_bwd hA h₂ (hA.refine hΓ hκ he₀) hσ hκ r₂
      exact ⟨o, .iteFalse he₀ h₂₀, hag⟩
  | .whileFalse he, _, _, _, _, hΓ, hσ, hκ, .whileDo hle r _ _ _ =>
      ⟨_, .whileFalse (eval_bwd hA he (hle _ hΓ) hσ hκ r), hσ⟩
  | .whileTrue he (.seqNormal hs hw), _, _, _, _, hΓ, hσ, hκ, .whileDo hle r ha hle' rb => by
      have he₀ := eval_bwd hA he (hle _ hΓ) hσ hκ r
      have hΓᵢ := hA.refine (hle _ hΓ) hκ he₀
      obtain ⟨_, hs₀, hag⟩ := exec_bwd hA hs hΓᵢ hσ hκ rb
      obtain ⟨_, rfl, hσ₁⟩ := hag.normal_right
      obtain ⟨o, hw₀, hag'⟩ := exec_bwd hA hw (exec_sound hA hs₀ hΓᵢ hκ ha) hσ₁ hκ
        (.whileDo hle' r ha hle' rb)
      exact ⟨o, .whileTrue he₀ (.seqNormal hs₀ hw₀), hag'⟩
  | .whileTrue he (.seqRet hs), _, _, _, _, hΓ, hσ, hκ, .whileDo hle r _ _ rb => by
      have he₀ := eval_bwd hA he (hle _ hΓ) hσ hκ r
      obtain ⟨_, hs₀, hag⟩ := exec_bwd hA hs (hA.refine (hle _ hΓ) hκ he₀) hσ hκ rb
      obtain rfl := hag.ret_right
      exact ⟨_, .whileTrue he₀ (.seqRet hs₀), rfl⟩
  | .withCtx he hs, _, _, _, _, hΓ, hσ, _, .withCtx r ha rb => by
      have he₀ := eval_bwd hA he hΓ hσ (admits_some _) r
      cases eval_sound hA he₀ hΓ (admits_some _) ha with
      | known =>
        obtain ⟨o, hs₀, hag⟩ := exec_bwd hA hs hΓ hσ (admits_some _) rb
        exact ⟨o, .withCtx he₀ hs₀, hag⟩
  | .withCtx he hs, _, _, _, _, hΓ, hσ, _, .withUnknown r rb => by
      obtain ⟨o, hs₀, hag⟩ := exec_bwd hA hs hΓ hσ (admits_none _) rb
      exact ⟨o, .withCtx (eval_bwd hA he hΓ hσ (admits_some _) r) hs₀, hag⟩

end

/-- **Congruence**: rewriting sites, each under the `Γ` and `κ` format inference
assigns it, gives a statement that simulates the original. -/
theorem Rw.sim (hA : A.Sound Φ) {Γ : AEnv D} {κ : Option Val} {s s' : Stmt L}
    (h : Rw A Φ Φ' X Γ κ s s') : Sim Φ Φ' X Γ κ s s' :=
  fun _ _ _ hΓ hσ hκ =>
    ⟨fun _ hs => exec_fwd hA hs hΓ hσ hκ h, fun _ hs => exec_bwd hA hs hΓ hσ hκ h⟩

/-- A rewrite at a site: `s` rewritten to `s₁` within, then `s₁` to `s'` by a
correct rewrite whose `Γ` binds no fresh variable. -/
theorem Sim.equiv {Γ : AEnv D} {κ : Option Val} {s s₁ s' : Stmt L}
    (h : Sim Φ Φ' X Γ κ s s₁) (h' : Equiv Φ' X Γ κ s₁ s') (hX : ∀ x ∈ X, Γ x = none) :
    Sim Φ Φ' X Γ κ s s' := by
  intro σ σ' C hΓ hσ hκ
  have hΓ' := hΓ.agree hσ hX
  refine ⟨fun o hs => ?_, fun o' hs' => ?_⟩
  · obtain ⟨o₁, hs₁, hag₁⟩ := (h hΓ hσ hκ).1 o hs
    obtain ⟨o', hs', hag⟩ := (h' hΓ' hκ).1 o₁ hs₁
    exact ⟨o', hs', hag₁.trans hag⟩
  · obtain ⟨o₁, hs₁, hag⟩ := (h' hΓ' hκ).2 o' hs'
    obtain ⟨o, hs, hag₁⟩ := (h hΓ hσ hκ).2 o₁ hs₁
    exact ⟨o, hs, hag₁.trans hag⟩

/-- **Rewriting preserves semantics**: if the entry function's body is
rewritten under format inference from an argument bound `a`, the program
returns the same values on every argument `a` describes. -/
theorem run_iff_of_rw (hA : A.Sound Φ) {f : Fn} {y : Var} {s s' : Stmt L} {a : AVal D}
    (hΦ : Φ f = some (y, s)) (hΦ' : Φ' f = some (y, s'))
    (h : Rw A Φ Φ' X (.single y a) (some .real) s s') {v v' : Val} (hv : Describes a v) :
    Run Φ f v v' ↔ Run Φ' f v v' := by
  have hsim := h.sim hA (AEnv.holds_single hv) (Store.Agree.refl _) (admits_some _)
  constructor
  · rintro ⟨_, _, hΦ₁, hs⟩
    rw [hΦ] at hΦ₁
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hΦ₁)
    obtain ⟨_, hs', hag⟩ := hsim.1 _ hs
    obtain rfl := hag.ret_left
    exact ⟨y, s', hΦ', hs'⟩
  · rintro ⟨_, _, hΦ₁, hs'⟩
    rw [hΦ'] at hΦ₁
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hΦ₁)
    obtain ⟨_, hs, hag⟩ := hsim.2 _ hs'
    obtain rfl := hag.ret_right
    exact ⟨y, s, hΦ, hs⟩

end Fpy
