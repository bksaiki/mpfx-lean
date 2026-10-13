import Fpy.DigitBound.Basic

/-!
# Soundness of the digit-bound analysis (Theorem 4.2)

`eval_sound` and `exec_sound`, by induction on the evaluation, in prefix form:
from an assignment describing the store, one agreeing with it below the
derivation's first fresh variable satisfies the derivation's constraints and
describes the result. Untaken branches, and loop bodies run zero times, have
their variables re-chosen in head order (`Sat.extend`). `DEval.wf` gives the
fresh ranges and variable bounds every derivation has.
-/

namespace Fpy.DigitBound

open Mpfx

variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}

/-! ## Well-formed derivations -/

theorem ctxBelow_real (n : ℕ) : CtxBelow n (some SCtx.real) :=
  fun K hK => by obtain rfl := Option.mem_some_iff.mp hK; trivial

mutual

theorem DEval.wf {Δ : DEnv} {κ : Option SCtx} {n₀ : ℕ} {e : Expr (fpy decode)} {d : DVal}
    {Ψ : List Con} {n₁ : ℕ} :
    DEval decode Φ Δ κ n₀ e d Ψ n₁ →
      Fresh n₀ n₁ Ψ ∧ (Δ.Below n₀ → CtxBelow n₀ κ → d.Below n₁)
  | .const hτ => ⟨Fresh.nil _, fun _ _ => ⟨trivial, trivial, fun t ht => by
      obtain ⟨z, rfl, -⟩ := hτ t ht
      trivial⟩⟩
  | .bool => ⟨Fresh.nil _, fun _ _ => trivial⟩
  | .real => ⟨Fresh.nil _, fun _ _ => trivial⟩
  | .var hx => ⟨Fresh.nil _, fun hΔ _ => hΔ _ _ hx⟩
  | .list hl _ hF => ⟨(DEvalList.wf hl).1.append hF, fun _ _ => trivial⟩
  | .index h₁ h₂ _ hF hb => ⟨((DEval.wf h₁).1.append (DEval.wf h₂).1).append hF, fun _ _ => hb⟩
  | .record hf => ⟨(DEvalFields.wf hf).1, fun hΔ hκ => (DEvalFields.wf hf).2 hΔ hκ⟩
  | .proj h hl => ⟨(DEval.wf h).1, fun hΔ hκ => DVal.BelowFields.lookup ((DEval.wf h).2 hΔ hκ) hl⟩
  | .ctx (d := d) h => ⟨(DEval.wf h).1, fun hΔ hκ => by
      cases hc : ctxOf d with
      | none => trivial
      | some C => exact ctxOf_below ((DEval.wf h).2 hΔ hκ) hc⟩
  | .arith hl _ hF hlb hmb => ⟨(DEvalList.wf hl).1.append hF, fun _ _ =>
      ⟨hlb, hmb, fun t ht => absurd ht (by simp)⟩⟩
  | .linear (op := op) hop hl _ hF hlb hmb => ⟨(DEvalList.wf hl).1.append hF, fun hΔ hκ => by
      have hb := (DEvalList.wf hl).2 hΔ hκ
      have h₁ := (hb _ (List.mem_cons_self ..)).2.2 _ rfl
      have h₂ := (hb _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))).2.2 _ rfl
      have hle := hF.le
      refine ⟨hlb, hmb, fun t ht => ?_⟩
      obtain rfl := Option.mem_some_iff.mp ht
      split
      · exact ⟨h₁.mono hle, h₂.mono hle⟩
      · exact ⟨h₁.mono hle, h₂.mono hle⟩⟩
  | .neg hl _ hF hlb hmb => ⟨(DEvalList.wf hl).1.append hF, fun hΔ hκ => by
      have h₁ := ((DEvalList.wf hl).2 hΔ hκ _ (List.mem_cons_self ..)).2.2 _ rfl
      refine ⟨hlb, hmb, fun t ht => ?_⟩
      obtain rfl := Option.mem_some_iff.mp ht
      exact Term.Below.mono hF.le h₁⟩
  | .logb hl _ hF hlb hmb => ⟨(DEvalList.wf hl).1.append hF, fun hΔ hκ => by
      have h₁ := ((DEvalList.wf hl).2 hΔ hκ _ (List.mem_cons_self ..)).2.1
      refine ⟨hlb, hmb, fun t ht => ?_⟩
      obtain rfl := Option.mem_some_iff.mp ht
      exact h₁.mono hF.le⟩
  | .ext (n₂ := n₂) _ _ _ hl _ hF hlb hmb =>
      ⟨((DEvalList.wf hl).1.append hF).append (Fresh.single n₂ rfl), fun _ _ =>
        ⟨hlb.mono (Nat.le_succ _), hmb.mono (Nat.le_succ _), fun t ht => by
          obtain rfl := Option.mem_some_iff.mp ht
          exact Nat.lt_succ_self _⟩⟩
  | .exact hl _ => ⟨(DEvalList.wf hl).1, fun _ _ => trivial⟩
  | .len hl => ⟨(DEvalList.wf hl).1.mono_right (by omega), fun _ _ =>
      ⟨show _ < _ by omega, show _ < _ by omega, fun t ht => absurd ht (by simp)⟩⟩
  | .call _ he hs => ⟨(DEval.wf he).1.append (DExec.wf hs).1, fun hΔ hκ =>
      ((DExec.wf hs).2 (DEnv.Below.single ((DEval.wf he).2 hΔ hκ))
        (hκ.mono (DEval.wf he).1.le)).2 _ rfl⟩
termination_by structural h => h

theorem DEvalList.wf {Δ : DEnv} {κ : Option SCtx} {n₀ : ℕ} {es : List (Expr (fpy decode))}
    {ds : List DVal} {Ψ : List Con} {n₁ : ℕ} :
    DEvalList decode Φ Δ κ n₀ es ds Ψ n₁ →
      Fresh n₀ n₁ Ψ ∧ (Δ.Below n₀ → CtxBelow n₀ κ → ∀ d ∈ ds, d.Below n₁)
  | .nil => ⟨Fresh.nil _, fun _ _ _ h => absurd h List.not_mem_nil⟩
  | .cons h hs => ⟨(DEval.wf h).1.append (DEvalList.wf hs).1, fun hΔ hκ => by
      have h₀₁ := (DEval.wf h).1.le
      have hd₀ := ((DEval.wf h).2 hΔ hκ).mono (DEvalList.wf hs).1.le
      have hds := (DEvalList.wf hs).2 (hΔ.mono h₀₁) (hκ.mono h₀₁)
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hd₀
      · exact hds d hd⟩
termination_by structural h => h

theorem DEvalFields.wf {Δ : DEnv} {κ : Option SCtx} {n₀ : ℕ}
    {fs : List (Label × Expr (fpy decode))} {afs : List (Label × DVal)} {Ψ : List Con} {n₁ : ℕ} :
    DEvalFields decode Φ Δ κ n₀ fs afs Ψ n₁ →
      Fresh n₀ n₁ Ψ ∧ (Δ.Below n₀ → CtxBelow n₀ κ → DVal.BelowFields n₁ afs)
  | .nil => ⟨Fresh.nil _, fun _ _ => trivial⟩
  | .cons h hs => ⟨(DEval.wf h).1.append (DEvalFields.wf hs).1, fun hΔ hκ =>
      have h₀₁ := (DEval.wf h).1.le
      ⟨((DEval.wf h).2 hΔ hκ).mono (DEvalFields.wf hs).1.le,
        (DEvalFields.wf hs).2 (hΔ.mono h₀₁) (hκ.mono h₀₁)⟩⟩
termination_by structural h => h

theorem DExec.wf {Δ : DEnv} {κ : Option SCtx} {n₀ : ℕ} {s : Stmt (fpy decode)} {Δ' : DEnv}
    {a : Option DVal} {Ψ : List Con} {n₁ : ℕ} :
    DExec decode Φ Δ κ n₀ s Δ' a Ψ n₁ →
      Fresh n₀ n₁ Ψ ∧ (Δ.Below n₀ → CtxBelow n₀ κ → Δ'.Below n₁ ∧ RetBelow n₁ a)
  | .assign h => ⟨(DEval.wf h).1, fun hΔ hκ =>
      ⟨(hΔ.mono (DEval.wf h).1.le).update _ ((DEval.wf h).2 hΔ hκ), fun _ h => absurd h (by simp)⟩⟩
  | .skip => ⟨Fresh.nil _, fun hΔ _ => ⟨hΔ, fun _ h => absurd h (by simp)⟩⟩
  | .ret h => ⟨(DEval.wf h).1, fun hΔ hκ => by
      have hd₀ := (DEval.wf h).2 hΔ hκ
      exact ⟨hΔ.mono (DEval.wf h).1.le, fun _ hd => Option.mem_some_iff.mp hd ▸ hd₀⟩⟩
  | .assert h => ⟨(DEval.wf h).1, fun hΔ _ =>
      ⟨hΔ.mono (DEval.wf h).1.le, fun _ h => absurd h (by simp)⟩⟩
  | .seq h₁ h₂ _ _ hF ha => ⟨((DExec.wf h₁).1.append (DExec.wf h₂).1).append hF, fun hΔ hκ =>
      have h₀₁ := (DExec.wf h₁).1.le
      ⟨(((DExec.wf h₂).2 ((DExec.wf h₁).2 hΔ hκ).1 (hκ.mono h₀₁)).1).mono hF.le, ha⟩⟩
  | .ite h₁ h₂ _ _ _ _ hF hΔ' ha => ⟨((DExec.wf h₁).1.append (DExec.wf h₂).1).append hF,
      fun _ _ => ⟨hΔ', ha⟩⟩
  | .whileDo _ hFᵢ hbᵢ hs _ => ⟨hFᵢ.append (DExec.wf hs).1, fun _ hκ =>
      ⟨hbᵢ.mono (DExec.wf hs).1.le, ((DExec.wf hs).2 hbᵢ (hκ.mono hFᵢ.le)).2⟩⟩
  | .withCtx he hs => ⟨(DEval.wf he).1.append (DExec.wf hs).1, fun hΔ _ => by
      have hC₀ := (DEval.wf he).2 hΔ (ctxBelow_real _)
      exact (DExec.wf hs).2 (hΔ.mono (DEval.wf he).1.le)
        (fun C hC => Option.mem_some_iff.mp hC ▸ hC₀)⟩
  | .withUnknown he hs => ⟨(DEval.wf he).1.append (DExec.wf hs).1, fun hΔ _ =>
      (DExec.wf hs).2 (hΔ.mono (DEval.wf he).1.le) (fun _ h => absurd h (by simp))⟩
termination_by structural h => h

end

/-! ## Helpers -/

local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem args_one {ι : Asgn} {l m : Term} {τ : Option Term} {ns : List Num}
    (h : List.Forall₂ (Describes ι) [.num l m τ] (ns.map .num)) :
    ∃ u, ns = [u] ∧ NumIn ι l m τ u := by
  rcases ns with _ | ⟨u, _ | ⟨_, _⟩⟩
  · cases h
  · cases h with
    | cons h _ => cases h with
      | num h => exact ⟨u, rfl, h⟩
  · cases h with | cons _ h => cases h

theorem args_two {ι : Asgn} {l₁ m₁ l₂ m₂ : Term} {τ₁ τ₂ : Option Term} {ns : List Num}
    (h : List.Forall₂ (Describes ι) [.num l₁ m₁ τ₁, .num l₂ m₂ τ₂] (ns.map .num)) :
    ∃ u₁ u₂, ns = [u₁, u₂] ∧ NumIn ι l₁ m₁ τ₁ u₁ ∧ NumIn ι l₂ m₂ τ₂ u₂ := by
  rcases ns with _ | ⟨u₁, _ | ⟨u₂, _ | ⟨_, _⟩⟩⟩
  · cases h
  · cases h with | cons _ h => cases h
  · cases h with
    | cons h₁ h => cases h with
      | cons h₂ _ => cases h₁ with
        | num h₁ => cases h₂ with
          | num h₂ => exact ⟨u₁, u₂, rfl, h₁, h₂⟩
  · cases h with | cons _ h => cases h with | cons _ h => cases h

theorem numIns {ι : Asgn} : ∀ {Is : List (Term × Term × Option Term)} {ns : List Num},
    List.Forall₂ (Describes ι) (Is.map fun I => .num I.1 I.2.1 I.2.2) (ns.map .num) →
    List.Forall₂ (fun (I : Term × Term × Option Term) n => NumIn ι I.1 I.2.1 I.2.2 n) Is ns
  | [], [], _ => .nil
  | _ :: _, _ :: _, .cons h hs => by
    cases h with
    | num h => exact .cons h (numIns hs)
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h

theorem add_term {u₁ u₂ : Num} {a b : EInt} (h₁ : u₁ = nan ∨ u₁ = numOfE a)
    (h₂ : u₂ = nan ∨ u₂ = numOfE b) : Num.add u₁ u₂ = nan ∨ Num.add u₁ u₂ = numOfE (a + b) := by
  rcases h₁ with rfl | rfl
  · left; rcases u₂ with _ | (_ | _) <;> rfl
  · rcases h₂ with rfl | rfl
    · left; cases a using WithBotTop.rec <;> rfl
    · exact add_numOfE a b

theorem neg_term {u : Num} {a : EInt} (h : u = nan ∨ u = numOfE a) :
    Num.neg u = nan ∨ Num.neg u = numOfE (negE a) := by
  rcases h with rfl | rfl
  · exact .inl rfl
  · exact .inr (neg_numOfE a)

theorem ext_term {u₁ u₂ : Num} {a b : EInt} (ge : Bool) (h₁ : u₁ = nan ∨ u₁ = numOfE a)
    (h₂ : u₂ = nan ∨ u₂ = numOfE b) :
    (if ge then Num.max u₁ u₂ else Num.min u₁ u₂) = nan ∨
      (if ge then Num.max u₁ u₂ else Num.min u₁ u₂) = numOfE (if ge then max a b else min a b) := by
  rcases h₁ with rfl | rfl
  · left; cases ge <;> rcases u₂ with _ | (_ | _) <;> rfl
  · rcases h₂ with rfl | rfl
    · left; cases ge <;> cases a using WithBotTop.rec <;> rfl
    · right; cases ge
      · exact min_numOfE a b
      · exact max_numOfE a b

theorem logb_term {ι : Asgn} {l m : Term} {τ : Option Term} {u : Num} (h : NumIn ι l m τ u) :
    Num.logb u = nan ∨ Num.logb u = numOfE (m.eval ι) := by
  rcases h with rfl | ⟨-, hm, -⟩
  · exact .inl rfl
  · by_cases hu : u = nan
    · subst hu; exact .inl rfl
    · exact .inr (by rw [logb_eq hu, hm])

theorem admits_real {ι : Asgn} {C : Val} (h : ∀ K ∈ some SCtx.real, K.Admits ι C) : C = .real :=
  h _ rfl

theorem admits_real' (ι : Asgn) : ∀ K ∈ some SCtx.real, K.Admits ι .real :=
  fun K hK => by obtain rfl := Option.mem_some_iff.mp hK; rfl

/-- The end of `s₁; s₂`: the outcome of `s₂`, with the return bounds joined. -/
theorem within_seq {n₂ n₃ : ℕ} {Ψ : List Con} {ι : Asgn} {Δ : DEnv} {a₂ a : Option DVal}
    {o : Outcome} (hw : Within ι Δ a₂ o) (hΔ : Δ.Below n₂) (hF : Fresh n₂ n₃ Ψ)
    (hra : RetLe n₂ n₃ Ψ a₂ a) : ∃ ι', Agree n₂ ι ι' ∧ Sat ι' Ψ ∧ Within ι' Δ a o := by
  cases o with
  | normal σ =>
    obtain ⟨ι', h, hs⟩ := Sat.extend hF ι
    exact ⟨ι', h, hs, DEnv.Holds.congr h hΔ hw⟩
  | ret v =>
    obtain ⟨d, hd, hv⟩ := hw
    obtain ⟨d', hd', hle⟩ := hra d hd
    obtain ⟨ι', h, hs, hv'⟩ := hle ι v hv
    exact ⟨ι', h.agree, hs, d', hd', hv'⟩

/-- The end of a branch: its outcome, with environments and return bounds joined. -/
theorem within_join {n₂ n₃ : ℕ} {Ψ : List Con} {ι : Asgn} {Δ₁ Δ' : DEnv} {a₁ a : Option DVal}
    {o : Outcome} (hw : Within ι Δ₁ a₁ o) (hle : DEnv.Le n₂ n₃ Ψ Δ₁ Δ') (hra : RetLe n₂ n₃ Ψ a₁ a) :
    ∃ ι', Agree n₂ ι ι' ∧ Sat ι' Ψ ∧ Within ι' Δ' a o := by
  cases o with
  | normal σ =>
    obtain ⟨ι', h, hs, hσ⟩ := hle ι σ hw
    exact ⟨ι', h.agree, hs, hσ⟩
  | ret v =>
    obtain ⟨d, hd, hv⟩ := hw
    obtain ⟨d', hd', hle'⟩ := hra d hd
    obtain ⟨ι', h, hs, hv'⟩ := hle' ι v hv
    exact ⟨ι', h.agree, hs, d', hd', hv'⟩

/-- Composes two steps of a prefix-form soundness proof. -/
theorem chain {P : Asgn → Prop} {n₀ n₁ : ℕ} {Ψ Ψ' : List Con} {ι ι₁ ι₂ : Asgn}
    (hF : Fresh n₀ n₁ Ψ) (a₁ : Agree n₀ ι ι₁) (hs₁ : Sat ι₁ Ψ) (a₂ : Agree n₁ ι₁ ι₂)
    (hs₂ : Sat ι₂ Ψ') (h : P ι₂) : ∃ ι', Agree n₀ ι ι' ∧ Sat ι' (Ψ ++ Ψ') ∧ P ι' :=
  ⟨ι₂, a₁.trans (a₂.mono hF.le), (Sat.congr hF a₂ hs₁).append hs₂, h⟩

/-! ## Integer rules

Each takes the soundness of the argument list. -/

section Rules

variable {Δ : DEnv} {n₀ n₁ n₂ : ℕ} {Ψ Ψ' : List Con} {ι : Asgn} {C : Val} {ns : List Num}
  {u : Num} {r : Num → Num} {l m l₁ m₁ l₂ m₂ τ₁ τ₂ : Term}

/-- D-Linear. -/
theorem linear_sound {op : ArithOp} {e₁ e₂ : Expr (fpy decode)} (hop' : op = .add ∨ op = .sub)
    (hdl : DEvalList decode Φ Δ (some .real) n₀ [e₁, e₂]
      [.num l₁ m₁ (some τ₁), .num l₂ m₂ (some τ₂)] Ψ n₁)
    (hok : ArithOK decode (some .real) op [(l₁, m₁, some τ₁), (l₂, m₂, some τ₂)] n₁ n₂ Ψ' l m)
    (hΔ : Δ.Below n₀)
    (hop : (fpy decode).arith op ns = some u) (hr : C.rnd (fpy decode) = some r)
    (hC : ∀ K ∈ some SCtx.real, K.Admits ι C)
    (ih : ∃ ι₁, Agree n₀ ι ι₁ ∧ Sat ι₁ Ψ ∧
      List.Forall₂ (Describes ι₁) [.num l₁ m₁ (some τ₁), .num l₂ m₂ (some τ₂)] (ns.map .num)) :
    ∃ ι', Agree n₀ ι ι' ∧ Sat ι' (Ψ ++ Ψ') ∧ Describes ι'
      (.num l m (some (if op = .add then .add τ₁ τ₂ else .add τ₁ (.neg τ₂)))) (.num (r u)) := by
  obtain ⟨ι₁, a₁, hs₁, hds⟩ := ih
  obtain rfl := admits_real hC
  obtain rfl : _ = id := (Option.some.inj hr).symm
  have hb := (DEvalList.wf hdl).2 hΔ (ctxBelow_real _)
  have hτ₁ := (hb _ (List.mem_cons_self ..)).2.2 _ rfl
  have hτ₂ := (hb _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))).2.2 _ rfl
  obtain ⟨u₁, u₂, rfl, hu₁, hu₂⟩ := args_two hds
  obtain ⟨ι₂, a₂, hs₂, hu⟩ := hok ι₁ _ _ _ _ (.cons hu₁ (.cons hu₂ .nil)) hop
    (admits_real' _) rfl
  have e₁ := Term.eval_congr a₂.agree hτ₁
  have e₂ := Term.eval_congr a₂.agree hτ₂
  refine chain (DEvalList.wf hdl).1 a₁ hs₁ a₂.agree hs₂ (.num ?_)
  rcases hop' with rfl | rfl
  · simp only [fpy, ArithOp.eval, Option.some.injEq] at hop
    subst hop
    rw [if_pos rfl]
    refine hu.withTerm ?_
    simp only [Term.eval, ← e₁, ← e₂]
    exact add_term hu₁.term hu₂.term
  · simp only [fpy, ArithOp.eval, Option.some.injEq] at hop
    subst hop
    rw [if_neg (by decide)]
    refine hu.withTerm ?_
    simp only [Term.eval, ← e₁, ← e₂]
    exact add_term hu₁.term (neg_term hu₂.term)

/-- D-Neg. -/
theorem neg_sound {e : Expr (fpy decode)} {τ : Term}
    (hdl : DEvalList decode Φ Δ (some .real) n₀ [e] [.num l₁ m₁ (some τ)] Ψ n₁)
    (hok : ArithOK decode (some .real) .neg [(l₁, m₁, some τ)] n₁ n₂ Ψ' l m) (hΔ : Δ.Below n₀)
    (hop : (fpy decode).arith .neg ns = some u) (hr : C.rnd (fpy decode) = some r)
    (hC : ∀ K ∈ some SCtx.real, K.Admits ι C)
    (ih : ∃ ι₁, Agree n₀ ι ι₁ ∧ Sat ι₁ Ψ ∧
      List.Forall₂ (Describes ι₁) [.num l₁ m₁ (some τ)] (ns.map .num)) :
    ∃ ι', Agree n₀ ι ι' ∧ Sat ι' (Ψ ++ Ψ') ∧
      Describes ι' (.num l m (some (.neg τ))) (.num (r u)) := by
  obtain ⟨ι₁, a₁, hs₁, hds⟩ := ih
  obtain rfl := admits_real hC
  obtain rfl : _ = id := (Option.some.inj hr).symm
  have hτ := ((DEvalList.wf hdl).2 hΔ (ctxBelow_real _) _ (List.mem_cons_self ..)).2.2 _ rfl
  obtain ⟨u₁, rfl, hu₁⟩ := args_one hds
  obtain ⟨ι₂, a₂, hs₂, hu⟩ := hok ι₁ _ _ _ _ (.cons hu₁ .nil) hop (admits_real' _) rfl
  refine chain (DEvalList.wf hdl).1 a₁ hs₁ a₂.agree hs₂ (.num ?_)
  simp only [fpy, ArithOp.eval, Option.some.injEq] at hop
  subst hop
  refine hu.withTerm ?_
  simp only [Term.eval, ← Term.eval_congr a₂.agree hτ]
  exact neg_term hu₁.term

/-- D-Logb. -/
theorem logb_sound {e : Expr (fpy decode)} {τ : Option Term}
    (hdl : DEvalList decode Φ Δ (some .real) n₀ [e] [.num l₁ m₁ τ] Ψ n₁)
    (hok : ArithOK decode (some .real) .logb [(l₁, m₁, τ)] n₁ n₂ Ψ' l m) (hΔ : Δ.Below n₀)
    (hop : (fpy decode).arith .logb ns = some u) (hr : C.rnd (fpy decode) = some r)
    (hC : ∀ K ∈ some SCtx.real, K.Admits ι C)
    (ih : ∃ ι₁, Agree n₀ ι ι₁ ∧ Sat ι₁ Ψ ∧
      List.Forall₂ (Describes ι₁) [.num l₁ m₁ τ] (ns.map .num)) :
    ∃ ι', Agree n₀ ι ι' ∧ Sat ι' (Ψ ++ Ψ') ∧ Describes ι' (.num l m (some m₁)) (.num (r u)) := by
  obtain ⟨ι₁, a₁, hs₁, hds⟩ := ih
  obtain rfl := admits_real hC
  obtain rfl : _ = id := (Option.some.inj hr).symm
  have hm := ((DEvalList.wf hdl).2 hΔ (ctxBelow_real _) _ (List.mem_cons_self ..)).2.1
  obtain ⟨u₁, rfl, hu₁⟩ := args_one hds
  obtain ⟨ι₂, a₂, hs₂, hu⟩ := hok ι₁ _ _ _ _ (.cons hu₁ .nil) hop (admits_real' _) rfl
  refine chain (DEvalList.wf hdl).1 a₁ hs₁ a₂.agree hs₂ (.num ?_)
  simp only [fpy, ArithOp.eval, Option.some.injEq] at hop
  subst hop
  refine hu.withTerm ?_
  rw [← Term.eval_congr a₂.agree hm]
  exact logb_term hu₁

/-- D-Max and D-Min: the fresh `val(e)` is the max (min) of the arguments' values. -/
theorem ext_sound {op : ArithOp} {ge : Bool} {e₁ e₂ : Expr (fpy decode)}
    (hop' : op = (if ge then .max else .min)) (hτ₁ : τ₁.Below n₂) (hτ₂ : τ₂.Below n₂)
    (hdl : DEvalList decode Φ Δ (some .real) n₀ [e₁, e₂]
      [.num l₁ m₁ (some τ₁), .num l₂ m₂ (some τ₂)] Ψ n₁)
    (hok : ArithOK decode (some .real) op [(l₁, m₁, some τ₁), (l₂, m₂, some τ₂)] n₁ n₂ Ψ' l m)
    (hF : Fresh n₁ n₂ Ψ') (hlb : l.Below n₂) (hmb : m.Below n₂) (hΔ : Δ.Below n₀)
    (hop : (fpy decode).arith op ns = some u) (hr : C.rnd (fpy decode) = some r)
    (hC : ∀ K ∈ some SCtx.real, K.Admits ι C)
    (ih : ∃ ι₁, Agree n₀ ι ι₁ ∧ Sat ι₁ Ψ ∧
      List.Forall₂ (Describes ι₁) [.num l₁ m₁ (some τ₁), .num l₂ m₂ (some τ₂)] (ns.map .num)) :
    ∃ ι', Agree n₀ ι ι' ∧ Sat ι' (Ψ ++ Ψ' ++ [Con.ext n₂ ge τ₁ τ₂ hτ₁ hτ₂]) ∧
      Describes ι' (.num l m (some (.var n₂))) (.num (r u)) := by
  obtain ⟨ι₁, a₁, hs₁, hds⟩ := ih
  obtain rfl := admits_real hC
  obtain rfl : _ = id := (Option.some.inj hr).symm
  have hF₁ := (DEvalList.wf hdl).1
  obtain ⟨u₁, u₂, rfl, hu₁, hu₂⟩ := args_two hds
  obtain ⟨ι₂, a₂, hs₂, hu⟩ := hok ι₁ _ _ _ _ (.cons hu₁ (.cons hu₂ .nil)) hop
    (admits_real' _) rfl
  have hb := (DEvalList.wf hdl).2 hΔ (ctxBelow_real _)
  have hτ₁' := (hb _ (List.mem_cons_self ..)).2.2 _ rfl
  have hτ₂' := (hb _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))).2.2 _ rfl
  let z : EInt := if ge then max (τ₁.eval ι₁) (τ₂.eval ι₁) else min (τ₁.eval ι₁) (τ₂.eval ι₁)
  let ι₃ := Function.update ι₂ n₂ z
  have a₃ : Agree n₂ ι₂ ι₃ := fun x hx => (Function.update_of_ne hx.ne _ _).symm
  have f₁ : τ₁.eval ι₃ = τ₁.eval ι₁ :=
    (Term.eval_congr a₃ hτ₁).symm.trans (Term.eval_congr a₂.agree hτ₁').symm
  have f₂ : τ₂.eval ι₃ = τ₂.eval ι₁ :=
    (Term.eval_congr a₃ hτ₂).symm.trans (Term.eval_congr a₂.agree hτ₂').symm
  have hz : ι₃ n₂ = z := Function.update_self ..
  have a₂₃ : Agree n₁ ι₁ ι₃ := a₂.agree.trans (a₃.mono hF.le)
  refine ⟨ι₃, a₁.trans (a₂₃.mono hF₁.le), ?_, .num ?_⟩
  · refine ((Sat.congr hF₁ a₂₃ hs₁).append (Sat.congr hF a₃ hs₂)).append ?_
    intro c hc
    obtain rfl := List.mem_singleton.mp hc
    simp only [Con.ext]
    rw [f₁, f₂, hz]
    cases ge
    · exact ⟨min_le_left _ _, min_le_right _ _⟩
    · exact ⟨le_max_left _ _, le_max_right _ _⟩
  · refine (hu.congr a₃ hlb hmb (fun _ h => absurd h (by simp))).withTerm ?_
    simp only [Term.eval, hz]
    cases ge <;> simp only [Bool.false_eq_true, if_false, if_true] at hop' <;> subst hop' <;>
      simp only [fpy, ArithOp.eval, Option.some.injEq] at hop <;> subst hop
    · exact ext_term false hu₁.term hu₂.term
    · exact ext_term true hu₁.term hu₂.term

end Rules

/-! ## Theorem 4.2 -/

mutual

/-- **Theorem 4.2** (soundness of digit-bound analysis), in prefix form. If
`Δ, κ ⊢♮ e : d` with fresh variables from `n₀`, `ι` describes the store and `κ`
the context, and `⟨σ, C, e⟩ ⇓ v`, then an assignment agreeing with `ι` below
`n₀` satisfies the derivation's constraints and describes `v` by `d`. -/
theorem eval_sound {σ : Store} {C : Val} {e : Expr (fpy decode)} {v : Val} :
    Eval Φ σ C e v → ∀ {Δ κ n₀ d Ψ n₁ ι}, DEval decode Φ Δ κ n₀ e d Ψ n₁ → Δ.Below n₀ →
      CtxBelow n₀ κ → Δ.Holds ι σ → (∀ K ∈ κ, K.Admits ι C) →
      ∃ ι', Agree n₀ ι ι' ∧ Sat ι' Ψ ∧ Describes ι' d v
  | .bool, _, _, _, _, _, _, ι, .bool, _, _, _, _ =>
      ⟨ι, Agree.refl _ _, fun _ h => absurd h List.not_mem_nil, .bool⟩
  | .num, _, _, _, _, _, _, ι, .const hτ, _, _, _, _ =>
      ⟨ι, Agree.refl _ _, fun _ h => absurd h List.not_mem_nil, .num (.inr ⟨rfl, rfl, fun t ht => by
        obtain ⟨z, rfl, hz⟩ := hτ t ht
        exact hz⟩)⟩
  | .real, _, _, _, _, _, _, ι, .real, _, _, _, _ =>
      ⟨ι, Agree.refl _ _, fun _ h => absurd h List.not_mem_nil, .sctx rfl⟩
  | .var hx, _, _, _, _, _, _, ι, .var hΔx, _, _, hσ, _ => by
      obtain ⟨v', hv', hd⟩ := hσ _ _ hΔx
      exact ⟨ι, Agree.refl _ _, fun _ h => absurd h List.not_mem_nil,
        (Option.some.inj (hv'.symm.trans hx)) ▸ hd⟩
  | .list hl, _, _, _, _, _, _, _, .list hdl hle hF, hΔ, hκ, hσ, hC => by
      obtain ⟨ι₁, h₁, hs₁, hds⟩ := evalList_sound hl hdl hΔ hκ hσ hC
      have hF₁ := (DEvalList.wf hdl).1
      obtain ⟨ι₂, h₂, hs₂⟩ := Sat.extend hF ι₁
      exact chain hF₁ h₁ hs₁ h₂ hs₂ (.list (describesAll_of_le hds hle))
  | .index h₁ h₂ hk, _, _, _, _, _, _, _, .index hd₁ hd₂ hcopy hF _, hΔ, hκ, hσ, hC => by
      have hF₁ := (DEval.wf hd₁).1
      have hF₂ := (DEval.wf hd₂).1
      obtain ⟨ι₁, a₁, hs₁, hl⟩ := eval_sound h₁ hd₁ hΔ hκ hσ hC
      cases hl with
      | list hall =>
        obtain ⟨ι₀, hv₀⟩ := hall.mem (List.mem_of_getElem? hk)
        obtain ⟨ι₂, a₂, hs₂, -⟩ := eval_sound h₂ hd₂ (hΔ.mono hF₁.le) (hκ.mono hF₁.le)
          (hσ.congr a₁ hΔ) (admits_congr a₁ hκ hC)
        obtain ⟨ι₃, a₃, hs₃, hv⟩ := hcopy ι₀ ι₂ _ hv₀
        have a₃' := a₃.agree
        exact ⟨ι₃, a₁.trans ((a₂.trans (a₃'.mono hF₂.le)).mono hF₁.le),
          ((Sat.congr hF₁ (a₂.trans (a₃'.mono hF₂.le)) hs₁).append
            (Sat.congr hF₂ a₃' hs₂)).append hs₃, hv⟩
  | .record hf, _, _, _, _, _, _, _, .record hdf, hΔ, hκ, hσ, hC => by
      obtain ⟨ι₁, a₁, hs₁, hfs⟩ := evalFields_sound hf hdf hΔ hκ hσ hC
      exact ⟨ι₁, a₁, hs₁, .record hfs⟩
  | .proj h hl, _, _, _, _, _, _, _, .proj hd hal, hΔ, hκ, hσ, hC => by
      obtain ⟨ι₁, a₁, hs₁, hr⟩ := eval_sound h hd hΔ hκ hσ hC
      cases hr with
      | record hfs => exact ⟨ι₁, a₁, hs₁, hfs.lookup hal hl⟩
  | .ctx h _, _, _, _, _, _, _, _, .ctx (d := d) hd, hΔ, hκ, hσ, hC => by
      obtain ⟨ι₁, a₁, hs₁, hr⟩ := eval_sound h hd hΔ hκ hσ hC
      refine ⟨ι₁, a₁, hs₁, ?_⟩
      cases hc : ctxOf d with
      | none => exact .ctxv
      | some C' => exact .sctx (ctxOf_admits hr hc)
  | .arith hl hop hr, _, _, _, _, _, _, _, .arith hdl hok hF _ _, hΔ, hκ, hσ, hC => by
      obtain ⟨ι₁, a₁, hs₁, hds⟩ := evalList_sound hl hdl hΔ hκ hσ hC
      have hF₁ := (DEvalList.wf hdl).1
      obtain ⟨ι₂, a₂, hs₂, hu⟩ := hok ι₁ _ _ _ _ (numIns hds) hop (admits_congr a₁ hκ hC) hr
      exact chain hF₁ a₁ hs₁ a₂.agree hs₂ (.num hu)
  | .arith hl hop hr, _, _, _, _, _, _, _, .linear hop' hdl hok _ _ _, hΔ, hκ, hσ, hC =>
      linear_sound hop' hdl hok hΔ hop hr hC (evalList_sound hl hdl hΔ hκ hσ hC)
  | .arith hl hop hr, _, _, _, _, _, _, _, .neg hdl hok _ _ _, hΔ, hκ, hσ, hC =>
      neg_sound hdl hok hΔ hop hr hC (evalList_sound hl hdl hΔ hκ hσ hC)
  | .arith hl hop hr, _, _, _, _, _, _, _, .logb hdl hok _ _ _, hΔ, hκ, hσ, hC =>
      logb_sound hdl hok hΔ hop hr hC (evalList_sound hl hdl hΔ hκ hσ hC)
  | .arith hl hop hr, _, _, _, _, _, _, _, .ext hop' hτ₁ hτ₂ hdl hok hF hlb hmb, hΔ, hκ, hσ, hC =>
      ext_sound hop' hτ₁ hτ₂ hdl hok hF hlb hmb hΔ hop hr hC (evalList_sound hl hdl hΔ hκ hσ hC)
  | .exact hl hop, _, _, _, _, _, _, _, .exact hdl hne, hΔ, hκ, hσ, hC => by
      obtain ⟨ι₁, a₁, hs₁, -⟩ := evalList_sound hl hdl hΔ hκ hσ hC
      obtain ⟨b, rfl⟩ := ExactOp.eval_bool hop hne
      exact ⟨ι₁, a₁, hs₁, .bool⟩
  | .exact hl hop, _, _, _, _, _, _, _, .len (n₁ := n₁) hdl, hΔ, hκ, hσ, hC => by
      obtain ⟨ι₁, a₁, hs₁, -⟩ := evalList_sound hl hdl hΔ hκ hσ hC
      have hF₁ := (DEvalList.wf hdl).1
      obtain ⟨k, rfl⟩ := ExactOp.eval_len hop
      let ι₂ := Function.update (Function.update ι₁ n₁ (lsbOf (.finite k))) (n₁ + 1)
        (msbOf (.finite k))
      have a₂ : Agree n₁ ι₁ ι₂ := fun x hx => by
        simp only [ι₂, Function.update_of_ne (show x ≠ n₁ + 1 by omega),
          Function.update_of_ne (show x ≠ n₁ by omega)]
      refine ⟨ι₂, a₁.trans (a₂.mono hF₁.le), Sat.congr hF₁ a₂ hs₁, .num (.inr ⟨?_, ?_, ?_⟩)⟩
      · simp [ι₂, Term.eval]
      · simp [ι₂, Term.eval]
      · intro t ht; exact absurd ht (by simp)
  | .call hΦ he hs, _, _, _, _, _, _, _, .call hΦ' hd hbody, hΔ, hκ, hσ, hC => by
      rw [hΦ] at hΦ'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hΦ')
      have hF₁ := (DEval.wf hd).1
      obtain ⟨ι₁, a₁, hs₁, hv⟩ := eval_sound he hd hΔ hκ hσ hC
      obtain ⟨ι₂, a₂, hs₂, d', hd', hv'⟩ := exec_sound hs hbody
        (DEnv.Below.single ((DEval.wf hd).2 hΔ hκ)) (hκ.mono hF₁.le) (DEnv.Holds.single hv)
        (admits_congr a₁ hκ hC)
      obtain rfl := Option.mem_some_iff.mp hd'
      exact chain hF₁ a₁ hs₁ a₂ hs₂ hv'
termination_by structural h => h

theorem evalList_sound {σ : Store} {C : Val} {es : List (Expr (fpy decode))} {vs : List Val} :
    EvalList Φ σ C es vs → ∀ {Δ κ n₀ ds Ψ n₁ ι}, DEvalList decode Φ Δ κ n₀ es ds Ψ n₁ →
      Δ.Below n₀ → CtxBelow n₀ κ → Δ.Holds ι σ → (∀ K ∈ κ, K.Admits ι C) →
      ∃ ι', Agree n₀ ι ι' ∧ Sat ι' Ψ ∧ List.Forall₂ (Describes ι') ds vs
  | .nil, _, _, _, _, _, _, ι, .nil, _, _, _, _ =>
      ⟨ι, Agree.refl _ _, fun _ h => absurd h List.not_mem_nil, .nil⟩
  | .cons h hs, _, _, _, _, _, _, _, .cons hd hds, hΔ, hκ, hσ, hC => by
      have hF₁ := (DEval.wf hd).1
      obtain ⟨ι₁, a₁, hs₁, hv⟩ := eval_sound h hd hΔ hκ hσ hC
      obtain ⟨ι₂, a₂, hs₂, hvs⟩ := evalList_sound hs hds (hΔ.mono hF₁.le) (hκ.mono hF₁.le)
        (hσ.congr a₁ hΔ) (admits_congr a₁ hκ hC)
      exact chain hF₁ a₁ hs₁ a₂ hs₂ (.cons (hv.congr a₂ ((DEval.wf hd).2 hΔ hκ)) hvs)
termination_by structural h => h

theorem evalFields_sound {σ : Store} {C : Val} {fs : List (Label × Expr (fpy decode))}
    {vs : List (Label × Val)} :
    EvalFields Φ σ C fs vs → ∀ {Δ κ n₀ afs Ψ n₁ ι}, DEvalFields decode Φ Δ κ n₀ fs afs Ψ n₁ →
      Δ.Below n₀ → CtxBelow n₀ κ → Δ.Holds ι σ → (∀ K ∈ κ, K.Admits ι C) →
      ∃ ι', Agree n₀ ι ι' ∧ Sat ι' Ψ ∧ DescribesFields ι' afs vs
  | .nil, _, _, _, _, _, _, ι, .nil, _, _, _, _ =>
      ⟨ι, Agree.refl _ _, fun _ h => absurd h List.not_mem_nil, .nil⟩
  | .cons h hs, _, _, _, _, _, _, _, .cons hd hds, hΔ, hκ, hσ, hC => by
      have hF₁ := (DEval.wf hd).1
      obtain ⟨ι₁, a₁, hs₁, hv⟩ := eval_sound h hd hΔ hκ hσ hC
      obtain ⟨ι₂, a₂, hs₂, hvs⟩ := evalFields_sound hs hds (hΔ.mono hF₁.le) (hκ.mono hF₁.le)
        (hσ.congr a₁ hΔ) (admits_congr a₁ hκ hC)
      exact chain hF₁ a₁ hs₁ a₂ hs₂ (.cons (hv.congr a₂ ((DEval.wf hd).2 hΔ hκ)) hvs)
termination_by structural h => h

theorem exec_sound {σ : Store} {C : Val} {s : Stmt (fpy decode)} {o : Outcome} :
    Exec Φ σ C s o → ∀ {Δ κ n₀ Δ' a Ψ n₁ ι}, DExec decode Φ Δ κ n₀ s Δ' a Ψ n₁ →
      Δ.Below n₀ → CtxBelow n₀ κ → Δ.Holds ι σ → (∀ K ∈ κ, K.Admits ι C) →
      ∃ ι', Agree n₀ ι ι' ∧ Sat ι' Ψ ∧ Within ι' Δ' a o
  | .assign he, _, _, _, _, _, _, _, _, .assign hd, hΔ, hκ, hσ, hC => by
      obtain ⟨ι₁, a₁, hs₁, hv⟩ := eval_sound he hd hΔ hκ hσ hC
      exact ⟨ι₁, a₁, hs₁, (hσ.congr a₁ hΔ).update _ hv⟩
  | .skip, _, _, _, _, _, _, _, ι, .skip, _, _, hσ, _ =>
      ⟨ι, Agree.refl _ _, fun _ h => absurd h List.not_mem_nil, hσ⟩
  | .ret he, _, _, _, _, _, _, _, _, .ret hd, hΔ, hκ, hσ, hC => by
      obtain ⟨ι₁, a₁, hs₁, hv⟩ := eval_sound he hd hΔ hκ hσ hC
      exact ⟨ι₁, a₁, hs₁, _, rfl, hv⟩
  | .assert he, _, _, _, _, _, _, _, _, .assert hd, hΔ, hκ, hσ, hC => by
      obtain ⟨ι₁, a₁, hs₁, -⟩ := eval_sound he hd hΔ hκ hσ hC
      exact ⟨ι₁, a₁, hs₁, hσ.congr a₁ hΔ⟩
  | .seqNormal h₁ h₂, _, _, _, _, _, _, _, _, .seq hd₁ hd₂ _ hra₂ hF _, hΔ, hκ, hσ, hC => by
      have hF₁ := (DExec.wf hd₁).1
      have hF₂ := (DExec.wf hd₂).1
      have hb₁ := (DExec.wf hd₁).2 hΔ hκ
      have hb₂ := (DExec.wf hd₂).2 hb₁.1 (hκ.mono hF₁.le)
      obtain ⟨ι₁, a₁, hs₁, hw₁⟩ := exec_sound h₁ hd₁ hΔ hκ hσ hC
      obtain ⟨ι₂, a₂, hs₂, hw₂⟩ := exec_sound h₂ hd₂ hb₁.1 (hκ.mono hF₁.le) hw₁
        (admits_congr a₁ hκ hC)
      obtain ⟨ι₃, a₃, hs₃, hw⟩ := within_seq hw₂ hb₂.1 hF hra₂
      have a₂₃ := a₂.trans (a₃.mono hF₂.le)
      exact ⟨ι₃, a₁.trans (a₂₃.mono hF₁.le),
        ((Sat.congr hF₁ a₂₃ hs₁).append (Sat.congr hF₂ a₃ hs₂)).append hs₃, hw⟩
  | .seqRet h₁, _, _, _, _, _, _, _, _, .seq hd₁ hd₂ hra₁ _ hF _, hΔ, hκ, hσ, hC => by
      have hF₁ := (DExec.wf hd₁).1
      have hF₂ := (DExec.wf hd₂).1
      have hb₁ := (DExec.wf hd₁).2 hΔ hκ
      obtain ⟨ι₁, a₁, hs₁, hw₁⟩ := exec_sound h₁ hd₁ hΔ hκ hσ hC
      obtain ⟨ι₂, a₂, hs₂⟩ := Sat.extend hF₂ ι₁
      obtain ⟨d, hd, hv⟩ := hw₁
      obtain ⟨d', hd', hle⟩ := hra₁ d hd
      obtain ⟨ι₃, a₃, hs₃, hv'⟩ := hle ι₂ _ (hv.congr a₂ (hb₁.2 d hd))
      have a₂₃ := a₂.trans (a₃.agree.mono hF₂.le)
      exact ⟨ι₃, a₁.trans (a₂₃.mono hF₁.le),
        ((Sat.congr hF₁ a₂₃ hs₁).append (Sat.congr hF₂ a₃.agree hs₂)).append hs₃, d', hd', hv'⟩
  | .iteTrue _ h₁, _, _, _, _, _, _, _, _, .ite hd₁ hd₂ hle₁ _ hra₁ _ hF _ _, hΔ, hκ, hσ, hC => by
      have hF₁ := (DExec.wf hd₁).1
      have hF₂ := (DExec.wf hd₂).1
      have hb₁ := (DExec.wf hd₁).2 hΔ hκ
      obtain ⟨ι₁, a₁, hs₁, hw₁⟩ := exec_sound h₁ hd₁ hΔ hκ hσ hC
      obtain ⟨ι₂, a₂, hs₂⟩ := Sat.extend hF₂ ι₁
      obtain ⟨ι₃, a₃, hs₃, hw⟩ := within_join (hw₁.congr a₂ hb₁.1 hb₁.2) hle₁ hra₁
      have a₂₃ := a₂.trans (a₃.mono hF₂.le)
      exact ⟨ι₃, a₁.trans (a₂₃.mono hF₁.le),
        ((Sat.congr hF₁ a₂₃ hs₁).append (Sat.congr hF₂ a₃ hs₂)).append hs₃, hw⟩
  | .iteFalse _ h₂, _, _, _, _, _, _, _, ι, .ite hd₁ hd₂ _ hle₂ _ hra₂ hF _ _, hΔ, hκ, hσ, hC => by
      have hF₁ := (DExec.wf hd₁).1
      have hF₂ := (DExec.wf hd₂).1
      obtain ⟨ι₁, a₁, hs₁⟩ := Sat.extend hF₁ ι
      obtain ⟨ι₂, a₂, hs₂, hw₂⟩ := exec_sound h₂ hd₂ (hΔ.mono hF₁.le) (hκ.mono hF₁.le)
        (hσ.congr a₁ hΔ) (admits_congr a₁ hκ hC)
      obtain ⟨ι₃, a₃, hs₃, hw⟩ := within_join hw₂ hle₂ hra₂
      have a₂₃ := a₂.trans (a₃.mono hF₂.le)
      exact ⟨ι₃, a₁.trans (a₂₃.mono hF₁.le),
        ((Sat.congr hF₁ a₂₃ hs₁).append (Sat.congr hF₂ a₃ hs₂)).append hs₃, hw⟩
  | .whileFalse _, _, _, _, _, _, _, _, _, .whileDo hle hFᵢ hbᵢ hd _, _, _, hσ, _ => by
      have hF := (DExec.wf hd).1
      obtain ⟨ι₁, a₁, hs₁, hσ₁⟩ := hle _ _ hσ
      obtain ⟨ι₂, a₂, hs₂⟩ := Sat.extend hF ι₁
      exact chain hFᵢ a₁.agree hs₁ a₂ hs₂ (hσ₁.congr a₂ hbᵢ)
  | .whileTrue _ (.seqNormal hs hw), _, _, _, _, _, _, _, _, .whileDo hle hFᵢ hbᵢ hd hle',
      _, hκ, hσ, hC => by
      obtain ⟨ι₁, a₁, hs₁, hσ₁⟩ := hle _ _ hσ
      obtain ⟨ι₂, a₂, hs₂, hσ₂⟩ := exec_sound hs hd hbᵢ (hκ.mono hFᵢ.le) hσ₁
        (admits_congr a₁.agree hκ hC)
      obtain ⟨ι₃, a₃, hs₃, hσ₃⟩ := hle' _ _ hσ₂
      have a₁₃ := (a₁.agree.trans (a₂.mono hFᵢ.le)).trans a₃.agree
      obtain ⟨ι₄, a₄, hs₄, hw'⟩ := loop_sound hw rfl hFᵢ hbᵢ hd hle' hκ hσ₃ hs₃
        (admits_congr a₁₃ hκ hC)
      exact ⟨ι₄, a₁₃.trans a₄, hs₄, hw'⟩
  | .whileTrue _ (.seqRet hs), _, _, _, _, _, _, _, _, .whileDo hle hFᵢ hbᵢ hd _,
      _, hκ, hσ, hC => by
      obtain ⟨ι₁, a₁, hs₁, hσ₁⟩ := hle _ _ hσ
      obtain ⟨ι₂, a₂, hs₂, hw⟩ := exec_sound hs hd hbᵢ (hκ.mono hFᵢ.le) hσ₁
        (admits_congr a₁.agree hκ hC)
      exact chain hFᵢ a₁.agree hs₁ a₂ hs₂ hw
  | .withCtx he hs, _, _, _, _, _, _, _, _, .withCtx hd hbody, hΔ, _, hσ, _ => by
      have hF₁ := (DEval.wf hd).1
      have hb := (DEval.wf hd).2 hΔ (ctxBelow_real _)
      obtain ⟨ι₁, a₁, hs₁, hv⟩ := eval_sound he hd hΔ (ctxBelow_real _) hσ (admits_real' _)
      cases hv with
      | sctx hA =>
        obtain ⟨ι₂, a₂, hs₂, hw⟩ := exec_sound hs hbody (hΔ.mono hF₁.le)
          (fun K hK => Option.mem_some_iff.mp hK ▸ hb) (hσ.congr a₁ hΔ)
          (fun K hK => Option.mem_some_iff.mp hK ▸ hA)
        exact chain hF₁ a₁ hs₁ a₂ hs₂ hw
  | .withCtx he hs, _, _, _, _, _, _, _, _, .withUnknown hd hbody, hΔ, _, hσ, _ => by
      have hF₁ := (DEval.wf hd).1
      obtain ⟨ι₁, a₁, hs₁, -⟩ := eval_sound he hd hΔ (ctxBelow_real _) hσ (admits_real' _)
      obtain ⟨ι₂, a₂, hs₂, hw⟩ := exec_sound hs hbody (hΔ.mono hF₁.le)
        (fun _ h => absurd h (by simp)) (hσ.congr a₁ hΔ) (fun _ h => absurd h (by simp))
      exact chain hF₁ a₁ hs₁ a₂ hs₂ hw
termination_by structural h => h

/-- The loop invariant: from a store `Δᵢ` describes, the rest of a loop ends in
`Δᵢ` or returns within its bound. -/
theorem loop_sound {σ : Store} {C : Val} {w : Stmt (fpy decode)} {o : Outcome} :
    Exec Φ σ C w o → ∀ {e s Δᵢ κ n₀ n₁ Ψᵢ Δ' a Ψ n₂ ι}, w = .whileDo e s →
      Fresh n₀ n₁ Ψᵢ → Δᵢ.Below n₁ → DExec decode Φ Δᵢ κ n₁ s Δ' a Ψ n₂ →
      DEnv.Le n₀ n₁ Ψᵢ Δ' Δᵢ → CtxBelow n₀ κ → Δᵢ.Holds ι σ → Sat ι Ψᵢ →
      (∀ K ∈ κ, K.Admits ι C) → ∃ ι', Agree n₀ ι ι' ∧ Sat ι' (Ψᵢ ++ Ψ) ∧ Within ι' Δᵢ a o
  | .whileFalse _, _, _, _, _, _, _, _, _, _, _, _, ι, rfl, hFᵢ, hbᵢ, hd, _, _, hσ, hsᵢ, _ => by
      have hF := (DExec.wf hd).1
      obtain ⟨ι₁, a₁, hs₁⟩ := Sat.extend hF ι
      exact ⟨ι₁, a₁.mono hFᵢ.le, (Sat.congr hFᵢ a₁ hsᵢ).append hs₁, hσ.congr a₁ hbᵢ⟩
  | .whileTrue _ (.seqNormal hs hw), _, _, _, _, _, _, _, _, _, _, _, _, rfl, hFᵢ, hbᵢ, hd, hle',
      hκ, hσ, _, hC => by
      obtain ⟨ι₂, a₂, hs₂, hσ₂⟩ := exec_sound hs hd hbᵢ (hκ.mono hFᵢ.le) hσ hC
      obtain ⟨ι₃, a₃, hs₃, hσ₃⟩ := hle' _ _ hσ₂
      have a₁₃ := (a₂.mono hFᵢ.le).trans a₃.agree
      obtain ⟨ι₄, a₄, hs₄, hw'⟩ := loop_sound hw rfl hFᵢ hbᵢ hd hle' hκ hσ₃ hs₃
        (admits_congr a₁₃ hκ hC)
      exact ⟨ι₄, a₁₃.trans a₄, hs₄, hw'⟩
  | .whileTrue _ (.seqRet hs), _, _, _, _, _, _, _, _, _, _, _, _, rfl, hFᵢ, hbᵢ, hd, _, hκ, hσ,
      hsᵢ, hC => by
      obtain ⟨ι₂, a₂, hs₂, hw⟩ := exec_sound hs hd hbᵢ (hκ.mono hFᵢ.le) hσ hC
      exact ⟨ι₂, a₂.mono hFᵢ.le, (Sat.congr hFᵢ a₂ hsᵢ).append hs₂, hw⟩
  | .assign _, _, _, _, _, _, _, _, _, _, _, _, _, h, _, _, _, _, _, _, _, _
  | .skip, _, _, _, _, _, _, _, _, _, _, _, _, h, _, _, _, _, _, _, _, _
  | .ret _, _, _, _, _, _, _, _, _, _, _, _, _, h, _, _, _, _, _, _, _, _
  | .assert _, _, _, _, _, _, _, _, _, _, _, _, _, h, _, _, _, _, _, _, _, _
  | .seqNormal _ _, _, _, _, _, _, _, _, _, _, _, _, _, h, _, _, _, _, _, _, _, _
  | .seqRet _, _, _, _, _, _, _, _, _, _, _, _, _, h, _, _, _, _, _, _, _, _
  | .iteTrue _ _, _, _, _, _, _, _, _, _, _, _, _, _, h, _, _, _, _, _, _, _, _
  | .iteFalse _ _, _, _, _, _, _, _, _, _, _, _, _, _, h, _, _, _, _, _, _, _, _
  | .withCtx _ _, _, _, _, _, _, _, _, _, _, _, _, _, h, _, _, _, _, _, _, _, _ => by cases h
termination_by structural h => h

end

/-- **Theorem 4.2** for a program (D-Program): an argument described by `d`
gives a result described by `a`. -/
theorem run_sound {f : Fn} {y : Var} {s : Stmt (fpy decode)} {d a : DVal} {Δ' : DEnv}
    {Ψ : List Con} {n₀ n₁ : ℕ} (hΦ : Φ f = some (y, s))
    (hs : DExec decode Φ (.single y d) (some .real) n₀ s Δ' (some a) Ψ n₁) (hd : d.Below n₀)
    {ι : Asgn} {v v' : Val} (hv : Describes ι d v) (hrun : Run Φ f v v') :
    ∃ ι', Agree n₀ ι ι' ∧ Sat ι' Ψ ∧ Describes ι' a v' := by
  obtain ⟨y', s', hΦ', hexec⟩ := hrun
  rw [hΦ] at hΦ'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hΦ')
  obtain ⟨ι', h, hsat, d', hd', hv'⟩ := exec_sound hexec hs (DEnv.Below.single hd)
    (ctxBelow_real _) (DEnv.Holds.single hv) (admits_real' _)
  obtain rfl := Option.mem_some_iff.mp hd'
  exact ⟨ι', h, hsat, hv'⟩

end Fpy.DigitBound
