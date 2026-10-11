import Fpy.Semantics

/-!
# Format inference (§4.2, Figure 11)

Format inference bounds every value of an FPy program by a format. It is an
abstract interpretation over any representation of formats meeting the
interface `FormatDomain`; the analysis-specific operations (`op♯`, the format
of each context, condition refinement) are an `Analysis`. Theorem 4.1
(`eval_sound`) holds whenever those operations meet the obligations in
`Analysis.Sound`.

Two rules differ from the draft, which is unsound there (see `ROADMAP.md`):

* rounding under an unknown context `?` gives `⊤`, not the exact bound;
* an abstract value can be a known context `⟨C⟩`, and `with e in s` analyzes
  `s` under the context read off `e`'s abstract value, so a context passed as
  an argument stays known.
-/

namespace Fpy

/-- The operations format inference needs on formats, with their soundness. -/
structure FormatDomain where
  Fmt : Type
  /-- The values a format contains. -/
  γ : Fmt → Set Num
  top : Fmt
  bot : Fmt
  join : Fmt → Fmt → Fmt
  /-- A containment check. -/
  sub : Fmt → Fmt → Bool
  /-- A format containing a constant. -/
  ofNum : Num → Fmt
  mem_top : ∀ n, n ∈ γ top
  mem_join_left : ∀ {F₁ F₂ n}, n ∈ γ F₁ → n ∈ γ (join F₁ F₂)
  mem_join_right : ∀ {F₁ F₂ n}, n ∈ γ F₂ → n ∈ γ (join F₁ F₂)
  sub_sound : ∀ {F₁ F₂}, sub F₁ F₂ = true → γ F₁ ⊆ γ F₂
  mem_ofNum : ∀ n, n ∈ γ (ofNum n)

variable {L : Signature} {D : FormatDomain}

/-! ## Abstract values -/

variable (D) in
/-- Abstract values: a format bounds a number, `list a` bounds every element by
`a`, records are bounded field by field, `other` (`•`) is any boolean or
context, `known C` is exactly the context `C`, and `top` is any value. -/
inductive AVal where
  | fmt (F : D.Fmt)
  | list (a : AVal)
  | record (fs : List (Label × AVal))
  | other
  | known (C : Val)
  | top

mutual

/-- `Describes a v` is `v ∈ γ(a)`. -/
inductive Describes : AVal D → Val → Prop
  | fmt {F n} : n ∈ D.γ F → Describes (.fmt F) (.num n)
  | list {a vs} : DescribesAll a vs → Describes (.list a) (.list vs)
  | record {afs fs} : DescribesFields afs fs → Describes (.record afs) (.record fs)
  | bool {b} : Describes .other (.bool b)
  | real : Describes .other .real
  | ctx {fs} : Describes .other (.ctx fs)
  | known {C} : Describes (.known C) C
  | top {v} : Describes .top v

/-- `a` describes every element of a list. -/
inductive DescribesAll : AVal D → List Val → Prop
  | nil {a} : DescribesAll a []
  | cons {a v vs} : Describes a v → DescribesAll a vs → DescribesAll a (v :: vs)

/-- Records with the same labels in order, described field by field. -/
inductive DescribesFields : List (Label × AVal D) → List (Label × Val) → Prop
  | nil : DescribesFields [] []
  | cons {l a v afs fs} : Describes a v → DescribesFields afs fs →
      DescribesFields ((l, a) :: afs) ((l, v) :: fs)

end

theorem describesAll_iff {a : AVal D} {vs : List Val} :
    DescribesAll a vs ↔ ∀ v ∈ vs, Describes a v := by
  induction vs with
  | nil => exact ⟨fun _ _ h => absurd h List.not_mem_nil, fun _ => .nil⟩
  | cons v vs ih =>
    constructor
    · rintro (_ | ⟨hv, hvs⟩) w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hv
      · exact ih.mp hvs w hw
    · intro h
      exact .cons (h v (List.mem_cons_self ..)) (ih.mpr fun w hw => h w (List.mem_cons_of_mem _ hw))

theorem DescribesFields.lookup {l : Label} {a : AVal D} {v : Val} :
    {afs : List (Label × AVal D)} → {fs : List (Label × Val)} → DescribesFields afs fs →
      afs.lookup l = some a → fs.lookup l = some v → Describes a v
  | _, _, .nil, ha, _ => by simp [List.lookup] at ha
  | _, _, .cons (l := l') hd tl, ha, hv => by
    by_cases hl : l = l'
    · subst hl
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at ha hv
      exact ha ▸ hv ▸ hd
    · have hne : (l == l') = false := by simpa using hl
      simp only [List.lookup, hne] at ha hv
      exact DescribesFields.lookup tl ha hv

/-! ### Joins -/

open Classical in
mutual

/-- The join of abstract values. Mismatched shapes give `top`. -/
noncomputable def AVal.join : AVal D → AVal D → AVal D
  | .fmt F₁, .fmt F₂ => .fmt (D.join F₁ F₂)
  | .list a₁, .list a₂ => .list (a₁.join a₂)
  | .record fs₁, .record fs₂ => (AVal.joinFields fs₁ fs₂).elim .top .record
  | .other, .other => .other
  | .known C₁, .known C₂ => if C₁ = C₂ then .known C₁ else .top
  | _, _ => .top

/-- Field-by-field join of two records with the same labels in order. -/
noncomputable def AVal.joinFields :
    List (Label × AVal D) → List (Label × AVal D) → Option (List (Label × AVal D))
  | [], [] => some []
  | (l₁, a₁) :: fs₁, (l₂, a₂) :: fs₂ =>
      if l₁ = l₂ then (AVal.joinFields fs₁ fs₂).map ((l₁, a₁.join a₂) :: ·) else none
  | _, _ => none

end

mutual

theorem Describes.join_left {a₁ : AVal D} {v : Val} (a₂ : AVal D) :
    Describes a₁ v → Describes (a₁.join a₂) v
  | .fmt h => by cases a₂ <;> first | exact .fmt (D.mem_join_left h) | exact .top
  | .list h => by
      cases a₂ with
      | list a₂ => exact .list (DescribesAll.join_left a₂ h)
      | _ => exact .top
  | .record (afs := afs) h => by
      cases a₂ with
      | record afs₂ =>
        simp only [AVal.join]
        cases hj : AVal.joinFields afs afs₂ with
        | none => exact .top
        | some fs' => exact .record (DescribesFields.join_left afs₂ h hj)
      | _ => exact .top
  | .bool => by cases a₂ <;> first | exact .bool | exact .top
  | .real => by cases a₂ <;> first | exact .real | exact .top
  | .ctx => by cases a₂ <;> first | exact .ctx | exact .top
  | .known (C := C) => by
      cases a₂ with
      | known C₂ =>
        simp only [AVal.join]
        split
        · exact .known
        · exact .top
      | _ => exact .top
  | .top => by cases a₂ <;> exact .top

theorem DescribesAll.join_left {a₁ : AVal D} {vs : List Val} (a₂ : AVal D) :
    DescribesAll a₁ vs → DescribesAll (a₁.join a₂) vs
  | .nil => .nil
  | .cons h hs => .cons (Describes.join_left a₂ h) (DescribesAll.join_left a₂ hs)

theorem DescribesFields.join_left {afs₁ : List (Label × AVal D)} {fs : List (Label × Val)}
    (afs₂ : List (Label × AVal D)) {afs : List (Label × AVal D)} :
    DescribesFields afs₁ fs → AVal.joinFields afs₁ afs₂ = some afs → DescribesFields afs fs
  | .nil, h => by
      cases afs₂ with
      | nil =>
        simp only [AVal.joinFields, Option.some.injEq] at h
        exact h ▸ .nil
      | cons _ _ => simp [AVal.joinFields] at h
  | .cons (l := l) (a := a) hd tl, h => by
      cases afs₂ with
      | nil => simp [AVal.joinFields] at h
      | cons p afs₂ =>
        obtain ⟨l₂, a₂⟩ := p
        simp only [AVal.joinFields] at h
        split at h
        · obtain ⟨rest, hj, rfl⟩ := Option.map_eq_some_iff.mp h
          exact .cons (Describes.join_left a₂ hd) (DescribesFields.join_left afs₂ tl hj)
        · simp at h

end

mutual

theorem Describes.join_right (a₁ : AVal D) {a₂ : AVal D} {v : Val} :
    Describes a₂ v → Describes (a₁.join a₂) v
  | .fmt h => by cases a₁ <;> first | exact .fmt (D.mem_join_right h) | exact .top
  | .list h => by
      cases a₁ with
      | list a₁ => exact .list (DescribesAll.join_right a₁ h)
      | _ => exact .top
  | .record (afs := afs) h => by
      cases a₁ with
      | record afs₁ =>
        simp only [AVal.join]
        cases hj : AVal.joinFields afs₁ afs with
        | none => exact .top
        | some fs' => exact .record (DescribesFields.join_right afs₁ h hj)
      | _ => exact .top
  | .bool => by cases a₁ <;> first | exact .bool | exact .top
  | .real => by cases a₁ <;> first | exact .real | exact .top
  | .ctx => by cases a₁ <;> first | exact .ctx | exact .top
  | .known (C := C) => by
      cases a₁ with
      | known C₁ =>
        simp only [AVal.join]
        split
        · next h => exact h ▸ .known
        · exact .top
      | _ => exact .top
  | .top => by cases a₁ <;> exact .top

theorem DescribesAll.join_right (a₁ : AVal D) {a₂ : AVal D} {vs : List Val} :
    DescribesAll a₂ vs → DescribesAll (a₁.join a₂) vs
  | .nil => .nil
  | .cons h hs => .cons (Describes.join_right a₁ h) (DescribesAll.join_right a₁ hs)

theorem DescribesFields.join_right (afs₁ : List (Label × AVal D))
    {afs₂ : List (Label × AVal D)} {fs : List (Label × Val)} {afs : List (Label × AVal D)} :
    DescribesFields afs₂ fs → AVal.joinFields afs₁ afs₂ = some afs → DescribesFields afs fs
  | .nil, h => by
      cases afs₁ with
      | nil =>
        simp only [AVal.joinFields, Option.some.injEq] at h
        exact h ▸ .nil
      | cons _ _ => simp [AVal.joinFields] at h
  | .cons (l := l) (a := a) hd tl, h => by
      cases afs₁ with
      | nil => simp [AVal.joinFields] at h
      | cons p afs₁ =>
        obtain ⟨l₁, a₁⟩ := p
        simp only [AVal.joinFields] at h
        split at h
        · next hl =>
          subst hl
          obtain ⟨rest, hj, rfl⟩ := Option.map_eq_some_iff.mp h
          exact .cons (Describes.join_right a₁ hd) (DescribesFields.join_right afs₁ tl hj)
        · simp at h

end

/-- The join of a list's element bounds, `a₁ ⊔ ⋯ ⊔ aₘ`; `bot` for no elements. -/
noncomputable def AVal.joinAll : List (AVal D) → AVal D
  | [] => .fmt D.bot
  | [a] => a
  | a :: as => a.join (AVal.joinAll as)

theorem describesAll_joinAll {as : List (AVal D)} {vs : List Val}
    (h : List.Forall₂ Describes as vs) : DescribesAll (AVal.joinAll as) vs := by
  induction h with
  | nil => exact .nil
  | @cons a v as vs hd tl ih =>
    cases tl with
    | nil => exact .cons hd .nil
    | cons hd' tl' =>
      refine .cons (hd.join_left _) ?_
      exact describesAll_iff.mpr fun w hw => (describesAll_iff.mp ih w hw).join_right a

/-- The format bounding a number described by `a`. -/
def AVal.toFmt : AVal D → D.Fmt
  | .fmt F => F
  | _ => D.top

theorem Describes.mem_toFmt {a : AVal D} {n : Num} (h : Describes a (.num n)) :
    n ∈ D.γ a.toFmt := by
  cases h with
  | fmt h => exact h
  | known | top => exact D.mem_top n

/-! ## Abstract environments -/

variable (D) in
/-- A format environment `Γ`. -/
abbrev AEnv := Var → Option (AVal D)

/-- `σ ∈ Γ`: every variable bound in `Γ` is bound in `σ` to a value `Γ` describes. -/
def AEnv.Holds (Γ : AEnv D) (σ : Store) : Prop :=
  ∀ x a, Γ x = some a → ∃ v, σ x = some v ∧ Describes a v

/-- `Γ ⊑ Γ'`: every store in `Γ` is in `Γ'`. -/
def AEnv.Le (Γ Γ' : AEnv D) : Prop := ∀ σ, Γ.Holds σ → Γ'.Holds σ

def AEnv.single (y : Var) (a : AVal D) : AEnv D := fun x => if x = y then some a else none

def AEnv.update (Γ : AEnv D) (x : Var) (a : AVal D) : AEnv D := Function.update Γ x (some a)

/-- The pointwise join. A variable bound on one side only is left unbound. -/
noncomputable def AEnv.join (Γ₁ Γ₂ : AEnv D) : AEnv D := fun x =>
  match Γ₁ x, Γ₂ x with
  | some a₁, some a₂ => some (a₁.join a₂)
  | _, _ => none

theorem AEnv.holds_single {y : Var} {a : AVal D} {v : Val} (h : Describes a v) :
    (AEnv.single y a).Holds (Store.single y v) := by
  intro x a' hx
  by_cases hxy : x = y
  · subst hxy
    simp only [AEnv.single, if_pos, Option.some.injEq] at hx
    subst hx
    exact ⟨v, by simp [Store.single], h⟩
  · simp [AEnv.single, hxy] at hx

theorem AEnv.Holds.update {Γ : AEnv D} {σ : Store} (hΓ : Γ.Holds σ) (x : Var)
    {a : AVal D} {v : Val} (h : Describes a v) : (Γ.update x a).Holds (σ.update x v) := by
  intro z a' hz
  by_cases hzx : z = x
  · subst hzx
    simp only [AEnv.update, Function.update_self, Option.some.injEq] at hz
    exact ⟨v, by simp [Store.update], hz ▸ h⟩
  · simp only [AEnv.update, Function.update_of_ne hzx] at hz
    simpa [Store.update, Function.update_of_ne hzx] using hΓ z a' hz

theorem AEnv.Holds.join_left {Γ₁ : AEnv D} {σ : Store} (h : Γ₁.Holds σ) (Γ₂ : AEnv D) :
    (Γ₁.join Γ₂).Holds σ := by
  intro x a hx
  simp only [AEnv.join] at hx
  split at hx
  · next a₁ a₂ h₁ _ =>
    obtain ⟨v, hv, ha⟩ := h x a₁ h₁
    exact ⟨v, hv, (Option.some.inj hx) ▸ ha.join_left a₂⟩
  · simp at hx

theorem AEnv.Holds.join_right (Γ₁ : AEnv D) {Γ₂ : AEnv D} {σ : Store} (h : Γ₂.Holds σ) :
    (Γ₁.join Γ₂).Holds σ := by
  intro x a hx
  simp only [AEnv.join] at hx
  split at hx
  · next a₁ a₂ _ h₂ =>
    obtain ⟨v, hv, ha⟩ := h x a₂ h₂
    exact ⟨v, hv, (Option.some.inj hx) ▸ ha.join_right a₁⟩
  · simp at hx

/-! ## The analysis -/

/-- The context the analysis runs under: `some C` for a known context, `none`
for the unknown context `?`. `Admits κ C` says `κ` describes `C`. -/
def Admits (κ : Option Val) (C : Val) : Prop := ∀ C₀ ∈ κ, C₀ = C

theorem admits_none (C : Val) : Admits none C := fun _ h => absurd h (by simp)

theorem admits_some (C : Val) : Admits (some C) C := fun _ h => (Option.mem_some_iff.mp h).symm

def Val.isReal : Val → Bool
  | .real => true
  | _ => false

theorem Val.eq_real_of_isReal {C : Val} (h : C.isReal = true) : C = .real := by
  cases C <;> simp_all [Val.isReal]

variable (L D) in
/-- The analysis-specific operations of format inference. -/
structure Analysis where
  /-- `op♯` for rounded operators: a format bounding the exact result. -/
  arith : L.ArithOp → List D.Fmt → D.Fmt
  /-- `op♯` for unrounded operators. -/
  exact : L.ExactOp → List (AVal D) → AVal D
  /-- `F_C`, the format of a context, when the analysis understands it. -/
  ctxFmt : Val → Option D.Fmt
  /-- The context a record's abstract value determines, if any. -/
  ctxOf : AVal D → Option Val
  /-- Condition refinement `⟦e⟧♯` (for `true`) and `⟦¬e⟧♯` (for `false`). -/
  refine : Option Val → Expr L → Bool → AEnv D → AEnv D

/-- `rnd♯_C(F)`: the bound after rounding a value bounded by `F` under `κ`.
Under `R` nothing rounds; under a known context with format `F_C`, the bound is
kept if `F ⊆ F_C` and is `F_C` otherwise; under `?` it is `⊤`. -/
def Analysis.rnd (A : Analysis L D) (κ : Option Val) (F : D.Fmt) : D.Fmt :=
  match κ with
  | none => D.top
  | some C =>
    if C.isReal then F
    else match A.ctxFmt C with
      | some FC => if D.sub F FC then F else FC
      | none => D.top

variable (A : Analysis L D) (Φ : Program L)

mutual

/-- `Γ, κ ⊢♯ e : a`. -/
inductive AEval : AEnv D → Option Val → Expr L → AVal D → Prop
  | bool {Γ κ b} : AEval Γ κ (.bool b) .other
  | num {Γ κ n} : AEval Γ κ (.num n) (.fmt (D.ofNum n))
  | real {Γ κ} : AEval Γ κ .real (.known .real)
  | var {Γ κ x a} : Γ x = some a → AEval Γ κ (.var x) a
  | list {Γ κ es as} : AEvalList Γ κ es as → AEval Γ κ (.list es) (.list (AVal.joinAll as))
  | index {Γ κ e₁ e₂ a a₂} : AEval Γ κ e₁ (.list a) → AEval Γ κ e₂ a₂ →
      AEval Γ κ (.index e₁ e₂) a
  | record {Γ κ fs afs} : AEvalFields Γ κ fs afs → AEval Γ κ (.record fs) (.record afs)
  | proj {Γ κ e afs l a} : AEval Γ κ e (.record afs) → afs.lookup l = some a →
      AEval Γ κ (.proj e l) a
  | ctx {Γ κ e a} : AEval Γ κ e a → AEval Γ κ (.ctx e) ((A.ctxOf a).elim .other .known)
  | arith {Γ κ op es as} : AEvalList Γ κ es as →
      AEval Γ κ (.arith op es) (.fmt (A.rnd κ (A.arith op (as.map AVal.toFmt))))
  | exact {Γ κ op es as} : AEvalList Γ κ es as → AEval Γ κ (.exact op es) (A.exact op as)
  | call {Γ κ f e y s a Γ' a'} : Φ f = some (y, s) → AEval Γ κ e a →
      AExec (.single y a) κ s Γ' a' → AEval Γ κ (.call f e) a'

inductive AEvalList : AEnv D → Option Val → List (Expr L) → List (AVal D) → Prop
  | nil {Γ κ} : AEvalList Γ κ [] []
  | cons {Γ κ e es a as} : AEval Γ κ e a → AEvalList Γ κ es as →
      AEvalList Γ κ (e :: es) (a :: as)

inductive AEvalFields : AEnv D → Option Val → List (Label × Expr L) →
    List (Label × AVal D) → Prop
  | nil {Γ κ} : AEvalFields Γ κ [] []
  | cons {Γ κ l e fs a afs} : AEval Γ κ e a → AEvalFields Γ κ fs afs →
      AEvalFields Γ κ ((l, e) :: fs) ((l, a) :: afs)

/-- `Γ, κ ⊢♯ s : ⟨Γ', a⟩`: `s` ends normally in `Γ'`, or returns a value
`a` describes. -/
inductive AExec : AEnv D → Option Val → Stmt L → AEnv D → AVal D → Prop
  | assign {Γ κ x e a} : AEval Γ κ e a → AExec Γ κ (.assign x e) (Γ.update x a) (.fmt D.bot)
  | skip {Γ κ} : AExec Γ κ .skip Γ (.fmt D.bot)
  | ret {Γ κ e a} : AEval Γ κ e a → AExec Γ κ (.ret e) Γ a
  | assert {Γ κ e a} : AEval Γ κ e a → AExec Γ κ (.assert e) (A.refine κ e true Γ) (.fmt D.bot)
  | seq {Γ κ s₁ s₂ Γ₁ Γ₂ a₁ a₂} : AExec Γ κ s₁ Γ₁ a₁ → AExec Γ₁ κ s₂ Γ₂ a₂ →
      AExec Γ κ (.seq s₁ s₂) Γ₂ (a₁.join a₂)
  | ite {Γ κ e s₁ s₂ Γ₁ Γ₂ a₁ a₂} : AExec (A.refine κ e true Γ) κ s₁ Γ₁ a₁ →
      AExec (A.refine κ e false Γ) κ s₂ Γ₂ a₂ →
      AExec Γ κ (.ite e s₁ s₂) (Γ₁.join Γ₂) (a₁.join a₂)
  | whileDo {Γ κ e s Γᵢ Γ' a} : Γ.Le Γᵢ → AExec (A.refine κ e true Γᵢ) κ s Γ' a → Γ'.Le Γᵢ →
      AExec Γ κ (.whileDo e s) (A.refine κ e false Γᵢ) a
  /-- The body runs under the context `e` is known to give. -/
  | withCtx {Γ κ e C s Γ' a} : AEval Γ (some .real) e (.known C) → AExec Γ (some C) s Γ' a →
      AExec Γ κ (.withCtx e s) Γ' a
  /-- The body runs under the unknown context `?`. -/
  | withUnknown {Γ κ e a₀ s Γ' a} : AEval Γ (some .real) e a₀ → AExec Γ none s Γ' a →
      AExec Γ κ (.withCtx e s) Γ' a

end

/-- The obligations under which format inference is sound: each `op♯` bounds
its operator's result, each context `C` rounds into `F_C` and leaves the values
of `F_C` unchanged, `ctxOf` names the context a record builds, and refinement
keeps every store that satisfies the condition. -/
structure Analysis.Sound : Prop where
  arith : ∀ {op ns Fs n}, List.Forall₂ (fun n F => n ∈ D.γ F) ns Fs →
    L.arith op ns = some n → n ∈ D.γ (A.arith op Fs)
  exact : ∀ {op as vs v}, List.Forall₂ Describes as vs → L.exact op vs = some v →
    Describes (A.exact op as) v
  ctxFmt : ∀ {C FC r}, A.ctxFmt C = some FC → C.rnd L = some r →
    (∀ n, r n ∈ D.γ FC) ∧ ∀ n ∈ D.γ FC, r n = n
  ctxOf : ∀ {a C fs}, A.ctxOf a = some C → Describes a (.record fs) → C = .ctx fs
  refine : ∀ {Γ κ e b σ C}, Γ.Holds σ → Admits κ C → Eval Φ σ C e (.bool b) →
    (A.refine κ e b Γ).Holds σ

/-! ## Soundness (Theorem 4.1) -/

variable {A Φ}

theorem Analysis.mem_rnd (hA : A.Sound Φ) {κ : Option Val} {C : Val} {r : Num → Num}
    {F : D.Fmt} {n : Num} (hn : n ∈ D.γ F) (hκ : Admits κ C) (hr : C.rnd L = some r) :
    r n ∈ D.γ (A.rnd κ F) := by
  cases κ with
  | none => exact D.mem_top _
  | some C₀ =>
    obtain rfl := hκ C₀ rfl
    simp only [Analysis.rnd]
    split
    · next h =>
      obtain rfl := Val.eq_real_of_isReal h
      simp only [Val.rnd, Option.some.injEq] at hr
      exact hr ▸ hn
    · split
      · next FC hFC =>
        obtain ⟨hinto, hfix⟩ := hA.ctxFmt hFC hr
        split
        · next hsub => exact (hfix n (D.sub_sound hsub hn)).symm ▸ hn
        · exact hinto n
      · exact D.mem_top _

/-- What a statement's outcome must satisfy: a normal end in `Γ'`, or a
returned value described by `a`. -/
def Outcome.Within (Γ' : AEnv D) (a : AVal D) : Outcome → Prop
  | .normal σ => Γ'.Holds σ
  | .ret v => Describes a v

theorem Outcome.Within.join {Γ₁ : AEnv D} {a₁ : AVal D} {o : Outcome}
    (h : o.Within Γ₁ a₁) (Γ₂ : AEnv D) (a₂ : AVal D) :
    o.Within (Γ₁.join Γ₂) (a₁.join a₂) := by
  cases o with
  | normal σ => exact AEnv.Holds.join_left h Γ₂
  | ret v => exact Describes.join_left a₂ h

theorem Outcome.Within.join_ret {Γ : AEnv D} {a₂ : AVal D} {o : Outcome} (a₁ : AVal D)
    (h : o.Within Γ a₂) : o.Within Γ (a₁.join a₂) := by
  cases o with
  | normal σ => exact h
  | ret v => exact Describes.join_right a₁ h

theorem Outcome.Within.join' {Γ₂ : AEnv D} {a₂ : AVal D} {o : Outcome}
    (Γ₁ : AEnv D) (a₁ : AVal D) (h : o.Within Γ₂ a₂) :
    o.Within (Γ₁.join Γ₂) (a₁.join a₂) := by
  cases o with
  | normal σ => exact AEnv.Holds.join_right Γ₁ h
  | ret v => exact Describes.join_right a₁ h

mutual

/-- **Theorem 4.1** (soundness of format inference). If `σ ∈ Γ`,
`Γ, κ ⊢♯ e : a` with `κ` describing the current context, and
`⟨σ, C, e⟩ ⇓ v`, then `v ∈ γ(a)`. -/
theorem eval_sound (hA : A.Sound Φ) {σ : Store} {C : Val} {e : Expr L} {v : Val} :
    Eval Φ σ C e v → ∀ {Γ κ a}, Γ.Holds σ → Admits κ C → AEval A Φ Γ κ e a → Describes a v
  | .bool, _, _, _, _, _, .bool => .bool
  | .num, _, _, _, _, _, .num => .fmt (D.mem_ofNum _)
  | .real, _, _, _, _, _, .real => .known
  | .var hx, _, _, _, hΓ, _, .var hΓx => by
      obtain ⟨v', hv', ha⟩ := hΓ _ _ hΓx
      exact (Option.some.inj (hx.symm.trans hv')) ▸ ha
  | .list hl, _, _, _, hΓ, hκ, .list hal =>
      .list (describesAll_joinAll (evalList_sound hA hl hΓ hκ hal))
  | .index h₁ _ hk, _, _, _, hΓ, hκ, .index ha₁ _ => by
      cases eval_sound hA h₁ hΓ hκ ha₁ with
      | list hvs => exact describesAll_iff.mp hvs _ (List.mem_of_getElem? hk)
  | .record hf, _, _, _, hΓ, hκ, .record haf => .record (evalFields_sound hA hf hΓ hκ haf)
  | .proj h hl, _, _, _, hΓ, hκ, .proj ha hal => by
      cases eval_sound hA h hΓ hκ ha with
      | record hfs => exact hfs.lookup hal hl
  | .ctx h _, _, _, _, hΓ, hκ, .ctx (a := a) ha => by
      have hd := eval_sound hA h hΓ hκ ha
      cases hc : A.ctxOf a with
      | none => exact .ctx
      | some C' => exact (hA.ctxOf hc hd) ▸ .known
  | .arith hl hop hr, _, _, _, hΓ, hκ, .arith hal => by
      have hs := List.forall₂_map_right_iff.mp (evalList_sound hA hl hΓ hκ hal)
      have hF : List.Forall₂ (fun a n => n ∈ D.γ (AVal.toFmt a)) _ _ :=
        hs.imp fun _ _ h => h.mem_toFmt
      exact .fmt (A.mem_rnd hA (hA.arith (List.forall₂_map_right_iff.mpr hF.flip) hop) hκ hr)
  | .exact hl hop, _, _, _, hΓ, hκ, .exact hal => hA.exact (evalList_sound hA hl hΓ hκ hal) hop
  | .call hΦ he hs, _, _, _, hΓ, hκ, .call hΦ' ha hs' => by
      rw [hΦ] at hΦ'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hΦ')
      exact exec_sound hA hs (AEnv.holds_single (eval_sound hA he hΓ hκ ha)) hκ hs'

theorem evalList_sound (hA : A.Sound Φ) {σ : Store} {C : Val} {es : List (Expr L)}
    {vs : List Val} :
    EvalList Φ σ C es vs → ∀ {Γ κ as}, Γ.Holds σ → Admits κ C → AEvalList A Φ Γ κ es as →
      List.Forall₂ Describes as vs
  | .nil, _, _, _, _, _, .nil => .nil
  | .cons h hs, _, _, _, hΓ, hκ, .cons ha has =>
      .cons (eval_sound hA h hΓ hκ ha) (evalList_sound hA hs hΓ hκ has)

theorem evalFields_sound (hA : A.Sound Φ) {σ : Store} {C : Val}
    {fs : List (Label × Expr L)} {vs : List (Label × Val)} :
    EvalFields Φ σ C fs vs → ∀ {Γ κ afs}, Γ.Holds σ → Admits κ C →
      AEvalFields A Φ Γ κ fs afs → DescribesFields afs vs
  | .nil, _, _, _, _, _, .nil => .nil
  | .cons h hs, _, _, _, hΓ, hκ, .cons ha has =>
      .cons (eval_sound hA h hΓ hκ ha) (evalFields_sound hA hs hΓ hκ has)

/-- Theorem 4.1 for statements: a normal end lands in `Γ'`, and a returned value
is described by `a`. -/
theorem exec_sound (hA : A.Sound Φ) {σ : Store} {C : Val} {s : Stmt L} {o : Outcome} :
    Exec Φ σ C s o → ∀ {Γ κ Γ' a}, Γ.Holds σ → Admits κ C → AExec A Φ Γ κ s Γ' a →
      o.Within Γ' a
  | .assign he, _, _, _, _, hΓ, hκ, .assign ha => hΓ.update _ (eval_sound hA he hΓ hκ ha)
  | .skip, _, _, _, _, hΓ, _, .skip => hΓ
  | .ret he, _, _, _, _, hΓ, hκ, .ret ha => eval_sound hA he hΓ hκ ha
  | .assert he, _, _, _, _, hΓ, hκ, .assert _ => hA.refine hΓ hκ he
  | .seqNormal h₁ h₂, _, _, _, _, hΓ, hκ, .seq ha₁ ha₂ =>
      (exec_sound hA h₂ (exec_sound hA h₁ hΓ hκ ha₁) hκ ha₂).join_ret _
  | .seqRet h₁, _, _, _, _, hΓ, hκ, .seq ha₁ _ =>
      Describes.join_left _ (exec_sound hA h₁ hΓ hκ ha₁)
  | .iteTrue he h₁, _, _, _, _, hΓ, hκ, .ite ha₁ _ =>
      (exec_sound hA h₁ (hA.refine hΓ hκ he) hκ ha₁).join _ _
  | .iteFalse he h₂, _, _, _, _, hΓ, hκ, .ite _ ha₂ =>
      Outcome.Within.join' _ _ (exec_sound hA h₂ (hA.refine hΓ hκ he) hκ ha₂)
  | .whileFalse he, _, _, _, _, hΓ, hκ, .whileDo hle _ _ => hA.refine (hle _ hΓ) hκ he
  | .whileTrue he (.seqNormal hs hw), _, _, _, _, hΓ, hκ, .whileDo hle hbody hle' =>
      exec_sound hA hw (exec_sound hA hs (hA.refine (hle _ hΓ) hκ he) hκ hbody) hκ
        (.whileDo hle' hbody hle')
  | .whileTrue he (.seqRet hs), _, _, _, _, hΓ, hκ, .whileDo hle hbody _ => by
      have h := exec_sound hA hs (hA.refine (hle _ hΓ) hκ he) hκ hbody
      exact h
  | .withCtx he hs, _, _, _, _, hΓ, _, .withCtx ha hs' => by
      cases eval_sound hA he hΓ (admits_some _) ha with
      | known => exact exec_sound hA hs hΓ (admits_some _) hs'
  | .withCtx _ hs, _, _, _, _, hΓ, _, .withUnknown _ hs' =>
      exec_sound hA hs hΓ (admits_none _) hs'

end

/-- Format inference for a whole program (A-Program): an argument described by
`a` gives a result described by `a'`. -/
theorem run_sound (hA : A.Sound Φ) {f : Fn} {y : Var} {s : Stmt L} {a a' : AVal D}
    {Γ' : AEnv D} (hΦ : Φ f = some (y, s)) (hs : AExec A Φ (.single y a) (some .real) s Γ' a')
    {v v' : Val} (hv : Describes a v) (hrun : Run Φ f v v') : Describes a' v' := by
  obtain ⟨y', s', hΦ', hexec⟩ := hrun
  rw [hΦ] at hΦ'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hΦ')
  exact exec_sound hA hexec (AEnv.holds_single hv) (admits_some _) hs

end Fpy
