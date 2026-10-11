import Fpy.FormatInference.Ops
import Fpy.FormatInference.Sound

/-!
# Condition refinement (§4.2)

`refine κ e b Γ` is `⟦e⟧♯ Γ` for `b = true` and `⟦¬e⟧♯ Γ` for `b = false`. It
narrows a variable `x` by a test against a constant `c`: `x ⋈ c`, and under
`R`, where they are exact, `|x| ⋈ c` and `logb x ⋈ c`. A set keeps the values
that pass. On an abstract format, a test implying `|x| ≤ c` lowers the bound
to `c`, and one implying `logb x ≥ k` raises the minimum exponent to
`k − p + 1`, since `x` has at most `p` digits. `not`, a true `and` and a false
`or` refine through their operands. `refine_sound` is the obligation
`Analysis.Sound.refine`.
-/

namespace Fpy

open Mpfx

/-! ## Tests on one variable -/

/-- The comparisons a test can use. -/
inductive Cmp where
  | lt | le | eq

noncomputable def Cmp.eval : Cmp → Num → Num → Bool
  | .lt => Num.lt
  | .le => Num.le
  | .eq => Num.eq

def Cmp.ofOp : ExactOp → Option Cmp
  | .lt => some .lt
  | .le => some .le
  | .eq => some .eq
  | _ => none

/-- What a test compares with the constant: `x`, `|x|` or `logb x`. -/
inductive Lhs where
  | id | abs | logb

noncomputable def Lhs.eval : Lhs → Num → Num
  | .id => fun u => u
  | .abs => Num.abs
  | .logb => Num.logb

/-- The test `g(x) ⋈ c`, or `c ⋈ g(x)` when `flip`. -/
structure Atom where
  x : Var
  g : Lhs
  cmp : Cmp
  c : Num
  flip : Bool

/-- The comparison has outcome `b` when `g(x)` is `v`. -/
def Atom.CmpHolds (a : Atom) (v : Num) (b : Bool) : Prop :=
  (if a.flip then a.cmp.eval a.c v else a.cmp.eval v a.c) = b

/-- The test has outcome `b` when `x` is `u`. -/
def Atom.Holds (a : Atom) (u : Num) (b : Bool) : Prop := a.CmpHolds (a.g.eval u) b

variable {decode : List (Label × Val) → Option RoundCtx}

/-- `x`, or `|x|` and `logb x` under `R`. -/
def parseLhs : Option Val → Expr (fpy decode) → Option (Var × Lhs)
  | _, .var x => some (x, .id)
  | some .real, .arith op [.var x] =>
    if (show ArithOp from op) = .abs then some (x, .abs)
    else if (show ArithOp from op) = .logb then some (x, .logb)
    else none
  | _, _ => none

/-- Reads `e` as a test on one variable. -/
def parseAtom (κ : Option Val) : Expr (fpy decode) → Option Atom
  | .exact op [e, .num c] => do
    let k ← Cmp.ofOp op
    let (x, g) ← parseLhs κ e
    pure ⟨x, g, k, c, false⟩
  | .exact op [.num c, e] => do
    let k ← Cmp.ofOp op
    let (x, g) ← parseLhs κ e
    pure ⟨x, g, k, c, true⟩
  | _ => none

/-! ### What a test's outcome says about `x` -/

variable {Φ : Program (fpy decode)}

theorem eval_parseLhs {κ : Option Val} {e : Expr (fpy decode)} {x : Var} {g : Lhs}
    (he : parseLhs κ e = some (x, g)) {σ : Store} {C : Val} (hκ : Admits κ C) {n : Num}
    (h : Eval Φ σ C e (.num n)) : ∃ u, σ x = some (.num u) ∧ n = g.eval u := by
  unfold parseLhs at he
  split at he
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he)
    cases h with
    | var hx => exact ⟨n, hx, rfl⟩
  · next op x' =>
    obtain rfl := hκ _ rfl
    cases h with
    | @arith _ _ _ _ ns m r hl hop hr =>
      generalize hvs : ns.map Val.num = vs at hl
      cases hl with
      | @cons _ _ _ _ v vs' hv hl =>
        cases hl
        cases hv with
        | var hx =>
          obtain ⟨u, rfl, rfl⟩ : ∃ u, ns = [u] ∧ v = .num u := by
            cases ns with
            | nil => simp at hvs
            | cons u ns =>
              simp only [List.map_cons, List.cons.injEq, List.map_eq_nil_iff] at hvs
              exact ⟨u, by rw [hvs.2], hvs.1.symm⟩
          simp only [Val.rnd, Option.some.injEq] at hr
          subst hr
          split_ifs at he with h₁ h₂ <;>
            simp only [Option.some.injEq, Prod.mk.injEq] at he
          · obtain ⟨rfl, rfl⟩ := he
            subst h₁
            simp only [fpy, ArithOp.eval, Option.some.injEq] at hop
            exact ⟨u, hx, by simp [Lhs.eval, hop]⟩
          · obtain ⟨rfl, rfl⟩ := he
            subst h₂
            simp only [fpy, ArithOp.eval, Option.some.injEq] at hop
            exact ⟨u, hx, by simp [Lhs.eval, hop]⟩
  · simp at he

theorem eval_cmp {op : ExactOp} {k : Cmp} (hk : Cmp.ofOp op = some k) {σ : Store} {C : Val}
    {e₁ e₂ : Expr (fpy decode)} {b : Bool} (h : Eval Φ σ C (.exact op [e₁, e₂]) (.bool b)) :
    ∃ n₁ n₂, Eval Φ σ C e₁ (.num n₁) ∧ Eval Φ σ C e₂ (.num n₂) ∧ k.eval n₁ n₂ = b := by
  cases h with
  | exact hl hop =>
    cases hl with
    | @cons _ _ _ _ v₁ _ h₁ hl =>
      cases hl with
      | @cons _ _ _ _ v₂ _ h₂ hl =>
        cases hl
        cases op <;> simp only [Cmp.ofOp, reduceCtorEq, Option.some.injEq] at hk <;>
          subst hk <;>
          rcases v₁ with _ | n₁ | _ | _ | _ | _ <;> rcases v₂ with _ | n₂ | _ | _ | _ | _ <;>
          simp only [fpy, ExactOp.eval, reduceCtorEq, Option.some.injEq, Val.bool.injEq] at hop <;>
          exact ⟨_, _, h₁, h₂, by simp [Cmp.eval, hop]⟩

theorem eval_parseAtom {κ : Option Val} {e : Expr (fpy decode)} {a : Atom}
    (he : parseAtom κ e = some a) {σ : Store} {C : Val} (hκ : Admits κ C) {b : Bool}
    (h : Eval Φ σ C e (.bool b)) : ∃ u, σ a.x = some (.num u) ∧ a.Holds u b := by
  unfold parseAtom at he
  split at he
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at he
    obtain ⟨k, hk, ⟨x, g⟩, hlhs, rfl⟩ := he
    obtain ⟨n₁, n₂, h₁, h₂, hb⟩ := eval_cmp hk h
    cases h₂
    obtain ⟨u, hu, rfl⟩ := eval_parseLhs hlhs hκ h₁
    exact ⟨u, hu, by simpa [Atom.Holds, Atom.CmpHolds] using hb⟩
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at he
    obtain ⟨k, hk, ⟨x, g⟩, hlhs, rfl⟩ := he
    obtain ⟨n₁, n₂, h₁, h₂, hb⟩ := eval_cmp hk h
    cases h₁
    obtain ⟨u, hu, rfl⟩ := eval_parseLhs hlhs hκ h₂
    exact ⟨u, hu, by simpa [Atom.Holds, Atom.CmpHolds] using hb⟩
  · simp at he

/-! ## Narrowing a format by a test -/

theorem boundOK_min {b : Bound} {d : NonNegDyadic} {x : Mpfx.Dyadic} (hb : Format.boundOK b x)
    (hx : |(x : ℚ)| ≤ ((d.1 : Mpfx.Dyadic) : ℚ)) : Format.boundOK (min b ↑d) x := by
  rcases min_choice b ↑d with h | h <;> rw [h]
  · exact hb
  · exact hx

/-- A nonzero value with at most `p` digits and magnitude at least `2^k` has
quantum at least `2^(k − p + 1)`. -/
theorem quantumAtLeast_of_le_log {p : ℕ} {k : ℤ} {d : Mpfx.Dyadic}
    (hp : Dyadic.precisionAtMost (p : Prec) d) (hd : (d : ℝ) ≠ 0)
    (hk : k ≤ Int.log 2 |(d : ℝ)|) : Dyadic.quantumAtLeast ((k - p + 1 : ℤ) : QExp) d := by
  obtain ⟨c, e, hde, hc⟩ := (Dyadic.precisionAtMost_coe_real p d).mp hp
  by_cases he : k - p + 1 ≤ e
  · exact Dyadic.quantumAtLeast_anti (WithBot.coe_le_coe.mpr he)
      ((Dyadic.quantumAtLeast_coe_real e d).mpr ⟨c, hde⟩)
  · exfalso
    have h2k : (2 : ℝ) ^ k ≤ |(d : ℝ)| :=
      (Int.zpow_le_iff_le_log (by norm_num) (abs_pos.mpr hd)).mpr hk
    have hcR : |(c : ℝ)| < (2 : ℝ) ^ (p : ℤ) := by
      rw [zpow_natCast, ← Int.cast_abs]
      exact_mod_cast hc
    have : |(d : ℝ)| < (2 : ℝ) ^ k := by
      rw [hde, abs_mul_two_zpow]
      calc |(c : ℝ)| * (2 : ℝ) ^ e < (2 : ℝ) ^ (p : ℤ) * (2 : ℝ) ^ e :=
            mul_lt_mul_of_pos_right hcR (zpow_pos (by norm_num) _)
        _ = (2 : ℝ) ^ ((p : ℤ) + e) := (zpow_add₀ (by norm_num) _ _).symm
        _ ≤ (2 : ℝ) ^ k := zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith

/-- `F` with minimum exponent raised to `k − p + 1`, for values with
`logb x ≥ k`. -/
noncomputable def narrowLogb (F : Format) (k : ℤ) : Format :=
  if F.p = ⊤ then F else { F with exp := max F.exp ((k - F.p.toNat + 1 : ℤ) : QExp) }

open Classical in
/-- Narrows `F` to the values passing the test: a test implying `|x| ≤ c`
lowers the bound to `c`, and one implying `logb x ≥ c` raises the minimum
exponent. Other tests leave `F` unchanged. -/
noncomputable def Atom.narrow (a : Atom) (b : Bool) (F : Format) : Format :=
  match a.g, a.c with
  | .abs, .finite r =>
    if h : (∀ y, a.CmpHolds (.finite y) b → y ≤ r) ∧
        ∃ d : NonNegDyadic, ((d.1 : Mpfx.Dyadic) : ℝ) = r then
      { F with b := min F.b ↑(Classical.choose h.2) }
    else F
  | .logb, .finite r =>
    if ¬ a.CmpHolds (.special (.inf true)) b ∧ ∀ y, a.CmpHolds (.finite y) b → r ≤ y then
      narrowLogb F ⌈r⌉
    else F
  | _, _ => F

theorem Atom.reals_narrow {a : Atom} {b : Bool} {F : Format} {u : Num} (hu : u ∈ F.reals)
    (ha : a.Holds u b) : u ∈ (a.narrow b F).reals := by
  unfold Atom.narrow
  split
  · next r hg hc =>
    split
    · next h =>
      obtain ⟨w, hw, rfl⟩ := hu
      refine ⟨w, ?_, rfl⟩
      cases w with
      | special s => exact hw
      | finite d' =>
        refine ⟨hw.1, hw.2.1, boundOK_min hw.2.2 ?_⟩
        have hle := h.1 |(d' : ℝ)| (by simpa [Atom.Holds, hg, Lhs.eval, Num.abs] using ha)
        rw [← Classical.choose_spec h.2] at hle
        exact_mod_cast hle
    · exact hu
  · next r hg hc =>
    split
    · next h =>
      obtain ⟨w, hw, rfl⟩ := hu
      refine ⟨w, ?_, rfl⟩
      cases w with
      | special s => unfold narrowLogb; split <;> exact hw
      | finite d' =>
        have hlog : a.CmpHolds (Num.logb (.finite (d' : ℝ))) b := by
          simpa [Atom.Holds, hg, Lhs.eval] using ha
        by_cases hd : (d' : ℝ) = 0
        · simp only [Num.logb, hd, if_true] at hlog
          exact absurd hlog h.1
        · simp only [Num.logb, hd, if_false] at hlog
          have hk : ⌈r⌉ ≤ Int.log 2 |(d' : ℝ)| := Int.ceil_le.mpr (h.2 _ hlog)
          unfold narrowLogb
          split
          · exact hw
          · next hp =>
            have hp' : F.p = ((F.p.toNat : ℕ) : Prec) := (ENat.coe_toNat hp).symm
            have hq := quantumAtLeast_of_le_log (hp' ▸ hw.1) hd hk
            refine ⟨hw.1, ?_, hw.2.2⟩
            change Dyadic.quantumAtLeast (max F.exp _) d'
            rcases max_choice F.exp ((⌈r⌉ - F.p.toNat + 1 : ℤ) : QExp) with h' | h' <;> rw [h']
            · exact hw.2.1
            · exact hq
    · exact hu
  · exact hu

open Classical in
/-- Narrows a format of Figure 4: a set keeps the values that pass. -/
noncomputable def Atom.narrowFmt (a : Atom) (b : Bool) : Fmt → Fmt
  | .set S => .set (S.filter fun u => a.Holds u b)
  | .abs F => .abs (a.narrow b F)
  | .top => .top

theorem Atom.mem_narrowFmt {a : Atom} {b : Bool} {F : Fmt} {u : Num} (hu : u ∈ F.γ)
    (ha : a.Holds u b) : u ∈ (a.narrowFmt b F).γ := by
  classical
  cases F with
  | set S => exact Finset.mem_filter.mpr ⟨hu, ha⟩
  | abs F => exact a.reals_narrow hu ha
  | top => trivial

/-! ## Refinement -/

variable {c : Ceiling}

/-- Refines `Γ` by the test `a` having outcome `b`. -/
noncomputable def Atom.refine (a : Atom) (b : Bool) (Γ : AEnv (Fmt.domain c)) :
    AEnv (Fmt.domain c) :=
  match Γ a.x with
  | some (.fmt F) => Γ.update a.x (.fmt (a.narrowFmt b F))
  | _ => Γ

theorem Atom.holds_refine {a : Atom} {b : Bool} {Γ : AEnv (Fmt.domain c)} {σ : Store}
    (hΓ : Γ.Holds σ) {u : Num} (hx : σ a.x = some (.num u)) (ha : a.Holds u b) :
    (a.refine b Γ).Holds σ := by
  unfold Atom.refine
  split
  · next F hF =>
    obtain ⟨v, hv, hd⟩ := hΓ _ _ hF
    rw [hx, Option.some.injEq] at hv
    subst hv
    cases hd with
    | fmt hu =>
      have := hΓ.update a.x (Describes.fmt (D := Fmt.domain c) (a.mem_narrowFmt hu ha))
      rwa [Store.update, ← hx, Function.update_eq_self] at this
  · exact hΓ

/-- `⟦e⟧♯ Γ` (`b = true`) and `⟦¬e⟧♯ Γ` (`b = false`) for the FPy signature. -/
noncomputable def refine (κ : Option Val) (e : Expr (fpy decode)) (b : Bool)
    (Γ : AEnv (Fmt.domain c)) : AEnv (Fmt.domain c) :=
  match e with
  | .exact op [e₁] =>
    if (show ExactOp from op) = .not then refine κ e₁ (!b) Γ
    else (parseAtom κ e).elim Γ (·.refine b Γ)
  | .exact op [e₁, e₂] =>
    if (show ExactOp from op) = .and ∧ b = true then refine κ e₂ true (refine κ e₁ true Γ)
    else if (show ExactOp from op) = .or ∧ b = false then
      refine κ e₂ false (refine κ e₁ false Γ)
    else (parseAtom κ e).elim Γ (·.refine b Γ)
  | e => (parseAtom κ e).elim Γ (·.refine b Γ)

theorem holds_refine_atom {κ : Option Val} {e : Expr (fpy decode)} {b : Bool}
    {Γ : AEnv (Fmt.domain c)} {σ : Store} {C : Val} (hΓ : Γ.Holds σ) (hκ : Admits κ C)
    (h : Eval Φ σ C e (.bool b)) : ((parseAtom κ e).elim Γ (·.refine b Γ)).Holds σ := by
  cases ha : parseAtom κ e with
  | none => exact hΓ
  | some a =>
    obtain ⟨u, hx, hu⟩ := eval_parseAtom ha hκ h
    exact Atom.holds_refine hΓ hx hu

/-- Refinement keeps every store that gives the test its outcome: the obligation
`Analysis.Sound.refine`. -/
theorem refine_sound {κ : Option Val} {C : Val} (hκ : Admits κ C) :
    ∀ (e : Expr (fpy decode)) {b : Bool} {Γ : AEnv (Fmt.domain c)} {σ : Store},
      Γ.Holds σ → Eval Φ σ C e (.bool b) → (refine κ e b Γ).Holds σ
  | .exact op [e₁], b, Γ, σ, hΓ, h => by
    unfold refine
    split
    · next hop =>
      cases h with
      | exact hl hev =>
        cases hl with
        | @cons _ _ _ _ v₁ _ h₁ hl =>
          cases hl
          change ExactOp.eval op [v₁] = _ at hev
          rw [hop] at hev
          rcases v₁ with _ | _ | _ | _ | _ | _ <;>
            simp only [ExactOp.eval, Option.some.injEq, reduceCtorEq, Val.bool.injEq] at hev
          subst hev
          rw [Bool.not_not]
          exact refine_sound hκ e₁ hΓ h₁
    · exact holds_refine_atom hΓ hκ h
  | .exact op [e₁, e₂], b, Γ, σ, hΓ, h => by
    unfold refine
    split
    · next hop =>
      obtain ⟨hop, rfl⟩ := hop
      cases h with
      | exact hl hev =>
        cases hl with
        | @cons _ _ _ _ v₁ _ h₁ hl =>
          cases hl with
          | @cons _ _ _ _ v₂ _ h₂ hl =>
            cases hl
            change ExactOp.eval op [v₁, v₂] = _ at hev
            rw [hop] at hev
            rcases v₁ with b₁ | _ | _ | _ | _ | _ <;> rcases v₂ with b₂ | _ | _ | _ | _ | _ <;>
              simp only [ExactOp.eval, Option.some.injEq, reduceCtorEq, Val.bool.injEq,
                Bool.and_eq_true] at hev
            obtain ⟨rfl, rfl⟩ := hev
            exact refine_sound hκ e₂ (refine_sound hκ e₁ hΓ h₁) h₂
    · split
      · next hop =>
        obtain ⟨hop, rfl⟩ := hop
        cases h with
        | exact hl hev =>
          cases hl with
          | @cons _ _ _ _ v₁ _ h₁ hl =>
            cases hl with
            | @cons _ _ _ _ v₂ _ h₂ hl =>
              cases hl
              change ExactOp.eval op [v₁, v₂] = _ at hev
              rw [hop] at hev
              rcases v₁ with b₁ | _ | _ | _ | _ | _ <;> rcases v₂ with b₂ | _ | _ | _ | _ | _ <;>
                simp only [ExactOp.eval, Option.some.injEq, reduceCtorEq, Val.bool.injEq,
                  Bool.or_eq_false_iff] at hev
              obtain ⟨rfl, rfl⟩ := hev
              exact refine_sound hκ e₂ (refine_sound hκ e₁ hΓ h₁) h₂
      · exact holds_refine_atom hΓ hκ h
  | .bool _, _, _, _, hΓ, h | .num _, _, _, _, hΓ, h | .var _, _, _, _, hΓ, h
  | .arith _ _, _, _, _, hΓ, h | .list _, _, _, _, hΓ, h | .index _ _, _, _, _, hΓ, h
  | .record _, _, _, _, hΓ, h | .proj _ _, _, _, _, hΓ, h | .call _ _, _, _, _, hΓ, h
  | .real, _, _, _, hΓ, h | .ctx _, _, _, _, hΓ, h
  | .exact _ [], _, _, _, hΓ, h | .exact _ (_ :: _ :: _ :: _), _, _, _, hΓ, h => by
    unfold refine
    exact holds_refine_atom hΓ hκ h

end Fpy
