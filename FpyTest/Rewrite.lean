import Fpy.Rewrite
import FpyTest.FormatInference

/-!
# A rewrite with a fresh variable, end to end

`x = e ⇝ t = e; x = t` names a value with a fresh `t`. It is correct for every
program, environment and context, so a site holding it rewrites a program
without changing what it returns.
-/

namespace FpyTest

open Fpy

theorem equiv_name {L : Signature} {D : FormatDomain} {Φ : Program L} {Γ : AEnv D}
    {κ : Option Val} {x t : Var} {e : Expr L} :
    Equiv Φ {t} Γ κ (.assign x e) (.seq (.assign t e) (.assign x (.var t))) := by
  have hag : ∀ (σ : Store) (v : Val), (σ.update x v).Agree {t} ((σ.update t v).update x v) := by
    intro σ v z hz
    simp only [Set.mem_singleton_iff] at hz
    simp [Store.update, Function.update_apply, hz]
  intro σ C _ _
  refine ⟨fun o h => ?_, fun o' h => ?_⟩
  · cases h with
    | assign he => exact ⟨_, .seqNormal (.assign he) (.assign (.var (by simp [Store.update]))),
        hag σ _⟩
  · cases h with
    | seqNormal h₁ h₂ =>
      cases h₁ with
      | assign he =>
        cases h₂ with
        | assign hv =>
          cases hv with
          | var hx =>
            simp only [Store.update, Function.update_self, Option.some.injEq] at hx
            exact ⟨_, .assign he, hx ▸ hag σ _⟩
    | seqRet h₁ => cases h₁

/-- `r = c; ret r`. -/
noncomputable def srcBody : Stmt L := .seq (.assign "r" (.var "c")) (.ret (.var "r"))

/-- `(t = c; r = t); ret r`. -/
noncomputable def tgtBody : Stmt L :=
  .seq (.seq (.assign "t" (.var "c")) (.assign "r" (.var "t"))) (.ret (.var "r"))

noncomputable def src : Program L := fun f => if f = "f" then some ("c", srcBody) else none

noncomputable def tgt : Program L := fun f => if f = "f" then some ("c", tgtBody) else none

example (a : AVal D) {v v' : Val} (hv : Describes a v) : Run src "f" v v' ↔ Run tgt "f" v v' :=
  run_iff_of_rw (A_sound src) (y := "c") (s := srcBody) (s' := tgtBody) (by simp [src])
    (by simp [tgt])
    (.seq (.assign (.var (a := a) (by simp [AEnv.single])))
      (.site (Sim.equiv (Rw.sim (A_sound src) (.assign (.var (by simp)))) equiv_name
        (by simp [AEnv.single])))
      (.ret (.var (by simp))))
    hv

end FpyTest
