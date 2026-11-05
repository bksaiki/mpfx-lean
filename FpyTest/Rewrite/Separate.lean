import Fpy.Rewrite.Separate
import Mpfx.DoubleRounding.Add

/-!
# Elim on expressions; Split from Mpfx's double-rounding rules
-/

namespace FpyTest

open Fpy Mpfx

variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {Γ : AEnv D} {fs₁ fs₂ : List (Label × Val)} {c : Expr (fpy decode)}
  {x t : Var} {ys : List Var} {F₁ F₂ : FiniteFormat} {S₁ : SpecialMap F₁.toFormat}
  {O₁ : OverflowMap F₁.toFormat} {S₂ : SpecialMap F₂.toFormat} {O₂ : OverflowMap F₂.toFormat}

/-- Split through round-to-odd: rounding to odd in `F₂`, with two more digits,
then to nearest in `F₁` is rounding to nearest in `F₁` (`rndRTO_RN`). -/
example {tb : TieBreak} {op : ArithOp} (h₁u : ¬ F₁.IsUndefined (.nearest tb))
    (h₂u : ¬ F₂.IsUndefined .toOdd) (hd₁ : decode fs₁ = some ⟨F₁, S₁, O₁, .nearest tb, h₁u⟩)
    (hd₂ : decode fs₂ = some ⟨F₂, S₂, O₂, .toOdd, h₂u⟩) (hc : Denotes Φ c (.ctx fs₂))
    (hsub : (F₁.extend 2).toFormat ⊆ F₂.toFormat) (hp : ((2 : ℕ) : Prec) ≤ F₂.p)
    (hov : OverflowAgrees F₁ S₁ O₁ (.nearest tb) F₂ O₂ .toOdd)
    (hS : S₂.Composes S₁ O₁ (.nearest tb)) (hO : O₂.Composes S₁ O₁ (.nearest tb))
    {Fs : List D.Fmt} (hF : FmtsIn Γ ys Fs) :
    Equiv Φ {t} Γ (some (.ctx fs₁)) (.assign x (.arith op (ys.map .var)))
      (.seq (.withCtx c (.assign t (.arith op (ys.map .var))))
        (.assign x (.arith (show ArithOp from .round) [.var t]))) :=
  equiv_split hc (fpy_rnd_ctx hd₁) (fpy_rnd_ctx hd₂) fpy_round hF fun _ _ _ _ =>
    RoundCtx.round_round (fun _ _ => rndRTO_RN hsub hp h₁u hov hS hO) _

/-- Split with `C' = R`: the condition is `rfl`. -/
example {op : ArithOp} {r : Num → Num} (hr : (Val.ctx fs₁).rnd (fpy decode) = some r)
    {Fs : List D.Fmt} (hF : FmtsIn Γ ys Fs) :
    Equiv Φ {t} Γ (some (.ctx fs₁)) (.assign x (.arith op (ys.map .var)))
      (.seq (.withCtx .real (.assign t (.arith op (ys.map .var))))
        (.assign x (.arith (show ArithOp from .round) [.var t]))) :=
  equiv_split denotes_real hr rfl fpy_round hF fun _ _ _ _ => rfl

/-- Split for `+`: addition to nearest in `F₂`, with `2p₁ + 1` digits, then
rounding to nearest in `F₁` is addition to nearest in `F₁` (`rndAdd`). -/
example {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ}
    (h₁u : ¬ F₁.IsUndefined (.nearest tb₁)) (h₂u : ¬ F₂.IsUndefined (.nearest tb₂))
    (hd₁ : decode fs₁ = some ⟨F₁, S₁, O₁, .nearest tb₁, h₁u⟩)
    (hd₂ : decode fs₂ = some ⟨F₂, S₂, O₂, .nearest tb₂, h₂u⟩) (hc : Denotes Φ c (.ctx fs₂))
    (hp₁ : F₁.p = (p₁ : Prec)) (hp₂ : F₂.p = (p₂ : Prec)) (hpp : 2 * p₁ + 1 ≤ p₂)
    (hexp : F₂.exp ≤ F₁.exp) (hb : F₂.b = ⊤) (hS : S₂.Composes S₁ O₁ (.nearest tb₁))
    {Fs : List D.Fmt} (hF : FmtsIn Γ ys Fs) (hFs : ∀ F ∈ Fs, D.γ F ⊆ F₁.reals) :
    Equiv Φ {t} Γ (some (.ctx fs₁)) (.assign x (.arith (show ArithOp from .add) (ys.map .var)))
      (.seq (.withCtx c (.assign t (.arith (show ArithOp from .add) (ys.map .var))))
        (.assign x (.arith (show ArithOp from .round) [.var t]))) :=
  equiv_split hc (fpy_rnd_ctx hd₁) (fpy_rnd_ctx hd₂) fpy_round hF fun us n hus =>
    split_add (c₁ := ⟨F₁, S₁, O₁, .nearest tb₁, h₁u⟩) (c₂ := ⟨F₂, S₂, O₂, .nearest tb₂, h₂u⟩)
      hS hb (fun ha hb' => rndAdd hp₁ hp₂ hpp hexp h₁u ha hb') us n
      (forall_mem_of_forall₂ hus hFs)

/-- Elim on `op(e₁, e₂)`: bind the operands to fresh `t₁`, `t₂`, then drop the rounding. -/
example {L : Signature} {Φ : Program L} {A : Analysis L D} (hA : A.Sound Φ) {C : Val}
    {r : Num → Num} {FC G₁ G₂ : D.Fmt} {t₁ t₂ : Var} {op : L.ArithOp} {e₁ e₂ : Expr L}
    {a₁ a₂ : AVal D} (hne : t₁ ≠ t₂) (he : ∀ e ∈ [e₁, e₂], Avoids {t₁, t₂} e)
    (ha : AEvalList A Φ Γ (some C) [e₁, e₂] [a₁, a₂]) (hr : C.rnd L = some r)
    (hFC : A.ctxFmt C = some FC) (h₁ : D.γ a₁.toFmt ⊆ D.γ G₁) (h₂ : D.γ a₂.toFmt ⊆ D.γ G₂)
    (hsub : D.γ (A.arith op [G₁, G₂]) ⊆ D.γ FC) :
    Equiv Φ {t₁, t₂} Γ (some C) (.assign x (.arith op [e₁, e₂]))
      (Stmt.binds [t₁, t₂] [e₁, e₂] (.withCtx .real (.assign x (.arith op [.var t₁, .var t₂])))) :=
  equiv_bind hA (by simp [hne]) rfl (by simp) he ha <| equiv_elim hA hr hFC
    (.cons ⟨a₁, by simp [updates, Function.update, hne], h₁⟩
      (.cons ⟨a₂, by simp [updates], h₂⟩ .nil)) hsub

end FpyTest
