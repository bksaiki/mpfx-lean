import Fpy.Rewrite.Separate
import Mpfx.DoubleRounding.Add

/-!
# Split and SplitOp from Mpfx's double-rounding rules
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
    (hS : S₂.Composes S₁ O₁ (.nearest tb)) (hO : O₂.Composes S₁ O₁ (.nearest tb)) :
    Equiv Φ {t} Γ (some (.ctx fs₁)) (.assign x (.arith op (ys.map .var)))
      (.seq (.withCtx c (.assign t (.arith op (ys.map .var))))
        (.assign x (.arith (show ArithOp from .round) [.var t]))) :=
  equiv_split hc (fpy_rnd_ctx hd₁) (fpy_rnd_ctx hd₂) fpy_round
    (RoundCtx.round_round fun _ _ => rndRTO_RN hsub hp h₁u hov hS hO)

/-- SplitOp for `+`: addition to nearest in `F₂`, with `2p₁ + 1` digits, then
rounding to nearest in `F₁` is addition to nearest in `F₁` (`rndAdd`). -/
example {tb₁ tb₂ : TieBreak} {p₁ p₂ : ℕ} {as : List (AVal D)}
    (h₁u : ¬ F₁.IsUndefined (.nearest tb₁)) (h₂u : ¬ F₂.IsUndefined (.nearest tb₂))
    (hd₁ : decode fs₁ = some ⟨F₁, S₁, O₁, .nearest tb₁, h₁u⟩)
    (hd₂ : decode fs₂ = some ⟨F₂, S₂, O₂, .nearest tb₂, h₂u⟩) (hc : Denotes Φ c (.ctx fs₂))
    (hp₁ : F₁.p = (p₁ : Prec)) (hp₂ : F₂.p = (p₂ : Prec)) (hpp : 2 * p₁ + 1 ≤ p₂)
    (hexp : F₂.exp ≤ F₁.exp) (hb : F₂.b = ⊤) (hS : S₂.Composes S₁ O₁ (.nearest tb₁))
    (has : List.Forall₂ (fun y a => Γ y = some a) ys as)
    (hfmt : ∀ a ∈ as, D.γ a.toFmt ⊆ F₁.reals) :
    Equiv Φ {t} Γ (some (.ctx fs₁)) (.assign x (.arith (show ArithOp from .add) (ys.map .var)))
      (.seq (.withCtx c (.assign t (.arith (show ArithOp from .add) (ys.map .var))))
        (.assign x (.arith (show ArithOp from .round) [.var t]))) :=
  equiv_splitOp hc (fpy_rnd_ctx hd₁) (fpy_rnd_ctx hd₂) fpy_round has hfmt
    (splitOp_add (c₁ := ⟨F₁, S₁, O₁, .nearest tb₁, h₁u⟩) (c₂ := ⟨F₂, S₂, O₂, .nearest tb₂, h₂u⟩)
      hS hb fun ha hb' => rndAdd hp₁ hp₂ hpp hexp h₁u ha hb')

end FpyTest
