import Fpy.FormatInference.Sound
import Fpy.Sum

/-!
# A-Sum

The summary of `sum` for format inference, proved against its definition:
`sum(e) : F_L` when `e : [F]` has length `L`, with `F₀ = {0}`, `F₁ = F` and
`F_{i+1} = rnd♯_κ(F_i ⊕ F)`.
-/

namespace Fpy

variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {A : Analysis (fpy decode) D}

variable (A) in
/-- `F_L`: the format of the sum of `L` values in `F` under `κ`. -/
noncomputable def sumFmt (κ : Option Val) (F : D.Fmt) : ℕ → D.Fmt
  | 0 => D.ofNum (.finite 0)
  | 1 => F
  | n + 2 => A.rnd κ (A.arith .add [sumFmt κ F (n + 1), F])

theorem sumVal_mem (hA : A.Sound Φ) {κ : Option Val} {C : Val} {r : Num → Num}
    (hκ : Admits κ C) (hr : C.rnd (fpy decode) = some r) {F : D.Fmt} :
    ∀ {us : List Num}, (∀ u ∈ us, u ∈ D.γ F) → sumVal r us ∈ D.γ (sumFmt A κ F us.length)
  | [], _ => D.mem_ofNum _
  | u :: us, hus => by
    have key : ∀ (ws : List Num) (k : ℕ) (s : Num), s ∈ D.γ (sumFmt A κ F (k + 1)) →
        (∀ w ∈ ws, w ∈ D.γ F) →
        ws.foldl (fun s w => r (Num.add s w)) s ∈ D.γ (sumFmt A κ F (k + 1 + ws.length)) := by
      intro ws
      induction ws with
      | nil => exact fun _ _ hs _ => hs
      | cons w ws ih =>
        intro k s hs hws
        have hadd := hA.arith (op := .add) (.cons hs (.cons (hws w (List.mem_cons_self ..)) .nil))
          rfl
        have e : k + 1 + (w :: ws).length = k + 1 + 1 + ws.length := by simp; omega
        rw [List.foldl_cons, e]
        exact ih (k + 1) _ (A.mem_rnd hA hadd hκ hr) fun w' h => hws w' (List.mem_cons_of_mem _ h)
    simpa [Nat.add_comm] using key us 0 u (hus u (List.mem_cons_self ..))
      fun w h => hus w (List.mem_cons_of_mem _ h)

/-- **A-Sum**: a call to `sum` on `e : [F]` of length `L`, under a context with
rounding `r`, returns a value in `F_L`. -/
theorem eval_sum (hA : A.Sound Φ) (hsum : Φ "sum" = some ("xs", sumBody)) {Γ : AEnv D}
    {κ : Option Val} {σ : Store} {C : Val} {r : Num → Num} {e : Expr (fpy decode)}
    {F : D.Fmt} {L : ℕ} {v : Val} (hΓ : Γ.Holds σ) (hκ : Admits κ C)
    (hr : C.rnd (fpy decode) = some r) (he : AEval A Φ Γ κ e (.list (.fmt F)))
    (hL : ∀ vs, Eval Φ σ C e (.list vs) → vs.length = L) (h : Eval Φ σ C (.call "sum" e) v) :
    Describes (.fmt (sumFmt A κ F L)) v := by
  cases h with
  | call hΦ he' hs =>
    rw [hsum] at hΦ
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hΦ)
    cases eval_sound hA he' hΓ hκ he with
    | list hall =>
      obtain ⟨us, rfl, hus⟩ := exists_map_num (P := (· ∈ D.γ F)) fun w hw => by
        cases describesAll_iff.mp hall w hw with | fmt hu => exact ⟨_, rfl, hu⟩
      obtain rfl := hL _ he'
      obtain ⟨⟩ := exec_sumBody hr hs
      rw [List.length_map]
      exact .fmt (sumVal_mem hA hκ hr hus)

end Fpy
