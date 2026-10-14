import Fpy.DigitBound.Basic

/-!
# The draft's joins as order premises

D-List, D-If, D-Seq and D-While take an order (`DVal.Le`, `DEnv.Le`) in place of
the draft's joins. The interval join `[l₁, m₁] ⊔ [l₂, m₂] = [min(l₁, l₂),
max(m₁, m₂)]`, with fresh endpoints, is an instance (`le_num`); environment
joins are built from reflexivity, one changed variable at a time
(`DEnv.Le.update`), and composition (`DEnv.Le.trans`).
-/

namespace Fpy.DigitBound

/-- A number in `[l, m]` lies in a fresh interval `[n + 1, n]` bounded by `Lo ≤ l`
and `m ≤ Hi`. -/
theorem le_num {Ψg : List Con} {n : ℕ} {l m Lo Hi : Term} {τ : Option Term} (hLo : Lo.Below n)
    (hHi : Hi.Below n) (hl : ∀ ι, Lo.eval ι ≤ l.eval ι) (hm : ∀ ι, m.eval ι ≤ Hi.eval ι) :
    DVal.Le n (n + 2) Ψg (bounds n Lo Hi (hLo.mono (Nat.le_succ n)) hHi) (.num l m τ)
      (.num (.var (n + 1)) (.var n) none) := by
  intro _ ι v _ hd
  cases hd with
  | num hu =>
    obtain ⟨ι', a, hs, hw⟩ := fresh_numIn (hLo.mono (Nat.le_succ n)) hHi ι _ fun hn => by
      obtain ⟨hl', hm'⟩ := hu.eq hn
      rw [eval_update hLo, hl', hm']
      exact ⟨hm ι, hl ι⟩
    exact ⟨ι', a, hs, .num hw⟩

theorem DEnv.Le.refl {Ψg : List Con} (n : ℕ) (Δ : DEnv) : DEnv.Le n n Ψg [] Δ Δ :=
  fun _ ι _ _ hσ => ⟨ι, fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil, by simpa using hσ⟩

/-- Changing one variable's abstract value along `d ⊑ d'`. -/
theorem DEnv.Le.update {Ψg Ψ : List Con} {n₀ n₁ : ℕ} {Δ : DEnv} {x : Var} {d d' : DVal}
    (hx : Δ x = some d) (hle : DVal.Le n₀ n₁ Ψg Ψ d d') (hF : Fresh n₀ n₁ Ψ)
    (hΔ : Δ.Below n₀) : DEnv.Le n₀ n₁ Ψg Ψ Δ (Δ.update x d') := by
  intro hb ι σ hs hσ
  obtain ⟨v, hv, hd⟩ := hσ x d hx
  obtain ⟨ι', a, hs', hd'⟩ := hle hb ι v hs hd
  refine ⟨ι', a, hs', fun z d₀ hz => ?_⟩
  by_cases hzx : z = x
  · subst hzx
    simp only [DEnv.update, Function.update_self, Option.some.injEq] at hz
    exact ⟨v, hv, hz ▸ hd'⟩
  · simp only [DEnv.update, Function.update_of_ne hzx] at hz
    obtain ⟨w, hw, hdw⟩ := hσ z d₀ hz
    exact ⟨w, hw, hdw.grow hb hF a.agree (hΔ z d₀ hz)⟩

theorem DEnv.Le.trans {Ψg Ψ₁ Ψ₂ : List Con} {n₀ n₁ n₂ : ℕ} {Δ Δ₁ Δ₂ : DEnv}
    (h₁ : DEnv.Le n₀ n₁ Ψg Ψ₁ Δ Δ₁) (h₂ : DEnv.Le n₁ n₂ (Ψg ++ Ψ₁) Ψ₂ Δ₁ Δ₂)
    (hF₁ : Fresh n₀ n₁ Ψ₁) (hF₂ : Fresh n₁ n₂ Ψ₂) :
    DEnv.Le n₀ n₂ Ψg (Ψ₁ ++ Ψ₂) Δ Δ₂ := by
  intro hb ι σ hs hσ
  obtain ⟨ι₁, a₁, hs₁, hσ₁⟩ := h₁ hb ι σ hs hσ
  obtain ⟨ι₂, a₂, hs₂, hσ₂⟩ := h₂ (hb.append hF₁) ι₁ σ
    ((Sat.congr hb a₁.agree hs).append hs₁) hσ₁
  refine ⟨ι₂, fun z hz => ?_, (Sat.congr hF₁.before a₂.agree hs₁).append hs₂,
    by simpa using hσ₂⟩
  have := hF₁.le
  have := hF₂.le
  rcases hz with hz | hz
  · rw [a₂ z (.inl (by omega)), a₁ z (.inl hz)]
  · rw [a₂ z (.inr hz), a₁ z (.inr (by omega))]

end Fpy.DigitBound
