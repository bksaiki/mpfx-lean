import Fpy.DigitBound.Sound
import Fpy.Sum

/-!
# D-Sum

D-Sum, proved against the definition of `sum`. On values (`sumVal_inRange`,
`eval_sum_inRange`): under `R`, if each of `L ≥ 1` elements has digits in
`[lo, hi]`, their sum has digits in `[lo, hi + ⌈log₂ L⌉]`. Over the analysis
(`eval_sum_sound`): if the constraints so far bound a list summary
`⟨[l, m], τ⟩` by terms `lo ≤ l`, `m ≤ hi` over earlier variables, `sum(e)`
lies in a fresh `[λ, μ]` with `λ ≥ lo`, `μ ≤ hi + ⌈log₂ L⌉`.
-/

namespace Fpy.DigitBound

open Mpfx

local notation "nan" => (WithSpecial.special Special.nan : Num)

@[simp] theorem Num.add_nan_left (w : Num) : Num.add nan w = nan := by
  rcases w with _ | (_ | _) <;> rfl

@[simp] theorem Num.add_nan_right (s : Num) : Num.add s nan = nan := by
  rcases s with _ | (_ | _) <;> rfl

/-- An invariant of `sum`'s additions, indexed by the number of terms. -/
theorem foldl_add_inv {P : ℕ → Num → Prop} {Q : Num → Prop}
    (hstep : ∀ k s w, P k s → Q w → P (k + 1) (Num.add s w)) :
    ∀ (ws : List Num) (k : ℕ) (s : Num), P k s → (∀ w ∈ ws, Q w) →
      P (k + ws.length) (ws.foldl (fun s w => id (Num.add s w)) s)
  | [], _, _, h, _ => h
  | w :: ws, k, s, h, hws => by
    have := foldl_add_inv hstep ws (k + 1) _ (hstep k s w h (hws w (List.mem_cons_self ..)))
      fun w' h' => hws w' (List.mem_cons_of_mem _ h')
    rwa [List.length_cons, ← Nat.add_assoc, Nat.add_right_comm]

/-- The invariant at the end of `sum`. -/
theorem sumVal_inv {P : ℕ → Num → Prop} {Q : Num → Prop}
    (hstep : ∀ k s w, P k s → Q w → P (k + 1) (Num.add s w)) (hstart : ∀ u, Q u → P 1 u)
    {us : List Num} (hL : 1 ≤ us.length) (hus : ∀ u ∈ us, Q u) : P us.length (sumVal id us) := by
  rcases us with _ | ⟨u, us⟩
  · simp at hL
  · simpa [sumVal, Nat.add_comm] using foldl_add_inv hstep us 1 u
      (hstart u (hus u (List.mem_cons_self ..))) fun w h => hus w (List.mem_cons_of_mem _ h)

/-- **D-Sum**, on values: the sum of `L ≥ 1` values with digits in `[lo, hi]`
has digits in `[lo, hi + ⌈log₂ L⌉]`. -/
theorem sumVal_inRange {lo hi : EInt} {us : List Num} (hL : 1 ≤ us.length)
    (hus : ∀ u ∈ us, InRange lo hi u) :
    InRange lo (hi + ((Nat.clog 2 us.length : ℕ) : ℤ)) (sumVal id us) := by
  set c := Nat.clog 2 us.length
  -- The least significant digit never drops below `lo`.
  have hlsb := sumVal_inv (P := fun _ s => s = nan ∨ lo ≤ lsbOf s) (Q := InRange lo hi)
    (fun _ s w hs hw => by
      rcases hs with rfl | hs
      · exact .inl (Num.add_nan_left w)
      rcases hw with rfl | ⟨hw, -⟩
      · exact .inl (Num.add_nan_right s)
      exact .inr ((le_min hs hw).trans (lsb_add s w)))
    (fun u hu => hu.imp id And.left) hL hus
  by_cases hn : sumVal id us = nan
  · exact .inl hn
  refine .inr ⟨hlsb.resolve_left hn, ?_⟩
  cases hi using WithBotTop.rec with
  | top => simp
  | bot =>
    -- Every term is zero.
    have h0 := sumVal_inv (P := fun _ s => s = nan ∨ s = .finite 0) (Q := InRange lo ⊥)
      (fun _ s w hs hw => by
        rcases hs with rfl | rfl
        · exact .inl (Num.add_nan_left w)
        rcases hw with rfl | ⟨-, hw⟩
        · exact .inl rfl
        rcases w with x | _
        · by_cases hx : x = 0
          · exact .inr (by simp [Num.add, hx])
          · exact absurd hw (by simp [msbOf_of_ne_zero hx])
        · exact absurd hw (by simp [msbOf_special]))
      (fun u hu => by
        rcases hu with rfl | ⟨-, hu⟩
        · exact .inl rfl
        rcases u with x | _
        · by_cases hx : x = 0
          · exact .inr (by rw [hx])
          · exact absurd hu (by simp [msbOf_of_ne_zero hx])
        · exact absurd hu (by simp [msbOf_special])) hL hus
    rw [h0.resolve_left hn, msbOf_zero]
    exact bot_le
  | coe h =>
    -- A partial sum of `k` terms has magnitude below `k · 2^(h+1)`.
    have hmag := sumVal_inv
      (P := fun k s => s = nan ∨ ∃ x, s = .finite x ∧ |x| < k * 2 ^ (h + 1))
      (Q := InRange lo h)
      (fun k s w hs hw => by
        rcases hs with rfl | ⟨x, rfl, hx⟩
        · exact .inl (Num.add_nan_left w)
        rcases hw with rfl | ⟨-, hw⟩
        · exact .inl (Num.add_nan_right _)
        rcases w with y | _
        · refine .inr ⟨x + y, rfl, (abs_add_le x y).trans_lt ?_⟩
          have := msbOf_le_coe.mp hw
          push_cast; linarith
        · exact absurd hw (by simp [msbOf_special]))
      (fun u hu => by
        rcases hu with rfl | ⟨-, hu⟩
        · exact .inl rfl
        rcases u with x | _
        · exact .inr ⟨x, rfl, by simpa using msbOf_le_coe.mp hu⟩
        · exact absurd hu (by simp [msbOf_special])) hL hus
    obtain ⟨x, hx, hlt⟩ := hmag.resolve_left hn
    rw [hx, coe_add_coe]
    refine msbOf_le_coe.mpr (hlt.trans_le ?_)
    have hc : (us.length : ℝ) ≤ 2 ^ c := by exact_mod_cast Nat.le_pow_clog (by norm_num) _
    rw [show h + c + 1 = (c : ℤ) + (h + 1) by ring,
      show (2 : ℝ) ^ ((c : ℤ) + (h + 1)) = 2 ^ c * 2 ^ (h + 1) by
        rw [zpow_add₀ two_ne_zero, zpow_natCast]]
    exact mul_le_mul_of_nonneg_right hc (zpow_pos two_pos _).le

variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}

/-- **D-Sum**: under `R`, a call to `sum` on `L ≥ 1` numbers with digits in
`[lo, hi]` returns a number with digits in `[lo, hi + ⌈log₂ L⌉]`. -/
theorem eval_sum_inRange (hsum : Φ "sum" = some ("xs", sumBody)) {σ : Store}
    {e : Expr (fpy decode)} {lo hi : EInt} {L : ℕ} {v : Val} (hL : 1 ≤ L)
    (he : ∀ v₀, Eval Φ σ .real e v₀ →
      ∃ vs, v₀ = .list vs ∧ vs.length = L ∧ ∀ w ∈ vs, ∃ u, w = .num u ∧ InRange lo hi u)
    (h : Eval Φ σ .real (.call "sum" e) v) :
    ∃ u, v = .num u ∧ InRange lo (hi + ((Nat.clog 2 L : ℕ) : ℤ)) u := by
  cases h with
  | call hΦ he' hs =>
    rw [hsum] at hΦ
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hΦ)
    obtain ⟨vs, rfl, hlen, hws⟩ := he _ he'
    obtain ⟨us, rfl, hus⟩ := exists_map_num hws
    obtain ⟨⟩ := exec_sumBody (r := id) rfl hs
    rw [List.length_map] at hlen
    subst hlen
    exact ⟨_, rfl, sumVal_inRange hL hus⟩

variable {D : FormatDomain} {A : Analysis (fpy decode) D}

/-- **D-Sum**, over the analysis: a list summary bounded by `lo` and `hi` under
the constraints so far gives `sum(e)` the fresh interval `[n₁ + 1, n₁]` with
`lo ≤ λ` and `μ ≤ hi + ⌈log₂ L⌉`. -/
theorem eval_sum_sound (hA : A.Sound Φ) (hsum : Φ "sum" = some ("xs", sumBody))
    {Δ : DEnv} {Γ : AEnv D} {χ : Option Val} {Ψg Ψ : List Con} {n₀ n₁ a : ℕ}
    {e : Expr (fpy decode)} {l m lo hi : Term} {τ : Option Term} {L : ℕ}
    (hd : DEval decode Φ A Δ Γ (some .real) χ Ψg n₀ e (.list (.num l m τ) a) Ψ n₁)
    (hlo : lo.Below a) (hhi : hi.Below a) (ha : a ≤ n₁)
    (hbnd : ∀ ι, Sat ι (Ψg ++ Ψ) → lo.eval ι ≤ l.eval ι ∧ m.eval ι ≤ hi.eval ι) (hL : 1 ≤ L)
    (hlen : ∀ σ vs, Eval Φ σ .real e (.list vs) → vs.length = L) {σ : Store} {v : Val}
    {ι : Asgn} (h : Eval Φ σ .real (.call "sum" e) v) (hbg : Before n₀ Ψg) (hsg : Sat ι Ψg)
    (hΔ : Δ.Below n₀) (hσ : Δ.Holds Ψg ι σ) (hΓ : Γ.Holds σ) (hχ : Admits χ .real) :
    ∃ ι', Agree n₀ ι ι' ∧
      Sat ι' (Ψ ++ bounds n₁ lo (.add hi (.const ((Nat.clog 2 L : ℕ) : ℤ)))
        ((hlo.mono ha).mono (Nat.le_succ n₁)) ⟨hhi.mono ha, trivial⟩) ∧
      Describes (Ψg ++ (Ψ ++ bounds n₁ lo (.add hi (.const ((Nat.clog 2 L : ℕ) : ℤ)))
        ((hlo.mono ha).mono (Nat.le_succ n₁)) ⟨hhi.mono ha, trivial⟩)) ι'
        (.num (.var (n₁ + 1)) (.var n₁) none) v := by
  cases h with
  | call hΦ he hs =>
    rw [hsum] at hΦ
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hΦ)
    obtain ⟨ι₁, a₁, hs₁, hdl⟩ := eval_sound hA hd he hbg hsg hΔ (ctxBelow_real _) hσ hΓ
      (admits_real' _) hχ
    cases hdl with
    | list hall =>
      rename_i vs
      have hel : ∀ w ∈ vs, ∃ u, w = .num u ∧ InRange (lo.eval ι₁) (hi.eval ι₁) u := by
        intro w hw
        obtain ⟨ι₀, h₀, hs₀, hd₀⟩ := hall.mem hw
        cases hd₀ with
        | num hu =>
          refine ⟨_, rfl, hu.imp id fun ⟨hl', hm', _⟩ => ?_⟩
          obtain ⟨b₁, b₂⟩ := hbnd ι₀ hs₀
          rw [Term.eval_congr h₀ hlo, Term.eval_congr h₀ hhi, hl', hm']
          exact ⟨b₁, b₂⟩
      obtain ⟨us, rfl, hus⟩ := exists_map_num hel
      obtain ⟨⟩ := exec_sumBody (r := id) rfl hs
      have hlen' := hlen σ _ he
      rw [List.length_map] at hlen'
      have hr := sumVal_inRange (by omega) hus
      rw [hlen'] at hr
      obtain ⟨ι₂, a₂, hs₂, hw⟩ := fresh_numIn (n := n₁)
        ((hlo.mono ha).mono (Nat.le_succ n₁)) (Hi := .add hi (.const ((Nat.clog 2 L : ℕ) : ℤ)))
        ⟨hhi.mono ha, trivial⟩ ι₁ _ fun hn => by
          obtain ⟨h₁, h₂⟩ := hr.resolve_left hn
          rw [eval_update (hlo.mono ha)]
          exact ⟨h₂, h₁⟩
      exact chain (DEval.wf hd).1 a₁ hs₁ a₂.agree hs₂ (.num hw)

end Fpy.DigitBound
