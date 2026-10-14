import Fpy.DigitBound.Digits
import Fpy.Sum

/-!
# D-Sum

The arithmetic content of D-Sum, proved against the definition of `sum`: under
`R`, if each of `L ≥ 1` elements has digits in `[lo, hi]`, their sum has digits
in `[lo, hi + ⌈log₂ L⌉]`. It is stated on values: the analysis's list summaries
re-choose their variables per element, so their bounds are not visible here
(as for D-Index).
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

end Fpy.DigitBound
