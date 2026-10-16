import Fpy.DigitBound.Copy
import Fpy.DigitBound.Table
import FpyTest.Rewrite.Lower

/-!
# Table 2

D-Arith's premise for `x + y` under `R`, from Table 2's rows; and a witness that
the draft's `IEEE754(es, nb, rm)` row, `μ ≤ m + 1`, fails below the smallest
subnormal: rounding `2⁻¹¹` up into E4M3 gives `2⁻⁹`.
-/

namespace FpyTest

open Fpy Fpy.DigitBound Mpfx

example {decode : List (Label × Val) → Option RoundCtx} (l₁ m₁ l₂ m₂ : EInt) :
    ArithOK decode (some .real) .add [(.const l₁, .const m₁, none), (.const l₂, .const m₂, none)]
      0 2 (bounds 0 (.min (.const l₁) (.const l₂)) (.add (.max (.const m₁) (.const m₂))
        (.const (1 : ℤ))) ⟨trivial, trivial⟩ ⟨⟨trivial, trivial⟩, trivial⟩ ++ [])
      (.var 1) (.var 0) :=
  ArithOK.comp (opOK_add (.inl rfl) (by exact ⟨trivial, trivial⟩)
    (by exact ⟨⟨trivial, trivial⟩, trivial⟩)) rndOK_real
    (fresh_bounds 0 _ _) (Fresh.nil 2) fun _ h => by obtain rfl := Option.mem_some_iff.mp h; trivial

theorem log_two_zpow (z : ℤ) : Int.log 2 ((2 : ℝ) ^ z) = z := by
  simpa using Int.log_zpow (R := ℝ) (b := 2) (by norm_num) z

/-- Under the unknown context `?`, which admits `R`, the "all others" row applies. -/
example {decode : List (Label × Val) → Option RoundCtx} {l m : Term} (hl : l.Below 0) :
    RndOK decode none l m 0 2
      (bounds 0 (.min l (.const ⊥)) (.max (.const ⊤) (.const ⊤)) ⟨hl.mono (Nat.le_succ 0), trivial⟩
        ⟨trivial, trivial⟩) (.var 1) (.var 0) :=
  rndOK_any (Lo := .const ⊥) (Ho := .const ⊤) hl trivial trivial fun ι C r _ hr => by
    cases C with
    | real => exact .inl (Option.some.inj hr).symm
    | ctx fs =>
      obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.mp hr
      exact .inr ⟨c, rfl, fun _ => .inr ⟨bot_le, le_top⟩, fun _ => .inl (.inr ⟨bot_le, le_top⟩)⟩
    | _ => cases hr

/-- RTP into E4M3 sends `2⁻¹¹` to `2⁻⁹`. -/
theorem rtp_e4m3 :
    ((rndUnbounded e4m3 .toPositive (2 ^ (-11 : ℤ)) (not_isUndefined_toPositive _) :
      Mpfx.Dyadic) : ℝ) = 2 ^ (-9 : ℤ) := by
  rw [RoundsFinite.unique_toPositive (rndUnbounded_satisfies _ _ _ _) (rndUp_spec _ _), rndUp_eq,
    canonicalExp_expFinite (p := 4) rfl rfl (by positivity), abs_of_pos (by positivity),
    log_two_zpow]
  norm_num

theorem draft_ieee_rm_bound :
    msbOf (.finite ((rndUnbounded e4m3 .toPositive (2 ^ (-11 : ℤ))
      (not_isUndefined_toPositive _) : Mpfx.Dyadic) : ℝ)) = ((-9 : ℤ) : EInt) ∧
    msbOf (.finite ((2 : ℝ) ^ (-11 : ℤ))) + ((1 : ℤ) : EInt) = ((-10 : ℤ) : EInt) := by
  rw [rtp_e4m3, msbOf_of_ne_zero (by positivity), msbOf_of_ne_zero (by positivity),
    abs_of_pos (by positivity), abs_of_pos (by positivity), log_two_zpow, log_two_zpow,
    coe_add_coe]
  norm_num

/-- A list summary's constraints bound every element: under `μ ≤ 10`, the
summary `⟨[λ, μ], _⟩` does not describe `[2²⁰]`. -/
example (ι : Asgn) :
    ¬ Describes [Con.upper 1 (.const (10 : ℤ)) trivial] ι
      (.list (.num (.var 0) (.var 1) none) 0) (.list [.num (.finite ((2 : ℝ) ^ (20 : ℤ)))]) := by
  intro h
  cases h with | list hall => cases hall with | cons _ hs hd _ => cases hd with | num hu =>
  rcases hu with h | ⟨-, hm, -⟩
  · cases h
  · have h10 := hs _ (List.mem_singleton_self _)
    simp only [Con.upper, Term.eval] at h10
    rw [msbOf_of_ne_zero (by positivity), abs_of_pos (by positivity), log_two_zpow] at hm
    simp only [Term.eval] at hm
    rw [← hm] at h10
    exact absurd (WithBotTop.coe_le_coe.mp h10) (by norm_num)

/-- D-Index's copy premises hold for a numeric element whose summary has
variables `[0, 2)`, copied to `[5, 7)` with its constraints. -/
example {Ψg : List Con} (hnd : (Ψg.map Con.head).Nodup) {l m : Term} (hl : l.Below 2)
    (hm : m.Below 2) :
    DVal.Copy 5 7 Ψg (copyCons Ψg 0 2 5 (by omega)) (.num l m none) 0
        (.num (l.rename (shift 0 2 5)) (m.rename (shift 0 2 5)) none) ∧
      Fresh 5 7 (copyCons Ψg 0 2 5 (by omega)) :=
  ⟨copy_num (a := 0) (b := 2) (n := 5) (by omega) (by omega) hl hm (by simp),
    fresh_copyCons (a := 0) (b := 2) (n := 5) (by omega) (by omega) hnd⟩

end FpyTest
