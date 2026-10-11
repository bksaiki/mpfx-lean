import Fpy.FormatInference

/-!
# Format inference on a toy signature

A signature with exact `+` and `×` on finite reals, whose every context rounds
down to an integer, and the most precise format domain, sets of numbers. The
examples check the two rules that differ from the draft.
-/

namespace FpyTest

open Fpy Mpfx

inductive Op where
  | add
  | mul

/-- Rounds a finite value down to an integer. -/
noncomputable def floorNum : Num → Num
  | .finite x => .finite ⌊x⌋
  | n => n

theorem floorNum_floorNum (n : Num) : floorNum (floorNum n) = floorNum n := by
  cases n <;> simp [floorNum]

noncomputable abbrev L : Signature where
  ArithOp := Op
  ExactOp := Empty
  arith
    | .add, [.finite x, .finite y] => some (.finite (x + y))
    | .mul, [.finite x, .finite y] => some (.finite (x * y))
    | _, _ => none
  exact op _ := op.elim
  ρ _ := some floorNum

open Classical in
noncomputable abbrev D : FormatDomain where
  Fmt := Set Num
  γ F := F
  top := Set.univ
  bot := ∅
  join := (· ∪ ·)
  sub F₁ F₂ := decide (F₁ ⊆ F₂)
  ofNum n := {n}
  mem_top _ := trivial
  mem_join_left h := Or.inl h
  mem_join_right h := Or.inr h
  sub_sound h := of_decide_eq_true h
  mem_ofNum _ := rfl

/-- The collecting analysis: each `op♯` is the image of its operator, and a
context's format is the range of its rounding function. -/
noncomputable abbrev A : Analysis L D where
  arith op Fs := {n | ∃ ns, List.Forall₂ (fun n F => n ∈ D.γ F) ns Fs ∧ L.arith op ns = some n}
  exact op _ := op.elim
  ctxFmt C := (C.rnd L).map Set.range
  ctxOf _ := none
  refine _ _ _ Γ := Γ

theorem rnd_idem {C : Val} {r : Num → Num} (h : C.rnd L = some r) (n : Num) :
    r (r n) = r n := by
  cases C <;> simp only [Val.rnd, reduceCtorEq] at h
  · obtain rfl := Option.some.inj h
    rfl
  · obtain rfl := Option.some.inj h
    exact floorNum_floorNum n

theorem A_sound (Φ : Program L) : A.Sound Φ where
  arith h hop := ⟨_, h, hop⟩
  exact {op} := op.elim
  ctxFmt {C FC r} hFC hr := by
    simp only [hr, Option.map_some, Option.some.injEq] at hFC
    subst hFC
    exact ⟨fun n => ⟨n, rfl⟩, fun _ ⟨m, hm⟩ => hm ▸ rnd_idem hr m⟩
  ctxOf h := by simp at h
  refine hΓ _ _ := hΓ

/-- `ctx {}`: a context that rounds down. -/
def floorCtx : Val := .ctx []

/-! ### Rounding under the unknown context `?` -/

/-- The draft keeps the exact bound under `?` (`F ⊆ F_? = R*` always holds),
but a context may round: `1/2 + 0` under `floorCtx` is `0`, outside the exact
bound `{1/2}`. -/
theorem draft_rnd_unknown_unsound :
    Eval (L := L) (fun _ => none) (fun _ => none) floorCtx
        (.arith Op.add [.num (.finite (1 / 2)), .num (.finite 0)]) (.num (.finite 0)) ∧
      (.finite 0 : Num) ∉
        D.γ (A.arith Op.add [D.ofNum (.finite (1 / 2)), D.ofNum (.finite 0)]) := by
  constructor
  · have h := Eval.arith (Φ := (fun _ => none : Program L)) (σ := fun _ => none)
      (C := floorCtx) (op := Op.add) (ns := [.finite (1 / 2), .finite 0]) (r := floorNum)
      (.cons .num (.cons .num .nil)) rfl rfl
    convert h using 2
    simp only [floorNum, add_zero, WithSpecial.finite.injEq]
    norm_num [Int.floor_eq_iff]
  · rintro ⟨ns, hns, hop⟩
    obtain ⟨rfl, rfl⟩ : ns = [.finite (1 / 2), .finite 0] := by
      rcases hns with _ | ⟨rfl, _ | ⟨rfl, _ | _⟩⟩
      rfl
    simp at hop

/-- Under `?` the bound is `⊤`. -/
example (F : D.Fmt) : A.rnd none F = D.top := rfl

/-! ### A context passed as an argument stays known -/

/-- `f(c) = with c in ret 2 × 3`. -/
noncomputable def body : Stmt L :=
  .withCtx (.var "c") (.ret (.arith Op.mul [.num (.finite 2), .num (.finite 3)]))

noncomputable def Φ : Program L := fun f => if f = "f" then some ("c", body) else none

/-- Called as `f(R)` from a rounding context, `f`'s body runs under `R`… -/
example : AEval A Φ (fun _ => none) (some floorCtx) (.call "f" .real)
    (.fmt (A.rnd (some .real) (A.arith Op.mul [D.ofNum (.finite 2), D.ofNum (.finite 3)]))) :=
  .call (y := "c") (s := body) (by simp [Φ]) .real
    (.withCtx (C := .real) (.var (x := "c") (by simp [AEnv.single]))
      (.ret (.arith (.cons .num (.cons .num .nil)))))

/-- …so its product keeps the exact bound. -/
example (F : D.Fmt) : A.rnd (some .real) F = F := rfl

end FpyTest
