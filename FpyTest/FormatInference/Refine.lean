import Fpy.FormatInference.Analysis

/-!
# Condition refinement on the examples of §4.2
-/

namespace FpyTest

open Fpy Mpfx

variable {decode : List (Label × Val) → Option RoundCtx} {c : Ceiling}

/-- `Γ(x) = {1, 2, 4}`. -/
noncomputable def Γ₀ : AEnv (Fmt.domain c) :=
  AEnv.single "x" (.fmt (.set {.finite 1, .finite 2, .finite 4}))

/-- The test `x < 3`. -/
noncomputable def lt3 : Atom := ⟨"x", .id, .lt, .finite 3, false⟩

/-- In the branch where `x < 3`, `x` is narrowed by the test… -/
example : refine (decode := decode) (some .real)
      (.exact (show ExactOp from .lt) [.var "x", .num (.finite 3)]) true (Γ₀ (c := c)) "x" =
      some (.fmt (lt3.narrowFmt true (.set {.finite 1, .finite 2, .finite 4}))) := by
  simp [refine, parseAtom, Cmp.ofOp, parseLhs, Atom.refine, Γ₀, AEnv.single, AEnv.update, lt3]

/-- …to `{1, 2}`. -/
example : (.finite 2 : Num) ∈ (lt3.narrowFmt true (.set {.finite 1, .finite 2, .finite 4})).γ ∧
    (.finite 4 : Num) ∉ (lt3.narrowFmt true (.set {.finite 1, .finite 2, .finite 4})).γ := by
  simp only [Atom.narrowFmt, Fmt.γ, Finset.coe_filter, Set.mem_setOf_eq]
  norm_num [Atom.Holds, Atom.CmpHolds, Lhs.eval, Cmp.eval, Num.lt, lt3]

end FpyTest
