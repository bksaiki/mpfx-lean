import Fpy.Sum

/-!
# `sum`

Under `R`, `sum [1, 2, 3]` returns `6`.
-/

namespace FpyTest

open Fpy Mpfx

example {decode : List (Label × Val) → Option RoundCtx} (Φ : Program (fpy decode)) :
    Exec Φ (Store.single "xs" (.list ([1, 2, 3].map fun x : ℝ => .num (.finite x)))) .real
      sumBody (.ret (.num (.finite 6))) := by
  have h := sumBody_run (Φ := Φ) (C := .real) (r := id) rfl [.finite 1, .finite 2, .finite 3]
  convert h using 3
  simp [sumVal, Num.add]; norm_num

end FpyTest
