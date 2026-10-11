import Mpfx.Rounding.Defs
import Mpfx.Format.CanonicalExp

/-!
# The rounding function

`rnd` and the integer steps it dispatches to. The relational spec is
`Mpfx/Rounding/Defs.lean`, its consequences `Mpfx/Rounding/Basic.lean`; `rnd_iff_rounds`
(in `Mpfx/Rounding/Op.lean`) connects the two.

`rnd` is `noncomputable`: `Int.log : ℝ → ℤ`, and the branches decide real
comparisons through `Classical.propDecidable`. That commitment is confined to
this directory.
-/

namespace Mpfx

-- FLoPS-style: noncomputable definitions rely on Mathlib's
-- `Real.decidableLT`/`decidableEq` plus the classical `propDecidable`
-- fallback for `if-then-else` on undecidable real comparisons. Marked
-- `local` so this taint is scoped per file.
attribute [local instance] Classical.propDecidable

/-- Integer-rounding step. Picks the integer `c` for which `c · 2^e` is the
value that mode `rm` selects for `x`: the floor or ceiling of the scaled
mantissa `s`, or, for the parity and nearest modes, `⌊s⌋` or `⌊s⌋ + 1` by the
fraction `s − ⌊s⌋`, the sign of `x`, and the parity of the floor point in `F`. -/
noncomputable def rndInt (F : FiniteFormat) (rm : RoundingMode) (x : ℝ) (e : ℤ) : ℤ :=
  let s := x * (2 : ℝ) ^ (-e)
  let lo := ⌊s⌋
  let δ := s - (lo : ℝ)
  match rm with
  | .toZero    => if 0 ≤ x then ⌊s⌋ else ⌈s⌉
  | .toNegative => ⌊s⌋
  | .toPositive => ⌈s⌉
  | .awayZero   => if 0 ≤ x then ⌈s⌉ else ⌊s⌋
  | .toOdd =>
      if (lo : ℝ) = s then lo                   -- x is exactly on lo
      else if F.IsOdd (Dyadic.ofIntZpow lo e) then lo else lo + 1
  | .nearest .awayZero =>
      if δ < 1/2 then lo
      else if 1/2 < δ then lo + 1
      else if 0 ≤ x then lo + 1 else lo         -- tie: away from zero
  | .nearest .toEven =>
      if δ < 1/2 then lo
      else if 1/2 < δ then lo + 1
      else if F.IsEven (Dyadic.ofIntZpow lo e) then lo else lo + 1   -- tie: even

/-- The unbounded rounding step: the integer step at the canonical exponent,
*without* checking `F.b`. Used by `rnd` as the candidate value that the bound
check filters. The body does not consult `_h_undef`; it restricts
`rndUnbounded` to the pairs where `rnd` calls it. -/
noncomputable def rndUnbounded (F : FiniteFormat) (rm : RoundingMode) (x : ℝ)
    (_h_undef : ¬ F.IsUndefined rm) : Dyadic :=
  Dyadic.ofIntZpow (rndInt F rm x (F.canonicalExp x)) (F.canonicalExp x)

/-- Rounding into `F` under mode `rm`, with special inputs sent through `S`.
A real input goes to `rndUnbounded`, then the bound is checked: the rounded
value if it fits, otherwise the overflow table `O` at the value's sign. -/
noncomputable def rnd (F : FiniteFormat) (S : SpecialMap F.toFormat)
    (O : OverflowMap F.toFormat) (rm : RoundingMode) : WithSpecial ℝ → RoundResult
  | .special s => .value (S.map s)
  | .finite x =>
    if h_undef : F.IsUndefined rm then
      .undefined
    else
      let y := rndUnbounded F rm x h_undef
      if Format.boundOK F.b y then .value (.finite y)
      else .value (O.map (decide ((y : ℚ) < 0)))

/-! The per-mode proofs that `rndUnbounded` satisfies the spec live in
`Directed.lean`, `ToOdd.lean` and `Nearest.lean`. -/

end Mpfx
