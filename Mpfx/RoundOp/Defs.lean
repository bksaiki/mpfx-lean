import Mpfx.Rounding
import Mpfx.CanonicalExp

/-!
# Constructive rounding: definitions + soundness helpers

The noncomputable layer of the rounding architecture. See
`Mpfx/Rounding.lean` for the relational spec `Rounds`; this file
provides the function `rnd` and the shared arithmetic helpers used by
the per-mode soundness/uniqueness proofs.

`rnd` is `noncomputable` because of `Int.log : ℝ → ℤ` and because the
`if`-then-else branches reduce undecidable real comparisons via
`Classical.propDecidable`. The bridge lemma `rnd_iff_rounds` connects
this to the relational layer.

Theorems about `Rounds` alone live in `Mpfx/Rounding.lean` and stay
in constructive logic; the classical commitment is isolated here.
-/

namespace Mpfx

-- FLoPS-style: noncomputable definitions rely on Mathlib's
-- `Real.decidableLT`/`decidableEq` plus the classical `propDecidable`
-- fallback for `if-then-else` on undecidable real comparisons. Marked
-- `local` so this taint is scoped per file.
attribute [local instance] Classical.propDecidable

/-- Integer-rounding step for the format-agnostic modes. Picks the
integer `c` for which `c · 2^e` is the F-grid value selected by mode
`rm` from input `x`. Parity-aware modes (`.toOdd`, `.nearest .toEven`)
are handled separately by `rndParity` since they need format info to
disambiguate. -/
noncomputable def rndInt (rm : RoundingMode) (x : ℝ) (e : ℤ) : ℤ :=
  let s := x * (2 : ℝ) ^ (-e)
  match rm with
  | .toZero    => if 0 ≤ x then ⌊s⌋ else ⌈s⌉
  | .toNegative => ⌊s⌋
  | .toPositive => ⌈s⌉
  | .awayZero   => if 0 ≤ x then ⌈s⌉ else ⌊s⌋
  | .nearest .awayZero =>
      let lo := ⌊s⌋
      let δ := s - (lo : ℝ)
      if δ < 1/2 then lo
      else if 1/2 < δ then lo + 1
      else if 0 ≤ x then lo + 1 else lo   -- tie: away from zero
  -- .toOdd and .nearest .toEven are handled by `rndParity` (need parity).
  | _ => ⌊s⌋   -- unreachable: filtered out before `rndInt` is called

/-- Parity-aware integer-rounding step. Identifies the two F-adjacents
to `x` at exponent `e` (via floor and ceiling of the scaled mantissa),
then picks the one whose parity satisfies the mode's rule. -/
noncomputable def rndParity (F : ParityFormat) (rm : RoundingMode)
    (x : ℝ) (e : ℤ) : Dyadic :=
  let s := x * (2 : ℝ) ^ (-e)
  let lo : ℤ := ⌊s⌋
  let dlo : Dyadic := Dyadic.ofIntZpow lo e
  let dhi : Dyadic := Dyadic.ofIntZpow (lo + 1) e
  match rm with
  | .toOdd =>
      if (lo : ℝ) = s then dlo                  -- x is exactly on lo
      else if F.IsOdd dlo then dlo else dhi
  | .nearest .toEven =>
      let δ := s - (lo : ℝ)
      if δ < 1/2 then dlo
      else if 1/2 < δ then dhi
      else if F.IsEven dlo then dlo else dhi    -- tie → even
  | _ => dlo   -- unreachable: `rndParity` only called for parity modes

/-- The unbounded rounding step: produce a `Dyadic` per `rm`, *without*
checking `F.b`. Used by `rnd` as the candidate value that the bound check
filters. -/
noncomputable def rndUnbounded (F : FiniteFormat) (rm : RoundingMode) (x : ℝ)
    (h_undef : ¬ F.IsUndefined rm) : Dyadic :=
  if h1 : rm = .toOdd then
    rndParity (F.toParityFormatOfToOdd (h1 ▸ h_undef)) .toOdd x (F.canonicalExp x)
  else if h2 : rm = .nearest .toEven then
    rndParity (F.toParityFormatOfNearestEven (h2 ▸ h_undef))
      (.nearest .toEven) x (F.canonicalExp x)
  else
    Dyadic.ofIntZpow (rndInt rm x (F.canonicalExp x)) (F.canonicalExp x)

/-- The rounded value of `x` in `F` under mode `rm`, as a `RoundResult`.
Dispatches to `rndUnbounded` for the round-without-bound value, then
checks the format's magnitude bound: if the rounded result fits, return
`.finite y`; otherwise `.overflow b` where `b` records the sign of the
would-be result (`true` for positive). -/
noncomputable def rnd (F : FiniteFormat) (rm : RoundingMode) (x : ℝ) : RoundResult :=
  if h_undef : F.IsUndefined rm then
    .undefined
  else
    let y := rndUnbounded F rm x h_undef
    if Format.boundOK F.b y then .finite y
    else .overflow (if (0 : ℚ) < (y : ℚ) then true else false)

/-! ### Soundness of `rndUnbounded`

The two key obligations linking `rnd` and `Rounds`:

* `rndUnbounded_satisfies` — `rndUnbounded F rm x h` is a value
  satisfying `RoundsFinite F.unbounded rm x`.
* `rndUnbounded_unique` — uniquely so: any `y` satisfying that spec
  equals `rndUnbounded F rm x h`.

Together these say `rndUnbounded` *is* the unbounded rounding. They
are mode-specific arithmetic obligations; deferred. -/

end Mpfx
