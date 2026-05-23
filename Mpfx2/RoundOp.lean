import Mpfx2.Rounding

/-!
# Constructive rounding function (Mpfx2)

The noncomputable layer of the rounding architecture. See
`Mpfx2/Rounding.lean` for the relational spec `Rounds`; this file
provides the function `rnd` and bridges to the relation.

`rnd` is `noncomputable` because of `Int.log : ℝ → ℤ` and because the
`if`-then-else branches reduce undecidable real comparisons via
`Classical.propDecidable`. The bridge lemma `rnd_iff_rounds` connects
this to the relational layer.

Theorems about `Rounds` alone live in `Mpfx2/Rounding.lean` and stay
in constructive logic; the classical commitment is isolated here.
-/

namespace Mpfx2

-- FLoPS-style: noncomputable definitions rely on Mathlib's
-- `Real.decidableLT`/`decidableEq` plus the classical `propDecidable`
-- fallback for `if-then-else` on undecidable real comparisons. Marked
-- `local` so this taint is scoped to `RoundOp.lean`.
attribute [local instance] Classical.propDecidable

/-- Canonical exponent for representing `x` in `F`. Junk value `0` when
`Format.IsUndefined F _` (those cases are filtered earlier). -/
noncomputable def Format.canonicalExp (F : Format) (x : ℝ) : ℤ :=
  match F.p, F.exp with
  | ⊤, ⊥ => 0  -- junk; never used (filtered by IsUndefined)
  | ⊤, (e : ℤ) => e
  | (p : ℕ+), ⊥ =>
      if x = 0 then 0 else Int.log 2 |x| + 1 - (p : ℤ)
  | (p : ℕ+), (e : ℤ) =>
      if x = 0 then e
      else max (Int.log 2 |x| + 1 - (p : ℤ)) e

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

/-- Promote `F : Format` to `ParityFormat` from a `¬ IsUndefined .toOdd`
witness. The two non-degeneracy invariants both fall out of the
negation. -/
private def Format.toParityFormatOfToOdd
    (F : Format) (h : ¬ F.IsUndefined .toOdd) : ParityFormat := by
  refine ⟨⟨F, ?_⟩, ?_⟩
  · by_contra h_neg; push Not at h_neg
    exact h (Or.inl ⟨h_neg.1, h_neg.2⟩)
  · by_contra h_neg; push Not at h_neg
    exact h (Or.inr ⟨h_neg.1, h_neg.2, Or.inl rfl⟩)

/-- Promote `F : Format` to `ParityFormat` from a
`¬ IsUndefined (.nearest .toEven)` witness. -/
private def Format.toParityFormatOfNearestEven
    (F : Format) (h : ¬ F.IsUndefined (.nearest .toEven)) : ParityFormat := by
  refine ⟨⟨F, ?_⟩, ?_⟩
  · by_contra h_neg; push Not at h_neg
    exact h (Or.inl ⟨h_neg.1, h_neg.2⟩)
  · by_contra h_neg; push Not at h_neg
    exact h (Or.inr ⟨h_neg.1, h_neg.2, Or.inr rfl⟩)

/-- The unbounded rounding step: produce a `Dyadic` per `rm`, *without*
checking `F.b`. Used by `rnd` as the candidate value that the bound check
filters. -/
noncomputable def rndUnbounded (F : Format) (rm : RoundingMode) (x : ℝ)
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
`.finite y`; otherwise `.overflow`. -/
noncomputable def rnd (F : Format) (rm : RoundingMode) (x : ℝ) : RoundResult :=
  if h_undef : F.IsUndefined rm then
    .undefined
  else
    let y := rndUnbounded F rm x h_undef
    if Format.boundOK F.b y then .finite y else .overflow

/-! ### Soundness of `rndUnbounded`

The two key obligations linking `rnd` and `Rounds`:

* `rndUnbounded_satisfies` — `rndUnbounded F rm x h` is a value
  satisfying `RoundsFinite F.unbounded rm x`.
* `rndUnbounded_unique` — uniquely so: any `y` satisfying that spec
  equals `rndUnbounded F rm x h`.

Together these say `rndUnbounded` *is* the unbounded rounding. They
are mode-specific arithmetic obligations; deferred. -/

/-- The constructive `rndUnbounded` satisfies the unbounded rounding spec. -/
theorem rndUnbounded_satisfies (F : Format) (rm : RoundingMode) (x : ℝ)
    (h : ¬ F.IsUndefined rm) :
    RoundsFinite F.unbounded rm x (rndUnbounded F rm x h) := by
  sorry

/-- Uniqueness: any `y` satisfying the unbounded rounding spec equals
`rndUnbounded F rm x h`. -/
theorem rndUnbounded_unique (F : Format) (rm : RoundingMode) (x : ℝ)
    (h : ¬ F.IsUndefined rm) {y : Dyadic}
    (hy : RoundsFinite F.unbounded rm x y) :
    y = rndUnbounded F rm x h := by
  sorry

/-! ### Bridge lemma

The `RoundResult`-typed `Rounds` collapses the per-mode bridges to one
uniform statement: `rnd` and `Rounds` agree on the same `RoundResult`. -/

theorem rnd_iff_rounds (F : Format) (rm : RoundingMode) (x : ℝ) (r : RoundResult) :
    rnd F rm x = r ↔ Rounds F rm x r := by
  cases r with
  | undefined =>
    -- `Rounds F rm x .undefined` reduces to `F.IsUndefined rm` by definition.
    -- `rnd F rm x = .undefined` is true iff the outer `if` of `rnd` fires,
    -- i.e., iff `F.IsUndefined rm` holds.
    change rnd F rm x = .undefined ↔ F.IsUndefined rm
    constructor
    · intro h_eq
      by_contra h_undef
      unfold rnd at h_eq
      rw [dif_neg h_undef] at h_eq
      -- `let y := rndUnbounded ...; if boundOK ... then .finite y else .overflow`
      -- doesn't auto-reduce; force it with `dsimp only` so `split_ifs`
      -- can see the inner conditional and decompose to constructor-mismatch.
      dsimp only at h_eq
      split_ifs at h_eq
    · intro h_undef
      unfold rnd
      rw [dif_pos h_undef]
  | overflow =>
    change rnd F rm x = .overflow ↔
      ¬ F.IsUndefined rm ∧
      ∃ y, RoundsFinite F.unbounded rm x y ∧ ¬ Format.boundOK F.b y
    constructor
    · -- Forward: rnd = .overflow ⇒ ¬ IsUndefined ∧ witness via rndUnbounded.
      intro h_eq
      have h_undef : ¬ F.IsUndefined rm := by
        intro h
        unfold rnd at h_eq
        rw [dif_pos h] at h_eq
        exact RoundResult.noConfusion h_eq
      refine ⟨h_undef, rndUnbounded F rm x h_undef,
              rndUnbounded_satisfies F rm x h_undef, ?_⟩
      -- Show ¬ boundOK F.b (rndUnbounded ...) from h_eq.
      intro hb
      unfold rnd at h_eq
      rw [dif_neg h_undef] at h_eq
      dsimp only at h_eq
      rw [if_pos hb] at h_eq
      exact RoundResult.noConfusion h_eq
    · -- Reverse: ⟨h_undef, y, RoundsFinite y, ¬ boundOK y⟩ ⇒ rnd = .overflow.
      -- By uniqueness, y = rndUnbounded; transport ¬ boundOK to rndUnbounded.
      rintro ⟨h_undef, y, hRF, hBN⟩
      have h_y_eq : y = rndUnbounded F rm x h_undef :=
        rndUnbounded_unique F rm x h_undef hRF
      unfold rnd
      rw [dif_neg h_undef]
      dsimp only
      rw [if_neg (h_y_eq ▸ hBN)]
  | finite y => sorry

end Mpfx2
