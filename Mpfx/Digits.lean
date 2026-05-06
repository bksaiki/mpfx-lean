import Mpfx.Format
import Mathlib.Data.Int.Log

/-!
# Lemmas 5.1 and 5.2 — digit positions of roundings

Lemma 5.1 says the number of binary digits a rounding `rnd_{A(p,exp,b),rm}(x)`
keeps is a function of `(p, exp, x)` only — not of `b` or `rm`. In our
spec-relational setup we capture this by *defining* `numDigits` via the same
case analysis the paper's proof uses; the type signature `ℕ∞ → WithBot ℤ → ℝ → ℕ`
*is* Lemma 5.1.

Lemma 5.2 says shifting parameters by `(p, exp) ↦ (p + k, exp − k)` shifts the
digit count by `+k`. We prove this for `x ≠ 0` and non-degenerate formats
(the case `p = ⊤ ∧ exp = ⊥` is excluded — there is no quantum and no precision,
so no rounding happens).
-/

namespace Mpfx

namespace AbstractFormat

/-- Subtract a natural number from a `WithBot ℤ`. `⊥ - k = ⊥`. -/
def expSub (e : WithBot ℤ) (k : ℕ) : WithBot ℤ :=
  e.map (· - (k : ℤ))

@[simp] theorem expSub_bot (k : ℕ) : expSub ⊥ k = ⊥ := rfl

@[simp] theorem expSub_coe (e : ℤ) (k : ℕ) :
    expSub (e : WithBot ℤ) k = ((e - k : ℤ) : WithBot ℤ) := rfl

/-- **Lemma 5.1**: number of binary digits a format `(p, exp)` rounds `x` to.

Case analysis follows the paper's proof of Lemma 5.1:
- `p = ⊤, exp = ⊥`: degenerate (no rounding happens); return `0`.
- `p = ⊤, exp = e`: fixed-point with quantum `2^e`. Digits = `⌊log₂|x|⌋ - e + 1`.
- `p = n, exp = ⊥`: pure floating-point with precision `n`. Digits = `n`.
- `p = n, exp = e`: floating-point with min quantum `2^e`. Digits = `min(n, e' - e + 1)`
  where `e' = ⌊log₂|x|⌋`. The `min` captures subnormal behaviour.

The result is `ℤ`-valued: a negative or zero result indicates the rounding
underflows to `0`. For `x = 0` we return `0` by convention. -/
noncomputable def numDigits (p : ℕ∞) (exp : WithBot ℤ) (x : ℝ) : ℤ :=
  if x = 0 then 0
  else
    let e : ℤ := Int.log 2 |x|
    match p, exp with
    | ⊤, ⊥ => 0
    | ⊤, ((e' : ℤ) : WithBot ℤ) => e - e' + 1
    | ((n : ℕ) : ℕ∞), ⊥ => (n : ℤ)
    | ((n : ℕ) : ℕ∞), ((e' : ℤ) : WithBot ℤ) => min (n : ℤ) (e - e' + 1)

/-- **Lemma 5.2**: shifting `(p, exp)` by `(+k, -k)` shifts digits by `+k`.

Excludes the degenerate `p = ⊤ ∧ exp = ⊥` case where `numDigits` returns `0`
regardless. Requires `x ≠ 0`. -/
theorem numDigits_shift (p : ℕ∞) (exp : WithBot ℤ) (k : ℕ) (x : ℝ) (hx : x ≠ 0)
    (hnd : p ≠ ⊤ ∨ exp ≠ ⊥) :
    numDigits (p + k) (expSub exp k) x = numDigits p exp x + k := by
  unfold numDigits
  simp only [hx, ↓reduceIte]
  match hp : p, hexp : exp with
  | ⊤, ⊥ => simp at hnd
  | ⊤, ((e' : ℤ) : WithBot ℤ) =>
    change Int.log 2 |x| - (e' - (k : ℤ)) + 1 = Int.log 2 |x| - e' + 1 + k
    ring
  | ((n : ℕ) : ℕ∞), ⊥ =>
    change ((n + k : ℕ) : ℤ) = (n : ℤ) + k
    push_cast; ring
  | ((n : ℕ) : ℕ∞), ((e' : ℤ) : WithBot ℤ) =>
    change min ((n + k : ℕ) : ℤ) (Int.log 2 |x| - (e' - (k : ℤ)) + 1)
        = min (n : ℤ) (Int.log 2 |x| - e' + 1) + k
    have h1 : Int.log 2 |x| - (e' - (k : ℤ)) + 1 = Int.log 2 |x| - e' + 1 + k := by ring
    rw [h1]
    omega

end AbstractFormat

end Mpfx
