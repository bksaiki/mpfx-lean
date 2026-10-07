import Mpfx.DoubleRounding.Counterexample.Instances

/-!
# Counterexamples to the invalid double-rounding pairings (§5.2)

The ten `no_rnd<rm₂>_<rm₁>` theorems refute every mode pairing absent
from the double-rounding rules: rounding `x` first in `F₂` under `rm₂` and then in `F₁`
under `rm₁` can disagree with rounding `x` directly in `F₁` under `rm₁`.
Each takes an arbitrary **unbounded** inner format `F₁ = 𝒜(p₁, exp₁, ⊤)`
— the precision `p₁` and quantum `exp₁` are otherwise unconstrained — and
holds for **every** `F₂` satisfying the stated containment, so no side
condition on `(p₁, exp₁, p₂, exp₂, b₂)` can validate these pairings.

All ten are proven once against `AnchorNeighborhood F₁`: three
consecutive `F₁`-elements `lo2 < lo < hi` (lower gap `2^s`, upper gap
`2^t` — equal away from a binade boundary, but `s = t − 1` when an anchor
is a power of two), with `lo2`, `hi` even, `hi` not odd, their
`F₁`-adjacency facts, and `F₂`-side local-step gap bounds. `neighborhoodOf`
dispatches on `F₁.p` then `F₁.exp`:

* `quantumNeighborhood` (`p₁` finite `≥ 2`, `exp₁ = e`): anchors
  `2·2^e < 3·2^e < 4·2^e`;
* `topNeighborhood` (`p₁ = ⊤`, so `exp₁ = e` by the format invariant):
  the same anchors on the full integer grid of step `2^e`;
* `floatingNeighborhood` (`p₁` finite `≥ 2`, `exp₁ = ⊥`): anchors
  `s·2^t < (s+1)·2^t < (s+2)·2^t`, `s = 2^(p₁−1)`, inside the binade
  `[2^(t+p₁−1), 2^(t+p₁))`;
* `powerOfTwoNeighborhood` (`p₁ = 1`, `exp₁ = e`): the power-of-two
  anchors `2^(e+1) < 2^(e+2) < 2^(e+3)`, where parity is read from the
  exponent rather than the significand.

The only `ParityFormat` left out is `𝒜(1, ⊥, ·)` — excluded by the
`ParityFormat` invariant itself (its even/odd classification is undefined).

Every witness is `anchor ± δ` with `δ = 2^(K−2)` a quarter of `F₂`'s
*local step* at the anchor: the global quantum `2^f₂` when `F₂.exp = f₂`
is finite, and the binade step `2^(E−q₂+1)` when `F₂.exp = ⊥` (where the
`FiniteFormat` invariant forces `F₂.p = q₂` finite). Only the ten
counterexamples are public; everything else is `private`.
-/

namespace Mpfx

namespace Cex

/-! ## The unified counterexamples

One theorem per invalid pairing, over an arbitrary unbounded
`F₁ : ParityFormat` (`b = ⊤`); the precision `p` and quantum `exp` are
otherwise unconstrained (the sole excluded shape `𝒜(1, ⊥, ·)` is ruled
out by the `ParityFormat` invariant). In the doc comments,
`lo2 < lo < hi` are the neighborhood anchors (`lo` odd, `lo2`/`hi` even)
and `δ` is a quarter of `F₂`'s local step at the anchor. -/

/-- A `ParityFormat` is determined by its three data fields: with
`p = p₁`, `exp = e`, `b = ⊤` it *is* the quantum target format. -/
private theorem eq_F₁_g {F₁ : ParityFormat} {p₁ : ℕ} {e : ℤ}
    (hp_ge_2 : 2 ≤ p₁)
    (hp : F₁.p = (p₁ : Prec))
    (hexp : F₁.exp = (e : QExp))
    (hb : F₁.b = ⊤) :
    F₁ = F₁_g p₁ hp_ge_2 e := by
  obtain ⟨⟨⟨pp, ee, bb⟩, fin⟩, par⟩ := F₁
  subst hp hexp hb
  rfl

/-- With `p = p₁`, `exp = ⊥`, `b = ⊤` it *is* the floating target format. -/
private theorem eq_F₁f_g {F₁ : ParityFormat} {p₁ : ℕ}
    (hp_ge_2 : 2 ≤ p₁)
    (hp : F₁.p = (p₁ : Prec))
    (hexp : F₁.exp = ⊥)
    (hb : F₁.b = ⊤) :
    F₁ = F₁f_g p₁ hp_ge_2 := by
  obtain ⟨⟨⟨pp, ee, bb⟩, fin⟩, par⟩ := F₁
  subst hp hexp hb
  rfl

/-- With `p = ⊤`, `exp = e`, `b = ⊤` it *is* the full-precision target
format. -/
private theorem eq_F₁t_g {F₁ : ParityFormat} {e : ℤ}
    (hp : F₁.p = ⊤) (hexp : F₁.exp = (e : QExp))
    (hb : F₁.b = ⊤) :
    F₁ = F₁t_g e := by
  obtain ⟨⟨⟨pp, ee, bb⟩, fin⟩, par⟩ := F₁
  subst hp hexp hb
  rfl

/-- With `p = 1`, `exp = e`, `b = ⊤` it *is* the single-precision target
format. -/
private theorem eq_F₁p_g {F₁ : ParityFormat} {e : ℤ}
    (hp : F₁.p = ((1 : ℕ) : Prec))
    (hexp : F₁.exp = (e : QExp)) (hb : F₁.b = ⊤) :
    F₁ = F₁p_g e := by
  obtain ⟨⟨⟨pp, ee, bb⟩, fin⟩, par⟩ := F₁
  subst hp hexp hb
  rfl

/-- Every unbounded `ParityFormat` carries an anchor neighborhood,
whatever its precision and quantum: dispatch on `F₁.p`, then on `F₁.exp`.
The only excluded shape is `𝒜(1, ⊥, ·)`, ruled out by the `ParityFormat`
invariant. -/
private noncomputable def neighborhoodOf (F₁ : ParityFormat) (hb : F₁.b = ⊤) :
    AnchorNeighborhood F₁ :=
  match hP : F₁.p with
  | ⊤ =>
    -- `p = ⊤`: the `FiniteFormat` invariant forces a finite quantum.
    match hexp : F₁.exp with
    | none => False.elim (F₁.finite.elim (fun h => h hP) (fun h => h hexp))
    | some e => by
        rw [eq_F₁t_g (e := e) hP hexp hb]
        exact topNeighborhood e
  | (p₁ : ℕ) =>
    if hp1 : p₁ = (1 : ℕ) then
      -- `p = 1`: the `ParityFormat` invariant forces a finite quantum.
      have hP1 : F₁.p = ((1 : ℕ) : Prec) := by rw [hP, hp1]; rfl
      match hexp : F₁.exp with
      | none =>
        False.elim (F₁.parity.elim (fun h => h hP1) (fun h => h hexp))
      | some e => by
          rw [eq_F₁p_g (e := e) hP1 hexp hb]
          exact powerOfTwoNeighborhood e
    else
      have hp_ge_2 : 2 ≤ p₁ := by
        have h3 : 0 < p₁ := F₁.p_pos hP
        omega
      match hexp : F₁.exp with
      | none => by
          rw [eq_F₁f_g hp_ge_2 hP hexp hb]
          exact floatingNeighborhood p₁ hp_ge_2 0
      | some e => by
          rw [eq_F₁_g (e := e) hp_ge_2 hP hexp hb]
          exact quantumNeighborhood p₁ hp_ge_2 e

/-- **RNE → RNE.** One extra digit makes the midpoint of `(lo, hi)`
`F₂`-representable: the intermediate RNE lands exactly on it,
manufacturing a tie that breaks to the even `hi`, while the direct RNE
returns the strictly nearer `lo`. (Tight: with `F₂ = F₁`,
RNE ∘ RNE = RNE by idempotence.) -/
theorem no_rndRNE_RNE
    (F₁ : ParityFormat) (hb : F₁.b = ⊤)
    (F₂ : FiniteFormat)
    (hsub : (F₁.toFiniteFormat.extend 1).toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ (.nearest .toEven) x z ∧
      RoundsFinite F₁.toFiniteFormat (.nearest .toEven) (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat (.nearest .toEven) x w :=
  (neighborhoodOf F₁ hb).no_rndRNE_RNE F₂ hsub

/-- **RNE → RAZ.** `x = hi + δ`: the intermediate RNE rounds down onto
`hi`, which RAZ fixes — but the direct RAZ must be at least `x > hi`. -/
theorem no_rndRNE_RAZ
    (F₁ : ParityFormat) (hb : F₁.b = ⊤)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ (.nearest .toEven) x z ∧
      RoundsFinite F₁.toFiniteFormat .awayZero (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat .awayZero x w :=
  (neighborhoodOf F₁ hb).no_rndRNE_RAZ F₂ hsub

/-- **RNE → RTZ.** `x = hi − δ`: the intermediate RNE carries `x` up onto
`hi`, which RTZ fixes — but the direct RTZ truncates to `lo` or below. -/
theorem no_rndRNE_RTZ
    (F₁ : ParityFormat) (hb : F₁.b = ⊤)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ (.nearest .toEven) x z ∧
      RoundsFinite F₁.toFiniteFormat .toZero (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat .toZero x w :=
  (neighborhoodOf F₁ hb).no_rndRNE_RTZ F₂ hsub

/-- **RTZ → RAZ.** `x = hi + δ`: the intermediate RTZ truncates onto `hi`,
which RAZ fixes — but the direct RAZ must reach the next `F₁`-element. -/
theorem no_rndRTZ_RAZ
    (F₁ : ParityFormat) (hb : F₁.b = ⊤)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .toZero x z ∧
      RoundsFinite F₁.toFiniteFormat .awayZero (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat .awayZero x w :=
  (neighborhoodOf F₁ hb).no_rndRTZ_RAZ F₂ hsub

/-- **RAZ → RTZ.** `x = hi − δ`: the intermediate RAZ pushes `x` up onto
`hi`, which RTZ fixes — but the direct RTZ truncates to `lo` or below. -/
theorem no_rndRAZ_RTZ
    (F₁ : ParityFormat) (hb : F₁.b = ⊤)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .awayZero x z ∧
      RoundsFinite F₁.toFiniteFormat .toZero (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat .toZero x w :=
  (neighborhoodOf F₁ hb).no_rndRAZ_RTZ F₂ hsub

/-- **RAZ → RTO.** `x = hi − δ`: the intermediate RAZ lands exactly on the
even `hi`, which RTO fixes — but the direct RTO selects the odd `lo`. -/
theorem no_rndRAZ_RTO
    (F₁ : ParityFormat) (hb : F₁.b = ⊤)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .awayZero x z ∧
      RoundsFinite F₁.toFiniteFormat .toOdd (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat .toOdd x w :=
  (neighborhoodOf F₁ hb).no_rndRAZ_RTO F₂ hsub

/-- **RNE → RTO.** `x = hi − δ`: the intermediate RNE lands exactly on the
even `hi`, which RTO fixes — but the direct RTO selects the odd `lo`. -/
theorem no_rndRNE_RTO
    (F₁ : ParityFormat) (hb : F₁.b = ⊤)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ (.nearest .toEven) x z ∧
      RoundsFinite F₁.toFiniteFormat .toOdd (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat .toOdd x w :=
  (neighborhoodOf F₁ hb).no_rndRNE_RTO F₂ hsub

/-- **RTZ → RTO.** `x = hi + δ`: the intermediate RTZ truncates onto the
even `hi`, which RTO fixes — but the direct RTO selects the odd element
above. -/
theorem no_rndRTZ_RTO
    (F₁ : ParityFormat) (hb : F₁.b = ⊤)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .toZero x z ∧
      RoundsFinite F₁.toFiniteFormat .toOdd (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat .toOdd x w :=
  (neighborhoodOf F₁ hb).no_rndRTZ_RTO F₂ hsub

/-- **RAZ → RNE.** `x = m − δ` for `m` the midpoint of `(lo, hi)`: the
intermediate RAZ lands on or above `m` (a spurious tie, or past the
boundary), so the inner RNE returns the even `hi` — but the direct RNE
returns the strictly nearer odd `lo`. -/
theorem no_rndRAZ_RNE
    (F₁ : ParityFormat) (hb : F₁.b = ⊤)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .awayZero x z ∧
      RoundsFinite F₁.toFiniteFormat (.nearest .toEven) (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat (.nearest .toEven) x w :=
  (neighborhoodOf F₁ hb).no_rndRAZ_RNE F₂ hsub

/-- **RTZ → RNE.** `x = m + δ` for `m` the midpoint of `(lo2, lo)`: the
intermediate RTZ lands on or below `m` (a spurious tie, or past the
boundary), so the inner RNE returns the even `lo2` — but the direct RNE
returns the strictly nearer odd `lo`. -/
theorem no_rndRTZ_RNE
    (F₁ : ParityFormat) (hb : F₁.b = ⊤)
    (F₂ : FiniteFormat) (hsub : F₁.toFormat ⊆ F₂.toFormat) :
    ∃ (x : ℝ) (z w : Dyadic),
      RoundsFinite F₂ .toZero x z ∧
      RoundsFinite F₁.toFiniteFormat (.nearest .toEven) (z : ℝ) w ∧
      ¬ RoundsFinite F₁.toFiniteFormat (.nearest .toEven) x w :=
  (neighborhoodOf F₁ hb).no_rndRTZ_RNE F₂ hsub

end Cex

end Mpfx
