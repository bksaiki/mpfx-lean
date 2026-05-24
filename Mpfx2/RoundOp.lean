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

/-- The canonical exponent dominates `F.exp` whenever `F.exp` is finite.
Needed to discharge `quantumAtLeast F.exp` for the rounded value. -/
theorem Format.exp_le_canonicalExp (F : Format) (x : ℝ)
    {e' : ℤ} (hexp : F.exp = (e' : WithBot ℤ)) :
    e' ≤ F.canonicalExp x := by
  unfold canonicalExp
  cases hp : F.p with
  | top => simp [hexp]
  | coe p =>
    simp only [hexp]
    split_ifs
    · exact le_refl _
    · exact le_max_right _ _

/-- The canonical exponent dominates `Int.log 2 |x| + 1 - p` whenever
`F.p` is finite and `x ≠ 0`. Needed to bound `|⌊x · 2^(-e)⌋| ≤ 2^p`. -/
theorem Format.log_sub_p_le_canonicalExp (F : Format) {x : ℝ} (hx : x ≠ 0)
    {p : ℕ+} (hp : F.p = ((p : ℕ+) : WithTop ℕ+)) :
    Int.log 2 |x| + 1 - (p : ℤ) ≤ F.canonicalExp x := by
  unfold canonicalExp
  cases F.exp with
  | bot => simp [hp, hx]
  | coe e' => simp [hp, hx]

/-- For `r` with `|r| < N`, the floor `⌊r⌋` has `|⌊r⌋| ≤ N`. The
asymmetry: negative floors can saturate (e.g. `⌊-1.5⌋ = -2` with
`|-1.5| < 2` but `|⌊-1.5⌋| = 2`). -/
private theorem abs_floor_le_of_abs_lt {r : ℝ} {N : ℤ} (h : |r| < (N : ℝ)) :
    |⌊r⌋| ≤ N := by
  obtain ⟨h_neg, h_pos⟩ := abs_lt.mp h
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have h_lt : (-N - 1 : ℝ) < (⌊r⌋ : ℝ) := by
      have := Int.sub_one_lt_floor r
      linarith
    have : (-N - 1 : ℤ) < ⌊r⌋ := by exact_mod_cast h_lt
    omega
  · have h_lt : (⌊r⌋ : ℝ) < (N : ℝ) :=
      lt_of_le_of_lt (Int.floor_le r) h_pos
    exact_mod_cast h_lt.le

/-- Mirror of `abs_floor_le_of_abs_lt` for the ceiling: positive ceilings
can saturate (e.g. `⌈1.5⌉ = 2` with `|1.5| < 2` but `|⌈1.5⌉| = 2`). -/
private theorem abs_ceil_le_of_abs_lt {r : ℝ} {N : ℤ} (h : |r| < (N : ℝ)) :
    |⌈r⌉| ≤ N := by
  obtain ⟨h_neg, h_pos⟩ := abs_lt.mp h
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have h_lt : (-N : ℝ) < (⌈r⌉ : ℝ) :=
      lt_of_lt_of_le h_neg (Int.le_ceil r)
    have : (-N : ℤ) < ⌈r⌉ := by exact_mod_cast h_lt
    omega
  · have h_lt : (⌈r⌉ : ℝ) < (N : ℝ) + 1 := by
      have := Int.ceil_lt_add_one r
      linarith
    have : (⌈r⌉ : ℤ) < N + 1 := by exact_mod_cast h_lt
    omega

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

/-! Per-mode soundness obligations for `rndUnbounded`. Each is a
mode-specific arithmetic argument over `Int.log`, `Int.floor`,
`Int.ceil`, plus the `canonicalExp`/`rndInt` definitions. -/

theorem rndUnbounded_satisfies_toNegative (F : Format) (x : ℝ)
    (h : ¬ F.IsUndefined .toNegative) :
    RoundsFinite F.unbounded .toNegative x (rndUnbounded F .toNegative x h) := by
  have h_rnd_eq : rndUnbounded F .toNegative x h =
      Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋ (F.canonicalExp x) := by
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.toNegative : RoundingMode) ≠ .toOdd)]
    rw [dif_neg (by decide : (RoundingMode.toNegative : RoundingMode) ≠ .nearest .toEven)]
    rfl
  rw [h_rnd_eq]
  set e := F.canonicalExp x
  set c := ⌊x * (2 : ℝ) ^ (-e)⌋
  set y : Dyadic := Dyadic.ofIntZpow c e
  have h_y_real : (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ e := Dyadic.coe_ofIntZpow c e
  have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · -- precisionAtMost F.unbounded.p y; via the canonical-mantissa range.
    change Dyadic.precisionAtMost F.p y
    cases hp : F.p with
    | top => trivial
    | coe p =>
      apply Dyadic.precisionAtMost_of_abs_le c e h_y_real
      apply abs_floor_le_of_abs_lt
      push_cast
      by_cases hx : x = 0
      · subst hx
        simp
      · have h_e_ge : Int.log 2 |x| + 1 - (p : ℤ) ≤ e :=
          F.log_sub_p_le_canonicalExp hx hp
        have h_x_lt : |x| < (2 : ℝ) ^ (Int.log 2 |x| + 1) := by
          have hlt := Int.lt_zpow_succ_log_self (b := 2)
            (by norm_num : (1 : ℕ) < 2) |x|
          exact_mod_cast hlt
        have h_abs : |x * (2 : ℝ) ^ (-e)| = |x| * (2 : ℝ) ^ (-e) := by
          rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)]
        have h_pcast : ((p : ℕ+) : ℤ) = ((p : ℕ) : ℤ) := rfl
        have hle : Int.log 2 |x| + 1 + (-e) ≤ ((p : ℕ) : ℤ) := by
          linarith [h_e_ge, h_pcast]
        rw [h_abs]
        calc |x| * (2 : ℝ) ^ (-e)
            < (2 : ℝ) ^ (Int.log 2 |x| + 1) * (2 : ℝ) ^ (-e) :=
              mul_lt_mul_of_pos_right h_x_lt (zpow_pos (by norm_num) _)
          _ = (2 : ℝ) ^ (Int.log 2 |x| + 1 + (-e)) := by
              rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          _ ≤ (2 : ℝ) ^ ((p : ℕ) : ℤ) := zpow_le_zpow_right₀ (by norm_num) hle
          _ = (2 : ℝ) ^ (p : ℕ) := by rw [zpow_natCast]
  · -- quantumAtLeast F.unbounded.exp y; uses `exp_le_canonicalExp`.
    change Dyadic.quantumAtLeast F.exp y
    cases hexp : F.exp with
    | bot => trivial
    | coe e' =>
      rw [Dyadic.quantumAtLeast_coe]
      have h_e_ge : e' ≤ e := F.exp_le_canonicalExp x hexp
      refine ⟨c * 2 ^ (e - e').toNat, ?_⟩
      rw [h_y_real]
      have h_diff_nn : 0 ≤ e - e' := by omega
      have h_split : (2 : ℝ) ^ e = (2 : ℝ) ^ (e - e').toNat * (2 : ℝ) ^ e' := by
        rw [show ((2 : ℝ) ^ (e - e').toNat : ℝ) = (2 : ℝ) ^ ((e - e').toNat : ℤ)
            from (zpow_natCast _ _).symm, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
            Int.toNat_of_nonneg h_diff_nn]
        congr 1; ring
      rw [h_split, ← mul_assoc]
      push_cast
      ring
  · -- boundOK F.unbounded.b y = boundOK ⊤ y (trivial)
    change Format.boundOK F.unbounded.b y
    rw [Format.unbounded_b]
    trivial
  · -- (y : ℝ) ≤ x
    rw [h_y_real]
    have hfl_le : (c : ℝ) ≤ x * (2 : ℝ) ^ (-e) := Int.floor_le _
    have hmul : (c : ℝ) * (2 : ℝ) ^ e ≤ x * (2 : ℝ) ^ (-e) * (2 : ℝ) ^ e :=
      mul_le_mul_of_nonneg_right hfl_le h_2e_pos.le
    rwa [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), neg_add_cancel,
         zpow_zero, mul_one] at hmul
  · -- TODO: minimality — any `z ∈ F.unbounded` with `z ≤ x` has `z ≤ y`.
    sorry

theorem rndUnbounded_satisfies_toPositive (F : Format) (x : ℝ)
    (h : ¬ F.IsUndefined .toPositive) :
    RoundsFinite F.unbounded .toPositive x (rndUnbounded F .toPositive x h) := by
  have h_rnd_eq : rndUnbounded F .toPositive x h =
      Dyadic.ofIntZpow ⌈x * (2 : ℝ) ^ (-(F.canonicalExp x))⌉ (F.canonicalExp x) := by
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.toPositive : RoundingMode) ≠ .toOdd)]
    rw [dif_neg (by decide : (RoundingMode.toPositive : RoundingMode) ≠ .nearest .toEven)]
    rfl
  rw [h_rnd_eq]
  set e := F.canonicalExp x
  set c := ⌈x * (2 : ℝ) ^ (-e)⌉
  set y : Dyadic := Dyadic.ofIntZpow c e
  have h_y_real : (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ e := Dyadic.coe_ofIntZpow c e
  have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · -- precisionAtMost; via abs_ceil_le_of_abs_lt, same template as toNegative.
    change Dyadic.precisionAtMost F.p y
    cases hp : F.p with
    | top => trivial
    | coe p =>
      apply Dyadic.precisionAtMost_of_abs_le c e h_y_real
      apply abs_ceil_le_of_abs_lt
      push_cast
      by_cases hx : x = 0
      · subst hx; simp
      · have h_e_ge : Int.log 2 |x| + 1 - (p : ℤ) ≤ e :=
          F.log_sub_p_le_canonicalExp hx hp
        have h_x_lt : |x| < (2 : ℝ) ^ (Int.log 2 |x| + 1) := by
          exact_mod_cast Int.lt_zpow_succ_log_self (b := 2)
            (by norm_num : (1 : ℕ) < 2) |x|
        have h_abs : |x * (2 : ℝ) ^ (-e)| = |x| * (2 : ℝ) ^ (-e) := by
          rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)]
        have h_pcast : ((p : ℕ+) : ℤ) = ((p : ℕ) : ℤ) := rfl
        have hle : Int.log 2 |x| + 1 + (-e) ≤ ((p : ℕ) : ℤ) := by
          linarith [h_e_ge, h_pcast]
        rw [h_abs]
        calc |x| * (2 : ℝ) ^ (-e)
            < (2 : ℝ) ^ (Int.log 2 |x| + 1) * (2 : ℝ) ^ (-e) :=
              mul_lt_mul_of_pos_right h_x_lt (zpow_pos (by norm_num) _)
          _ = (2 : ℝ) ^ (Int.log 2 |x| + 1 + (-e)) := by
              rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          _ ≤ (2 : ℝ) ^ ((p : ℕ) : ℤ) := zpow_le_zpow_right₀ (by norm_num) hle
          _ = (2 : ℝ) ^ (p : ℕ) := by rw [zpow_natCast]
  · -- quantumAtLeast (mirror of toNegative).
    change Dyadic.quantumAtLeast F.exp y
    cases hexp : F.exp with
    | bot => trivial
    | coe e' =>
      rw [Dyadic.quantumAtLeast_coe]
      have h_e_ge : e' ≤ e := F.exp_le_canonicalExp x hexp
      refine ⟨c * 2 ^ (e - e').toNat, ?_⟩
      rw [h_y_real]
      have h_diff_nn : 0 ≤ e - e' := by omega
      have h_split : (2 : ℝ) ^ e = (2 : ℝ) ^ (e - e').toNat * (2 : ℝ) ^ e' := by
        rw [show ((2 : ℝ) ^ (e - e').toNat : ℝ) = (2 : ℝ) ^ ((e - e').toNat : ℤ)
            from (zpow_natCast _ _).symm, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
            Int.toNat_of_nonneg h_diff_nn]
        congr 1; ring
      rw [h_split, ← mul_assoc]
      push_cast
      ring
  · -- boundOK trivially via F.unbounded.b = ⊤.
    change Format.boundOK F.unbounded.b y
    rw [Format.unbounded_b]
    trivial
  · -- x ≤ (y : ℝ): the ceiling of `x · 2^(-e)`, rescaled by `2^e`, is ≥ x.
    rw [h_y_real]
    have hce_le : x * (2 : ℝ) ^ (-e) ≤ (c : ℝ) := Int.le_ceil _
    have hmul : x * (2 : ℝ) ^ (-e) * (2 : ℝ) ^ e ≤ (c : ℝ) * (2 : ℝ) ^ e :=
      mul_le_mul_of_nonneg_right hce_le h_2e_pos.le
    rwa [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), neg_add_cancel,
         zpow_zero, mul_one] at hmul
  · -- TODO: minimality — any `z ∈ F.unbounded` with `x ≤ z` has `y ≤ z`.
    sorry

theorem rndUnbounded_satisfies_toZero (F : Format) (x : ℝ)
    (h : ¬ F.IsUndefined .toZero) :
    RoundsFinite F.unbounded .toZero x (rndUnbounded F .toZero x h) := by
  have h_rnd_eq : rndUnbounded F .toZero x h =
      Dyadic.ofIntZpow (rndInt .toZero x (F.canonicalExp x)) (F.canonicalExp x) := by
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.toZero : RoundingMode) ≠ .toOdd)]
    rw [dif_neg (by decide : (RoundingMode.toZero : RoundingMode) ≠ .nearest .toEven)]
  rw [h_rnd_eq]
  set e := F.canonicalExp x
  set c := rndInt .toZero x e
  set y : Dyadic := Dyadic.ofIntZpow c e
  have h_y_real : (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ e := Dyadic.coe_ofIntZpow c e
  have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have h_c_eq : c = if 0 ≤ x then ⌊x * (2 : ℝ) ^ (-e)⌋ else ⌈x * (2 : ℝ) ^ (-e)⌉ := by
    change rndInt .toZero x e = _
    rfl
  -- Reusable: |x · 2^(-e)| bound from the canonical exponent.
  have h_scaled_lt_when_finite_p {p : ℕ+} (hp : F.p = ((p : ℕ+) : WithTop ℕ+)) :
      |x * (2 : ℝ) ^ (-e)| < (2 : ℝ) ^ (p : ℕ) := by
    by_cases hx : x = 0
    · subst hx; simp
    · have h_e_ge : Int.log 2 |x| + 1 - (p : ℤ) ≤ e :=
        F.log_sub_p_le_canonicalExp hx hp
      have h_x_lt : |x| < (2 : ℝ) ^ (Int.log 2 |x| + 1) := by
        exact_mod_cast Int.lt_zpow_succ_log_self (b := 2)
          (by norm_num : (1 : ℕ) < 2) |x|
      have h_abs : |x * (2 : ℝ) ^ (-e)| = |x| * (2 : ℝ) ^ (-e) := by
        rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)]
      have h_pcast : ((p : ℕ+) : ℤ) = ((p : ℕ) : ℤ) := rfl
      have hle : Int.log 2 |x| + 1 + (-e) ≤ ((p : ℕ) : ℤ) := by
        linarith [h_e_ge, h_pcast]
      rw [h_abs]
      calc |x| * (2 : ℝ) ^ (-e)
          < (2 : ℝ) ^ (Int.log 2 |x| + 1) * (2 : ℝ) ^ (-e) :=
            mul_lt_mul_of_pos_right h_x_lt (zpow_pos (by norm_num) _)
        _ = (2 : ℝ) ^ (Int.log 2 |x| + 1 + (-e)) := by
            rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        _ ≤ (2 : ℝ) ^ ((p : ℕ) : ℤ) := zpow_le_zpow_right₀ (by norm_num) hle
        _ = (2 : ℝ) ^ (p : ℕ) := by rw [zpow_natCast]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- precisionAtMost
    change Dyadic.precisionAtMost F.p y
    cases hp : F.p with
    | top => trivial
    | coe p =>
      apply Dyadic.precisionAtMost_of_abs_le c e h_y_real
      rw [h_c_eq]
      by_cases hx_nn : 0 ≤ x
      · rw [if_pos hx_nn]
        apply abs_floor_le_of_abs_lt
        push_cast
        exact h_scaled_lt_when_finite_p hp
      · rw [if_neg hx_nn]
        apply abs_ceil_le_of_abs_lt
        push_cast
        exact h_scaled_lt_when_finite_p hp
  · -- quantumAtLeast (same template as toNegative)
    change Dyadic.quantumAtLeast F.exp y
    cases hexp : F.exp with
    | bot => trivial
    | coe e' =>
      rw [Dyadic.quantumAtLeast_coe]
      have h_e_ge : e' ≤ e := F.exp_le_canonicalExp x hexp
      refine ⟨c * 2 ^ (e - e').toNat, ?_⟩
      rw [h_y_real]
      have h_diff_nn : 0 ≤ e - e' := by omega
      have h_split : (2 : ℝ) ^ e = (2 : ℝ) ^ (e - e').toNat * (2 : ℝ) ^ e' := by
        rw [show ((2 : ℝ) ^ (e - e').toNat : ℝ) = (2 : ℝ) ^ ((e - e').toNat : ℤ)
            from (zpow_natCast _ _).symm, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
            Int.toNat_of_nonneg h_diff_nn]
        congr 1; ring
      rw [h_split, ← mul_assoc]
      push_cast
      ring
  · -- boundOK trivial
    change Format.boundOK F.unbounded.b y
    rw [Format.unbounded_b]
    trivial
  · -- |y| ≤ |x|: sign-split.
    rw [h_y_real]
    rw [show (c : ℝ) * (2 : ℝ) ^ e = (c : ℝ) * (2 : ℝ) ^ e from rfl]
    by_cases hx_nn : 0 ≤ x
    · -- x ≥ 0: c = ⌊s⌋, c · 2^e ≤ x, also c · 2^e ≥ 0.
      have h_c : c = ⌊x * (2 : ℝ) ^ (-e)⌋ := by rw [h_c_eq, if_pos hx_nn]
      have h_floor_le : (c : ℝ) ≤ x * (2 : ℝ) ^ (-e) := by rw [h_c]; exact Int.floor_le _
      have h_floor_nn : 0 ≤ c := by
        rw [h_c]; exact Int.floor_nonneg.mpr (mul_nonneg hx_nn (zpow_pos (by norm_num) _).le)
      have hy_nn : 0 ≤ (c : ℝ) * (2 : ℝ) ^ e :=
        mul_nonneg (by exact_mod_cast h_floor_nn) h_2e_pos.le
      rw [abs_of_nonneg hy_nn, abs_of_nonneg hx_nn]
      have hmul : (c : ℝ) * (2 : ℝ) ^ e ≤ x * (2 : ℝ) ^ (-e) * (2 : ℝ) ^ e :=
        mul_le_mul_of_nonneg_right h_floor_le h_2e_pos.le
      rwa [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), neg_add_cancel,
           zpow_zero, mul_one] at hmul
    · -- x < 0: c = ⌈s⌉, x ≤ c · 2^e ≤ 0.
      push Not at hx_nn
      have h_c : c = ⌈x * (2 : ℝ) ^ (-e)⌉ := by rw [h_c_eq, if_neg (not_le.mpr hx_nn)]
      have h_s_neg : x * (2 : ℝ) ^ (-e) < 0 :=
        mul_neg_of_neg_of_pos hx_nn (zpow_pos (by norm_num) _)
      have h_ceil_le : x * (2 : ℝ) ^ (-e) ≤ (c : ℝ) := by rw [h_c]; exact Int.le_ceil _
      have h_ceil_np : c ≤ 0 := by
        rw [h_c]
        exact Int.ceil_le.mpr (by push_cast; exact h_s_neg.le)
      have hy_np : (c : ℝ) * (2 : ℝ) ^ e ≤ 0 :=
        mul_nonpos_iff.mpr (Or.inr ⟨by exact_mod_cast h_ceil_np, h_2e_pos.le⟩)
      rw [abs_of_nonpos hy_np, abs_of_neg hx_nn]
      have hmul : x * (2 : ℝ) ^ (-e) * (2 : ℝ) ^ e ≤ (c : ℝ) * (2 : ℝ) ^ e :=
        mul_le_mul_of_nonneg_right h_ceil_le h_2e_pos.le
      rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), neg_add_cancel,
           zpow_zero, mul_one] at hmul
      linarith
  · -- y · x ≥ 0: sign-split.
    rw [h_y_real]
    by_cases hx_nn : 0 ≤ x
    · -- x ≥ 0: c ≥ 0 (floor of nonneg), so c · 2^e · x ≥ 0.
      have h_c : c = ⌊x * (2 : ℝ) ^ (-e)⌋ := by rw [h_c_eq, if_pos hx_nn]
      have h_c_nn : 0 ≤ c := by
        rw [h_c]; exact Int.floor_nonneg.mpr (mul_nonneg hx_nn (zpow_pos (by norm_num) _).le)
      have h_y_nn : 0 ≤ (c : ℝ) * (2 : ℝ) ^ e :=
        mul_nonneg (by exact_mod_cast h_c_nn) h_2e_pos.le
      exact mul_nonneg h_y_nn hx_nn
    · -- x < 0: c ≤ 0 (ceil of nonpos), so c · 2^e ≤ 0 and x < 0, product ≥ 0.
      push Not at hx_nn
      have h_c : c = ⌈x * (2 : ℝ) ^ (-e)⌉ := by rw [h_c_eq, if_neg (not_le.mpr hx_nn)]
      have h_s_neg : x * (2 : ℝ) ^ (-e) < 0 :=
        mul_neg_of_neg_of_pos hx_nn (zpow_pos (by norm_num) _)
      have h_c_np : c ≤ 0 := by
        rw [h_c]
        exact Int.ceil_le.mpr (by push_cast; exact h_s_neg.le)
      have h_y_np : (c : ℝ) * (2 : ℝ) ^ e ≤ 0 :=
        mul_nonpos_iff.mpr (Or.inr ⟨by exact_mod_cast h_c_np, h_2e_pos.le⟩)
      exact mul_nonneg_iff.mpr (Or.inr ⟨h_y_np, hx_nn.le⟩)
  · -- TODO: minimality.
    sorry

theorem rndUnbounded_satisfies_awayZero (F : Format) (x : ℝ)
    (h : ¬ F.IsUndefined .awayZero) :
    RoundsFinite F.unbounded .awayZero x (rndUnbounded F .awayZero x h) := by
  have h_rnd_eq : rndUnbounded F .awayZero x h =
      Dyadic.ofIntZpow (rndInt .awayZero x (F.canonicalExp x)) (F.canonicalExp x) := by
    unfold rndUnbounded
    rw [dif_neg (by decide : (RoundingMode.awayZero : RoundingMode) ≠ .toOdd)]
    rw [dif_neg (by decide : (RoundingMode.awayZero : RoundingMode) ≠ .nearest .toEven)]
  rw [h_rnd_eq]
  set e := F.canonicalExp x
  set c := rndInt .awayZero x e
  set y : Dyadic := Dyadic.ofIntZpow c e
  have h_y_real : (y : ℝ) = (c : ℝ) * (2 : ℝ) ^ e := Dyadic.coe_ofIntZpow c e
  have h_2e_pos : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have h_c_eq : c = if 0 ≤ x then ⌈x * (2 : ℝ) ^ (-e)⌉ else ⌊x * (2 : ℝ) ^ (-e)⌋ := by
    change rndInt .awayZero x e = _
    rfl
  have h_scaled_lt_when_finite_p {p : ℕ+} (hp : F.p = ((p : ℕ+) : WithTop ℕ+)) :
      |x * (2 : ℝ) ^ (-e)| < (2 : ℝ) ^ (p : ℕ) := by
    by_cases hx : x = 0
    · subst hx; simp
    · have h_e_ge : Int.log 2 |x| + 1 - (p : ℤ) ≤ e :=
        F.log_sub_p_le_canonicalExp hx hp
      have h_x_lt : |x| < (2 : ℝ) ^ (Int.log 2 |x| + 1) := by
        exact_mod_cast Int.lt_zpow_succ_log_self (b := 2)
          (by norm_num : (1 : ℕ) < 2) |x|
      have h_abs : |x * (2 : ℝ) ^ (-e)| = |x| * (2 : ℝ) ^ (-e) := by
        rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)]
      have h_pcast : ((p : ℕ+) : ℤ) = ((p : ℕ) : ℤ) := rfl
      have hle : Int.log 2 |x| + 1 + (-e) ≤ ((p : ℕ) : ℤ) := by
        linarith [h_e_ge, h_pcast]
      rw [h_abs]
      calc |x| * (2 : ℝ) ^ (-e)
          < (2 : ℝ) ^ (Int.log 2 |x| + 1) * (2 : ℝ) ^ (-e) :=
            mul_lt_mul_of_pos_right h_x_lt (zpow_pos (by norm_num) _)
        _ = (2 : ℝ) ^ (Int.log 2 |x| + 1 + (-e)) := by
            rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        _ ≤ (2 : ℝ) ^ ((p : ℕ) : ℤ) := zpow_le_zpow_right₀ (by norm_num) hle
        _ = (2 : ℝ) ^ (p : ℕ) := by rw [zpow_natCast]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- precisionAtMost
    change Dyadic.precisionAtMost F.p y
    cases hp : F.p with
    | top => trivial
    | coe p =>
      apply Dyadic.precisionAtMost_of_abs_le c e h_y_real
      rw [h_c_eq]
      by_cases hx_nn : 0 ≤ x
      · rw [if_pos hx_nn]
        apply abs_ceil_le_of_abs_lt
        push_cast
        exact h_scaled_lt_when_finite_p hp
      · rw [if_neg hx_nn]
        apply abs_floor_le_of_abs_lt
        push_cast
        exact h_scaled_lt_when_finite_p hp
  · -- quantumAtLeast
    change Dyadic.quantumAtLeast F.exp y
    cases hexp : F.exp with
    | bot => trivial
    | coe e' =>
      rw [Dyadic.quantumAtLeast_coe]
      have h_e_ge : e' ≤ e := F.exp_le_canonicalExp x hexp
      refine ⟨c * 2 ^ (e - e').toNat, ?_⟩
      rw [h_y_real]
      have h_diff_nn : 0 ≤ e - e' := by omega
      have h_split : (2 : ℝ) ^ e = (2 : ℝ) ^ (e - e').toNat * (2 : ℝ) ^ e' := by
        rw [show ((2 : ℝ) ^ (e - e').toNat : ℝ) = (2 : ℝ) ^ ((e - e').toNat : ℤ)
            from (zpow_natCast _ _).symm, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
            Int.toNat_of_nonneg h_diff_nn]
        congr 1; ring
      rw [h_split, ← mul_assoc]
      push_cast
      ring
  · change Format.boundOK F.unbounded.b y
    rw [Format.unbounded_b]
    trivial
  · -- |x| ≤ |y|: sign-split. RAZ rounds away from zero, so |y| ≥ |x|.
    rw [h_y_real]
    by_cases hx_nn : 0 ≤ x
    · -- x ≥ 0: c = ⌈s⌉, c · 2^e ≥ x ≥ 0.
      have h_c : c = ⌈x * (2 : ℝ) ^ (-e)⌉ := by rw [h_c_eq, if_pos hx_nn]
      have h_ceil_ge : x * (2 : ℝ) ^ (-e) ≤ (c : ℝ) := by rw [h_c]; exact Int.le_ceil _
      have h_ceil_nn : 0 ≤ c := by
        rw [h_c]; exact Int.ceil_nonneg (mul_nonneg hx_nn (zpow_pos (by norm_num) _).le)
      have hy_nn : 0 ≤ (c : ℝ) * (2 : ℝ) ^ e :=
        mul_nonneg (by exact_mod_cast h_ceil_nn) h_2e_pos.le
      rw [abs_of_nonneg hy_nn, abs_of_nonneg hx_nn]
      have hmul : x * (2 : ℝ) ^ (-e) * (2 : ℝ) ^ e ≤ (c : ℝ) * (2 : ℝ) ^ e :=
        mul_le_mul_of_nonneg_right h_ceil_ge h_2e_pos.le
      rwa [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), neg_add_cancel,
           zpow_zero, mul_one] at hmul
    · -- x < 0: c = ⌊s⌋, c · 2^e ≤ x < 0.
      push Not at hx_nn
      have h_c : c = ⌊x * (2 : ℝ) ^ (-e)⌋ := by rw [h_c_eq, if_neg (not_le.mpr hx_nn)]
      have h_s_neg : x * (2 : ℝ) ^ (-e) < 0 :=
        mul_neg_of_neg_of_pos hx_nn (zpow_pos (by norm_num) _)
      have h_floor_le : (c : ℝ) ≤ x * (2 : ℝ) ^ (-e) := by rw [h_c]; exact Int.floor_le _
      have h_c_neg : c < 0 := by
        rw [h_c]
        exact Int.floor_lt.mpr (by push_cast; exact h_s_neg)
      have hy_np : (c : ℝ) * (2 : ℝ) ^ e ≤ 0 :=
        mul_nonpos_iff.mpr (Or.inr ⟨by exact_mod_cast h_c_neg.le, h_2e_pos.le⟩)
      rw [abs_of_nonpos hy_np, abs_of_neg hx_nn]
      have hmul : (c : ℝ) * (2 : ℝ) ^ e ≤ x * (2 : ℝ) ^ (-e) * (2 : ℝ) ^ e :=
        mul_le_mul_of_nonneg_right h_floor_le h_2e_pos.le
      rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), neg_add_cancel,
           zpow_zero, mul_one] at hmul
      linarith
  · -- y · x ≥ 0
    rw [h_y_real]
    by_cases hx_nn : 0 ≤ x
    · have h_c : c = ⌈x * (2 : ℝ) ^ (-e)⌉ := by rw [h_c_eq, if_pos hx_nn]
      have h_c_nn : 0 ≤ c := by
        rw [h_c]; exact Int.ceil_nonneg (mul_nonneg hx_nn (zpow_pos (by norm_num) _).le)
      have h_y_nn : 0 ≤ (c : ℝ) * (2 : ℝ) ^ e :=
        mul_nonneg (by exact_mod_cast h_c_nn) h_2e_pos.le
      exact mul_nonneg h_y_nn hx_nn
    · push Not at hx_nn
      have h_c : c = ⌊x * (2 : ℝ) ^ (-e)⌋ := by rw [h_c_eq, if_neg (not_le.mpr hx_nn)]
      have h_s_neg : x * (2 : ℝ) ^ (-e) < 0 :=
        mul_neg_of_neg_of_pos hx_nn (zpow_pos (by norm_num) _)
      have h_c_neg : c < 0 := by
        rw [h_c]
        exact Int.floor_lt.mpr (by push_cast; exact h_s_neg)
      have h_y_np : (c : ℝ) * (2 : ℝ) ^ e ≤ 0 :=
        mul_nonpos_iff.mpr (Or.inr ⟨by exact_mod_cast h_c_neg.le, h_2e_pos.le⟩)
      exact mul_nonneg_iff.mpr (Or.inr ⟨h_y_np, hx_nn.le⟩)
  · sorry

theorem rndUnbounded_satisfies_toOdd (F : Format) (x : ℝ)
    (h : ¬ F.IsUndefined .toOdd) :
    RoundsFinite F.unbounded .toOdd x (rndUnbounded F .toOdd x h) := by
  sorry

theorem rndUnbounded_satisfies_nearest (F : Format) (tb : TieBreak) (x : ℝ)
    (h : ¬ F.IsUndefined (.nearest tb)) :
    RoundsFinite F.unbounded (.nearest tb) x (rndUnbounded F (.nearest tb) x h) := by
  sorry

/-- The constructive `rndUnbounded` satisfies the unbounded rounding spec. -/
theorem rndUnbounded_satisfies (F : Format) (rm : RoundingMode) (x : ℝ)
    (h : ¬ F.IsUndefined rm) :
    RoundsFinite F.unbounded rm x (rndUnbounded F rm x h) := by
  cases rm with
  | toNegative => exact rndUnbounded_satisfies_toNegative F x h
  | toPositive => exact rndUnbounded_satisfies_toPositive F x h
  | toZero => exact rndUnbounded_satisfies_toZero F x h
  | awayZero => exact rndUnbounded_satisfies_awayZero F x h
  | toOdd => exact rndUnbounded_satisfies_toOdd F x h
  | nearest tb => exact rndUnbounded_satisfies_nearest F tb x h

/-! Per-mode uniqueness obligations. The pattern follows the spec:
two values agreeing on the mode-spec must equal each other. -/

theorem rndUnbounded_unique_toNegative (F : Format) (x : ℝ)
    (h : ¬ F.IsUndefined .toNegative) {y : Dyadic}
    (hy : RoundsFinite F.unbounded .toNegative x y) :
    y = rndUnbounded F .toNegative x h := by
  set y' := rndUnbounded F .toNegative x h
  have hy' : RoundsFinite F.unbounded .toNegative x y' :=
    rndUnbounded_satisfies_toNegative F x h
  obtain ⟨hy_mem, hy_le, hy_max⟩ := hy
  obtain ⟨hy'_mem, hy'_le, hy'_max⟩ := hy'
  have h1 : (y' : ℝ) ≤ (y : ℝ) := hy_max y' hy'_mem hy'_le
  have h2 : (y : ℝ) ≤ (y' : ℝ) := hy'_max y hy_mem hy_le
  exact Subtype.ext (le_antisymm h2 h1)

theorem rndUnbounded_unique_toPositive (F : Format) (x : ℝ)
    (h : ¬ F.IsUndefined .toPositive) {y : Dyadic}
    (hy : RoundsFinite F.unbounded .toPositive x y) :
    y = rndUnbounded F .toPositive x h := by
  set y' := rndUnbounded F .toPositive x h
  have hy' : RoundsFinite F.unbounded .toPositive x y' :=
    rndUnbounded_satisfies_toPositive F x h
  obtain ⟨hy_mem, hy_ge, hy_min⟩ := hy
  obtain ⟨hy'_mem, hy'_ge, hy'_min⟩ := hy'
  have h1 : (y : ℝ) ≤ (y' : ℝ) := hy_min y' hy'_mem hy'_ge
  have h2 : (y' : ℝ) ≤ (y : ℝ) := hy'_min y hy_mem hy_ge
  exact Subtype.ext (le_antisymm h1 h2)

theorem rndUnbounded_unique_toZero (F : Format) (x : ℝ)
    (h : ¬ F.IsUndefined .toZero) {y : Dyadic}
    (hy : RoundsFinite F.unbounded .toZero x y) :
    y = rndUnbounded F .toZero x h := by
  set y' := rndUnbounded F .toZero x h
  have hy' : RoundsFinite F.unbounded .toZero x y' :=
    rndUnbounded_satisfies_toZero F x h
  obtain ⟨hy_mem, hy_bnd, hy_sign, hy_max⟩ := hy
  obtain ⟨hy'_mem, hy'_bnd, hy'_sign, hy'_max⟩ := hy'
  have h1 : |(y' : ℝ)| ≤ |(y : ℝ)| := hy_max y' hy'_mem hy'_bnd hy'_sign
  have h2 : |(y : ℝ)| ≤ |(y' : ℝ)| := hy'_max y hy_mem hy_bnd hy_sign
  have habs : |(y : ℝ)| = |(y' : ℝ)| := le_antisymm h2 h1
  apply Subtype.ext
  rcases abs_eq_abs.mp habs with heq | hneg
  · exact heq
  · -- y = -y': combine the two `* x ≥ 0` constraints to force y'·x = 0.
    have h_prod_le : (y' : ℝ) * x + (y' : ℝ) * x ≤ 0 := by
      have h_y : (y : ℝ) * x = -((y' : ℝ) * x) := by rw [hneg]; ring
      linarith [hy_sign, hy'_sign, h_y]
    have h_prod_zero : (y' : ℝ) * x = 0 := by linarith [hy'_sign]
    rcases mul_eq_zero.mp h_prod_zero with h' | hx0
    · rw [hneg, h']; ring
    · -- x = 0: the `|y| ≤ |x|` clause directly forces y = y' = 0.
      have hy0 : (y : ℝ) = 0 := by
        have : |(y : ℝ)| ≤ 0 := by rw [hx0] at hy_bnd; simpa using hy_bnd
        exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
      have hy'0 : (y' : ℝ) = 0 := by
        have : |(y' : ℝ)| ≤ 0 := by rw [hx0] at hy'_bnd; simpa using hy'_bnd
        exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
      rw [hy0, hy'0]

theorem rndUnbounded_unique_awayZero (F : Format) (x : ℝ)
    (h : ¬ F.IsUndefined .awayZero) {y : Dyadic}
    (hy : RoundsFinite F.unbounded .awayZero x y) :
    y = rndUnbounded F .awayZero x h := by
  set y' := rndUnbounded F .awayZero x h
  have hy' : RoundsFinite F.unbounded .awayZero x y' :=
    rndUnbounded_satisfies_awayZero F x h
  obtain ⟨hy_mem, hy_bnd, hy_sign, hy_min⟩ := hy
  obtain ⟨hy'_mem, hy'_bnd, hy'_sign, hy'_min⟩ := hy'
  have h1 : |(y : ℝ)| ≤ |(y' : ℝ)| := hy_min y' hy'_mem hy'_bnd hy'_sign
  have h2 : |(y' : ℝ)| ≤ |(y : ℝ)| := hy'_min y hy_mem hy_bnd hy_sign
  have habs : |(y : ℝ)| = |(y' : ℝ)| := le_antisymm h1 h2
  apply Subtype.ext
  rcases abs_eq_abs.mp habs with heq | hneg
  · exact heq
  · have h_prod_zero : (y' : ℝ) * x = 0 := by
      have h_y : (y : ℝ) * x = -((y' : ℝ) * x) := by rw [hneg]; ring
      linarith [hy_sign, hy'_sign, h_y]
    rcases mul_eq_zero.mp h_prod_zero with h' | hx0
    · rw [hneg, h']; ring
    · -- x = 0: RAZ's bound clause is vacuous; min-clause via `0 ∈ F` pins y = y' = 0.
      have h_zero_mem : (0 : Dyadic) ∈ F.unbounded := Format.zero_mem F.unbounded
      have h_zero_bnd : |x| ≤ |((0 : Dyadic) : ℝ)| := by rw [hx0]; simp
      have h_zero_sign : ((0 : Dyadic) : ℝ) * x ≥ 0 := by simp
      have hy_le_0 : |(y : ℝ)| ≤ |((0 : Dyadic) : ℝ)| :=
        hy_min 0 h_zero_mem h_zero_bnd h_zero_sign
      have hy'_le_0 : |(y' : ℝ)| ≤ |((0 : Dyadic) : ℝ)| :=
        hy'_min 0 h_zero_mem h_zero_bnd h_zero_sign
      have hy0 : (y : ℝ) = 0 := by
        have : |(y : ℝ)| ≤ 0 := by simpa using hy_le_0
        exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
      have hy'0 : (y' : ℝ) = 0 := by
        have : |(y' : ℝ)| ≤ 0 := by simpa using hy'_le_0
        exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
      linarith

theorem rndUnbounded_unique_toOdd (F : Format) (x : ℝ)
    (h : ¬ F.IsUndefined .toOdd) {y : Dyadic}
    (hy : RoundsFinite F.unbounded .toOdd x y) :
    y = rndUnbounded F .toOdd x h := by
  sorry

theorem rndUnbounded_unique_nearest (F : Format) (tb : TieBreak) (x : ℝ)
    (h : ¬ F.IsUndefined (.nearest tb)) {y : Dyadic}
    (hy : RoundsFinite F.unbounded (.nearest tb) x y) :
    y = rndUnbounded F (.nearest tb) x h := by
  sorry

/-- Uniqueness: any `y` satisfying the unbounded rounding spec equals
`rndUnbounded F rm x h`. -/
theorem rndUnbounded_unique (F : Format) (rm : RoundingMode) (x : ℝ)
    (h : ¬ F.IsUndefined rm) {y : Dyadic}
    (hy : RoundsFinite F.unbounded rm x y) :
    y = rndUnbounded F rm x h := by
  cases rm with
  | toNegative => exact rndUnbounded_unique_toNegative F x h hy
  | toPositive => exact rndUnbounded_unique_toPositive F x h hy
  | toZero => exact rndUnbounded_unique_toZero F x h hy
  | awayZero => exact rndUnbounded_unique_awayZero F x h hy
  | toOdd => exact rndUnbounded_unique_toOdd F x h hy
  | nearest tb => exact rndUnbounded_unique_nearest F tb x h hy

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
  | finite y =>
    change rnd F rm x = .finite y ↔
      ¬ F.IsUndefined rm ∧
      RoundsFinite F.unbounded rm x y ∧ Format.boundOK F.b y
    constructor
    · -- Forward: rnd = .finite y ⇒ ⟨h_undef, RoundsFinite y, boundOK y⟩.
      -- Reading off `rnd`'s `if`s: the equation pins y = rndUnbounded ... and
      -- the bound check succeeded.
      intro h_eq
      have h_undef : ¬ F.IsUndefined rm := by
        intro h
        unfold rnd at h_eq
        rw [dif_pos h] at h_eq
        exact RoundResult.noConfusion h_eq
      unfold rnd at h_eq
      rw [dif_neg h_undef] at h_eq
      dsimp only at h_eq
      split_ifs at h_eq with hb
      · have h_y_eq : rndUnbounded F rm x h_undef = y := by injection h_eq
        refine ⟨h_undef, ?_, ?_⟩
        · rw [← h_y_eq]; exact rndUnbounded_satisfies F rm x h_undef
        · rw [← h_y_eq]; exact hb
    · -- Reverse: ⟨h_undef, RoundsFinite y, boundOK y⟩ ⇒ rnd = .finite y.
      -- By uniqueness, y = rndUnbounded; the bound check succeeds.
      rintro ⟨h_undef, hRF, hBOK⟩
      have h_y_eq : y = rndUnbounded F rm x h_undef :=
        rndUnbounded_unique F rm x h_undef hRF
      unfold rnd
      rw [dif_neg h_undef]
      dsimp only
      rw [if_pos (h_y_eq ▸ hBOK)]
      exact congrArg _ h_y_eq.symm

end Mpfx2
