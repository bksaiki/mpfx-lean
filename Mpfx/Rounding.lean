import Mpfx.Format

/-!
# Rounding spec (relational layer)

The constructive-logic layer of the rounding architecture. Defines:

* `RoundingMode`, `TieBreak`, `RoundResult` — the modes and the
  result ADT (`.finite`, `.overflow`, `.undefined`).
* `Format.IsUndefined`, `Format.IsOverflow` — when each `RoundResult`
  case fires.
* `IsFaithfulRound` — RoundDown or RoundUp.
* `Rounds : Format → RoundingMode → ℝ → RoundResult → Prop` — the
  specification relation, all seven modes.

The companion file **`Mpfx/RoundOp.lean`** adds the noncomputable
function `rnd` and the bridge `rnd_iff_rounds`.
-/

namespace Mpfx

/-- Tie-breaking for the nearest-rounding modes. -/
inductive TieBreak where
  /-- Ties to the value with even significand (IEEE `roundTiesToEven`). -/
  | toEven : TieBreak
  /-- Ties to the value with larger magnitude (IEEE `roundTiesToAway`). -/
  | awayZero : TieBreak
deriving DecidableEq, Repr

/-- IEEE-754 + paper-extended rounding modes.

* `ToNegative` (RTN) — round toward `-∞`.
* `ToPositive` (RTP) — round toward `+∞`.
* `ToZero` (RTZ) — round toward `0`.
* `AwayZero` (RAZ) — round away from `0`.
* `ToOdd` (RTO; not IEEE) — round to the F-adjacent with odd significand.
* `Nearest tb` — round to nearest; ties broken by `tb`. -/
inductive RoundingMode where
  | toNegative : RoundingMode
  | toPositive : RoundingMode
  | toZero : RoundingMode
  | awayZero : RoundingMode
  | toOdd : RoundingMode
  | nearest : TieBreak → RoundingMode
deriving DecidableEq, Repr

/-- The result of rounding a real `x` in a `Format` with some `RoundingMode`.

* `.finite d` — `d : Dyadic` is the rounded value.
* `.overflow positive` — `|x|` exceeds the format's magnitude bound. The
  `positive : Bool` records the sign of the would-be result: `true` for
  positive overflow, `false` for negative. (The would-be result is never
  zero, since `0 ∈ F` always.)
* `.undefined` — the `(Format, RoundingMode)` combination is degenerate
  and rounding has no semantic meaning. Currently fires only on
  `(p = 1, exp = ⊥, rm ∈ {.toOdd, .nearest .toEven})`. -/
inductive RoundResult where
  | finite (d : Dyadic) : RoundResult
  | overflow (positive : Bool) : RoundResult
  | undefined : RoundResult

namespace RoundResult

/-- Pointwise negation on `RoundResult`. `.finite y` maps to `.finite (-y)`;
`.overflow positive` flips the sign bit; `.undefined` is a fixed point. -/
def neg : RoundResult → RoundResult
  | .finite y    => .finite (-y)
  | .overflow b  => .overflow !b
  | .undefined   => .undefined

@[simp] theorem neg_finite (y : Dyadic) : (RoundResult.finite y).neg = .finite (-y) := rfl
@[simp] theorem neg_overflow (b : Bool) :
    (RoundResult.overflow b).neg = .overflow !b := rfl
@[simp] theorem neg_undefined : RoundResult.undefined.neg = .undefined := rfl

@[simp] theorem neg_neg (r : RoundResult) : r.neg.neg = r := by
  cases r <;> simp [neg]

end RoundResult

/-- The format/mode pair is degenerate (no meaningful rounding):
`(1, ⊥, rm)` for `rm ∈ {.toOdd, .nearest .toEven}` — precision `1` with
no quantum has no anchor for parity, so the modes that consult
`IsOdd`/`IsEven` are meaningless.

The `(⊤, ⊥)` case (fully unconstrained) is structurally excluded by
`FiniteFormat`'s `finite` invariant. -/
def FiniteFormat.IsUndefined (F : FiniteFormat) (rm : RoundingMode) : Prop :=
  F.p = (1 : ℕ+) ∧ F.exp = ⊥ ∧
    (rm = .toOdd ∨ rm = .nearest .toEven)

/-- `IsUndefined` depends only on `(F.p, F.exp)`, both preserved by
`F.unbounded`. -/
@[simp] theorem FiniteFormat.unbounded_isUndefined (F : FiniteFormat)
    (rm : RoundingMode) :
    F.unbounded.IsUndefined rm = F.IsUndefined rm := rfl

/-! ### The specification relation `Rounds`

`Rounds F rm x r : Prop` asserts that `r : RoundResult` is *the* answer
that mode `rm` gives for input `x : ℝ` in format `F`:

* `Rounds F rm x .undefined`  ↔  `F.IsUndefined rm`.
* `Rounds F rm x .overflow`   ↔  not undefined *and* the unbounded
                                 rounding produces a value that
                                 violates `F.b`. (IEEE-style overflow.)
* `Rounds F rm x (.finite y)` ↔  not undefined *and* `y` is the
                                 unbounded rounding *and* `y` fits the
                                 bound `F.b`.

The mode-specific rounding spec `RoundsFinite` is evaluated against
`F.unbounded` (i.e., `F` with `b := ⊤`) — the bound check is a
*separate* conjunct, applied to the value chosen by the unbounded
spec. This ensures IEEE-style overflow: saturation isn't a "valid
answer" — the only candidate is the unbounded rounding, and overflow
fires if and only if that candidate is out of range. -/

/-- A *faithful* rounding of `x`: `y ∈ F` is either the largest F-element
≤ `x` (RTN) or the smallest F-element ≥ `x` (RTP). All of RTO, RNE, RNA
require their result to be faithful. -/
def IsFaithfulRound (F : FiniteFormat) (x : ℝ) (y : Dyadic) : Prop :=
  (y ∈ F ∧ (y : ℝ) ≤ x ∧ ∀ z : Dyadic, z ∈ F → (z : ℝ) ≤ x → (z : ℝ) ≤ (y : ℝ)) ∨
  (y ∈ F ∧ x ≤ (y : ℝ) ∧ ∀ z : Dyadic, z ∈ F → x ≤ (z : ℝ) → (y : ℝ) ≤ (z : ℝ))

-- `ParityFormat.IsOdd` and `ParityFormat.IsEven` live in
-- `Mpfx/Format.lean`, built on `Format.numDigits` (Lemma 5.1) +
-- `Dyadic.IsRepresentableAtP`.

/-- The finite-result rounding spec: when `r = .finite y`, this is the
mode-specific condition `y` must satisfy. Lifted out of `Rounds` so the
`.overflow` clause can quantify over its negation. -/
def RoundsFinite (F : FiniteFormat) (rm : RoundingMode) (x : ℝ) (y : Dyadic) :
    Prop :=
  y ∈ F ∧
  match rm with
  | .toNegative =>
      (y : ℝ) ≤ x ∧
      ∀ z : Dyadic, z ∈ F → (z : ℝ) ≤ x → (z : ℝ) ≤ (y : ℝ)
  | .toPositive =>
      x ≤ (y : ℝ) ∧
      ∀ z : Dyadic, z ∈ F → x ≤ (z : ℝ) → (y : ℝ) ≤ (z : ℝ)
  | .toZero =>
      |(y : ℝ)| ≤ |x| ∧ (y : ℝ) * x ≥ 0 ∧
      ∀ z : Dyadic, z ∈ F → |(z : ℝ)| ≤ |x| → (z : ℝ) * x ≥ 0 →
        |(z : ℝ)| ≤ |(y : ℝ)|
  | .awayZero =>
      |x| ≤ |(y : ℝ)| ∧ (y : ℝ) * x ≥ 0 ∧
      ∀ z : Dyadic, z ∈ F → |x| ≤ |(z : ℝ)| → (z : ℝ) * x ≥ 0 →
        |(y : ℝ)| ≤ |(z : ℝ)|
  | .toOdd =>
      IsFaithfulRound F x y ∧
      (x ≠ (y : ℝ) →
        ∃ F' : ParityFormat, F'.toFormat = F.toFormat ∧ F'.IsOdd y)
  | .nearest .toEven =>
      IsFaithfulRound F x y ∧
      (∀ z : Dyadic, z ∈ F → IsFaithfulRound F x z →
        |x - (y : ℝ)| ≤ |x - (z : ℝ)|) ∧
      ((∃ z : Dyadic, z ∈ F ∧ IsFaithfulRound F x z ∧
          z ≠ y ∧ |x - (y : ℝ)| = |x - (z : ℝ)|) →
        ∃ F' : ParityFormat, F'.toFormat = F.toFormat ∧ F'.IsEven y)
  | .nearest .awayZero =>
      IsFaithfulRound F x y ∧
      (∀ z : Dyadic, z ∈ F → IsFaithfulRound F x z →
        |x - (y : ℝ)| ≤ |x - (z : ℝ)|) ∧
      (∀ z : Dyadic, z ∈ F → IsFaithfulRound F x z →
          z ≠ y → |x - (y : ℝ)| = |x - (z : ℝ)| → |(z : ℝ)| ≤ |(y : ℝ)|)

/-- Per-mode, per-result rounding-specification predicate. Dispatches on
the `RoundResult` constructor; the mode-spec is always against
`F.unbounded` and the bound `F.b` is checked separately. -/
def Rounds (F : FiniteFormat) (rm : RoundingMode) (x : ℝ) (r : RoundResult) :
    Prop :=
  match r with
  | .undefined   => F.IsUndefined rm
  | .overflow b  =>
      ¬ F.IsUndefined rm ∧
      ∃ y, RoundsFinite F.unbounded rm x y ∧ ¬ Format.boundOK F.b y ∧
           (b ↔ (0 : ℚ) < (y : ℚ))
  | .finite y    =>
      ¬ F.IsUndefined rm ∧
      RoundsFinite F.unbounded rm x y ∧ Format.boundOK F.b y

/-! ## Sign-symmetry algebraic helpers -/

private lemma neg_sub_neg_abs (a b : ℝ) : |(-a) - (-b)| = |a - b| := by
  rw [show -a - -b = -(a - b) by ring, abs_neg]

private lemma abs_neg_sub_dyadic (x : ℝ) (z : Dyadic) :
    |(-x) - (z : ℝ)| = |x - ((-z : Dyadic) : ℝ)| := by
  rw [Dyadic.coe_real_neg, show -x - (z : ℝ) = -(x - -(z : ℝ)) by ring, abs_neg]

/-- Sign-flip iff for the `(b ↔ 0 < y)` predicate under `y ↦ -y`, given
`y ≠ 0`. Used inside the overflow case of each `Rounds.neg_*` theorem. -/
private lemma sign_iff_neg (b : Bool) {y : ℚ} (hy : y ≠ 0) :
    (b ↔ 0 < y) ↔ (!b ↔ 0 < -y) := by
  rcases lt_or_gt_of_ne hy with hneg | hpos
  · have h1 : ¬ (0 < y) := not_lt.mpr (le_of_lt hneg)
    have h2 : 0 < -y := by linarith
    cases b <;> simp [h1, h2]
  · have h1 : ¬ (0 < -y) := not_lt.mpr (by linarith)
    cases b <;> simp [hpos, h1]

/-- Helper used inside the `.overflow` case of every sign-symmetry theorem:
extract `y ≠ 0` from the bound-violation hypothesis. -/
private lemma overflow_witness_ne_zero {F : FiniteFormat} {y : Dyadic}
    (h : ¬ Format.boundOK F.b y) : (y : ℚ) ≠ 0 := by
  intro h0
  apply h
  have hy0 : y = 0 := Subtype.ext h0
  rw [hy0]; exact Format.boundOK_zero _

/-! ## Sign-symmetry helper: `IsFaithfulRound` -/

/-- `IsFaithfulRound` is invariant under joint negation of `x` and `y`. The
two disjuncts swap roles: a max-below witness for `x` becomes a min-above
witness for `-x`. -/
theorem IsFaithfulRound.neg_iff (F : FiniteFormat) (x : ℝ) (y : Dyadic) :
    IsFaithfulRound F x y ↔ IsFaithfulRound F (-x) (-y) := by
  unfold IsFaithfulRound
  simp only [Dyadic.coe_real_neg, FiniteFormat.mem_neg_iff]
  constructor
  · rintro (⟨hm, h_le, h_max⟩ | ⟨hm, h_le, h_min⟩)
    · right
      refine ⟨hm, by linarith, ?_⟩
      intro z hz hxz
      have hnz : (-z) ∈ F := FiniteFormat.neg_mem hz
      have hnzx : ((-z : Dyadic) : ℝ) ≤ x := by rw [Dyadic.coe_real_neg]; linarith
      have h := h_max (-z) hnz hnzx
      rw [Dyadic.coe_real_neg] at h; linarith
    · left
      refine ⟨hm, by linarith, ?_⟩
      intro z hz hzx
      have hnz : (-z) ∈ F := FiniteFormat.neg_mem hz
      have hnzx : x ≤ ((-z : Dyadic) : ℝ) := by rw [Dyadic.coe_real_neg]; linarith
      have h := h_min (-z) hnz hnzx
      rw [Dyadic.coe_real_neg] at h; linarith
  · rintro (⟨hm, h_le, h_max⟩ | ⟨hm, h_le, h_min⟩)
    · right
      refine ⟨hm, by linarith, ?_⟩
      intro z hz hxz
      have hnz : (-z) ∈ F := FiniteFormat.neg_mem hz
      have hnzx : ((-z : Dyadic) : ℝ) ≤ -x := by rw [Dyadic.coe_real_neg]; linarith
      have h := h_max (-z) hnz hnzx
      rw [Dyadic.coe_real_neg] at h; linarith
    · left
      refine ⟨hm, by linarith, ?_⟩
      intro z hz hzx
      have hnz : (-z) ∈ F := FiniteFormat.neg_mem hz
      have hnzx : -x ≤ ((-z : Dyadic) : ℝ) := by rw [Dyadic.coe_real_neg]; linarith
      have h := h_min (-z) hnz hnzx
      rw [Dyadic.coe_real_neg] at h; linarith

/-- `IsFaithfulRound` is exactly "round-down or round-up", phrased via the
directed `RoundsFinite` specs. This lets the round-to-nearest machinery work
with `RoundsFinite .toNegative/.toPositive` while the `.nearest` spec hands
out an `IsFaithfulRound`. -/
theorem isFaithfulRound_iff_directed {F : FiniteFormat} {x : ℝ} {y : Dyadic} :
    IsFaithfulRound F x y ↔
      RoundsFinite F .toNegative x y ∨ RoundsFinite F .toPositive x y := by
  unfold IsFaithfulRound RoundsFinite
  constructor
  · rintro (⟨hm, h_le, h_max⟩ | ⟨hm, h_le, h_min⟩)
    · exact Or.inl ⟨hm, h_le, h_max⟩
    · exact Or.inr ⟨hm, h_le, h_min⟩
  · rintro (⟨hm, h_le, h_max⟩ | ⟨hm, h_le, h_min⟩)
    · exact Or.inl ⟨hm, h_le, h_max⟩
    · exact Or.inr ⟨hm, h_le, h_min⟩

/-- If `x ∈ F` and `y` is the RTO-rounding of `x` in `F`, then `y = x`. -/
theorem RoundsFinite.toOdd_unique_of_mem {F : FiniteFormat} {x : Dyadic}
    (hx : x ∈ F) {y : Dyadic} (h : RoundsFinite F .toOdd (x : ℝ) y) : y = x := by
  obtain ⟨_, hadj, _⟩ := h
  rcases hadj with ⟨-, hyx, hmax⟩ | ⟨-, hxy, hmin⟩
  · -- round-down: (y:ℝ) ≤ (x:ℝ) and y is largest such
    have hxy : (x : ℝ) ≤ (y : ℝ) := hmax x hx (le_refl _)
    exact (Dyadic.coe_real_inj y x).mp (le_antisymm hyx hxy)
  · -- round-up: (x:ℝ) ≤ (y:ℝ) and y is smallest such
    have hyx : (y : ℝ) ≤ (x : ℝ) := hmin x hx (le_refl _)
    exact (Dyadic.coe_real_inj y x).mp (le_antisymm hyx hxy)

/-- A representable value is its own faithful rounding: `d` is the largest
`F`-element `≤ d` (the round-down disjunct). -/
theorem isFaithfulRound_self {F : FiniteFormat} {d : Dyadic} (hd : d ∈ F) :
    IsFaithfulRound F (d : ℝ) d :=
  Or.inl ⟨hd, le_rfl, fun _ _ hz => hz⟩

/-- Two reals with equal magnitude and a common sign are equal. -/
private theorem eq_of_abs_eq_of_mul_nonneg {a b : ℝ}
    (habs : |a| = |b|) (hsign : 0 ≤ a * b) : a = b := by
  rcases abs_eq_abs.mp habs with h | h
  · exact h
  · -- `a = -b` forces `b = 0` (else the product is strictly negative), so `a = b`.
    subst h
    have hbb : b * b = 0 :=
      le_antisymm (by nlinarith) (mul_self_nonneg b)
    have hb : b = 0 := mul_self_eq_zero.mp hbb
    rw [hb]; ring

/-- **Rounding fixes representable values** — the spec-relational form of
Flocq's `round_generic` (paper Def. 7: `∀ f ∈ F, ◦(f) = f`). If `d ∈ F` and
`y` is the `rm`-rounding of `(d : ℝ)` in `F`, then `y = d`, for *any* mode `rm`
(including the degenerate `IsUndefined` formats — `RoundsFinite` never consults
`IsUndefined`). -/
theorem RoundsFinite.eq_of_mem {F : FiniteFormat} {rm : RoundingMode} {d : Dyadic}
    (hd : d ∈ F) {y : Dyadic} (h : RoundsFinite F rm (d : ℝ) y) : y = d := by
  obtain ⟨hyF, hcond⟩ := h
  have coe_inj : (y : ℝ) = (d : ℝ) → y = d := (Dyadic.coe_real_inj y d).mp
  cases rm with
  | toNegative =>
      obtain ⟨hle, hmax⟩ := hcond
      exact coe_inj (le_antisymm hle (hmax d hd le_rfl))
  | toPositive =>
      obtain ⟨hle, hmin⟩ := hcond
      exact coe_inj (le_antisymm (hmin d hd le_rfl) hle)
  | toZero =>
      obtain ⟨habs, hsign, hmax⟩ := hcond
      have hge : |(d : ℝ)| ≤ |(y : ℝ)| := hmax d hd le_rfl (mul_self_nonneg _)
      exact coe_inj (eq_of_abs_eq_of_mul_nonneg (le_antisymm habs hge) hsign)
  | awayZero =>
      obtain ⟨habs, hsign, hmin⟩ := hcond
      have hle : |(y : ℝ)| ≤ |(d : ℝ)| := hmin d hd le_rfl (mul_self_nonneg _)
      exact coe_inj (eq_of_abs_eq_of_mul_nonneg (le_antisymm hle habs) hsign)
  | toOdd =>
      exact RoundsFinite.toOdd_unique_of_mem hd ⟨hyF, hcond⟩
  | nearest tb =>
      cases tb with
      | toEven =>
          obtain ⟨_, hnear, _⟩ := hcond
          have hle := hnear d hd (isFaithfulRound_self hd)
          rw [sub_self, abs_zero] at hle
          have : (d : ℝ) - (y : ℝ) = 0 := abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
          exact coe_inj (by linarith)
      | awayZero =>
          obtain ⟨_, hnear, _⟩ := hcond
          have hle := hnear d hd (isFaithfulRound_self hd)
          rw [sub_self, abs_zero] at hle
          have : (d : ℝ) - (y : ℝ) = 0 := abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
          exact coe_inj (by linarith)

/-! ## Sign-symmetry of `Rounds`

For each rounding mode we relate `Rounds F rm x r` to `Rounds F rm' (-x) r.neg`,
where `rm'` is either `rm` itself (modes symmetric around zero) or its
"flipped" partner (`.toNegative` ↔ `.toPositive`).

Each mode gets its own theorem — there is intentionally no unified
`Rounds.neg` polymorphic over the mode. -/

/-- Sign-symmetry of `RoundsFinite` at mode `.toZero`. -/
theorem RoundsFinite.neg_toZero (F : FiniteFormat) (x : ℝ) (y : Dyadic) :
    RoundsFinite F .toZero x y ↔ RoundsFinite F .toZero (-x) (-y) := by
  unfold RoundsFinite
  simp only [Dyadic.coe_real_neg, abs_neg, neg_mul_neg, FiniteFormat.mem_neg_iff]
  refine and_congr_right' (and_congr_right' (and_congr_right' ?_))
  refine ⟨fun h z hz hzabs hzsign => ?_, fun h z hz hzabs hzsign => ?_⟩
  · have hnz : (-z) ∈ F := FiniteFormat.neg_mem hz
    have hnzabs : |((-z : Dyadic) : ℝ)| ≤ |x| := by
      rw [Dyadic.coe_real_neg, abs_neg]; exact hzabs
    have hnzsign : ((-z : Dyadic) : ℝ) * x ≥ 0 := by
      rw [Dyadic.coe_real_neg]; linarith
    have := h (-z) hnz hnzabs hnzsign
    rwa [Dyadic.coe_real_neg, abs_neg] at this
  · have hnz : (-z) ∈ F := FiniteFormat.neg_mem hz
    have hnzabs : |((-z : Dyadic) : ℝ)| ≤ |x| := by
      rw [Dyadic.coe_real_neg, abs_neg]; exact hzabs
    have hnzsign : ((-z : Dyadic) : ℝ) * (-x) ≥ 0 := by
      rw [Dyadic.coe_real_neg]; linarith
    have := h (-z) hnz hnzabs hnzsign
    rwa [Dyadic.coe_real_neg, abs_neg] at this

/-- Sign-symmetry: `.toNegative` ↔ `.toPositive` swaps under negation. -/
theorem RoundsFinite.neg_toNegative_iff_toPositive (F : FiniteFormat) (x : ℝ)
    (y : Dyadic) :
    RoundsFinite F .toNegative x y ↔ RoundsFinite F .toPositive (-x) (-y) := by
  unfold RoundsFinite
  simp only [Dyadic.coe_real_neg, FiniteFormat.mem_neg_iff]
  refine and_congr_right' ?_
  constructor
  · rintro ⟨h_le, h_max⟩
    refine ⟨by linarith, ?_⟩
    intro z hz hzx
    have hnz : (-z) ∈ F := FiniteFormat.neg_mem hz
    have hnzx : ((-z : Dyadic) : ℝ) ≤ x := by
      rw [Dyadic.coe_real_neg]; linarith
    have h := h_max (-z) hnz hnzx
    rw [Dyadic.coe_real_neg] at h
    linarith
  · rintro ⟨h_le, h_max⟩
    refine ⟨by linarith, ?_⟩
    intro z hz hzx
    have hnz : (-z) ∈ F := FiniteFormat.neg_mem hz
    have hnzx : -x ≤ ((-z : Dyadic) : ℝ) := by
      rw [Dyadic.coe_real_neg]; linarith
    have h := h_max (-z) hnz hnzx
    rw [Dyadic.coe_real_neg] at h
    linarith

/-- **Sign-symmetry combinator for `Rounds`.** Given that undefinedness matches
(`hu`) and that the finite spec is negation-symmetric (`hfin`), the whole
`RoundResult`-level `Rounds` predicate is negation-symmetric too. The
`undefined`/`overflow`/`finite` case scaffold — previously copy-pasted across
every `Rounds.neg_*` theorem — lives here once. -/
theorem Rounds.neg_congr {F : FiniteFormat} {rm rm' : RoundingMode} {x : ℝ}
    (hu : F.IsUndefined rm ↔ F.IsUndefined rm')
    (hfin : ∀ y : Dyadic,
      RoundsFinite F.unbounded rm x y ↔ RoundsFinite F.unbounded rm' (-x) (-y))
    (r : RoundResult) :
    Rounds F rm x r ↔ Rounds F rm' (-x) r.neg := by
  cases r with
  | undefined => simpa [Rounds, RoundResult.neg] using hu
  | overflow b =>
      simp only [Rounds, RoundResult.neg_overflow]
      refine and_congr (not_congr hu) ?_
      constructor
      · rintro ⟨y, h_rf, h_bnd, h_sign⟩
        have hy0 := overflow_witness_ne_zero h_bnd
        refine ⟨-y, (hfin y).mp h_rf, by rwa [Format.boundOK_neg_iff], ?_⟩
        rw [Subring.coe_neg]
        exact (sign_iff_neg b hy0).mp h_sign
      · rintro ⟨y, h_rf, h_bnd, h_sign⟩
        have hy0 := overflow_witness_ne_zero h_bnd
        have hiff := hfin (-y)
        simp only [neg_neg] at hiff
        refine ⟨-y, hiff.mpr h_rf, by rwa [Format.boundOK_neg_iff], ?_⟩
        rw [Subring.coe_neg]
        have := (sign_iff_neg (!b) hy0).mp h_sign
        simpa using this
  | finite y =>
      simp only [Rounds, RoundResult.neg]
      exact and_congr (not_congr hu)
        (and_congr (hfin y) (by rw [Format.boundOK_neg_iff]))

/-- `.toNegative` is RTP-symmetric under negation. -/
theorem Rounds.neg_toNegative_iff_toPositive (F : FiniteFormat) (x : ℝ)
    (r : RoundResult) :
    Rounds F .toNegative x r ↔ Rounds F .toPositive (-x) r.neg :=
  Rounds.neg_congr (by simp [FiniteFormat.IsUndefined])
    (RoundsFinite.neg_toNegative_iff_toPositive F.unbounded x) r

/-- Sign-symmetry of `RoundsFinite` at mode `.awayZero`. -/
theorem RoundsFinite.neg_awayZero (F : FiniteFormat) (x : ℝ) (y : Dyadic) :
    RoundsFinite F .awayZero x y ↔ RoundsFinite F .awayZero (-x) (-y) := by
  unfold RoundsFinite
  simp only [Dyadic.coe_real_neg, abs_neg, neg_mul_neg, FiniteFormat.mem_neg_iff]
  refine and_congr_right' (and_congr_right' (and_congr_right' ?_))
  refine ⟨fun h z hz hzabs hzsign => ?_, fun h z hz hzabs hzsign => ?_⟩
  · have hnz : (-z) ∈ F := FiniteFormat.neg_mem hz
    have hnzabs : |x| ≤ |((-z : Dyadic) : ℝ)| := by
      rw [Dyadic.coe_real_neg, abs_neg]; exact hzabs
    have hnzsign : ((-z : Dyadic) : ℝ) * x ≥ 0 := by
      rw [Dyadic.coe_real_neg]; linarith
    have := h (-z) hnz hnzabs hnzsign
    rwa [Dyadic.coe_real_neg, abs_neg] at this
  · have hnz : (-z) ∈ F := FiniteFormat.neg_mem hz
    have hnzabs : |x| ≤ |((-z : Dyadic) : ℝ)| := by
      rw [Dyadic.coe_real_neg, abs_neg]; exact hzabs
    have hnzsign : ((-z : Dyadic) : ℝ) * (-x) ≥ 0 := by
      rw [Dyadic.coe_real_neg]; linarith
    have := h (-z) hnz hnzabs hnzsign
    rwa [Dyadic.coe_real_neg, abs_neg] at this

/-- `.awayZero` is symmetric around zero. -/
theorem Rounds.neg_awayZero (F : FiniteFormat) (x : ℝ) (r : RoundResult) :
    Rounds F .awayZero x r ↔ Rounds F .awayZero (-x) r.neg :=
  Rounds.neg_congr Iff.rfl (RoundsFinite.neg_awayZero F.unbounded x) r

/-- Sign-symmetry of `RoundsFinite` at mode `.nearest .awayZero`. -/
theorem RoundsFinite.neg_nearest_awayZero (F : FiniteFormat) (x : ℝ) (y : Dyadic) :
    RoundsFinite F (.nearest .awayZero) x y ↔
      RoundsFinite F (.nearest .awayZero) (-x) (-y) := by
  unfold RoundsFinite
  simp only [FiniteFormat.mem_neg_iff]
  refine and_congr_right' ?_
  rw [← IsFaithfulRound.neg_iff]
  refine and_congr_right' (and_congr ?_ ?_)
  · constructor
    · intro h z hz hfr_z
      have hnz : (-z) ∈ F := FiniteFormat.neg_mem hz
      have hfr_nz : IsFaithfulRound F x (-z) :=
        (IsFaithfulRound.neg_iff F x (-z)).mpr (by simpa)
      have hh := h (-z) hnz hfr_nz
      change |(-x) - ((-y : Dyadic) : ℝ)| ≤ |(-x) - (z : ℝ)|
      rw [Dyadic.coe_real_neg, neg_sub_neg_abs, abs_neg_sub_dyadic]
      exact hh
    · intro h z hz hfr_z
      have hnz : (-z) ∈ F := FiniteFormat.neg_mem hz
      have hfr_nz : IsFaithfulRound F (-x) (-z) :=
        (IsFaithfulRound.neg_iff F x z).mp hfr_z
      have hh := h (-z) hnz hfr_nz
      rw [Dyadic.coe_real_neg, Dyadic.coe_real_neg, neg_sub_neg_abs, neg_sub_neg_abs] at hh
      exact hh
  · constructor
    · intro h z hz hfr_z hzne heq
      have hnz : (-z) ∈ F := FiniteFormat.neg_mem hz
      have hfr_nz : IsFaithfulRound F x (-z) :=
        (IsFaithfulRound.neg_iff F x (-z)).mpr (by simpa)
      have hne : (-z) ≠ y := fun hye => hzne (neg_eq_iff_eq_neg.mp hye)
      have heq' : |x - (y : ℝ)| = |x - ((-z : Dyadic) : ℝ)| := by
        rw [Dyadic.coe_real_neg, neg_sub_neg_abs] at heq
        rw [abs_neg_sub_dyadic] at heq
        exact heq
      have hh := h (-z) hnz hfr_nz hne heq'
      change |(z : ℝ)| ≤ |((-y : Dyadic) : ℝ)|
      rw [Dyadic.coe_real_neg] at hh
      rw [abs_neg] at hh
      rw [Dyadic.coe_real_neg, abs_neg]
      exact hh
    · intro h z hz hfr_z hzne heq
      have hnz : (-z) ∈ F := FiniteFormat.neg_mem hz
      have hfr_nz : IsFaithfulRound F (-x) (-z) :=
        (IsFaithfulRound.neg_iff F x z).mp hfr_z
      have hne : (-z) ≠ -y := fun hye => hzne (neg_inj.mp hye)
      have heq' : |(-x) - ((-y : Dyadic) : ℝ)| = |(-x) - ((-z : Dyadic) : ℝ)| := by
        rw [Dyadic.coe_real_neg, Dyadic.coe_real_neg, neg_sub_neg_abs, neg_sub_neg_abs]
        exact heq
      have hh := h (-z) hnz hfr_nz hne heq'
      rw [Dyadic.coe_real_neg, Dyadic.coe_real_neg, abs_neg, abs_neg] at hh
      exact hh

/-- `.nearest .awayZero` is symmetric around zero. -/
theorem Rounds.neg_nearest_awayZero (F : FiniteFormat) (x : ℝ) (r : RoundResult) :
    Rounds F (.nearest .awayZero) x r ↔
      Rounds F (.nearest .awayZero) (-x) r.neg :=
  Rounds.neg_congr Iff.rfl (RoundsFinite.neg_nearest_awayZero F.unbounded x) r

/-- Sign-symmetry of `RoundsFinite` at mode `.toOdd`. -/
theorem RoundsFinite.neg_toOdd (F : FiniteFormat) (x : ℝ) (y : Dyadic) :
    RoundsFinite F .toOdd x y ↔ RoundsFinite F .toOdd (-x) (-y) := by
  unfold RoundsFinite
  simp only [FiniteFormat.mem_neg_iff, ParityFormat.IsOdd.neg_iff, Dyadic.coe_real_neg,
    ne_eq, neg_inj]
  rw [← IsFaithfulRound.neg_iff]

/-- Sign-symmetry of `RoundsFinite` at mode `.nearest .toEven`. -/
theorem RoundsFinite.neg_nearest_toEven (F : FiniteFormat) (x : ℝ) (y : Dyadic) :
    RoundsFinite F (.nearest .toEven) x y ↔
      RoundsFinite F (.nearest .toEven) (-x) (-y) := by
  unfold RoundsFinite
  simp only [FiniteFormat.mem_neg_iff, ParityFormat.IsEven.neg_iff]
  refine and_congr_right' ?_
  rw [← IsFaithfulRound.neg_iff]
  refine and_congr_right' (and_congr ?_ ?_)
  · constructor
    · intro h z hz hfr_z
      have hnz : (-z) ∈ F := FiniteFormat.neg_mem hz
      have hfr_nz : IsFaithfulRound F x (-z) :=
        (IsFaithfulRound.neg_iff F x (-z)).mpr (by simpa)
      have hh := h (-z) hnz hfr_nz
      change |(-x) - ((-y : Dyadic) : ℝ)| ≤ |(-x) - (z : ℝ)|
      rw [Dyadic.coe_real_neg, neg_sub_neg_abs, abs_neg_sub_dyadic]
      exact hh
    · intro h z hz hfr_z
      have hnz : (-z) ∈ F := FiniteFormat.neg_mem hz
      have hfr_nz : IsFaithfulRound F (-x) (-z) :=
        (IsFaithfulRound.neg_iff F x z).mp hfr_z
      have hh := h (-z) hnz hfr_nz
      rw [Dyadic.coe_real_neg, Dyadic.coe_real_neg, neg_sub_neg_abs, neg_sub_neg_abs] at hh
      exact hh
  · constructor
    · intro h_impl ⟨z, hz, hfr_z, hzne, heq⟩
      apply h_impl
      refine ⟨-z, FiniteFormat.neg_mem hz,
        (IsFaithfulRound.neg_iff F x (-z)).mpr (by simpa), ?_, ?_⟩
      · intro hye; apply hzne; exact neg_eq_iff_eq_neg.mp hye
      · rw [Dyadic.coe_real_neg, neg_sub_neg_abs] at heq
        rw [abs_neg_sub_dyadic] at heq
        exact heq
    · intro h_impl ⟨z, hz, hfr_z, hzne, heq⟩
      apply h_impl
      refine ⟨-z, FiniteFormat.neg_mem hz,
        (IsFaithfulRound.neg_iff F x z).mp hfr_z, ?_, ?_⟩
      · intro hye; apply hzne; exact neg_inj.mp hye
      · change |(-x) - ((-y : Dyadic) : ℝ)| = |(-x) - ((-z : Dyadic) : ℝ)|
        rw [Dyadic.coe_real_neg, Dyadic.coe_real_neg, neg_sub_neg_abs, neg_sub_neg_abs]
        exact heq

/-- `.nearest .toEven` is symmetric around zero. -/
theorem Rounds.neg_nearest_toEven (F : FiniteFormat) (x : ℝ) (r : RoundResult) :
    Rounds F (.nearest .toEven) x r ↔ Rounds F (.nearest .toEven) (-x) r.neg :=
  Rounds.neg_congr Iff.rfl (RoundsFinite.neg_nearest_toEven F.unbounded x) r

/-- `.toOdd` is symmetric around zero. -/
theorem Rounds.neg_toOdd (F : FiniteFormat) (x : ℝ) (r : RoundResult) :
    Rounds F .toOdd x r ↔ Rounds F .toOdd (-x) r.neg :=
  Rounds.neg_congr Iff.rfl (RoundsFinite.neg_toOdd F.unbounded x) r

/-- `.toZero` is symmetric around zero. -/
theorem Rounds.neg_toZero (F : FiniteFormat) (x : ℝ) (r : RoundResult) :
    Rounds F .toZero x r ↔ Rounds F .toZero (-x) r.neg :=
  Rounds.neg_congr Iff.rfl (RoundsFinite.neg_toZero F.unbounded x) r

/-! ## Directed-vs-zero-relative mode equivalences

For nonnegative `x`, RTP coincides with RAZ and RTN with RTZ; for nonpositive
`x`, the relationships swap. These let callers reduce RTP/RTN to RTZ/RAZ
when the sign of `x` is known. -/

private lemma dyadic_coe_zero : ((0 : Dyadic) : ℝ) = 0 := by push_cast; rfl

theorem RoundsFinite.toPositive_iff_awayZero_of_nonneg
    (F : FiniteFormat) {x : ℝ} (hx : 0 ≤ x) (y : Dyadic) :
    RoundsFinite F .toPositive x y ↔ RoundsFinite F .awayZero x y := by
  unfold RoundsFinite
  refine and_congr_right' ?_
  constructor
  · rintro ⟨hxy, h_min⟩
    have hy_nn : (0 : ℝ) ≤ (y : ℝ) := le_trans hx hxy
    refine ⟨?_, mul_nonneg hy_nn hx, ?_⟩
    · rw [abs_of_nonneg hx, abs_of_nonneg hy_nn]; exact hxy
    · intro z hz hxz hzx
      rw [abs_of_nonneg hx] at hxz
      rcases eq_or_lt_of_le hx with rfl | hx_pos
      · have h_zero_in : (0 : Dyadic) ∈ F := FiniteFormat.zero_mem F
        have hy_le_zero := h_min 0 h_zero_in (by rw [dyadic_coe_zero])
        rw [dyadic_coe_zero] at hy_le_zero
        have hy_eq : (y : ℝ) = 0 := le_antisymm hy_le_zero hy_nn
        rw [hy_eq, abs_zero]; exact abs_nonneg _
      · have hz_nn : (0 : ℝ) ≤ (z : ℝ) := by
          by_contra hz_neg
          rw [not_le] at hz_neg
          linarith [mul_neg_of_neg_of_pos hz_neg hx_pos]
        rw [abs_of_nonneg hz_nn] at hxz
        rw [abs_of_nonneg hy_nn, abs_of_nonneg hz_nn]
        exact h_min z hz hxz
  · rintro ⟨h_xa, h_zx, h_min⟩
    rw [abs_of_nonneg hx] at h_xa
    rcases eq_or_lt_of_le hx with rfl | hx_pos
    · have h_zero_in : (0 : Dyadic) ∈ F := FiniteFormat.zero_mem F
      have h := h_min 0 h_zero_in
        (by rw [dyadic_coe_zero])
        (by rw [dyadic_coe_zero]; simp)
      rw [dyadic_coe_zero, abs_zero] at h
      have hy_abs_zero : |(y : ℝ)| = 0 := le_antisymm h (abs_nonneg _)
      have hy_eq : (y : ℝ) = 0 := abs_eq_zero.mp hy_abs_zero
      refine ⟨by rw [hy_eq], ?_⟩
      intro z hz hxz
      rw [hy_eq]; exact hxz
    · have hy_nn : (0 : ℝ) ≤ (y : ℝ) :=
        (mul_nonneg_iff_of_pos_right hx_pos).mp h_zx
      rw [abs_of_nonneg hy_nn] at h_xa
      refine ⟨h_xa, ?_⟩
      intro z hz hxz
      have hz_nn : (0 : ℝ) ≤ (z : ℝ) := le_trans hx_pos.le hxz
      have h := h_min z hz
        (by rw [abs_of_nonneg hx, abs_of_nonneg hz_nn]; exact hxz)
        (mul_nonneg hz_nn hx_pos.le)
      rw [abs_of_nonneg hy_nn, abs_of_nonneg hz_nn] at h
      exact h

theorem RoundsFinite.toPositive_iff_toZero_of_nonpos
    (F : FiniteFormat) {x : ℝ} (hx : x ≤ 0) (y : Dyadic) :
    RoundsFinite F .toPositive x y ↔ RoundsFinite F .toZero x y := by
  unfold RoundsFinite
  refine and_congr_right' ?_
  constructor
  · rintro ⟨hxy, h_min⟩
    have h_zero_in : (0 : Dyadic) ∈ F := FiniteFormat.zero_mem F
    have hy_le_zero : (y : ℝ) ≤ 0 := by
      have := h_min 0 h_zero_in (by rw [dyadic_coe_zero]; exact hx)
      rwa [dyadic_coe_zero] at this
    refine ⟨?_, ?_, ?_⟩
    · rw [abs_of_nonpos hx, abs_of_nonpos hy_le_zero]; linarith
    · nlinarith
    · intro z hz hzabs hzx
      rw [abs_of_nonpos hx] at hzabs
      rcases eq_or_lt_of_le hx with hx0 | hx_neg
      · subst hx0
        have hxy' : (y : ℝ) ≥ 0 := hxy
        have hy_eq : (y : ℝ) = 0 := le_antisymm hy_le_zero hxy'
        rw [hy_eq, abs_zero]
        have h_z_zero : (z : ℝ) = 0 := by
          have : |(z : ℝ)| ≤ 0 := by linarith
          have := abs_nonneg (z : ℝ)
          have : |(z : ℝ)| = 0 := by linarith
          exact abs_eq_zero.mp this
        rw [h_z_zero, abs_zero]
      · have hz_nonpos : (z : ℝ) ≤ 0 := by
          by_contra hz_pos
          rw [not_le] at hz_pos
          have : (z : ℝ) * x < 0 := mul_neg_of_pos_of_neg hz_pos hx_neg
          linarith
        rw [abs_of_nonpos hz_nonpos] at hzabs
        have hxz : x ≤ (z : ℝ) := by linarith
        have h_y_le_z := h_min z hz hxz
        rw [abs_of_nonpos hy_le_zero, abs_of_nonpos hz_nonpos]
        linarith
  · rintro ⟨hya, h_yx, h_min⟩
    rw [abs_of_nonpos hx] at hya
    rcases eq_or_lt_of_le hx with hx0 | hx_neg
    · subst hx0
      have hy_abs_zero : |(y : ℝ)| ≤ 0 := by linarith
      have hy_eq : (y : ℝ) = 0 := by
        have hnn := abs_nonneg (y : ℝ)
        have habs : |(y : ℝ)| = 0 := le_antisymm hy_abs_zero hnn
        exact abs_eq_zero.mp habs
      refine ⟨by rw [hy_eq], ?_⟩
      intro z hz hxz
      rw [hy_eq]; exact hxz
    · have hy_le_zero : (y : ℝ) ≤ 0 := by
        by_contra h_pos
        rw [not_le] at h_pos
        have : (y : ℝ) * x < 0 := mul_neg_of_pos_of_neg h_pos hx_neg
        linarith
      rw [abs_of_nonpos hy_le_zero] at hya
      refine ⟨by linarith, ?_⟩
      intro z hz hxz
      by_cases hz_np : (z : ℝ) ≤ 0
      · have hzabs : |(z : ℝ)| ≤ |x| := by
          rw [abs_of_nonpos hx, abs_of_nonpos hz_np]; linarith
        have hzx : (z : ℝ) * x ≥ 0 := by
          have : (z : ℝ) * x = (-(z : ℝ)) * (-x) := by ring
          rw [this]
          exact mul_nonneg (neg_nonneg.mpr hz_np) (neg_nonneg.mpr hx_neg.le)
        have h := h_min z hz hzabs hzx
        rw [abs_of_nonpos hy_le_zero, abs_of_nonpos hz_np] at h
        linarith
      · push Not at hz_np
        linarith

/-- For `x ≤ 0`, rounding toward `−∞` coincides with rounding away from zero
(both move to the more-negative side). Sign-mirror of
`toPositive_iff_awayZero_of_nonneg`, derived via joint negation. -/
theorem RoundsFinite.toNegative_iff_awayZero_of_nonpos
    (F : FiniteFormat) {x : ℝ} (hx : x ≤ 0) (y : Dyadic) :
    RoundsFinite F .toNegative x y ↔ RoundsFinite F .awayZero x y :=
  calc RoundsFinite F .toNegative x y
      ↔ RoundsFinite F .toPositive (-x) (-y) :=
        RoundsFinite.neg_toNegative_iff_toPositive F x y
    _ ↔ RoundsFinite F .awayZero (-x) (-y) :=
        RoundsFinite.toPositive_iff_awayZero_of_nonneg F (neg_nonneg.mpr hx) (-y)
    _ ↔ RoundsFinite F .awayZero x y := (RoundsFinite.neg_awayZero F x y).symm

/-- For `0 ≤ x`, rounding toward `−∞` coincides with rounding toward zero
(both move down). Sign-mirror of `toPositive_iff_toZero_of_nonpos`. -/
theorem RoundsFinite.toNegative_iff_toZero_of_nonneg
    (F : FiniteFormat) {x : ℝ} (hx : 0 ≤ x) (y : Dyadic) :
    RoundsFinite F .toNegative x y ↔ RoundsFinite F .toZero x y :=
  calc RoundsFinite F .toNegative x y
      ↔ RoundsFinite F .toPositive (-x) (-y) :=
        RoundsFinite.neg_toNegative_iff_toPositive F x y
    _ ↔ RoundsFinite F .toZero (-x) (-y) :=
        RoundsFinite.toPositive_iff_toZero_of_nonpos F (neg_nonpos.mpr hx) (-y)
    _ ↔ RoundsFinite F .toZero x y := (RoundsFinite.neg_toZero F x y).symm

/-- **Result-preserving congruence for `Rounds`.** Companion to `Rounds.neg_congr`
for the same-`x` mode equivalences: matching undefinedness (`hu`) and a same-input
`RoundsFinite` equivalence (`hfin`) lift to `Rounds`. -/
theorem Rounds.congr_of_roundsFinite {F : FiniteFormat} {rm rm' : RoundingMode}
    {x : ℝ} (hu : F.IsUndefined rm ↔ F.IsUndefined rm')
    (hfin : ∀ y : Dyadic,
      RoundsFinite F.unbounded rm x y ↔ RoundsFinite F.unbounded rm' x y)
    (r : RoundResult) :
    Rounds F rm x r ↔ Rounds F rm' x r := by
  cases r with
  | undefined => simpa [Rounds] using hu
  | overflow b =>
      simp only [Rounds]
      exact and_congr (not_congr hu)
        ⟨fun ⟨y, h_rf, rest⟩ => ⟨y, (hfin y).mp h_rf, rest⟩,
         fun ⟨y, h_rf, rest⟩ => ⟨y, (hfin y).mpr h_rf, rest⟩⟩
  | finite y =>
      simp only [Rounds]
      exact and_congr (not_congr hu) (and_congr (hfin y) Iff.rfl)

theorem Rounds.toPositive_iff_awayZero_of_nonneg
    (F : FiniteFormat) {x : ℝ} (hx : 0 ≤ x) (r : RoundResult) :
    Rounds F .toPositive x r ↔ Rounds F .awayZero x r :=
  Rounds.congr_of_roundsFinite (by simp [FiniteFormat.IsUndefined])
    (RoundsFinite.toPositive_iff_awayZero_of_nonneg F.unbounded hx) r

theorem Rounds.toPositive_iff_toZero_of_nonpos
    (F : FiniteFormat) {x : ℝ} (hx : x ≤ 0) (r : RoundResult) :
    Rounds F .toPositive x r ↔ Rounds F .toZero x r :=
  Rounds.congr_of_roundsFinite (by simp [FiniteFormat.IsUndefined])
    (RoundsFinite.toPositive_iff_toZero_of_nonpos F.unbounded hx) r

/-- Derived from `toPositive_iff_toZero_of_nonpos` via the RTN↔RTP and
RTZ self-symmetry theorems. -/
theorem Rounds.toNegative_iff_toZero_of_nonneg
    (F : FiniteFormat) {x : ℝ} (hx : 0 ≤ x) (r : RoundResult) :
    Rounds F .toNegative x r ↔ Rounds F .toZero x r := by
  have h1 := Rounds.neg_toNegative_iff_toPositive F x r
  have h2 :=
    Rounds.toPositive_iff_toZero_of_nonpos F (neg_nonpos.mpr hx) r.neg
  have h3 := (Rounds.neg_toZero F x r).symm
  exact h1.trans (h2.trans h3)

/-- Derived from `toPositive_iff_awayZero_of_nonneg` via the RTN↔RTP and
RAZ self-symmetry theorems. -/
theorem Rounds.toNegative_iff_awayZero_of_nonpos
    (F : FiniteFormat) {x : ℝ} (hx : x ≤ 0) (r : RoundResult) :
    Rounds F .toNegative x r ↔ Rounds F .awayZero x r := by
  have h1 := Rounds.neg_toNegative_iff_toPositive F x r
  have h2 :=
    Rounds.toPositive_iff_awayZero_of_nonneg F (neg_nonneg.mpr hx) r.neg
  have h3 := (Rounds.neg_awayZero F x r).symm
  exact h1.trans (h2.trans h3)


/-! ### Modes that are always defined -/

theorem not_isUndefined_toZero (F : FiniteFormat) :
    ¬ F.IsUndefined .toZero := by
  rintro ⟨-, -, h | h⟩ <;> simp at h

theorem not_isUndefined_awayZero (F : FiniteFormat) :
    ¬ F.IsUndefined .awayZero := by
  rintro ⟨-, -, h | h⟩ <;> simp at h

/-- Directed modes are never undefined. -/
theorem not_isUndefined_toNegative (F : FiniteFormat) :
    ¬ F.IsUndefined .toNegative := by
  rintro ⟨-, -, h | h⟩ <;> simp at h

theorem not_isUndefined_toPositive (F : FiniteFormat) :
    ¬ F.IsUndefined .toPositive := by
  rintro ⟨-, -, h | h⟩ <;> simp at h

/-- `2 ≤ F.p` rules out `IsUndefined` (which requires `p = 1`). -/
theorem not_isUndefined_of_two_le_p {F : FiniteFormat} {rm : RoundingMode}
    (hp : ((2 : ℕ+) : WithTop ℕ+) ≤ F.p) : ¬ F.IsUndefined rm := by
  rintro ⟨h1, -, -⟩
  rw [h1] at hp
  have h2 : (2 : ℕ+) ≤ (1 : ℕ+) := by exact_mod_cast hp
  have h3 : ((2 : ℕ+) : ℕ) ≤ ((1 : ℕ+) : ℕ) := h2
  simp at h3

/-- Package an out-of-bound unbounded rounding as an overflow `Rounds`
result (with the sign bit computed from the witness). -/
theorem rounds_overflow_of_not_boundOK {F : FiniteFormat} {rm : RoundingMode}
    {x : ℝ} {y : Dyadic} (h₁u : ¬ F.IsUndefined rm)
    (hy : RoundsFinite F.unbounded rm x y) (hbOK : ¬ Format.boundOK F.b y) :
    ∃ b, Rounds F rm x (.overflow b) :=
  ⟨decide ((0 : ℚ) < (y : ℚ)), h₁u, y, hy, hbOK, by simp⟩

end Mpfx
