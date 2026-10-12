import Fpy.FormatInference.Domain
import Mpfx.Format.Inference

/-!
# The abstract operators of Table 1

`ArithOp.fmt` is `op♯` for each rounded operator and `ExactOp.aval` for each
unrounded one; `ArithOp.fmt_sound` and `ExactOp.aval_sound` are the
obligations `Analysis.Sound.arith` and `Analysis.Sound.exact`.

On finite sets each operator acts element-wise. On abstract formats the rows
are Table 1's, with the specials each operator can produce added: the draft's
formats have none, but `logb 0 = −∞` and every format contains `0` (see
`docs/agents/FPY_PLAN.md`). A set meeting an abstract format is first replaced
by `⌈S⌉`.
-/

namespace Fpy

open Mpfx

/-! ## The `Num` operators on Mpfx values -/

theorem Dyadic.coe_real_eq_zero {d : Mpfx.Dyadic} : (d : ℝ) = 0 ↔ d = 0 :=
  ⟨eq_zero_of_coe_real_zero, fun h => by simp [h]⟩

theorem toReal_add (u v : WithSpecial Mpfx.Dyadic) :
    Num.add u.toReal v.toReal = (u + v).toReal := by
  rcases u with x | (a | _) <;> rcases v with y | (b | _) <;> simp [Num.add, WithSpecial.toReal]
  · split_ifs <;> simp

theorem toReal_mul (u v : WithSpecial Mpfx.Dyadic) :
    Num.mul u.toReal v.toReal = (u * v).toReal := by
  rcases u with x | (a | _) <;> rcases v with y | (b | _) <;>
    simp only [Num.mul, WithSpecial.toReal, WithSpecial.finite_mul_finite,
      WithSpecial.inf_mul_finite, WithSpecial.finite_mul_inf, WithSpecial.inf_mul_inf,
      WithSpecial.nan_mul, WithSpecial.mul_nan, Dyadic.coe_real_mul,
      Dyadic.coe_real_eq_zero, Dyadic.coe_real_lt_zero_iff]
  all_goals split_ifs <;> rfl

theorem toReal_neg (u : WithSpecial Mpfx.Dyadic) : Num.neg u.toReal = (-u).toReal := by
  rcases u with x | s <;> simp [Num.neg, WithSpecial.toReal]

theorem toReal_abs (u : WithSpecial Mpfx.Dyadic) :
    Num.abs u.toReal = (WithSpecial.abs u).toReal := by
  rcases u with x | (a | _) <;> simp [Num.abs, WithSpecial.abs, WithSpecial.toReal]

theorem reals_opAdd {F₁ F₂ : Format} {u v : Num} (hu : u ∈ F₁.reals) (hv : v ∈ F₂.reals) :
    Num.add u v ∈ (Format.opAdd F₁ F₂).reals := by
  obtain ⟨w₁, hw₁, rfl⟩ := hu
  obtain ⟨w₂, hw₂, rfl⟩ := hv
  exact ⟨w₁ + w₂, Format.add_subset F₁ F₂ ⟨w₁, hw₁, w₂, hw₂, rfl⟩, (toReal_add ..).symm⟩

theorem reals_opNeg {F : Format} {u : Num} (hu : u ∈ F.reals) :
    Num.neg u ∈ (Format.opNeg F).reals := by
  obtain ⟨w, hw, rfl⟩ := hu
  exact ⟨-w, Format.neg_subset F (by simpa using hw), (toReal_neg w).symm⟩

theorem reals_opAbs {F : Format} {u : Num} (hu : u ∈ F.reals) :
    Num.abs u ∈ (Format.opAbs F).reals := by
  obtain ⟨w, hw, rfl⟩ := hu
  exact ⟨WithSpecial.abs w, Format.abs_subset F ⟨w, hw, rfl⟩, (toReal_abs w).symm⟩

/-! ## Precision -/

/-- `F` with precision `p`. -/
def _root_.Mpfx.Format.withP (F : Format) (p : Prec) : Format := { F with p := p }

theorem reals_withP {F : Format} {p : Prec} (h : F.p ≤ p) {u : Num} (hu : u ∈ F.reals) :
    u ∈ (F.withP p).reals := by
  obtain ⟨w, hw, rfl⟩ := hu
  refine ⟨w, ?_, rfl⟩
  cases w with
  | finite d => exact ⟨Dyadic.precisionAtMost_mono h hw.1, hw.2.1, hw.2.2⟩
  | special s => exact hw

/-- `bits(b, exp)`, the precision the bound and the quantum alone allow; `⊤`
when either is infinite. -/
noncomputable def _root_.Mpfx.Format.bits (F : Format) : Prec :=
  match F.b, F.exp with
  | (b : NonNegDyadic), (e : ℤ) => (Format.bitsFor ((b.1 : Mpfx.Dyadic) : ℝ) e : Prec)
  | _, _ => ⊤

/-- `p̂ = min(p, bits(b, exp))`. -/
noncomputable def _root_.Mpfx.Format.pHat (F : Format) : Prec := min F.p F.bits

theorem precisionAtMost_pHat {F : Format} {d : Mpfx.Dyadic} (hd : d ∈ F) :
    Dyadic.precisionAtMost F.pHat d := by
  have hbits : Dyadic.precisionAtMost F.bits d := by
    unfold Format.bits
    obtain ⟨_, hq, hb⟩ := hd
    split
    · next b e hb' he' =>
      rw [he'] at hq
      rw [hb'] at hb
      refine Format.precisionAtMost_bitsFor hq ?_
      change |(d : ℚ)| ≤ ((b.1 : Mpfx.Dyadic) : ℚ) at hb
      exact_mod_cast hb
    · trivial
  unfold Format.pHat
  rcases min_choice F.p F.bits with h | h <;> rw [h]
  · exact hd.1
  · exact hbits

theorem precisionAtMost_mul_of_one {q : Prec} {x y : Mpfx.Dyadic}
    (hx : Dyadic.precisionAtMost ((1 : ℕ) : Prec) x) (hy : Dyadic.precisionAtMost q y) :
    Dyadic.precisionAtMost q (x * y) := by
  cases q using ENat.recTopCoe with
  | top => trivial
  | coe q =>
    obtain ⟨c₁, e₁, hx, hc₁⟩ := hx
    obtain ⟨c₂, e₂, hy, hc₂⟩ := hy
    refine ⟨c₁ * c₂, e₁ + e₂, ?_, ?_⟩
    · change ((x * y : Mpfx.Dyadic) : ℚ) = _
      push_cast
      rw [hx, hy, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
      ring
    · have : |c₁| ≤ 1 := by
        have : |c₁| < 2 := by simpa using hc₁
        omega
      rw [abs_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (abs_nonneg _) this) hc₂

/-- `q₁ ⊞ q₂`: a factor of precision `1` is a signed power of two, which does
not add digits. -/
noncomputable def precMul (q₁ q₂ : Prec) : Prec :=
  if q₁ = ((1 : ℕ) : Prec) ∨ q₂ = ((1 : ℕ) : Prec) then max q₁ q₂ else max 1 (q₁ + q₂)

theorem precisionAtMost_precMul {q₁ q₂ : Prec} {x y : Mpfx.Dyadic}
    (hx : Dyadic.precisionAtMost q₁ x) (hy : Dyadic.precisionAtMost q₂ y) :
    Dyadic.precisionAtMost (precMul q₁ q₂) (x * y) := by
  unfold precMul
  split
  · next h =>
    rcases h with rfl | rfl
    · exact Dyadic.precisionAtMost_mono le_sup_right (precisionAtMost_mul_of_one hx hy)
    · rw [mul_comm]
      exact Dyadic.precisionAtMost_mono le_sup_left (precisionAtMost_mul_of_one hy hx)
  · exact Dyadic.precisionAtMost_mono le_sup_right (Dyadic.precisionAtMost_mul hx hy)

/-! ## The rows on abstract formats -/

/-- `+`: `𝒜(max(1, bits(b₁ + b₂, e)), e, b₁ + b₂)` with `e = min(exp₁, exp₂)`. -/
noncomputable def addFmt (F₁ F₂ : Format) : Format :=
  (Format.opAdd F₁ F₂).withP (max 1 (Format.opAdd F₁ F₂).p)

theorem reals_addFmt {F₁ F₂ : Format} {u v : Num} (hu : u ∈ F₁.reals) (hv : v ∈ F₂.reals) :
    Num.add u v ∈ (addFmt F₁ F₂).reals :=
  reals_withP le_sup_right (reals_opAdd hu hv)

/-- `×`: `𝒜(p̂₁ ⊞ p̂₂, exp₁ + exp₂, b₁ b₂)`. -/
noncomputable def mulFmt (F₁ F₂ : Format) : Format :=
  (Format.opMul F₁ F₂).withP (precMul F₁.pHat F₂.pHat)

theorem reals_mulFmt {F₁ F₂ : Format} {u v : Num} (hu : u ∈ F₁.reals) (hv : v ∈ F₂.reals) :
    Num.mul u v ∈ (mulFmt F₁ F₂).reals := by
  obtain ⟨w₁, hw₁, rfl⟩ := hu
  obtain ⟨w₂, hw₂, rfl⟩ := hv
  refine ⟨w₁ * w₂, ?_, (toReal_mul ..).symm⟩
  have hm : w₁ * w₂ ∈ (Format.opMul F₁ F₂).values :=
    Format.mul_subset F₁ F₂ ⟨w₁, hw₁, w₂, hw₂, rfl⟩
  cases h : w₁ * w₂ with
  | finite z =>
    obtain ⟨x, y, rfl, rfl, rfl⟩ := WithSpecial.mul_eq_finite.mp h
    change x * y ∈ (Format.opMul F₁ F₂) at hm
    exact ⟨precisionAtMost_precMul (precisionAtMost_pHat hw₁) (precisionAtMost_pHat hw₂),
      hm.2.1, hm.2.2⟩
  | special s =>
    rw [h] at hm
    exact hm

/-- The specials `logb` produces from `F`: `−∞` from `0`, `+∞` from an infinity,
and NaN from NaN. -/
def logbSpecials (F : Format) : Set Special
  | .inf true => True
  | .inf false => ∃ a, .inf a ∈ F.specials
  | .nan => .nan ∈ F.specials

/-- `logb`: `𝒜(max(1, bits(b′, 0)), 0, b′)` with `b′ = max(|exp|, |⌊log₂ b⌋|)`,
when `exp > −∞` and `0 < b < ∞`; otherwise `R*`. -/
noncomputable def logbFmt (F : Format) : Fmt :=
  match F.exp, F.b with
  | (e : ℤ), (b : NonNegDyadic) =>
    if 0 < ((b.1 : Mpfx.Dyadic) : ℚ) then
      let b' : ℕ := max e.natAbs (Int.log 2 ((b.1 : Mpfx.Dyadic) : ℝ)).natAbs
      .abs
        { p := max 1 (Format.bitsFor b' 0 : Prec)
          exp := (0 : ℤ)
          b := (⟨Dyadic.ofIntZpow b' 0, by simp⟩ : NonNegDyadic)
          specials := logbSpecials F }
    else .top
  | _, _ => .top

theorem reals_logbFmt {F : Format} {u : Num} (hu : u ∈ F.reals) :
    Num.logb u ∈ (logbFmt F).γ := by
  unfold logbFmt
  split
  · next e b he hb =>
    split
    · next hbpos =>
      obtain ⟨w, hw, rfl⟩ := hu
      rcases w with d | (a | _)
      · simp only [WithSpecial.toReal_finite, Num.logb, Dyadic.coe_real_eq_zero]
        split
        · exact ⟨.special (.inf true), trivial, rfl⟩
        · next hd0 =>
          have hd0' : (d : ℝ) ≠ 0 := fun h => hd0 (eq_zero_of_coe_real_zero h)
          set k := Int.log 2 |(d : ℝ)|
          refine ⟨.finite (Dyadic.ofIntZpow k 0), ?_, by simp⟩
          obtain ⟨_, hq, hbd⟩ := hw
          rw [he] at hq
          rw [hb] at hbd
          change |(d : ℚ)| ≤ ((b.1 : Mpfx.Dyadic) : ℚ) at hbd
          have hbdR : |(d : ℝ)| ≤ ((b.1 : Mpfx.Dyadic) : ℝ) := by exact_mod_cast hbd
          have hlo : e ≤ k := Dyadic.le_log_of_quantum hq hd0'
          have hhi : k ≤ Int.log 2 ((b.1 : Mpfx.Dyadic) : ℝ) :=
            Int.log_mono_right (abs_pos.mpr hd0') hbdR
          set L := Int.log 2 ((b.1 : Mpfx.Dyadic) : ℝ)
          have hkZ : |k| ≤ ((max e.natAbs L.natAbs : ℕ) : ℤ) := by
            push_cast
            rw [abs_le]
            have h1 := neg_abs_le e
            have h2 := le_abs_self L
            have h3 := le_max_left |e| |L|
            have h4 := le_max_right |e| |L|
            constructor <;> linarith
          have hk : |(k : ℝ)| ≤ (((max e.natAbs L.natAbs : ℕ) : ℤ) : ℝ) := by
            rw [← Int.cast_abs]
            exact Int.cast_le.mpr hkZ
          refine ⟨Dyadic.precisionAtMost_mono le_sup_right
            (Format.precisionAtMost_bitsFor (Dyadic.quantumAtLeast_ofIntZpow le_rfl)
              (by simpa using hk)), Dyadic.quantumAtLeast_ofIntZpow le_rfl, ?_⟩
          change |((Dyadic.ofIntZpow k 0 : Mpfx.Dyadic) : ℚ)| ≤
            ((Dyadic.ofIntZpow _ 0 : Mpfx.Dyadic) : ℚ)
          simp only [Dyadic.coe_rat_ofIntZpow, zpow_zero, mul_one]
          rw [← Int.cast_abs]
          exact Int.cast_le.mpr hkZ
      · exact ⟨.special (.inf false), ⟨a, hw⟩, rfl⟩
      · exact ⟨.special .nan, hw, rfl⟩
    · trivial
  · trivial

/-- The specials `exp2` produces from `F`: `+∞` from `+∞`, and NaN from NaN.
`2^(−∞) = 0` is in every format. -/
def exp2Specials (F : Format) : Set Special
  | .inf true => False
  | .inf false => .inf false ∈ F.specials
  | .nan => .nan ∈ F.specials

/-- `exp2`: `𝒜(1, −⌊b⌋, 2^⌊b⌋)` when `exp ≥ 0` and `b < ∞`; otherwise `R*`. -/
noncomputable def exp2Fmt (F : Format) : Fmt :=
  match F.exp, F.b with
  | (e : ℤ), (b : NonNegDyadic) =>
    if 0 ≤ e then
      .abs
        { p := (1 : ℕ)
          exp := (-⌊((b.1 : Mpfx.Dyadic) : ℚ)⌋ : ℤ)
          b := (⟨Dyadic.ofIntZpow 1 ⌊((b.1 : Mpfx.Dyadic) : ℚ)⌋, by
            rw [Dyadic.coe_rat_ofIntZpow]; positivity⟩ : NonNegDyadic)
          specials := exp2Specials F }
    else .top
  | _, _ => .top

theorem reals_exp2Fmt {F : Format} {u : Num} (hu : u ∈ F.reals) :
    Num.exp2 u ∈ (exp2Fmt F).γ := by
  unfold exp2Fmt
  split
  · next e b he hb =>
    split
    · next he0 =>
      obtain ⟨w, hw, rfl⟩ := hu
      rcases w with d | (a | _)
      · obtain ⟨_, hq, hbd⟩ := hw
        rw [he] at hq
        rw [hb] at hbd
        change |(d : ℚ)| ≤ ((b.1 : Mpfx.Dyadic) : ℚ) at hbd
        obtain ⟨c, hc⟩ := (Dyadic.quantumAtLeast_coe e d).mp hq
        obtain ⟨k, hdk⟩ : ∃ k : ℤ, (d : ℚ) = k :=
          ⟨c * 2 ^ e.toNat, by rw [hc]; push_cast; rw [← zpow_natCast, Int.toNat_of_nonneg he0]⟩
        set B := ⌊((b.1 : Mpfx.Dyadic) : ℚ)⌋
        have hkB : |k| ≤ B := by
          refine Int.le_floor.mpr ?_
          rw [Int.cast_abs, ← hdk]
          exact hbd
        refine ⟨.finite (Dyadic.ofIntZpow 1 k), ⟨?_, ?_, ?_⟩, ?_⟩
        · exact ⟨1, k, by rw [Dyadic.coe_rat_ofIntZpow], by norm_num⟩
        · exact Dyadic.quantumAtLeast_ofIntZpow (WithBot.coe_le_coe.mpr (by
            have := neg_abs_le k
            omega))
        · change |((Dyadic.ofIntZpow 1 k : Mpfx.Dyadic) : ℚ)| ≤
            ((Dyadic.ofIntZpow 1 B : Mpfx.Dyadic) : ℚ)
          simp only [Dyadic.coe_rat_ofIntZpow, Int.cast_one, one_mul]
          rw [abs_of_pos (zpow_pos (by norm_num) _)]
          exact zpow_le_zpow_right₀ (by norm_num) ((le_abs_self k).trans hkB)
        · have hdR : (d : ℝ) = k := by
            rw [Dyadic.coe_real_eq_ratCast, hdk]
            push_cast
            rfl
          simp only [WithSpecial.toReal_finite, Num.exp2, hdR, Real.rpow_intCast,
            Dyadic.coe_ofIntZpow, Int.cast_one, one_mul]
      · rcases a with _ | _
        · exact ⟨.special (.inf false), hw, rfl⟩
        · exact ⟨.finite 0, Format.zero_mem _, by simp [Num.exp2]⟩
      · exact ⟨.special .nan, hw, rfl⟩
    · trivial
  · trivial

theorem Num.min_eq_or (u v : Num) : Num.min u v = u ∨ Num.min u v = v := by
  rcases u with x | (a | _) <;> rcases v with y | (b | _) <;>
    first
    | (simp [Num.min]; done)
    | exact (min_choice x y).imp (congrArg _) (congrArg _)
    | (cases a <;> cases b <;> simp [Num.min])
    | (cases a <;> simp [Num.min])
    | (cases b <;> simp [Num.min])

theorem Num.max_eq_or (u v : Num) : Num.max u v = u ∨ Num.max u v = v := by
  rcases u with x | (a | _) <;> rcases v with y | (b | _) <;>
    first
    | (simp [Num.max]; done)
    | exact (max_choice x y).imp (congrArg _) (congrArg _)
    | (cases a <;> cases b <;> simp [Num.max])
    | (cases a <;> simp [Num.max])
    | (cases b <;> simp [Num.max])

theorem reals_fmtJoin_of_eq_or {F₁ F₂ : Format} {u v n : Num} (hu : u ∈ F₁.reals)
    (hv : v ∈ F₂.reals) (h : n = u ∨ n = v) : n ∈ (fmtJoin F₁ F₂).reals := by
  rcases h with rfl | rfl
  · exact reals_fmtJoin_left hu F₂
  · exact reals_fmtJoin_right F₁ hv

/-! ## Lifting the rows to `Fmt` -/

section Lift

variable (c : Ceiling)

open Classical in
/-- A binary row: element-wise on two sets, the row `fa` on abstract formats,
`⌈S⌉` for a set meeting an abstract format, and `R*` otherwise. -/
noncomputable def lift2 (f : Num → Num → Num) (fa : Format → Format → Fmt) : Fmt → Fmt → Fmt
  | .set S₁, .set S₂ => .set (Finset.image₂ f S₁ S₂)
  | .set S, .abs F => (c.ceil S).elim .top (fa · F)
  | .abs F, .set S => (c.ceil S).elim .top (fa F ·)
  | .abs F₁, .abs F₂ => fa F₁ F₂
  | _, _ => .top

open Classical in
/-- A unary row that acts element-wise on a set. -/
noncomputable def lift1 (f : Num → Num) (fa : Format → Fmt) : Fmt → Fmt
  | .set S => .set (S.image f)
  | .abs F => fa F
  | .top => .top

/-- A unary row that replaces a set by `⌈S⌉`. -/
noncomputable def liftCeil (fa : Format → Fmt) : Fmt → Fmt
  | .set S => (c.ceil S).elim .top fa
  | .abs F => fa F
  | .top => .top

variable {c}

theorem mem_lift2 {f : Num → Num → Num} {fa : Format → Format → Fmt}
    (ha : ∀ {F₁ F₂ u v}, u ∈ F₁.reals → v ∈ F₂.reals → f u v ∈ (fa F₁ F₂).γ)
    {F₁ F₂ : Fmt} {u v : Num} (hu : u ∈ F₁.γ) (hv : v ∈ F₂.γ) :
    f u v ∈ (lift2 c f fa F₁ F₂).γ := by
  classical
  cases F₁ <;> cases F₂ <;> simp only [lift2]
  all_goals first
    | trivial
    | exact Finset.mem_image₂_of_mem hu hv
    | exact ha hu hv
    | (cases hc : c.ceil _ with
        | none => trivial
        | some F' =>
          first
          | exact ha (c.sound hc u hu) hv
          | exact ha hu (c.sound hc v hv))

theorem mem_lift1 {f : Num → Num} {fa : Format → Fmt}
    (ha : ∀ {F u}, u ∈ F.reals → f u ∈ (fa F).γ) {F : Fmt} {u : Num} (hu : u ∈ F.γ) :
    f u ∈ (lift1 f fa F).γ := by
  classical
  cases F with
  | set S => exact Finset.mem_image_of_mem f hu
  | abs F => exact ha hu
  | top => trivial

theorem mem_liftCeil {f : Num → Num} {fa : Format → Fmt}
    (ha : ∀ {F u}, u ∈ F.reals → f u ∈ (fa F).γ) {F : Fmt} {u : Num} (hu : u ∈ F.γ) :
    f u ∈ (liftCeil c fa F).γ := by
  cases F with
  | set S =>
    simp only [liftCeil]
    cases hc : c.ceil S with
    | none => trivial
    | some F' => exact ha (c.sound hc u hu)
  | abs F => exact ha hu
  | top => trivial

end Lift

/-! ## `op♯` -/

/-- `op♯` for the rounded operators of Table 1. `÷`, `√` and `fma` are `R*`. -/
noncomputable def ArithOp.fmt (c : Ceiling) : ArithOp → List Fmt → Fmt
  | .add, [F₁, F₂] => lift2 c Num.add (fun F₁ F₂ => .abs (addFmt F₁ F₂)) F₁ F₂
  | .sub, [F₁, F₂] =>
      lift2 c Num.sub (fun F₁ F₂ => .abs (addFmt F₁ (Format.opNeg F₂))) F₁ F₂
  | .mul, [F₁, F₂] => lift2 c Num.mul (fun F₁ F₂ => .abs (mulFmt F₁ F₂)) F₁ F₂
  | .neg, [F] => lift1 Num.neg (fun F => .abs (Format.opNeg F)) F
  | .abs, [F] => lift1 Num.abs (fun F => .abs (Format.opAbs F)) F
  | .logb, [F] => liftCeil c logbFmt F
  | .exp2, [F] => liftCeil c exp2Fmt F
  | .min, [F₁, F₂] => lift2 c Num.min (fun F₁ F₂ => .abs (fmtJoin F₁ F₂)) F₁ F₂
  | .max, [F₁, F₂] => lift2 c Num.max (fun F₁ F₂ => .abs (fmtJoin F₁ F₂)) F₁ F₂
  | .round, [F] | .cast, [F] => F
  | _, _ => .top

/-- Each `op♯` bounds its operator's exact result. -/
theorem ArithOp.fmt_sound (c : Ceiling) {op : ArithOp} {ns : List Num} {Fs : List Fmt}
    {n : Num} (h : List.Forall₂ (fun n F => n ∈ F.γ) ns Fs) (hop : op.eval ns = some n) :
    n ∈ (op.fmt c Fs).γ := by
  rcases h with _ | ⟨hu, _ | ⟨hv, _ | ⟨hw, h⟩⟩⟩
  · cases op <;> simp [ArithOp.eval] at hop
  · cases op <;> simp only [ArithOp.eval, Option.some.injEq, reduceCtorEq] at hop <;> subst hop
    all_goals first
      | trivial
      | exact hu
      | exact mem_lift1 (f := Num.neg) (fa := fun F => .abs (Format.opNeg F))
          (fun hu => reals_opNeg hu) hu
      | exact mem_lift1 (f := Num.abs) (fa := fun F => .abs (Format.opAbs F))
          (fun hu => reals_opAbs hu) hu
      | exact mem_liftCeil (f := Num.logb) (fun hu => reals_logbFmt hu) hu
      | exact mem_liftCeil (f := Num.exp2) (fun hu => reals_exp2Fmt hu) hu
  · cases op <;> simp only [ArithOp.eval, Option.some.injEq, reduceCtorEq] at hop <;> subst hop
    all_goals first
      | trivial
      | exact mem_lift2 (f := Num.add) (fa := fun F₁ F₂ => .abs (addFmt F₁ F₂))
          (fun hu hv => reals_addFmt hu hv) hu hv
      | exact mem_lift2 (f := Num.sub) (fa := fun F₁ F₂ => .abs (addFmt F₁ (Format.opNeg F₂)))
          (fun hu hv => reals_addFmt hu (reals_opNeg hv)) hu hv
      | exact mem_lift2 (f := Num.mul) (fa := fun F₁ F₂ => .abs (mulFmt F₁ F₂))
          (fun hu hv => reals_mulFmt hu hv) hu hv
      | exact mem_lift2 (f := Num.min) (fa := fun F₁ F₂ => .abs (fmtJoin F₁ F₂))
          (fun hu hv => reals_fmtJoin_of_eq_or hu hv (Num.min_eq_or _ _)) hu hv
      | exact mem_lift2 (f := Num.max) (fa := fun F₁ F₂ => .abs (fmtJoin F₁ F₂))
          (fun hu hv => reals_fmtJoin_of_eq_or hu hv (Num.max_eq_or _ _)) hu hv
  · cases h with
    | nil =>
      cases op <;> simp only [ArithOp.eval, Option.some.injEq, reduceCtorEq] at hop
      subst hop
      trivial
    | cons _ _ => cases op <;> simp [ArithOp.eval] at hop

/-! ## `exact♯` -/

/-- The integers, `𝒜(∞, 0, ∞)`. -/
def intFormat : Format := { p := ⊤, exp := (0 : ℤ), b := ⊤, specials := ∅ }

theorem mem_intFormat (n : ℕ) : (.finite (n : ℝ) : Num) ∈ intFormat.reals :=
  ⟨.finite (Dyadic.ofIntZpow n 0), ⟨trivial, Dyadic.quantumAtLeast_ofIntZpow le_rfl, trivial⟩,
    by simp⟩

/-- `exact♯`: a list length is an integer; every other unrounded operator gives
a boolean. -/
def ExactOp.aval (c : Ceiling) : ExactOp → List (AVal (Fmt.domain c)) → AVal (Fmt.domain c)
  | .len, _ => .fmt (.abs intFormat)
  | _, _ => .other

theorem ExactOp.aval_sound (c : Ceiling) {op : ExactOp} {as : List (AVal (Fmt.domain c))}
    {vs : List Val} {v : Val} (hop : op.eval vs = some v) : Describes (op.aval c as) v := by
  unfold ExactOp.eval at hop
  split at hop <;> simp only [Option.some.injEq, reduceCtorEq] at hop <;> subst hop
  all_goals first
    | exact .bool
    | exact .fmt (mem_intFormat _)

end Fpy
