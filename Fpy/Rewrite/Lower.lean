import Fpy.Rewrite.Separate
import Mpfx.Rounding.Monotone
import Mpfx.Rounding.Parity

/-!
# Lowering a rounding (§5.2)

The rewrites of §5.2 on `x = round(t)` under a context `C`:

* **Special** branches on NaN, the infinities and zero before rounding;
* **Overflow** rounds into `C`'s format without its bound, then replaces a
  result beyond the bound by `C`'s overflow value, or tests `t` against a
  threshold;
* **FloatToFixed** rounds at the fixed position `max(logb(t) − p + 1, exp)`;
* **Rescale** rounds `2⁻ᵏt` to an integer and scales back.

Each is an `Equiv` (`equiv_special`, `equiv_overflow`,
`equiv_overflow_threshold`, `equiv_floatToFixed`, `equiv_rescale`). The draft's
Overflow compares `|r|` under `C`, which rounds it; here the comparisons are
exact. Its `copysign(·, t)` is a branch on the sign, since a context's maps need
not be symmetric.

FloatToFixed and Rescale rest on two rounding identities,
`rndUnbounded_eq_fixed` and `rndUnbounded_scale`: the integer step depends on
the format only through the parity of the floor point (`rndInt_congr`), which
for `p ≠ 1` is the parity of its significand.
-/

namespace Fpy

open Mpfx

/-! ## Rounding identities -/

/-- The integer step agrees on two inputs with the same scaled mantissa and
sign, when the formats agree on the parity of the floor point off the grid. -/
theorem rndInt_congr {F G : FiniteFormat} {rm : RoundingMode} {x x' : ℝ} {e e' : ℤ}
    (hs : x' * (2 : ℝ) ^ (-e') = x * (2 : ℝ) ^ (-e)) (hx : 0 ≤ x' ↔ 0 ≤ x)
    (hodd : (⌊x * (2 : ℝ) ^ (-e)⌋ : ℝ) ≠ x * (2 : ℝ) ^ (-e) →
      (G.IsOdd (Mpfx.Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-e)⌋ e') ↔
        F.IsOdd (Mpfx.Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-e)⌋ e)))
    (heven : (⌊x * (2 : ℝ) ^ (-e)⌋ : ℝ) ≠ x * (2 : ℝ) ^ (-e) →
      (G.IsEven (Mpfx.Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-e)⌋ e') ↔
        F.IsEven (Mpfx.Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-e)⌋ e))) :
    rndInt G rm x' e' = rndInt F rm x e := by
  unfold rndInt
  rw [hs]
  set s := x * (2 : ℝ) ^ (-e)
  cases rm with
  | toNegative | toPositive => rfl
  | toZero | awayZero =>
    dsimp only
    by_cases h : 0 ≤ x
    · rw [if_pos h, if_pos (hx.mpr h)]
    · rw [if_neg h, if_neg (mt hx.mp h)]
  | toOdd =>
    dsimp only
    by_cases h : (⌊s⌋ : ℝ) = s
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
      by_cases ho : F.IsOdd (Mpfx.Dyadic.ofIntZpow ⌊s⌋ e)
      · rw [if_pos ho, if_pos ((hodd h).mpr ho)]
      · rw [if_neg ho, if_neg (mt (hodd h).mp ho)]
  | nearest tb =>
    cases tb with
    | awayZero =>
      dsimp only
      by_cases h : 0 ≤ x
      · simp only [h, hx.mpr h, if_true]
      · simp only [h, mt hx.mp h, if_false]
    | toEven =>
      dsimp only
      by_cases h₁ : s - ⌊s⌋ < 1 / 2
      · rw [if_pos h₁, if_pos h₁]
      · rw [if_neg h₁, if_neg h₁]
        have hne : (⌊s⌋ : ℝ) ≠ s := fun h' => h₁ (by rw [h']; norm_num)
        by_cases he : F.IsEven (Mpfx.Dyadic.ofIntZpow ⌊s⌋ e)
        · rw [if_pos ((heven hne).mpr he), if_pos he]
        · rw [if_neg (mt (heven hne).mp he), if_neg he]

theorem p_ne_one_of_top {F : FiniteFormat} (h : F.p = ⊤) : F.p ≠ ((1 : ℕ) : Prec) := by
  rw [h]; exact WithTop.top_ne_coe

/-- For `p ≠ 1`, rounding into `F` is rounding into a fixed-point format whose
quantum is `x`'s canonical exponent in `F`. -/
theorem rndUnbounded_eq_fixed {F G : FiniteFormat} {rm : RoundingMode}
    (hp1 : F.p ≠ ((1 : ℕ) : Prec)) {x : ℝ} (hGp : G.p = ⊤)
    (hGe : G.exp = ((F.canonicalExp x : ℤ) : QExp)) (hF : ¬ F.IsUndefined rm)
    (hG : ¬ G.IsUndefined rm) : rndUnbounded G rm x hG = rndUnbounded F rm x hF := by
  have he : G.canonicalExp x = F.canonicalExp x := canonicalExp_pTop hGp hGe x
  unfold rndUnbounded
  rw [he]
  congr 1
  refine rndInt_congr rfl Iff.rfl (fun h => ?_) (fun h => ?_)
  · have hG' := isOdd_neighbor_iff (p_ne_one_of_top hGp) (x := x) (by rwa [he])
      (Or.inl (by rw [he]))
    rw [he] at hG'
    rw [hG', isOdd_neighbor_iff hp1 h (Or.inl rfl)]
  · have hG' := isEven_neighbor_iff (p_ne_one_of_top hGp) (x := x) (by rwa [he])
      (Or.inl (by rw [he]))
    rw [he] at hG'
    rw [hG', isEven_neighbor_iff hp1 h (Or.inl rfl)]

/-- Rounding into `𝒜(∞, k)` is `2ᵏ` times rounding `2⁻ᵏx` into `𝒜(∞, 0)`. -/
theorem rndUnbounded_scale {F G : FiniteFormat} {rm : RoundingMode} {k : ℤ}
    (hFp : F.p = ⊤) (hFe : F.exp = (k : QExp)) (hGp : G.p = ⊤) (hGe : G.exp = ((0 : ℤ) : QExp))
    (x : ℝ) (hF : ¬ F.IsUndefined rm) (hG : ¬ G.IsUndefined rm) :
    ((rndUnbounded F rm x hF : Mpfx.Dyadic) : ℝ) =
      2 ^ k * (rndUnbounded G rm (2 ^ (-k) * x) hG : Mpfx.Dyadic) := by
  have heF : F.canonicalExp x = k := canonicalExp_pTop hFp hFe x
  have heG : G.canonicalExp (2 ^ (-k) * x) = 0 := canonicalExp_pTop hGp hGe _
  have hs : 2 ^ (-k) * x * (2 : ℝ) ^ (-(0 : ℤ)) = x * 2 ^ (-k) := by simp [mul_comm]
  have hint : rndInt G rm (2 ^ (-k) * x) 0 = rndInt F rm x k := by
    refine rndInt_congr hs (mul_nonneg_iff_of_pos_left (zpow_pos two_pos _))
      (fun h => ?_) (fun h => ?_)
    · have hG' := isOdd_neighbor_iff (p_ne_one_of_top hGp) (x := 2 ^ (-k) * x)
        (by rwa [heG, hs]) (Or.inl (by rw [heG, hs]))
      have hF' := isOdd_neighbor_iff (p_ne_one_of_top hFp) (x := x) (by rwa [heF])
        (Or.inl (by rw [heF]))
      rw [heG] at hG'
      rw [heF] at hF'
      rw [hG', hF']
    · have hG' := isEven_neighbor_iff (p_ne_one_of_top hGp) (x := 2 ^ (-k) * x)
        (by rwa [heG, hs]) (Or.inl (by rw [heG, hs]))
      have hF' := isEven_neighbor_iff (p_ne_one_of_top hFp) (x := x) (by rwa [heF])
        (Or.inl (by rw [heF]))
      rw [heG] at hG'
      rw [heF] at hF'
      rw [hG', hF']
  unfold rndUnbounded
  rw [heF, heG, hint, Mpfx.Dyadic.coe_ofIntZpow, Mpfx.Dyadic.coe_ofIntZpow]
  ring

/-- A value between two in-bound values is in bound. -/
theorem boundOK_of_between {b : Bound} {lo z hi : Mpfx.Dyadic} (hlo : Format.boundOK b lo)
    (hhi : Format.boundOK b hi) (h₁ : (lo : ℝ) ≤ z) (h₂ : (z : ℝ) ≤ hi) : Format.boundOK b z := by
  cases b using WithTop.recTopCoe with
  | top => trivial
  | coe b =>
    change |(lo : ℚ)| ≤ _ at hlo
    change |(hi : ℚ)| ≤ _ at hhi
    change |(z : ℚ)| ≤ _
    rw [Mpfx.Dyadic.coe_real_eq_ratCast, Mpfx.Dyadic.coe_real_eq_ratCast, Rat.cast_le] at h₁ h₂
    obtain ⟨hlo, -⟩ := abs_le.mp hlo
    obtain ⟨-, hhi⟩ := abs_le.mp hhi
    exact abs_le.mpr ⟨hlo.trans h₁, h₂.trans hhi⟩

/-- Overflow's threshold condition, by monotonicity: if `±θ` round in bound and
every input beyond them rounds out of bound, `F` overflows exactly beyond `±θ`. -/
theorem overflows_iff_of_threshold {F : FiniteFormat} {rm : RoundingMode}
    (h : ¬ F.IsUndefined rm) {θ : ℝ} (hlo : Format.boundOK F.b (rndUnbounded F rm (-θ) h))
    (hhi : Format.boundOK F.b (rndUnbounded F rm θ h))
    (hout : ∀ y, y < -θ ∨ θ < y → ¬ Format.boundOK F.b (rndUnbounded F rm y h)) (y : ℝ) :
    Overflows F rm y ↔ y < -θ ∨ θ < y := by
  refine ⟨fun ⟨z, hz, hnb⟩ => ?_, fun hy => ⟨_, rndUnbounded_satisfies F rm y h, hout y hy⟩⟩
  rw [RoundsFinite.unique h hz (rndUnbounded_satisfies F rm y h)] at hnb
  by_contra hy
  push Not at hy
  exact hnb (boundOK_of_between hlo hhi
    (RoundsFinite.mono h hy.1 (rndUnbounded_satisfies _ _ _ _) (rndUnbounded_satisfies _ _ _ _))
    (RoundsFinite.mono h hy.2 (rndUnbounded_satisfies _ _ _ _) (rndUnbounded_satisfies _ _ _ _)))

/-! ## Roundings of FPy's contexts -/

theorem boundOK_top (d : Mpfx.Dyadic) : Format.boundOK ⊤ d := trivial

namespace RoundCtx

theorem round_of_overflows (c : RoundCtx) {y : ℝ} (h : Overflows c.F c.rm y) :
    c.round (.finite y) = (c.O.map (decide (y < 0))).toReal := by
  simp only [RoundCtx.round, rnd_of_overflows c.defined h]

/-- A context into `F` without its bound rounds without overflow. -/
theorem round_unbounded {c c' : RoundCtx} (hF : c'.F = c.F.unbounded) (hrm : c'.rm = c.rm)
    (y : ℝ) :
    c'.round (.finite y) = .finite ((rndUnbounded c.F c.rm y c.defined : Mpfx.Dyadic) : ℝ) := by
  obtain ⟨F', S', O', rm', h'⟩ := c'
  simp only at hF hrm
  subst hF hrm
  rw [round_finite]
  dsimp only
  rw [FiniteFormat.unbounded_b, if_pos (boundOK_top _)]
  rfl

/-- FloatToFixed on contexts: `c'` rounds into the fixed-point format at `y`'s
canonical exponent in `c`'s format, with `c`'s mode. -/
theorem round_fixed {c c' : RoundCtx} (hp1 : c.F.p ≠ ((1 : ℕ) : Prec)) (hb : c.F.b = ⊤)
    (hp' : c'.F.p = ⊤) (hb' : c'.F.b = ⊤) (hrm : c'.rm = c.rm) {y : ℝ}
    (he : c'.F.exp = ((c.F.canonicalExp y : ℤ) : QExp)) :
    c'.round (.finite y) = c.round (.finite y) := by
  obtain ⟨F', S', O', rm', h'⟩ := c'
  simp only at hp' hb' hrm he
  subst hrm
  rw [round_finite, round_finite]
  dsimp only
  rw [hb, hb', if_pos (boundOK_top _), if_pos (boundOK_top _),
    rndUnbounded_eq_fixed hp1 hp' he c.defined h']

/-- `c₀` is `c` scaled by `2⁻ᵏ`: `c` rounds into `𝒜(∞, k, b)` and `c₀` into
`𝒜(∞, 0, 2⁻ᵏb)` with the same mode, and `c`'s special and overflow values are
`2ᵏ` times `c₀`'s. -/
structure Scaled (c c₀ : RoundCtx) (k : ℤ) : Prop where
  p : c.F.p = ⊤
  exp : c.F.exp = (k : QExp)
  p₀ : c₀.F.p = ⊤
  exp₀ : c₀.F.exp = ((0 : ℤ) : QExp)
  rm : c₀.rm = c.rm
  bound : ∀ y y₀ : Mpfx.Dyadic, (y : ℝ) = 2 ^ k * y₀ →
    (Format.boundOK c.F.b y ↔ Format.boundOK c₀.F.b y₀)
  special : ∀ s, (c.S.map s).toReal = Num.mul (.finite (2 ^ k)) (c₀.S.map s).toReal
  overflow : ∀ neg, (c.O.map neg).toReal = Num.mul (.finite (2 ^ k)) (c₀.O.map neg).toReal

/-- Rescale on contexts. -/
theorem round_scale {c c₀ : RoundCtx} {k : ℤ} (h : c.Scaled c₀ k) (v : Num) :
    c.round v = Num.mul (.finite (2 ^ k)) (c₀.round (Num.mul (.finite (2 ^ (-k))) v)) := by
  obtain ⟨F₀, S₀, O₀, rm₀, h₀⟩ := c₀
  have hrm : rm₀ = c.rm := h.rm
  subst hrm
  have h2 : (2 : ℝ) ^ (-k) ≠ 0 := zpow_ne_zero _ two_ne_zero
  have h2' : ¬ (2 : ℝ) ^ (-k) < 0 := not_lt.mpr (zpow_pos two_pos _).le
  rcases v with y | (neg | _)
  · have hy := rndUnbounded_scale h.p h.exp h.p₀ h.exp₀ y c.defined h₀
    have hm : Num.mul (.finite (2 ^ (-k))) (.finite y) = .finite (2 ^ (-k) * y) := rfl
    rw [hm, round_finite, round_finite]
    set yU := rndUnbounded c.F c.rm y c.defined
    set y₀ := rndUnbounded F₀ c.rm (2 ^ (-k) * y) h₀
    by_cases hbd : Format.boundOK c.F.b yU
    · rw [if_pos hbd, if_pos ((h.bound _ _ hy).mp hbd)]
      simp only [Num.mul, hy]
    · rw [if_neg hbd, if_neg (mt (h.bound _ _ hy).mpr hbd), h.overflow]
      congr 4
      rw [← Mpfx.Dyadic.coe_real_lt_zero_iff, ← Mpfx.Dyadic.coe_real_lt_zero_iff, hy]
      have h2k : (0 : ℝ) < 2 ^ k := zpow_pos two_pos k
      refine propext ⟨fun h' => ?_, fun h' => mul_neg_of_pos_of_neg h2k h'⟩
      by_contra h''
      exact absurd h' (not_lt.mpr (mul_nonneg h2k.le (not_lt.mp h'')))
  · simp only [Num.mul, h2, h2', decide_false, Bool.xor_false, if_false, round_special]
    exact h.special _
  · exact h.special _

end RoundCtx

/-! ## Inversion -/

section Inversion

variable {L : Signature} {Φ : Program L} {σ : Store} {C : Val}

theorem eval_var_inv {x : Var} {v : Val} (h : Eval Φ σ C (.var x) v) : σ x = some v := by
  cases h with | var h => exact h

theorem EvalList.num_of_mem : ∀ {es : List (Expr L)} {ns : List Num},
    EvalList Φ σ C es (ns.map .num) → ∀ e ∈ es, ∃ u, Eval Φ σ C e (.num u) := by
  intro es
  induction es with
  | nil => intro _ _ e he; exact absurd he List.not_mem_nil
  | cons e es ih =>
    intro ns h e' he
    rcases ns with _ | ⟨u, ns⟩
    · cases h
    · cases h with
      | cons h₁ hs =>
        rcases List.mem_cons.mp he with rfl | he
        · exact ⟨u, h₁⟩
        · exact ih hs e' he

/-- An argument of a rounded operator evaluates to a number. -/
theorem Eval.num_of_arith {op : L.ArithOp} {es : List (Expr L)} {v : Val} {e : Expr L}
    (h : Eval Φ σ C (.arith op es) v) (he : e ∈ es) : ∃ u, Eval Φ σ C e (.num u) := by
  cases h with | arith hl _ _ => exact hl.num_of_mem e he

theorem Exec.seq_left {s₁ s₂ : Stmt L} {o : Outcome} (h : Exec Φ σ C (.seq s₁ s₂) o) :
    ∃ o₁, Exec Φ σ C s₁ o₁ := by
  cases h with
  | seqNormal h₁ _ => exact ⟨_, h₁⟩
  | seqRet h₁ => exact ⟨_, h₁⟩

theorem Exec.ite_guard {e : Expr L} {s₁ s₂ : Stmt L} {o : Outcome}
    (h : Exec Φ σ C (.ite e s₁ s₂) o) : ∃ b, Eval Φ σ C e (.bool b) := by
  cases h with
  | iteTrue he _ => exact ⟨_, he⟩
  | iteFalse he _ => exact ⟨_, he⟩

theorem Exec.ite_dec {e : Expr L} {s₁ s₂ : Stmt L} {o : Outcome} {b : Prop} [Decidable b]
    (he : Eval Φ σ C e (.bool (decide b))) (h₁ : b → Exec Φ σ C s₁ o)
    (h₂ : ¬ b → Exec Φ σ C s₂ o) : Exec Φ σ C (.ite e s₁ s₂) o := by
  by_cases hb : b
  · exact .iteTrue (by rwa [decide_eq_true hb] at he) (h₁ hb)
  · exact .iteFalse (by rwa [decide_eq_false hb] at he) (h₂ hb)

theorem Exec.withCtx_assign {e e' : Expr L} {y : Var} {o : Outcome}
    (h : Exec Φ σ C (.withCtx e (.assign y e')) o) : ∃ C' v, Eval Φ σ C' e' v := by
  cases h with | withCtx _ h => cases h with | assign he => exact ⟨_, _, he⟩

end Inversion

/-! ## The rewrites -/

variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {Γ : AEnv D} {X : Set Var}

/-- `op(e⃗)` with a rounded FPy operator. -/
abbrev Expr.arithOp (op : ArithOp) (es : List (Expr (fpy decode))) : Expr (fpy decode) :=
  .arith op es

/-- `op(e⃗)` with an unrounded FPy operator. -/
abbrev Expr.exactOp (op : ExactOp) (es : List (Expr (fpy decode))) : Expr (fpy decode) :=
  .exact op es

theorem exec_round {σ : Store} {C : Val} {r : Num → Num} {x t : Var} {u : Num}
    (hr : C.rnd (fpy decode) = some r) (ht : σ t = some (.num u)) :
    Exec Φ σ C (.assign x (.arithOp .round [.var t])) (.normal (σ.update x (.num (r u)))) :=
  .assign (.arith (ns := [u]) (.cons (.var ht) .nil) rfl hr)

theorem exec_round_inv {σ : Store} {C : Val} {r : Num → Num} {x t : Var} {o : Outcome}
    (hr : C.rnd (fpy decode) = some r) (h : Exec Φ σ C (.assign x (.arithOp .round [.var t])) o) :
    ∃ u, σ t = some (.num u) ∧ o = .normal (σ.update x (.num (r u))) := by
  obtain ⟨u, ht⟩ : ∃ u, σ t = some (.num u) := by
    cases h with
    | assign he =>
      obtain ⟨u, hu⟩ := he.num_of_arith (List.mem_singleton_self _)
      exact ⟨u, eval_var_inv hu⟩
  exact ⟨u, ht, Exec.det _ h (exec_round hr ht)⟩

theorem eval_lt {σ : Store} {C : Val} {e₁ e₂ : Expr (fpy decode)} {a b : ℝ}
    (h₁ : Eval Φ σ C e₁ (.num (.finite a))) (h₂ : Eval Φ σ C e₂ (.num (.finite b))) :
    Eval Φ σ C (.exactOp .lt [e₁, e₂]) (.bool (decide (a < b))) :=
  .exact (.cons h₁ (.cons h₂ .nil)) rfl

theorem eval_eq {σ : Store} {C : Val} {e₁ e₂ : Expr (fpy decode)} {a b : ℝ}
    (h₁ : Eval Φ σ C e₁ (.num (.finite a))) (h₂ : Eval Φ σ C e₂ (.num (.finite b))) :
    Eval Φ σ C (.exactOp .eq [e₁, e₂]) (.bool (decide (a = b))) :=
  .exact (.cons h₁ (.cons h₂ .nil)) rfl

theorem num_of_unary {σ : Store} {C : Val} {t : Var} {v : Val} {op : ExactOp}
    (hop : op = .isNaN ∨ op = .isInf) (h : Eval Φ σ C (.exactOp op [.var t]) v) :
    ∃ u, σ t = some (.num u) := by
  obtain ⟨w, hx, hev⟩ : ∃ w, σ t = some w ∧ ExactOp.eval op [w] = some v := by
    cases h with
    | exact hl hev => cases hl with
      | cons hv hl => cases hl; cases hv with | var hx => exact ⟨_, hx, hev⟩
  rcases hop with rfl | rfl <;> rcases w with _ | u | _ | _ | _ | _ <;>
    first | exact ⟨u, hx⟩ | cases hev

theorem num_of_binary {σ : Store} {C : Val} {t : Var} {c : Num} {v : Val} {op : ExactOp}
    (hop : op = .lt ∨ op = .eq) (h : Eval Φ σ C (.exactOp op [.var t, .num c]) v) :
    ∃ u, σ t = some (.num u) := by
  obtain ⟨w, hx, hev⟩ : ∃ w, σ t = some w ∧ ExactOp.eval op [w, .num c] = some v := by
    cases h with
    | exact hl hev => cases hl with
      | cons hv hl => cases hl with
        | cons hc hl => cases hl; cases hc; cases hv with | var hx => exact ⟨_, hx, hev⟩
  rcases hop with rfl | rfl <;> rcases w with _ | u | _ | _ | _ | _ <;>
    first | exact ⟨u, hx⟩ | cases hev

/-! ### Special -/

/-- Special's NaN branch, if kept: `if isnan(t) then x = C(NaN) else s`. -/
def nanBranch (r : Num → Num) (kn : Bool) (x t : Var) (s : Stmt (fpy decode)) :
    Stmt (fpy decode) :=
  bif kn then .ite (.exactOp .isNaN [.var t]) (.assign x (.num (r (.special .nan)))) s else s

/-- Special's infinity branch, if kept:
`if isinf(t) then (if t < 0 then x = C(−∞) else x = C(+∞)) else s`. -/
def infBranch (r : Num → Num) (ki : Bool) (x t : Var) (s : Stmt (fpy decode)) :
    Stmt (fpy decode) :=
  bif ki then
    .ite (.exactOp .isInf [.var t])
      (.ite (.exactOp .lt [.var t, .num (.finite 0)])
        (.assign x (.num (r (.special (.inf true)))))
        (.assign x (.num (r (.special (.inf false)))))) s
  else s

/-- Special's zero branch, if kept: `if t = 0 then x = t else s`. -/
def zeroBranch (kz : Bool) (x t : Var) (s : Stmt (fpy decode)) : Stmt (fpy decode) :=
  bif kz then .ite (.exactOp .eq [.var t, .num (.finite 0)]) (.assign x (.var t)) s else s

theorem exec_zeroBranch {σ : Store} {C : Val} {r : Num → Num} {x t : Var} {u : Num}
    (hr : C.rnd (fpy decode) = some r) (h0 : r (.finite 0) = .finite 0)
    (ht : σ t = some (.num u)) (kz : Bool) :
    Exec Φ σ C (zeroBranch kz x t (.assign x (.arithOp .round [.var t])))
      (.normal (σ.update x (.num (r u)))) := by
  cases kz
  · exact exec_round hr ht
  · have he : Eval Φ σ C (.exactOp .eq [.var t, .num (.finite 0)])
        (.bool (Num.eq u (.finite 0))) := .exact (.cons (.var ht) (.cons .num .nil)) rfl
    cases hb : Num.eq u (.finite 0)
    · exact .iteFalse (hb ▸ he) (exec_round hr ht)
    · obtain rfl : u = .finite 0 := by rcases u with y | (_ | _) <;> simp_all [Num.eq]
      rw [h0]
      exact .iteTrue (hb ▸ he) (.assign (.var ht))

theorem exec_infBranch {σ : Store} {C : Val} {r : Num → Num} {x t : Var} {u : Num}
    {s : Stmt (fpy decode)} (ht : σ t = some (.num u))
    (hs : Exec Φ σ C s (.normal (σ.update x (.num (r u))))) (ki : Bool) :
    Exec Φ σ C (infBranch r ki x t s) (.normal (σ.update x (.num (r u)))) := by
  cases ki
  · exact hs
  · rcases u with y | (neg | _)
    · exact .iteFalse (.exact (.cons (.var ht) .nil) rfl) hs
    · refine .iteTrue (.exact (.cons (.var ht) .nil) rfl) ?_
      cases neg
      · exact .iteFalse (.exact (.cons (.var ht) (.cons .num .nil)) rfl) (.assign .num)
      · exact .iteTrue (.exact (.cons (.var ht) (.cons .num .nil)) rfl) (.assign .num)
    · exact .iteFalse (.exact (.cons (.var ht) .nil) rfl) hs

theorem exec_nanBranch {σ : Store} {C : Val} {r : Num → Num} {x t : Var} {u : Num}
    {s : Stmt (fpy decode)} (ht : σ t = some (.num u))
    (hs : Exec Φ σ C s (.normal (σ.update x (.num (r u))))) (kn : Bool) :
    Exec Φ σ C (nanBranch r kn x t s) (.normal (σ.update x (.num (r u)))) := by
  cases kn
  · exact hs
  · rcases u with y | (_ | _)
    · exact .iteFalse (.exact (.cons (.var ht) .nil) rfl) hs
    · exact .iteFalse (.exact (.cons (.var ht) .nil) rfl) hs
    · exact .iteTrue (.exact (.cons (.var ht) .nil) rfl) (.assign .num)

/-- **Special**: `[C] x = round(t) ⇝ if isnan(t) then x = C(NaN) else if isinf(t) then
(if t < 0 then x = C(−∞) else x = C(+∞)) else if t = 0 then x = t else x = round(t)`, for a
context whose rounding function `r` fixes `0` (every Mpfx context, `RoundCtx.round_zero`).
Any branch may be omitted (`kn`, `ki`, `kz` false): a branch computes what `round(t)` would,
so omitting one needs no condition. -/
theorem equiv_special {C : Val} {r : Num → Num} {x t : Var}
    (hr : C.rnd (fpy decode) = some r) (h0 : r (.finite 0) = .finite 0) (kn ki kz : Bool) :
    Equiv Φ X Γ (some C) (.assign x (.arithOp .round [.var t]))
      (nanBranch r kn x t (infBranch r ki x t
        (zeroBranch kz x t (.assign x (.arithOp .round [.var t]))))) := by
  refine Equiv.of_fwd (fun σ C₀ o _ hκ hs => ?_) (fun σ C₀ o' _ hκ hs => ?_)
  · obtain rfl := hκ C rfl
    obtain ⟨u, ht, rfl⟩ := exec_round_inv hr hs
    exact ⟨_, exec_nanBranch ht (exec_infBranch ht (exec_zeroBranch hr h0 ht kz) ki) kn,
      Store.Agree.refl _⟩
  · obtain rfl := hκ C rfl
    obtain ⟨u, ht⟩ : ∃ u, σ t = some (.num u) := by
      cases kn
      · cases ki
        · cases kz
          · exact (exec_round_inv hr hs).imp fun _ h => h.1
          · obtain ⟨_, he⟩ := Exec.ite_guard hs
            exact num_of_binary (.inr rfl) he
        · obtain ⟨_, he⟩ := Exec.ite_guard hs
          exact num_of_unary (.inr rfl) he
      · obtain ⟨_, he⟩ := Exec.ite_guard hs
        exact num_of_unary (.inl rfl) he
    exact ⟨_, exec_round hr ht⟩

/-! ### Overflow -/

/-- **Overflow**: `[C] x = round(t) ⇝ with C' in r = round(t); if r < −b then x = ovf(−)
else if b < r then x = ovf(+) else x = r`, where `C` rounds into `F` with bound `b` and `C'`
rounds into `F` without it, for finite `t`. -/
theorem equiv_overflow {C C' : Val} {c c' : RoundCtx} {ce : Expr (fpy decode)} {x t r : Var}
    {b : NonNegDyadic} (hC : C.rnd (fpy decode) = some c.round) (hce : Denotes Φ ce C')
    (hC' : C'.rnd (fpy decode) = some c'.round) (hF : c'.F = c.F.unbounded) (hrm : c'.rm = c.rm)
    (hb : c.F.b = b) (hfin : ∀ σ, Γ.Holds σ → ∀ u, σ t = some (.num u) → ∃ y, u = .finite y) :
    Equiv Φ {r} Γ (some C) (.assign x (.arithOp .round [.var t]))
      (.seq (.withCtx ce (.assign r (.arithOp .round [.var t])))
        (.ite (.exactOp .lt [.var r, .num (.finite (-(b.1 : ℝ)))])
          (.assign x (.num (c.O.map true).toReal))
          (.ite (.exactOp .lt [.num (.finite (b.1 : ℝ)), .var r])
            (.assign x (.num (c.O.map false).toReal)) (.assign x (.var r))))) := by
  refine Equiv.of_fwd (fun σ C₀ o hΓ hκ hs => ?_) (fun σ C₀ o' _ hκ hs => ?_)
  · obtain rfl := hκ C rfl
    obtain ⟨u, ht, rfl⟩ := exec_round_inv hC hs
    obtain ⟨y, rfl⟩ := hfin σ hΓ u ht
    set yU := rndUnbounded c.F c.rm y c.defined
    have h₁ : Exec Φ σ C (.withCtx ce (.assign r (.arithOp .round [.var t])))
        (.normal (σ.update r (.num (.finite (yU : ℝ))))) := by
      have h := Exec.withCtx (C := C) ((hce σ C').mpr rfl) (exec_round (x := r) hC' ht)
      rwa [RoundCtx.round_unbounded hF hrm] at h
    have hr₁ : (σ.update r (.num (.finite (yU : ℝ)))) r = some (.num (.finite (yU : ℝ))) := by
      simp [Store.update]
    have hB : (0 : ℝ) ≤ (b.1 : ℝ) := by
      rw [Mpfx.Dyadic.coe_real_eq_ratCast]; exact_mod_cast b.2
    have hbd : Format.boundOK c.F.b yU ↔ |(yU : ℝ)| ≤ (b.1 : ℝ) := by
      rw [hb]
      change |(yU : ℚ)| ≤ ((b.1 : Mpfx.Dyadic) : ℚ) ↔ _
      rw [Mpfx.Dyadic.coe_real_eq_ratCast, Mpfx.Dyadic.coe_real_eq_ratCast, ← Rat.cast_abs,
        Rat.cast_le]
    rw [RoundCtx.round_finite]
    by_cases hin : Format.boundOK c.F.b yU
    · rw [if_pos hin]
      obtain ⟨hlo, hhi⟩ := abs_le.mp (hbd.mp hin)
      exact ⟨_, .seqNormal h₁ (.ite_dec (eval_lt (.var hr₁) .num) (fun h => by linarith)
        fun _ => .ite_dec (eval_lt .num (.var hr₁)) (fun h => by linarith)
          fun _ => .assign (.var hr₁)), Store.Agree.update_fresh _ _ _⟩
    · rw [if_neg hin]
      have hout := (not_congr hbd).mp hin
      rw [abs_le, not_and_or, not_le, not_le] at hout
      by_cases hneg : (yU : ℝ) < -(b.1 : ℝ)
      · rw [decide_eq_true (by rw [← Mpfx.Dyadic.coe_real_lt_zero_iff]; linarith)]
        exact ⟨_, .seqNormal h₁ (.ite_dec (eval_lt (.var hr₁) .num) (fun _ => .assign .num)
          fun h => absurd hneg h), Store.Agree.update_fresh _ _ _⟩
      · have hpos : (b.1 : ℝ) < yU := hout.resolve_left hneg
        rw [decide_eq_false (by rw [← Mpfx.Dyadic.coe_real_lt_zero_iff]; linarith)]
        exact ⟨_, .seqNormal h₁ (.ite_dec (eval_lt (.var hr₁) .num) (fun h => absurd h hneg)
          fun _ => .ite_dec (eval_lt .num (.var hr₁)) (fun _ => .assign .num)
            fun h => absurd hpos h), Store.Agree.update_fresh _ _ _⟩
  · obtain rfl := hκ C rfl
    obtain ⟨_, h₁⟩ := hs.seq_left
    obtain ⟨_, _, he⟩ := h₁.withCtx_assign
    obtain ⟨u, hu⟩ := he.num_of_arith (List.mem_singleton_self _)
    exact ⟨_, exec_round hC (eval_var_inv hu)⟩

/-- **Overflow** by a threshold: `[C] x = round(t) ⇝ if t < −θ then x = ovf(−) else if
θ < t then x = ovf(+) else x = round(t)`, when `C` overflows exactly beyond `±θ`, for finite
`t`. -/
theorem equiv_overflow_threshold {C : Val} {c : RoundCtx} {x t : Var} {θ : ℝ}
    (hC : C.rnd (fpy decode) = some c.round) (hθ0 : 0 ≤ θ)
    (hθ : ∀ y, Overflows c.F c.rm y ↔ y < -θ ∨ θ < y)
    (hfin : ∀ σ, Γ.Holds σ → ∀ u, σ t = some (.num u) → ∃ y, u = .finite y) :
    Equiv Φ X Γ (some C) (.assign x (.arithOp .round [.var t]))
      (.ite (.exactOp .lt [.var t, .num (.finite (-θ))]) (.assign x (.num (c.O.map true).toReal))
        (.ite (.exactOp .lt [.num (.finite θ), .var t]) (.assign x (.num (c.O.map false).toReal))
          (.assign x (.arithOp .round [.var t])))) := by
  refine Equiv.of_fwd (fun σ C₀ o hΓ hκ hs => ?_) (fun σ C₀ o' _ hκ hs => ?_)
  · obtain rfl := hκ C rfl
    obtain ⟨u, ht, rfl⟩ := exec_round_inv hC hs
    obtain ⟨y, rfl⟩ := hfin σ hΓ u ht
    refine ⟨.normal (σ.update x (.num (c.round (.finite y)))), ?_, Store.Agree.refl _⟩
    refine .ite_dec (eval_lt (.var ht) .num) (fun hneg => ?_) fun hneg =>
      .ite_dec (eval_lt .num (.var ht)) (fun hpos => ?_) fun _ => exec_round hC ht
    · rw [c.round_of_overflows ((hθ y).mpr (.inl hneg)), decide_eq_true (by linarith)]
      exact .assign .num
    · rw [c.round_of_overflows ((hθ y).mpr (.inr hpos)), decide_eq_false (by linarith)]
      exact .assign .num
  · obtain rfl := hκ C rfl
    obtain ⟨_, he⟩ := hs.ite_guard
    obtain ⟨u, ht⟩ := num_of_binary (.inl rfl) he
    exact ⟨_, exec_round hC ht⟩

/-- A quantum exponent as a number, with `⊥` as `−∞`. -/
def qexpNum (e : QExp) : Num :=
  QExp.recBotCoe (C := fun _ => Num) (.special (.inf true)) (fun k => .finite k) e

/-- `max(logb(y) + (1 − p), exp)` is `y`'s canonical exponent. -/
theorem num_canonicalExp {F : FiniteFormat} {p : ℕ} (hp : F.p = p) {y : ℝ} (hy : y ≠ 0) :
    Num.max (Num.add (Num.logb (.finite y)) (.finite (1 - p))) (qexpNum F.exp) =
      .finite (F.canonicalExp y : ℝ) := by
  have hl : Num.logb (.finite y) = .finite (Int.log 2 |y| : ℝ) := by simp [Num.logb, hy]
  rw [hl]
  cases hexp : F.exp using QExp.recBotCoe with
  | bot =>
    rw [canonicalExp_expBot hp hexp hy]
    change (.finite ((Int.log 2 |y| : ℝ) + (1 - p)) : Num) = _
    push_cast; ring_nf
  | coe e =>
    rw [canonicalExp_expFinite hp hexp hy]
    change (.finite (max ((Int.log 2 |y| : ℝ) + (1 - p)) (e : ℝ)) : Num) = _
    push_cast; ring_nf

/-- **FloatToFixed**: `[C] x = round(t) ⇝ with R in n = max(logb(t) + (1 − p), exp);
with C' in x = round(t)`, where `C` rounds into `𝒜(p, exp, ∞)` with `p ≠ 1` and `C'`, built
from `n`, rounds into `𝒜(∞, n, ∞)` with `C`'s mode, for finite nonzero `t`. -/
theorem equiv_floatToFixed {C : Val} {c : RoundCtx} {cf : Expr (fpy decode)} {x t n : Var}
    {p : ℕ} (hC : C.rnd (fpy decode) = some c.round) (hp : c.F.p = p) (hp1 : p ≠ 1)
    (hb : c.F.b = ⊤) (hnt : n ≠ t)
    (hcf : ∀ σ (k : ℤ), σ n = some (.num (.finite k)) → ∃ C' c', DenotesAt Φ σ cf C' ∧
      C'.rnd (fpy decode) = some (RoundCtx.round c') ∧ c'.F.p = ⊤ ∧ c'.F.exp = (k : QExp) ∧
      c'.F.b = ⊤ ∧ c'.rm = c.rm)
    (hfin : ∀ σ, Γ.Holds σ → ∀ u, σ t = some (.num u) → ∃ y, u = .finite y ∧ y ≠ 0) :
    Equiv Φ {n} Γ (some C) (.assign x (.arithOp .round [.var t]))
      (.seq (.withCtx .real (.assign n (.arithOp .max
          [.arithOp .add [.arithOp .logb [.var t], .num (.finite (1 - p))],
            .num (qexpNum c.F.exp)])))
        (.withCtx cf (.assign x (.arithOp .round [.var t])))) := by
  refine Equiv.of_fwd (fun σ C₀ o hΓ hκ hs => ?_) (fun σ C₀ o' _ hκ hs => ?_)
  · obtain rfl := hκ C rfl
    obtain ⟨u, ht, rfl⟩ := exec_round_inv hC hs
    obtain ⟨y, rfl, hy⟩ := hfin σ hΓ u ht
    set k := c.F.canonicalExp y
    have hev : Eval Φ σ .real (.arithOp .max
        [.arithOp .add [.arithOp .logb [.var t], .num (.finite (1 - p))],
          .num (qexpNum c.F.exp)]) (.num (.finite (k : ℝ))) := by
      rw [← num_canonicalExp hp hy]
      exact .arith (ns := [_, _]) (r := id) (.cons (.arith (ns := [_, _]) (r := id)
        (.cons (.arith (ns := [_]) (r := id) (.cons (.var ht) .nil) rfl rfl) (.cons .num .nil))
          rfl rfl) (.cons .num .nil)) rfl rfl
    obtain ⟨C', c', hden, hC', hp', he', hb', hrm'⟩ :=
      hcf (σ.update n (.num (.finite (k : ℝ)))) k (by simp [Store.update])
    have ht₁ : (σ.update n (.num (.finite (k : ℝ)))) t = some (.num (.finite y)) := by
      simp [Store.update, Ne.symm hnt, ht]
    have hp1' : c.F.p ≠ ((1 : ℕ) : Prec) := by
      rw [hp]; exact fun h => hp1 (by exact_mod_cast h)
    refine ⟨_, .seqNormal (.withCtx .real (.assign hev))
      (.withCtx ((hden C').mpr rfl) (exec_round hC' ht₁)), ?_⟩
    rw [RoundCtx.round_fixed hp1' hb hp' hb' hrm' he']
    exact Store.Agree.update_fresh _ _ _
  · obtain rfl := hκ C rfl
    obtain ⟨_, h₁⟩ := hs.seq_left
    obtain ⟨_, _, he⟩ := h₁.withCtx_assign
    obtain ⟨_, he⟩ := he.num_of_arith (List.mem_cons_self ..)
    obtain ⟨_, he⟩ := he.num_of_arith (List.mem_cons_self ..)
    obtain ⟨u, hu⟩ := he.num_of_arith (List.mem_singleton_self _)
    exact ⟨_, exec_round hC (eval_var_inv hu)⟩

/-- **Rescale**: `[C] x = round(t) ⇝ with R in u = 2⁻ᵏ × t; with C₀ in m = round(u);
with R in x = 2ᵏ × m`, where `C₀` is `C` scaled by `2⁻ᵏ` (`RoundCtx.Scaled`). -/
theorem equiv_rescale {C C₀ : Val} {c c₀ : RoundCtx} {ce : Expr (fpy decode)} {x t u m : Var}
    {k : ℤ} (hC : C.rnd (fpy decode) = some c.round) (hce : Denotes Φ ce C₀)
    (hC₀ : C₀.rnd (fpy decode) = some c₀.round) (hsc : c.Scaled c₀ k) :
    Equiv Φ {u, m} Γ (some C) (.assign x (.arithOp .round [.var t]))
      (.seq (.withCtx .real (.assign u (.arithOp .mul [.num (.finite (2 ^ (-k))), .var t])))
        (.seq (.withCtx ce (.assign m (.arithOp .round [.var u])))
          (.withCtx .real (.assign x (.arithOp .mul [.num (.finite (2 ^ k)), .var m]))))) := by
  refine Equiv.of_fwd (fun σ C₁ o _ hκ hs => ?_) (fun σ C₁ o' _ hκ hs => ?_)
  · obtain rfl := hκ C rfl
    obtain ⟨v, ht, rfl⟩ := exec_round_inv hC hs
    set σ₁ := σ.update u (.num (Num.mul (.finite (2 ^ (-k))) v))
    set σ₂ := σ₁.update m (.num (c₀.round (Num.mul (.finite (2 ^ (-k))) v)))
    have h₁ : Exec Φ σ .real (.assign u (.arithOp .mul [.num (.finite (2 ^ (-k))), .var t]))
        (.normal σ₁) :=
      .assign (.arith (ns := [_, _]) (r := id) (.cons .num (.cons (.var ht) .nil)) rfl rfl)
    have h₂ : Exec Φ σ₁ C₀ (.assign m (.arithOp .round [.var u])) (.normal σ₂) :=
      exec_round hC₀ (by simp [σ₁, Store.update])
    have h₃ : Exec Φ σ₂ .real (.assign x (.arithOp .mul [.num (.finite (2 ^ k)), .var m]))
        (.normal (σ₂.update x (.num (c.round v)))) := by
      rw [RoundCtx.round_scale hsc v]
      exact .assign (.arith (ns := [_, _]) (r := id)
        (.cons .num (.cons (.var (by simp [σ₂, Store.update])) .nil)) rfl rfl)
    refine ⟨_, .seqNormal (.withCtx .real h₁)
      (.seqNormal (.withCtx ((hce σ₁ C₀).mpr rfl) h₂) (.withCtx .real h₃)), ?_⟩
    exact Store.Agree.update ((σ.agree_update_of_mem (by simp) _).trans
      (σ₁.agree_update_of_mem (by simp) _)) _ _
  · obtain rfl := hκ C rfl
    obtain ⟨_, h₁⟩ := hs.seq_left
    obtain ⟨_, _, he⟩ := h₁.withCtx_assign
    obtain ⟨u, hu⟩ := he.num_of_arith (by simp : Expr.var t ∈ _)
    exact ⟨_, exec_round hC (eval_var_inv hu)⟩

/-! ## Well-formedness

The targets build no record literals outside their context expressions, so each
is well formed when those are. -/

theorem wf_special (r : Num → Num) (x t : Var) (kn ki kz : Bool) :
    (nanBranch r kn x t (infBranch r ki x t
      (zeroBranch kz x t (.assign x (.arithOp .round [.var t]))) : Stmt (fpy decode))).WF := by
  cases kn <;> cases ki <;> cases kz <;>
    simp [nanBranch, infBranch, zeroBranch, Stmt.WF, Expr.WF, Expr.WFList]

theorem wf_overflow {ce : Expr (fpy decode)} (hce : ce.WF) (x t r : Var) (lo hi o₁ o₂ : Num) :
    (Stmt.seq (.withCtx ce (.assign r (.arithOp .round [.var t])))
      (.ite (.exactOp .lt [.var r, .num lo]) (.assign x (.num o₁))
        (.ite (.exactOp .lt [.num hi, .var r]) (.assign x (.num o₂))
          (.assign x (.var r))))).WF := by
  simp [Stmt.WF, Expr.WF, Expr.WFList, hce]

theorem wf_overflow_threshold (x t : Var) (lo hi o₁ o₂ : Num) :
    (Stmt.ite (.exactOp .lt [.var t, .num lo]) (.assign x (.num o₁))
      (.ite (.exactOp .lt [.num hi, .var t]) (.assign x (.num o₂))
        (.assign x (.arithOp .round [.var t]))) : Stmt (fpy decode)).WF := by
  simp [Stmt.WF, Expr.WF, Expr.WFList]

theorem wf_floatToFixed {cf : Expr (fpy decode)} (hcf : cf.WF) (x t n : Var) (q e : Num) :
    (Stmt.seq (.withCtx .real (.assign n (.arithOp .max
        [.arithOp .add [.arithOp .logb [.var t], .num q], .num e])))
      (.withCtx cf (.assign x (.arithOp .round [.var t])))).WF := by
  simp [Stmt.WF, Expr.WF, Expr.WFList, hcf]

theorem wf_rescale {ce : Expr (fpy decode)} (hce : ce.WF) (x t u m : Var) (a b : Num) :
    (Stmt.seq (.withCtx .real (.assign u (.arithOp .mul [.num a, .var t])))
      (.seq (.withCtx ce (.assign m (.arithOp .round [.var u])))
        (.withCtx .real (.assign x (.arithOp .mul [.num b, .var m]))))).WF := by
  simp [Stmt.WF, Expr.WF, Expr.WFList, hce]

end Fpy
