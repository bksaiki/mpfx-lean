import Fpy.DigitBound.Digits
import Mpfx.Rounding.Ulp

/-!
# Table 2: abstract operators and rounding

D-Arith's premise `ArithOK` is `rnd♮_C(op♮(Is))`: an operator transfer
`OpOK` followed by a rounding transfer `RndOK` (`ArithOK.comp`). Each row of
Table 2 discharges one. A compound endpoint is a fresh variable bounded by it:
the result interval is `[λ, μ]` with `μ = n` bounded above and `λ = n + 1`
below (`fresh_numIn`). Under the extended endpoints this applies to a lone
endpoint as well, since a value can round to `0`, whose interval is `[+∞, −∞]`.

The rounding rows take the contexts `κ` admits through `Decodes`: each decodes
to a context of the row's shape whose overflow and special values have digits
within `[Lo, Ho]`, and the row's interval is joined with `[Lo, Ho]`.
-/

namespace Fpy.DigitBound

open Mpfx

local notation "nan" => (WithSpecial.special Special.nan : Num)

variable {decode : List (Label × Val) → Option RoundCtx}

/-! ## Transfers -/

/-- `op♮(Is)`: `[l, m]`, with fresh variables `[n₀, n₁)` bounded by `Ψ`,
bounds `op` on values described by `Is`, before rounding. -/
def OpOK (op : ArithOp) (Is : List (Term × Term × Option Term)) (n₀ n₁ : ℕ) (Ψ : List Con)
    (l m : Term) : Prop :=
  ∀ ι ns u, List.Forall₂ (fun (I : Term × Term × Option Term) n => NumIn ι I.1 I.2.1 I.2.2 n)
    Is ns → op.eval ns = some u → ∃ ι', AgreeOut n₀ n₁ ι ι' ∧ Sat ι' Ψ ∧ NumIn ι' l m none u

variable (decode) in
/-- `rnd♮_κ([l, m])`: `[l', m']`, with fresh variables `[n₀, n₁)` bounded by
`Ψ`, bounds the rounding of a value in `[l, m]` under any context `κ` admits. -/
def RndOK (κ : Option SCtx) (l m : Term) (n₀ n₁ : ℕ) (Ψ : List Con) (l' m' : Term) : Prop :=
  ∀ ι u C r, NumIn ι l m none u → (∀ K ∈ κ, K.Admits ι C) → C.rnd (fpy decode) = some r →
    ∃ ι', AgreeOut n₀ n₁ ι ι' ∧ Sat ι' Ψ ∧ NumIn ι' l' m' none (r u)

/-- D-Arith's premise from Table 2's two columns. -/
theorem ArithOK.comp {κ : Option SCtx} {op : ArithOp} {Is : List (Term × Term × Option Term)}
    {n₀ n₁ n₂ : ℕ} {Ψ₁ Ψ₂ : List Con} {l m l' m' : Term} (ho : OpOK op Is n₀ n₁ Ψ₁ l m)
    (hr : RndOK decode κ l m n₁ n₂ Ψ₂ l' m') (hF₁ : Fresh n₀ n₁ Ψ₁) (hF₂ : Fresh n₁ n₂ Ψ₂)
    (hκ : CtxBelow n₀ κ) : ArithOK decode κ op Is n₀ n₂ (Ψ₁ ++ Ψ₂) l' m' := by
  intro ι ns u C r hns hop hC hr'
  obtain ⟨ι₁, a₁, s₁, h₁⟩ := ho ι ns u hns hop
  obtain ⟨ι₂, a₂, s₂, h₂⟩ := hr ι₁ u C r h₁ (admits_congr a₁.agree hκ hC) hr'
  refine ⟨ι₂, fun x hx => ?_, (Sat.congr hF₁ a₂.agree s₁).append s₂, h₂⟩
  have := hF₁.le
  have := hF₂.le
  rw [a₂ x (by omega), a₁ x (by omega)]

/-! ## Operator rows -/

theorem forall₂_one {α β : Type} {R : α → β → Prop} {a : α} {l : List β}
    (h : List.Forall₂ R [a] l) : ∃ b, l = [b] ∧ R a b := by
  rcases h with _ | ⟨h, h'⟩; cases h'; exact ⟨_, rfl, h⟩

theorem forall₂_two {α β : Type} {R : α → β → Prop} {a₁ a₂ : α} {l : List β}
    (h : List.Forall₂ R [a₁, a₂] l) : ∃ b₁ b₂, l = [b₁, b₂] ∧ R a₁ b₁ ∧ R a₂ b₂ := by
  rcases h with _ | ⟨h₁, _ | ⟨h₂, h'⟩⟩; cases h'; exact ⟨_, _, rfl, h₁, h₂⟩

/-- A row whose interval is fresh, bounded by `Lo` and `Hi` on the operands'
endpoints. -/
theorem opOK_of {op : ArithOp} {Is : List (Term × Term × Option Term)} {n : ℕ} {Lo Hi : Term}
    (hLo : Lo.Below n) (hHi : Hi.Below n)
    (h : ∀ ι ns u, List.Forall₂ (fun (I : Term × Term × Option Term) n => NumIn ι I.1 I.2.1 I.2.2 n)
      Is ns → op.eval ns = some u → u ≠ nan → msbOf u ≤ Hi.eval ι ∧ Lo.eval ι ≤ lsbOf u) :
    OpOK op Is n (n + 2) (bounds n Lo Hi (hLo.mono (Nat.le_succ n)) hHi) (.var (n + 1))
      (.var n) := fun ι ns u hns hop => fresh_numIn _ hHi ι u fun hu => by
  obtain ⟨h₁, h₂⟩ := h ι ns u hns hop hu
  exact ⟨h₁, by rwa [← Term.eval_congr (fun x hx => (Function.update_of_ne hx.ne _ _).symm) hLo]⟩

variable {n : ℕ} {l m l₁ m₁ l₂ m₂ : Term} {τ τ₁ τ₂ : Option Term}

/-- `x ± y : [min(l₁, l₂), max(m₁, m₂) + 1]`. -/
theorem opOK_add {op : ArithOp} (hop : op = .add ∨ op = .sub) (hLo : (Term.min l₁ l₂).Below n)
    (hHi : (Term.add (.max m₁ m₂) (.const (1 : ℤ))).Below n) :
    OpOK op [(l₁, m₁, τ₁), (l₂, m₂, τ₂)] n (n + 2)
      (bounds n _ _ (hLo.mono (Nat.le_succ n)) hHi) (.var (n + 1)) (.var n) :=
  opOK_of hLo hHi fun ι ns u hns hu hn => by
    obtain ⟨u₁, u₂, rfl, h₁, h₂⟩ := forall₂_two hns
    obtain ⟨v, rfl, hv, hlv, hmv⟩ : ∃ v, u = Num.add u₁ v ∧ (u₂ = nan → v = nan) ∧
        lsbOf v = lsbOf u₂ ∧ msbOf v = msbOf u₂ := by
      rcases hop with rfl | rfl <;> simp only [ArithOp.eval, Option.some.injEq] at hu <;> subst hu
      exacts [⟨u₂, rfl, id, rfl, rfl⟩,
        ⟨Num.neg u₂, rfl, fun h => by rw [h]; rfl, lsbOf_neg _, msbOf_neg _⟩]
    have n₁ : u₁ ≠ nan := by rintro rfl; exact hn (by rcases v with _ | (_ | _) <;> rfl)
    have n₂ : u₂ ≠ nan := fun h => hn (by rw [hv h]; rcases u₁ with _ | (_ | _) <;> rfl)
    obtain ⟨hl₁, hm₁⟩ := h₁.eq n₁
    obtain ⟨hl₂, hm₂⟩ := h₂.eq n₂
    refine ⟨(msb_add u₁ v).trans_eq ?_, (lsb_add u₁ v).trans_eq' ?_⟩ <;>
      simp only [Term.eval, hlv, hmv, hl₁, hm₁, hl₂, hm₂]

/-- `x × y : [l₁ + l₂, m₁ + m₂ + 1]`. -/
theorem opOK_mul (hLo : (Term.add l₁ l₂).Below n)
    (hHi : (Term.add (.add m₁ m₂) (.const (1 : ℤ))).Below n) :
    OpOK .mul [(l₁, m₁, τ₁), (l₂, m₂, τ₂)] n (n + 2)
      (bounds n _ _ (hLo.mono (Nat.le_succ n)) hHi) (.var (n + 1)) (.var n) :=
  opOK_of hLo hHi fun ι ns u hns hu hn => by
    obtain ⟨u₁, u₂, rfl, h₁, h₂⟩ := forall₂_two hns
    simp only [ArithOp.eval, Option.some.injEq] at hu
    subst hu
    have n₁ : u₁ ≠ nan := by rintro rfl; exact hn (by rcases u₂ with _ | (_ | _) <;> rfl)
    have n₂ : u₂ ≠ nan := by rintro rfl; exact hn (by rcases u₁ with _ | (_ | _) <;> rfl)
    obtain ⟨hl₁, hm₁⟩ := h₁.eq n₁
    obtain ⟨hl₂, hm₂⟩ := h₂.eq n₂
    refine ⟨(msb_mul hn).trans_eq ?_, (lsb_mul u₁ u₂).trans_eq' ?_⟩ <;>
      simp only [Term.eval, hl₁, hm₁, hl₂, hm₂]

/-- `−x`, `|x|`, `round(x)` keep `[l, m]`. -/
theorem opOK_exact {op : ArithOp} (hop : op = .neg ∨ op = .abs ∨ op = .round ∨ op = .cast) :
    OpOK op [(l, m, τ)] n n [] l m := by
  intro ι ns u hns hu
  obtain ⟨u₁, rfl, h₁⟩ := forall₂_one hns
  refine ⟨ι, fun _ _ => rfl, fun _ h => absurd h (by simp), ?_⟩
  obtain ⟨f, rfl, hf, hl, hm⟩ : ∃ f : Num → Num, u = f u₁ ∧ f nan = nan ∧
      lsbOf (f u₁) = lsbOf u₁ ∧ msbOf (f u₁) = msbOf u₁ := by
    rcases hop with rfl | rfl | rfl | rfl <;> simp only [ArithOp.eval, Option.some.injEq] at hu <;>
      subst hu
    exacts [⟨Num.neg, rfl, rfl, lsbOf_neg _, msbOf_neg _⟩, ⟨Num.abs, rfl, rfl, lsbOf_abs _,
      msbOf_abs _⟩, ⟨id, rfl, rfl, rfl, rfl⟩, ⟨id, rfl, rfl, rfl, rfl⟩]
  rcases h₁.forget with rfl | ⟨hl₁, hm₁, -⟩
  · exact .inl hf
  · exact .inr ⟨hl.trans hl₁, hm.trans hm₁, fun _ h => absurd h (by simp)⟩

/-- `min(x, y)`, `max(x, y) : [min(l₁, l₂), max(m₁, m₂)]`. -/
theorem opOK_ext {op : ArithOp} (hop : op = .min ∨ op = .max) (hLo : (Term.min l₁ l₂).Below n)
    (hHi : (Term.max m₁ m₂).Below n) :
    OpOK op [(l₁, m₁, τ₁), (l₂, m₂, τ₂)] n (n + 2)
      (bounds n _ _ (hLo.mono (Nat.le_succ n)) hHi) (.var (n + 1)) (.var n) :=
  opOK_of hLo hHi fun ι ns u hns hu hn => by
    obtain ⟨u₁, u₂, rfl, h₁, h₂⟩ := forall₂_two hns
    have hc : u = u₁ ∨ u = u₂ ∨ u = nan := by
      rcases hop with rfl | rfl <;> simp only [ArithOp.eval, Option.some.injEq] at hu <;>
        subst hu
      exacts [Num.min_cases u₁ u₂, Num.max_cases u₁ u₂]
    simp only [Term.eval]
    rcases hc with rfl | rfl | rfl
    · obtain ⟨hl, hm⟩ := h₁.eq hn
      exact ⟨hm ▸ le_max_left _ _, hl ▸ min_le_left _ _⟩
    · obtain ⟨hl, hm⟩ := h₂.eq hn
      exact ⟨hm ▸ le_max_right _ _, hl ▸ min_le_right _ _⟩
    · exact absurd rfl hn

/-- `2ˣ : [τ, τ]` when `x` has term `τ`. -/
theorem opOK_exp2 {t : Term} (hLo : t.Below n) :
    OpOK .exp2 [(l, m, some t)] n (n + 2) (bounds n t t (hLo.mono (Nat.le_succ n)) hLo)
      (.var (n + 1)) (.var n) :=
  opOK_of hLo hLo fun ι ns u hns hu hn => by
    obtain ⟨u₁, rfl, h₁⟩ := forall₂_one hns
    simp only [ArithOp.eval, Option.some.injEq] at hu
    subst hu
    rcases h₁.term with rfl | rfl
    · exact absurd rfl hn
    · exact (digits_exp2 _).symm

/-- `logb(x) : [0, μ]`. -/
theorem opOK_logb :
    OpOK .logb [(l, m, τ)] n (n + 2) (bounds n (.const (0 : ℤ)) (.const ⊤) trivial trivial)
      (.var (n + 1)) (.var n) :=
  opOK_of (Lo := .const (0 : ℤ)) (Hi := .const ⊤) trivial trivial fun ι ns u hns hu _ => by
    obtain ⟨u₁, rfl, -⟩ := forall₂_one hns
    simp only [ArithOp.eval, Option.some.injEq] at hu
    subst hu
    exact ⟨le_top, lsb_logb u₁⟩

/-- All other operators: `[λ, μ]`. -/
theorem opOK_any {op : ArithOp} {Is : List (Term × Term × Option Term)} :
    OpOK op Is n (n + 2) (bounds n (.const ⊥) (.const ⊤) trivial trivial) (.var (n + 1))
      (.var n) :=
  opOK_of (Lo := .const ⊥) (Hi := .const ⊤) trivial trivial fun _ _ _ _ _ _ => ⟨le_top, bot_le⟩

/-! ## Rounding rows -/

/-- `c`'s overflow and special values have digits in `[lo, hi]`, except an
infinity sent to an infinity. -/
def ImagesIn (c : RoundCtx) (lo hi : EInt) : Prop :=
  (∀ b, InRange lo hi (c.O.map b).toReal) ∧
    ∀ s, InRange lo hi (c.S.map s).toReal ∨ ∃ a b, s = .inf a ∧ c.S.map s = .special (.inf b)

variable (decode) in
/-- Each context `κ` admits decodes to a context `P` accepts, whose overflow
and special values have digits in `[Lo, Ho]`. -/
def Decodes (κ : Option SCtx) (P : Asgn → RoundCtx → Prop) (Lo Ho : Term) : Prop :=
  ∀ ι C r, (∀ K ∈ κ, K.Admits ι C) → C.rnd (fpy decode) = some r →
    ∃ c : RoundCtx, r = c.round ∧ P ι c ∧ ImagesIn c (Lo.eval ι) (Ho.eval ι)

/-- The quantum of `c` is `2^τ`. -/
def QuantumIs (τ : Term) (ι : Asgn) (c : RoundCtx) : Prop := ∃ k : ℤ, τ.eval ι = k ∧ c.F.exp = k

/-- `R`: `[l, m]`. -/
theorem rndOK_real : RndOK decode (some .real) l m n n [] l m := by
  intro ι u C r hu hC hr
  obtain rfl : C = .real := hC _ rfl
  obtain rfl : id = r := Option.some.inj hr
  exact ⟨ι, fun _ _ => rfl, fun _ h => absurd h (by simp), hu⟩

/-- A row whose interval is fresh, bounded by `Lr` and `Hr` on the input's
endpoints and joined with the overflow and special values' digits. `Lr` may
mention the result's most significant digit `n`. -/
theorem rndOK_of {κ : Option SCtx} {P : Asgn → RoundCtx → Prop} {Lr Hr Lo Ho : Term}
    (hLr : Lr.Below (n + 1)) (hHr : Hr.Below n) (hLo : Lo.Below n) (hHo : Ho.Below n)
    (hκ : Decodes decode κ P Lo Ho) (htop : ∀ ι, m.eval ι = ⊤ → Hr.eval ι = ⊤)
    (hrow : ∀ ι c (x : ℝ) (y : Mpfx.Dyadic), P ι c → x ≠ 0 → lsbOf (.finite x) = l.eval ι →
      msbOf (.finite x) = m.eval ι → RoundsFinite c.F.unbounded c.rm x y → (y : ℝ) ≠ 0 →
      msbOf (.finite (y : ℝ)) ≤ Hr.eval ι ∧
        Lr.eval (Function.update ι n (msbOf (.finite (y : ℝ)))) ≤ lsbOf (.finite (y : ℝ))) :
    RndOK decode κ l m n (n + 2)
      (bounds n (.min Lr Lo) (.max Hr Ho) ⟨hLr, hLo.mono (Nat.le_succ n)⟩ ⟨hHr, hHo⟩)
      (.var (n + 1)) (.var n) := by
  intro ι u C r hu hC hr
  obtain ⟨c, rfl, hP, hO, hS⟩ := hκ ι C r hC hr
  refine fresh_numIn _ _ ι _ fun hw => ?_
  simp only [Term.eval, eval_update hLo]
  have ofRange : ∀ w, InRange (Lo.eval ι) (Ho.eval ι) w → w ≠ nan →
      msbOf w ≤ max (Hr.eval ι) (Ho.eval ι) ∧
        min (Lr.eval (Function.update ι n (msbOf w))) (Lo.eval ι) ≤ lsbOf w := fun w h hn => by
    obtain ⟨h₁, h₂⟩ := h.resolve_left hn
    exact ⟨h₂.trans (le_max_right _ _), (min_le_right _ _).trans h₁⟩
  rcases u with x | s
  · by_cases hx : x = 0
    · subst hx
      rw [RoundCtx.round_zero, lsbOf_zero, msbOf_zero]
      exact ⟨bot_le, le_top⟩
    obtain ⟨hl, hm⟩ := hu.eq (by simp)
    rw [RoundCtx.round_finite] at hw ⊢
    split_ifs at hw ⊢
    · by_cases hy : ((rndUnbounded c.F c.rm x c.defined : Mpfx.Dyadic) : ℝ) = 0
      · rw [hy, lsbOf_zero, msbOf_zero]
        exact ⟨bot_le, le_top⟩
      obtain ⟨h₁, h₂⟩ := hrow ι c x _ hP hx hl hm (rndUnbounded_satisfies _ _ _ _) hy
      exact ⟨h₁.trans (le_max_left _ _), (min_le_left _ _).trans h₂⟩
    · exact ofRange _ (hO _) hw
  · rw [RoundCtx.round_special] at hw ⊢
    rcases hS s with h | ⟨a, b, rfl, he⟩
    · exact ofRange _ h hw
    · obtain ⟨-, hm⟩ := hu.eq (by simp)
      rw [he, WithSpecial.toReal_special, msbOf_special, lsbOf_special, htop ι hm.symm]
      exact ⟨le_max_left _ _, le_top⟩

theorem lsb_round {F : FiniteFormat} {rm : RoundingMode} {x : ℝ} {y : Mpfx.Dyadic}
    (hy : RoundsFinite F.unbounded rm x y) : lsbOf (.finite x) ≤ lsbOf (.finite (y : ℝ)) :=
  EInt.le_of_forall_coe_le fun _ hk => by
    obtain ⟨_, hz⟩ := coe_le_lsbOf.mp hk
    exact coe_le_lsbOf.mpr (hy.mul_zpow_of_mul_zpow hz)

theorem canonicalExp_le_lsb {F : FiniteFormat} {rm : RoundingMode} {x : ℝ} {y : Mpfx.Dyadic}
    (hy : RoundsFinite F.unbounded rm x y) :
    ((F.canonicalExp x : ℤ) : EInt) ≤ lsbOf (.finite (y : ℝ)) :=
  coe_le_lsbOf.mpr hy.exists_mul_zpow

/-- A rounding stays below the next power of two at or above the quantum. -/
theorem msb_round_le {F : FiniteFormat} {rm : RoundingMode} {x : ℝ} {y : Mpfx.Dyadic}
    (hy : RoundsFinite F.unbounded rm x y) (hx : x ≠ 0) {k : ℤ} (hk : F.exp ≤ (k : QExp)) :
    msbOf (.finite (y : ℝ)) ≤ ((max (Int.log 2 |x| + 1) k : ℤ) : EInt) := by
  set j := max (Int.log 2 |x| + 1) k
  have hN := F.zpow_mem_unbounded (j := j) (hk.trans (by exact_mod_cast le_max_right _ _))
  have hxN : |x| ≤ ((Dyadic.ofIntZpow 1 j : Mpfx.Dyadic) : ℝ) := by
    rw [Dyadic.coe_ofIntZpow, Int.cast_one, one_mul]
    exact (msbOf_le_coe.mp (msbOf_of_ne_zero hx).le).le.trans
      (zpow_le_zpow_right₀ (by norm_num) (le_max_left _ _))
  have hyN := abs_faithful_le_of_le hN hxN hy.isFaithfulRound
  rw [Dyadic.coe_ofIntZpow, Int.cast_one, one_mul] at hyN
  refine msbOf_le_coe.mpr (hyN.trans_lt ?_)
  exact zpow_lt_zpow_right₀ (by norm_num) (by omega)

/-- A value of precision `p` has its digits within `p` positions. -/
theorem msb_add_le_lsb {F : FiniteFormat} {p : ℕ} (hp : F.p = p) {y : Mpfx.Dyadic}
    (hy : y ∈ F.unbounded) (h0 : (y : ℝ) ≠ 0) :
    msbOf (.finite (y : ℝ)) + ((1 - p : ℤ) : EInt) ≤ lsbOf (.finite (y : ℝ)) := by
  obtain ⟨c, e, hce, hc⟩ := (Dyadic.precisionAtMost_coe_real p y).mp (hp ▸ hy.1)
  refine le_trans ?_ (coe_le_lsbOf.mpr ⟨c, hce⟩)
  have hlt : |(y : ℝ)| < 2 ^ ((e + p - 1 : ℤ) + 1) := by
    rw [hce, abs_mul_two_zpow, show (e + p - 1 : ℤ) + 1 = p + e by ring, zpow_add₀ two_ne_zero,
      zpow_natCast]
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hc) (zpow_pos two_pos e)
  have hM := msbOf_le_coe.mpr hlt
  rw [msbOf_of_ne_zero h0, WithBotTop.coe_le_coe] at hM
  rw [msbOf_of_ne_zero h0, coe_add_coe, WithBotTop.coe_le_coe]
  omega

variable {κ : Option SCtx} {Lo Ho : Term}

/-- `Fixed(τ, RTZ) : [max(l, τ), m]`. -/
theorem rndOK_fixedRTZ {t : Term} (hl : l.Below n) (ht : t.Below n) (hm : m.Below n)
    (hLo : Lo.Below n) (hHo : Ho.Below n)
    (hκ : Decodes decode κ (fun ι c => QuantumIs t ι c ∧ c.rm = .toZero) Lo Ho) :
    RndOK decode κ l m n (n + 2)
      (bounds n (.min (.max l t) Lo) (.max m Ho)
        ⟨⟨hl.mono (Nat.le_succ n), ht.mono (Nat.le_succ n)⟩, hLo.mono (Nat.le_succ n)⟩ ⟨hm, hHo⟩)
      (.var (n + 1)) (.var n) :=
  rndOK_of (Lr := .max l t) ⟨hl.mono (Nat.le_succ n), ht.mono (Nat.le_succ n)⟩ hm hLo hHo hκ
    (fun _ h => h) fun ι c x y ⟨⟨k, hk, he⟩, hrm⟩ _ hl' hm' hy _ => by
    rw [hrm] at hy
    refine ⟨hm' ▸ msbOf_mono hy.2.1, ?_⟩
    simp only [Term.eval, eval_update hl, eval_update ht, hk]
    exact max_le (hl' ▸ lsb_round hy) ((WithBotTop.coe_le_coe.mpr
      (c.F.exp_le_canonicalExp x he)).trans (canonicalExp_le_lsb hy))

/-- `max(m + 1, τ)` is `⊤` at `m = ⊤`. -/
theorem max_succ_top {t : Term} (ι : Asgn) (h : m.eval ι = ⊤) :
    (Term.max (.add m (.const (1 : ℤ))) t).eval ι = ⊤ := by
  simp only [Term.eval, h, EInt.top_add_coe]
  exact max_eq_left le_top

/-- `max(m + 1, τ)` at a finite `m`. -/
theorem max_succ_eval {t : Term} {ι : Asgn} {M k : ℤ} (hm : m.eval ι = M) (ht : t.eval ι = k) :
    (Term.max (.add m (.const (1 : ℤ))) t).eval ι = ((max (M + 1) k : ℤ) : EInt) := by
  simp only [Term.eval, hm, ht, coe_add_coe, coe_max_coe]

/-- `Fixed(τ, rm) : [max(l, τ), max(m + 1, τ)]`. -/
theorem rndOK_fixed {t : Term} (hl : l.Below n) (ht : t.Below n) (hm : m.Below n)
    (hLo : Lo.Below n) (hHo : Ho.Below n) (hκ : Decodes decode κ (QuantumIs t) Lo Ho) :
    RndOK decode κ l m n (n + 2)
      (bounds n (.min (.max l t) Lo) (.max (.max (.add m (.const (1 : ℤ))) t) Ho)
        ⟨⟨hl.mono (Nat.le_succ n), ht.mono (Nat.le_succ n)⟩, hLo.mono (Nat.le_succ n)⟩
        ⟨⟨⟨hm, trivial⟩, ht⟩, hHo⟩)
      (.var (n + 1)) (.var n) :=
  rndOK_of (Lr := .max l t) (Hr := .max (.add m (.const (1 : ℤ))) t)
    ⟨hl.mono (Nat.le_succ n), ht.mono (Nat.le_succ n)⟩ ⟨⟨hm, trivial⟩, ht⟩ hLo hHo hκ max_succ_top
    fun ι c x y ⟨k, hk, he⟩ hx hl' hm' hy _ => by
    refine ⟨?_, ?_⟩
    · rw [max_succ_eval (hm'.symm.trans (msbOf_of_ne_zero hx)) hk]
      exact msb_round_le hy hx he.le
    · simp only [Term.eval, eval_update hl, eval_update ht, hk]
      exact max_le (hl' ▸ lsb_round hy) ((WithBotTop.coe_le_coe.mpr
        (c.F.exp_le_canonicalExp x he)).trans (canonicalExp_le_lsb hy))

/-- `IEEE754(es, nb, RTZ) : [max(l, m − p + 1), m]`, for precision `p`. -/
theorem rndOK_precRTZ {p : ℕ} (hl : l.Below n) (hm : m.Below n) (hLo : Lo.Below n)
    (hHo : Ho.Below n) (hκ : Decodes decode κ (fun _ c => c.F.p = p ∧ c.rm = .toZero) Lo Ho) :
    RndOK decode κ l m n (n + 2)
      (bounds n (.min (.max l (.add m (.const (1 - p : ℤ)))) Lo) (.max m Ho)
        ⟨⟨hl.mono (Nat.le_succ n), hm.mono (Nat.le_succ n), trivial⟩, hLo.mono (Nat.le_succ n)⟩
        ⟨hm, hHo⟩)
      (.var (n + 1)) (.var n) :=
  rndOK_of (Lr := .max l (.add m (.const (1 - p : ℤ))))
    ⟨hl.mono (Nat.le_succ n), hm.mono (Nat.le_succ n), trivial⟩ hm hLo hHo hκ
    (fun _ h => h) fun ι c x y ⟨hp, hrm⟩ hx hl' hm' hy _ => by
    rw [hrm] at hy
    refine ⟨hm' ▸ msbOf_mono hy.2.1, ?_⟩
    simp only [Term.eval, eval_update hl, eval_update hm, ← hm', msbOf_of_ne_zero hx, coe_add_coe]
    refine max_le (hl' ▸ lsb_round hy) ((WithBotTop.coe_le_coe.mpr ?_).trans
      (canonicalExp_le_lsb hy))
    have := c.F.log_sub_p_le_canonicalExp hx hp
    omega

/-- `IEEE754(es, nb, rm) : [max(l, μ − p + 1), μ]` with `μ ≤ max(m + 1, τ)`, for
precision `p` and quantum `2^τ`. -/
theorem rndOK_prec {p : ℕ} {t : Term} (hl : l.Below n) (ht : t.Below n) (hm : m.Below n)
    (hLo : Lo.Below n) (hHo : Ho.Below n)
    (hκ : Decodes decode κ (fun ι c => c.F.p = p ∧ QuantumIs t ι c) Lo Ho) :
    RndOK decode κ l m n (n + 2)
      (bounds n (.min (.max l (.add (.var n) (.const (1 - p : ℤ)))) Lo)
        (.max (.max (.add m (.const (1 : ℤ))) t) Ho)
        ⟨⟨hl.mono (Nat.le_succ n), Nat.lt_succ_self n, trivial⟩, hLo.mono (Nat.le_succ n)⟩
        ⟨⟨⟨hm, trivial⟩, ht⟩, hHo⟩)
      (.var (n + 1)) (.var n) :=
  rndOK_of (Lr := .max l (.add (.var n) (.const (1 - p : ℤ))))
    (Hr := .max (.add m (.const (1 : ℤ))) t)
    ⟨hl.mono (Nat.le_succ n), Nat.lt_succ_self n, trivial⟩ ⟨⟨hm, trivial⟩, ht⟩ hLo hHo hκ
    max_succ_top fun ι c x y ⟨hp, k, hk, he⟩ hx hl' hm' hy hy0 => by
    refine ⟨?_, ?_⟩
    · rw [max_succ_eval (hm'.symm.trans (msbOf_of_ne_zero hx)) hk]
      exact msb_round_le hy hx he.le
    · simp only [Term.eval, eval_update hl, Function.update_self]
      exact max_le (hl' ▸ lsb_round hy) (msb_add_le_lsb hp hy.1 hy0)

/-- All other contexts: `[l, μ]`. -/
theorem rndOK_any (hl : l.Below n) (hLo : Lo.Below n) (hHo : Ho.Below n)
    (hκ : Decodes decode κ (fun _ _ => True) Lo Ho) :
    RndOK decode κ l m n (n + 2)
      (bounds n (.min l Lo) (.max (.const ⊤) Ho) ⟨hl.mono (Nat.le_succ n), hLo.mono (Nat.le_succ n)⟩
        ⟨trivial, hHo⟩)
      (.var (n + 1)) (.var n) :=
  rndOK_of (Hr := .const ⊤) (hl.mono (Nat.le_succ n)) trivial hLo hHo hκ (fun _ _ => rfl)
    fun ι _ _ _ _ _ hl' _ hy _ => ⟨le_top, by rw [eval_update hl, ← hl']; exact lsb_round hy⟩

end Fpy.DigitBound
