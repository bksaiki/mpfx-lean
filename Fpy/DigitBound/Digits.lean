import Fpy.DigitBound.Basic

/-!
# Digit positions of numbers

`lsbOf x ≥ k` says `x` is a multiple of `2ᵏ` (`coe_le_lsbOf`), and
`msbOf x ≤ k` that `|x| < 2ᵏ⁺¹` (`msbOf_le_coe`). From these, the digit
positions of each operator's result, as Table 2 bounds them.
-/

namespace Fpy.DigitBound

open Mpfx

local notation "nan" => (WithSpecial.special Special.nan : Num)

/-! ## Extended integers -/

/-- `a ≤ b` once every integer below `a` is below `b`. -/
theorem EInt.le_of_forall_coe_le {a b : EInt} (h : ∀ k : ℤ, (k : EInt) ≤ a → (k : EInt) ≤ b) :
    a ≤ b := by
  cases a using WithBotTop.rec with
  | bot => exact bot_le
  | coe k => exact h k le_rfl
  | top =>
    cases b using WithBotTop.rec with
    | bot => simpa using h 0 le_top
    | coe j => simpa using h (j + 1) le_top
    | top => exact le_rfl

/-- `a ≤ b` once every integer above `b` is above `a`. -/
theorem EInt.le_of_forall_le_coe {a b : EInt} (h : ∀ k : ℤ, b ≤ k → a ≤ k) : a ≤ b := by
  cases b using WithBotTop.rec with
  | top => exact le_top
  | coe k => exact h k le_rfl
  | bot =>
    cases a using WithBotTop.rec with
    | bot => exact le_rfl
    | coe j => simpa using h (j - 1) bot_le
    | top => simpa using h 0 bot_le

@[simp] theorem EInt.top_add_coe (k : ℤ) : (⊤ : EInt) + k = ⊤ := rfl

theorem EInt.add_coe_le_coe {a : EInt} {j k : ℤ} : a + j ≤ k ↔ a ≤ ((k - j : ℤ) : EInt) := by
  cases a using WithBotTop.rec with
  | bot => simp
  | coe i => rw [coe_add_coe]; simp only [WithBotTop.coe_le_coe]; omega
  | top => simp

/-! ## Digit positions of reals -/

theorem LsbAt.ne_zero {x : ℝ} {k : ℤ} : LsbAt x k → x ≠ 0 := by
  rintro ⟨c, hc, rfl⟩
  have : (c : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (by rintro rfl; simp at hc)
  exact mul_ne_zero this (zpow_ne_zero _ two_ne_zero)

theorem LsbAt.le {x : ℝ} {j k : ℤ} (hj : LsbAt x j) (hk : LsbAt x k) : j ≤ k := by
  obtain ⟨c, hc, rfl⟩ := hj
  obtain ⟨d, hd, he⟩ := hk
  by_contra hlt
  have := coeff_eq_of_shift (K := ℝ) (not_le.mp hlt).le he.symm
  have h2 : (2 : ℤ) ∣ d := this ▸ dvd_mul_of_dvd_right (dvd_pow_self 2 (by omega)) c
  exact (Int.not_even_iff_odd.mpr hd) (even_iff_two_dvd.mpr h2)

theorem lsbOf_of_lsbAt {x : ℝ} {k : ℤ} (h : LsbAt x k) : lsbOf (.finite x) = k := by
  have hex : ∃ k, LsbAt x k := ⟨k, h⟩
  simp only [lsbOf, if_neg h.ne_zero, dif_pos hex]
  have hc := Classical.choose_spec hex
  rw [le_antisymm (hc.le h) (h.le hc)]

/-- A nonzero multiple of `2ᵏ` has its least significant digit at or above `k`. -/
theorem exists_lsbAt {x : ℝ} {z k : ℤ} (hx : x = z * 2 ^ k) (h0 : x ≠ 0) :
    ∃ j, k ≤ j ∧ LsbAt x j := by
  have hz : z ≠ 0 := by rintro rfl; exact h0 (by simpa using hx)
  obtain ⟨n, m, hm, hzm⟩ := Nat.exists_eq_two_pow_mul_odd (Int.natAbs_ne_zero.mpr hz)
  have hm' : Odd (m : ℤ) := (Int.odd_coe_nat m).mpr hm
  have e : ∀ c : ℤ, (c : ℝ) * 2 ^ k = (c / 2 ^ n : ℝ) * 2 ^ (k + n) := fun c => by
    rw [zpow_add₀ two_ne_zero, zpow_natCast]; field_simp
  refine ⟨k + n, by omega, ?_⟩
  rcases Int.natAbs_eq z with h | h
  · exact ⟨m, hm', by rw [hx, e, h, hzm]; push_cast; field_simp⟩
  · exact ⟨-m, hm'.neg, by rw [hx, e, h, hzm]; push_cast; field_simp⟩

theorem lsbOf_ne_top {x : ℝ} (h0 : x ≠ 0) : lsbOf (.finite x) ≠ ⊤ := by
  simp only [lsbOf, if_neg h0]
  split_ifs <;> simp

theorem coe_le_lsbOf {x : ℝ} {k : ℤ} : (k : EInt) ≤ lsbOf (.finite x) ↔ ∃ z : ℤ, x = z * 2 ^ k := by
  by_cases h0 : x = 0
  · simp [lsbOf, h0]
  constructor
  · intro hk
    by_cases hex : ∃ j, LsbAt x j
    · obtain ⟨j, c, hodd, hc⟩ := hex
      rw [lsbOf_of_lsbAt ⟨c, hodd, hc⟩, WithBotTop.coe_le_coe] at hk
      exact ⟨_, hc.trans (two_zpow_shift c hk)⟩
    · simp [lsbOf, h0, hex] at hk
  · rintro ⟨z, hz⟩
    obtain ⟨j, hj, hl⟩ := exists_lsbAt hz h0
    rw [lsbOf_of_lsbAt hl]
    exact WithBotTop.coe_le_coe.mpr hj

theorem msbOf_le_coe {x : ℝ} {k : ℤ} : msbOf (.finite x) ≤ k ↔ |x| < 2 ^ (k + 1) := by
  by_cases h0 : x = 0
  · rw [h0, abs_zero]; exact iff_of_true (by simp [msbOf]) (by positivity)
  simp only [msbOf, if_neg h0, WithBotTop.coe_le_coe]
  rw [← Int.lt_add_one_iff, ← Int.lt_zpow_iff_log_lt (by norm_num) (abs_pos.mpr h0)]
  norm_num

theorem msbOf_mono {x y : ℝ} (h : |x| ≤ |y|) : msbOf (.finite x) ≤ msbOf (.finite y) :=
  EInt.le_of_forall_le_coe fun _ hk => msbOf_le_coe.mpr (h.trans_lt (msbOf_le_coe.mp hk))

theorem lsbOf_neg_real (x : ℝ) : lsbOf (.finite (-x)) = lsbOf (.finite x) := by
  have key : ∀ y : ℝ, lsbOf (.finite y) ≤ lsbOf (.finite (-y)) := fun y =>
    EInt.le_of_forall_coe_le fun k hk => by
      obtain ⟨z, hz⟩ := coe_le_lsbOf.mp hk
      exact coe_le_lsbOf.mpr ⟨-z, by rw [hz]; push_cast; ring⟩
  exact le_antisymm (by simpa using key (-x)) (key x)

theorem lsbOf_abs_real (x : ℝ) : lsbOf (.finite |x|) = lsbOf (.finite x) := by
  rcases abs_choice x with h | h <;> rw [h]; exact lsbOf_neg_real x

/-! ## Table 2's operator intervals -/

theorem lsbOf_special (s : Special) : lsbOf (.special s) = ⊤ := rfl

theorem msbOf_special (s : Special) : msbOf (.special s) = ⊤ := rfl

theorem lsbOf_zero : lsbOf (.finite 0) = ⊤ := by simp [lsbOf]

theorem msbOf_zero : msbOf (.finite 0) = ⊥ := by simp [msbOf]

theorem msbOf_ne_bot {x : ℝ} (h0 : x ≠ 0) : msbOf (.finite x) ≠ ⊥ := by
  simp [msbOf, h0]

theorem msbOf_of_ne_zero {x : ℝ} (h0 : x ≠ 0) : msbOf (.finite x) = (Int.log 2 |x| : ℤ) := by
  simp [msbOf, h0]

theorem EInt.top_add {a : EInt} (h : a ≠ ⊥) : ⊤ + a = ⊤ := by
  cases a using WithBotTop.rec with
  | bot => exact absurd rfl h
  | coe k => rfl
  | top => rfl

theorem EInt.add_top {a : EInt} (h : a ≠ ⊥) : a + ⊤ = ⊤ := by
  rw [add_comm]; exact EInt.top_add h

theorem lsb_add (u v : Num) : min (lsbOf u) (lsbOf v) ≤ lsbOf (Num.add u v) := by
  cases h : Num.add u v with
  | special => exact le_top
  | finite =>
    obtain ⟨x, y, rfl, rfl, rfl⟩ := Num.add_eq_finite h
    refine EInt.le_of_forall_coe_le fun k hk => ?_
    obtain ⟨a, ha⟩ := coe_le_lsbOf.mp (hk.trans (min_le_left _ _))
    obtain ⟨b, hb⟩ := coe_le_lsbOf.mp (hk.trans (min_le_right _ _))
    exact coe_le_lsbOf.mpr ⟨a + b, by rw [ha, hb]; push_cast; ring⟩

theorem msb_add (u v : Num) :
    msbOf (Num.add u v) ≤ max (msbOf u) (msbOf v) + ((1 : ℤ) : EInt) := by
  rcases u with x | _ <;> rcases v with y | _
  · refine EInt.le_of_forall_le_coe fun k hk => ?_
    rw [EInt.add_coe_le_coe] at hk
    have hx := msbOf_le_coe.mp ((le_max_left _ _).trans hk)
    have hy := msbOf_le_coe.mp ((le_max_right _ _).trans hk)
    simp only [sub_add_cancel] at hx hy
    refine msbOf_le_coe.mpr ((abs_add_le x y).trans_lt ?_)
    rw [zpow_add_one₀ two_ne_zero]; linarith
  all_goals simp only [msbOf_special, max_eq_left, max_eq_right, le_top, EInt.top_add_coe]

theorem lsb_mul (u v : Num) : lsbOf u + lsbOf v ≤ lsbOf (Num.mul u v) := by
  cases h : Num.mul u v with
  | special => exact le_top
  | finite =>
    obtain ⟨x, y, rfl, rfl, rfl⟩ := Num.mul_eq_finite h
    by_cases hx : x = 0
    · simp [hx, lsbOf_zero]
    by_cases hy : y = 0
    · simp [hy, lsbOf_zero]
    refine EInt.le_of_forall_coe_le fun k hk => ?_
    cases ha : lsbOf (.finite x) using WithBotTop.rec with
    | bot => simp [ha] at hk
    | top => exact absurd ha (lsbOf_ne_top hx)
    | coe a =>
      cases hb : lsbOf (.finite y) using WithBotTop.rec with
      | bot => simp [ha, hb] at hk
      | top => exact absurd hb (lsbOf_ne_top hy)
      | coe b =>
        rw [ha, hb, coe_add_coe, WithBotTop.coe_le_coe] at hk
        obtain ⟨c, hc⟩ := coe_le_lsbOf.mp ha.ge
        obtain ⟨d, hd⟩ := coe_le_lsbOf.mp hb.ge
        rw [hc, hd, show (c : ℝ) * 2 ^ a * (d * 2 ^ b) = ((c * d : ℤ) : ℝ) * 2 ^ (a + b) by
          rw [zpow_add₀ two_ne_zero]; push_cast; ring]
        exact coe_le_lsbOf.mpr ⟨_, two_zpow_shift _ hk⟩

theorem msb_mul {u v : Num} (hn : Num.mul u v ≠ nan) :
    msbOf (Num.mul u v) ≤ msbOf u + msbOf v + ((1 : ℤ) : EInt) := by
  rcases u with x | s <;> rcases v with y | t
  · simp only [Num.mul]
    by_cases hx : x = 0
    · simp [hx, msbOf_zero]
    by_cases hy : y = 0
    · simp [hy, msbOf_zero]
    rw [msbOf_of_ne_zero hx, msbOf_of_ne_zero hy, coe_add_coe, coe_add_coe]
    refine msbOf_le_coe.mpr ?_
    have h₁ := msbOf_le_coe.mp (msbOf_of_ne_zero hx).le
    have h₂ := msbOf_le_coe.mp (msbOf_of_ne_zero hy).le
    rw [abs_mul, show Int.log 2 |x| + Int.log 2 |y| + 1 + 1 =
      (Int.log 2 |x| + 1) + (Int.log 2 |y| + 1) by ring, zpow_add₀ two_ne_zero]
    exact mul_lt_mul'' h₁ h₂ (abs_nonneg _) (abs_nonneg _)
  · have hx : x ≠ 0 := by rintro rfl; rcases t with _ | _ <;> simp [Num.mul] at hn
    rw [msbOf_special, EInt.add_top (msbOf_ne_bot hx)]; exact le_top
  · have hy : y ≠ 0 := by rintro rfl; rcases s with _ | _ <;> simp [Num.mul] at hn
    rw [msbOf_special, EInt.top_add (msbOf_ne_bot hy)]; exact le_top
  · rw [msbOf_special, msbOf_special, EInt.top_add WithBotTop.top_ne_bot]; exact le_top

@[simp] theorem lsbOf_neg (u : Num) : lsbOf (Num.neg u) = lsbOf u := by
  rcases u with x | _
  · exact lsbOf_neg_real x
  · rfl

@[simp] theorem msbOf_neg (u : Num) : msbOf (Num.neg u) = msbOf u := by
  rcases u with x | _
  · simp [Num.neg, msbOf]
  · rfl

@[simp] theorem lsbOf_abs (u : Num) : lsbOf (Num.abs u) = lsbOf u := by
  rcases u with x | (_ | _)
  · exact lsbOf_abs_real x
  all_goals rfl

@[simp] theorem msbOf_abs (u : Num) : msbOf (Num.abs u) = msbOf u := by
  rcases u with x | (_ | _)
  · simp [Num.abs, msbOf]
  all_goals rfl

/-- `2ᵉ` has its only digit at `e`, or none (`2^(−∞) = 0`). -/
theorem digits_exp2 (e : EInt) :
    e ≤ lsbOf (Num.exp2 (numOfE e)) ∧ msbOf (Num.exp2 (numOfE e)) ≤ e := by
  cases e using WithBotTop.rec with
  | bot => exact ⟨bot_le, by simp [Num.exp2, msbOf_zero]⟩
  | top => exact ⟨le_rfl, le_rfl⟩
  | coe k =>
    simp only [numOfE_coe, Num.exp2, Real.rpow_intCast]
    refine ⟨coe_le_lsbOf.mpr ⟨1, by simp⟩, msbOf_le_coe.mpr ?_⟩
    rw [abs_of_pos (zpow_pos two_pos _), zpow_add_one₀ two_ne_zero]
    linarith [zpow_pos (two_pos (α := ℝ)) k]

/-- `logb` returns an integer. -/
theorem lsb_logb (u : Num) : ((0 : ℤ) : EInt) ≤ lsbOf (Num.logb u) := by
  rcases u with x | (_ | _)
  · simp only [Num.logb]
    split_ifs
    · exact le_top
    · exact coe_le_lsbOf.mpr ⟨Int.log 2 |x|, by simp⟩
  all_goals exact le_top

end Fpy.DigitBound
