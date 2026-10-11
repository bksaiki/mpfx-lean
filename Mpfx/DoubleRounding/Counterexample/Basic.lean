import Mpfx.Rounding.Op
import Mpfx.Rounding.Ulp

/-!
# Double-rounding counterexamples: grid facts

The format-generic facts the counterexamples are built from. Every format is
discrete away from zero (`exists_isolated`), so a positive value has an
adjacent predecessor (`exists_pred`) whose parity alternates with it
(`alternate_of_adjacent`). A rounding of a point close to an isolated value
lands on it (`roundsDown_of_isolated`, …), and nearest-even rounding between
adjacent values is read off the midpoint (`roundsRNE_of_bracket`).
-/

namespace Mpfx

namespace Cex

/-! ## Isolation -/

/-- No value of `F` other than `m` lies within `2^K` of `m`. -/
def Isolated (F : FiniteFormat) (m : Dyadic) (K : ℤ) : Prop :=
  ∀ v ∈ F.unbounded, |(v : ℝ) - m| < (2 : ℝ) ^ K → v = m

theorem Isolated.mono {F : FiniteFormat} {m : Dyadic} {K K' : ℤ} (h : Isolated F m K)
    (hK : K' ≤ K) : Isolated F m K' :=
  fun v hv hlt => h v hv (hlt.trans_le (zpow_le_zpow_right₀ (by norm_num) hK))

/-- Any other value of `F` is at least `2^K` from `m`. -/
theorem Isolated.le_abs_sub {F : FiniteFormat} {m : Dyadic} {K : ℤ} (h : Isolated F m K)
    {v : Dyadic} (hv : v ∈ F.unbounded) (hne : v ≠ m) : (2 : ℝ) ^ K ≤ |(v : ℝ) - m| :=
  not_lt.mp fun hlt => hne (h v hv hlt)

/-- `c · 2^a` is an integer multiple of `2^K` for `K ≤ a`. -/
private theorem exists_mul_zpow_of_le (c : ℤ) {a K : ℤ} (h : K ≤ a) :
    ∃ n : ℤ, (c : ℝ) * (2 : ℝ) ^ a = (n : ℝ) * (2 : ℝ) ^ K := by
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr h)
  refine ⟨c * 2 ^ k, ?_⟩
  rw [show a = K + k by omega, zpow_add₀ two_ne_zero, zpow_natCast]
  push_cast; ring

/-- **Discreteness away from zero.** Every format is isolated at every nonzero
dyadic `m`: its values of magnitude at least `|m|/2` share a quantum, fixed by
the precision or else by the minimum quantum, and `m` has one too. -/
theorem exists_isolated (F : FiniteFormat) {m : Dyadic} (hm : (m : ℝ) ≠ 0) :
    ∃ K : ℤ, Isolated F m K := by
  obtain ⟨cm, j, hcm⟩ := m.property
  have hm_eq : (m : ℝ) = (cm : ℝ) * (2 : ℝ) ^ j := by
    rw [Dyadic.coe_real_eq_ratCast, hcm]; push_cast; ring
  set E : ℤ := Int.log 2 |(m : ℝ)| - 1 with hE
  have hmE : (2 : ℝ) ^ (E + 1) ≤ |(m : ℝ)| := by
    rw [hE, sub_add_cancel]
    exact Int.zpow_log_le_self (b := 2) (by norm_num) (abs_pos.mpr hm)
  -- Values of magnitude at least `2^E` are multiples of a common `2^k`.
  obtain ⟨k, hk⟩ : ∃ k : ℤ, ∀ v ∈ F.unbounded, (2 : ℝ) ^ E ≤ |(v : ℝ)| →
      ∃ c : ℤ, (v : ℝ) = (c : ℝ) * (2 : ℝ) ^ k := by
    cases hp : F.p using ENat.recTopCoe with
    | top =>
      cases he : F.exp using QExp.recBotCoe with
      | bot => exact (F.finite.elim (· hp) (· he)).elim
      | coe e =>
        refine ⟨e, fun v hv _ => ?_⟩
        have hq : Dyadic.quantumAtLeast F.exp v := hv.2.1
        rw [he] at hq
        exact (Dyadic.quantumAtLeast_coe_real e v).mp hq
    | coe q =>
      refine ⟨E - q + 1, fun v hv hvE => ?_⟩
      have hpv : Dyadic.precisionAtMost F.p v := hv.1
      rw [hp] at hpv
      obtain ⟨c, e, hce, hc⟩ := (Dyadic.precisionAtMost_coe_real q v).mp hpv
      -- `|v| < 2^(q + e)`, so `E < q + e`.
      have h_lt : (2 : ℝ) ^ E < (2 : ℝ) ^ ((q : ℤ) + e) := by
        refine hvE.trans_lt ?_
        rw [hce, abs_mul, abs_of_pos (zpow_pos two_pos e : (0 : ℝ) < 2 ^ e), zpow_add₀ two_ne_zero,
          zpow_natCast]
        exact mul_lt_mul_of_pos_right (by exact_mod_cast hc) (zpow_pos two_pos e)
      have he : E - q + 1 ≤ e := by
        have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp h_lt
        omega
      rw [hce]
      exact exists_mul_zpow_of_le c he
  refine ⟨min (min j k) E, fun v hv hlt => ?_⟩
  set K := min (min j k) E
  have hKE : (2 : ℝ) ^ K ≤ (2 : ℝ) ^ E := zpow_le_zpow_right₀ (by norm_num) (min_le_right _ _)
  have hE1 : (2 : ℝ) ^ (E + 1) = 2 * (2 : ℝ) ^ E := by rw [zpow_add_one₀ two_ne_zero]; ring
  -- `v` is within `2^E` of `m`, so `|v| ≥ 2^E`.
  have hvE : (2 : ℝ) ^ E ≤ |(v : ℝ)| := by
    have := abs_sub_abs_le_abs_sub (m : ℝ) v
    rw [abs_sub_comm] at this
    linarith
  obtain ⟨cv, hcv⟩ := hk v hv hvE
  obtain ⟨n₁, hn₁⟩ := exists_mul_zpow_of_le cv
    (show K ≤ k from (min_le_left _ _).trans (min_le_right _ _))
  obtain ⟨n₂, hn₂⟩ := exists_mul_zpow_of_le cm
    (show K ≤ j from (min_le_left _ _).trans (min_le_left _ _))
  have hdiff : (v : ℝ) - m = ((n₁ - n₂ : ℤ) : ℝ) * (2 : ℝ) ^ K := by
    rw [hcv, hm_eq, hn₁, hn₂]; push_cast; ring
  rw [hdiff, abs_mul, abs_of_pos (zpow_pos two_pos K : (0 : ℝ) < 2 ^ K)] at hlt
  have h0 : n₁ - n₂ = 0 := by
    have h1 : |((n₁ - n₂ : ℤ) : ℝ)| < 1 := (mul_lt_iff_lt_one_left (zpow_pos two_pos K)).mp hlt
    exact Int.abs_lt_one_iff.mp (by exact_mod_cast h1)
  apply Dyadic.ext_real
  have : (v : ℝ) - m = 0 := by rw [hdiff, h0]; simp
  linarith

/-- Two formats are isolated at a positive dyadic `m` with a common `K`, small
enough that `2^K ≤ m`. -/
theorem exists_isolated₂ (F G : FiniteFormat) {m : Dyadic} (hm : (0 : ℝ) < m) :
    ∃ K : ℤ, Isolated F m K ∧ Isolated G m K ∧ (2 : ℝ) ^ K ≤ m := by
  obtain ⟨K₁, h₁⟩ := exists_isolated F hm.ne'
  obtain ⟨K₂, h₂⟩ := exists_isolated G hm.ne'
  refine ⟨min (min K₁ K₂) (Int.log 2 (m : ℝ)), h₁.mono ((min_le_left _ _).trans (min_le_left _ _)),
    h₂.mono ((min_le_left _ _).trans (min_le_right _ _)), ?_⟩
  exact (zpow_le_zpow_right₀ (by norm_num) (min_le_right _ _)).trans
    (Int.zpow_log_le_self (b := 2) (by norm_num) hm)

/-! ## Adjacency and parity -/

/-- `u < u'` are adjacent values of `F`: nothing of `F` lies strictly between. -/
def Adjacent (F : FiniteFormat) (u u' : Dyadic) : Prop :=
  u ∈ F.unbounded ∧ u' ∈ F.unbounded ∧ (u : ℝ) < u' ∧
    ∀ v ∈ F.unbounded, (v : ℝ) < u' → (v : ℝ) ≤ u

/-- A positive value of `F` has an adjacent predecessor `u ≥ 0`. -/
theorem exists_pred (F : FiniteFormat) {a : Dyadic} (ha : a ∈ F.unbounded)
    (ha_pos : (0 : ℝ) < a) : ∃ u : Dyadic, Adjacent F u a ∧ 0 ≤ (u : ℝ) := by
  obtain ⟨K, hK, -, hK_le⟩ := exists_isolated₂ F F ha_pos
  have hK_pos : (0 : ℝ) < (2 : ℝ) ^ K := zpow_pos two_pos K
  set x₀ : ℝ := (a : ℝ) - (2 : ℝ) ^ K / 2 with hx₀
  refine ⟨rndDown F x₀, ⟨rndDown_mem F x₀, ha, (rndDown_le F x₀).trans_lt (by linarith),
    fun v hv hva => rndDown_max F x₀ hv (not_lt.mp fun hgt => ?_)⟩,
    RoundsFinite.toNegative_nonneg (by linarith) (rndDown_spec F x₀)⟩
  have := hK v hv (abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩)
  rw [this] at hva
  exact lt_irrefl _ hva

/-- Adjacent values alternate in parity: exactly one is odd, and one is even. -/
theorem alternate_of_adjacent (F : ParityFormat) {u u' : Dyadic}
    (h : Adjacent F.toFiniteFormat u u') :
    (F.IsOdd u' ↔ ¬ F.IsOdd u) ∧ (¬ F.IsEven u → F.IsEven u') := by
  obtain ⟨hu, hu', hlt, hadj⟩ := h
  set x : ℝ := ((u : ℝ) + u') / 2 with hx
  have hdown : RoundsFinite F.unbounded.unbounded .toNegative x u :=
    ⟨hu, by linarith, fun v hv hvx => hadj v hv (by linarith)⟩
  have hup : RoundsFinite F.unbounded.unbounded .toPositive x u' :=
    ⟨hu', by linarith, fun v hv hxv => not_lt.mp fun hv' => by linarith [hadj v hv hv']⟩
  obtain ⟨hodd, heven⟩ := alternate_of_bracketing (F := F.unbounded)
    (F.not_isUndefined .toOdd) hdown hup (by linarith)
  refine ⟨⟨fun h₁ h₂ => hodd.mp (h₁.congr rfl rfl) (h₂.congr rfl rfl),
    fun h₁ => (hodd.mpr fun h₂ => h₁ (h₂.congr rfl rfl)).congr rfl rfl⟩,
    fun h₁ => (heven fun h₂ => h₁ (h₂.congr rfl rfl)).congr rfl rfl⟩

/-- `F`'s parity witness for the nearest-even spec on `F.unbounded`. -/
theorem isEven_witness (F : ParityFormat) {y : Dyadic} (h : F.IsEven y) :
    ∃ F' : ParityFormat, F'.toFormat = F.unbounded.toFormat ∧ F'.IsEven y :=
  ⟨⟨F.unbounded, F.parity⟩, rfl, h.congr rfl rfl⟩

/-- A round-to-odd result off its input is odd in `F`. -/
theorem isOdd_of_roundsRTO (F : ParityFormat) {x : ℝ} {y : Dyadic}
    (h : RoundsFinite F.unbounded .toOdd x y) (hne : x ≠ (y : ℝ)) : F.IsOdd y := by
  obtain ⟨F', hF', hodd⟩ := h.2.2 hne
  exact hodd.congr (congrArg Format.p hF' :) (congrArg Format.exp hF' :)

/-! ## Roundings near an isolated value -/

/-- A point at most `2^K` above an isolated value `h` rounds down onto it. -/
theorem roundsDown_of_isolated {F : FiniteFormat} {h : Dyadic} {K : ℤ} (hK : Isolated F h K)
    (hh : h ∈ F.unbounded) {x : ℝ} (hx : (h : ℝ) ≤ x) (hx' : x < h + (2 : ℝ) ^ K) :
    RoundsFinite F.unbounded .toNegative x h :=
  ⟨hh, hx, fun v hv hvx => not_lt.mp fun hlt => by
    have := hK v hv (abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩)
    rw [this] at hlt
    exact lt_irrefl _ hlt⟩

/-- A point at most `2^K` below an isolated value `h` rounds up onto it. -/
theorem roundsUp_of_isolated {F : FiniteFormat} {h : Dyadic} {K : ℤ} (hK : Isolated F h K)
    (hh : h ∈ F.unbounded) {x : ℝ} (hx : (h : ℝ) - (2 : ℝ) ^ K < x) (hx' : x ≤ h) :
    RoundsFinite F.unbounded .toPositive x h :=
  ⟨hh, hx', fun v hv hxv => not_lt.mp fun hlt => by
    have := hK v hv (abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩)
    rw [this] at hlt
    exact lt_irrefl _ hlt⟩

/-- A point within `2^K / 2` of an isolated value `h` rounds nearest onto it,
with no tie. -/
theorem roundsRNE_of_isolated {F : FiniteFormat} {h : Dyadic} {K : ℤ} (hK : Isolated F h K)
    (hh : h ∈ F.unbounded) {x : ℝ} (hx : |x - h| < (2 : ℝ) ^ K / 2) :
    RoundsFinite F.unbounded (.nearest .toEven) x h := by
  -- Every other value is strictly farther from `x` than `h` is.
  have hfar : ∀ v ∈ F.unbounded, v ≠ h → |x - h| < |x - v| := fun v hv hne => by
    have h₁ := hK.le_abs_sub hv hne
    have h₂ := abs_sub_le (v : ℝ) x h
    rw [abs_sub_comm (v : ℝ) x] at h₂
    linarith
  have hfy : IsFaithfulRound F.unbounded x h := by
    rcases le_total (h : ℝ) x with hhx | hxh
    · refine Or.inl ⟨hh, hhx, fun v hv hvx => not_lt.mp fun hlt => ?_⟩
      have := hfar v hv (fun e => by rw [e] at hlt; exact lt_irrefl _ hlt)
      rw [abs_of_nonneg (by linarith : 0 ≤ x - h), abs_of_nonneg (by linarith : 0 ≤ x - v)]
        at this
      linarith
    · refine Or.inr ⟨hh, hxh, fun v hv hxv => not_lt.mp fun hlt => ?_⟩
      have := hfar v hv (fun e => by rw [e] at hlt; exact lt_irrefl _ hlt)
      rw [abs_of_nonpos (by linarith : x - h ≤ 0), abs_of_nonpos (by linarith : x - v ≤ 0)]
        at this
      linarith
  refine ⟨hh, hfy, fun v hv _ => ?_, fun ⟨v, hv, _, hne, heq⟩ => ?_⟩
  · by_cases hne : v = h
    · rw [hne]
    · exact (hfar v hv hne).le
  · exact absurd heq (hfar v hv hne).ne

/-- A round-down of a point less than `2^K` above an isolated `m` is at most
`m`, whether or not `m` is a value. -/
theorem le_of_roundsDown_of_isolated {F : FiniteFormat} {m : Dyadic} {K : ℤ}
    (hK : Isolated F m K) {x : ℝ} {z : Dyadic} (hz : RoundsFinite F.unbounded .toNegative x z)
    (hx : x < m + (2 : ℝ) ^ K) : (z : ℝ) ≤ m :=
  not_lt.mp fun hlt => by
    have hzx := hz.2.1
    have := hK z hz.1 (abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩)
    rw [this] at hlt
    exact lt_irrefl _ hlt

/-- A round-up of a point less than `2^K` below an isolated `m` is at least
`m`. -/
theorem le_of_roundsUp_of_isolated {F : FiniteFormat} {m : Dyadic} {K : ℤ}
    (hK : Isolated F m K) {x : ℝ} {z : Dyadic} (hz : RoundsFinite F.unbounded .toPositive x z)
    (hx : (m : ℝ) - (2 : ℝ) ^ K < x) : (m : ℝ) ≤ z :=
  not_lt.mp fun hlt => by
    have hzx := hz.2.1
    have := hK z hz.1 (abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩)
    rw [this] at hlt
    exact lt_irrefl _ hlt

/-! ## Nearest-even rounding between adjacent values -/

/-- Between adjacent values `u < u'`, nearest-even rounding returns the nearer
one, and on a tie the even one. -/
theorem roundsRNE_of_bracket {F : FiniteFormat} {u u' y : Dyadic} {z : ℝ}
    (h : Adjacent F u u') (hzu : (u : ℝ) ≤ z) (hzu' : z ≤ (u' : ℝ)) (hy : y = u ∨ y = u')
    (hclose : |z - y| ≤ |z - u| ∧ |z - y| ≤ |z - u'|)
    (htie : |z - u| = |z - u'| →
      ∃ F' : ParityFormat, F'.toFormat = F.unbounded.toFormat ∧ F'.IsEven y) :
    RoundsFinite F.unbounded (.nearest .toEven) z y := by
  obtain ⟨hu, hu', hlt, hadj⟩ := h
  -- The faithful roundings of `z` are `u` and `u'`.
  have hfaith : ∀ c : Dyadic, IsFaithfulRound F.unbounded z c → c = u ∨ c = u' := by
    rintro c (⟨hc, hcz, hmax⟩ | ⟨hc, hzc, hmin⟩)
    · rcases (hcz.trans hzu').lt_or_eq with h | h
      · exact Or.inl (Dyadic.ext_real (le_antisymm (hadj c hc h) (hmax u hu hzu)))
      · exact Or.inr (Dyadic.ext_real h)
    · rcases (hmin u' hu' hzu').lt_or_eq with h | h
      · exact Or.inl (Dyadic.ext_real (le_antisymm (hadj c hc h) (hzu.trans hzc)))
      · exact Or.inr (Dyadic.ext_real h)
  have hfy : IsFaithfulRound F.unbounded z y := by
    rcases hy with rfl | rfl
    · refine Or.inl ⟨hu, hzu, fun v hv hvz => ?_⟩
      rcases (hvz.trans hzu').lt_or_eq with h | h
      · exact hadj v hv h
      · -- `z = u'`, strictly nearer to `u'` than to `y`.
        have hz : z = u' := le_antisymm hzu' (h ▸ hvz)
        have := hclose.2
        rw [hz, sub_self, abs_zero, abs_nonpos_iff, sub_eq_zero] at this
        linarith
    · refine Or.inr ⟨hu', hzu', fun v hv hzv => not_lt.mp fun h => ?_⟩
      have hz : z = u := le_antisymm (hzv.trans (hadj v hv h)) hzu
      have := hclose.1
      rw [hz, sub_self, abs_zero, abs_nonpos_iff, sub_eq_zero] at this
      linarith
  refine ⟨hfy.elim (·.1) (·.1), hfy, fun c _ hc => ?_, fun ⟨c, _, hc, hne, heq⟩ => htie ?_⟩
  · rcases hfaith c hc with rfl | rfl
    exacts [hclose.1, hclose.2]
  · rcases hfaith c hc with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hne
    · exact heq.symm
    · exact heq
    · exact absurd rfl hne

end Cex

end Mpfx
