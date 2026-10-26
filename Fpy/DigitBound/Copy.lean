import Fpy.DigitBound.Basic

/-!
# D-Index's fresh copy

A fresh copy of a list element's abstract value renames its variables `[a, b)`
to `[n, n + (b − a))` (`shift`), and copies the constraints on them
(`copyCons`). For a numeric element it is an instance of `DVal.Copy`
(`copy_num`), so `xs[i]` keeps the list summary's bounds.
-/

namespace Fpy.DigitBound

/-- The renaming of `[a, b)` to `[n, n + (b − a))`. -/
def shift (a b n x : ℕ) : ℕ := if a ≤ x ∧ x < b then x - a + n else x

def Term.rename (f : ℕ → ℕ) : Term → Term
  | .const z => .const z
  | .var x => .var (f x)
  | .add s t => .add (s.rename f) (t.rename f)
  | .neg t => .neg (t.rename f)
  | .max s t => .max (s.rename f) (t.rename f)
  | .min s t => .min (s.rename f) (t.rename f)

theorem Term.eval_rename (f : ℕ → ℕ) (ι : Asgn) :
    ∀ t : Term, (t.rename f).eval ι = t.eval (ι ∘ f)
  | .const _ | .var _ => rfl
  | .add s t | .max s t | .min s t => by
    simp only [Term.rename, Term.eval, Term.eval_rename f ι s, Term.eval_rename f ι t]
  | .neg t => by simp only [Term.rename, Term.eval, Term.eval_rename f ι t]

theorem Term.Below.rename_shift {a b n : ℕ} (hab : a ≤ b) (hbn : b ≤ n) :
    ∀ {t : Term}, t.Below b → (t.rename (shift a b n)).Below (n + (b - a))
  | .const _, _ => trivial
  | .var x, hx => by
    have hx : x < b := hx
    change shift a b n x < _
    unfold shift
    split_ifs <;> omega
  | .add s t, ⟨hs, ht⟩ | .max s t, ⟨hs, ht⟩ | .min s t, ⟨hs, ht⟩ =>
    ⟨Term.Below.rename_shift hab hbn hs, Term.Below.rename_shift hab hbn ht⟩
  | .neg t, ht => Term.Below.rename_shift (t := t) hab hbn ht

theorem Term.Below.rename {f : ℕ → ℕ} {k k' : ℕ} (hf : ∀ x < k, f x < k') :
    ∀ {t : Term}, t.Below k → (t.rename f).Below k'
  | .const _, _ => trivial
  | .var x, hx => hf x hx
  | .add s t, ⟨hs, ht⟩ | .max s t, ⟨hs, ht⟩ | .min s t, ⟨hs, ht⟩ =>
    ⟨Term.Below.rename hf hs, Term.Below.rename hf ht⟩
  | .neg t, ht => Term.Below.rename (t := t) hf ht

def Atom.rename (f : ℕ → ℕ) (a : Atom) : Atom := ⟨a.lhs.rename f, a.rhs.rename f⟩

theorem Atom.holds_rename (f : ℕ → ℕ) (ι : Asgn) (a : Atom) :
    (a.rename f).Holds ι ↔ a.Holds (ι ∘ f) := by
  simp only [Atom.Holds, Atom.rename, Term.eval_rename]

/-- A constraint on `[a, b)`'s variable `c.head`, copied to `shift`'s range. -/
def Con.copy (c : Con) (a b n : ℕ) (hc : a ≤ c.head ∧ c.head < b) (han : a ≤ n) : Con where
  head := c.head - a + n
  atoms := c.atoms.map (Atom.rename (shift a b n))
  below e ha := by
    obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha
    have hf : ∀ x < c.head + 1, shift a b n x < c.head - a + n + 1 := fun x hx => by
      unfold shift; split_ifs <;> omega
    exact ⟨(c.below a₀ ha₀).1.rename hf, (c.below a₀ ha₀).2.rename hf⟩
  sat ι := by
    obtain ⟨z, hz⟩ := c.sat (ι ∘ shift a b n)
    refine ⟨z, fun e ha => ?_⟩
    obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha
    refine (Atom.holds_rename _ _ _).mpr (c.dep (ι := Function.update (ι ∘ shift a b n) c.head z)
      (fun x hx => ?_) hz a₀ ha₀)
    simp only [Function.comp_apply, Function.update_apply]
    unfold shift
    split_ifs <;> first | rfl | omega

theorem Con.P_copy {c : Con} {a b n : ℕ} {hc : a ≤ c.head ∧ c.head < b} {han : a ≤ n}
    {ι : Asgn} : (c.copy a b n hc han).P ι ↔ c.P (ι ∘ shift a b n) := by
  simp only [Con.P, Con.copy, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Atom.holds_rename]

/-- The constraints of `Ψ` on `[a, b)`, copied to `shift`'s range. -/
def copyCons (Ψ : List Con) (a b n : ℕ) (han : a ≤ n) : List Con :=
  Ψ.filterMap fun c => if h : a ≤ c.head ∧ c.head < b then some (c.copy a b n h han) else none

theorem mem_copyCons {Ψ : List Con} {a b n : ℕ} {han : a ≤ n} {c' : Con}
    (h : c' ∈ copyCons Ψ a b n han) :
    ∃ c ∈ Ψ, ∃ hc : a ≤ c.head ∧ c.head < b, c' = c.copy a b n hc han := by
  obtain ⟨c, hc, h⟩ := List.mem_filterMap.mp h
  split_ifs at h with hc'
  exact ⟨c, hc, hc', (Option.some.inj h).symm⟩

theorem fresh_copyCons {a b n : ℕ} (hab : a ≤ b) (hbn : b ≤ n) :
    ∀ {Ψ : List Con}, (Ψ.map Con.head).Nodup →
      Fresh n (n + (b - a)) (copyCons Ψ a b n (hab.trans hbn))
  | [], _ => Fresh.nil n |>.mono_right (by omega)
  | c :: Ψ, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have ih := fresh_copyCons hab hbn hnd.2
    unfold copyCons
    rw [List.filterMap_cons]
    split_ifs with hc
    · refine ⟨by omega, ?_, fun c' h => ?_⟩
      · rw [List.map_cons, List.nodup_cons]
        refine ⟨fun h => ?_, ih.2.1⟩
        obtain ⟨c', hc', he⟩ := List.mem_map.mp h
        obtain ⟨c₀, hc₀, hc₀', rfl⟩ := mem_copyCons hc'
        simp only [Con.copy] at he
        exact hnd.1 (List.mem_map.mpr ⟨c₀, hc₀, by omega⟩)
      · rcases List.mem_cons.mp h with rfl | h
        · simp only [Con.copy]; omega
        · exact ih.2.2 c' h
    · exact ih

/-- **D-Index's copy** of a numeric element: its variables `[a, b)` renamed to
`[n, n + (b − a))`, with the constraints of `Ψg` on them copied. -/
theorem copy_num {Ψg : List Con} {a b n : ℕ} {l m : Term} {τ : Option Term} (hab : a ≤ b)
    (hbn : b ≤ n) (hl : l.Below b) (hm : m.Below b) (hτ : ∀ t ∈ τ, t.Below b) :
    DVal.Copy n (n + (b - a)) Ψg (copyCons Ψg a b n (hab.trans hbn)) (.num l m τ) a
      (.num (l.rename (shift a b n)) (m.rename (shift a b n))
        (τ.map (Term.rename (shift a b n)))) := by
  intro _ ι ι₀ v _ h₀ hs₀ hd
  let ι' : Asgn := fun x => if n ≤ x ∧ x < n + (b - a) then ι₀ (x - n + a) else ι x
  have key : ∀ x < b, ι' (shift a b n x) = ι₀ x := by
    intro x hx
    by_cases ha : a ≤ x
    · have hs : shift a b n x = x - a + n := if_pos ⟨ha, hx⟩
      simp only [ι', hs]
      rw [if_pos (by omega)]
      congr 1; omega
    · have hs : shift a b n x = x := if_neg (by omega)
      simp only [ι', hs]
      rw [if_neg (by omega)]
      exact h₀ x (by omega)
  have hev : ∀ t : Term, t.Below b → (t.rename (shift a b n)).eval ι' = t.eval ι₀ := fun t ht =>
    (Term.eval_rename _ _ t).trans (Term.eval_congr (fun x hx => key x hx) ht)
  refine ⟨ι', fun x hx => ?_, fun c hc => ?_, ?_⟩
  · simp only [ι']
    rw [if_neg (by omega)]
  · obtain ⟨c₀, hc₀, hc₀', rfl⟩ := mem_copyCons hc
    exact Con.P_copy.mpr (c₀.dep (fun x hx => (key x (by omega)).symm) (hs₀ c₀ hc₀))
  · cases hd with
    | num hu =>
      refine .num (hu.imp id fun ⟨hl', hm', ht'⟩ => ⟨?_, ?_, fun t ht => ?_⟩)
      · rw [hev l hl, hl']
      · rw [hev m hm, hm']
      · obtain ⟨t₀, ht₀, rfl⟩ := Option.mem_map.mp ht
        rw [hev t₀ (hτ t₀ ht₀), ht' t₀ ht₀]

end Fpy.DigitBound
