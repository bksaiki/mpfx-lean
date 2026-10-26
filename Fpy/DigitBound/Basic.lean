import Fpy.DigitBound.Defs

/-!
# Lemmas for the digit-bound analysis

Any fresh range's constraints can be satisfied by re-choosing its variables
(`Sat.extend`); descriptions depend only on the variables below a bound, and
survive new constraints on fresh variables (`Describes.grow`); and symbolic
values follow FPy's `+`, `−`, `max`, `min` and `logb` through `numOfE`.
-/

namespace Fpy.DigitBound

open Mpfx

/-! ## Bounds on variables -/

theorem SCtx.Below.mono {n n' : ℕ} (h : n ≤ n') : ∀ {C : SCtx}, C.Below n → C.Below n'
  | .real, _ => trivial
  | .record _, hC => fun f hf => (hC f hf).mono h

mutual

theorem DVal.Below.mono {n n' : ℕ} (h : n ≤ n') : ∀ {d : DVal}, d.Below n → d.Below n'
  | .num _ _ _, ⟨hl, hm, hτ⟩ => ⟨hl.mono h, hm.mono h, fun t ht => (hτ t ht).mono h⟩
  | .list _ _, ⟨ha, hd⟩ => ⟨ha.trans h, DVal.Below.mono h hd⟩
  | .record _, hfs => DVal.BelowFields.mono h hfs
  | .other, _ => trivial
  | .ctx _, hC => SCtx.Below.mono h hC

theorem DVal.BelowFields.mono {n n' : ℕ} (h : n ≤ n') :
    ∀ {fs : List (Label × DVal)}, DVal.BelowFields n fs → DVal.BelowFields n' fs
  | [], _ => trivial
  | (_, _) :: _, ⟨hd, hfs⟩ => ⟨DVal.Below.mono h hd, DVal.BelowFields.mono h hfs⟩

end

theorem DEnv.Below.mono {n n' : ℕ} (h : n ≤ n') {Δ : DEnv} (hΔ : Δ.Below n) : Δ.Below n' :=
  fun x d hx => (hΔ x d hx).mono h

theorem RetBelow.mono {n n' : ℕ} (h : n ≤ n') {a : Option DVal} (ha : RetBelow n a) :
    RetBelow n' a := fun d hd => (ha d hd).mono h

theorem CtxBelow.mono {n n' : ℕ} (h : n ≤ n') {κ : Option SCtx} (hκ : CtxBelow n κ) :
    CtxBelow n' κ := fun C hC => (hκ C hC).mono h

theorem DVal.BelowFields.lookup {n : ℕ} {l : Label} {d : DVal} :
    ∀ {fs : List (Label × DVal)}, DVal.BelowFields n fs → fs.lookup l = some d → d.Below n
  | [], _, h => by simp [List.lookup] at h
  | (l', d') :: fs, ⟨hd, hfs⟩, h => by
    by_cases hl : l = l'
    · subst hl
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h
      exact h ▸ hd
    · have hne : (l == l') = false := by simpa using hl
      simp only [List.lookup, hne] at h
      exact DVal.BelowFields.lookup hfs h

theorem DEnv.Below.update {n : ℕ} {Δ : DEnv} (hΔ : Δ.Below n) (x : Var) {d : DVal}
    (hd : d.Below n) : (Δ.update x d).Below n := by
  intro z d' hz
  by_cases hzx : z = x
  · subst hzx
    simp only [DEnv.update, Function.update_self, Option.some.injEq] at hz
    exact hz ▸ hd
  · simp only [DEnv.update, Function.update_of_ne hzx] at hz
    exact hΔ z d' hz

theorem DEnv.Below.single {n : ℕ} {y : Var} {d : DVal} (hd : d.Below n) :
    (DEnv.single y d).Below n := by
  intro z d' hz
  by_cases hzy : z = y
  · subst hzy
    simp only [DEnv.single, if_pos, Option.some.injEq] at hz
    exact hz ▸ hd
  · simp [DEnv.single, hzy] at hz

/-! ## Agreement -/

theorem Agree.mono {n n' : ℕ} (h : n ≤ n') {ι ι' : Asgn} (hι : Agree n' ι ι') : Agree n ι ι' :=
  fun x hx => hι x (lt_of_lt_of_le hx h)

theorem Agree.trans {n : ℕ} {ι₁ ι₂ ι₃ : Asgn} (h₁ : Agree n ι₁ ι₂) (h₂ : Agree n ι₂ ι₃) :
    Agree n ι₁ ι₃ := fun x hx => (h₁ x hx).trans (h₂ x hx)

theorem Agree.refl (n : ℕ) (ι : Asgn) : Agree n ι ι := fun _ _ => rfl

theorem AgreeOut.agree {n₀ n₁ : ℕ} {ι ι' : Asgn} (h : AgreeOut n₀ n₁ ι ι') : Agree n₀ ι ι' :=
  fun x hx => (h x (.inl hx)).symm

theorem AgreeOut.trans {n₀ n₁ n₂ : ℕ} {ι₀ ι₁ ι₂ : Asgn} (h₀₁ : n₀ ≤ n₁) (h₁₂ : n₁ ≤ n₂)
    (a₁ : AgreeOut n₀ n₁ ι₀ ι₁) (a₂ : AgreeOut n₁ n₂ ι₁ ι₂) : AgreeOut n₀ n₂ ι₀ ι₂ := fun z hz => by
  rcases hz with hz | hz
  · rw [a₂ z (.inl (by omega)), a₁ z (.inl hz)]
  · rw [a₂ z (.inr hz), a₁ z (.inr (by omega))]

theorem NumIn.congr {n : ℕ} {ι ι' : Asgn} (h : Agree n ι ι') {l m : Term} {τ : Option Term}
    {u : Num} (hl : l.Below n) (hm : m.Below n) (hτ : ∀ t ∈ τ, t.Below n) (hu : NumIn ι l m τ u) :
    NumIn ι' l m τ u := by
  rcases hu with hu | ⟨hlu, hmu, htu⟩
  · exact .inl hu
  · refine .inr ⟨?_, ?_, fun t ht => ?_⟩
    · rw [hlu, Term.eval_congr h hl]
    · rw [hmu, Term.eval_congr h hm]
    · rw [htu t ht, Term.eval_congr h (hτ t ht)]

theorem SCtx.Admits.congr {n : ℕ} {ι ι' : Asgn} (h : Agree n ι ι') :
    ∀ {C : SCtx} {v : Val}, C.Below n → C.Admits ι v → C.Admits ι' v
  | .real, _, _, hv => hv
  | .record fs, _, hC, ⟨vs, rfl, hvs⟩ => by
    refine ⟨vs, rfl, ?_⟩
    revert hC
    induction hvs with
    | nil => exact fun _ => .nil
    | cons hfw _ ih =>
      intro hC
      refine .cons ⟨hfw.1, ?_⟩ (ih fun f hf => hC f (List.mem_cons_of_mem _ hf))
      rw [← Term.eval_congr h (hC _ (List.mem_cons_self ..))]
      exact hfw.2

theorem admits_congr {n : ℕ} {ι ι' : Asgn} (h : Agree n ι ι') {κ : Option SCtx} {C : Val}
    (hκ : CtxBelow n κ) (hC : ∀ K ∈ κ, K.Admits ι C) : ∀ K ∈ κ, K.Admits ι' C :=
  fun K hK => (hC K hK).congr h (hκ K hK)

/-! ## Constraints -/

theorem Sat.append {ι : Asgn} {Ψ Ψ' : List Con} (h : Sat ι Ψ) (h' : Sat ι Ψ') :
    Sat ι (Ψ ++ Ψ') := fun c hc => (List.mem_append.mp hc).elim (h c) (h' c)

theorem Sat.left {ι : Asgn} {Ψ Ψ' : List Con} (h : Sat ι (Ψ ++ Ψ')) : Sat ι Ψ :=
  fun c hc => h c (List.mem_append_left _ hc)

theorem Sat.right {ι : Asgn} {Ψ Ψ' : List Con} (h : Sat ι (Ψ ++ Ψ')) : Sat ι Ψ' :=
  fun c hc => h c (List.mem_append_right _ hc)

theorem Fresh.nil (n : ℕ) : Fresh n n [] :=
  ⟨le_rfl, List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩

theorem Fresh.le {n₀ n₁ : ℕ} {Ψ : List Con} (h : Fresh n₀ n₁ Ψ) : n₀ ≤ n₁ := h.1

theorem Fresh.mono_right {n₀ n₁ n₂ : ℕ} {Ψ : List Con} (h : Fresh n₀ n₁ Ψ) (h₁₂ : n₁ ≤ n₂) :
    Fresh n₀ n₂ Ψ :=
  ⟨h.1.trans h₁₂, h.2.1, fun c hc => ⟨(h.2.2 c hc).1, lt_of_lt_of_le (h.2.2 c hc).2 h₁₂⟩⟩

theorem Fresh.single (n : ℕ) {c : Con} (hc : c.head = n) : Fresh n (n + 1) [c] :=
  ⟨Nat.le_succ n, List.nodup_singleton _, fun c' h => by
    obtain rfl := List.mem_singleton.mp h
    omega⟩

theorem Fresh.append {n₀ n₁ n₂ : ℕ} {Ψ Ψ' : List Con} (h : Fresh n₀ n₁ Ψ) (h' : Fresh n₁ n₂ Ψ') :
    Fresh n₀ n₂ (Ψ ++ Ψ') := by
  obtain ⟨h₀₁, hn, hr⟩ := h
  obtain ⟨h₁₂, hn', hr'⟩ := h'
  refine ⟨h₀₁.trans h₁₂, ?_, fun c hc => ?_⟩
  · rw [List.map_append]
    refine List.Nodup.append hn hn' (List.disjoint_left.mpr fun _ hx hx' => ?_)
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    obtain ⟨c', hc', he⟩ := List.mem_map.mp hx'
    have := (hr c hc).2
    have := (hr' c' hc').1
    omega
  · rcases List.mem_append.mp hc with hc | hc
    · exact ⟨(hr c hc).1, by have := (hr c hc).2; omega⟩
    · exact ⟨by have := (hr' c hc).1; omega, (hr' c hc).2⟩

/-- **Re-choosing fresh variables.** The constraints of a fresh range are
satisfied by re-choosing its variables in head order, keeping those below. -/
theorem Sat.extend {n₀ n₁ : ℕ} {Ψ : List Con} (hΨ : Fresh n₀ n₁ Ψ) (ι : Asgn) :
    ∃ ι', Agree n₀ ι ι' ∧ Sat ι' Ψ := by
  -- Downward induction on `j`: the constraints with heads below `j` hold.
  have key : ∀ k j, n₁ - j = k → ∀ ι : Asgn, (∀ c ∈ Ψ, c.head < j → c.P ι) →
      ∃ ι', Agree j ι ι' ∧ Sat ι' Ψ := by
    intro k
    induction k with
    | zero =>
      intro j hj ι hι
      exact ⟨ι, Agree.refl _ _, fun c hc => hι c hc (by have := (hΨ.2.2 c hc).2; omega)⟩
    | succ k ih =>
      intro j hj ι hι
      by_cases hc : ∃ c ∈ Ψ, c.head = j
      · obtain ⟨c, hcΨ, rfl⟩ := hc
        obtain ⟨z, hz⟩ := c.sat ι
        obtain ⟨ι', hι', hs⟩ := ih (c.head + 1) (by omega) (Function.update ι c.head z) (by
          intro c' hc' hlt
          rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | heq
          · exact c'.dep (fun x hx => (Function.update_of_ne (by omega) _ _).symm) (hι c' hc' hlt)
          · obtain rfl : c' = c := List.inj_on_of_nodup_map hΨ.2.1 hc' hcΨ heq
            exact hz)
        refine ⟨ι', fun x hx => ?_, hs⟩
        rw [← hι' x (by omega), Function.update_of_ne (by omega)]
      · obtain ⟨ι', hι', hs⟩ := ih (j + 1) (by omega) ι (fun c' hc' hlt => by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | heq
          · exact hι c' hc' hlt
          · exact absurd ⟨c', hc', heq⟩ hc)
        exact ⟨ι', Agree.mono (Nat.le_succ j) hι', hs⟩
  exact key _ n₀ rfl ι fun c hc hlt => absurd (hΨ.2.2 c hc).1 (by omega)

theorem Fresh.before {n₀ n₁ : ℕ} {Ψ : List Con} (h : Fresh n₀ n₁ Ψ) : Before n₁ Ψ :=
  fun c hc => (h.2.2 c hc).2

theorem Before.append {n₀ n₁ : ℕ} {Ψ Ψ' : List Con} (hΨ : Before n₀ Ψ) (h : Fresh n₀ n₁ Ψ') :
    Before n₁ (Ψ ++ Ψ') := fun c hc =>
  (List.mem_append.mp hc).elim (fun hc => lt_of_lt_of_le (hΨ c hc) h.le) (h.before c)

theorem Sat.congr {n : ℕ} {Ψ : List Con} (hΨ : Before n Ψ) {ι ι' : Asgn}
    (h : Agree n ι ι') (hs : Sat ι Ψ) : Sat ι' Ψ := fun c hc =>
  c.dep (fun x hx => h x (lt_of_le_of_lt hx (hΨ c hc))) (hs c hc)

/-! ## Descriptions -/

mutual

/-- A description under `ι` holds under any `ι'` agreeing below `n`,
with constraints on fresh variables from `n` added: each list element's
assignment re-chooses those variables. -/
theorem Describes.grow {n n' : ℕ} {Ψ Ψ' : List Con} (hb : Before n Ψ) (hF : Fresh n n' Ψ') :
    ∀ {ι ι' : Asgn} {d : DVal} {v : Val}, Agree n ι ι' → Describes Ψ ι d v → d.Below n →
      Describes (Ψ ++ Ψ') ι' d v
  | _, _, _, _, h, .num hu, ⟨hl, hm, hτ⟩ => .num (hu.congr h hl hm hτ)
  | _, _, _, _, h, .list hall, ⟨ha, hd⟩ => .list (DescribesAll.grow hb hF h hall ha hd)
  | _, _, _, _, h, .record hfs, hbs => .record (DescribesFields.grow hb hF h hfs hbs)
  | _, _, _, _, _, .bool, _ => .bool
  | _, _, _, _, _, .real, _ => .real
  | _, _, _, _, _, .ctxv, _ => .ctxv
  | _, _, _, _, h, .sctx hC, hbC => .sctx (hC.congr h hbC)

theorem DescribesAll.grow {n n' : ℕ} {Ψ Ψ' : List Con} (hb : Before n Ψ) (hF : Fresh n n' Ψ') :
    ∀ {ι ι' : Asgn} {d : DVal} {a : ℕ} {vs : List Val}, Agree n ι ι' →
      DescribesAll Ψ ι d a vs → a ≤ n → d.Below n → DescribesAll (Ψ ++ Ψ') ι' d a vs
  | _, _, _, _, _, _, .nil, _, _ => .nil
  | _, _, _, _, _, h, .cons (ι' := ι₀) h₀ hs hd tl, ha, hdb => by
    obtain ⟨ι₁, a₁, hs₁⟩ := Sat.extend hF ι₀
    exact .cons (fun x hx => (h x (lt_of_lt_of_le hx ha)).symm.trans
        ((h₀ x hx).trans (a₁ x (lt_of_lt_of_le hx ha))))
      ((Sat.congr hb a₁ hs).append hs₁) (Describes.grow hb hF a₁ hd hdb)
      (DescribesAll.grow hb hF h tl ha hdb)

theorem DescribesFields.grow {n n' : ℕ} {Ψ Ψ' : List Con} (hb : Before n Ψ)
    (hF : Fresh n n' Ψ') :
    ∀ {ι ι' : Asgn} {afs : List (Label × DVal)} {fs : List (Label × Val)}, Agree n ι ι' →
      DescribesFields Ψ ι afs fs → DVal.BelowFields n afs → DescribesFields (Ψ ++ Ψ') ι' afs fs
  | _, _, _, _, _, .nil, _ => .nil
  | _, _, _, _, h, .cons hd hfs, ⟨hb₁, hbs⟩ =>
    .cons (Describes.grow hb hF h hd hb₁) (DescribesFields.grow hb hF h hfs hbs)

end

mutual

theorem Describes.of_append {Ψ Ψ' : List Con} :
    ∀ {ι : Asgn} {d : DVal} {v : Val}, Describes (Ψ ++ Ψ') ι d v → Describes Ψ ι d v
  | _, _, _, .num hu => .num hu
  | _, _, _, .list hall => .list (DescribesAll.of_append hall)
  | _, _, _, .record hfs => .record (DescribesFields.of_append hfs)
  | _, _, _, .bool => .bool
  | _, _, _, .real => .real
  | _, _, _, .ctxv => .ctxv
  | _, _, _, .sctx hC => .sctx hC

theorem DescribesAll.of_append {Ψ Ψ' : List Con} :
    ∀ {ι : Asgn} {d : DVal} {a : ℕ} {vs : List Val}, DescribesAll (Ψ ++ Ψ') ι d a vs →
      DescribesAll Ψ ι d a vs
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons h hs hd tl =>
    .cons h hs.left (Describes.of_append hd) (DescribesAll.of_append tl)

theorem DescribesFields.of_append {Ψ Ψ' : List Con} :
    ∀ {ι : Asgn} {afs : List (Label × DVal)} {fs : List (Label × Val)},
      DescribesFields (Ψ ++ Ψ') ι afs fs → DescribesFields Ψ ι afs fs
  | _, _, _, .nil => .nil
  | _, _, _, .cons hd hfs => .cons (Describes.of_append hd) (DescribesFields.of_append hfs)

end

theorem DEnv.Holds.of_append {Ψ Ψ' : List Con} {Δ : DEnv} {ι : Asgn} {σ : Store}
    (h : Δ.Holds (Ψ ++ Ψ') ι σ) : Δ.Holds Ψ ι σ := fun x d hx =>
  (h x d hx).imp fun _ ⟨hv, hd⟩ => ⟨hv, hd.of_append⟩

theorem DEnv.Holds.grow {n n' : ℕ} {Ψ Ψ' : List Con} (hb : Before n Ψ) (hF : Fresh n n' Ψ')
    {ι ι' : Asgn} (h : Agree n ι ι') {Δ : DEnv} {σ : Store} (hΔ : Δ.Below n)
    (hσ : Δ.Holds Ψ ι σ) : Δ.Holds (Ψ ++ Ψ') ι' σ := fun x d hx => by
  obtain ⟨v, hv, hd⟩ := hσ x d hx
  exact ⟨v, hv, hd.grow hb hF h (hΔ x d hx)⟩

theorem DEnv.without_eq_some {Δ : DEnv} {X : List Var} {x : Var} {d : DVal} :
    Δ.without X x = some d ↔ x ∉ X ∧ Δ x = some d := by
  unfold DEnv.without; split <;> simp_all

theorem DEnv.Below.without {n : ℕ} {Δ : DEnv} (hΔ : Δ.Below n) (X : List Var) :
    (Δ.without X).Below n := fun x d hx => hΔ x d (DEnv.without_eq_some.mp hx).2

theorem DEnv.Holds.without {Δ : DEnv} {Ψ : List Con} {ι : Asgn} {σ : Store}
    (hσ : Δ.Holds Ψ ι σ) (X : List Var) : (Δ.without X).Holds Ψ ι σ := fun x d hx =>
  hσ x d (DEnv.without_eq_some.mp hx).2

theorem DEnv.Holds.update {Δ : DEnv} {Ψ : List Con} {ι : Asgn} {σ : Store}
    (hσ : Δ.Holds Ψ ι σ) (x : Var) {d : DVal} {v : Val} (hd : Describes Ψ ι d v) :
    (Δ.update x d).Holds Ψ ι (σ.update x v) := by
  intro z d' hz
  by_cases hzx : z = x
  · subst hzx
    simp only [DEnv.update, Function.update_self, Option.some.injEq] at hz
    exact ⟨v, by simp [Store.update], hz ▸ hd⟩
  · simp only [DEnv.update, Function.update_of_ne hzx] at hz
    simpa [Store.update, Function.update_of_ne hzx] using hσ z d' hz

theorem DEnv.Holds.single {Ψ : List Con} {ι : Asgn} {y : Var} {d : DVal} {v : Val}
    (hd : Describes Ψ ι d v) : (DEnv.single y d).Holds Ψ ι (Store.single y v) := by
  intro x d' hx
  by_cases hxy : x = y
  · subst hxy
    simp only [DEnv.single, if_pos, Option.some.injEq] at hx
    exact ⟨v, by simp [Store.single], hx ▸ hd⟩
  · simp [DEnv.single, hxy] at hx

local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem NumIn.eq {ι : Asgn} {l m : Term} {τ : Option Term} {u : Num} (h : NumIn ι l m τ u)
    (hu : u ≠ nan) : lsbOf u = l.eval ι ∧ msbOf u = m.eval ι :=
  (h.resolve_left hu).imp_right And.left

theorem eval_update {n : ℕ} {t : Term} (h : t.Below n) (ι : Asgn) (z : EInt) :
    t.eval (Function.update ι n z) = t.eval ι :=
  (Term.eval_congr (fun _ hx => (Function.update_of_ne hx.ne _ _).symm) h).symm

theorem forall₂_one {α β : Type} {R : α → β → Prop} {a : α} {l : List β}
    (h : List.Forall₂ R [a] l) : ∃ b, l = [b] ∧ R a b := by
  rcases h with _ | ⟨h, h'⟩; cases h'; exact ⟨_, rfl, h⟩

theorem forall₂_two {α β : Type} {R : α → β → Prop} {a₁ a₂ : α} {l : List β}
    (h : List.Forall₂ R [a₁, a₂] l) : ∃ b₁ b₂, l = [b₁, b₂] ∧ R a₁ b₁ ∧ R a₂ b₂ := by
  rcases h with _ | ⟨h₁, _ | ⟨h₂, h'⟩⟩; cases h'; exact ⟨_, _, rfl, h₁, h₂⟩

/-! ## Fresh intervals -/

theorem fresh_bounds (n : ℕ) {Lo Hi : Term} (hLo : Lo.Below (n + 1)) (hHi : Hi.Below n) :
    Fresh n (n + 2) (bounds n Lo Hi hLo hHi) :=
  ⟨by omega, by simp [bounds, Con.upper, Con.lower], fun c hc => by
    simp only [bounds, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp [Con.upper, Con.lower]⟩

/-- `w` lies in the fresh interval `[n + 1, n]` once its digits meet the bounds;
`n` takes `w`'s most significant digit, which `Lo` may mention. -/
theorem fresh_numIn {n : ℕ} {Lo Hi : Term} (hLo : Lo.Below (n + 1)) (hHi : Hi.Below n)
    (ι : Asgn) (w : Num)
    (h : w ≠ nan → msbOf w ≤ Hi.eval ι ∧ Lo.eval (Function.update ι n (msbOf w)) ≤ lsbOf w) :
    ∃ ι', AgreeOut n (n + 2) ι ι' ∧ Sat ι' (bounds n Lo Hi hLo hHi) ∧
      NumIn ι' (.var (n + 1)) (.var n) none w := by
  have key : ∀ a b : EInt, b ≤ Hi.eval ι → Lo.eval (Function.update ι n b) ≤ a →
      (w = nan ∨ a = lsbOf w ∧ b = msbOf w) →
      ∃ ι', AgreeOut n (n + 2) ι ι' ∧ Sat ι' (bounds n Lo Hi hLo hHi) ∧
        NumIn ι' (.var (n + 1)) (.var n) none w := by
    intro a b hb ha hw
    let ι₁ := Function.update ι n b
    let ι' := Function.update ι₁ (n + 1) a
    have e₁ : Agree n ι ι₁ := fun x hx => (Function.update_of_ne hx.ne _ _).symm
    have e' : Agree (n + 1) ι₁ ι' := fun x hx => (Function.update_of_ne hx.ne _ _).symm
    have hn : ι' n = b := by simp [ι', ι₁]
    have hn1 : ι' (n + 1) = a := by simp [ι']
    refine ⟨ι', fun x hx => ?_, fun c hc => ?_, ?_⟩
    · simp only [ι', ι₁]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    · simp only [bounds, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · simp only [Con.P_upper, hn]
        rwa [← Term.eval_congr (e₁.trans (e'.mono (Nat.le_succ n))) hHi]
      · simp only [Con.P_lower, hn1]
        rwa [← Term.eval_congr e' hLo]
    · rcases hw with hw | ⟨rfl, rfl⟩
      · exact .inl hw
      · exact .inr ⟨hn1.symm, hn.symm, fun _ h => absurd h (by simp)⟩
  by_cases hw : w = nan
  · exact key ⊤ ⊥ bot_le le_top (.inl hw)
  · exact key _ _ (h hw).1 (h hw).2 (.inr ⟨rfl, rfl⟩)

/-! ## Symbolic values -/

@[simp] theorem numOfE_bot : numOfE ⊥ = .special (.inf true) := rfl
@[simp] theorem numOfE_top : numOfE ⊤ = .special (.inf false) := rfl
@[simp] theorem numOfE_coe (k : ℤ) : numOfE k = .finite (k : ℝ) := rfl

theorem coe_add_coe (a b : ℤ) : ((a : EInt) + (b : EInt)) = ((a + b : ℤ) : EInt) := by
  change ((a : WithTop ℤ) : WithBot (WithTop ℤ)) + ((b : WithTop ℤ) : WithBot (WithTop ℤ)) =
    (((a + b : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))
  rw [← WithBot.coe_add, ← WithTop.coe_add]

theorem coe_max_coe (a b : ℤ) : max (a : EInt) (b : EInt) = ((max a b : ℤ) : EInt) :=
  (WithBotTop.coe_monotone.map_max).symm

theorem coe_min_coe (a b : ℤ) : min (a : EInt) (b : EInt) = ((min a b : ℤ) : EInt) :=
  (WithBotTop.coe_monotone.map_min).symm

theorem add_numOfE (a b : EInt) :
    Num.add (numOfE a) (numOfE b) = nan ∨ Num.add (numOfE a) (numOfE b) = numOfE (a + b) := by
  cases a using WithBotTop.rec <;> cases b using WithBotTop.rec
  case coe.coe a b => right; rw [coe_add_coe]; simp [Num.add]
  all_goals first | exact .inr rfl | exact .inl rfl

theorem neg_numOfE (a : EInt) : Num.neg (numOfE a) = numOfE (negE a) := by
  cases a using WithBotTop.rec <;> first | rfl | simp [Num.neg, negE, WithSpecial.neg]

theorem max_numOfE (a b : EInt) : Num.max (numOfE a) (numOfE b) = numOfE (max a b) := by
  cases a using WithBotTop.rec <;> cases b using WithBotTop.rec <;>
    simp [Num.max, coe_max_coe]

theorem min_numOfE (a b : EInt) : Num.min (numOfE a) (numOfE b) = numOfE (min a b) := by
  cases a using WithBotTop.rec <;> cases b using WithBotTop.rec <;>
    simp [Num.min, coe_min_coe]

theorem logb_eq {u : Num} (hu : u ≠ nan) : Num.logb u = numOfE (msbOf u) := by
  rcases u with x | ((_ | _) | _)
  · by_cases hx : x = 0 <;> simp [Num.logb, msbOf, hx]
  · rfl
  · rfl
  · exact absurd rfl hu

/-- Interval and symbolic value together. -/
theorem NumIn.withTerm {ι : Asgn} {l m t : Term} {u : Num} (h : NumIn ι l m none u)
    (ht : u = nan ∨ u = numOfE (t.eval ι)) : NumIn ι l m (some t) u := by
  rcases h with h | ⟨hl, hm, -⟩
  · exact .inl h
  · rcases ht with ht | ht
    · exact .inl ht
    · exact .inr ⟨hl, hm, fun t' ht' => by cases ht'; exact ht⟩

theorem NumIn.forget {ι : Asgn} {l m : Term} {τ : Option Term} {u : Num} (h : NumIn ι l m τ u) :
    NumIn ι l m none u :=
  h.imp_right fun ⟨hl, hm, _⟩ => ⟨hl, hm, fun _ ht => absurd ht (by simp)⟩

theorem NumIn.term {ι : Asgn} {l m t : Term} {u : Num} (h : NumIn ι l m (some t) u) :
    u = nan ∨ u = numOfE (t.eval ι) :=
  h.imp_right fun ⟨_, _, ht⟩ => ht t rfl

/-! ## Unrounded operators and records -/

theorem ExactOp.eval_bool {op : ExactOp} {vs : List Val} {v : Val} (h : op.eval vs = some v)
    (hop : op ≠ .len) : ∃ b, v = .bool b := by
  unfold ExactOp.eval at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    first | exact ⟨_, rfl⟩ | exact absurd rfl hop

theorem ExactOp.eval_len {vs : List Val} {v : Val} (h : ExactOp.len.eval vs = some v) :
    ∃ k : ℕ, v = .num (.finite k) := by
  unfold ExactOp.eval at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    first | exact ⟨_, rfl⟩ | (exfalso; simp_all)

theorem ctxOfFields_admits {Ψ : List Con} {ι : Asgn} :
    ∀ {afs : List (Label × DVal)} {fs : List (Label × Val)} {ts : List (Label × Term)},
      DescribesFields Ψ ι afs fs → ctxOfFields afs = some ts →
      List.Forall₂ (fun (f : Label × Term) (w : Label × Val) =>
        f.1 = w.1 ∧ (w.2 = .num (numOfE (f.2.eval ι)) ∨ w.2 = .num nan)) ts fs
  | _, _, _, .nil, h => by simp only [ctxOfFields, Option.some.injEq] at h; subst h; exact .nil
  | _, _, ts, .cons (l := l) (a := a) hd hfs, h => by
    cases a with
    | num lo hi τ =>
      cases τ with
      | none => simp [ctxOfFields] at h
      | some t =>
        simp only [ctxOfFields, Option.map_eq_some_iff] at h
        obtain ⟨ts', hts', rfl⟩ := h
        cases hd with
        | num hu =>
          exact .cons ⟨rfl, (hu.term).symm.imp (congrArg Val.num) (congrArg Val.num)⟩
            (ctxOfFields_admits hfs hts')
    | _ => simp [ctxOfFields] at h

theorem ctxOf_admits {Ψ : List Con} {ι : Asgn} {d : DVal} {fs : List (Label × Val)}
    {C : SCtx} (hd : Describes Ψ ι d (.record fs)) (hC : ctxOf d = some C) :
    C.Admits ι (.ctx fs) := by
  cases hd with
  | record hfs =>
    simp only [ctxOf, Option.map_eq_some_iff] at hC
    obtain ⟨ts, hts, rfl⟩ := hC
    exact ⟨fs, rfl, ctxOfFields_admits hfs hts⟩
  | sctx _ => simp [ctxOf] at hC

theorem ctxOfFields_below {n : ℕ} :
    ∀ {afs : List (Label × DVal)} {ts : List (Label × Term)}, DVal.BelowFields n afs →
      ctxOfFields afs = some ts → ∀ f ∈ ts, f.2.Below n
  | [], _, _, h, f, hf => by
    simp only [ctxOfFields, Option.some.injEq] at h
    subst h
    exact absurd hf List.not_mem_nil
  | (_, d) :: _, _, ⟨hd, hb⟩, h, f, hf => by
    cases d with
    | num lo hi τ =>
      cases τ with
      | none => simp [ctxOfFields] at h
      | some t =>
        simp only [ctxOfFields, Option.map_eq_some_iff] at h
        obtain ⟨ts', hts', rfl⟩ := h
        rcases List.mem_cons.mp hf with rfl | hf
        · exact hd.2.2 t rfl
        · exact ctxOfFields_below hb hts' f hf
    | _ => simp [ctxOfFields] at h

theorem ctxOf_below {n : ℕ} {d : DVal} {C : SCtx} (hd : d.Below n) (hC : ctxOf d = some C) :
    C.Below n := by
  cases d with
  | record afs =>
    simp only [ctxOf, Option.map_eq_some_iff] at hC
    obtain ⟨ts, hts, rfl⟩ := hC
    exact ctxOfFields_below hd hts
  | _ => simp [ctxOf] at hC

theorem DescribesFields.lookup {Ψ : List Con} {ι : Asgn} {l : Label} {a : DVal}
    {v : Val} :
    ∀ {afs : List (Label × DVal)} {fs : List (Label × Val)}, DescribesFields Ψ ι afs fs →
      afs.lookup l = some a → fs.lookup l = some v → Describes Ψ ι a v
  | _, _, .nil, ha, _ => by simp [List.lookup] at ha
  | _, _, .cons (l := l') hd tl, ha, hv => by
    by_cases hl : l = l'
    · subst hl
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at ha hv
      exact ha ▸ hv ▸ hd
    · have hne : (l == l') = false := by simpa using hl
      simp only [List.lookup, hne] at ha hv
      exact DescribesFields.lookup tl ha hv

/-- D-List: each element, described by its own abstract value, is described by
the summary `d` once its fresh variables `[n₀, n₁)` are re-chosen. -/
theorem describesAll_of_le {n₀ n₁ : ℕ} {Ψ Ψ' : List Con} {d : DVal} {ι ι' : Asgn}
    (hb : Before n₀ Ψ) (hs : Sat ι Ψ) (h : Agree n₀ ι ι') :
    ∀ {ds : List DVal} {vs : List Val}, List.Forall₂ (Describes Ψ ι) ds vs →
      (∀ d' ∈ ds, DVal.Le n₀ n₁ Ψ Ψ' d' d) → DescribesAll (Ψ ++ Ψ') ι' d n₀ vs
  | _, _, .nil, _ => .nil
  | _, _, .cons hd tl, hle => by
    obtain ⟨ι₁, a₁, hs₁, hd'⟩ := hle _ (List.mem_cons_self ..) hb _ _ hs hd
    exact .cons (fun x hx => (h x hx).symm.trans (a₁.agree x hx))
      ((Sat.congr hb a₁.agree hs).append hs₁) hd'
      (describesAll_of_le hb hs h tl fun d' hd' => hle d' (List.mem_cons_of_mem _ hd'))

theorem DescribesAll.mem {Ψ : List Con} {ι : Asgn} {d : DVal} {a : ℕ} :
    ∀ {vs : List Val}, DescribesAll Ψ ι d a vs → ∀ {v : Val}, v ∈ vs →
      ∃ ι₀, Agree a ι ι₀ ∧ Sat ι₀ Ψ ∧ Describes Ψ ι₀ d v
  | _, .nil, _, hv => absurd hv List.not_mem_nil
  | _, .cons h₀ hs hd tl, _, hv =>
    (List.mem_cons.mp hv).elim (fun h => h ▸ ⟨_, h₀, hs, hd⟩) (fun h => DescribesAll.mem tl h)

/-! ## Outcomes -/

/-- What a statement's outcome must satisfy: a normal end in `Δ'`, or a value
returned within `a`. -/
def Within (Ψ : List Con) (ι : Asgn) (Δ' : DEnv) (a : Option DVal) : Outcome → Prop
  | .normal σ => Δ'.Holds Ψ ι σ
  | .ret v => ∃ d ∈ a, Describes Ψ ι d v

theorem Within.grow {n n' : ℕ} {Ψ Ψ' : List Con} (hb : Before n Ψ) (hF : Fresh n n' Ψ')
    {ι ι' : Asgn} (h : Agree n ι ι') {Δ' : DEnv} {a : Option DVal} (hΔ : Δ'.Below n)
    (ha : RetBelow n a) : ∀ {o : Outcome}, Within Ψ ι Δ' a o → Within (Ψ ++ Ψ') ι' Δ' a o
  | .normal _, hw => DEnv.Holds.grow hb hF h hΔ hw
  | .ret _, ⟨d, hd, hv⟩ => ⟨d, hd, hv.grow hb hF h (ha d hd)⟩

end Fpy.DigitBound
