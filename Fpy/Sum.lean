import Fpy.Semantics
import Fpy.Ops

/-!
# `sum` (Appendix A)

`sum` is an FPy function, not a primitive: it adds a list's elements in order,
each addition rounding under the caller's context, with the index arithmetic
under `R`. `exec_sumBody` gives its result, from which A-Sum and D-Sum follow.
-/

namespace Fpy

open Mpfx

variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}

/-- The loop of `sum`. -/
def sumLoop : Stmt (fpy decode) :=
  .whileDo (.exactOp .lt [.var "i", .exactOp .len [.var "xs"]])
    (.seq (.assign "s" (.arithOp .add [.var "s", .index (.var "xs") (.var "i")]))
      (.withCtx .real (.assign "i" (.arithOp .add [.var "i", .num (.finite 1)]))))

/-- The body of `sum(xs)`. -/
def sumBody : Stmt (fpy decode) :=
  .ite (.exactOp .eq [.exactOp .len [.var "xs"], .num (.finite 0)]) (.ret (.num (.finite 0)))
    (.seq (.assign "s" (.index (.var "xs") (.num (.finite 0))))
      (.seq (.assign "i" (.num (.finite 1))) (.seq sumLoop (.ret (.var "s")))))

/-- A list of values that are all numbers. -/
theorem exists_map_num {P : Num → Prop} : ∀ {vs : List Val}, (∀ w ∈ vs, ∃ u, w = .num u ∧ P u) →
    ∃ us : List Num, vs = us.map .num ∧ ∀ u ∈ us, P u
  | [], _ => ⟨[], rfl, by simp⟩
  | w :: ws, h => by
    obtain ⟨us, rfl, hus⟩ := exists_map_num fun w' h' => h w' (List.mem_cons_of_mem _ h')
    obtain ⟨u, rfl, hu⟩ := h w (List.mem_cons_self ..)
    exact ⟨u :: us, rfl, by simpa [hu] using hus⟩

/-- What `sum` computes with rounding `r`: `r(…r(v₁ + v₂)… + v_L)`, and `0` for `[]`. -/
noncomputable def sumVal (r : Num → Num) : List Num → Num
  | [] => .finite 0
  | u :: us => us.foldl (fun s w => r (Num.add s w)) u

theorem sumVal_take_succ (r : Num → Num) {us : List Num} {k : ℕ} (hk : 1 ≤ k)
    (hkL : k < us.length) :
    sumVal r (us.take (k + 1)) = r (Num.add (sumVal r (us.take k)) us[k]) := by
  rcases us with _ | ⟨u, us⟩
  · simp at hkL
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [List.take_succ_cons, sumVal, List.getElem_cons_succ]
    rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem (by simp at hkL; omega)]
    rfl

section Run

variable {C : Val} {r : Num → Num} (hr : C.rnd (fpy decode) = some r) (us : List Num)

/-- The store inside the loop: `s` holds the partial sum `p`, `i` the index `k`. -/
def sumStore (p : Num) (k : ℕ) : Store :=
  ((Store.single "xs" (.list (us.map .num))).update "s" (.num p)).update "i" (.num (.finite k))

include hr in
theorem sumLoop_run : ∀ j k, us.length - k = j → 1 ≤ k → k ≤ us.length →
    Exec Φ (sumStore us (sumVal r (us.take k)) k) C sumLoop
      (.normal (sumStore us (sumVal r us) us.length)) := by
  have hxs : ∀ p k, sumStore us p k "xs" = some (.list (us.map .num)) := by
    intro p k; simp [sumStore, Store.update, Store.single]
  have hlen : ∀ p k, Eval Φ (sumStore us p k) C (.exactOp .len [.var "xs"])
      (.num (.finite us.length)) := fun p k =>
    .exact (.cons (.var (hxs p k)) .nil) (by simp [fpy, ExactOp.eval])
  have hi : ∀ p k, sumStore us p k "i" = some (.num (.finite k)) := by
    intro p k; simp [sumStore, Store.update]
  have hguard : ∀ p k, Eval Φ (sumStore us p k) C
      (.exactOp .lt [.var "i", .exactOp .len [.var "xs"]]) (.bool (decide (k < us.length))) :=
    fun p k => .exact (.cons (.var (hi p k)) (.cons (hlen p k) .nil)) (by simp [fpy, ExactOp.eval,
      Num.lt])
  intro j
  induction j with
  | zero =>
    intro k hj _ hkL
    obtain rfl : k = us.length := by omega
    rw [List.take_length]
    exact .whileFalse (by simpa using hguard (sumVal r us) us.length)
  | succ j ih =>
    intro k hj hk _
    have hkL : k < us.length := by omega
    set p := sumVal r (us.take k)
    have hs : sumStore us p k "s" = some (.num p) := by simp [sumStore, Store.update]
    have hidx : Eval Φ (sumStore us p k) C (.index (.var "xs") (.var "i")) (.num us[k]) :=
      .index (.var (hxs p k)) (.var (hi p k)) (by simp [hkL])
    have h₁ : Exec Φ (sumStore us p k) C
        (.assign "s" (.arithOp .add [.var "s", .index (.var "xs") (.var "i")]))
        (.normal ((sumStore us p k).update "s" (.num (r (Num.add p us[k]))))) :=
      .assign (.arith (ns := [p, us[k]]) (.cons (.var hs) (.cons hidx .nil)) rfl hr)
    have h₂ : Exec Φ ((sumStore us p k).update "s" (.num (r (Num.add p us[k])))) C
        (.withCtx .real (.assign "i" (.arithOp .add [.var "i", .num (.finite 1)])))
        (.normal (sumStore us (r (Num.add p us[k])) (k + 1))) := by
      have h : Exec Φ ((sumStore us p k).update "s" (.num (r (Num.add p us[k])))) C
          (.withCtx .real (.assign "i" (.arithOp .add [.var "i", .num (.finite 1)])))
          (.normal (((sumStore us p k).update "s" (.num (r (Num.add p us[k])))).update "i"
            (.num (id (Num.add (.finite k) (.finite 1)))))) :=
        .withCtx .real trivial (.assign (.arith (ns := [.finite k, .finite 1]) (r := id)
          (.cons (.var (by simp [sumStore, Store.update])) (.cons .num .nil)) rfl rfl))
      convert h using 2
      funext x
      simp only [sumStore, Store.update, Function.update_apply, id, Num.add]
      split_ifs <;> simp_all
    have h₃ := ih (k + 1) (by omega) (by omega) (by omega)
    rw [sumVal_take_succ r hk hkL] at h₃
    exact .whileTrue (by simpa [hkL] using hguard p k) (.seqNormal (.seqNormal h₁ h₂) h₃)

include hr in
theorem sumBody_run :
    Exec Φ (Store.single "xs" (.list (us.map .num))) C sumBody (.ret (.num (sumVal r us))) := by
  have hxs : Store.single "xs" (.list (us.map .num)) "xs" = some (.list (us.map .num)) := by
    simp [Store.single]
  have hlen : Eval Φ (Store.single "xs" (.list (us.map .num))) C (.exactOp .len [.var "xs"])
      (.num (.finite us.length)) := .exact (.cons (.var hxs) .nil) (by simp [fpy, ExactOp.eval])
  have hguard : Eval Φ (Store.single "xs" (.list (us.map .num))) C
      (.exactOp .eq [.exactOp .len [.var "xs"], .num (.finite 0)])
      (.bool (decide (us.length = 0))) :=
    .exact (.cons hlen (.cons .num .nil)) (by simp [fpy, ExactOp.eval, Num.eq])
  rcases us with _ | ⟨u, us'⟩
  · exact .iteTrue (by simpa using hguard) (.ret .num)
  · refine .iteFalse (by simpa using hguard) ?_
    have h₀ : Exec Φ (Store.single "xs" (.list ((u :: us').map .num))) C
        (.assign "s" (.index (.var "xs") (.num (.finite 0))))
        (.normal ((Store.single "xs" (.list ((u :: us').map .num))).update "s" (.num u))) :=
      .assign (.index (k := 0) (.var hxs) (by simpa using (Eval.num : Eval Φ _ C
        (.num (.finite 0)) _)) rfl)
    have h₁ : Exec Φ ((Store.single "xs" (.list ((u :: us').map .num))).update "s" (.num u)) C
        (.assign "i" (.num (.finite 1)))
        (.normal (sumStore (u :: us') (sumVal r ((u :: us').take 1)) 1)) := by
      simpa [sumStore, sumVal] using (Exec.assign (x := "i") Eval.num :
        Exec Φ ((Store.single "xs" (.list ((u :: us').map .num))).update "s" (.num u)) C
          (.assign "i" (.num (.finite 1))) _)
    have h₂ := sumLoop_run (Φ := Φ) hr (u :: us') _ 1 rfl le_rfl (by simp)
    exact .seqNormal h₀ (.seqNormal h₁ (.seqNormal h₂ (.ret (.var (by simp [sumStore,
      Store.update])))))

end Run

/-- `sum` returns `sumVal r` of its argument's elements. -/
theorem exec_sumBody {C : Val} {r : Num → Num} (hr : C.rnd (fpy decode) = some r)
    {us : List Num} {o : Outcome}
    (h : Exec Φ (Store.single "xs" (.list (us.map .num))) C sumBody o) :
    o = .ret (.num (sumVal r us)) :=
  Exec.det _ h (sumBody_run hr us)

end Fpy
