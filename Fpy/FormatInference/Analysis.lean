import Fpy.FormatInference.Refine

/-!
# Format inference for FPy

The analysis of §4.2 for the FPy signature: the formats of Figure 4, the
abstract operators of Table 1, the formats of Mpfx contexts, and condition
refinement. A record whose abstract value is a constant builds a known context.
`fpyAnalysis_sound` discharges every obligation of `Analysis.Sound`, so
Theorem 4.1 holds for it (`fpy_run_sound`).
-/

namespace Fpy

open Mpfx

variable {decode : List (Label × Val) → Option RoundCtx} {c : Ceiling}

open Classical in
mutual

/-- The value an abstract value pins down, if it pins one down: a singleton set,
a known context, or a record of these. -/
noncomputable def AVal.const? : AVal (Fmt.domain c) → Option Val
  | .fmt F =>
    match (show Fmt from F) with
    | .set S => if h : ∃ n, S = {n} then some (.num (Classical.choose h)) else none
    | _ => none
  | .record afs => (AVal.constFields afs).map .record
  | .known C => some C
  | _ => none

noncomputable def AVal.constFields :
    List (Label × AVal (Fmt.domain c)) → Option (List (Label × Val))
  | [] => some []
  | (l, a) :: afs => do
    let v ← a.const?
    let vs ← AVal.constFields afs
    pure ((l, v) :: vs)

end

mutual

theorem Describes.eq_of_const? {a : AVal (Fmt.domain c)} {v w : Val} :
    Describes a v → a.const? = some w → v = w
  | .fmt (F := F) (n := n) h, hw => by
    unfold AVal.const? at hw
    split at hw
    · next S hS =>
      split at hw
      · next hn =>
        simp only [Option.some.injEq] at hw
        subst hw
        have hmem : n ∈ (show Fmt from F).γ := h
        rw [hS, Classical.choose_spec hn] at hmem
        rw [Finset.mem_singleton.mp hmem]
      · simp at hw
    · simp at hw
  | .record (fs := fs) h, hw => by
    simp only [AVal.const?, Option.map_eq_some_iff] at hw
    obtain ⟨ws, hws, rfl⟩ := hw
    rw [DescribesFields.eq_of_constFields h hws]
  | .known, hw => by simpa [AVal.const?] using hw
  | .list _, hw | .bool, hw | .real, hw | .ctx, hw | .top, hw => by simp [AVal.const?] at hw

theorem DescribesFields.eq_of_constFields {afs : List (Label × AVal (Fmt.domain c))}
    {fs ws : List (Label × Val)} :
    DescribesFields afs fs → AVal.constFields afs = some ws → fs = ws
  | .nil, hw => by simpa [AVal.constFields] using hw
  | .cons (l := l) hd tl, hw => by
    simp only [AVal.constFields, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hw
    obtain ⟨v, hv, vs, hvs, rfl⟩ := hw
    rw [Describes.eq_of_const? hd hv, DescribesFields.eq_of_constFields tl hvs]

end

/-- The context a constant record builds. -/
noncomputable def ctxOfAVal (a : AVal (Fmt.domain c)) : Option Val :=
  match a.const? with
  | some (.record fs) => some (.ctx fs)
  | _ => none

theorem ctxOfAVal_sound {a : AVal (Fmt.domain c)} {C : Val} {fs : List (Label × Val)}
    (hC : ctxOfAVal a = some C) (ha : Describes a (.record fs)) : C = .ctx fs := by
  unfold ctxOfAVal at hC
  split at hC
  · next fs' hfs =>
    obtain rfl := Option.some.inj hC
    cases ha.eq_of_const? hfs
    rfl
  · simp at hC

variable (decode c) in
/-- Format inference for FPy, for a choice of `⌈S⌉`. -/
noncomputable def fpyAnalysis : Analysis (fpy decode) (Fmt.domain c) where
  arith := ArithOp.fmt c
  exact := ExactOp.aval c
  ctxFmt := fpyCtxFmt decode
  ctxOf := ctxOfAVal
  refine := refine

/-- FPy's format inference meets every obligation of `Analysis.Sound`. -/
theorem fpyAnalysis_sound (Φ : Program (fpy decode)) : (fpyAnalysis decode c).Sound Φ where
  arith h hop := ArithOp.fmt_sound c h hop
  exact _ hop := ExactOp.aval_sound c hop
  ctxFmt := fpyCtxFmt_sound
  ctxOf := ctxOfAVal_sound
  refine hΓ hκ h := refine_sound hκ _ hΓ h

/-- **Theorem 4.1** for FPy: a program's result lies in the format inferred for
it. -/
theorem fpy_run_sound {Φ : Program (fpy decode)} {f : Fn} {y : Var} {s : Stmt (fpy decode)}
    {a a' : AVal (Fmt.domain c)} {Γ' : AEnv (Fmt.domain c)} (hΦ : Φ f = some (y, s))
    (hs : AExec (fpyAnalysis decode c) Φ (.single y a) (some .real) s Γ' a')
    {v v' : Val} (hv : Describes a v) (hrun : Run Φ f v v') : Describes a' v' :=
  run_sound (fpyAnalysis_sound Φ) hΦ hs hv hrun

end Fpy
