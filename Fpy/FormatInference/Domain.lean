import Fpy.FormatInference.Defs
import Fpy.Ops
import Mpfx.Format.Containment

/-!
# The format domain of Figure 4

A format is a finite set of values, an abstract format `𝒜(p, exp, b)` (with its
specials), or `R*`. A set meeting an abstract format in a join is first
replaced by `⌈S⌉`, an abstract format containing it. The draft takes `⌈S⌉` to
be the smallest one; soundness needs only containment, so `⌈S⌉` is any
`Ceiling`.

The format of an Mpfx context is its own format `F`, provided its special map
fixes the format's specials (`fpyCtxFmt_sound`).
-/

namespace Fpy

open Mpfx

/-- The values of a format, read as numbers. -/
def _root_.Mpfx.Format.reals (F : Format) : Set Num := {n | ∃ v ∈ F.values, v.toReal = n}

/-- `𝒜(max(p₁, p₂), min(exp₁, exp₂), max(b₁, b₂))`, with the specials of both. -/
noncomputable def fmtJoin (F₁ F₂ : Format) : Format where
  p := max F₁.p F₂.p
  exp := min F₁.exp F₂.exp
  b := max F₁.b F₂.b
  specials := F₁.specials ∪ F₂.specials

theorem _root_.Mpfx.Format.reals_mono {F G : Format} (h : F ⊆ G) {n : Num} (hn : n ∈ F.reals) :
    n ∈ G.reals := by
  obtain ⟨v, hv, rfl⟩ := hn
  refine ⟨v, ?_, rfl⟩
  cases v with
  | finite d => exact h d hv
  | special s => exact h.specials hv

theorem reals_fmtJoin_left {F₁ : Format} {n : Num} (h : n ∈ F₁.reals) (F₂ : Format) :
    n ∈ (fmtJoin F₁ F₂).reals :=
  Format.reals_mono (Format.containsPrec le_sup_left inf_le_left le_sup_left
    Set.subset_union_left) h

theorem reals_fmtJoin_right (F₁ : Format) {F₂ : Format} {n : Num} (h : n ∈ F₂.reals) :
    n ∈ (fmtJoin F₁ F₂).reals :=
  Format.reals_mono (Format.containsPrec le_sup_right inf_le_right le_sup_right
    Set.subset_union_right) h

/-- Formats of Figure 4. -/
inductive Fmt where
  | set (S : Finset Num)
  | abs (F : Format)
  | top

def Fmt.γ : Fmt → Set Num
  | .set S => ↑S
  | .abs F => F.reals
  | .top => Set.univ

/-- `⌈S⌉`: an abstract format containing `S`, if one is chosen. -/
structure Ceiling where
  ceil : Finset Num → Option Format
  sound : ∀ {S F}, ceil S = some F → ∀ n ∈ S, n ∈ F.reals

open Classical in
/-- The join of Figure 4. -/
noncomputable def Fmt.join (c : Ceiling) : Fmt → Fmt → Fmt
  | .set S₁, .set S₂ => .set (S₁ ∪ S₂)
  | .set S, .abs F | .abs F, .set S =>
      if ↑S ⊆ F.reals then .abs F else (c.ceil S).elim .top (fun F' => .abs (fmtJoin F' F))
  | .abs F₁, .abs F₂ => .abs (fmtJoin F₁ F₂)
  | _, _ => .top

open Classical in
theorem Fmt.mem_join_set {c : Ceiling} {S : Finset Num} {F : Format} {n : Num}
    (h : n ∈ (Fmt.set S).γ ∨ n ∈ (Fmt.abs F).γ) :
    n ∈ ((if ↑S ⊆ F.reals then Fmt.abs F
      else (c.ceil S).elim .top (fun F' => .abs (fmtJoin F' F))) : Fmt).γ := by
  split
  · next hS => exact h.elim (fun h => hS h) id
  · cases hc : c.ceil S with
    | none => trivial
    | some F' =>
      rcases h with h | h
      · exact reals_fmtJoin_left (c.sound hc n h) F
      · exact reals_fmtJoin_right F' h

theorem Fmt.mem_join_left {c : Ceiling} {F₁ F₂ : Fmt} {n : Num} (h : n ∈ F₁.γ) :
    n ∈ (Fmt.join c F₁ F₂).γ := by
  cases F₁ <;> cases F₂ <;> simp only [Fmt.join]
  all_goals first
    | trivial
    | exact Fmt.mem_join_set (Or.inl h)
    | exact Fmt.mem_join_set (Or.inr h)
    | exact Finset.mem_union_left _ h
    | exact reals_fmtJoin_left h _

theorem Fmt.mem_join_right {c : Ceiling} {F₁ F₂ : Fmt} {n : Num} (h : n ∈ F₂.γ) :
    n ∈ (Fmt.join c F₁ F₂).γ := by
  cases F₁ <;> cases F₂ <;> simp only [Fmt.join]
  all_goals first
    | trivial
    | exact Fmt.mem_join_set (Or.inl h)
    | exact Fmt.mem_join_set (Or.inr h)
    | exact Finset.mem_union_right _ h
    | exact reals_fmtJoin_right _ h

open Classical in
/-- The format domain of Figure 4, for a choice of `⌈S⌉`. The containment check
is exact. -/
noncomputable def Fmt.domain (c : Ceiling) : FormatDomain where
  Fmt := Fmt
  γ := Fmt.γ
  top := .top
  bot := .set ∅
  join := Fmt.join c
  sub F₁ F₂ := decide (F₁.γ ⊆ F₂.γ)
  ofNum n := .set {n}
  mem_top _ := trivial
  mem_join_left := Fmt.mem_join_left
  mem_join_right := Fmt.mem_join_right
  sub_sound h := of_decide_eq_true h
  mem_ofNum _ := Finset.mem_singleton_self _

/-! ## Formats of Mpfx contexts -/

open Classical in
/-- `F_C` for an Mpfx context: its own format, when its special map fixes
the format's specials. Other contexts are not understood. -/
noncomputable def fpyCtxFmt (decode : List (Label × Val) → Option RoundCtx) : Val → Option Fmt
  | .ctx fs => (decode fs).bind fun c =>
      if ∀ s ∈ c.F.specials, c.S.map s = .special s then some (.abs c.F.toFormat) else none
  | _ => none

/-- An Mpfx context rounds into its format and leaves the format's values
unchanged: the obligation `Analysis.Sound.ctxFmt`. -/
theorem fpyCtxFmt_sound {decode : List (Label × Val) → Option RoundCtx} {C : Val} {FC : Fmt}
    {r : Num → Num} (hFC : fpyCtxFmt decode C = some FC) (hr : C.rnd (fpy decode) = some r) :
    (∀ n, r n ∈ FC.γ) ∧ ∀ n ∈ FC.γ, r n = n := by
  cases C with
  | ctx fs =>
    simp only [fpyCtxFmt, Option.bind_eq_some_iff] at hFC
    obtain ⟨c, hc, hFC⟩ := hFC
    split at hFC
    · next hS =>
      obtain rfl := Option.some.inj hFC
      simp only [Val.rnd, fpy, hc, Option.map_some, Option.some.injEq] at hr
      subst hr
      refine ⟨fun n => ?_, fun n hn => ?_⟩
      · obtain ⟨w, hw, hround⟩ := c.exists_rnd_eq n
        exact ⟨w, rnd_mem_values hw, hround.symm⟩
      · obtain ⟨w, hw, rfl⟩ := hn
        obtain ⟨w', hw', hround⟩ := c.exists_rnd_eq w.toReal
        rw [rnd_of_mem_values hS c.defined hw, RoundResult.value.injEq] at hw'
        rw [hround, hw']
    · simp at hFC
  | _ => simp [fpyCtxFmt] at hFC

end Fpy
