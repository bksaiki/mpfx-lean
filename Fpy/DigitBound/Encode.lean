import Fpy.DigitBound.Sound

/-!
# Integer encoding of the constraints

What a solver sees: integer terms (`ITerm`) and formulas (`IForm`) over a model
(`IModel`) giving each variable an integer and two flags, "not `+∞`" and "not
`−∞`". A term over `ℤ ∪ {±∞}` encodes as formulas for "is `+∞`" and "is `−∞`"
and an integer value (`Term.enc`); an atom as a guarded comparison
(`Atom.enc`). The encoding is exact (`sat_iff`, `sat_decode`), so `precBound`
and the implementation's `precBoundFin` are validity questions over integers
(`precBound_le_iff`, `precBoundFin_le_iff`).
-/

namespace Fpy.DigitBound

open Mpfx

mutual

/-- Integer terms; `max` and `min` are `ite`. -/
inductive ITerm where
  | const (k : ℤ)
  | var (x : ℕ)
  | add (a b : ITerm)
  | smul (c : ℤ) (a : ITerm)
  | ite (φ : IForm) (a b : ITerm)

/-- Formulas over integer terms and the flags. -/
inductive IForm where
  | tt
  | ff
  | notTop (x : ℕ)
  | notBot (x : ℕ)
  | le (a b : ITerm)
  | not (φ : IForm)
  | and (φ ψ : IForm)
  | or (φ ψ : IForm)

end

/-- An integer model: a value and the flags "not `+∞`", "not `−∞`" per variable. -/
structure IModel where
  val : ℕ → ℤ
  notTop : ℕ → Bool
  notBot : ℕ → Bool

mutual

def ITerm.eval (M : IModel) : ITerm → ℤ
  | .const k => k
  | .var x => M.val x
  | .add a b => a.eval M + b.eval M
  | .smul c a => c * a.eval M
  | .ite φ a b => if φ.holds M then a.eval M else b.eval M

def IForm.holds (M : IModel) : IForm → Bool
  | .tt => true
  | .ff => false
  | .notTop x => M.notTop x
  | .notBot x => M.notBot x
  | .le a b => decide (a.eval M ≤ b.eval M)
  | .not φ => !φ.holds M
  | .and φ ψ => φ.holds M && ψ.holds M
  | .or φ ψ => φ.holds M || ψ.holds M

end

/-- `+∞` if `T`, else `−∞` if `B`, else `k`. -/
def decodeE (T B : Bool) (k : ℤ) : EInt := if T then ⊤ else if B then ⊥ else k

/-- The assignment a model stands for. -/
def IModel.decode (M : IModel) : Asgn := fun x => decodeE (!M.notTop x) (!M.notBot x) (M.val x)

/-- The model standing for an assignment. -/
def IModel.ofAsgn (ι : Asgn) : IModel where
  val x := WithBotTop.rec (motive := fun _ => ℤ) 0 id 0 (ι x)
  notTop x := ι x ≠ ⊤
  notBot x := ι x ≠ ⊥

theorem decode_ofAsgn (ι : Asgn) : (IModel.ofAsgn ι).decode = ι := by
  funext x
  simp only [IModel.decode, IModel.ofAsgn, decodeE]
  cases ι x using WithBotTop.rec <;> simp

/-- A term's encoding: when it is `+∞`, when `−∞`, and its value otherwise. -/
structure EncTerm where
  top : IForm
  bot : IForm
  val : ITerm

def Term.enc : Term → EncTerm
  | .const z => WithBotTop.rec (motive := fun _ => EncTerm) ⟨.ff, .tt, .const 0⟩
      (fun k => ⟨.ff, .ff, .const k⟩) ⟨.tt, .ff, .const 0⟩ z
  | .var x => ⟨.not (.notTop x), .and (.notTop x) (.not (.notBot x)), .var x⟩
  | .add a b => ⟨.and (.not (.or a.enc.bot b.enc.bot)) (.or a.enc.top b.enc.top),
      .or a.enc.bot b.enc.bot, .add a.enc.val b.enc.val⟩
  | .neg a => ⟨a.enc.bot, a.enc.top, .smul (-1) a.enc.val⟩
  | .smul c a => if 0 < c then ⟨a.enc.top, a.enc.bot, .smul c a.enc.val⟩
      else if c < 0 then ⟨a.enc.bot, a.enc.top, .smul c a.enc.val⟩
      else ⟨.ff, .ff, .const 0⟩
  | .max a b => ⟨.or a.enc.top b.enc.top, .and a.enc.bot b.enc.bot,
      .ite a.enc.bot b.enc.val (.ite b.enc.bot a.enc.val
        (.ite (.le a.enc.val b.enc.val) b.enc.val a.enc.val))⟩
  | .min a b => ⟨.and a.enc.top b.enc.top, .or a.enc.bot b.enc.bot,
      .ite a.enc.top b.enc.val (.ite b.enc.top a.enc.val
        (.ite (.le a.enc.val b.enc.val) a.enc.val b.enc.val))⟩

/-- The encoding is exact, and never both `+∞` and `−∞`. -/
theorem Term.eval_decode (M : IModel) : ∀ t : Term,
    ¬(t.enc.top.holds M ∧ t.enc.bot.holds M) ∧
      t.eval M.decode = decodeE (t.enc.top.holds M) (t.enc.bot.holds M) (t.enc.val.eval M)
  | .const z => by
    cases z using WithBotTop.rec <;> simp [Term.enc, Term.eval, IForm.holds, ITerm.eval, decodeE]
  | .var x => by
    simp only [Term.enc, Term.eval, IForm.holds, ITerm.eval, IModel.decode, decodeE]
    cases M.notTop x <;> cases M.notBot x <;> simp
  | .add a b => by
    obtain ⟨xa, ha⟩ := Term.eval_decode M a
    obtain ⟨xb, hb⟩ := Term.eval_decode M b
    simp only [Term.enc, Term.eval, IForm.holds, ITerm.eval, ha, hb]
    generalize a.enc.top.holds M = Ta, a.enc.bot.holds M = Ba, b.enc.top.holds M = Tb,
      b.enc.bot.holds M = Bb at *
    cases Ta <;> cases Ba <;> cases Tb <;> cases Bb <;>
      simp_all [decodeE, coe_add_coe, EInt.add_top, EInt.top_add]
  | .neg a => by
    obtain ⟨xa, ha⟩ := Term.eval_decode M a
    simp only [Term.enc, Term.eval, ITerm.eval, ha]
    generalize a.enc.top.holds M = Ta, a.enc.bot.holds M = Ba at *
    cases Ta <;> cases Ba <;> simp_all [decodeE, negE]
  | .smul c a => by
    obtain ⟨xa, ha⟩ := Term.eval_decode M a
    rcases lt_trichotomy c 0 with hc | rfl | hc
    · have hc' : ¬0 < c := by omega
      simp only [Term.enc, Term.eval, ha, if_neg hc', if_pos hc, smulE]
      generalize a.enc.top.holds M = Ta, a.enc.bot.holds M = Ba at *
      cases Ta <;> cases Ba <;> simp_all [decodeE, ITerm.eval]
    · simp only [Term.enc, Term.eval, ha, smulE]
      generalize a.enc.top.holds M = Ta, a.enc.bot.holds M = Ba at *
      cases Ta <;> cases Ba <;> simp_all [decodeE, ITerm.eval, IForm.holds] <;> rfl
    · have hc' : ¬c < 0 := by omega
      simp only [Term.enc, Term.eval, ha, if_neg hc', if_pos hc, smulE]
      generalize a.enc.top.holds M = Ta, a.enc.bot.holds M = Ba at *
      cases Ta <;> cases Ba <;> simp_all [decodeE, ITerm.eval]
  | .max a b => by
    obtain ⟨xa, ha⟩ := Term.eval_decode M a
    obtain ⟨xb, hb⟩ := Term.eval_decode M b
    simp only [Term.enc, Term.eval, IForm.holds, ITerm.eval, ha, hb]
    generalize a.enc.top.holds M = Ta, a.enc.bot.holds M = Ba, b.enc.top.holds M = Tb,
      b.enc.bot.holds M = Bb at *
    cases Ta <;> cases Ba <;> cases Tb <;> cases Bb <;> simp_all [decodeE, max_def]; split <;> rfl
  | .min a b => by
    obtain ⟨xa, ha⟩ := Term.eval_decode M a
    obtain ⟨xb, hb⟩ := Term.eval_decode M b
    simp only [Term.enc, Term.eval, IForm.holds, ITerm.eval, ha, hb]
    generalize a.enc.top.holds M = Ta, a.enc.bot.holds M = Ba, b.enc.top.holds M = Tb,
      b.enc.bot.holds M = Bb at *
    cases Ta <;> cases Ba <;> cases Tb <;> cases Bb <;> simp_all [decodeE, min_def]; split <;> rfl

/-- `lhs ≤ rhs`: `lhs` is `−∞`, `rhs` is `+∞`, or both are finite and compare. -/
def Atom.enc (a : Atom) : IForm :=
  .or a.lhs.enc.bot (.or a.rhs.enc.top
    (.and (.not a.lhs.enc.top) (.and (.not a.rhs.enc.bot) (.le a.lhs.enc.val a.rhs.enc.val))))

theorem Atom.holds_decode (M : IModel) (a : Atom) : a.Holds M.decode ↔ a.enc.holds M := by
  obtain ⟨x₁, h₁⟩ := a.lhs.eval_decode M
  obtain ⟨x₂, h₂⟩ := a.rhs.eval_decode M
  simp only [Atom.Holds, Atom.enc, IForm.holds, h₁, h₂]
  generalize a.lhs.enc.top.holds M = T₁, a.lhs.enc.bot.holds M = B₁, a.rhs.enc.top.holds M = T₂,
    a.rhs.enc.bot.holds M = B₂ at *
  cases T₁ <;> cases B₁ <;> cases T₂ <;> cases B₂ <;> simp_all [decodeE]

/-- The formulas a solver is given for `Ψ`. -/
def encode (Ψ : List Con) : List IForm := Ψ.flatMap fun c => c.atoms.map Atom.enc

theorem sat_decode (M : IModel) (Ψ : List Con) :
    Sat M.decode Ψ ↔ ∀ φ ∈ encode Ψ, φ.holds M := by
  simp only [Sat, Con.P, encode, List.mem_flatMap, List.mem_map, Atom.holds_decode]
  exact ⟨fun h φ ⟨c, hc, a, ha, he⟩ => he ▸ h c hc a ha, fun h c hc a ha => h _ ⟨c, hc, a, ha, rfl⟩⟩

theorem sat_iff (ι : Asgn) (Ψ : List Con) :
    Sat ι Ψ ↔ ∀ φ ∈ encode Ψ, φ.holds (IModel.ofAsgn ι) := by
  rw [← sat_decode, decode_ofAsgn]

/-- `Ψ` is satisfiable exactly when its encoding is. -/
theorem sat_exists (Ψ : List Con) : (∃ ι, Sat ι Ψ) ↔ ∃ M : IModel, ∀ φ ∈ encode Ψ, φ.holds M :=
  ⟨fun ⟨ι, h⟩ => ⟨_, (sat_iff ι Ψ).mp h⟩, fun ⟨M, h⟩ => ⟨_, (sat_decode M Ψ).mpr h⟩⟩

/-- The query: `precBound Ψ l m ≤ p` exactly when every model of `Ψ`'s encoding
satisfies the encoded `m − l + 1 ≤ p`. -/
theorem precBound_le_iff (Ψ : List Con) (l m : Term) (p : ℤ) :
    precBound Ψ l m ≤ p ↔ ∀ M : IModel, (∀ φ ∈ encode Ψ, φ.holds M) →
      (Atom.enc ⟨l.width m, .const p⟩).holds M := by
  simp only [precBound, iSup₂_le_iff, ← Atom.holds_decode]
  refine ⟨fun h M hM => h _ ((sat_decode M Ψ).mpr hM), fun h ι hι => ?_⟩
  have := h _ ((sat_iff ι Ψ).mp hι)
  rwa [decode_ofAsgn] at this

theorem Term.ne_bot_decode (M : IModel) (t : Term) :
    t.eval M.decode ≠ ⊥ ↔ t.enc.bot.holds M = false := by
  obtain ⟨x, h⟩ := t.eval_decode M
  rw [h]
  generalize t.enc.top.holds M = T, t.enc.bot.holds M = B at *
  cases T <;> cases B <;> simp_all [decodeE]

theorem Term.ne_top_decode (M : IModel) (t : Term) :
    t.eval M.decode ≠ ⊤ ↔ t.enc.top.holds M = false := by
  obtain ⟨x, h⟩ := t.eval_decode M
  rw [h]
  generalize t.enc.top.holds M = T, t.enc.bot.holds M = B at *
  cases T <;> cases B <;> simp_all [decodeE]

/-- The implementation's query: `precBoundFin Ψ l m ≤ p` exactly when every
model of `Ψ`'s encoding where `l` is not `−∞` and `m` not `+∞` satisfies the
encoded `m − l + 1 ≤ p`. -/
theorem precBoundFin_le_iff (Ψ : List Con) (l m : Term) (p : ℤ) :
    precBoundFin Ψ l m ≤ p ↔ ∀ M : IModel, (∀ φ ∈ encode Ψ, φ.holds M) →
      l.enc.bot.holds M = false → m.enc.top.holds M = false →
      (Atom.enc ⟨l.width m, .const p⟩).holds M := by
  simp only [precBoundFin, iSup₂_le_iff, ← Atom.holds_decode, ← Term.ne_bot_decode,
    ← Term.ne_top_decode]
  refine ⟨fun h M hM hl hm => h _ ⟨(sat_decode M Ψ).mpr hM, hl, hm⟩,
    fun h ι ⟨hι, hl, hm⟩ => ?_⟩
  have := h _ ((sat_iff ι Ψ).mp hι) (by rwa [decode_ofAsgn]) (by rwa [decode_ofAsgn])
  rwa [decode_ofAsgn] at this

end Fpy.DigitBound
