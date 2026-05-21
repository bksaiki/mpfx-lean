# Autoformalization TODO — *When Double Rounding is Correct*

Plan reference: `~/.claude/plans/i-d-like-to-autoformalize-warm-kurzweil.md`
Paper reference: `When_Double_Rounding_is_Correct.pdf`.

The full Appendix A is mechanized: format containment (`containsPrec`,
`containsSub`), Lemmas 5.1/5.2/5.3 (`numDigits`, `numDigits_shift`,
`precisionAtMost_not_IsOdd` and friends), and all double-rounding rules
from Fig. 9 (`rndRTZ_RTZ`, `rndRAZ_RAZ`, `rndRTO_RTO`, `rndRTO_RTZ`,
`rndRTO_RAZ`, `rndRTO_RN`). The double-rounding theorems are stated
paper-aligned; `rndRTO_RAZ` additionally takes an explicit `2 ≤ F₂.p`
hypothesis (a concrete counterexample shows it cannot be derived from the
paper-aligned `F₁.extend 1 ⊆ F₂` alone).

Beyond the paper, the IEEE 754 directed modes (RTP, RTN) and the alternative
tie-break (RNA) are also covered. The unified `rndRTO_RN` theorem covers
both RNE (`tb = .ToEven`) and RNA (`tb = .AwayZero`) via a `TieBreak`
parameter, sharing the bulk of the proof in `rndRTO_nearest_facts`. The
directed-mode theorems `rndRTP_RTP`, `rndRTN_RTN`, `rndRTO_RTP`,
`rndRTO_RTN` are mechanized via sign-reduction.

`rndRNA_RNA` is **not a theorem** — pen-and-paper analysis shows that
RNA→RNA chains can fail at binade-boundary inputs.

There is also a directed `RoundsRTE` (round-to-even, the dual of RTO). It is
a valid rounding mode but `rndRTE_RTE` is **not a theorem** — counterexample
in `Mpfx/Rounding.lean`'s notes — so no double-rounding theorem is stated.

**Unified `Rounds F rm x y` API.** `Rounds : AbstractFormat → RoundingMode →
ℝ → Dyadic → Prop` is a single dispatcher over the seven per-mode predicates,
indexed by `RoundingMode` (which itself takes a `TieBreak` parameter for
`.Nearest`). All public double-rounding theorem signatures use `Rounds F .X
x y` form; the per-mode predicates remain as primitives and helpers continue
to use them internally.

Status legend: `[ ]` not started · `[~]` in progress · `[x]` done · `[!]` blocked.

## Tests & smoke tests

- [ ] Instantiate Fig. 7 formats (`binary64`, `binary32`, `E5M2`, `E4M3`, `int8`, `fixed<-4, 8>`) in `Mpfx/Tests.lean`.
- [ ] `decide` / `native_decide` concrete membership examples per instance.
- [ ] `#check @containsPrec`, `@containsSub`, all seven `rnd*_*` against the paper's notation.
- [ ] Cross-check: `binary32 ⊆ binary64`, `E5M2 ⊆ binary64` via `containsPrec` (and via `containsSub` where applicable).
- [ ] §3.5 numeric example: `rnd_{E5M2,RNE}(1.26)` evaluates correctly.
- [ ] Counterexample: composing E2M1 and E4M3 RNE rounding of 1.26 differs from direct E2M1 RNE rounding.

## Substrate ergonomics

The proofs work via `Dyadic.precisionAtMost` / `Dyadic.quantumAtLeast` /
`AbstractFormat.numDigits` / `AbstractFormat.IsOdd`. Adding direct user-facing
wrappers would simplify smoke tests and external use.

- [ ] Public `Dyadic.precision : Dyadic → ℕ∞` (currently approximated by `numDigits`, which is format-parameterized).
- [ ] Public `Dyadic.quantum : Dyadic → WithBot ℤ`.
- [ ] `Dyadic.toCanonical : Dyadic → ℤ × ℤ` returning `(c, e)` with `c` odd or `c = 0`. Backbone exists in `exists_odd_canonical_of_precisionAtMost`.
- [ ] `Dyadic.isOdd`, `Dyadic.isEven` user-facing predicates (independent of a format).
- [ ] `simp` set for `c * 2^e` normalization (associativity, commutativity, regrouping `c · 2^e = 2c · 2^(e-1)`).

## API polish

- [ ] Merge `exists_grid_rep` and `exists_grid_rep_exp_bot` (and the `_exp_bot` siblings of `no_F_element_in_step_interval`, `F_adjacent_step_form`, `midpoint_mem_extend_one_of_F_adjacent_pos`) under a unified `k = (F.exp.unbotD (log y - p + 1)) ⊔ (log y - p + 1)` form. Trade-off: pushes the `cases F.exp` dispatch inward; the current twin-lemma structure with the dispatcher in `DoubleRounding.lean` is acceptable.
- [ ] Encode `1 ≤ p` at the type level by changing `p : ℕ∞` to `p : WithTop ℕ+`. Drops the `p_pos` field. Significant cast-threading refactor. Investigated previously; left deferred — `p_pos` is fine in practice.
- [ ] Migrate sign-bridge lemmas (`RoundsRTP_iff_RAZ_of_nn`, etc.) to use `Rounds F .X` form for API consistency. Low-priority polish.
- [ ] Migrate private helpers (`rndRTO_no_tie_contradiction`, `rndRTO_RNE_close_transfer`, etc.) to use `Rounds`. Cosmetic.

## Constructive rounding (deferred)

The double-rounding proofs use spec-relational `Rounds`/`RoundsXX` predicates
rather than a constructive `rnd`. A constructive `rnd` would unblock
`decide`-based smoke tests but is not load-bearing for the paper's theorems.

- [ ] `AbstractFormat.adjacents : AbstractFormat → ℝ → Option (Dyadic × Dyadic)`.
- [ ] Existence + uniqueness for adjacents (off-overflow).
- [ ] `rnd : AbstractFormat → RoundingMode → ℝ → Dyadic`.
- [ ] `rnd F rm x ∈ F` for non-overflow inputs.
- [ ] `rnd F rm x = ⟨x, _⟩` when `x ∈ F`.
- [ ] Connect `rnd` to `Rounds` predicate: `Rounds F rm x (rnd F rm x)`.

## Out of scope (paper §9)

Open in the paper itself; not planned for this formalization.

- Special values (signed zero, ∞, NaN).
- Posits, P3109 unsigned floats.
- Overflow semantics for double rounding.
- Subnormal flushing.
