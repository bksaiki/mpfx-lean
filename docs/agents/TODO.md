# Autoformalization TODO — *When Double Rounding is Correct*

Plan reference: `~/.claude/plans/i-d-like-to-autoformalize-warm-kurzweil.md`
Paper reference: `When_Double_Rounding_is_Correct.pdf`.

The full Appendix A is mechanized: format containment (`containsPrec`,
`containsSub`), Lemmas 5.1/5.2/5.3 (`numDigits`, `numDigits_shift`,
`precisionAtMost_not_IsOdd` and friends), and all seven double-rounding rules
from Fig. 9 (`rndRTZ_RTZ`, `rndRAZ_RAZ`, `rndRTO_RTO`, `rndRTO_RTZ`,
`rndRTO_RAZ`, `rndRTO_RNE`). All seven double-rounding theorems are stated
fully paper-aligned (no `hp_F₂`, no F.exp-finite, no auxiliary closeness or
midpoint hypotheses).

Beyond the paper, an extension to the additional IEEE 754 modes (RTP, RTN,
RNA) is planned — see "Additional rounding modes" below.

Status legend: `[ ]` not started · `[~]` in progress · `[x]` done · `[!]` blocked.

## Additional rounding modes (RTP, RTN, RNA)

Extend coverage from the four paper-Fig. 9 modes to the IEEE 754 set. RTP and
RTN are semantic aliases for the existing `RoundsUp` / `RoundsDown` predicates;
RNA is the away-from-zero tie-break variant of RNE.

### Definitions (`Mpfx/Rounding.lean`)
- [ ] `RoundsRTP F x y := RoundsUp F x y` (round to +∞).
- [ ] `RoundsRTN F x y := RoundsDown F x y` (round to −∞).
- [ ] `RoundsRNA F x y` — round to nearest, ties to larger magnitude. Same shape as `RoundsRNE` except the tie-break clause becomes `... → IsLargerMagnitude F y` (or stated directly: `|y| ≥ |z|` for any equidistant `z ∈ F`).
- [ ] Add `RTP | RTN | RNA` constructors to `inductive RoundingMode`.

### Sign-based reduction lemmas (`Mpfx/Rounding.lean`)
The key bridges that let the new theorems reduce to existing ones:
- [ ] `RoundsRTP_iff_RAZ_of_nn : 0 ≤ x → (RoundsRTP F x y ↔ RoundsRAZ F x y)`.
- [ ] `RoundsRTP_iff_RTZ_of_nonpos : x ≤ 0 → (RoundsRTP F x y ↔ RoundsRTZ F x y)`.
- [ ] `RoundsRTN_iff_RTZ_of_nn : 0 ≤ x → (RoundsRTN F x y ↔ RoundsRTZ F x y)`.
- [ ] `RoundsRTN_iff_RAZ_of_nonpos : x ≤ 0 → (RoundsRTN F x y ↔ RoundsRAZ F x y)`.
- [ ] `RoundsRNA_iff_RNE_of_no_tie : (¬ ∃ y₁ y₂, ... midpoint ...) → (RoundsRNA F x y ↔ RoundsRNE F x y)` — RNA equals RNE when there is no tie.
- [ ] `RoundsRNA.neg`, `RoundsRTP.neg`, `RoundsRTN.neg` symmetry lemmas (RTP and RTN swap under negation).

### Double-rounding theorems (`Mpfx/DoubleRounding.lean`)
Fig. 9 only treats RTZ/RAZ/RTO/RNE. The new theorems are derived via sign analysis or parallel proofs:

- [ ] **`rndRTP_RTP`** (`F₁ ⊆ F₂`): split on `sign x`, reduce positive case to `rndRAZ_RAZ`, negative case to `rndRTZ_RTZ`, x = 0 trivial. ~30 lines.
- [ ] **`rndRTN_RTN`** (`F₁ ⊆ F₂`): symmetric to RTP via sign reduction. ~30 lines.
- [ ] **`rndRTO_RTP`** (paper-aligned containment, same as `rndRTO_RTZ` / `rndRTO_RAZ`): split on sign of `x`, reduce to `rndRTO_RTZ` (negative) / `rndRTO_RAZ` (positive).
- [ ] **`rndRTO_RTN`**: symmetric.
- [ ] **`rndRTO_RNA`** (paper-aligned containment, same as `rndRTO_RNE`): the `notMem_of_extend_subset` chain forces `z ≠ midpoint(w', z')`, so `x` lies strictly off-midpoint and **no tie occurs in F₁ rounding** — RNE and RNA coincide on the actual round-step. The proof body is a near-copy of `rndRTO_RNE` with the tie-break clause swapped from `IsEven` to "larger magnitude". Likely shareable scaffolding via a parametric helper over the tie-break predicate.
- [ ] **`rndRNA_RNA`** (paper-aligned containment): closer to `rndRTO_RNE`'s structure but harder — RNA→RNA chains can produce ties differently. Likely needs the same `notMem_of_extend_subset` trick + a same-side-of-midpoint argument. May require a separate lemma `RoundsRNA.notMem_of_extend_subset` analogous to `RoundsRTO.notMem_of_extend_subset` but with RNA's parity-discrimination semantics.

### Estimated effort
- Definitions + sign-bridge lemmas: ~150 lines (`Mpfx/Rounding.lean`).
- `rndRTP_RTP`, `rndRTN_RTN`, `rndRTO_RTP`, `rndRTO_RTN` (sign-reduction theorems): ~150 lines combined.
- `rndRTO_RNA`: ~200 lines (parallels `rndRTO_RNE`'s 180-line body); could share `rndRTO_RNE_close_transfer` if generalized over the tie-break predicate.
- `rndRNA_RNA`: hardest; likely needs new infrastructure analogous to `numDigits_eq_of_subset_of_isOdd` if the RTO-bypass trick doesn't apply directly.

### Suggested order
1. Definitions + sign-reduction bridges.
2. `rndRTP_RTP`, `rndRTN_RTN` (smallest, validates the sign-reduction approach).
3. `rndRTO_RTP`, `rndRTO_RTN` (extension of #2 to RTO-prefix chains).
4. `rndRTO_RNA` (refactor `rndRTO_RNE_close_transfer` to be tie-break-generic, then derive both RNE and RNA versions).
5. `rndRNA_RNA` (last; may surface new infrastructure needs).

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
- [ ] Encode `1 ≤ p` at the type level by changing `p : ℕ∞` to `p : WithTop ℕ+`. Drops the `p_pos` field. Significant cast-threading refactor across numeric literals, `F.p + k`, and `exact_mod_cast`s.

## Constructive rounding (deferred)

The double-rounding proofs use spec-relational `RoundsXX` predicates rather
than a constructive `rnd`. The `RoundingMode` inductive is defined but
unused; a constructive `rnd` would unblock `decide`-based smoke tests but is
not load-bearing for the paper's theorems.

- [ ] `AbstractFormat.adjacents : AbstractFormat → ℝ → Option (Dyadic × Dyadic)`.
- [ ] Existence + uniqueness for adjacents (off-overflow).
- [ ] `rnd : AbstractFormat → RoundingMode → ℝ → Dyadic`.
- [ ] `rnd F rm x ∈ F` for non-overflow inputs.
- [ ] `rnd F rm x = ⟨x, _⟩` when `x ∈ F`.
- [ ] Connect `rnd` to `RoundsXX` predicates (e.g., `RoundsRTZ F x (rnd F .RTZ x)`).

## Out of scope (paper §9)

Open in the paper itself; not planned for this formalization.

- Special values (signed zero, ∞, NaN).
- Posits, P3109 unsigned floats.
- Overflow semantics for double rounding.
- Subnormal flushing.
