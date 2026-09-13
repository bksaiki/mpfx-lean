# ulp, succ and pred

Item 4 of [`FLOCQ_ROADMAP.md`](FLOCQ_ROADMAP.md) is done: `ulp` at zero,
`Mpfx/Ulp.lean`, `succ`/`pred` with their involutions, `FiniteFormat.next`,
adjacency through `succ`, the `Discrete.lean` merge, the error bounds and the
bracket characterisations have all landed. One optional cleanup remains; the two
reference sections below record the decisions the implementation rests on.

## Which convention `ulp` follows

`ulp(x)` is not a single notion — definitions disagree at powers of two, where
the gap below `x` is half the gap above. Ours is:

```
ulp F x = 2 ^ canonicalExp F x       canonicalExp F x = max (⌊log₂|x|⌋ + 1 − p) exp
```

At `x = 2^e` this gives `2^(e+1−p)`: the spacing of the binade **above** `x`,
twice the spacing immediately below it. That is Goldberg's convention, and
Flocq's — `mag (2^e) = e+1`, so `cexp = fexp (mag x)` lands in the upper binade
too. Harrison's definition (the distance between the closest straddling pair
`a ≤ x ≤ b`, `a ≠ b`) takes the *smaller* value there, and Kahan's differs
again. We follow Flocq; do not mix conventions mid-development.

**Where this bites, concretely.** With the upper-binade convention,

* `succ x = x + ulp x` is correct at a power of two — the step up really is the
  larger one;
* `pred x = x − ulp x` is **wrong** there — the step down is half that.

So `succ` is uniform and `pred` is not; `predPos` carries the special case. Any
lemma pairing `succ` with `pred` needs checking at `|x| = 2^e`.

## Vocabulary

"Grid" has no Flocq counterpart — the word appears nowhere in Flocq's source.
That is not an oversight: once you have `ulp`, `succ` and discreteness you never
need to name the set of representable values at a fixed exponent.

| concept | word |
| ------- | ---- |
| spacing at `x` | `ulp` |
| next / previous representable value | `succ` / `pred` |
| nothing lies strictly between | discreteness |
| the interval `[2^e, 2^(e+1))` | **`binade`** |
| the lattice at a fixed exponent | *no name needed* |

`binade` is **not** a synonym for "grid". They agree in the normal range, one
binade to one grid, but diverge below it: at precision `p` with minimum quantum
`emin`, everything under
`2^(emin+p−1)` has `canonicalExp = emin`, so one grid of spacing `2^emin` spans
many binades. That divergence is exactly what produced the `_exp_bot` twins.

---

## Optional cleanup

- [ ] **Optional:** rename `Format.next` to something bound-flavoured
      (`nextBound`, `boundStep`) so it does not read as the same notion as
      `FiniteFormat.next`. The two differ — `Format.next` advances a **bound**,
      with a convention at degenerate formats, while `FiniteFormat.next` is the
      **successor**, returning `0` when there is none, and
      `next_eq_format_next` records that they coincide for `b > 0`. ~200 call
      sites, mechanical.
