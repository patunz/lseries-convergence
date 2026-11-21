# The L-series of an elliptic curve over ℚ converges for Re s > 3/2

A Lean 4 proof, downstream of [Tau Ceti](https://github.com/TauCetiProject/TauCeti), that the
Dirichlet series of Mathlib's `WeierstrassCurve.LFunction` converges absolutely on the half-plane
`Re s > 3/2`.

```lean
theorem LSeriesConv.lseriesSummable_LFunction (W : WeierstrassCurve ℚ) {s : ℂ}
    (hs : 3 / 2 < s.re) : LSeriesSummable (fun n => ((W.LFunction n : ℤ) : ℂ)) s

theorem LSeriesConv.norm_LFunction_prime_pow_le (W : WeierstrassCurve ℚ) {p : ℕ}
    (hp : p.Prime) (k : ℕ) : ‖((W.LFunction (p ^ k) : ℤ) : ℂ)‖ ≤ (k + 1) * √(p : ℝ) ^ k

theorem LSeriesConv.abscissaOfAbsConv_LFunction_le (W : WeierstrassCurve ℚ) :
    LSeries.abscissaOfAbsConv (fun n => ((W.LFunction n : ℤ) : ℂ)) ≤ (3 / 2 : ℝ)
```

The coefficient bound holds at every prime, of good or bad reduction. No `sorry`, no
`native_decide`; `#print axioms` on the three theorems gives
`[propext, Classical.choice, Quot.sound]`.

## Status and caveats

- **Pinned** to Tau Ceti `b608709b45f23ccda55703d572b0adb1fdec30fd` (Lean `v4.37.0-rc1`,
  Mathlib `31ce06ea`). It is not part of Tau Ceti and has not been through its review.
- **Over `ℚ` only.** The local bound (`norm_coeff_localPowerSeries_le`) is stated for any
  discrete valuation ring with finite residue field; the global step is not done for number
  fields.
- **Summability only.** The equality with a convergent Euler product, and non-vanishing on the
  half-plane, are not proved. `3/2` is not shown to be optimal.
- **Not house style.** The files do not use the module system, they `import Mathlib` wholesale,
  and their comments and docstrings are in Italian.
- **Novelty not established.** A search of Mathlib, Tau Ceti, and public Lean repositories on
  21 November 2026 found no earlier formal proof of this statement. That is a search, not a proof
  of absence.
- **Verification.** `scripts/build.sh` was run once on a clean machine (21 November 2026) and
  reproduced the build and the axiom check. Both runs were the author's; an independent rebuild
  is welcome.
- **AI assistance.** The Lean code was written with Claude (Anthropic).

## What is used and what is new

From Tau Ceti:

- `WeierstrassCurve.isMultiplicative_LFunction`
- `WeierstrassCurve.localPolynomial_eq_of_hasGoodReduction`
- `WeierstrassCurve.frobeniusTrace_sq_le_four_mul_card` (the Hasse bound)

In this repository:

| File | Lines | Content | Depends on |
|---|---|---|---|
| `LSeriesConv/Analysis.lean` | 185 | If `f` is the inverse of `(1 - αT)(1 - βT)` with `‖α‖, ‖β‖ ≤ r`, then `‖coeff k f‖ ≤ (k + 1) r ^ k`. If `a² ≤ 4q`, then `1 - aT + qT²` splits over `ℂ` with reciprocal roots of norm at most `√q`. A summability criterion: a nonnegative multiplicative `F : ℕ → ℝ` with `F 1 = 1` is summable if its sums over the positive powers of each prime are dominated by a summable function. | Mathlib |
| `LSeriesConv/EulerAtPrime.lean` | 118 | The value at `p ^ k` of `ArithmeticFunction.eulerProduct` of factors `ofPowerSeries (q i) (f i)` is the `k`-th coefficient of the factor with `q i = p`. | Mathlib |
| `LSeriesConv/Main.lean` | 239 | The local bound for every reduction type; the residue field of `ℚ` at `p` is `ZMod p`; `W.LFunction (p ^ k)` as a coefficient of the local power series; the theorem. | Tau Ceti |

Outline: `F n = ‖a_n‖ · n ^ (-σ)` is multiplicative; at each prime
`F (p ^ k) ≤ (k + 1) y ^ k` with `y = p ^ (1/2 - σ) ≤ 1/2`, so the sum over positive powers is at
most `C · p ^ (1/2 - σ)`, which is summable over `p` because `σ - 1/2 > 1`.

## Building

Needs `git`, [`elan`](https://github.com/leanprover/elan) and
[`uv`](https://docs.astral.sh/uv/) (Tau Ceti's cache script uses it).

```bash
scripts/build.sh
```

This clones Tau Ceti at the pinned commit into `_tc/`, registers `LSeriesConv` as a library in
its `lakefile.toml`, fetches the Mathlib and Tau Ceti caches, builds, and prints the axioms of the
three theorems. On a clean 8-vCPU machine the whole script took about three minutes, and used
about 15 GB of disk.

## License

Apache 2.0, the same as Tau Ceti and Mathlib. See [LICENSE](LICENSE).
