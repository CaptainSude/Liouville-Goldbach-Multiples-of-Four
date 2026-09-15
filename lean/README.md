# Shusterman's Liouville Conjecture for Multiples of Four

Lean verification of the following theorem, with one published theorem supplied as an explicit input:

> Every positive integer divisible by four is the sum of two positive integers whose Liouville values are both −1.

Here λ(n) = (−1)^Ω(n), where Ω counts prime factors with multiplicity. The formal conclusion uses Mathlib's `ArithmeticFunction.liouville`, not an abstract substitute.

## What is verified

The build and assumption audit passed on 15 September 2026. See [the verification record](VERIFICATION.md) and [the build output](BUILD-LOG.txt).

The development proves the elementary descent, the small cases, the scaling argument, and the deduction from the exact published input. The final declaration is `Shusterman.shusterman_multiples_of_four`:

```lean
theorem shusterman_multiples_of_four
    (hM : MangerelNonextremality) {N : ℕ}
    (hN : 0 < N) (hfour : 4 ∣ N) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = N ∧
      ArithmeticFunction.liouville a = -1 ∧
      ArithmeticFunction.liouville b = -1
```

`MangerelNonextremality` states

\[
\left|\sum_{n=1}^{m-1}\lambda(n)\lambda(m-n)\right|<m-1
\quad\text{for every integer }m\ge11.
\]

This is **Theorem 1.2 of Mangerel's published 2024 paper**. It is unconditional mathematics, but its proof is **not formalized in this project**. Accordingly, the Lean result is a checked implication from this explicit input, not an end-to-end formalization of the literature theorem. The input is a theorem parameter, not an added axiom. Its equal-sign consequence is proved in Lean.

## Build

With Lean's standard `elan` installation and Git available, open a terminal in this directory and run:

```text
lake exe cache get
lake build
lake env lean Audit.lean
```

The toolchain is pinned to Lean `v4.34.0-rc2`, and Mathlib to commit `de2ef68216c6074f338c8e61890ee0a379ddfb9b`. Keep `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` together.

`Audit.lean` is included in the default build. It prints the final theorem's type, the precise external input, and logical axiom dependencies, and checks that the final proof uses only `propext`, `Classical.choice`, and `Quot.sound`. The last command above reruns that audit separately. An axiom list does not list explicit hypotheses: the displayed `hM` remains part of the theorem even when the only reported axioms are Lean's standard foundations.

## Proof map

| File | Content |
|---|---|
| `Shusterman/Reflection.lean` | Elementary descent for a sign function reversed by multiplication by two and three. |
| `Shusterman/Liouville.lean` | Actual Liouville values; precise literature input; nonextremality implies an equal-sign pair. |
| `Shusterman/Main.lean` | Scaling from 8 and 12, cases 4, 20, 28, and the final theorem. |
| `Audit.lean` | Theorem and axiom inspection. |
| `SOURCE-AUDIT.md` | Source correspondence and a check of the mathematical argument. |

For N = 4m, divisibility of m by two or three is handled by scaling small examples. Otherwise m is odd and not divisible by three. If there were no negative-negative pair at 4m, the descent would force every pair at m to have opposite signs. Mangerel's theorem excludes this for m ≥ 11; only m = 1, 5, 7 remain.

## Reference and license

Alexander P. Mangerel, *On a Goldbach-Type Problem for the Liouville Function*, International Mathematics Research Notices **2024**, no. 16, 11865–11877, Theorem 1.2. [Published paper](https://doi.org/10.1093/imrn/rnae149). The exact cutoff 11 comes from the published version; the earlier arXiv version states only a sufficiently-large cutoff.

Lean and [Mathlib](https://github.com/leanprover-community/mathlib4) supply the proof checker, arithmetic function definitions, and supporting lemmas. This project's source and accompanying documentation are licensed under Apache 2.0; see `LICENSE`. Dependencies retain their own licenses.
