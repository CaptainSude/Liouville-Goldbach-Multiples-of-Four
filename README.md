# Liouville's Goldbach Problem for Multiples of Four

**Every positive integer divisible by four is the sum of two positive integers whose Liouville values are both −1.**

The Liouville function is $\lambda(n)=(-1)^{\Omega(n)}$, where $\Omega(n)$ counts prime factors with multiplicity. Thus the two summands each have an odd number of prime factors, counted with multiplicity.

**[Read the two-page paper](paper/liouville-goldbach-multiples-of-four.pdf)** · [Editable manuscript](paper/liouville-goldbach-multiples-of-four.md) · [Lean proof](lean/Shusterman/Main.lean)

## The result and its proof

Shusterman asked whether every even integer greater than two has such a representation. This paper proves the assertion for every positive multiple of four. It combines Mangerel's published correlation theorem with an elementary descent, scaling, and three small cases. The paper gives the full argument and credits the earlier multiples-of-eight case and the known conditional result for sufficiently large even integers.

## What Lean verifies

The mathematical result is unconditional. The Lean proof is a checked implication from **one explicit published input**: Mangerel's Theorem 1.2 in IMRN (2024), which states

$$
\left|\sum_{n=1}^{m-1}\lambda(n)\lambda(m-n)\right|<m-1
\qquad(m\ge11).
$$

The accompanying development proves the elementary deduction from that bound, including the descent, scaling, and finite cases, using Mathlib's actual Liouville function. Mangerel's theorem itself is supplied as a parameter; its proof is not formalized here.

The final declaration is `Shusterman.shusterman_multiples_of_four`. The build includes an audit of its type and axiom dependencies. There are no unfinished proofs or added project axioms; this does not remove the explicit Mangerel hypothesis.

See the [Lean guide](lean/README.md), [verification record](lean/VERIFICATION.md), and [source audit](lean/SOURCE-AUDIT.md).

## Rebuild the proof

Install Lean using [the official instructions](https://lean-lang.org/install/), then run these commands from the repository's top folder:

```text
cd lean
lake exe cache get
lake build
```

The toolchain and all dependency revisions are pinned. `lake build` also checks `Audit.lean`. To display that audit again, run `lake env lean Audit.lean` from the `lean` folder.

The GitHub workflow, once installed, performs the same build in `lean/`. Its green check concerns the stated formal implication; it does not formalize the external theorem.

## Contents

- `paper/`: the PDF, editable manuscript, license, and optional typesetting source.
- `lean/`: the proof, pinned build files, and verification documentation.
- `LICENSES.md`: the distinction between the paper's and code's licenses.

The paper has no author line. The paper and manuscript use **CC BY 4.0**; Lean and typesetting code use **Apache 2.0**.

## References

1. M. Shusterman, *Goldbach's conjecture for the Liouville function*, MathOverflow, 3 August 2018. [Original question](https://mathoverflow.net/q/307479).
2. A. P. Mangerel, *On a Goldbach-Type Problem for the Liouville Function*, International Mathematics Research Notices **2024**, no. 16, 11865–11877. [Published paper](https://doi.org/10.1093/imrn/rnae149).
3. A. P. Mangerel, *On Shusterman's Goldbach-type problem for sign patterns of the Liouville function*, arXiv:2412.17199 (2024). [Paper](https://arxiv.org/abs/2412.17199).
