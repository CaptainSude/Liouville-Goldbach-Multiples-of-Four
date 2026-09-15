# Source and elementary-proof audit

Audited on 15 September 2026. This is an audit of the mathematical input and the handwritten argument, not a report that the Lean build has passed.

## Exact published input

Alexander P. Mangerel, *On a Goldbach-Type Problem for the Liouville Function*, **International Mathematics Research Notices** 2024(16), 11865–11877, DOI [10.1093/imrn/rnae149](https://doi.org/10.1093/imrn/rnae149), **Theorem 1.2**, proves unconditionally that

\[
\left|\sum_{1\le n<m}\lambda(n)\lambda(m-n)\right|<m-1
\qquad(m\ge11).
\]

The [publisher's full text](https://academic.oup.com/imrn/article/2024/16/11865/7704606) explicitly states this threshold. The [Durham copy](https://durham-repository.worktribe.com/OutputFile/2782464) is the published article; its indexed abstract confirms the threshold, although direct retrieval returned HTTP 403 during this audit. The earlier [arXiv:2404.12117](https://arxiv.org/abs/2404.12117) states only a sufficiently-large threshold and should not be the sole source for the numerical cutoff. The published paper explains that the effective refinement came after that earlier version.

Mangerel also restates the all-\(m\ge11\) bound and its equal-sign consequence in §1.1 of [arXiv:2412.17199v1](https://arxiv.org/html/2412.17199v1). That paper's later GRH-dependent results are **not** inputs here.

The exact consequence needed is

\[
\forall m\ge11\quad\exists a,b\in\mathbb N,\quad
0<a,\quad0<b,\quad a+b=m,\quad\lambda(a)=\lambda(b).
\]

Indeed, if every pair had opposite signs, all \(m-1\) terms in the correlation would be \(-1\), so its absolute value would be \(m-1\). This contradicts the displayed bound. The same equal-pair statement holds for \(-\lambda\), because negating both signs preserves equality.

## Formalization boundary

The local pinned Mathlib tree contains `ArithmeticFunction.liouville`, its prime-factor-count definition, its nonvanishing on positive integers, and its complete multiplicativity. A targeted search found no Mangerel correlation theorem or formal proof of this equal-pair consequence. The unrelated occurrences of “Liouville” in complex analysis and transcendence theory do not provide it.

Therefore the honest deliverable is a kernel-checked proof of the multiples-of-four theorem **from an explicit parameter expressing Mangerel's published theorem (or the equal-pair consequence)**. This leaves one established unconditional literature input outside Lean. It introduces no number-theoretic conjecture, but is not an end-to-end Lean proof of Mangerel's theorem. The final README and theorem names should expose this distinction; an assumption must not be disguised as a proved declaration. Using the full correlation statement and proving its equal-pair consequence in Lean makes the source-to-code correspondence particularly direct.

## Reflection lemma: audit passed

The reflection lemma formalized in `Shusterman/Reflection.lean` is valid for odd \(m>1\) with \(3\nmid m\). It requires only signs in \(\{-1,1\}\) and the identities \(f(2n)=-f(n)\), \(f(3n)=-f(n)\). The formal statement assumes these identities on all positive integers; the proof only uses arguments below \(4m\). It does not require complete multiplicativity or \(f(1)=1\), so it applies to both \(\lambda\) and \(-\lambda\).

The absence of a negative-negative pair at \(4m\) rules out a negative-negative pair at \(m\), by multiplication by four, and a positive-positive pair at \(2m\), by multiplication by two. Every new argument is positive and smaller than \(4m\).

If a positive-positive pair \(a+b=m\) has \(b=3c\), then \(c>0\), \(m-c>0\), and the sign chain is

\[
f(c)=-1,\quad f(m-c)=1,\quad f(3m-b)=-1,\quad f(m+b)=1.
\]

This produces the forbidden positive-positive pair \(a+(m+b)=2m\). The same argument interchanging \(a,b\) excludes \(3\mid a\). As \(3\nmid m\), the two nonzero residue classes of \(a,b\) must be equal. Consequently

\[
a'=(m+a)/3,\qquad b'=(m+b)/3
\]

are positive integers below \(m\), with sum \(m\). The forbidden positive-positive pairs at \(2m\) force \(f(m+a)=f(m+b)=-1\), hence \(f(a')=f(b')=1\). Oddness ensures \(a\ne b\), and

\[
0<|a'-b'|=|a-b|/3<|a-b|.
\]

Choosing the original pair with minimal positive difference gives a valid finite descent. No additional analytic input is hidden in it.

## Scaling and small cases: audit passed

For each positive multiplier \(d\), complete multiplicativity multiplies both signs by \(\lambda(d)\in\{-1,1\}\). Thus having both equal-sign patterns survives multiplication by any positive integer; their labels may interchange.

| Target | Negative-negative pair | Positive-positive pair |
|---|---|---|
| \(4\) | \(2+2\) | None required |
| \(8\) | \(3+5\) | \(4+4\) |
| \(12\) | \(5+7\) | \(6+6\) |
| \(20\) | \(3+17\) | \(4+16\) |
| \(28\) | \(5+23\) | \(14+14\) |

The signs follow directly from prime factorizations. For \(N=4m\), the scaled cases \(8\) and \(12\) cover \(2\mid m\) and \(3\mid m\), respectively. Otherwise \(m\) is odd and \(3\nmid m\). Below eleven the only such positive \(m\) are \(1,5,7\), handled by \(N=4,20,28\). For \(m\ge11\), Mangerel's equal-pair input contradicts the reflection lemma if either prescribed equal-sign pattern at \(4m\) is absent. This covers all positive multiples of four.

## Conclusion

No mathematical error was found in the stated multiples-of-four argument or its finite cases. The only non-formalized literature dependency identified by this audit is the exact, published, unconditional Mangerel input above. This audit does not establish publication novelty and does not report any result for the unresolved \(4k+2\) case.
