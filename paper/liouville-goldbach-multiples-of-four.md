# Liouville's Goldbach Problem for Multiples of Four

## The problem

For a positive integer $n$, let $\lambda(n)=(-1)^{\Omega(n)}$, where $\Omega(n)$ counts prime factors with multiplicity. Thus $\lambda(p)=-1$ for every prime $p$, and $\lambda(ab)=\lambda(a)\lambda(b)$ for all positive integers $a,b$.

In 2018, Shusterman asked whether every even integer $N>2$ can be written as $N=a+b$ with $a,b>0$ and $\lambda(a)=\lambda(b)=-1$ [1]. This weakens the binary Goldbach conjecture: each summand need only have an odd number of prime factors, counted with multiplicity.

Mangerel proved an unconditional correlation bound [2], recalled below. He later proved Shusterman's assertion for all sufficiently large even integers under the Generalised Riemann Hypothesis for Dirichlet $L$-functions [3, Theorem 1.2]. The same paper records an elementary unconditional proof for multiples of eight [3, Section 6.2]. We prove the following.

**Theorem.** Every positive integer divisible by four is the sum of two positive integers whose Liouville values are both $-1$.

The only external theorem needed is Mangerel's bound [2, Theorem 1.2]:

$$
\left|\sum_{n=1}^{m-1}\lambda(n)\lambda(m-n)\right|<m-1\qquad(m\geq11).
$$

In particular, some pair summing to $m$ has equal Liouville values: otherwise every term would be $-1$, making the absolute value exactly $m-1$. The descent below turns this unspecified equal-sign pair at $m$ into a pair of negative signs at $4m$.

## A descent

**Lemma.** Let $m>1$ be odd and not divisible by three. If no pair of positive integers summing to $4m$ has both Liouville values $-1$, then

$$
\lambda(n)=-\lambda(m-n)\qquad(1\leq n<m).
$$

**Proof.** Multiplication by four preserves Liouville values, so there is no pair of negative signs summing to $m$. Multiplication by two reverses them, so there is no pair of positive signs summing to $2m$.

It remains to exclude a pair $a+b=m$ with $\lambda(a)=\lambda(b)=1$. Suppose such a pair exists. Since $m$ is odd, we may order each such pair with $a<b$. Choose one minimizing $b-a$.

First, neither summand is divisible by three. If $b=3c$, then $\lambda(c)=-1$. The absence of a pair of negative signs at $m$ forces $\lambda(m-c)=1$, and hence

$$
\lambda(3m-b)=\lambda(3(m-c))=-1.
$$

The complement of $3m-b$ at $4m$ is $m+b$, so $\lambda(m+b)=1$. But $a+(m+b)=2m$ is now a forbidden pair of positive signs. Interchanging $a$ and $b$ also excludes divisibility of $a$ by three.

Since $3$ does not divide $m=a+b$, the nonzero residues of $a$ and $b$ modulo three must be equal. Therefore

$$
a'=\frac{m+a}{3},\qquad b'=\frac{m+b}{3}
$$

are positive integers with $a'+b'=m$. The pairs $b+(m+a)=2m$ and $a+(m+b)=2m$ force $\lambda(m+a)=\lambda(m+b)=-1$. Multiplication by three reverses Liouville values, so $\lambda(a')=\lambda(b')=1$. Yet

$$
0<b'-a'=\frac{b-a}{3}<b-a,
$$

contradicting minimality. Thus every pair at $m$ has opposite signs, as claimed. $\square$

## Completing the proof

Write $N=4m$. Suppose first that $m\geq11$ and neither two nor three divides $m$. If the required pair at $4m$ were absent, the lemma would force every summand in (1) to be $-1$, contradicting Mangerel's bound.

Next observe that

$$
8=3+5=4+4,\qquad12=5+7=6+6.
$$

For each total, the first pair has two negative signs and the second has two positive signs. Multiplying all summands by any positive integer $d$ multiplies both signs by $\lambda(d)$, so these two possibilities are either preserved or interchanged. Hence every multiple of eight or twelve has a pair of negative signs. This covers $2\mid m$ and $3\mid m$.

The only positive integers $m<11$ divisible by neither two nor three are $1,5,7$. They are covered by

$$
4=2+2,\qquad20=3+17,\qquad28=5+23,
$$

whose summands are all prime. This proves the theorem. $\square$

**Formal verification.** The accompanying Lean 4 development checks the elementary argument and the deduction from Mangerel's bound, using Mathlib's Liouville function. Mangerel's published theorem is an explicit input; its proof is not part of the formalization. The mathematical theorem above is unconditional.

## References

1. M. Shusterman, *Goldbach's conjecture for the Liouville function*, MathOverflow question 307479, 3 August 2018. https://mathoverflow.net/q/307479
2. A. P. Mangerel, *On a Goldbach-Type Problem for the Liouville Function*, International Mathematics Research Notices **2024**, no. 16, 11865-11877. https://doi.org/10.1093/imrn/rnae149
3. A. P. Mangerel, *On Shusterman's Goldbach-type problem for sign patterns of the Liouville function*, arXiv:2412.17199, 2024. https://arxiv.org/abs/2412.17199
