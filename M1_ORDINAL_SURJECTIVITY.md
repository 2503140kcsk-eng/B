# M1-D — Surjectivity of the source prime-factor CNF map

**Status:** Mathematical proof plan. It has not yet been encoded or checked by Lean. The strengthened invariant below repairs the parity problem in the simpler odd-index attempt.

## 1. Source recursion

For n in N, define C(0)=0. If n>0, put k=n+1, let p be the least prime divisor of k, let v>=1 be the exponent of p in k, and put j=k/p^v. The author-defined recursion is

\[
C(n)=\omega^{C(v-1)}+C(j-1).
\]

The codomain is the ordinals below epsilon-zero, represented in Lean by Mathlib's NONote (normal Cantor-normal-form notations). This map must be implemented as its own recursion; it must not be replaced by the generic library CNF enumerator.

## 2. Correct strengthened invariant

The direct idea of requiring an odd representing index fails: the natural parent construction 2^u*j is always even. The correct invariant controls the prime factors instead.

For every ordinal alpha<epsilon-zero and every natural bound b, prove

\[
\operatorname{Rep}(\alpha,b):
\quad
\exists q\geq1,\quad C(q-1)=\alpha
\quad\land\quad
\forall r\in\operatorname{primeFactors}(q),\ b<r.
\tag{Rep}
\]

Thus q has no prime factor less than or equal to b. The case q=1 is allowed; it has no prime factors.

This stronger statement gives the quotient child the prime-factor separation needed to force an arbitrary chosen prime to be the least prime divisor of the parent.

## 3. Ordinal decomposition

For every nonzero alpha<epsilon-zero, its Cantor normal form has a leading term

\[
\alpha=\omega^\gamma c+\delta,
\]

where c is a positive natural number and delta<omega^gamma. Set

\[
\beta=\omega^\gamma(c-1)+\delta.
\]

By comparison of Cantor normal forms,

\[
\alpha=\omega^\gamma+\beta,\qquad
\gamma<\alpha,\qquad
\beta<\alpha.
\tag{Decomp}
\]

The inequality beta<alpha follows because its leading coefficient is c-1 rather than c, with the same lower tail. The inequality gamma<alpha follows from gamma<omega^gamma<=alpha, with gamma=0 handled by 0<1=omega^0.

In Lean, this should be a lemma about NONote, with the leading exponent, positive coefficient and lower tail exposed explicitly. Do not try to get strict monotonicity in the left argument of ordinal addition: ordinal addition is not strictly monotone there in general.

## 4. Transfinite induction proving Rep

Proceed by well-founded induction on alpha<epsilon-zero, proving Rep(alpha,b) for every b.

**Base alpha=0.** Take q=1. It is positive, C(q-1)=C(0)=0, and has no prime factors, so the prime-factor condition is vacuous for every b.

**Step alpha>0.** Use Decomp to write alpha=omega^gamma+beta with gamma,beta<alpha. By the induction hypotheses, which are uniform in the bound:

- choose u>=1 with C(u-1)=gamma (apply Rep(gamma,0));
- choose j>=1 with C(j-1)=beta and every prime factor r of j satisfies p<r, where p will be chosen next.

Choose any prime p>b. Such a prime exists by infinitude of primes. More formally, first choose p>b, then apply Rep(beta,p) to obtain j; the induction hypothesis is uniform in the bound, so this order is legitimate.

Now put

\[
k=p^u j,\qquad q=k.
\]

Every prime factor of j is strictly greater than p, so p does not divide j. Consequently the prime factorization of k has:
- least prime divisor p;
- p-adic exponent exactly u;
- quotient after removal of p^u exactly j.

Also every prime factor of k is greater than b: the new factor p is greater than b, and every prime factor of j is greater than p.

The source recursion at q-1=k-1 therefore gives

\[
\begin{aligned}
C(q-1)
 &=\omega^{C(u-1)}+C(j-1)\\
 &=\omega^\gamma+\beta\\
 &=\alpha.
\end{aligned}
\]

This proves Rep(alpha,b).

Taking b=0 yields a representing natural q for every alpha<epsilon-zero, so C is surjective onto the ordinals below epsilon-zero.

## 5. Why the prime-factor invariant matters

The key step is not merely that j is coprime to p. It is that all prime factors of j are greater than p. This guarantees that p is the least prime divisor of p^u*j, not just one of its divisors. It also guarantees that the exponent of p in the product remains exactly u.

This is why the induction hypothesis must be uniform in an arbitrary lower bound b. A mere existence statement for an arbitrary q would not let us choose a parent prime p below every prime factor of the quotient representation.

## 6. Lean/Mathlib API plan at v4.35.0

The repository uses Lean 4.35.0. Mathlib tag v4.35.0 is pinned to match it.

Inspected modules and relevant components:

- Mathlib/SetTheory/Ordinal/Notation.lean
  - ONote.oadd e n a represents omega^(repr e) * n + repr a.
  - ONote.NF and ONote.NFBelow certify Cantor normal form.
  - NONote is the subtype of ONote satisfying NF.
  - NONote.opow constructs ordinal exponentiation and preserves normal form.
  - Addition on NONote preserves normal form; repr_add and repr_opow connect the representation to ordinal arithmetic.
- Mathlib/Data/Nat/Prime/Nth.lean
  - Nat.nth Nat.Prime enumerates the prime numbers.
- Mathlib/Data/Nat/Factorization/Basic.lean
  - Nat.factorization, Nat.factorization_mul, Nat.factorization_pow.
  - Nat.Prime.pow_dvd_iff_le_factorization.
  - Nat.mul_factorization_le gives a useful bound on prime exponents.
- Mathlib/Data/Nat/Factorization/PrimePow.lean
  - Prime-power and minimum-prime-factor factorization lemmas.
- Natural-number minimum-prime-factor API
  - Nat.minFac_prime and Nat.minFac_dvd.

A Lean implementation should proceed in this order:

1. Define the source recursion on n by well-founded recursion.
2. Prove the recursive arguments v-1 and j-1 are strictly below n.
3. Return NONote.opow omegaNote (C(v-1)) + C(j-1), where omegaNote is the NONote representation of omega.
4. Prove the prime-factor separation lemma: if p is prime and every prime factor of j is greater than p, then p is the least prime factor of p^u*j and its factorization exponent is u.
5. Formalize Rep(alpha,b) by transfinite induction over NONote.
6. Prove surjectivity by taking b=0.
7. Prove the representation equality between NONote.repr and the source ordinal expression.

The critical technical tasks are to prove the ordinal decomposition from NONote's CNF structure and formalize the prime-factor condition with Mathlib's primeFactors/factorization API. No theorem should be marked complete until these steps are checked in Lean.

## 7. Completion status

- Source recursion: transcribed in M1_SOURCE_AUDIT.md.
- Mathematical surjectivity argument: the prime-factor-bound invariant above supplies a valid proof strategy.
- Lean source map: not yet implemented.
- Recursive termination: not yet proved by Lean.
- Surjectivity theorem: not yet Lean-checked.
- Equivalence with the author's precise ordinal notation: not yet Lean-checked.

This document is a proof plan, not a machine-verified result.
