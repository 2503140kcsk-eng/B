# Proof sketch for the Garden Canopy construction

This is the ordinary-mathematics explanation of the Lean theorem. It is not a substitute for the Lean source; it explains why the finite construction works.

Fix any total function f from natural numbers to natural numbers. No monotonicity, computability, or growth assumption is made.

Let

- L = f applied to itself ten times, starting at the same Knuth-arrow seed as LNGN;
- P(n) = max(f(0), ..., f(n));
- E(n) = max(n+1, 2^(n+1), P(n)+1);
- x_0 = L and x_(k+1) = E(x_k);
- GCN = x_(L+1).

## Lemma 1: P(n) dominates the current value

The finite list used to define P(n) contains f(n). Therefore

\[
f(n)\le P(n).
\]

## Lemma 2: Every E-step strictly increases the current value

By definition,

\[
E(n)\ge n+1>n.
\]

Thus x_(k+1) > x_k at every step. All iterations are finite because the number of steps is the natural number L+1.

## Lemma 3: Every E-step beats f at the current input

Again by the definition of maximum,

\[
E(n)\ge P(n)+1> P(n)\ge f(n).
\]

In particular, x_1 = E(L) > f(L). Since later x-values increase, GCN > f(L).

## Lemma 4: The first E-step already reaches an exponential lower bound

\[
E(L)\ge 2^{L+1}.
\]

Since later E-steps never decrease the value,

\[
\mathrm{GCN}=x_{L+1}\ge x_1=E(L)\ge 2^{L+1}.
\]

## Main theorem: GCN strictly exceeds LNGN

The LNGN expression under this same interpretation of f is exactly L. Since L+1 is one of the lower bounds in E(L), we have E(L)>L. Subsequent iterations increase the value, so

\[
\boxed{\mathrm{GCN}>L=\mathrm{LNGN}}.
\]

Combining the results gives

\[
\boxed{\mathrm{GCN}>\max(L,f(L))}
\qquad\text{and}\qquad
\boxed{\mathrm{GCN}\ge 2^{L+1}}.
\]

The comparison is internal to one shared interpretation of f. This avoids asserting an unqualified ordering between numbers based on unrelated formal theories.

## What this proof does not establish

The Lean theorem quantifies over every total f. It does not yet define the particular source-theoretic function f from the LNGN construction. The semantic bridge from the author's theory T, coded syntax, satisfaction relation, and model sequence to a concrete total function Nat → Nat remains a separate milestone. The theorem becomes a theorem about the canonical LNGN instantiation once that bridge is formalized.
