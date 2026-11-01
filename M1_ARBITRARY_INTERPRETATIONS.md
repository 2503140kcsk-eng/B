# M1-E / M1-F — Arbitrary interpretations and the finite-sum obstruction

**Status:** A kernel-level counterexample is being formalized in GardenCanopy/M1Semantics.lean. The global U1-U3 model-sequence construction is not yet formalized. This note records the exact consequence of the user's clarified interpretation policy and the minimum repair needed for M1-F.

## 1. Adopted interpretation policy

The symbols c_i, f_(a,i), and r_(a,i) are interpreted independently in each model. In particular, no injectivity or pairwise-distinctness condition is imposed on the parameter constants c_i.

For a model M with domain D, write

\[
\operatorname{par}_M:\mathbb N\to D,\qquad
\operatorname{par}_M(m)=c_m^M.
\]

The source's Parameter(m) is the constant symbol c_m. Its semantic value in M is therefore par_M(m).

## 2. A single-formula obstruction

Fix any nonempty domain D and an element d in D. Consider the following permitted expansion:

\[
c_m^M=d\quad\text{for every }m\in\mathbb N,
\]

\[
r_{1,0}^M(x)\iff x=d,
\]

and interpret the remaining generic function and relation symbols arbitrarily (for example, all generic functions constantly d and all other generic relations as empty).

Let P(x_0) be the one-variable formula

\[
P(x_0)\equiv r_{1,0}(x_0).
\]

Then

\[
M\models P(x_0)\iff x_0=d,
\]

so P uniquely defines the object d. But for every natural m,

\[
\operatorname{Parameter}_M(m)=c_m^M=d,
\]

hence

\[
M\models P[\operatorname{Parameter}(m)/x_0]
\]

for every m.

Let q=MetaCode(P). For every n with q<n and 0<n, the source bounds admit this one fixed witness pair i=0 and P. Therefore the set of qualifying natural indices m contains all of \(\mathbb N\):

\[
S_n^M=\mathbb N.
\]

Consequently \(S_n^M\) is infinite. The source expression “sum the qualifying natural numbers m” is not a finite sum, so it does not define an element of Nat for this permitted expansion.

The Lean semantic interface in GardenCanopy/M1Semantics.lean targets the exact local statement: under the collapsed expansion, the fixed formula r_(1,0)(x_0) is unique-defining, every natural parameter index is a witness, and the bounded candidate-index set is infinite.

## 3. What this does and does not establish

The argument proves that **arbitrary interpretation of the parameter constants alone does not imply the finite-fiber property needed by M1-F**. It is not merely a concern about model-independence: the model-relative set being summed can itself be infinite.

The Lean counterexample is an expansion of a carrier structure. It is not yet a Lean construction of a full ordinal-indexed family U(alpha) satisfying U1, U2, U3, and every Henkin axiom. Thus a full countermodel to the entire theory T has not yet been certified by Lean.

A standard relative model construction is plausible when one assumes a sufficiently tall hierarchy of Grothendieck universes: make c_i, the generic f_(a,i), and the generic r_(a,i) definable from a fixed parameter in each transitive V_kappa; choose Theta as a witness selector for the coded Henkin instances; and make U point to the lower members of the hierarchy. The exact free-variable convention in Henkin's scheme and the required class-length universe assumptions still need a source-faithful proof. Until that construction is formalized, treat it as a conditional model-construction route, not as a completed theorem.

## 4. Minimum repair choices for M1-F

The finite-sum proof requires a finiteness property of the parameter map. A sufficient assumption is injectivity:

\[
\forall m_1,m_2,\quad c_{m_1}^M=c_{m_2}^M\to m_1=m_2.
\]

A weaker sufficient condition is finite fibers:

\[
\forall d\in D,\quad
\{m\in\mathbb N\mid c_m^M=d\}\text{ is finite}.
\tag{FiniteFiber}
\]

If a formula P uniquely defines d, then the qualifying indices m for that fixed (i,P) pair form a subset of this fiber; hence they are finite. Since there are finitely many i<n and finitely many formula codes below n once M1-B is complete, the total set S_n is finite.

The theorem parameterFiber_finite_of_injective in GardenCanopy/M1Semantics.lean formalizes injectivity as a sufficient condition for finite fibers. The finite-fiber condition itself is the exact weaker requirement to target.

Another possible source-level repair is to sum over distinct interpreted objects d rather than over natural indices m. This changes the source's summation variable and must not be adopted without an author-source justification.

## 5. M1-E / M1-F decision

Under the clarified fully arbitrary interpretation policy, the current acceptance criteria are inconsistent with unconditional totality of f unless the theory T or the source definition supplies a finite-fiber restriction.

Therefore:

- Continue to parameterize the semantic function as \(f_M\), indexed by an explicit model family M.
- Prove the finite-sum and totality theorem only under FiniteFiber (or a stronger source-derived condition).
- Keep the fully arbitrary expansion theorem as a counterexample to the unconditional version.
- Do not assert M1-F, M1-G, or the final LNGN/GCN comparison as unconditionally instantiated until this issue is settled.
