# M1-A — Primary-source lock and definition audit

**Audit date:** 2026-11-01  
**Status:** Primary author source identified; immutable revision identifiers and revision history pinned. The transcription below records the adopted source convention. Semantic ambiguities are recorded rather than silently repaired.  
**Scope:** This file is a source manifest and mathematical transcription. It does not claim that M1-B through M1-H, or the full LNGN semantics, have been formalized.

## 1. Canonical source and revision pin

The canonical primary source is the original author's Japanese blog post:

- **Author:** P進大好きbot
- **Title:** 「高階集合論を超えた1階述語論理」
- **Original publication:** 2019-12-03 09:52:57 UTC (MediaWiki revision 19450)
- **Original immutable revision:** [oldid=19450](https://googology.fandom.com/ja/wiki/ユーザーブログ:P進大好きbot/高階集合論を超えた1階述語論理?oldid=19450)
- **Latest author revision found in the revision-history API:** 2023-10-19 15:58:35 UTC (revision 61601)
- **Adopted immutable revision:** [oldid=61601](https://googology.fandom.com/ja/wiki/ユーザーブログ:P進大好きbot/高階集合論を超えた1階述語論理?oldid=61601)
- **Revision history:** [MediaWiki revision API](https://googology.fandom.com/ja/api.php?action=query&format=json&prop=revisions&titles=ユーザーブログ%3AP進大好きbot%2F高階集合論を超えた1階述語論理&rvprop=ids%7Ctimestamp%7Cuser%7Ccomment&rvlimit=max&formatversion=2)

The history returned ten author revisions: 19450 (2019-12-03), 19522 (2019-12-05), 19523 (2019-12-05), 19524 (2019-12-05), 19525 (2019-12-05), 19813 (2019-12-20), 19962 (2019-12-24), 20249 (2020-01-01), 20285 (2020-01-04), and 61601 (2023-10-19). The last revision's edit comment says it incorporates a mistake report by okkuu. We therefore pin both the first revision and the corrected author revision; the latter is canonical for transcription.

**Archival limitation:** The revision-history endpoint supplied the exact revision IDs, timestamps, authorship and edit comment. The source page itself was readable in the web retrieval used for this audit, but direct extraction of the oldid page URLs returned HTTP 403 in the extraction service. The immutable MediaWiki permalinks above are recorded; this repository does not claim to contain a byte-for-byte HTML snapshot or a cryptographic digest of the source page. A later archival pass should save a permitted WARC/PDF/text snapshot and record its SHA-256.

Secondary references are useful for cross-checking the headline expression, but are not authoritative where they abbreviate the source:

- [Japanese community exposition](https://googology.fandom.com/ja/wiki/巨大数庭園数)
- [English community exposition](https://googology.fandom.com/wiki/Large_Number_Garden_Number)
- [Older Miraheze exposition](https://googology.miraheze.org/wiki/Large_Number_Garden_Number)

Adoption rule: when a secondary page omits or compresses a condition, use the author revision 61601, not the secondary paraphrase. Do not infer a missing convention from the name of an encoding or from a standard textbook presentation.

## 2. Source-defined languages and symbols

The source uses two distinct languages. They must not be conflated.

### 2.1 The ambient language L

Start with first-order set theory whose variables are x_i for i∈N and whose primitive relation is membership ∈. Add one unary function symbol U. Call the resulting language L.

ZF_L is the collection of ZF axioms expressed in L, with Separation and Replacement schemes ranging over **all L-formulae**, including formulae using U.

### 2.2 The internally formalized language

The source formalizes a further first-order language, written here as ⌜L⌝. Its symbol-code constants are:

| Source code | Meaning |
|---:|---|
| 0 | ⊥ |
| 1 | → |
| 2 | ¬ |
| 3 | ∃ |
| 4 | left parenthesis |
| 5 | right parenthesis |
| 6 | Constant category |
| 7 | Variable category |
| 8 | Function category |
| 9 | Relation category |

The ordinal weights are Number = ω, Index = ω², and Arity = ω³. A symbol represented by the tuple (a₀,a₁,a₂,a₃) has ordinal code
\[
\omega^3a_3+\omega^2a_2+\omega a_1+a_0.
\]
The specific symbol assignments are:

\[
\begin{aligned}
\ulcorner c_i\urcorner&=\mathrm{Index}\cdot i+\mathrm{Number}\cdot0+\mathrm{Constant},\\
\ulcorner x_i\urcorner&=\mathrm{Index}\cdot i+\mathrm{Number}\cdot1+\mathrm{Variable},\\
\ulcorner U\urcorner&=\mathrm{Arity}\cdot1+\mathrm{Index}\cdot0+\mathrm{Number}\cdot2+\mathrm{Function},\\
\ulcorner\Theta\urcorner&=\mathrm{Arity}\cdot1+\mathrm{Index}\cdot0+\mathrm{Number}\cdot3+\mathrm{Function},\\
\ulcorner f_{a,i}\urcorner&=\mathrm{Arity}\cdot a+\mathrm{Index}\cdot i+\mathrm{Number}\cdot4+\mathrm{Function},\\
\ulcorner\in\urcorner&=\mathrm{Arity}\cdot2+\mathrm{Index}\cdot0+\mathrm{Number}\cdot5+\mathrm{Relation},\\
\ulcorner r_{a,i}\urcorner&=\mathrm{Arity}\cdot a+\mathrm{Index}\cdot i+\mathrm{Number}\cdot6+\mathrm{Relation}.
\end{aligned}
\]

The usual symbols ∧,∨,∀,= are abbreviations in the source, not extra primitive token codes in the displayed list. The internally formalized language adds countably many constants c_i, function symbols f_{a,i} of arity a, relation symbols r_{a,i} of arity a, and the unary function symbol Θ to the formalized L-language.

The source defines Parameter(c) as the constant symbol code (Constant,c) and Interpret(p) as its unique inverse when it exists. A structure M is viewed as a structure with parameter constants for elements of its domain.

**Important source note:** the author says that c_i, f_{a,i}, r_{a,i}, unlike Θ, are not given meanings and are present to facilitate embeddings of other theories. However, the definition of Formula below is over the full symbol set and does not visibly exclude these symbols. This is retained as a formalization obligation in §8; it is not resolved by deleting these symbols.

## 3. Formula strings, fresh variables and substitution

For a class X, Symbol_X contains the primitive logical tokens and the symbols of ⌜L⌝_X. Symbol is Symbol_∅. Formula is the collection of finite strings over Symbol that are well-formed ⌜L⌝-formulae. Formula_- is the corresponding collection with Θ excluded.

For a finite set S of symbol strings, New(S) is the **least** natural number j such that x_j occurs in none of the strings in S.

Substitution P[t/x] replaces free occurrences of x by the term t. For an existential formula ∃y(Q), if y occurs in t, the source first renames the bound variable y to x_New({P,t,x}), applying the corresponding substitution to Q, and then performs the requested substitution. The adopted implementation must use this least-fresh-variable convention, not merely an arbitrary alpha-renaming routine.

The source uses only ∃ as primitive quantifier; universal quantification is an abbreviation. A Lean AST may be used internally, but its serializer and parser must be proved to preserve exactly the source token-string language and this substitution convention.

## 4. Finite sequence and formula coding

For a finite sequence a=(a₀,…,a_{h−1})∈N^{<ω}, let p_i be the (i+1)-th prime; thus p₀=2, p₁=3, and so on. The source defines:
\[
\mathrm{Encode}(a)=2^h\prod_{i=0}^{h-1}p_{i+1}^{a_i}-1.
\]

In particular the prime 2 records the length, while the primes 3,5,7,… record the entries (including entries equal to zero, whose prime factors are absent).

Each symbol tuple in N⁴ is first encoded as a natural number. A finite formula is then represented by the finite sequence of its symbol codes, and Encode is applied again. The resulting natural number is MetaCode(P).

The decoder must be partial. For a candidate code n, factor n+1, set h=v₂(n+1), recover the h exponents of p₁,…,p_h, and accept the code only if the remaining cofactor is 1. Otherwise return none. For h=0, the empty sequence is decoded only when n=0. This rejects natural numbers that are not in the range of Encode; it must not silently map invalid codes to an arbitrary sequence.

Required theorem contracts for the sequence codec:

1. decode(encode(a)) = some(a) for every finite sequence a.
2. Therefore encode is injective.
3. encode(decode(n)) = n whenever decode(n) = some(a).
4. A code outside the range is reported as invalid (none), not coerced into a valid syntax object.

A Wolfram Language prototype checked sample round trips for [], [0], [1], [0,0], [0,1,0], [3,2,5], and [0,0,0,0]. This is a finite test only, not a proof and not a Lean CI result.

## 5. Numeral codes and the Henkin extension

For n∈ω, the source denotes by Formalise(n) a formula of ZFC_⌜L⌝ with x₀ as its only free variable, defining the numeral n by the source's repeated-successor formalization. Code(P) is Formalise(MetaCode(P)).

The source defines the Henkin axiom Henkin_{i,P} as the formalized assertion:

> If there exists an x_i satisfying P, then for every x₀, if Code(P) holds, then P[Θ(x₀)/x_i] holds.

The quantified scheme is indexed by i∈ω and P∈Formula_-. The resulting theory is
\[
\overline{ZFC}_{\ulcorner L\urcorner}
=ZFC_{\ulcorner L\urcorner}\cup
\{Henkin_{i,P}:i\in\omega,\ P\in\mathrm{Formula}_-\}.
\]

The distinction between Formula and Formula_- is mandatory: P in the Henkin scheme excludes Θ, while the later definition of Definable quantifies over Formula.

The exact Lean construction of Formalise(n) still needs to pin down the token-level formula for the empty set and the successor iteration from the primary source's numeral convention. It must not be replaced with Lean's Nat literal notation, because the code is a formula *inside* ZFC_⌜L⌝.

## 6. Theory T and its model sequence

The source defines:

- U1: for every ordinal α, U(α) ⊨ overline(ZFC)_⌜L⌝.
- U2: for every ordinal α and every β∈α, the interpretation of the internal symbol U in U(α), evaluated at β, equals the external U(β).
- U3: for every ordinal α, there is an ordinal β such that |U(α)|=V_β, and the membership relation interpreted inside U(α) agrees with actual membership on V_β.

Finally,
\[
T=ZF_L\cup\{U1,U2,U3\}.
\]

T is a first-order theory in the ambient language L. A Lean formalization must represent the syntax of its axioms, the structure interpreting L, the family of internal structures U(α), and the satisfaction relation explicitly. U1 is an axiom of the theory; it is not an external proof that a model of T exists.

The author notes that a universe hierarchy of this broad kind can be constructed in ZFC augmented by a Grothendieck-universe axiom. This is a source assertion/motivation, not a relative-consistency proof included in this repository. Any model-existence theorem must state the exact large-universe assumptions used and prove the model construction under those assumptions.

## 7. The ordinal map CNF and the function f

### 7.1 Source's recursive CNF map

The source's map is a specific prime-factor recursion, not simply the generic library function named Ordinal.CNF.

\[
\mathrm{CNF}(0)=0.
\]
For i>0, let p be the least prime dividing i+1, let v≥1 be its exponent in i+1, and let j=(i+1)/p^v. Then
\[
\mathrm{CNF}(i)=\omega^{\mathrm{CNF}(v-1)}+
\mathrm{CNF}(j-1).
\]
The author asserts that this is surjective onto the ordinals below ε₀, because every such ordinal has Cantor normal form.

A termination proof is available from elementary bounds: 2^v≤i+1 gives v≤i for i>0, hence v−1<i; and j≤(i+1)/2 gives j−1<i. The Lean definition should use well-founded recursion and prove both recursive arguments smaller than i. Surjectivity remains a theorem to prove; it must not be inferred solely from termination.

Mathlib has relevant representations in Mathlib/SetTheory/Ordinal/Notation.lean, whose NONote type represents ordinals below ε₀ in Cantor normal form, and generic Ordinal.CNF machinery in Mathlib/SetTheory/Ordinal/CantorNormalForm.lean. These are candidate library components, not proof of equivalence with the source's prime-factor map. The formalization must construct the source map and prove its relationship to the chosen Mathlib representation.

### 7.2 IsDefinition and Definable

For a formula P, IsDefinition(P) is the internal formula expressing:
\[
\exists x_0\,P(x_0)\quad\land\quad
\forall x_1\,(P[x_1/x_0]\to x_1=x_0).
\]
Thus it says that exactly one object satisfies P, relative to the model's satisfaction relation and assignment convention.

The source's Definable(m,i,P) is the ambient L-formula asserting:

1. i∈N;
2. P∈Formula;
3. U(CNF(i)) ⊨ IsDefinition(P);
4. U(CNF(i)) ⊨ P[Parameter(m)/x₀].

The parameter insertion must be implemented using the source's Parameter constant convention; it is not a native numeral substitution in Lean.

### 7.3 The finite sum

The source defines f(n) as the sum of those natural numbers m for which **there exist** i and P satisfying
\[
i\in n,\quad P\in\mathrm{Formula},\quad
\mathrm{MetaCode}(P)\in n,\quad
\mathrm{Definable}(m,i,P).
\]

Equivalently, define the set
\[
S_n=\{m\in\mathbb N\mid
\exists i<n,\exists P\in\mathrm{Formula},\
\mathrm{MetaCode}(P)<n\land\mathrm{Definable}(m,i,P)\}
\]
and let f(n)=∑_{m∈S_n}m.

**Adopted multiplicity rule:** each value m is counted once, even if several pairs (i,P) witness its definability. The source's summation variable is m, with i,P existentially quantified; summing over witness triples would be a different function.

Finiteness follows conditionally once (a) the sequence/formula code is injective and decodable, so there are finitely many formulas with MetaCode(P)<n, and (b) IsDefinition(P) gives at most one m for each pair (i,P). Totality of f:N→N then follows from finite summation. These implications still require Lean proofs under the formal semantics.

The headline number is
\[
\mathrm{LNGN}=f^{10}(10\uparrow^{10}10),
\]
where the source uses ten Knuth up-arrows and ten-fold function iteration.

## 8. Mandatory semantic audit gates (not silently discharged)

The source transcription exposes three points that must be answered before claiming a canonical, model-independent f.

### A. Extra signature symbols

The author says c_i,f_{a,i},r_{a,i} have no intended meaning, but Formula is built from the full Symbol and Definable ranges over all Formula. A model of a language with extra constants/functions/relations must interpret them. Unless a theorem shows that their interpretations cannot change the set S_n, or the source proves an equivalent reduced-language definition, their arbitrary interpretations may affect formula satisfaction and therefore Definable.

**Required result:** either (i) prove invariance of S_n and f(n) under all permitted interpretations of these symbols, or (ii) prove that the source's actual syntax excludes them from the formulae used in f, with a source-backed correction, or (iii) state a chosen expansion as an explicit parameter and make the resulting f relative to it. Do not quietly discard the symbols.

### B. Free variables in Henkin formulae

The Henkin scheme is indexed by P∈Formula_-, but the source clause does not visibly restrict P to have no free variables other than x_i, nor does it fully spell out the assignment convention for the other free variables in the displayed implication.

**Required result:** fix the source's intended free-variable/assignment convention and prove the Henkin clause under it. If an additional restriction is needed, document it as a source interpretation decision rather than silently strengthening the axiom scheme.

### C. Model existence and invariance

U1 asserts that the values of U are models of the internal Henkin theory, while U2 and U3 impose coherence and a rank/universe condition. These axioms do not themselves prove externally that a model of T exists. Nor does the source's motivating Grothendieck-universe remark alone establish that all required U(α), expansions, and satisfaction relations are unique or invariant.

**Required result:** state a precise assumption package (for example, a specific universe hierarchy plus the needed expansion/Henkin constructions), prove the model sequence under that package or mark it as an explicit assumption, and prove that all allowed choices give the same S_n and f if a canonical external natural number is claimed.

Until A–C are resolved, a theorem about one chosen model family is a conditional instantiation, not an unconditional proof that the source phrase determines one unique external function.

## 9. Tool and repository work allocation

The following assignments separate evidence generation from proof checking.

| Resource | Assigned responsibility | Evidence status and boundary |
|---|---|---|
| leanprover-community/mathlib4 | Main Lean library for NONote/ordinal operations, finite sets, recursion, and reusable syntax/logic API | Library source inspected; no theorem here substitutes for the source-equivalence proof |
| lean-dojo/LeanDojo-v2 | Locate existing declarations and suggest candidate Lean lemmas/tactics | Retrieval and suggestions only; Lean kernel remains the proof checker |
| cvc5/cvc5 | Check bounded arithmetic/finite-code obligations and selected first-order fragments after exact translation | No decision claim for full ZFC, class models, or the complete satisfaction relation |
| naproche/naproche | Organize human-readable definitions and proof arguments; detect prose gaps | Not a proof assistant for the full Lean development |
| sympy/sympy | Prototype prime-factor sequence encoding/decoding and finite test vectors | Tests do not prove injectivity or compute the uncomputable f |
| sagemath/sage | Prototype ordinal notation and test finite examples of the source CNF recursion | Experiments do not prove surjectivity or model existence |
| Macaulay2/M2 | Reserve for a concrete algebraic subproblem if one emerges | No central algebraic subproblem is currently identified |
| gap-system/gap | Reserve for a concrete finite group/combinatorial subproblem if one emerges | No group-theoretic obligation is currently identified |
| Sider Scholar | Search literature on ordinal notations, formal set-theory semantics and proof-assistant encodings | Search did not supply the primary LNGN source; primary source is the author blog above |
| Wolfram | Check small encoding examples and arithmetic identities independently | Computational checks are diagnostic, not proof |
| Context7 | Retrieve current Lean 4 / Mathlib API documentation | Documentation informs implementation; it does not certify code |
| Parallel Search | Locate primary/secondary pages and source revision metadata | Search excerpts and extracts are evidence pointers, not formal proof |
| GitHub | Pin commits, preserve this audit, run CI and publish run/axiom records | Only the target repository is writable through the current connection |

All eight user-supplied mathematical repositories were accessible as public read-only repositories in this session; their connection permissions did not include push access. The target 2503140kcsk-eng/B was writable.

## 10. Baseline verification boundary

The existing arithmetic theorem was CI-verified on source commit
2e85c1a2ce2ec0408de2d9784ca88fb568dc6450 by [run 41303244693](https://github.com/2503140kcsk-eng/B/actions/runs/41303244693), using Lean 4.35.0, lake build --wfail, and the configured axiom audit.

The current main head observed during this audit was
17deb9b1658e235ab265a3f93448a5f91658d8e6. A GitHub compare showed exactly one commit ahead of the CI-tested commit and exactly one changed file: FORMALIZATION_STATUS.md. Thus the Lean source and workflow were unchanged, but the success record is still attached to the earlier exact commit; it must not be relabelled as a run on the newer head.

The present audit adds documentation only. It does not claim a new Lean build, an axiom audit of source semantics, or completion of M1-B through M1-H.

## 11. Completion ledger

| Milestone | Status at this commit | What remains |
|---|---|---|
| M1-A source lock | Primary author source and revision history identified; source conventions transcribed and decision rules recorded | Cryptographic byte snapshot; settle semantic gates A–C before claiming the source fully determines one canonical external f |
| M1-B syntax and Gödel coding | Not implemented in Lean | Inductive grammar, parser/serializer, exact prime codec, round trips, injectivity, invalid-code behavior |
| M1-C substitution | Source convention transcribed only | Lean implementation, fresh-variable proof, no-capture theorem, semantic substitution lemma |
| M1-D ordinal CNF | Source recursion transcribed only | Lean recursion, termination, normal-form evaluation, surjectivity, source/Mathlib equivalence |
| M1-E theory and models | Axioms transcribed only | Formal structures/satisfaction, consistency/model assumptions, coherence and invariance theorems |
| M1-F function f | Mathematical finite-sum definition transcribed | Formal IsDefinition, Definable, unique-witness and finite-sum lemmas, totality and source match |
| M1-G GCN bridge | Generic theorem already exists | Construct source-relative f, prove identity with generic parameter, instantiate exact theorem |
| M1-H final audit | Baseline arithmetic CI/axiom record exists for its exact commit | CI on semantic implementation commit, zero warnings, no sorry/unapproved axioms, exact logs and assumptions |

A milestone is not complete merely because its specification is written down. Every checkmark must link to a Lean declaration or a reproducible artifact and to the exact commit that was checked.
