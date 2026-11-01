# Formalization status and long-term plan

## Status at project initialization

This repository is a fresh research project. The files currently describe a proposed definition and a general Lean theorem. Do not treat the exact source-theory semantics of LNGN as formalized.

| Layer | Status | Evidence required to upgrade |
|---|---|---|
| Definition of prefix maximum and amplification | Implemented in Lean source | Successful Lean build |
| Totality of finite iteration | By structural recursion in Lean | Successful Lean build |
| GCN(f) > L(f), for arbitrary f : Nat → Nat | Theorem written | Successful Lean build and kernel check |
| GCN(f) > f(L(f)) | Theorem written | Successful Lean build and kernel check |
| Exact Knuth-arrow seed convention | Defined recursively in Lean | Successful Lean build plus comparison against standard recurrence |
| Exact author-defined T, formal language, code maps and substitution | Not formalized | Line-by-line transcription and Lean definitions |
| U(alpha) model sequence, satisfaction relation and coherence axioms | Not formalized | Explicit semantic encoding, with assumptions exposed |
| Existence/consistency of required model sequence | Not proved here | A separate relative-consistency/model-existence argument or explicit assumptions |
| Identity between source f and Lean's f parameter | Not established | A theorem connecting the semantic construction to Nat → Nat |
| Instantiated canonical GCN natural number | Conditional on the above identity | Successful semantic bridge theorem |

## Long-term research milestones

### M0 — Baseline arithmetic proof
- Compile the Lean source under the pinned Lean toolchain.
- Inspect all warnings and eliminate warnings under --wfail.
- Record workflow run URL, commit SHA, and job log.
- Verify the source contains no sorry, admit, or unapproved axioms.

### M1 — Freeze the source definition
- Obtain the original author post and archive its exact revision/date.
- Define the syntax tree and Gödel coding without prose-level ambiguities.
- Fix the natural-number coding of variables, symbols, finite lists, formulae, substitution, and MetaCode.
- Reconcile all secondary-page discrepancies from the primary source only.

### M2 — Formalize the arithmetic and syntax
- Define formula syntax as a Lean inductive type.
- Define variable binding and capture-avoiding substitution.
- Define Gödel encoding/decoding and prove round-trip properties.
- Define CNF coding and prove the required properties of codes below epsilon_0.
- Prove finiteness of the relevant set of formula codes below every n.

### M3 — Formalize the theory and semantics
- Represent the theory T as an explicit collection of sentences.
- Define structures, satisfaction, transitivity, the U-indexed sequence, and the U1/U2/U3 conditions.
- Make all consistency, universe, and model-existence assumptions explicit. Never smuggle them in as implicit axioms.
- Prove that the source definition of f determines a unique natural number at every input under the stated assumptions.

### M4 — Bridge theorem
- Construct or parameterize f from the source semantics.
- Prove that this f is total.
- Connect the source's f(n) summation to the finite Lean implementation.
- Instantiate the GCN domination theorem with that exact f.

### M5 — Independent audit
- Re-check all definitions with a second formalization route (Rocq/Coq or an independently written Lean module).
- Use independent reviewers/tools to inspect the coding and semantic bridge.
- Keep proof-producing tools separate from the trusted proof kernel.
- Publish a proof status report with exact assumptions, axioms, and CI evidence.

## Roles for the linked mathematical repositories

These repositories are not interchangeable proof engines. Their use is scoped to tasks where they can add evidence:

| Repository | Appropriate role | What it cannot establish by itself |
|---|---|---|
| leanprover-community/mathlib4 | Main library candidate for ordinal, finite-set, syntax, and order lemmas | It does not remove the need to state the semantic assumptions of T |
| lean-dojo/LeanDojo-v2 | Search/retrieval and tactic-suggestion support for Lean proof development | Suggestions are not proof certificates; Lean's kernel remains the checker |
| cvc5/cvc5 | SMT checks for bounded arithmetic and first-order fragments after encoding | It cannot decide the intended full set-theoretic truth/satisfaction relation |
| naproche/naproche | Natural-language proof organization and controlled mathematical prose | It does not replace a kernel-checked semantics port |
| sympy/sympy | Small finite test cases for prefix maxima, iteration, and coding prototypes | It cannot evaluate the uncomputable source function f |
| sagemath/sage | Experimental ordinal notation and fast-growing hierarchy prototypes | Numerical experiments do not prove model existence or semantic identity |
| Macaulay2/M2 | Reserve for any algebraic subproblem that emerges in the coding/model analysis | No algebraic subproblem is currently central |
| gap-system/gap | Reserve for finite combinatorial/group-structure experiments if such a subproblem emerges | It does not address the current set-theoretic semantics |

## Integrity rules

- A passing CI run proves only that the submitted Lean project compiles under that toolchain and its imported axioms.
- A theorem quantified over arbitrary f proves a conditional arithmetic statement; it does not itself construct the source's f.
- A paper, wiki page, search result, or AI-generated proof sketch is not formal verification.
- Do not label GCN as “the world's largest number.”
- Do not call the semantic bridge complete until it is represented by definitions and theorems and has a successful kernel check.
