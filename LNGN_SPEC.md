# LNGN specification audit

## 1. Published headline definition

The community pages report the Large Number Garden Number as

\[
\mathrm{LNGN}=f^{10}(10\uparrow^{10}10),
\]

where the ten up-arrows are Knuth's up-arrow operation and f is the uncomputable function constructed from a theory described as first-order logic beyond higher-order set theory.

This document records the source-level outline, not an independent proof that every semantic clause is consistent or unambiguous.

## 2. Theory outline in the published description

The published construction can be summarized as follows.

1. Begin with a first-order set-theoretic language L extended by a unary function symbol U.
2. Let ZF_L contain the ZF axioms expressed in L, with the comprehension and replacement schemas ranging over L-formulae.
3. Internally construct a formal language, written here as corner-L, whose symbols include countably many variables, constants, function symbols, relation symbols, and a Henkin-style function symbol Θ. The symbols and finite formula strings are explicitly coded by natural numbers using an ordinal-based symbol coding and Gödel coding.
4. Construct a formalized ZFC theory in that language, then extend it by a Henkin axiom schema. The resulting theory is denoted ZFCH_corner-L in the source.
5. Add axioms U1, U2, U3 describing a sequence U(alpha) of structures. In outline, U1 says the relevant U(alpha) satisfies the formalized theory; U2 imposes coherence of the U-indexing; U3 says each U(alpha) is isomorphic, in the stated membership sense, to a suitable von Neumann rank V_beta.
6. Set T = ZF_L together with U1, U2, U3. The construction then uses interpretations U(CNF(i)), where CNF maps a natural-number code to an ordinal below epsilon_0 through Cantor normal form.

## 3. Definition of the function f (transcribed outline)

For a formula P, IsDefinition(P) expresses that there exists exactly one x satisfying P. Definable(m,i,P) is intended to assert:

- i is a natural-number index;
- P is a formula of the internally constructed language;
- the structure U(CNF(i)) satisfies IsDefinition(P);
- the same structure satisfies P with the candidate value m substituted for the designated free variable.

The Japanese explanatory page describes f(n) as the sum of the distinct natural numbers m for which there exist i and P with i < n, MetaCode(P) < n, and Definable(m,i,P). Because there are finitely many indices and formula codes below n, the intended sum is finite.

The exact syntax, coding conventions, variable-substitution operation, interpretation of CNF, and satisfaction relation must be copied from the creator's original specification before a full Lean semantics port is considered complete. In particular, a community page can summarize the source and is not a replacement for auditing the original post.

## 4. Definition-status caveat

The English Googology Wiki list explicitly marks LNGN's well-definedness as not yet determined. The Japanese page also describes the number as expected to be the largest defined googolism in a dated community snapshot, not as an established mathematical maximum.

Do not conflate these statements:

- a syntactic expression is written down;
- a theory is specified;
- the theory has a model or is consistent relative to stated assumptions;
- the intended f is a uniquely determined total function;
- the resulting natural number has a unique value.

The project must track each separately.

## 5. Why GCN compares within one interpretation

The original author's discussion of growth-rate comparisons warns that comparisons between numbers defined in different theories can be meaningless unless the embedding into a common base theory is fixed.

GCN avoids making an unqualified cross-theory claim. It uses exactly the same interpreted f and the same initial value s as LNGN, and proves an ordinary natural-number inequality inside that shared interpretation:

- L(f) = iterate f 10 s;
- P_f(n) is the finite prefix maximum of f through n;
- E_f(n) = max(n+1, 2^(n+1), P_f(n)+1);
- GCN(f) = iterate E_f (L(f)+1) L(f).

The kernel-level arithmetic theorem is independent of assumptions about f's monotonicity, computability, or growth rate. Only the semantic instantiation of f remains to be formalized.

## 6. Textual audit items

The English and Japanese community summaries are not perfectly identical in their abbreviated wording of the summation condition. The Japanese explanatory description explicitly mentions MetaCode(P) < n. The formalization must use the creator's original post as canonical and preserve the original exact definition rather than silently reconciling secondary summaries.

## 7. Primary and secondary reading list

- Creator-source entry point: https://googology.fandom.com/ja/wiki/ユーザーブログ:P進大好きbot/高階集合論を超えた1階述語論理
- Japanese community exposition: https://googology.fandom.com/ja/wiki/巨大数庭園数
- English community exposition: https://googology.fandom.com/wiki/Large_Number_Garden_Number
- Creator's comparison caveat: https://googology.fandom.com/wiki/User_blog:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/Growth_rates_of_my_functions
