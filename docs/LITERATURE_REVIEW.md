# Targeted literature comparison

Check date: 22 October 2026 UTC. This is a bounded public-source
search, not a finding of priority or an exhaustive citation-index review.

## Exact target and primary sources

| Source | Location and comparison |
| --- | --- |
| Došen–Petrić, [Proof-Theoretical Coherence, September 2007 revision](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf) | §14.2, printed p.322 (PDF page 334), leaves maximality of B open and conjectures nonmaximality. §14.3 defines the zero-identity Boolean categories. §§2.7 and 9.3 give the equational-substitution rule and the schematic/model formulation of maximality. The manuscript's substitution congruences are intended to express that schematic extension. A Lean bridge to the full presentation remains open. |
| Došen–Petrić, [Bicartesian Coherence Revisited, v3](https://arxiv.org/html/0711.4961v3) | §§8–10 treat maximality of lattice categories and relative maximality of dicartesian categories. The abstract explicitly excludes distribution. These results do not by themselves establish maximality of the full zero-identity Boolean signature. |
| Došen–Petrić, [Isomorphic Formulae in Classical Propositional Logic, v3](https://arxiv.org/pdf/0912.1271) | §4, Lemma 6, pp.12–13, gives an arrow with one selected cross-pair in its linking relation, assuming a tautological implication and matching variable occurrences in the top/bottom/conjunction/disjunction fragment. The linking relation is the reflexive, symmetric, transitive closure of the occurrence relation; it is not a generally faithful compositional replacement for that relation. This is a close antecedent for one-edge existence, but does not by itself give the manuscript's selector/coselector factorization of an arbitrary differing pair. Proposition 3 characterizes formula isomorphism under its stated normalization hypotheses. |
| [Petrić's official publication list](https://www.mi.sanu.ac.rs/~zpetric/cv.pdf) | Consulted as a lead; a publication list is not proof that no resolution exists elsewhere. |

The book's zero-identity equation is f ∘ 0_A = 0_B ∘ g for parallel f,g.
An existing-arrow witness is required to define 0_{A,B}. Its §14.3 observation
that B(A,B) is inhabited exactly when A → B is tautological rules out replacing
the target with a blanket zero-morphism category.

## Search and unresolved coverage

Searches included accented and unaccented author names with “Boolean”,
“maximality”, “nonmaximality”, and “zero-identity Boolean”. The primary book
and the related bicartesian paper were the directly relevant returned sources.
The second search engine returned substantial unrelated material; those hits
were not used as evidence. No earlier resolution of this exact B conjecture
was identified in this bounded check.

No comprehensive MathSciNet/zbMATH citation search or author contact was
performed. The broader *-autonomous Boolean-category literature, including
[Straßburger's axiomatisation](https://arxiv.org/pdf/cs/0512086), and all
forward citation chains have not been exhaustively checked in this session.
The continuation bundle records earlier comparison work, but does not replace
an independent current-source review of an alleged equivalent theorem.

Before a priority claim, complete that coverage and compare the actual axioms,
substitution closure, and conclusions. The present formalization remains
useful if an earlier proof is found; attribution would need revision.
