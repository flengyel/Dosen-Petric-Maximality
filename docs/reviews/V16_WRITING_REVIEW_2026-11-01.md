# Mathematical-writing review of manuscript v16

1 November 2026. Author-side AI-assisted review applying the mathematical-writing
plugin. Input: v15 at 216bca6e7765eae7a494b712facde55f8311e7cf and the accepted
reverse audit. Output: v16, 23 pages. The review covers the complete source in
reading order, with detailed comparison of the additions and preservation of
the previously reviewed argument. It does not repeat an independent mathematical
review of every Lean proof.

The added explanation serves the author's stated audience: mathematicians
unfamiliar with Lean or proof assistants. It explains a declaration and the
steps of an actual proof, then supplies source links at the relevant mathematics.
The Lean development contributes explicit terms and intermediate equations to
the paper rather than functioning only as an external certification reference.

## Governing source and actual outline

Knuth, Larrabee and Roberts, Mathematical Writing, is the governing prose
source. The [Stanford report](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf),
Section 1 and Sections 4–5, was consulted using the retained copy and text.
The relevant advice concerns complete statements, connected explanations,
notation, reader motivation and unnecessary jargon. No invented quotation or
unverified page number is used. The author's preference for Došen–Petrić's
direct exposition is independent of that source. Their
[revised book](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf),
printed pp.220, 290–291 and 294, supplies the cited union and isomorphism context.

| Existing part, in reading order | Function in v16 |
| --- | --- |
| Abstract; Introduction | State maximality and the literal-equation argument; compare the conjecture and prior results; give the appendix roadmap. |
| Section 2 | Define the category, typed operations, zeros, congruences and main theorem. |
| Section 3 | Define occurrences and G; state coherence; explain signs, negation, substitution blocks, the full substituted relation and substitution action. |
| Section 4 | Prove literal isolation and all K_A; add the general retract calculation before its double-negation instance. |
| Section 5 | Give the q_A/e_A collapse and model corollary; locate the explicit inverse terms in Appendix E. |
| Section 6 | Explain the formalization and alternative symmetric-fold proof; define union and its algebra. |
| A.1–A.3 | Define occurrence maps/fibres, finite-ordinal coordinates and shared-variable substitutions, with examples and squares. Preserved. |
| Appendix B | Give three typed defining diagrams. Preserved. |
| Appendix C | State the two published rank corrections. Preserved. |
| D.1 | Define terms, generated equality, quotient and primitive congruences. Preserved. |
| D.2 | Explain Lean's notation, read the selected maximality type and follow the short proof's mathematical steps. Added. |
| D.3–D.4 | State all five declarations and prove the term/arrow relation correspondence. Preserved, renumbered. |
| D.5 | Explain the coherence proof's objects, splitting equations, positive normal forms and common atomic factorization. Added. |
| E.1–E.3 | Construct the two inverses and both split comparison maps, with their equations. Added. |
| Disclosure; bibliography | Preserve the authorized disclosure and thirteen entries. |

The main dependencies remain occurrence interpretation→isolation→all K_A→equal
projections→maximality, with the model corollary and symmetric-fold alternative.
D.5 explains the proof behind the cited coherence theorem. E supplies terms
needed for the inverse construction and the split comparisons. No alternative
outline is proposed: the main proof stays short and the appendices supply
construction details and the Lean reading guide.

## Source comparison and implemented wording

| Manuscript location and difficulty | Verified source principle or editorial rationale | Implemented action |
| --- | --- | --- |
| Section 3 previously described only substituted endpoints | Section 1, points 10–11 and 14–15: connect formulas to explanations and keep notation consistent | Define R_(f,sigma) on the displayed dependent blocks, compare labelled inner positions in E_sigma, show the square and explain the composition step. |
| Substitution action changes both arrow endpoints | Complete statements and declared notation; explicit typing is also a supplementary convention | State formula and arrow laws together, then specify the endpoint identifications and extensionality. |
| Lemma 5.1 cited the existence of suitable isomorphisms | Reader motivation and sufficient explanation, Section 1 points 12–13 | Retain the cited proof and add explicit q/e inverse paths and their occurrence calculations in E. |
| Code identifiers alone do not explain a theorem to a new reader | Connected explanation and avoidance of unnecessary jargon, points 10–13 and 26 | D.2 explains terms/proofs, binders, fields, namespaces, conclusion and the proof commands used; its table translates four actual proof steps. |
| D.5 could obscure the order in which coherence inputs are proved | Mathematical dependency, independently checked; not a special rule attributed to Knuth | Give source-equation union laws, split comparisons and their typed equations before positive coherence. Distinguish those derivations from Section 6's proof using faithfulness. |
| The normal-form construction needs one inverse equation | Preserve hypotheses and equality direction; explicit editorial rationale | Write i_A,r_A and r_A i_A=1_A, then use that equation in the recovery calculation. |
| Long declaration names disrupt footnote layout | Readable sentences and economical notation, point 17; hyperlink layout is an implementation choice | Omit the common DosenPetric prefix once, allow identifier line breaks and link each name to a fixed source line. |

The most consequential replacement for a bare declaration reference is the
D.2 explanation: “The names closed, hne and hfg name proofs of the three
displayed hypotheses; the expression after the last colon is the conclusion.”
It immediately follows the printed type and is followed by the expansion of
R.Total. The proof table then gives inequality, literal isolation, substitution
and collapse as mathematical implications. No unexplained Lean name is used
as a substitute for the corresponding mathematical assertion.

## Definition order and notation

| Item | First explanation and checked use |
| --- | --- |
| Signed label | Section 3 defines negation parity after occurrence sets and G; the invariant states both label and sign equality. |
| Converse under negation | The arrow reverses endpoints; the formula reverses the ordered pair and identifies the original position sets. |
| chi and R_(f,sigma) | chi names the previously proved block bijection; R has its source/target displayed before the square. Equality in E_sigma avoids comparing unrelated fibre elements. |
| tau star sigma | Defined pointwise before composition laws; P,Q,R are variable sets, distinct from the occurrence relation R_(f,sigma). |
| Retract transport | i,r,theta and r∘i=1_A precede the transported K equation. |
| Union and order | The typed arrow formula precedes the relation formula and algebra; the hom-set existence condition precedes the least element and empty union. |
| Term, Hom, Prop, Derives | D.1 defines the mathematical objects; D.2 distinguishes a datum from its type and a proposition from its proof. |
| Nonempty P; implicit A,B | Explained immediately after the selected declaration; the surrounding universe parameter is made explicit. |
| Dot notation | Namespace qualification, a structure field and the defined property Closed are distinguished. |
| Positive; D_A,C_A; c,s,t | D.5 defines positive terms and the comparison types before using their equations to construct expansions. E gives the structural composites. |
| A',B',u,v,a,b,f_0,g_0 | All types and the common factorization and direct-image equations are displayed before deducing equality. |
| alpha,beta,c,v,b,t | Appendix E fixes associativity/symmetry directions; each new map has its complete source and target. Local v and b names do not alter Section 6's v_A,w_A. |

No new missing definition was established after searching the whole source.
Standard terms include literal, occurrence, relation, retract, section,
retraction, join semilattice and direct image. Lean identifiers are quoted
names with their mathematical content explained. The complete-source search
finds neither “genuine” nor “actual”; meaningful qualifications such as
structural induction and arbitrary formulas remain. All paragraphs have a
mathematical, construction, source-comparison or explicitly authorized
disclosure function. Review/release narration stays outside the manuscript.

The syntax explanation was compared with the official manual:
[dependent types](https://lean-lang.org/theorem_proving_in_lean4/Dependent-Type-Theory/),
[propositions and proofs](https://lean-lang.org/theorem_proving_in_lean4/Propositions-and-Proofs/) and
[tactics](https://lean-lang.org/theorem_proving_in_lean4/Tactics/).
This supports the concise reading guide; it does not turn the appendix into a
general Lean tutorial. The declaration links target the cited immutable archive.

## Verification and limits

The complete revised TeX was read continuously. Removing its thirteen recorded
additions and restoring suffixes recovers v15 byte for byte. All seven statement
bodies and twelve numbered displays are unchanged. The eleven prior diagrams
and 31 prior labels are retained; two diagrams and three labels are added.
Both bibliographies, all prior releases and the authorized disclosure remain.

Final manuscript and extracted-archive builds returned zero, give matching
23-page layout text and have no final reference, citation, box or duplicate
destination warnings. All pages were visually inspected on six contact sheets;
pages 6, 16, 17 and 19–22 were also viewed individually. All 49 source URLs
were checked against the recorded declaration lines and PDF link annotations.
No layout defect remained at delivery.

This is an editorial and correspondence review, with focused mathematical
checking of the additions. It is not independent peer review, a new literature
search, a rerun of Lean/kernel/Palomar verification or an independent reproof of
all coherence reductions. The arXiv server preview has not been inspected because
no upload has occurred. Exact records and delivery hashes are retained in the
v16 provenance; report copies are delivered from committed bytes to Downloads.
