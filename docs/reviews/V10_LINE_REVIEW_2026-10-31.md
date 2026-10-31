# Line review of v10 and v11; revision v12

Reviewed source: `manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v10.tex`
at `89ebf8390f8906a6c2529cea6f910c65ece8889f` (1003 physical lines).
The review reads the complete source, including displays, diagram arrows,
appendices, disclosure and bibliography. Original line numbers below refer to
that immutable source. The author requested implementation of corrections and
direct mathematical exposition modelled on Došen and Petrić.

## Outline recorded before revision

| Original lines | Function and contents |
| --- | --- |
| 1–45 | Preamble, metadata, abstract, MSC and keywords. |
| 46–105 | Introduction: conjecture, two proof steps, prior maximality results, other Boolean-category axioms, occurrence notation and roadmap. |
| 107–209 | Category, typed generators, zero identity/law, witnessed zero arrows, congruences, maximality theorem. |
| 211–351 | Tagged occurrences, relational interpretation and coherence, nonthinness and exponential obstruction, normal forms, signed labels, substitution bijection/square/functor. |
| 353–458 | Context K_A, isolation lemma and its recursive selectors, substitution for positive and negative literals. |
| 460–581 | The particular isomorphisms q_A and e_A, quotient collapse, main theorem and model corollary. |
| 583–632 | Lean syntax, general maximality inputs, alternative symmetric-fold argument, instantiated results and registered declarations. |
| 634–834 | Appendix A: profiles and fibres, tagged substitution, ordinal coordinates and example, shared variables and the context substitution. |
| 836–886 | Appendix B: three typed diagrams for defining equations. |
| 888–910 | Appendix C: two source rank errata and their mathematical explanations. |
| 912–917 | Author-authorized AI disclosure. |
| 919–1003 | Bibliography and source versions. |

The proof order is sound: definitions precede the main theorem; coherence and
substitution precede isolation; isolation precedes the contextual-collapse
argument. The occurrence appendices supply required coordinate details. They
are not removed to shorten the paper. The literature discussion is part of
the introduction, not a separate section.

## Governing writing source

Knuth, Larrabee and Roberts, *Mathematical Writing*, Stanford CS-TR-89-1193:
https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf.
The review applies §1 (especially economy and unnecessary jargon), §§4–5
(organization, definitions, notation and precision). The author also requests
Došen–Petrić's manner of exposition: definitions, equations, cited hypotheses
and deductions. No phrase is retained merely to announce that a construction
has been made. A technical term is assessed by its mathematical use; structural
induction, for example, names a proof method.

The line-coverage, source-comparison and validation records follow below.

## Complete original-line coverage

Each range was read, including the mathematical displays and blank separators.
The ranges are consecutive and cover all 1003 original physical lines. This is
an editorial/mathematical reading record, not a claim that every line needed an
edit. The exact release diff against v11 is retained in
`provenance/manuscript-v12-review-20261031/v11-to-v12.diff`.

| V10 lines | Passage | Decision and check |
| --- | --- | --- |
| 1–21 | Metadata and preamble | Version advanced to v12; equation destination names made unique. |
| 22–36 | Abstract | State nonempty P and closure conditions; remove the repeated coordinates slogan. |
| 37–45 | Classification and keywords | Retained; no mathematical claim or promotional language. |
| 46–55 | Conjecture and result | Name the zero-identity category and the closure conditions; exhibit nonthinness. |
| 56–65 | Proof outline | Choose an edge in one relation and not the other; identify the cited isomorphisms. |
| 66–72 | Cartesian comparison | Retain the exact shared reduction to equal projections, checked against §5. |
| 73–80 | Other maximality results | State Lemma 6's hypotheses and construction; check §16's differing-pair proof. |
| 81–93 | Other Boolean-category definitions | Qualify the freeness result; identify the negation composite and its equation. |
| 94–106 | Occurrence notation and roadmap | Retain the required notation attribution and appendix pointers; shorten the formalization pointer. |
| 107–117 | Generated category | Form(P), the objects, generated equality and notation are introduced in order. |
| 118–133 | Products, coproducts and composition | Add explicit pairing/copairing types. Existing notation was well typed; no Lean repair. |
| 134–146 | Distributor | Type and first-injection law match DP p.234; retained. |
| 147–159 | Negation and zero definition | Contravariance and every leg of the five-arrow endomorphism checked; retained. |
| 160–171 | Zero law and source locators | Both sides have type A→C; p.317/p.322 locators checked; retained. |
| 172–176 | Diagram pointer | Retained: it directs the reader to the required fully typed diagrams. |
| 177–184 | Witnessed zeros | Independence and both absorption laws checked; nonempty-hom proviso retained. |
| 185–194 | Congruences and substitution | Homwise equivalences, operation closure and substitution of endpoints are explicit; retained. |
| 195–210 | Maximality statement | Statement retained; delete the redundant theorem announcement; retain v11's proof pointer. |
| 211–231 | Occurrence recursion and labels | Negation and empty constants checked; repeated labels do not identify positions. |
| 232–239 | Ordinal coordinates | Replace the vague change-of-coordinates roadmap by the numbering map. |
| 240–262 | Relational interpretation | Projection/injection tags, pair/copair unions and rebracketing type checked. |
| 263–272 | Coherence and nonthinness | Faithfulness is applied to parallel arrows; the two projections have distinct graphs. |
| 273–279 | Exponential obstruction | The global-point hom-set has at most one member; 1_p and 0_p are distinct. Retained. |
| 280–287 | Normal forms | State the graph as a bijection Occ(A)→Occ(A°). |
| 288–298 | Signed-literal invariant | Separate object formation from arrow generators; check empty eta/epsilon relations. |
| 299–319 | Substitution blocks | Keep the induction and separate repeated tags; retain v11's explicit 'occurrence of A'. |
| 320–341 | Block square | Remove the 'organization' announcement; state the equal-image condition on coordinates. |
| 342–352 | Substitution functor | Identity/composition/operation preservation retained; clarify that B(Q) also exists for empty Q. |
| 353–367 | Context K_A | Both arrows and the alternative zero path have the stated endpoints; retained. |
| 368–382 | Isolation statement | Signed literal, interchange permission and both equations retained verbatim. |
| 383–391 | Normalization transport | Composition order with a_A inverse/a_C checked; retain v11's simpler naming. |
| 392–403 | Edge and empty-relation arrows | The two endpoints have the same signed literal; b_V and t_V are typed and empty. |
| 404–412 | Selector recursion | Product branch pairs with a zero-relation filler; coproduct branch injects. Types checked. |
| 413–419 | Coselector recursion | Projection and copairing branches are the correctly typed duals. |
| 420–425 | Isolation conclusion | Relational composition leaves one edge or none; source faithfulness gives both equalities. |
| 426–431 | All-contexts statement | Substitution-congruence hypothesis and quantifier over A retained. |
| 432–441 | Positive literal substitution | Preservation of operations and zero construction checked; shorten the cross-reference. |
| 442–459 | Negative literal substitution | Substitute neg A; both conjugating arrows in the double-negation square have the right direction. |
| 460–478 | q/e lemma | Remove the vague 'remove constants' introduction; both typed arrows and claim retained. |
| 479–486 | q at a variable | Existence plus the unique one-point bijection identifies the particular arrow. |
| 487–496 | e at a variable | Both possible two-point bijections are accounted for by source symmetry. |
| 497–501 | Substitution of the isomorphisms | A functor preserves the inverse equations; no illicit reflection of isomorphisms. |
| 502–507 | Collapse hypothesis | Proof congruence and all contextual equations retained. |
| 508–520 | Quotient products and terminal factorization | Pairing/copairing equations descend; the zero comparison is made in B, not in its quotient. |
| 521–528 | Terminal E | q inverse and terminal uniqueness give 1_E equivalent to s!_E; checked. |
| 529–542 | Equal projections | The projection inverse and diagonal calculation are typed; cancellation uses established invertibility. |
| 543–548 | Thinness | Pairing arbitrary parallel arrows proves equality; no hom-set inhabitation assumed. |
| 549–555 | Main theorem proof | The two preceding results have precisely the required congruence hypotheses. |
| 556–562 | Interpretation definition | List the preserved operations instead of saying 'structure-preserving'. |
| 563–570 | Model corollary statement | All interpretations and nonempty P retained verbatim. |
| 571–582 | Model corollary proof | Universal agreement is substitution-closed; an arbitrary target object is obtained by valuation. |
| 583–592 | Lean syntax and quotient | State generated equality and descent to the quotient; checked against typed Term and endpoint files. |
| 593–612 | General theorem and fold | Retain explicit hypotheses from v11; identify the fold as the proof route used and separate parameter independence. |
| 613–620 | Instantiation | Keep the distinction between proved presentation inputs and the relative theorem. |
| 621–629 | Short proof and other claims | q/e inverses, model interpretation and appendix correspondence claims checked against endpoints/map. |
| 630–633 | Registration scope | Five names match the registered comparator; retain the exact supplied citation key. |
| 634–644 | Appendix A purpose | Describe substitution and the occurrence-indexing pair directly. |
| 645–657 | Patterns and profiles | Finite ordinals and placeholder indices are defined before use. |
| 658–664 | Local patterns and zero cases | Replace the circular displayed-map qualification by the empty-placeholder boundary case. |
| 665–680 | D, C and injections | Distinguish occurrence coordinates from occurrences; injection domains checked. |
| 681–697 | Unique gamma | The disjoint-union representation proves existence and uniqueness; retain the square and formula. |
| 698–712 | Profile square | Write the composite equation; state precisely why repeated profiles have disjoint tagged copies. |
| 713–729 | Substitution and labels | Renaming q_i,s to (i,s), the bijection chi and its commuting square are typed. |
| 730–747 | Ordinal encoders | Prefix sums and one-based offsets checked, including zero-sized blocks. |
| 748–766 | Delta square and formula | Replace 'keeps ... visible' by theta_C gamma theta_D inverse; preserve the numbered formula. |
| 767–778 | Book notation and skeleton | Check the locator formula against DP p.46; retain v11's definition and spell out reconstruction. |
| 779–799 | Worked example | Recompute all eight outputs and the (1,2)↦(2,1)↦3 example; retained. |
| 800–823 | Shared variables | Noninjective renaming preserves occurrence positions; retain v11's specified induction object. |
| 824–835 | Context specialization | Name both endpoint patterns and both substituted arrows; preserve the negative branch. |
| 836–854 | First-injection diagram | All three arrow types and the equality of paths checked; retained verbatim. |
| 855–875 | Zero-identity diagram | Five-arrow composite and terminal/initial unit maps checked; retained verbatim. |
| 876–887 | Zero-law diagram | Top/right path is f after zero; left/bottom is zero after g. Arbitrary parallel f,g retained. |
| 888–896 | Source-rank conventions | Positive one-sided ranks and their sum checked against DP p.249. |
| 897–903 | Page 260 erratum | Rendered inequality is reversed; descending right-premise ranks and unchanged opposite rank justify correction. |
| 904–911 | Page 262 erratum | Rendered sentence omits 'right'; fresh right rank is one, total rank is at least two. |
| 912–918 | Disclosure | Author-authorized wording retained verbatim. |
| 919–1003 | Bibliography | Primary claims checked; v11 BibTeX conversion and exact Palomar entry retained, with two author-copy links added. |

## Concurrent v11 release

Main advanced to `97d728820d87f712c32c77dcb29fcd6fa0856e3d` during this
review. Its v11 source was read through the complete diff from v10. The BibTeX
conversion, exact author-supplied Palomar record, explicit induction object,
removal of 'canonical', simpler names for the isolating arrows, and explicit
signed-literal hypotheses are retained. Overlapping prose changes were
reconciled paragraph by paragraph. No published v11 file is replaced; this
review's release is v12. The unpublished local v11 draft was superseded.

## Definition and typing audit

Definitions precede use in the body: formulas/category; projections/injections;
pairing/copairing; units/composition; distributor; negation/zero; congruence;
occurrences/labels; Rel and G; signed literals/normal forms; substitution blocks
and F_sigma; contextual K; q/e; interpretations; profile coordinates and maps.
The introduction previews results whose notation is defined in the body.
The original pairing/copairing types were implicit in standard notation. Their
explicit display is a readability repair, not an ill-typed term or missing Lean
declaration. `DosenPetric/PresentationSyntax.lean` defines `Term` with two formula
indices and gives the expected types of `Term.pair` and `Term.copair`.
The body also now explicitly permits empty Q in B(Q), without weakening the
nonempty-P hypothesis of the main theorem/model corollary.

V11 had already defined skeleton before use. V12 retains that definition,
explains that constants/connectives are fixed, and states how the profile
reconstructs the placeholder at each position. 'Structural induction on the
formula' remains because it specifies a proof method. Internal TeX labels with
'structural' are not manuscript prose and remain to preserve cross-references.

## Representative replacements

| Earlier wording | Revised mathematical statement |
| --- | --- |
| “a relation distinguishing two arrows” | Choose an edge in one occurrence relation and not the other. |
| “Related occurrence-selection constructions” | State the two selected same-variable occurrences and the tautological-implication hypothesis of Lemma 6. |
| “equates an endomorphism with the identity” | Identify the composite in the displayed zero-identity formula and state that the other axioms make it 1_A. |
| “The organization of these blocks is expressed ...” | Delete the announcement and define E_sigma and its maps. |
| “fits over the outer profile” | p_C composed with gamma equals o_M composed with p_D. |
| “keeps the block and local position visible” | delta = theta_C composed with gamma composed with theta_D inverse. |
| “structure-preserving functor” | Name the products, coproducts, units, distributor, negation maps, eta and epsilon. |
| “remove the constants” | Identify the two isomorphisms of the cited types. |

The review does not equate terseness with rigor. The selector/coselector
recursions, zero witnesses, normal-form transport, both collapse routes,
substitution proof, typed diagrams, worked example and source-erratum arguments
remain. No editorial audit narration was added to the manuscript.

## Primary-source comparisons

| Work | Checked claim and locator | Result |
| --- | --- | --- |
| Došen–Petrić, *Proof-Theoretical Coherence*, revised September 2007 | §14.2 p.322 conjecture; §9.7 pp.215–216 context; §12.5 p.294 isomorphism types; pp.317–322 presentation/coherence; §2.5 p.46 ordinal formula; p.234 generator equations | Claims and displayed types agree. |
| *The maximality of cartesian categories* | §5, substitution and composition leading to equal projections | Comparison retained in shorter form. |
| *Bicartesian coherence revisited*, v3 | §§8–10, lattice maximality and dicartesian relative maximality | Scope retained; no claim of distribution is inserted. |
| *Isomorphic formulae in classical propositional logic*, v3 | Lemmas 6 and 7 | Specify the occurrence selection hypothesis; the isomorphism comparison is supported. |
| *Syntax for split preorders*, v7 | §16, maximality for PF, EF, RB under the stated congruence rules | Differing-pair comparison supported. |
| Lamarche–Straßburger, proceedings version | Theorem 3.5.4, graphical and Delta–Nabla-strong K-flat/K-sharp categories | Specify the theorem's class. The expanded version includes a separately named loop-killing condition; the revision cites the proceedings version. |
| Straßburger, TAC 18 | Axiomatizations based on star-autonomous categories; §5 monoid/comonoid equations | Narrow description supported. |
| Führmann–Pym, author version | Negation triangle (11), author p.8; Theorems 6.4–6.5 | The triangle gives the identity after the inverse right unit. Use equation (11), avoiding an unverified transfer of page numbers between editions. |
| Lengyel, *The Unbearable Notation of Logic*, v8 | §9.2–9.3, profiles, tagged blocks, ordinal transport and skeleton reconstruction | Appendix A's attribution and formulas agree. |
| Registered source | comparator.json at 2e771844077fd8cebfbe365230f13d4dd13a75b1 | Exactly the five declarations described in §6. |

The source-file hashes are recorded separately. Existing bibliographic facts
were preserved; the two author-copy links identify the versions used in the
comparisons. No exhaustive novelty search is claimed.

## Validation and remaining limits

See `docs/MANUSCRIPT_V12_REPORT.md` and the companion hostile review. The
release preserves all seven theorem statements, twelve numbered displays,
ten TikZ diagrams, thirty labels, Appendices B/C and the authorized disclosure
verbatim from v11. Source review, PDF compilation/rendering and package checks
are distinct from the preserved Lean verification. Windows Downloads delivery
of these new reports remains unavailable in this environment.

