# (A) Kill-shots / hard blockers

No confirmed mathematical blocker was found in the revised argument.

Reviewed: Florian Lengyel, *Maximality of the Došen–Petrić Boolean Category*, v6, dated 25 October 2026. The full source was read, including its changes from v5; the focused recheck concerns §3's Joyal comparison, §5's structural-isomorphism and quotient arguments, Theorem 2.1, Corollary 5.3, and the associated attribution. The source snapshot at completion has SHA-256 `2c30fd10cb81f5d8246dabdc7f343d6d9adeac91358d84273d2799ab514972b0`. Page anchors refer to the compiled v6 PDF supplied during this review.

The following attempted objections were resolved by explicit derivations rather than by interpreting an unstated intention.

| Anchor and claim | Objection tested | Evidence and result |
|---|---|---|
| p.4, §3: “The category B is not cartesian closed” | Perhaps the Joyal comparison merely omits a hypothesis that actually holds. | **Structural argument.** Faithfulness gives at most one arrow ⊤→E, whereas 1_p and 0_p have distinct relations. An exponential p⇒p would identify Hom(p,p) with Hom(⊤,p⇒p), which is impossible. The contradiction uses P nonempty, already fixed in §2. |
| p.6, Lemma 5.1: “q_A … e_A … are isomorphisms” | A faithful functor need not reflect isomorphisms; bijective occurrence graphs alone might be insufficient. | **Derivation and citation.** The proof first obtains an existing isomorphism from the published p.294 list. For q_p there is only one singleton bijection. For e_p the actual product swap aligns either possible two-element bijection. Faithfulness then identifies the specified arrow with an existing isomorphism. Fullness and general reflection of isomorphisms are not used. |
| p.6, Lemma 5.1, last paragraph: “For arbitrary A, substitute A for p” | The result may cover only one positive variable. | **Derivation.** F_σ is defined before use and preserves the arrow operations and inverse equations. It therefore sends the two established isomorphisms to q_A and e_A, including when A contains negation, constants, or p itself. Uniform substitution is simultaneous, so occurrence of p in A causes no recursion problem. |
| pp.6–7, Lemma 5.2: “q_A ≡ … = s∘!_S” | The empty ⊤ branch might have been dropped, or an unavailable zero arrow assumed. | **Derivation.** Both components are existing arrows; the first is zero because K_A holds, and equals s∘!_(A∧⊥) by original-category coherence. The second is s itself. Coproduct uniqueness gives [s∘!,s]=s∘!_S. The hom-set is inhabited by the displayed first component. |
| p.7, Lemma 5.2: “this makes E terminal in the quotient” | Coherence or cancellation may have been used illegitimately after quotienting. | **Derivation.** Original inverse equations for q_A pass through the congruence. Composing q_A≡s∘!_S with its inverse yields 1_E≡s∘!_E; terminality gives !_E∘s=1_⊤. Thus E≅⊤ in the quotient. No quotient faithfulness is asserted. |
| p.7, Lemma 5.2: “Hence π₁ is invertible” and subsequent projection equality | Invertibility of a projection might not force the other projection to agree. | **Derivation.** Since E is terminal, r:A∧E→A is invertible with the specified pairing as inverse. The composite r e_A=π₁ is invertible. Its right inverse Δ_A must be its inverse, and π₂=π₂Δ_Aπ₁=π₁. |
| p.7, Corollary 5.3: “C is a preorder” | Arbitrary model arrows need not be interpretations of syntactic arrows. | **Derivation.** The intersection of interpretation kernels is substitution-stable. Theorem 2.1 supplies equality of the two syntactic projections under every interpretation. Sending p to an arbitrary model object X makes its actual projections equal; pairing then equates arbitrary actual model arrows. No surjectivity of an interpretation is required. |

# (B) Major weaknesses

No major defect was confirmed in the specified mathematical scope.

The central proof depends on the published Boolean Coherence theorem and the published structural isomorphisms. These dependencies are stated and attributed. The revised manuscript proves the application to congruence quotients rather than attributing that application to the earlier sources.

The relevant source checks were made against the September 2007 *Proof-Theoretical Coherence*, printed pp.234, 294, 321–322, 324–326, and the author version of *Isomorphic Formulae in Classical Propositional Logic*, §4, especially Lemma 7's proof and Proposition 3, p.13. The latter proof realizes prescribed same-letter occurrence bijections and their inverses, so its use as an alternative source for the specific isomorphisms is justified.

No finding of `unsupported_novelty` is warranted from the shortness of the new proof. A theorem can be new even when it is a short consequence of older structural results. The manuscript makes the precise historical claim that it disproves the conjecture in the specified 2007 version; the quoted source does conjecture nonmaximality. Neither the new text nor this review establishes that no earlier source anywhere stated the maximality conclusion.

# (C) Minor issues

No required local mathematical correction was identified in the revised sections.

The Joyal paragraph uses established category-theoretic terminology at the intended research level and supplies a concrete obstruction to cartesian closure. The proof of Lemma 5.1 states the actual arrow types, identifies the use of the one-variable source theorem, and then handles general formulas by a previously defined substitution functor. Additional defensive warnings about fullness or quotient coherence are unnecessary in the manuscript because the actual inference is already explicit.

# (D) Cross-section consistency failures

No failure was found in the following dependencies.

| Dependency | Checked consistency |
|---|---|
| §2 congruences → Proposition 4.2 → Lemma 5.2 | Proposition 4.2 requires substitution closure and produces K_A for every A. Lemma 5.2 requires only proof-operation closure once all those contextual equations are supplied. The main theorem invokes them in the correct order. |
| Original equations → quotient equations | Equalities obtained from Boolean Coherence are equations in B. The notation ≡ marks the new quotient equalities. Existing inverse equations survive the quotient; no new interpretation is assumed faithful. |
| Nonempty P → p in Lemma 5.1, Joyal comparison, model corollary | The standing assumption supplies the variable needed in all three places. No finite cardinality of P is used. |
| Known isomorphism types → specified q_A and e_A | The proof does not equate unspecified arrows by type alone. It computes their singleton/two-element occurrence bijections, adjusts the latter with product symmetry, and invokes faithfulness. |
| Abstract and introduction → §5 | The abstract credits Došen–Petrić's structural isomorphisms; §5 proves their application to contextual collapse. The conclusion is not attributed to the earlier papers. |
| §5 paper proof → §6 description of a different formal proof | The paper uses q_A and e_A; §6 explicitly describes the formalization's mix/codiagonal argument. These are different proofs of the same collapse implication, not inconsistent definitions of one map. |
| §6 mix expression → cited (dm) | The types are A∧C→A∨C. Folding the codomain with [1_A,1_A] at C=A gives exactly the old h_A expression. Parameter independence and symmetry are credited to the established mix identities. |

Small edge cases checked: formulas with no variable occurrences, A=⊤ or A=⊥, a single generator P={p}, and substitutions in which p occurs in its replacement. None invalidates the revised argument. The plain two-object arrow category is not a model of the specified zero-identity Boolean structure, so it cannot serve as a counterexample merely by lacking an arbitrary arrow.

# (E) Acceptance conditions, non-negotiable

For the mathematical claims reviewed here, no repair remains outstanding. The following distinctions must be preserved in the delivered version:

1. **Theorem 2.1 and Proposition 4.2:** retain closure under uniform formula substitution and P≠∅. These hypotheses are used in the proof; dropping them would require a new argument.
2. **Lemma 5.1:** retain the identification of the specific q/e arrows with existing isomorphisms, or replace it with proved explicit inverses. A bare appeal to bijective occurrence graphs would not justify the conclusion.
3. **§6 and the abstract:** retain the explicit conditional scope of the Lean result unless the cited source development proves the missing presentation-level hypotheses. The current manuscript states that faithfulness and the full instantiation remain unproved. This mathematical review does not independently certify the software claims.

These conditions are satisfied by the text inspected; they are not requests for extra manuscript warnings or additional verification cycles.

# (F) Not checked / uncertainty log

The complete source was read, and the revised mathematical arguments were checked against their specified primary inputs. PDF text was used to establish page anchors. This subtask did not perform a visual layout audit, a new compilation, a Lean build, a kernel replay, or a repository-wide dependency audit. Those checks must not be inferred from this report.

The semantic truth of the external Boolean Coherence theorem was used as a published result; its full book-length proof was not reproved here. No exhaustive proof of worldwide novelty is possible from the literature search. No previously published exact maximality theorem was identified in the reviewed material, but the absence of such a finding is not proof of its nonexistence.

Strongest confirmed blocker: none in the revised mathematical argument.

Strongest suspected unconfirmed blocker: none with positive evidence. The concrete formalization claims in §6 require the separate source-level audit; their detailed implementation was outside this subtask.

Most important thing not checked here: whether every implementation assertion in §6 matches the pinned Lean source and its transitive assumptions.

Dependence on unavailable material: the mathematical assessment uses available primary book and paper texts. Global priority and complete software verification are outside its conclusion.

Final recommendation: **unknown** as an unrestricted publication decision; no confirmed mathematical blocker was found in the reviewed v6 proof. The revised attribution supports a conjecture-resolution claim, not a claim that the work is subsumed by a previously published maximality theorem.
