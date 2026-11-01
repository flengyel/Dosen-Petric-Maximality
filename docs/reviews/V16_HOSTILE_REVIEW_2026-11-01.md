# (A) Kill-shots / hard blockers

1 November 2026. Author-side AI-assisted audit using HostileRefereeGPT — Cat/Rec.
Subject: manuscript v16, 23 pages, compared with v15 at
216bca6e7765eae7a494b712facde55f8311e7cf and the registered source declarations.
Genre: mathematical preprint and explanation of formal proofs. Axes:
correctness, self-containedness and exposition. This is not independent peer review.

No fatal or major mathematical defect was established in the added content.
This statement concerns the inspected argument and source correspondence; it
does not certify every proof body or a journal's novelty threshold.

# (B) Major weaknesses

No unresolved major finding. The most consequential dependency issue examined
is at p.19, Appendix D.5, “These derivations do not use faithfulness,” and
pp.21–22, E.3, the split comparison equations. The union and split equations
are inputs to positive coherence; deriving them from the already proved
faithfulness or the quotient negation functor would be circular as an account
of the formal proof. Evidence: derivation and source dependencies in
ReducedUnion, GentzenDistributiveEpi/Mono and ReducedDualFunctor.
The final text derives union laws from source equations and supplies explicit
s and t terms with projection/injection equations. It does not make the
circular inference. Failure mode tested: unproved; severity if present: major;
repairability: direct structural constructions, supplied in E.2–E.3.

The explanation of Gentzenization, cut elimination and atomization on p.19
is a summary with source references. It does not reproduce every reduction.
The paper attributes the coherence theorem to the published source, retains
the two rank errata, and does not claim that Appendix D.5 replaces the complete
cut-elimination proof. Treating it as such a replacement would exceed the
printed argument and this review's scope.

# (C) Minor issues

No unresolved minor correction was identified. The seven accepted exposition
omissions are resolved at the following anchors. Evidence labels describe the
checks performed; the table does not classify true statements as defects.

| Anchor and claim as written | Typed derivation or source check | Status |
| --- | --- | --- |
| pp.5–6, Section 3: the “complete substituted relation” | R_(f,sigma):D_(A,sigma)→D_(C,sigma) compares (label,inner position) in the common E_sigma. Composition retains one intermediate old occurrence and the identical inner occurrence. Repeated tags remain distinct; empty fibres contribute nothing. Evidence: derivation, occurrence_substitute_expanded and Fiber.lift_composition. | R1 resolved; no ill_typed equality between different fibres. |
| pp.20–21, E.1–E.2: q-bar and e-bar are inverses | The q path has source A and target (A∧bottom)∨top. The e path uses the displayed sourceConj composite, then a copairing with zero witnessed by Delta_A∘pi_1. Their relation graphs are inverse to Gq_A and Ge_A, including empty occurrence sets. Evidence: derivation and four ShortProof inverse equations. | R2 resolved; the particular arrows, not only their object types, are identified. |
| p.10, Section 6: union and least element | f∪g=h_C∘(f∧g)∘Delta_A:A→C has the union relation. Faithfulness gives its algebra and composition laws. The least element and empty union are asserted on inhabited hom-sets. Evidence: structural_argument and ReducedUnion/FiniteUnion. | R3 resolved; transfer to B(P) is distinguished from a separately named native declaration. |
| p.6, Section 3: substitution action equations | sigma:P→Form(Q), tau:Q→Form(R); (tau star sigma)(p)=sigma(p)[tau]. Arrow equalities use the displayed object equalities at both endpoints. Evidence: derivation and FormulaSubstitutionLaws/PresentationSubstitutionActionQuotient. | R4 resolved; no untyped equality of differently indexed homs. |
| p.7, Section 4: K passes to retracts | i:A→B,r:B→A,ri=1_A. Precompose K_B by i∧1_bottom and postcompose by r∨1_top. The left composite is j_A pi_1 and the right is zero by absorption. Evidence: derivation and context_retract. | R5 resolved; a single retraction equation suffices. |
| pp.4–5, Section 3: signs and converse | Every edge preserves variable and negation parity. Negation reverses endpoints and relations; normalization transports the equation at the original positions. Evidence: structural_argument and occurrence_signedLabel/dual_relation/occurrence_negate. | R6 resolved; both signs and arbitrary formulas are covered. |
| pp.18–20, D.5: coherence construction | Split comparisons give r_A i_A=1_A; pure positive arrows are finite unions of projection/injection paths. Expansion and recovery prove positive coherence. The common atomic factorization uses shared A',B',u,v and direct-image relation equations for both terms. Evidence: derivation and named expansion/positive/common-factor/coherence declarations. | R7 resolved; no two-sided distributivity inverse is asserted. |

The new reader's guide at pp.16–17, D.2, prints a theorem statement rather
than a proof body with a hole. Its binders, conclusion, Not notation and
R.Total expansion agree with the registered type. The four-row proof table
is checked against Palomar.short_maximality, not inferred from theorem names.
The code names in the mathematical prose have defined mathematical meanings.

# (D) Cross-section consistency failures

No unresolved failure was established. In particular:

- Section 6 proves union laws using faithfulness; D.5 supplies the independent
  source-equation derivations required earlier in the coherence proof.
- D.5's comparisons have the displayed variance: c-wedge∘s=id and
  t∘c-vee=id. The normal expansions are retracts. E.3 uses structural terms
  in the reduced presentation before coherence, whereas E.1–E.2 may use
  Boolean Coherence to prove the inverse equations in B(P).
- D.2 distinguishes a term, a quotient arrow and a proof of Derives. Its
  short-proof table follows inequality→literal K→all K→collapse and explains
  the actual interpretation and substitution arguments.
- Three selected types require nonempty P; identity_ne_zero takes p:P;
  no_top_to_bot allows empty P. Totality does not manufacture arrows.
  The two-object category with one nonidentity arrow A→B tests the difference
  between a thin hom and an inhabited hom; no added construction infers B→A.
- Both maximality proofs, the model corollary, Appendices A–C and all seven
  numbered statement bodies are preserved. No fixed interpretation kernel
  is asserted to be uniformly substitution closed.

All 49 new distinct declaration URLs resolve to the recorded file and line
in source 2e771844077fd8cebfbe365230f13d4dd13a75b1 and occur as PDF links.
The exact supplied bibliography cites that version. The independently
registered version-2 tree is also preserved. Source references are not
additional Palomar theorem selections or a new registration.

# (E) Acceptance conditions, non-negotiable

These are conditions for this requested exposition release, not a journal decision.

1. Print all seven accepted additions with the correct endpoint and existence
   conditions. Endpoint: the R1–R7 anchors above and the active claim map.
   Completed. Failure would block the requested release.
2. Explain the proof-assistant notation and one actual proof route for a
   mathematician new to Lean. Endpoint: D.2's annotated statement and proof
   table. Completed. An identifier list alone would not satisfy the request.
3. Separate source-equation proofs from coherence consequences and retracts
   from isomorphisms. Endpoint: D.5 and E.3. Completed. A circular deduction
   would require repair before release.
4. Preserve prior releases, the selected types and frozen source inputs.
   Endpoint: 97 previous release files and 857 registered proof/input blob
   identities. Verified. Failure would block delivery.
5. Deliver a compiling manuscript and matching four-member archive, update
   active documentation and deliver committed reports. Endpoint: release
   validation and delivery receipt. Build and preservation checks completed;
   delivery and remote synchronization are recorded separately. Failure would
   block a claim of completed delivery.

# (F) Not checked / uncertainty log

The complete v16 TeX was read continuously. The added mathematical passages,
their types, proof order and named source statements were examined. All 23
rendered pages were viewed on contact sheets; pages 6, 16, 17, 19–22 were
also viewed individually. Manuscript/archive builds and layout-text equality
passed. Earlier source text is preserved by an inverse text comparison.

This review does not rerun Lean, kernel verification, Comparator or Palomar
checks. It does not independently inspect all 850 production module bodies,
reprove all cut-elimination branches or repeat the prior literature search.
The governing prose source, relevant book passages and official Lean manual
were consulted; no new novelty claim is introduced. Long-term link availability
and the arXiv server preview remain outside local validation.

Strongest confirmed blocker: none established in the inspected scope.
Strongest suspected unconfirmed blocker: none identified with evidence; full
independent proof-body review remains unavailable here. Most important unchecked
item: independent reconstruction of every cut-elimination reduction underlying
the coherence summary. The limited recommendation does not rely on treating
unavailable material as checked; a journal acceptance judgment would require
additional assessment. Final recommendation: unknown.
