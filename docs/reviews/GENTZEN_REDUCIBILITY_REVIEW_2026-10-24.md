## (A) Kill-shots / hard blockers

The development has made useful local progress, but it has not established the connection needed to reconstruct the source Reducibility Lemma. The drift is in the choice and acceptance of intermediate endpoints: positional classification and local rank calculations have proceeded without a proved passage to source-compatible reduction at a tied occurrence. This does not establish that the classifier is false, that the existing local equations are wrong, or that the formalization must be discarded.

This is an AI-assisted author-side review of the supplied evidence and selected committed sources at 9075ecc. It is not a fresh Lean build or independent kernel certification. Confidence: high concerning the demonstrated gaps; unknown concerning whether the present representation supports the entire intended proof without changes.

### A1. The classification theorem has no reduction conclusion

**Anchors:** [GentzenSelectionDispatch.lean, lines 92–100](https://github.com/flengyel/Dosen-Petric-Maximality/blob/9075ecc/DosenPetric/GentzenSelectionDispatch.lean#L92); GENTZEN_BLOCKED_CLASSIFICATION_REPORT.md, “Exact checkpoint and scope” and “Finite case ledger.”

For a contraction block d, its arity bound, and a cut-free premise g, classificationL proves:

~~~lean
¬ g.ruleKind.Basis ∧ g.ruleKind ≠ .cut ∧
  ∃ r : SelectionRegime,
    r.Holds (g.selectionPorts .left d.selected)
~~~

The right theorem has the corresponding right-side statement. Neither type mentions BlockedL/R, ReducibleL/R, a replacement proof, categorical equality, or a strict rank inequality. The proof combines exclusion of basis and cut heads with coverage of the selected-position profiles.

The per-position predecessor evidence is substantive; this is not merely an enumeration of names. Nevertheless, a witness to one of seven membership conditions is not a witness to a source reduction.

**Failure mode:** unsupported_generalization if this theorem is presented as certified reduction dispatch. **Evidence:** derivation from the actual theorem type. **Severity:** major for the reconstruction program; no demonstrated defect in the scoped classification theorem. **Repairability:** supply the missing construction and its correspondence proof. No inference to Reducibility is presently licensed.

### A2. Primitive disjunction and the blocked disjunction macros are demonstrably different

**Anchors:** [GentzenBlockedSource.lean, disjLLast](https://github.com/flengyel/Dosen-Petric-Maximality/blob/9075ecc/DosenPetric/GentzenBlockedSource.lean#L18); [GentzenBlockedPatterns.lean, BlockedL](https://github.com/flengyel/Dosen-Petric-Maximality/blob/9075ecc/DosenPetric/GentzenBlockedPatterns.lean); [GentzenReducibleOccurrences.lean, lines 23–27](https://github.com/flengyel/Dosen-Petric-Maximality/blob/9075ecc/DosenPetric/GentzenReducibleOccurrences.lean#L23).

The committed theorem BlockedL.premise_kind implies that the immediate premise of a blocked left contraction has one of these heads:

~~~text
mix, conjR, exchangeL, conjL
~~~

In particular, disjL is absent. This is explained by the implementation: disjLLast inserts exchanges in both premises and another exchange above the primitive disjL. The disjunction constructors of BlockedL recognize this macro.

A concrete separation is already derivable from the committed sources, independently of the unavailable local BoundaryChecks.lean. Put P = Empty and C = top ∨ bot. The committed proof freshBoth has type

~~~text
G Empty [C,C,C] [top,top]
~~~

and is a primitive disjL. Its three selected positions have the proved profile [fresh, first, second], hence regime selectedBoth. Form

~~~text
w = G.contractL C [[],[],[]] [] [top,top]
      (Nat.le_succ 2) freshBoth.
~~~

Then w has type G Empty [C] [top,top]. If BlockedL w held, premise_kind would imply that some disjL belongs to the displayed list, which is impossible. Thus this example has selectedBoth and an unblocked outer contraction.

This is a source-level derivation using committed definitions and theorems; it was not newly compiled in this review. It confirms the substance of the reported boundary observation without claiming access to the local check.

It refutes the implication “selectedBoth implies BlockedL” for this example. No such implication occurs in classificationL. It therefore does not refute the classifier. Nor does it alone establish that the encoding is incorrect: a macro representation can work, provided its required comparison theorems are proved.

**Failure mode:** unproved correspondence, not a confirmed false encoding. **Evidence:** derivation and explicit example. **Severity:** major. **Downstream impact:** the source case analysis cannot simply be applied to the classifier’s primitive heads. **Repairability:** prove the needed passage between the representations, or prove the reduction theorem directly for the present primitive grammar with justified blocked cases.

## (B) Major weaknesses

### B1. The replacement operation is real progress, but its hypothesis is the missing mathematical work

**Anchors:** [GentzenProofReplacement.lean, replace_denote and replace_cutFree](https://github.com/flengyel/Dosen-Petric-Maximality/blob/9075ecc/DosenPetric/GentzenProofReplacement.lean); GENTZEN_PROOF_REPLACEMENT_REPORT.md, “Construction and proof.”

The operation replaces one addressed subproof and preserves the outer sequent. Its denotation theorem assumes equality of the old and replacement denotations. The code derives the outer equality by rule congruence and address induction. The count balances and preservation of cut-freeness are appropriate and do not assume normalization.

The W5 integration supplies the equality from existing local theorems. This directly supports the larger proof and should be retained.

What is absent is a theorem producing a suitable replacement from ReducibleL/R, together with a statement about which contractions are reducible in the rebuilt cut. The replacement API cannot produce that conclusion from denotation equality: reducibility and rho are properties of proof syntax and tracing.

**Failure mode:** unproved integration into Reducibility. **Evidence:** actual theorem hypotheses and conclusions. **Severity:** major for the main target, none established for the replacement API. **Repairability:** use this API in the target theorem specified in §E.

### B2. The example offered for mixed W5 does not witness an unresolved reducible case

**Anchors:** GENTZEN_BLOCKED_CLASSIFICATION_HOSTILE.md, §B.1, lines 23–29; [GentzenBlockedExamples.lean, splitMix_ports and splitMix_regime](https://github.com/flengyel/Dosen-Petric-Maximality/blob/9075ecc/DosenPetric/GentzenBlockedExamples.lean); BlockedL.gammaMix.

The review uses splitMix_ports to support the claim that mixed-premise W5 is a confirmed missing case. For C = lit t, splitMix is mix(identity t, identity t). Its selected profile is [second, first].

However, contracting these two occurrences is exactly a BlockedL.gammaMix instance with all four gaps empty. It is therefore blocked and cannot satisfy ReducibleL. The example demonstrates a mixed profile, not a reducible mixed case requiring transformation.

The general mixed case remains relevant: branch multiplicities above the already-blocked base case can require a reduction. The new prompt correctly distinguishes n = m = 1 from larger selections. The defect is in the earlier inference from the example and in describing an entire regime as a missing reducer case without separating already-blocked inputs.

**Failure mode:** unsupported_generalization in the evidence offered for task selection. **Evidence:** explicit gammaMix instantiation. **Severity:** major for the justification of the continuation, repairable. **Repair:** exhibit an actual tied unblocked mixed contraction satisfying ReducibleL/R, then prove the required conclusion for that case from those hypotheses.

### B3. Administrative exchanges have measurable rank costs

**Anchors:** [GentzenClusterRank.lean, rho_eq](https://github.com/flengyel/Dosen-Petric-Maximality/blob/9075ecc/DosenPetric/GentzenClusterRank.lean); [GentzenOppositeExchangeRank.lean](https://github.com/flengyel/Dosen-Petric-Maximality/blob/9075ecc/DosenPetric/GentzenOppositeExchangeRank.lean); GENTZEN_BLOCKED_CLASSIFICATION_REPORT.md, “Source encoding and positions.”

The recurrence for rho counts one node plus the predecessor ranks. The existing opposite-side exchange theorems explicitly give rho(exchange f) = 1 + rho(f) at corresponding positions.

Consequently, equality of denotations, a list endpoint cast, and an inserted exchange must not be treated as interchangeable operations for rank arguments. A source comparison need not preserve rank exactly; it must prove the inequalities actually needed by the chosen induction. The reports correctly leave that comparison open.

**Failure mode:** unproved rank comparison. **Evidence:** committed rank recurrence and exchange equations. **Severity:** major. **Repairability:** account for every inserted node in the required inequality; do not assume rank invariance.

### B4. A decrease at the chosen contraction does not cover every newly reducible descendant

**Anchors:** GENTZEN_PROOF_REPLACEMENT_REPORT.md, “Source correspondence”; GENTZEN_BLOCKED_CLASSIFICATION_REPORT.md, case ledger; [GentzenSelectedLogicalRanks.lean](https://github.com/flengyel/Dosen-Petric-Maximality/blob/9075ecc/DosenPetric/GentzenSelectedLogicalRanks.lean).

The existing W4 rank file distinguishes the inner contraction’s strict decrease from the final retained position’s possible tie and increases at other fixed positions. These are different claims.

The relevant target must quantify over contractions inside the replacement that satisfy ReducibleL/R relative to the rebuilt cut. Checking only the explicitly introduced inner contractions does not discharge that quantifier. Old descendants can become eligible when an unblocked ancestor is removed or becomes blocked.

Conversely, a positional rank increase alone is not a counterexample to the intended result. The position may not be the lower formula of a contraction subject to the required reducibility condition. Nor is decrease of the sum of all positional ranks the stated target.

For the later multiset induction, a further argument must control newly eligible occurrences outside the replacement and changes to the surrounding blocked ancestors. This is a separate obligation from the local replacement conclusion.

**Failure mode:** unproved quantified rank conclusion. **Evidence:** comparison of the current local theorem types with the target in §E. **Severity:** major. **Repairability:** prove occurrence transport and eligibility-sensitive inequalities; do not replace them with an unqualified global sum.

## (C) Minor issues

The main editorial issue is the strength of status language, not missing elementary definitions.

### Existing outline

The replacement report proceeds through endpoint and hypotheses; reconstruction; W5 integration; source correspondence; verification. The classification report proceeds through scope; blocked patterns and positional conventions; occurrences; profile coverage; the case ledger; verification. Both outlines are usable. The classification report should place the missing representation comparison immediately after its opening claim and before describing the encoding as source-faithful.

### Writing comparison and concrete repairs

The consulted Knuth–Larrabee–Roberts report, §1 points 5, 11–14, supports explicit hypotheses, introduced variables, motivation and consistent notation. Section 4 qualifies definition placement. The judgments about proof-status claims below are independent mathematical and editorial judgments, not rules attributed to that book.

| Anchor | Difficulty | Recommended wording or action |
| --- | --- | --- |
| Classification dispatch: “source-faithful Blocked/Reducible definitions” | The report supplies encodings but leaves the comparison required for the argument unproved. | “Blocked-pattern encodings and reducibility predicates in the present G syntax; their adequacy for the source reduction remains to be proved.” |
| Classification report: “exhaustive finite classification” | Correct for profiles, potentially misleading for reduction cases. | “Exhaustive classification of selected-position profiles.” |
| Validation: “next missing classifier regime” | Every regime is already classified; the missing result is a reduction theorem for some inputs. | “The next proposed reduction construction concerns mixed selections with more than two selected copies.” |
| Mixed-W5 dispatch, final paragraph: “This closes one identified classifier regime” | Mix is only one head with parametricBoth; conjR/disjL remain. | “This would establish the mix branch of the mixed parametric case, subject to the stated integration and rank conclusions.” |
| Reviews: acceptance conditions marked met | A restricted encoding acceptance can be mistaken for acceptance of source correspondence. | Mark encoding and correspondence separately; the latter remains unproved. |

### Definition-order audit

The reports distinguish proof values from addresses, formula labels from positions, primitive heads from profiles, and denotation equality from relation equality. ProperContains is defined before its use in ReducibleL/R, and the strict-ancestor condition avoids requiring an occurrence to be both blocked and unblocked. No new defect in those definitions was established.

The needed correction is to distinguish “reducible according to the implemented predicate” from “proved to represent source reducibility.” No terminological cleanup can replace that proof.

## (D) Cross-section consistency failures

There is no basis for claiming that the attached reports declared Reducibility complete. They repeatedly state that it is open, and both preceding dispatches expressly forbid such a claim. The later retraction is accurate as a correction to broader reassurance; it is not a discovery that the reports had contained a completed reduction theorem.

The problem is that those qualifications did not govern the acceptance decision. The hostile review identifies the macro and rank comparison as a confirmed blocker, then accepts the narrower checkpoint and recommends another local family. The writing review approves the exposition at the same narrowed scope. Neither establishes that the next local endpoint resolves the main dependency.

The classification prompt itself permits a ledger of remaining obligations. Thus failure to prove all reducers during that checkpoint is not, by itself, a violation of its explicit scope. The unsupported step is treating that checkpoint as sufficient evidence that subsequent case implementation is securely connected to the source argument.

The two later validation attachments contain the preceding validation document unchanged beneath a new current section. I checked these inclusions byte-for-byte. Their cumulative length is therefore not independent corroboration by three validation runs of the latest state. Each current section reports its own checkpoint; historical sections retain older evidence.

The concurrency incidents are disclosed: transient overlapping files, a failed import-closure attempt, and an interrupted isolated rebuild. The reported final checks apply to the compared final candidate. These records justify neither alleging corruption nor claiming an independent clean rebuild. This review did not rerun them.

## (E) Acceptance conditions, non-negotiable

The next objective should be the source-shaped Reducibility theorem for the existing proof grammar, with an explicit justification of the representation used. Replace the mixed-W5-only continuation as the governing endpoint. Retain mixed W5 as a subordinate case if the target proof requires it.

### Precise left target

Fix a variable type P, a formula C, contexts Γ, Δ, Θ, Λ, and proofs

~~~text
f : G P Γ (C :: Δ)
g : G P (C :: Θ) Λ.
~~~

Let w : G P U V, let a : ProofAddress g w, and let x : At U C. Assume ReducibleL f g a x. Write den(q) for ofTerm q.denote.

The required source-shaped statement produces h : G P U V satisfying:

1. h.CutFree;
2. den(h) = den(w);
3. with g' = a.replace h and a' = a.inserted h, for every v : G P I J, b : ProofAddress h v, and y : At I C,
   ReducibleL f g' (a'.append b) y implies
   v.rho .left y < w.rho .left x.

All contexts and positions remain typed. The hypothesis already implies that the selected w is a tied contraction. Reducibility in item 3 is evaluated after replacement. The right target replaces an addressed subproof of f and uses ReducibleR and right-side positions. This is a proposed formal target, not a declaration claimed to have compiled.

This formulation follows the source replacement conclusion; its use with the current BlockedL/R and rho still requires the correspondence work identified above. The source states the left lemma on printed p.250, supplies its case analysis on pp.251–252, and states the right analogue and subsequent multiset argument on pp.252–253.

### Required deliverables

1. **Resolve the primitive/macro distinction.** Give the actual typed comparison used by reduction, including positions, tied occurrences, blocked status where required and the necessary rank inequalities. Cover native disjL and right-retention conventions. Alternatively, prove the theorem for the present primitive representation directly and justify its relation to the intended source theorem. Failure rejects any claim of completed source correspondence.

2. **Make the full target control case work.** Express the target above without a caller-supplied reduct, rank certificate or conclusion-equivalent hypothesis. Develop its proof through the existing rule/profile analysis. An unproved target must remain documented as unproved; introducing a proposition or a record is not a proof. Failure rejects a Reducibility completion claim.

3. **Connect existing results before extending the catalogue.** Use a completed family, such as terminal left W4, to discharge an actual branch of that target at arbitrary addressed occurrences. Establish blocked status of its outer result and bounds for every eligible descendant. For mixed W5, extract branch data from the input and separate the already-blocked singleton/singleton case. Continue toward the full theorem; do not make another isolated equality family the new final objective.

4. **Separate local reduction from multiset termination.** After proving both replacement results, prove the transport and outside-occurrence facts needed for the Blocked-w argument, with the actual finite collection and well-founded order specified. Failure leaves Blocked-w and later normalization claims open; it does not retroactively invalidate correct local equalities.

5. **Use checks appropriate to the changed proofs.** Run the repository’s required build and axiom/boundary checks after substantive proof changes. Record the exact target theorem and assumptions before build statistics. Retain the current local results unless a specific defect is found. Do not change blocked predicates or ranks merely to make tests pass, and do not assume coherence to prove the equality used in its reconstruction.

These are mathematical acceptance conditions for future completion, not a request for more approval checkpoints.

## (F) Not checked / uncertainty log

**Material inspected.** All three supplied dispatches, both main reports and all four review reports were read. The current sections of all three validation documents were compared, together with relevant historical rank and milestone entries. The repeated historical sections were checked for byte identity; this was not a fresh audit of every historical evidence archive.

Committed source inspection covered the eight classification/blocked/reducibility modules, PositiveGentzenSyntax, GentzenClusterRank, GentzenClusters, the proof replacement and immediate reconstruction modules, GentzenRewriteIntegration, GentzenOppositeExchangeRank, GentzenContractionBlocks, and the selected-logical rule/rank files. Imported dependencies were not all independently audited.

**Primary source.** The retrieved September 2007 Proof-Theoretical Coherence PDF has SHA-256 e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e, matching the supplied pin. Printed pp.248–253 were read; printed p.250 was also rendered and visually inspected. [Source PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf).

**Writing source.** The Stanford fetch failed. The MIT-hosted Mathematical Writing PDF was obtained with SHA-256 9bf404c2c75633a1f39aae97af0b2e9335ce6d83cf386c84906654589b4e82e6, matching the reports’ cited copy. Section 1 and the relevant Section 4 discussion were consulted. No identity with another edition is claimed. [Consulted PDF](https://jmlr.csail.mit.edu/reviewing-papers/knuth_mathematical_writing.pdf).

**Execution limits.** No Lean compiler was available on PATH in this review environment. No fresh Lean build, kernel replay, Git push, manuscript alteration or review of manuscript v5 was performed. The local uncommitted BoundaryChecks.lean was not supplied or inspected. Its reported conclusion was assessed against the independent committed-source derivation in §A2. Current remote-main synchronization was not investigated; source inspection used the requested commit 9075ecc.

**Strongest confirmed blocker:** no proved passage from the existing primitive/macro definitions and positional classification to the replacement-and-rank conclusion.

**Strongest suspected unconfirmed blocker:** the current literal blocked patterns and node-count rank may require a substantial representation comparison, or a justified revision, to support reduction for every primitive case. No counterexample to the full intended theorem was established.

**Most important unchecked item:** whether the precise target in §E is provable for the current definitions without changing them.

**Dependence on unavailable material:** the central findings do not depend on the unavailable local boundary file. A fresh compilation and complete dependency audit remain unavailable.

**Final recommendation:** reject the claim that source-faithful reduction dispatch is established. Retain the scoped replacement and classification results; redirect the continuation to the explicit Reducibility target and its representation obligations. No defect in the informal maximality manuscript follows from this audit.
