# Complete Lean formalization of manuscript v6

Authorized scope: 25 October 2026. The project target is the complete mathematical
content of *Maximality of the Došen–Petrić Boolean Category*, including the short
proof in v6, the actual-presentation maximality theorem, the model corollary,
and both appendices. A conditional maximality theorem alone does not complete
this task.

## Governing source and instruction order

The fixed manuscript baseline is
`manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v6.tex` at commit
`810dcdbccc76a4307028773c561f36b910b5170c`, SHA-256
`2c30fd10cb81f5d8246dabdc7f343d6d9adeac91358d84273d2799ab514972b0`.
The PDF has the same basename. Read the complete source, both appendices,
`AGENTS.md`, the statement and coverage maps, and the presentation correspondence.
Follow later explicitly authorized manuscript changes and update the source
anchor and claim ledger together; do not silently change the formal target.

This document governs the overall endpoint. `CODEX_NEXT_SESSION.txt` identifies
the immediate continuation. `CODEX_AFTER_05C6BC8_REDUCIBILITY.txt` and
`CODEX_GENTZEN_REDUCIBILITY_2026-10-24.txt` retain their exact mathematical targets
as subordinate instructions for the coherence work. Their older references to
the governing task do not restrict the project to Reducibility. Preserve their
source-shaped statements, rank conditions, and existing verified results.

The three existing milestones remain distinct: the structural collapse
interface, conditional relative maximality, and maximality for the actual
presentation. Full-paper completion is an additional requirement beyond those
milestones. Historical checkpoints are evidence of progress, not current proof
instructions when superseded by the current continuation and maps.

## Required endpoint

For every nonempty variable type P, construct the actual September 2007
equation-generated zero-identity Boolean category B(P), and prove that every
proof congruence closed under uniform endosubstitution which identifies distinct
parallel arrows identifies every parallel pair. Also prove the equivalence
with the statement that the only substitution congruences are equality and
the total congruence.

The final theorem must quantify over the actual source quotient and its actual
proof congruences. Instantiate or prove every interface used by
`relative_maximality`, including the restriction/correspondence for congruences
and substitution closure. Do not replace B(P) by `GeneratedModel`, a relation
category, a structural fragment, or a newly strengthened presentation.

Published mathematical inputs needed by the proof, especially Boolean
Coherence and the particular structural isomorphisms, must have Lean proofs
for this presentation or be supplied by compatible, pinned, verified library
theorems with proved correspondence. A citation, record field, local axiom, or
uninstantiated hypothesis does not discharge an input. Conditional lemmas remain
useful intermediate results and must remain labelled as such.

Complete mathematical content means the definitions, results, constructions,
equations, examples, and diagram identities developed in the paper, including
unnumbered assertions, together with the dependencies needed to prove them.
Bibliographic, historical, novelty, and disclosure prose does not require a
Lean encoding; nor does the task require formalizing every theorem mentioned
only to describe related literature. The paper's concrete non-cartesian-closure
argument does belong to the mathematical target.

## Claim ledger and correspondence

Maintain a complete claim ledger in `MANUSCRIPT_STATEMENTS.md`, with one entry
per numbered result or displayed identity and sufficient entries for the
unnumbered claims. For each entry record the manuscript label or precise prose
anchor, exact Lean declaration and file, hypotheses and universes, correspondence
proof, and status. Distinguish an existing declaration, a conditional theorem,
an instantiated source-presentation theorem, and an open obligation. A source
label cannot be marked complete merely because a weaker contextual consequence
or an analogous result in another model has been proved.

### Procedure for any necessary corrections

If a necessary correction is established during this work, its repair is
included in the task. This applies to manuscript claims, Lean statements and
proofs, source correspondences, citations and exposition. Maintain
`MANUSCRIPT_CORRECTIONS.md` outside the paper. For each confirmed defect record
the exact source anchor, evidence, repair, affected declarations or diagrams,
verification and resolution. Distinguish a confirmed error from an open proof
obligation, a suspected issue and an optional editorial preference. The current
record contains no outstanding confirmed manuscript error; this procedure does
not assert that one has been found.

Apply each justified correction consistently to the mathematical source and
formalization. Rebuild and inspect the PDF whenever its source changes, and run
the relevant Lean checks whenever proof sources change. Update the source
anchor, correction record, claim ledger and continuation together. Do not
silently weaken a statement, omit an appendix, change a definition, or remove
a mathematical qualification to make completion easier. If a substantive repair
cannot be proved, keep the affected claim open and state the exact obstruction.

Carry each accepted correction through the entire affected scope in the same
work pass: definitions, statements, proofs, repeated prose, diagrams, captions,
source comments, formalization, claim maps and reports as applicable. Search for
parallel instances and re-read the connected passages after editing. Preserve
the decision and verified resolution in the external record and continuation;
do not rely on the author's repeating it in later prompts. Record an accepted
editorial preference as such, rather than misclassifying it as a mathematical
error. A later steering message supplements the active task unless it explicitly
replaces it.

### Occurrence-substitution presentation

The tagged-block presentation is a required expository contribution of the
paper. Preserve its separation of outer occurrences, positions within inserted
formulas, and placeholder labels, together with the typed maps, commutative
diagrams and worked example. Its expository contribution is the explicit
organization of these data and their relation to substitution.

Prove exact correspondence with the finite-ordinal formula in
Došen–Petrić, *Proof-Theoretical Coherence*, September 2007, §2.5, pp.45–46.
In particular, verify gamma, both coordinate bijections, the transported delta,
the block locator, empty blocks, repeated labels and noninjective renaming.
An implementation of the ordinal formula alone does not complete this
correspondence obligation. Keep the mathematical account self-contained and
describe the maps and their properties directly; attribute the source formula
and the occurrence-coordinate presentation precisely.

The following list is mandatory coverage, not permission to omit a mathematical
claim found during the complete manuscript read.

| Manuscript component | Required formal content |
|---|---|
| §2 presentation and operations | Typed formula and arrow syntax, generated equality and quotient category; the specified products, coproducts, units and distributor; source correspondence for the primitive and derived operations and equations. |
| §2 negation | Derived contravariant arrow negation, its functor laws, and the specified natural double-negation and De Morgan isomorphisms, including constants. Object-level negation and a double-negation retract alone do not discharge this claim. |
| §2 equations (1)–(3) and zeros | The first-injection equation, equality of the displayed five-arrow zero composite with the source zero identity, the zero law, witness independence, commutation and absorption for inhabited hom-sets. |
| §2 congruences and Theorem 2.1 (`thm:main`) | Closure under every specified arrow operation, including derived negation, pairing and copairing; action of uniform substitution on arrows and endpoint types; actual-presentation maximality in both stated formulations. |
| §3 occurrences and Theorem 3.1 (`thm:coherence`) | Tagged occurrence sets, label maps, coordinate encoding, all stated relation operations, and the actual functor G; soundness and faithfulness for the source quotient, so both directions of the coherence equivalence are proved. |
| §3 unnumbered consequences | Distinct projections and id_p ≠ zero_p; each Hom(top,E) subsingleton; the resulting obstruction to a cartesian closed structure with the specified products; normal-form isomorphisms and their occurrence graphs; preservation of complete signed literal labels. |
| §3 substitution, (4)–(5) | The occurrence-block bijection and inverse, label compatibility and block square; the whole-arrow substitution functor and compatibility with generated equality and operations. Record identity/composition and endpoint transports needed by the appendix and model interpretation arguments. |
| Lemma 4.1 (`lem:isolation`) | Actual typed selector/coselector witnesses for the original endpoint formulas, their exact composite and zero equations after any required interchange of f and g, and the normalized relation calculation. A normalized contextual consequence alone is not the printed witness theorem. |
| Proposition 4.2 (`prop:all-contexts`) | From a new substitution-closed equation to K_A for every A, with both literal signs, whole-arrow substitution, the double-negation square and zero transport. |
| Lemma 5.1 (`lem:structural-isos`) | The particular q_A and e_A maps defined below are isomorphisms in the actual source quotient for every A; both inverse equations and the required substitution transport. |
| Lemma 5.2 (`lem:collapse`) | The short q/e quotient argument below, with only proof-congruence closure once all K_A are given. |
| Corollary 5.3 (`cor:models`) | The statement for every interpretation in every model of the specified presentation, with the interpretation/quotient bridge and substitution stability proved; conclude thinness of arbitrary model hom-sets. |
| §6 formalization mathematics | Retain the existing symmetric-fold proof as a separate route. Identify its displayed composite with mix followed by codiagonal, and prove the parameter independence and symmetry used there. Keep the prose scope aligned with the verified source. |
| Appendix A.1 | Profiles and dependent block sets D and C; injections a_r, b_i; existence and uniqueness of gamma; block projections; the fibre and profile squares; the actual-substitution bijection chi and label square. |
| Appendix A.2 | Prefix sums, both ordinal encodings and their inverses, existence and uniqueness of delta, the ordinal square and coordinate equation, the unique block locator including empty blocks, and correspondence with the book's generalized composition. Prove skeleton-plus-profile reconstruction and its compatibility with substituted patterns; verify the displayed eight-position example and delta(2)=3. |
| Appendix A.3 | Renaming and substitution square for arbitrary, possibly noninjective rho; preservation of separate occurrence positions under repeated names; specialization to the positive and negative substitutions in Proposition 4.2 with the stated endpoint types. |
| Appendix B | Explicitly typed path equalities for the first-injection triangle, five-arrow zero diagram and zero-law square, identified with the actual source operations. Reuse existing equations where they already prove these exact paths; duplicate proofs are unnecessary. |

For Appendix A, cover empty profiles and blocks whenever the displayed maps
exist. Do not impose positivity, injectivity of label maps, distinct actual
variables, or nonempty occurrence sets for convenience. Give an explicit
translation between any zero-based Lean `Fin` coordinates and the manuscript's
one-based finite ordinals.

## Formalize the shorter proof as well as its conclusion

The old symmetric-fold proof remains valuable and must be preserved. Its
existence does not complete the new proof-correspondence obligation for v6 §5.
Introduce the actual maps, with j_A the first injection A → A ∨ top:

    q_A = [j_A ∘ π₁^(A,bot), ι₂^(A,top)]
        : (A ∧ bot) ∨ top → A ∨ top
    e_A = 1_A ∧ j_A
        : A ∧ A → A ∧ (A ∨ top).

Prove both are isomorphisms. The manuscript identifies them with published
isomorphisms first at a variable p, using occurrence graphs and, for e_p, a
possible product swap, then applies substitution. Formalize those identifications
with proved source inputs, or give direct inverse equations in the same source
quotient and record the correspondence. A bijective occurrence graph alone does
not imply invertibility under a merely faithful functor.

For a proof congruence satisfying every K_A, formalize this sequence:

1. Set E = A ∨ top, S = (A ∧ bot) ∨ top, and s = ι₂ : top → E.
   Prove the relevant zero arrow equals s ∘ ! in the original category.
2. Obtain q_A ≡ s ∘ !_S. Transport its original inverse equations through the
   congruence, deduce 1_E ≡ s ∘ !_E, and prove that E is terminal in the quotient.
3. Prove that r = π₁ : A ∧ E → A is invertible in that quotient and that
   r ∘ e_A = π₁ : A ∧ A → A.
4. Use the diagonal as the inverse of this projection to obtain π₁ ≡ π₂;
   use pairing to equate arbitrary parallel arrows.

Prove the required quotient preservation of products, coproducts, units and
inverse equations, or implement an equivalent proof directly modulo the
congruence. Use coherence only in the original category. Do not assume quotient
faithfulness, cancel j_A, or supply zero arrows for empty hom-sets. Connect this
proof to Proposition 4.2 and the actual-presentation main theorem, rather than
leaving it as a disconnected conditional demonstration.

## Model corollary

Define interpretations for the full source signature and prove the induced
functor out of the equation-generated quotient. Prove that agreement under
every interpretation forms a proof congruence closed under endosubstitution;
this requires composition of an interpretation with substitution to be another
interpretation. Do not assume that the kernel of one interpretation is
substitution closed.

Use nonempty P to choose p, interpret p as an arbitrary object X of the target
category, and transfer equality of the projections at p to the projections at
X. Pair arbitrary target arrows to conclude thinness. No surjectivity of an
interpretation on objects or arrows may be an added assumption. Keep the target
model universe general enough to express the printed corollary.

## Immediate continuation and dependency order

For local Codex's concrete W6 implementation, also read
`CODEX_W6_CONSTRUCTION.md` and its two linked reviews. The author assigns
implementation/builds to local Codex and research, instructions and review to
ChatGPT. The construction analysis adds no checked Lean result and does not
change this full-paper endpoint.

The current Lean baseline is `1e967bcb913a74ae590dde940f246acaddce1fba`; later
manuscript commits have not completed any additional Lean obligation. Inspect
the live repository before work and preserve newer changes; this is not an
instruction to reset to the baseline.

Continue first from `CODEX_NEXT_SESSION.txt`: construct logical W6 with both
premises' parametric copies and the selected fresh compound, retaining the
actual `disjLLast` exchanges. Complete logical W5/W6, transport and general
profile-to-reducer dispatch, then both full Reducibility Lemmata with their
unchanged complete post-replacement descendant bounds. Reuse proved cut-entry
uniqueness, addressed W4 and constructed mixed-premise mix W5; do not restart
those completed branches or replace the full targets with auxiliary results.

Then prove the necessary outside-site transport, finite multiset descent,
Blocked-w and cut elimination; obtain positive/reduced coherence and Boolean
Coherence for the actual presentation. Build the remaining source instances
and congruence bridges, complete the short proof and actual maximality, and
complete the model corollary and appendices. Independent algebra, correspondence,
and appendix tasks may proceed in parallel when they do not interfere with
this dependency chain or verification. Follow mathematical dependencies rather
than treating this paragraph as a requirement to postpone all independent work.

Do not change rho, blockedness, reducibility, the source equations, or a theorem's
quantifiers to make a candidate pass. If a genuine mismatch is discovered,
record the exact statement and counterexample or failed obligation, establish
the smallest justified correction, and update the correspondence explicitly.
No caller-supplied reduct, injectivity, rank bound, assumed coherence, or
unproved equality reflection may discharge a general Reducibility theorem.

## Completion and verification

Full-paper completion requires all of the following:

- Every confirmed correction affecting a claimed result or correspondence is
  implemented and verified before that claim is marked complete. The correction
  record identifies any unresolved issue; an unproved Lean obligation is not
  labelled a manuscript error without separate mathematical evidence.
- Every mathematical claim in the ledger has an exact checked counterpart or
  a proved derivation from named checked counterparts. Every conditional input
  needed by a final paper theorem has an actual source-presentation instance.
- Both the short §5 argument and the retained symmetric-fold route have their
  stated scope verified. The main theorem and model corollary have no open
  coherence or presentation premise. Appendices A and B are accounted for,
  including examples, uniqueness statements and coordinate correspondences.
- No custom mathematical axioms, proof holes, `native_decide`, conclusion-shaped
  assumptions, unwitnessed zeros, or circular uses of the coherence being proved
  occur in production proof dependencies. Apply the existing foundation-axiom
  policy and inspect the transitive dependency closure of the final endpoints.
- Run `bash scripts/verify.sh` and the applicable source-boundary checks and
  negative controls on the final immutable source, using the pinned toolchain.
  Use one heavy build or kernel replay at a time. Verification of unchanged
  source from an earlier commit is not verification of newly added endpoints.
- Apply the hostile and mathematical-writing reviews to the actual theorem
  statements, proof correspondence, claim ledger and final manuscript scope.
  Update `MANUSCRIPT_STATEMENTS.md`, `MANUSCRIPT_COVERAGE.md`, README and the
  continuation so they agree with what has been proved.
- Preserve the existing manuscript and previous proof routes. Any necessary
  manuscript correction must be explicit, with its source and PDF rebuilt and
  verified; do not delete a claim merely to declare formalization complete.
- Commit and push verified changes to main without force under the existing
  authorization, preserving intervening work. Retain reports and perform the
  required byte-verified Downloads delivery when that destination is available;
  report an inaccessible destination explicitly. Keep publication and Palomar
  submission separate from local formalization and verification.

If an obligation remains open, record its exact statement, current hypotheses,
obstruction and concrete next proof task. Do not report the entire paper as
formalized because a conditional theorem compiles, a local reduction family is
complete, or the main theorem alone has been proved.
