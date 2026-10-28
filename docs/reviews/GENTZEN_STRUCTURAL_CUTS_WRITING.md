# Mathematical-writing review: structural selected-cut commutations

The new source and reports give explicit hypotheses, actual sequent indices and
the role of final atomization. Their scope distinguishes the proved structural
branches from the open global induction. This review covers the eight new Lean
modules, exact public check and updated correspondence/continuation records.
The manuscript is unchanged; no new whole-paper editorial certification is made.

## Governing source and actual outline

Knuth, Larrabee and Roberts, Mathematical Writing governs the review. The
consulted local PDF is
.codex-work/references/knuth-mathematical-writing-mit-9bf404c2.pdf, SHA-256
9bf404c2c75633a1f39aae97af0b2e9335ce6d83cf386c84906654589b4e82e6.
Relevant consulted passages are §1 points 5, 10–15 and 17, printed pp.2–3, and
§4, printed p.9. The skill's report format, typed-map conventions and prohibition
of process commentary in the paper are separate editorial requirements.

The actual outline follows the proof dependencies:

1. ResidualPositions defines typed deletion, proves its inverses and constructs
   routes from all tags; these are definitions and coordinate lemmas.
2. ResidualRoutes defines SingleFiber and the residual map, then proves the exact
   head-routing diagram; this is the central component comparison.
3. StructuralResiduals realizes that diagram and proves both cut equations;
   SingleFibers supplies the actual exchange/thinning/fixed-contraction cases.
4. CutReplacement reconstructs cut-free witnesses and atomizes the final result;
   Addresses gives actual paths and their lengths; CutDescent supplies inherited
   cleanliness, strict original rank and both rank-induction branches.
5. SelectedOppositeStructural extends the earlier opposite equations and descent
   to arbitrary selected gaps. Public checks and external records state scope.

## Source comparison and actions

| Anchor | Issue or successful feature | Verified source principle / rationale | Action |
| --- | --- | --- | --- |
| SingleFiber and residual_square | The unique selected tag is specified by typed maps and coordinates. | §1 point 5, self-contained statements; points 14–15, notation. | Retain the exact quantifiers. |
| same_right/same_left | Both original input and output context orders are explicit. | §1 point 5; supplementary arrow typing. | Retain the separate typed statements. |
| rank_same_* and same_*_rank_step | The measured child differs from the routed native representation. | §1 points 10–13, connected exposition; supplementary hypothesis protection. | Identify the original child at the recursive call and avoid an output-rank claim. |
| same_*_eliminated | Final atomization could be confused with recursive re-cleaning. | §1 point 5; substantive distinction required by the earlier counterexample. | Explain the actual order once in the report; keep the code order explicit. |
| contract_singleFiber | A fixed formula may have the same label as the contracted formula. | §1 points 14–15; supplementary occurrence convention. | State the index inequality and retain the equal-label check. |
| report/manuscript boundary | Build and review information is external to mathematical prose. | Skill's mandatory prohibition. | Keep the records under docs/ and preserve manuscript bytes. |

## Definition order and notation

remove precedes its inverse laws; formula_eq precedes its use in typed fiber
uniqueness. tabulate precedes its get law. SingleFiber precedes residual and its
square. StructuralProgram.route precedes route_arrow and residual reconstruction.
Both address definitions and their ascent/length laws precede cleanliness/rank
applications. No missing or late definition was identified in this scope.

The source distinguishes an occurrence from a formula label and a structural
program from its interpreted arrow. Original selected rank means the sum on the
original two premises before routing. steps counts actual structural constructors,
including empty exchanges, and excludes equality transports. comp retains the
project's left-argument-first convention; disjunction side notation uses the
opposite category. Left/right and same/opposite are tied to the explicit types.

## Revisions, priority and scope

Keep the dependency outline. The consequential report wording is: “The original
child, before any residual reconstruction or atomization, receives the recursive
call.” It records a mathematical dependency needed for strict rank descent.
The unchanged-degree atomization/blockedness distinction remains outside the
manuscript, together with the still-open global obligations. No hypothesis,
arrow type or quantifier was shortened away.

The complete new source comments and external records were read for consistency
with the actual statements. All eight modules pass the strict build and full
transitive audit; all seven public type files and five expected negative controls
pass. The unchanged v4/v5/v6/v7 manuscript hashes pass. No new TeX build or rendered
paper review was performed for this code-only checkpoint; the earlier v7 rendered
review remains separately recorded. Existing TikZ diagrams, appendices, citations
and the accepted disclosure are preserved. Later proof families and the full-paper
endpoint remain outside the proved scope of these structural branches.
