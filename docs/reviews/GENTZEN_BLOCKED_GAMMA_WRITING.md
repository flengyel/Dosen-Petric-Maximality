# Writing review of the first three blocked reductions

The new local argument has a coherent dependency order: common occurrence maps,
parallel splice equations, native context folds, actual source identification,
then eliminated witnesses and original-rank calls. Current coverage must say three
blocked cases completed and eleven pending. No change to manuscript v7 was
mathematically required.

This applies [Mathematical Writing](plugin://plugins_6abdaee576ac8191ba3f7c46784e1f59)
to the actual twenty modules, their comments, run report and linked active records.
The governing source is Knuth–Larrabee–Roberts, the retained MIT copy with SHA-256
9bf404c2c75633a1f39aae97af0b2e9335ce6d83cf386c84906654589b4e82e6.
Section 1 was consulted, especially point 5 on self-contained statements,
points 10–11 on connected explanation and definitions, and points 12–17 on
motivation, notation and readable prose; relevant definition placement in
Sections 4–5 was consulted in the continuing review. These are source principles;
the outline and reporting format below are the review workflow.

## Actual outline and mathematical functions

1. BlockedMixCore: shared input/output comparisons and the parallel splice
identity. Function: definitions and the mix calculation.
2. BlockedMixRoutes/Coordinates: finite structural programs, product/coproduct
splits and exact folds. Function: constructions and their equations.
3. BlockedMixNative/Source, SelectedRouteFactor: native reconstruction, selected
head/residual correspondence and arbitrary original-child factorization.
4. BlockedGammaMixData, SelectedContractionDescent, BlockedGammaMix: actual
source positions, inherited Clean/rank and complete left gamma-mix reduction.
5. RightMixCore/Coordinates/Native/Source and RightGammaMix: the separately typed
right gamma-mix calculation and actual source/rank correspondence.
6. BlockedConjLift/Core: the two coproduct-injection calculations and common splice
kernel for conjunction. Function: the central new logical equation.
7. BlockedConjNative/Source/Equation and BlockedGammaConj: actual native folds,
source identification, reconstruction and two original-rank calls.

The central question is how to reduce a cut whose selected premise ends in one
of these three actual blocked contractions. Each final handler gives a cut-free,
atomized same-sequent witness from the two strictly smaller original child cuts.
It does not yet discharge the global induction hypothesis.

## Comparison with the governing source

| Anchor | Issue or confirmed strength | Principle / rationale | Action |
| --- | --- | --- | --- |
| Three final rank_step statements | All selected contexts, ranks and hypotheses are explicit | Section 1, point 5 | Retain the full types |
| selectedResidual / selected_factor | Definition precedes selected-component equation | Section 1, point 11 | Retain the head/fixed-tag distinction |
| BlockedConjLift.lifted_pair | Final residual association is part of the equation | Source notation advice; independent typing requirement | Preserve assocL in statement and applications |
| source / native / rank sequence | Source term identification precedes completed correspondence claim | Connected explanation, points 10–13 | Retain the existing organization |
| Active status blocks and constructor table | Earlier fourteen-open count is superseded | Accurate claim scope; editorial rationale | State exactly three completed and eleven open |
| New comments and unchanged v7 | Mathematical functions and qualifications carry content | Economy and reader-directed prose | Keep process reports outside the manuscript |

## Definitions, notation and variance

sharedInput/sharedOutput and rightSharedInput/rightSharedOutput are defined before
their splice equations. Route.selectedResidual is typed by the erased selected
contexts; selected_factor gives the full product-category equation. firstTag is
an actual occurrence, with gammaBlock defining its source contraction before the
position lemmas. Equal labels remain distinct tags. The conjunction lift fixes
its output association at definition time. parallel is separately namespaced for
mix and conjunction, and every public example resolves its local namespace.

Category.comp applies its left argument first. Op.disj uses the opposite category
for structural product comparisons; the reported Reduced equations retain their
actual arrow direction. Same-degree rank refers to the original syntactic
selected premises, and full Clean is inherited before routing. Cut-free structural
atomization is applied after reconstruction. These conventions remain consistent
with the predecessor manuscript and declarations.

## Prioritized repairs and outcome

The active status block is replaced consistently across README, contract, claim,
coverage, validation and continuation records. Its operative wording is:
“BlockedL.gammaMix, BlockedR.gammaMix and BlockedL.gammaConj have actual source
reconstructions and instantiated original-rank steps. Eleven blocked reductions
and discharged global induction remain open.” The constructor table names the
three actual final handlers. The prior continuation is archived verbatim.

The complete new mathematical comments were inspected for their function and
read continuously with their declarations. No process-only paragraph was moved
into mathematical source, and no mathematical hypothesis or equality was removed
for economy. The existing outline works; no revised outline is proposed. No
manuscript correction is inferred from an unfinished formalization task.

Scope: actual new Lean argument and current correspondence prose. All nine
manuscript blobs remain unchanged, preserving v7, the authorized errata appendix,
older versions and diagrams. No fresh whole-paper prose or PDF/layout review,
TeX compilation, new bibliographic verification or independent mathematical
certification is claimed. Local build/check evidence is reported separately.
