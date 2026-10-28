# Mathematical-writing review: disjunction and principal degree steps

The new source documentation and correspondence reports state the principal
reduction and its conditional degree step precisely. They keep the open global
induction explicit. This review covers the sixteen new Lean modules, the exact
public check and updated claim/continuation records. It supplies no new whole-paper
editorial certification; v7 and all earlier manuscript files are unchanged.

## Governing source and actual outline

The governing source is Knuth, Larrabee and Roberts, Mathematical Writing.
The consulted PDF is retained locally as
.codex-work/references/knuth-mathematical-writing-mit-9bf404c2.pdf, SHA-256
9bf404c2c75633a1f39aae97af0b2e9335ce6d83cf386c84906654589b4e82e6.
Section 1, points 5, 10–15 and 17, printed pp.2–3, and the contextual discussion
in §4, printed p.9, inform this review. The skill's report format and supplementary
typing/diagram conventions are separate editorial requirements.

Actual dependency outline and functions:

1. MirrorCalculus defines the reversed, object-reindexed hom interpretation and
   proves its laws; MirrorSplice, MirrorDistribution and MirrorProductCalculations
   supply the typed diagram calculations; MirrorPrincipalEquation assembles them.
2. MirrorInterpretation identifies the actual sourceConj and splice diagrams.
   CrossComponents, HeadRouting and SideProductCalculations establish the precise
   component permutations; InverseContextAssociativity treats both list sides.
3. PrincipalDisjunction states the reflected equation; Native gives its ordinary
   two-splice form; Rule instantiates G denotations; Selected treats any tagged gap.
4. PrincipalDegreeSteps defines DegreeBelow before its use and proves both
   conditional principal branches. RankTwoDegreeStep combines exhaustive cases.
5. The public check records the actual types, equal-label positions, Empty atoms
   and dependency results. Reports and maps give the scope and continuation.

## Source comparison and actions

| Anchor | Issue or successful feature | Verified source principle / rationale | Action |
| --- | --- | --- | --- |
| selected_equation and rule_equation | The formula, both context orders and exact equality are explicit. | §1 point 5, self-contained statements. | Retain the full types. |
| DegreeBelow and both degree_step statements | A conditional induction branch can be mistaken for the endpoint. | §1 point 5; supplementary hypothesis protection. | State the strictly smaller degree hypothesis before the branch and retain the open global status in reports. |
| reduction and reflectionInput | Written association differs from operational cut order. | §1 points 14–15, consistent notation; supplementary composition convention. | Specify B first, then A; keep the actual association maps typed. |
| MirrorInterpretation | The reader needs the relationship to the actual source rule. | §1 points 10–13, connected explanation and purpose. | Name sourceConj and the explicit splice comparisons before the native equation. |
| source §11.2 pp.254–255 correspondence | The disjunction case is described by analogy. | Supplementary primary-source and exact-correspondence requirements. | Record the directly proved native construction; assert no unwritten displayed equality. |
| report versus manuscript | Build/review status belongs outside the mathematical paper. | Skill's mandatory process-commentary prohibition. | Keep every such record under docs/; preserve manuscript bytes. |

## Definition order and notation

mirror and MirrorCalculus.Hom precede their operations and laws. reflectedSplice
precedes reflected_equation; binaryInput, frontTwo and reflectionInput precede
the native equation. The G reduction and normal denotation precede their equality
proofs. DegreeBelow quantifies over strictly smaller degrees and arbitrary head
contexts before either degree_step uses it. The existing definitions of selected
At positions, erase, CutFree and Atomized are imported and reused.

Repeated labels retain distinct At tags. The source and target are checked at
every composition; side .disj uses opposite composition, while the final native
statements use ordinary Reduced composition. Operational inner/outer terminology
refers to the order of recursive cuts. No equality of objects is silently replaced
by an unspecified isomorphism. Empty contexts retain the actual unit comparisons.

## Revisions and priority

Keep the existing dependency outline. The report's consequential scope wording is:
“DegreeBelow has not been discharged globally. These conditional induction branches
do not prove CutElimination or AtomizedCutElimination.” This qualification expresses
a real open mathematical premise. It is not added to the manuscript as an audit
remark. The source/native reduction-order distinction remains in the correspondence
and correction records, together with the earlier conjunction distinction.

No theorem hypothesis, quantifier, arrow type, manuscript diagram or accepted
author disclosure was removed. No new manuscript figure was needed: this change
adds checked source equations and external records. Existing TikZ diagrams and
Appendices A–C remain preserved. Further prose changes are not required for this
bounded implementation.

## Scope and verification

The exact Lean statements and source comments were reviewed in dependency order.
The final strict build, six exact type files, full dependency audit, five expected
control rejections, public closure and manuscript hashes pass. V7's prior rendered
review remains recorded separately; no new TeX build or rendered-paper claim is
made for this unchanged manuscript. Later reductions, global elimination and
full-paper mathematics remain outside the proved scope of this checkpoint.
