# Writing and correspondence review of principal conjunction reduction

This author-side review uses
[mathematical-writing](plugin://plugins_6abdaee576ac8191ba3f7c46784e1f59).
The governing source is Knuth, Larrabee and Roberts, Mathematical Writing,
§1 points 5, 10–15 and 17, printed pp.2–3, and the retained §4 qualification
on definition placement, printed p.9. The retained governing PDF was consulted at these passages in
this continuation; its SHA-256 is
9bf404c2c75633a1f39aae97af0b2e9335ce6d83cf386c84906654589b4e82e6.
The review concerns the actual new proofs and correspondence records.

## Outline and dependency order

1. CutDistribution: factor the two distribution strengths; prove mixed_strength.
2. ProductCalculations: derive structural product adapters from the established
   product universal property, without a new coherence premise.
3. PrincipalConjunction: prove the typed categorical two-component identity.
4. ContextAssociativity/TripleContexts: account for each tag, inverse, unit and
   list-association transport in the actual fold comparisons.
5. PrincipalConjunctionRule: build the actual two cuts and prove native equality.
6. LogicalHeadRouting/PrincipalLogicalTransport: route an internal principal
   formula while moving its two component tags below the new logical rule.
7. PrincipalConjunctionSelected: instantiate the equation at arbitrary tagged
   gaps; prove exact count, atomization equivalence and degree decreases.

Definitions precede their uses. Hom endpoints and the source/target contexts
are explicit. Process reports stay outside mathematical prose. No reorganization
of the manuscript's accepted outline is needed.

## Findings and resolutions

| Anchor | Risk to the reader or correspondence | Governing principle | Resolution |
| --- | --- | --- | --- |
| rule_equation / source p.254 | Confusing the checked native A-then-B reduction with the displayed B-then-A order | Precise claim and explicit dependency | Record the alternative order, direct Reduced proof and same original cut outside the manuscript. |
| selectedReduction_count | Calling a two-cut equation a cut-free normal form | State exactly what the argument proves | Keep count two and global induction explicitly open; require inner elimination before the next outer topmost call. |
| component_degrees | Inferring a returned-rank bound after degree drops | Make the operative hypothesis visible | Both component degrees are strictly lower; no rank hypothesis is stated. |
| tripleIso / split_assoc | Hiding unit and opposite-coproduct transports | Explicit typing and connected explanation | Assemble actual isomorphisms, prove inverse/comparison laws and retain empty contexts. |
| LogicalHeadRouting.square | Losing equal-label tags or moving a rank-one property through an exchange wrapper | Consistent objects and notation | Check first/second/fixed positions; place component exchanges below the fresh native rule. |
| selected_equation | Different witnesses or output contexts could be conflated | Keep the same mathematical object throughout | One explicit reduction at the exact output with Reduced equality and its own Atomized/count laws. |
| Full-paper maps / Appendix C | Local progress could be overstated as global completion | Scale claims to proof | Update all current maps; concrete blocked rank correspondences and global elimination remain open. |

The bounded mathematical exposition is adequate. The typed equations carry the
required comparison-square content; no new manuscript diagram was requested.
All ten existing TikZ diagrams, accepted disclosure, v4/v5/v6 baselines and v7
source/PDF remain unchanged. Established composition, witnessed-zero, tag,
ordinal-coordinate and source/native decisions are retained.

## Verification and limits

The strict build/dependency audit checks 474 Lean files and 11,403 declarations.
All five exact type files, five expected negative-control rejections, public
source closure, manuscript hashes and whitespace pass. Retained evidence
identifies commands, exits, failed attempts and checked bytes. This writing
review supplies no independent mathematical, kernel, Comparator or service status.

The next proof work is the dual principal reduction, remaining commuting and
blocked equations, and the discharged global induction. All later full-paper
obligations remain authorized and open at their recorded statuses. Retain this
review in docs/reviews/ and deliver committed bytes to Downloads with the report's
post-commit path/hash verification.
