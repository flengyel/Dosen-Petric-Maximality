# Concrete mix algebra: mathematical-writing review

The source states eight typed equalities in a useful order: tensor distribution,
mix decomposition, splice distribution, then the actual native mix equation.
The documentation explicitly separates these algebraic inputs from missing
binary cut reconstruction. No manuscript change is required by this review.

Scope: GentzenMixUnion.lean, Checks/MixUnion.lean, this checkpoint's construction
report and active correspondence records. Applies
[mathematical-writing](plugin://plugins_6abdaee576ac8191ba3f7c46784e1f59).
Governing source: Knuth, Larrabee and Roberts, Mathematical Writing, consulted
locally in Section 1, points 5, 10–15 and 17, printed pp.2–3, with contextual
Section 4 discussion, printed p.9. Supplied PDF SHA-256:
9bf404c2c75633a1f39aae97af0b2e9335ce6d83cf386c84906654589b4e82e6.
This is an editorial source-correspondence review, not correctness certification.

## Actual outline

1. Four tensor/union lemmas: establish algebraic compatibility using explicitly
typed product and coproduct projections/injections.
2. mix_union: identify mix with its two derived projection-injection paths.
3. Two splice/union lemmas: apply the earlier compatibility to actual splice.
4. native_mix_union: connect the algebra to the actual G constructor and context
folds, retaining the reversed native placement of its two children.

The main additional bridge is native_mix_union. Its prerequisites precede it;
the existing union, splice and native G/Rules syntax are imported before use.

## Comparison and notation audit

| Anchor | Feature / reader risk | Verified source principle or editorial rationale | Action |
| --- | --- | --- | --- |
| All eight theorem statements | Full Hom types and quantifiers remain explicit | §1 point 5, self-contained statements | Retain |
| mix_union and native_mix_union docstrings | Identify the purpose before the equality | §1 points 10–13, connected explanation | Retain short introductions |
| native_mix_union | “First child” could otherwise be mistaken for first list block | §1 point 17, unambiguous reading; exact typing rationale | State second/first block placement explicitly |
| Construction report and active table | Algebraic equality could be mistaken for an Eliminated witness | Editorial scope precision | Keep binary equation/reconstruction status open |

NormalForm, Hom, union, tensor, mix, splice and G.mix are defined before these
uses. The operation name union denotes the existing derived arrow, not a new
set-based equality criterion. Composition remains left-argument first. Product
and coproduct laws have separately typed proofs; no unproved general proof
reflection is introduced. Every variable and context is bound. Empty contexts,
negative literals, witnessed zeros and distinct tags remain in force.

## Edits and organization

No alternative outline is warranted. The new source comments explain the
mathematical operation and native block placement. The active records name the
eight exact declarations and preserve the narrower conclusions. No theorem,
hypothesis, equality direction, appendix, citation, disclosure or diagram was
changed. Process and verification commentary remains outside manuscript prose.

## Scope and verification

All new source/comments and statements were read. The full strict Lean build,
expanded public types and dependency/source audits pass. No new manuscript prose
or TeX source was edited, compiled or rendered. Hashes verify manuscript bytes
unchanged. No new literature claim or novelty assessment was made. No independent
writing review or whole-manuscript certification is claimed.
