# Signed labels: mathematical-writing review and normalization follow-up

The exposition now distinguishes three facts: occurrence edges preserve
signed literals, individual relations can copy or merge positions, and
faithfulness remains unproved. The normalization statements also retain their
objectwise scope. The scoped prose needs no manuscript revision.

This author-side, AI-assisted review concerns the new construction descriptions,
source map, signed-label report, and current scope records, plus a follow-up
to the earlier normalization review. It is not independent mathematical
certification or a whole-manuscript judgment. The unchanged manuscript is
Florian Lengyel, *Maximality of the Došen–Petrić Boolean Category*, v4,
21 October 2026; its relevant anchor is §3's signed-literal paragraph.

The governing text was consulted directly: Knuth, Larrabee, and Roberts,
[*Mathematical Writing*, MIT-hosted course-report copy](https://jmlr.csail.mit.edu/reviewing-papers/knuth_mathematical_writing.pdf).
The title, all three authors, Stanford autumn-1987 course preface, and section
headings were checked. The 119-page PDF has creation metadata from 2005;
it is not asserted byte-identical to the unavailable Stanford scan or the
1989 MAA edition. SHA-256:
`9bf404c2c75633a1f39aae97af0b2e9335ce6d83cf386c84906654589b4e82e6`.
The consulted local copy and source metadata are identified in
`provenance/wsl-signed-label/writing-source.json`.

Section 1 was read directly, with particular application of points 5 and
10–15. Sections 4–5 were also read. Their printed pages 9–13 correspond to
one-based PDF pages 11–15; Section 1's printed pages 1–6 are PDF pages 3–8.
Rendered printed pages 2 and 9 were inspected to verify the page convention.
The organization of this review is an editorial method, not a prescription
attributed to the book. The judgments applying its advice below are the
reviewer's own applications.

## Actual outline and contribution

| Reviewed sequence | Function / prerequisites |
| --- | --- |
| Signed-label report: exact theorem | Quantifies over variables, endpoints, terms/arrows, positions, and edges before claiming preservation. |
| Raw proof and source-family table | Explains composition, tensor tags, structural maps, parity, and empty cases in the primitive grammar. |
| Quotient, normal forms, and transport | Reuses well-definedness, literal comparison, and normalization coordinates in dependency order. |
| Copying/merging boundary | Gives explicit tagged examples that prevent overreading the invariant. |
| Evidence and remaining obligations | States actual checks and the unproved coherence endpoint. |
| Normalization report (historical checkpoint) | Supplies object normal forms and comparison isomorphisms with inverse/coordinate laws; does not supply the source functor's naturality. |

The contribution is a label invariant for the existing occurrence assignment,
not a proof that it distinguishes all arrows. This sequence works. No new
manuscript outline, replacement diagram, or reorganization is warranted.

## Comparison table

| Anchor | Actual difficulty / risk | Verified source principle or independent rationale | Implemented action |
| --- | --- | --- | --- |
| Signed-label report, exact theorem | Nonemptiness and coherence could be silently inherited from the manuscript. | §1 point 5: theorem statements should usually include their assumptions. | State arbitrary P and the sole edge hypothesis explicitly. |
| Raw induction explanation | A list of constructor calculations could hide why composition works. | §1 points 10–13: connected explanation, introduced variables, motivation, and readable prose around formulas. | Explain the intermediate occurrence and matching tag branches before summarizing cases. |
| Signed-label and polarity terminology | A label, a position, and its sign could be conflated. | §1 point 14: use notation consistently; independent typing rationale. | Keep `signedLabel`, `label`, `polarity`, and occurrence tags distinct. |
| Copying/merging paragraph | “Injectivity” could refer either to a relation or to the map on arrows. | Independent mathematical/editorial rationale. | State functionality/injectivity of one relation separately from faithfulness of the interpretation. |
| Definition order | New notation might appear before its local meaning. | §§4–5: definition placement is contextual, with definitions near use. | Reuse confirmed existing definitions, and explain the theorem's parameter types at first use. |
| Normalization report and map | Object normalization might be promoted to source-functor naturality. | §1 point 5 and independent scope rationale. | Retain both inverse-arrow statements, coordinate types, and the explicit naturality/coherence boundary. |

## Definition and notation audit

Confirmed definitions precede the new theorem: `Literal`, `Formula.Occ`,
`Formula.signedLabel`, `Formula.label`, `Formula.polarity`, the typed `Term`
grammar, `Term.relation`, `Hom`, and `occurrenceMap`. `NormalForm.literalAt`
and `signedLabel_eq_literalAt` precede specialization. `transport_apply`,
`literal_fromOcc`, `toOcc`, and `transport_coordinates` precede the transport
corollaries. None is a missing-definition finding.

The raw term and quotient arrow remain different types. The edge hypothesis
is a proposition, and the conclusion is equality in `Literal P`. A source
variable label is not an occurrence identifier. The composition convention
is operationally explicit. The two copying/merging examples require a supplied
p; the global invariant does not. No replacement of the old faithful-interface
definition is suggested.

## Source-grounded follow-up to the provisional normalization review

The historical `NORMALIZATION_WRITING.md` and its recorded access failures
are preserved unchanged. This section completes the previously unavailable
source-grounded pass for the portions it reviewed; it does not rewrite that
historical outcome.

The normalization report's hypotheses, typed forward/backward arrows, and
two identity composites satisfy the checked self-contained-statement criterion
within their scope. Its Boolean recursion paragraph gives the reader the
meaning of the sign parameter before the cases. Its source table consistently
distinguishes primitive n/r/rho arrows from derived comparisons and fixes
composition order. The definitions and graph statements identify the coordinate
maps before transport. The source's later Auxiliary Lemma, naturality, and
equivalence remain explicitly outside the constructed record. These are
observed features of the actual normalization text; no new mathematical
certification follows from them.

The prior provisional report's recommended scope sentences remain appropriate.
Its then-open global signed-edge obligation is now proved separately by this
task. Its independent rationale can therefore be checked against the governing
text without treating historical access failure as historical success. No
substantive normalization prose repair was found necessary in this scoped pass.

## Prioritized wording and scope

Retain: “Every edge preserves the complete signed literal.” Retain also:
“Label agreement does not identify occurrence tags or prove faithfulness.”
In scope maps, use: “The occurrenceMap label invariant is proved; the faithful
OccurrenceInterpretation instance remains open.” No manuscript change or
revised outline is recommended.

No whole-document layout audit, fresh manuscript compilation, novelty survey,
independent source-transcription review, or proof of coherence was performed.
The existing manuscript TeX/PDF hashes were checked. The current review and
normalization follow-up are source-grounded for the identified passages;
Stanford-server access itself still failed. Local compiler/audit evidence is
recorded separately and is not an editorial certification.
