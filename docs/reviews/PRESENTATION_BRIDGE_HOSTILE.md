# Hostile-referee review of the presentation bridge

This is an author-side AI self-audit of the new Lean constructions and
`PRESENTATION_CORRESPONDENCE.md`, not independent peer review. Scope:
correctness, source correspondence, typing, and verification boundaries.
The unchanged manuscript is Florian Lengyel, *Maximality of the Došen–Petrić
Boolean Category*, v4, 21 October 2026. Its §§2–5 and Appendix A provide the
statement boundary; no new whole-manuscript or novelty finding is made.

## (A) Kill-shots / hard blockers

Anchor: manuscript `thm:coherence`, §3; book §14.2, printed p.321;
`Presentation.Equation.relation`, `occurrenceMap`; coverage milestone I.
The narrow assertion is that the published equation quotient has a
well-defined occurrence interpretation. Any assertion that this proves
faithfulness, or completes actual-presentation maximality, is **unproved**.
Evidence: **structural_argument**. The proved implication is
`Derives f g → relation f = relation g`; no converse is supplied. Distinct
projections follow from this implication alone and cannot supply its converse.
Missing statement: for every P, A, B and f,g : `Hom A B`, equality of their
occurrence relations implies f = g. Downstream: the existing
`OccurrenceInterpretation` record and `relative_maximality` cannot yet be
instantiated for this quotient. Severity: fatal for a completed maximality
claim; repairable by actual Boolean Coherence. The report and maps retain
this blocker explicitly.

The earlier absence of typed presentation syntax, `Structure`, and the
source zero formula is resolved by the compiled declarations named in the
checkpoint report. This does not downgrade the remaining faithfulness gate.

## (B) Major weaknesses

1. Anchor: manuscript §3 normalization and `lem:isolation`; `Normalization`
   and `SignedLabelPreservation`; source §14.1, pp.312–315. The new n-r/rho
   arrows are available, but the normalizer with inverse arrows and its
   occurrence correspondence is not constructed. Failure mode: **unproved**;
   evidence: **absence_in_text** of an instance for `Presentation.category`.
   Missing deliverable: the typed `normal`, `forward`, `backward`, both inverse
   laws, and signed-label transport. Downstream: isolation remains conditional.
   Severity: major; repairable by those constructions.
2. Anchor: source §14.3, p.322, Boolean-category definition; correspondence
   row for negation on arrows. The source defines a derived contravariant
   arrow operation. No such operation on the quotient or its functor and
   naturality laws is provided. Failure mode: **unproved**; evidence:
   **absence_in_text**. Downstream: no full Boolean-category record or
   universal property is claimed. Severity: major for that endpoint;
   repairable using the exact clauses on pp.311–316 and 322.
3. Anchor: `Presentation.substitution`, `Substitution.Closed`, coverage II.
   The per-substitution arrow functor and operation laws are proved. They do
   not prove that an arbitrary congruence is substitution stable. The bridge
   restricting every congruence of the complete presentation to the existing
   `Congruence` record is not packaged. Failure mode: **unproved** if inferred;
   evidence: **structural_argument**, since quotient equality and an additional
   congruence are different relations. Schema identity/composition with
   endpoint casts and Appendix A coordinate laws are also open. Downstream:
   no actual maximality instance. Severity: major; repairable without changing
   the quantified target.
4. Anchor: the 71-row equation table and source inheritance, pp.145,207,270,317.
   Lean checks the written presentation; it cannot certify a transcription
   from a PDF. Evidence: **structural_argument**. The source was consulted
   through the exact revision and inherited definitions, and the table makes
   every schema inspectable. An independent source-transcription review is
   not available. Failure mode: **unknown**, rather than a fabricated missing
   equation. Severity: major for independent correspondence certification;
   repairable by a second source review. No confirmed omitted or extraneous
   generator was found in this author-side comparison.

## (C) Minor issues

Anchor: `Op`, `assocR`, `swap`, and the correspondence conventions.
The book reverses the disjunctive symmetry indices, while the Lean constructor
uses a uniform source-to-target order. Omitting that convention would be
**ambiguous**. Evidence: **citation**, §6.4 p.121, together with constructor
types. The table and syntax docstring state the conversion. Severity: minor;
repair implemented. A count of 71 constructors must not be described as 71
individual equation instances, since `Op` packages two schemas. This
qualification is also implemented.

## (D) Cross-section consistency failures

No confirmed inconsistency was found within the scoped bridge claim.

| Claim | Typed data and law checked | Argument / boundary |
| --- | --- | --- |
| Syntactic category | Objects `Formula P`; `Hom A B = Quotient (Derives)`; covariant composition and tensors | Descent uses explicit congruence constructors; semantic equality is absent from the generators. |
| Source equations | `Equation` and lifted `Laws` | §11.5 removes `(m e∧)` and `(m e∨)`; `(w k k)`, terminality, initiality, and `(0ηε)` are derived rather than assumed. |
| Products and coproducts | For f : X → A and g : X → B, `pair f g : X → A ∧ B`; dual copair | `DiagonalData.diag_projections` derives eta using the medial square, units, and genuine source laws. Both beta equations and uniqueness compile. |
| Constructed zero | `zeroConstruction A : A → A`; `zeroConstruction_eq`; `ZeroIdentity.law` | Existing arrows into bottom are equal by `(0I)` and zero_bot = id. The contradiction arrow absorbs a zero on A; naturality squares move it through the displayed composite. The zero law then identifies the composite with primitive zero. |
| Occurrence interpretation | Object map A ↦ A.Occ; arrow map `Hom A B → Rel A.Occ B.Occ` | Every defining equation and derivation preserves relations; identity, composition, tensors, and §5 operation images compile. No converse is used. |
| Nonthinness | For p : P, `fst (var p) (var p) ≠ snd (var p) (var p)` | Equal arrows would have equal relations; evaluate at the first tagged position. No faithfulness premise. |
| Empty hom-set | `¬ Nonempty (Hom top bot)` for every P | Raw terms preserve a classical propositional truth valuation, including genuine negation. Quotient representatives would imply True → False. No zero arrow is invented without a witness. |
| Substitution and double negation | Whole-arrow/endpoints substitution and the two n-arrows | All equation schemas are stable under substitution, including the letterless condition; inverse equations give `DoubleNegation` directly. |

The one-way two-object category A → B with no B → A does not admit the
entire formula/product/coproduct signature and is not a counterexample to
these constructions. The relevant absence-of-arrows test is the proved
empty `Hom(top,bot)`. Repeated occurrence tags, negative literal objects,
and empty unit occurrence sets are included in the constructions.

## (E) Acceptance conditions, non-negotiable

1. The scoped bridge claim requires a strict build and transitive axiom audit
   for the recorded source inventory, plus rejection of the stated negative
   controls. Failure rejects the checkpoint's verification claim.
2. Full milestone I requires the faithful interpretation for this actual
   quotient. Soundness and nonthinness alone do not meet it; failure rejects
   completion of that milestone.
3. Intended maximality requires normalization, signed-label preservation,
   congruence restriction, and the remaining substitution correspondence,
   followed by an actual `relative_maximality` instance. Failure rejects
   an actual-presentation maximality claim.
4. A full §14.3 Boolean-category bridge also requires the derived negation
   functor and stated naturality/dinaturality laws. Failure rejects that claim.
5. Palomar readiness requires separate independent statement/shared-definition,
   source-closure, kernel, and official checks. Failure rejects readiness;
   the present local checks make no acceptance claim.

## (F) Not checked / uncertainty log

Boolean Coherence, the distributive-dicartesian coherence on which the book's
proof depends, normalization, signed labels, derived arrow negation,
substitution-schema composition, the every-interpretation model corollary,
and remaining Appendix A laws were not proved. No independent reviewer,
Challenge/Solution comparison, independent kernel replay, official preflight,
service verification, publication, or comprehensive novelty search was run.
The build/audit results and evidence hashes are recorded in the presentation
report. The manuscript TeX/PDF checksums are retained; no new manuscript
rendering or layout review is claimed.

Strongest confirmed blocker: occurrence faithfulness for the actual quotient.
Strongest suspected unconfirmed blocker: unknown; no mathematical
counterexample or omitted generator is asserted. Most important unchecked
item: the book's coherence reduction through pp.318–321 and its inherited
coherence inputs. The limited scope judgment does not depend on unavailable
material; independent correspondence certification is unavailable. Final
recommendation for a claim of completed actual-presentation maximality:
**reject**. This does not assert a defect in the narrower compiled bridge.
