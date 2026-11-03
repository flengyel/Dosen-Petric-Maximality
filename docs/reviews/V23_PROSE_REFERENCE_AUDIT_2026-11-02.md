# (A) Kill-shots / hard blockers

**Focused prose and reference audit of Maximality of the Došen–Petrić Boolean
Category, v23, 2 November 2026, 23 pages.** Reviewed snapshot:
`350651629e3a0893c3c9463bd87d661bd78b1cf9`.

Yes: the closer pass found additional local problems. There are four loose
references, one unexplained qualification and one redundant recap. None is a
new mathematical blocker. The two D.5 issues in the
[earlier v23 review](V23_READ_ONLY_REVIEW_2026-11-02.md) remain separate.
That report's list of minor issues was incomplete; this addendum extends it.

- [Reviewed source](../../manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v23.tex)
- [Reviewed PDF](../../manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v23.pdf)
- Source SHA-256: `b34afdb82b1f36731ef9c1d8cb6a369b07fc40a71e3189cf3c093677f3b303c2`
- PDF SHA-256: `732ce3d7886fc837b8297273ca1d33a50346ebc5b0e74a55d2b047cf52dce0c1`

This is an author-side AI-assisted audit using the mathematical-writing and
HostileRefereeGPT — Cat/Rec skills. It is not independent peer review.
The manuscript is unchanged; the repairs below are recommendations only.

# (B) Major weaknesses

None established in this focused pass. It does not reopen the previous
mathematical review or claim a fresh proof-dependency audit.

## Existing organization and its functions

| Part | Function |
| --- | --- |
| Abstract; §1 Introduction | State maximality, the collapse result and conjecture, then describe the proof and related work. |
| §2 The Boolean proof category | Define the presentation, operations and congruences; state Theorem 2.1. |
| §3 Occurrences and substitution | Define occurrence coordinates, signs, normalization and substitution; state Boolean Coherence. |
| §4 Isolating an occurrence | Select a differing occurrence pair and derive every K_A. |
| §5 Equality of the product projections | Identify q_A and e_A, prove collapse and maximality, and prove the model corollary. |
| §6 A second proof and the Lean formalization | Give the mix proof, union laws and formal correspondence. |
| A.1 Occurrence maps and their fibres | Define blocks and their maps. |
| A.2 The finite-ordinal presentation | Prove the coordinate formula and compute an example. |
| A.3 Shared variables and the maximality argument | Prove renaming compatibility and connect it to Proposition 4.2. |
| B Diagrams for three defining equations | Type and explain the three diagrams. |
| C Corrections to the cut-elimination argument used in Boolean Coherence | Identify the two published errors and give the rank inequalities. |
| D.1 Arrow terms and equations | Define terms, derivability, quotient arrows and term congruences. |
| D.2 Reading a Lean declaration | Explain declaration syntax and the mathematical steps of a proof. |
| D.3 The five declarations | Translate the registered entry points into mathematical statements. |
| D.4 Congruences on terms and on arrows | Explain their correspondence. |
| D.5 The proof of coherence | Explain the positive case, factorization and transfer to the original presentation. |
| E.1 The inverse of q_A; E.2 The inverse of e_A | Construct the inverse terms and verify the equations. |
| E.3 The split comparisons used in coherence | Construct the section/retraction and derive their equations. |
| Use of AI tools; references | Give the authorized disclosure and sources. |

The central result and its dependencies are unchanged: coherence and isolation
give K_A under substitution; the two isomorphisms or the mix argument then
give collapse. No reorganization is recommended.

## Findings at a glance

| Location | Issue | Basis | Recommended action |
| --- | --- | --- | --- |
| §1, p.1, lines 68–71 | “the equation of [1]” | The introduction does not identify the equation locally. | Point to K_A in §4 while retaining the attribution. |
| §1, p.1, lines 72–76 | “The two isomorphisms listed in [1]” | The paper later identifies the arrows in Lemma 5.1. | Point to that lemma while retaining the source citation. |
| §6, footnote 7, p.11, lines 887–889 | “these expressions” | The antecedent and domain of the two Lean maps are unstated. | Identify the laws in the normal-form presentation and the hom-set bijections. |
| D.4, p.18, lines 1454–1456 | “the substitution square” | The square has no local identifier in this sentence. | Specify D.1; this is optional navigation polish. |
| D.5, p.20, lines 1606–1614 | “atomic factorization” | “Atomic” is not explained for the displayed factorization. | State the typed existence assertion directly. |
| D.2, p.17, lines 1373–1374 | “These parameters supply ...” | The preceding sentences have just identified all those data and their roles. | Delete the recap; optional economy. |

The reference diagnoses concern identification and navigation, not broken
LaTeX references or false citations. All 83 `ref`/`eqref` occurrences resolve
to the manuscript's 34 labels.

# (C) Minor issues

## C1. “Atomic factorization” is unexplained as a prose label

- **Anchor:** p.20, D.5, source lines 1606–1609: “For arbitrary terms
  f,g ... atomic factorization constructs formulas A',B', arrows ... and
  positive terms ...”.
- **Failure mode:** `missing_definition`; severity **minor**, local terminology.
- **Evidence:** `absence_in_text`. The paper defines positive terms at
  lines 1504–1506 and gives the factorization's typed properties at
  lines 1606–1617, but does not explain what “atomic” specifies in this
  construction. In particular, the displayed intermediate formulas and
  positive terms are not asserted to be atoms.
- **Source distinction:** inspection of `CommonAtomicFactorization.lean`
  confirms that the Lean construction collects variable-indexed eta/epsilon
  data and constructs positive middle terms. This gives a meaning to the
  source name. It does not supply the missing explanation in the prose.
  No claim is made that the phrase is absent from all mathematical literature.
- **Impact and repair:** the typed factorization is stated, so this is not
  a missing formal proof or a newly exhibited gap in coherence. Replace
  “atomic factorization constructs” by “there are”. In the next sentence,
  replace “It also gives injections” by “There are also injections”, so the
  deletion does not leave a pronoun without an antecedent. Retain both
  displays, their types and the linked Lean declaration unchanged.
- **Rationale:** this applies Knuth–Larrabee–Roberts,
  [Mathematical Writing, §1, point 26](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf),
  on unnecessary jargon. It does not require renaming an immutable Lean
  identifier or introducing a new technical term.

## C2. A recap after the Lean proof table adds no new information

- **Anchor:** p.17, D.2, source lines 1373–1374:
  “These parameters supply the structures and equations used in the four
  steps above.”
- **Severity:** **minor, optional editorial deletion**; no mathematical
  failure is alleged.
- **Evidence:** `structural_argument`. Lines 1365–1372 have just identified
  the induced relation, interpretation, normalization, substitution and
  double-negation data and connected them to the proof. The final sentence
  restates their collective role without adding a map, law or correspondence.
- **Repair:** delete that sentence. Keep the table and the preceding
  explanation of each parameter: those provide the requested bridge to Lean.
  This is an independent economy judgment, not a claimed prohibition in KLR.

# (D) Cross-section consistency failures

## D1. The introduction points to an external equation without identifying it

- **Anchor:** p.1, §1, source lines 68–71: “give the equation of [1, §9.7,
  pp.215–216] ... then give this equation for every formula”.
- **Failure mode:** `ambiguous`; severity **minor**, local identification.
- **Evidence:** `absence_in_text`. The introduction does not identify which
  equation is meant. Section 4, lines 486–496, does: K_A, with the same source
  attribution. A reader can find the explanation later, but the introductory
  sentence gives only the external location.
- **Repair:** write “give equation (K_A) of Section 4”, retaining the source
  citation. This adds a local reference, not an elementary paraphrase of the
  theorem or a new introductory display.
- **Impact:** navigation and intelligibility of the proof outline; no false
  source attribution is established.

## D2. The introduction leaves the two isomorphisms as an external pointer

- **Anchor:** p.1, §1, source lines 72–76: “The two isomorphisms listed in
  [1, §12.5, p.294] give equality of the product projections.”
- **Failure mode:** `ambiguous`; severity **minor**, local identification.
- **Evidence:** `absence_in_text`. The sentence does not name the two arrows
  or their types. Lemma 5.1 supplies both arrows, their types and the deduction
  that they are isomorphisms. The introductory citation can remain, but it
  should not substitute for a reference to that local statement.
- **Repair:** begin “The isomorphisms of Lemma 5.1 ...”, retaining the source
  citation. Neither the abstract nor the introduction needs another display.
- **Impact:** identification of a proof input, with no change to Lemma 5.1.

## D3. “These expressions” does not identify the domain of the Lean maps

- **Anchor:** p.11, §6, footnote 7, source lines 887–889:
  “The maps ... reduceHom and ... recoverHom identify these expressions
  with arrows of B(P) and are inverse on each hom-set.”
- **Failure mode:** `ambiguous`; severity **minor**.
- **Evidence:** `absence_in_text` and selected source inspection. The main
  text already states the union formulas for arrows of B(P). The footnote
  lists Lean declarations in `Reduced` but does not identify the hom-sets
  on the other side of the correspondence. `ReducedQuotientReduction.lean`
  and `ReducedRecovery.lean` give the signatures and inverse laws: arrows
  A -> C in the original presentation correspond to arrows A-circle ->
  C-circle in the negation-normal-form presentation.
- **Repair:** after the declaration list, state:
  “These Lean laws are stated for arrows in the presentation on negation
  normal forms. The mutually inverse hom-set maps reduceHom and recoverHom
  transfer them to B(P).” Keep the existing declaration links.
- **Impact:** this repairs the translation between the two presentations.
  It does not question the proved inverse equations. This is additional to
  the previously reported D.5 reference to “recovery maps of Section 3”.

## D4. “The substitution square” could identify its subsection

- **Anchor:** p.18, D.4, source lines 1454–1456: “the substitution square
  with Q=P shows that they are preserved by F_sigma”.
- **Failure mode:** `ambiguous`; severity **minor, optional navigation polish**.
- **Evidence:** `absence_in_text`. D.1 contains the intended square between
  terms, quotient arrows and their substitutions, at lines 1242–1252.
  The sentence in D.4 does not name that location; §3 also contains a square
  relating substituted arrows and occurrence relations.
- **Repair:** “the substitution square in Appendix D.1, with Q=P ...”.
- **Impact:** a more precise pointer. The intended inference is recoverable
  and is not a mathematical gap.

## Definitions and qualifications that should remain

“Positive” is defined before its use in D.5. The canonical comparison arrows
are given by explicit product/copairing formulas. “Natural” refers to
naturality of specified maps. The empty-hom-set conditions, sign conditions,
and distinction between retractions and isomorphisms have mathematical
content. They are not empty qualifiers. The sentence that both inverse
constructions cover empty occurrence sets is also mathematically meaningful;
it is not counted as a weasel phrase.

No “genuine”, “actual”, “obvious”, “clearly”, “essentially”, “merely”,
“straightforward”, “remarkable” or “interesting” remains as a prose qualifier
in the reviewed source. “Structural” occurs only in unprinted reference
keys. “Raw” occurs in an exact Lean identifier. The authorized AI disclosure
and mathematical explanations of Lean syntax are not editorial clutter.

# (E) Acceptance conditions, non-negotiable

No new mathematical acceptance condition is established. These are local
prose and reference recommendations. C2 and D4 are optional polish; C1 and
D1–D3 would improve the identification of the mathematics being discussed.
No result needs to be dropped because of these findings.

Any future implementation should preserve the theorem statements, displayed
equations, hypotheses, exact source links, accepted abstract and intended
level of exposition. The new report does not authorize a manuscript revision.

# (F) Not checked / uncertainty log

The entire 1,781-line v23 source was reread in order for this focused pass,
including footnotes and appendices. Search results were checked against
their surrounding paragraphs. The PDF's extracted text was used to verify
the page anchors. Layout and compilation were not repeated in this pass;
the previous v23 PDF review and successful release checks remain applicable.

The retained KLR text was consulted directly, including §1, points 10–17
and 26. Its advice to explain concepts and use complementary formulations
does not imply deleting every repetition. C2 is a judgment about one recap
that adds no complementary information. No new factual literature claim or
priority claim is made; bibliographic sources were not re-audited.

The selected source checks were the definitions and inverse laws for
reduceHom/recoverHom and the data in CommonAtomicFactorization. No Lean
build, kernel replay, Comparator, Palomar action or arXiv upload was performed.
No new whole-development formal audit is claimed.

Retained report: `docs/reviews/V23_PROSE_REFERENCE_AUDIT_2026-11-02.md`.
Downloads target:
`/mnt/c/Users/fleng/Downloads/Dosen-Petric-V23-Review-20261102/V23_PROSE_REFERENCE_AUDIT_2026-11-02.md`.
Delivery is from committed bytes with byte/SHA-256 verification and a separate
receipt; conflicting existing files are preserved. The manuscript source and
PDF retain the hashes stated in A. Only this report and its receipt are added.

Strongest confirmed blocker: **none**.
Strongest suspected unconfirmed blocker: **none supported by this pass**.
Most important unchecked item: no new transitive audit of Lean proof dependencies.
No recommendation here depends on unavailable material.
Final formal referee recommendation: **unknown**; this is a prose audit.
