# V13 hostile mathematical review

31 October 2026. Author-side AI-assisted audit, not an independent journal
referee report. Genre: research article with a registered formalization.
Axes examined: correctness, stated hypotheses, exposition, source comparisons
and reproducibility claims. Input: v12 at
`cbcd59ca1b9382bdcd0de8c648e4a351495ccf81`; corrections implemented in v13.

## (A) Kill-shots / hard blockers

No fatal mathematical blocker was established. The maximality theorem, both
collapse routes, universal-model corollary and occurrence-coordinate constructions
were checked as recorded in the [statement review](V13_STATEMENT_REVIEW_2026-10-31.md).
The seven numbered statements have the same text in v12 and v13.

This conclusion is limited to the manuscript and the source inspection
performed. Registration and a successful build do not by themselves certify
the English exposition or exclude an earlier result in the literature.

## (B) Major weaknesses

No major mathematical weakness was established in this pass. In particular:

- The isolation proof uses the same signed literal at both ends of the chosen
  edge. Its negative case substitutes ¬A and transports the double negation.
- Coherence is applied in the original category. The quotient argument uses
  descended product/coproduct equations and retained inverse equations.
- A zero arrow requires an existing-arrow witness. No empty hom-set is filled.
- The model corollary quantifies over all interpretations and uses target
  pairing; it does not assume substitution closure of a single kernel or
  surjectivity of a functor on target arrows.
- The q/e proof and the alternative symmetric-fold proof have separate checked
  deductions and source correspondences.

## (C) Minor issues

### C1. The scope of the cited occurrence-selection lemma was overstated

- **Anchor:** v12 §1, source lines 79–81, the sentence describing Lemma 6 of
  *Isomorphic formulae*; exact replacement L3 in the editorial record.
- **Claim as written:** tautologicity of A→B and prescribed occurrences of the
  same variable suffice for the stated one-edge arrow.
- **Failure mode:** misuse_of_prior_work; false under the unrestricted reading.
- **Why:** the cited lemma restricts A and B to formulas without negation.
- **Evidence:** citation and counterexample. Take A=p, B=¬p∨p and select the
  negative target occurrence. A→B is tautological, but signed-label preservation
  excludes the requested edge. This is a small example; minimality is unproved.
- **Impact:** introductory account of prior work. Lemma 4.1 already enforces
  signed-label equality, and the q/e application is negation-free.
- **Severity and repair:** minor, local and repaired in v13 by adding the exact
  hypothesis. The previous v12 audit missed this qualification.

### C2. Close maximality antecedents were omitted

- **Anchor:** v12 §1, lines 70–85, the paragraphs on cartesian, lattice and
  relational maximality.
- **Claim as written:** a selection of antecedents, with no claim of an exhaustive
  survey.
- **Failure mode:** ambiguous positioning by omission, not a false novelty claim.
- **Evidence:** citation. DP's CCC maximality §11 and their zero-identity
  distributive results at book p.292 are close comparisons absent from that list.
- **Impact:** the introduction did not explain the most relevant additional
  antecedents or why CCC maximality cannot simply be applied to B.
- **Severity and repair:** minor; v13 adds both comparisons, states the absence
  of p⇒p, and also identifies the graph category in their proof-net coherence
  result. No unproved generalization claim is introduced.

### C3. Two source summaries were too compressed

- **Anchor:** v12 §1 lines 92–94 (“ordered soundness and completeness”) and §3
  lines 276–281 (the Joyal comparison).
- **Claim as written:** FP has ordered soundness/completeness; Joyal's result
  concerns cartesian closed categories with a dualizing object.
- **Failure mode:** ambiguous exposition, not an established false theorem.
- **Evidence:** citation. FP Theorems 6.4–6.5 quantify over inequalities and all
  interpretations of a net theory. DP p.324 gives the initial-object and
  double-negation exponential condition.
- **Impact:** the reader had to consult the sources to identify the exact
  conditions relevant to the comparison.
- **Severity and repair:** minor; v13 states both assertions explicitly.

### C4. The alternative collapse proof omitted its intermediate deductions

- **Anchor:** v12 §6, lines 614–617, ending with the claim that fold symmetry and
  the first-injection equation yield contextual collapse.
- **Claim as written:** the displayed facts suffice for collapse.
- **Failure mode:** unproved in that compressed paragraph; the main q/e proof
  already supplies a complete independent proof of collapse.
- **Evidence:** absence_in_text and derivation. The paragraph did not display
  jh≡jπ₂, equality of the injected projections, j≡ι₂!, or h≡π₁. These deductions
  are present in the existing ContextualCollapse source.
- **Impact:** readers could not follow the alternative route from that paragraph
  without reconstructing it or consulting Lean. The main theorem was unaffected.
- **Severity and repair:** minor in this article's organization; v13 supplies
  the intermediate equations and their reasons. No Lean proof was modified.

### C5. Three local descriptions could be made definite

- **Anchor:** v12 Appendix A lines 728–731, 779–782 and 828–837.
- **Claim as written:** the label is described emphatically; a skeleton is
  mentioned without naming the substituted pattern; the positive contextual
  case is introduced before the negative case without an explicit condition.
- **Failure mode:** ambiguous or redundant exposition.
- **Evidence:** absence_in_text plus the surrounding definitions. The required
  label is γ(r,t), the required skeleton is that of M[Φ₀], and the first branch
  assumes the isolated literal is p.
- **Impact:** local clarity only. The coordinate and negative-literal proofs
  already specify the correct constructions.
- **Severity and repair:** minor; v13 makes those three descriptions explicit
  and shortens the redundant Appendix B announcement.

## (D) Cross-section consistency failures

The C1 literature sentence was less restrictive than the signed-literal
condition in the manuscript's own proof. V13 resolves this by stating the
source lemma's negation-free hypothesis. C5's two contextual cases now match
the case split in Proposition 4.2 exactly.

No other drift was established in source/target types, variance, equality,
nonempty P, occurrence tags, empty blocks or the quantified model class.
The [definition/type ledger](V13_STATEMENT_REVIEW_2026-10-31.md) and the
complete claim map record the checks. “Structural induction” in Appendix A
denotes induction on the formula grammar; it is retained for that precise use.

The prior concern about missing typing in the formalization is not supported
by the inspected source. Pairing and copairing were already indexed by their
source and target in the registered syntax. The v12 and v13 prose changes do
not repair an ill-typed Lean declaration. No formal typing defect was found.

## (E) Acceptance conditions, non-negotiable

These are endpoints for closing this author-side revision, not a publication
acceptance verdict. Each is satisfied by the v13 artifacts and validation
record, subject to the stated scope.

| Condition | Deliverable and verifiable endpoint | Consequence if unmet |
| --- | --- | --- |
| Correct source scope | V13 §1 explicitly restricts Lemma 6 to negation-free formulas; exact source locator retained. | Reject the unrestricted literature assertion; remove or qualify it. |
| Explain close antecedents | Introduction and literature report distinguish cartesian, CCC, zero-identity distributive, Boolean and relational presentations. | Drop unsupported transfer/generalization or priority claims. |
| Make the second collapse route readable | §6 includes jh≡jπ₂, j≡ι₂!, h≡π₁ and equality of projections, with reasons and existing Lean correspondence. | Do not claim the paragraph presents the full alternative deduction. |
| Preserve and check the central argument | Statement ledger covers all seven statements and every unnumbered construction, including negative literals, witnessed zeros and all interpretations. | Reject any mathematical claim whose required hypothesis or deduction fails. |
| Keep registration scope exact | Five declaration descriptions match comparator.json; immutable proof commit and supplied BibTeX preserved. | Drop unsupported formalization/registration claims. |
| Deliver a reproducible manuscript package | TeX/PDF/BBL, four-member archive, independent extracted build, matching text/bibliography, resolved references and full-page visual inspection. | Do not call the upload package validated. |
| Preserve history and report delivery honestly | V12 and earlier files remain; new reports retained in repository; unavailable Windows copy explicitly reported. | Do not claim a preserved release or completed Downloads delivery without evidence. |

## (F) Not checked / uncertainty log

- No fresh Lean build, kernel replay, transitive axiom audit, Comparator run or
  Palomar registration was performed. Existing evidence is tied to its recorded
  commits. Relevant source declarations were read to check correspondence.
- The literature search cannot prove absence of an earlier result. Several
  peripheral works were inspected only at abstract or introductory level; the
  literature report identifies each such limit.
- No independent human referee or publication-value assessment was obtained.
  This is an author-side review using the requested tools.
- Windows Downloads and the author's WSL checkout are unavailable here. New
  report copies there have not been made or verified.

**Final self-audit.** Strongest confirmed finding: C1, the omitted negation-free
condition, now corrected; no central mathematical blocker was confirmed.
Strongest suspected but unconfirmed blocker: no specific one established;
unexamined literature may affect priority, but that possibility is not evidence
of a duplicate result. Most important unchecked work: an independent replay of
the whole formal development and an exhaustive priority assessment. The
manuscript correction does not depend on unavailable material; a publication
verdict would require evaluation beyond this audit. **Final recommendation:
unknown.** This is not a finding that the formal proof is wrong.
