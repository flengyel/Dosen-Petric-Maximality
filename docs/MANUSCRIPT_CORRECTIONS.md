# Manuscript corrections and unresolved findings

Current manuscript: v6, source commit
`810dcdbccc76a4307028773c561f36b910b5170c`, SHA-256
`2c30fd10cb81f5d8246dabdc7f343d6d9adeac91358d84273d2799ab514972b0`.
Record established: 25 October 2026.

## Current correction status

No outstanding confirmed manuscript correction is recorded in the completed
[v6 hostile review](reviews/V6_HOSTILE_REVIEW.md) or
[v6 writing review](reviews/V6_WRITING_REVIEW.md). The writing review's local
recommendation to remove the final repetitive sentence of §6 was applied and
confirmed in the committed v6 source.

The [focused occurrence-substitution check](reviews/OCCURRENCE_SUBSTITUTION_FOLLOWUP.md)
compared Appendix A and its uses in §§3–4 with the published formula. It found
no necessary correction in those passages. That focused result does not expand
the review scope to an independent reproof of the whole paper or its sources.

| Confirmed unresolved defect | Anchor | Evidence | Required repair | Status |
|---|---|---|---|---|
| None recorded at this checkpoint | v6 reviews and focused check above | See linked review scopes | No manuscript edit is required by these findings | No open confirmed correction recorded |

## Proof obligations are tracked separately

General Reducibility, Boolean Coherence for the actual source quotient, the
short proof's Lean implementation, actual-presentation maximality, the model
corollary and remaining appendix correspondences are unfinished formalization
obligations. Their open status alone is not evidence of an error in the written
mathematics. Track exact hypotheses and implementation status in
[the statement map](MANUSCRIPT_STATEMENTS.md) and
[coverage map](MANUSCRIPT_COVERAGE.md).

## Accepted workflow clarification: 25 October 2026

Category: author instruction about division of work, not a mathematical defect.
The author specified that local Codex performs implementation/builds and
ChatGPT provides instructions, review, mathematical/literature assistance,
manuscript checks and arXiv/Palomar preparation. Cloud source compilation is
unnecessary. The current W6 construction instructions, AGENTS, full-paper
contract and continuation now record that division. Local verification and
the existing publication/submission authorization boundaries are unchanged.

The W6 construction analysis records proposed equations as local-Codex proof
targets; the README and all three status/correspondence maps retain their open
status. No production Lean file or manuscript was revised. No confirmed
manuscript error was found or inferred from these open obligations.

## Recording and resolving a correction

For each new finding, record its category (confirmed defect, suspected issue,
open proof obligation, or optional exposition), exact manuscript or Lean anchor,
claim as written, evidence, affected results and diagrams, and proposed repair.
Do not label a suspicion a confirmed error without evidence.

For a confirmed defect, record the corrected statement or construction, its
mathematical justification, the corresponding source and Lean edits, relevant
checks and the resolution commit. Preserve the original claim in history and
make any change of hypotheses or conclusions explicit. Update the source
anchor and affected claim-ledger entries. A claim with an unresolved confirmed
defect cannot be marked complete.

Keep review and repair records outside publication prose. Necessary mathematical
qualifications belong in the statements and arguments themselves.
