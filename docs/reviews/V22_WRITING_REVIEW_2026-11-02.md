# Focused mathematical-writing review: v22

2 November 2026. Author-side AI-assisted review under the mathematical-writing
skill. Input v21 at 16e604e21a1b5505758b8b719ba879791ae9e699. Output v22.
The abstract now introduces the formalization as a formalization of the paper's
proofs and their dependencies. This resolves the author's stated ambiguity.

## Source and actual outline

Knuth–Larrabee–Roberts,
[Mathematical Writing](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf),
§1 points 10–13 were consulted in the retained retypeset text: connect the
exposition, introduce its referents and account for what the reader knows.
The exact replacement is the author's accepted wording, not a quotation from
the book. The earlier official-PDF abstract consultation remains applicable.

The unchanged order is abstract (result/method/scope), §1 problem/literature,
§2 category/congruences/theorem, §3 occurrences/coherence/substitution, §4
isolation/all contexts, §5 q/e collapse/models, §6 formalization/fold/union;
A.1–A.3 occurrence maps, ordinals and shared variables; B defining diagrams;
C source corrections; D.1–D.5 terms, reading Lean, selected theorems,
congruence correspondence and coherence; E.1–E.3 q/e inverses and split
comparisons; disclosure and references. No reorganization is proposed.
The main result and its coherence, isolation and substitution inputs remain.

| Anchor | Issue | Rationale | Repair |
| --- | --- | --- | --- |
| Abstract p.1 final two sentences | “The Lean formalization” has no introduced referent and suggests the proofs belong only to Lean. | Connected exposition and author's explicit diagnosis. | Introduce a formalization of these proofs and their dependencies; then identify what it includes. |

The [release report](../MANUSCRIPT_V22_REPORT.md) gives the exact replacement.
The earlier “We prove ...” statements identify the written proofs; “We also
give ...” introduces the formalization. Boolean Coherence is already named in
the proof summary. The model corollary retains every interpretation, and the
occurrence/ordinal correspondence retains both constructions. No new symbol,
type, quantifier, dependency assumption or mathematical claim is introduced.

Only this abstract tail and version suffixes change. Restoring them recovers
v21 byte for byte, so the body and its previous paragraph-function classifications
remain. The revised paragraph states results, summarizes the proof and identifies
its formalization. No editorial process narration is added to the manuscript.

Both builds pass with matching 23-page layout text and no final warnings.
Changed pages 1–14 were viewed on four contact sheets; p.1 individually.
Pages 15–23 match v21 in text and coordinates. This focused prose and
correspondence review is not a new independent mathematical, novelty or hostile
review. Proof/kernel/Palomar checks and registration are reused.

Retained: docs/reviews/V22_WRITING_REVIEW_2026-11-02.md.
Delivered: /mnt/c/Users/fleng/Downloads/Dosen-Petric-Manuscript-v22-20261102/V22_WRITING_REVIEW_2026-11-02.md.
The receipt records verification from committed bytes.
