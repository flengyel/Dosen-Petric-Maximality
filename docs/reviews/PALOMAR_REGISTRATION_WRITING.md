# Palomar registration package: mathematical-writing review

The selected mathematics is explicit and the raw/quotient relation is explained
before the result table. The new account distinguishes the two collapse proofs
and the intended full congruence relation without changing manuscript v8. The
public description separates the selected family from the retained complete
formalization and local verification from later service stages.

This is a local AI-assisted author-side review under the Mathematical Writing
skill, not external human peer review or a Palomar editorial decision. Scope:
the complete new Challenge, three new production modules, the correspondence
account, root metadata, current README and registration reports. The unchanged
manuscript is preserved rather than claimed as a newly rewritten document.

The governing source consulted was Donald E. Knuth, Tracy Larrabee and Paul M.
Roberts, [Mathematical Writing](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf).
The complete cached PDF has SHA-256
`9bf404c2c75633a1f39aae97af0b2e9335ce6d83cf386c84906654589b4e82e6`.
Section 1, especially points 5 and 10–17, and the contextual discussions in
Sections 4–5 were consulted. Locations below refer to printed sections/pages,
not invented PDF line numbers. The report format and economy/process-separation
requirements are the skill's supplementary editorial method; they are not
attributed to the book.

## Current outline and functions

1. Challenge introduction: actual presentation and composition convention.
2. Formula and occurrence/substitution definitions: objects, tagged positions
   and the operation on formulas.
3. Op and Term: actual typed primitive grammar and derived term macros.
4. Constant, Equation and Derives: positive constant side condition, generating
   schemas and generated equality.
5. Whole-arrow substitution and PrimitiveCongruence/Closed/Total: the precise
   relations and endosubstitution action.
6. Five formal theorem statements: the two maximality routes, dichotomy,
   nonzero identity and empty hom-set.
7. `PALOMAR_STATEMENT_CORRESPONDENCE.md`: definitions, descent/restriction and
   pointwise inverses, then the five-result table and its scope.
8. `formalization.yaml`: mathematical description, source attribution,
   classification, scope, AI role disclosure, fidelity and declaration alignment.
9. Separate registration report/status/reviews: verification, provenance,
   diagnostics, release decision and delivery; these are outside the manuscript.

The central result identifies every closed primitive congruence with generated
equality or hom-wise totality on the actual arrow grammar. The two structural
witnesses explain the nonthin/empty-hom setting. Quotient descent, substitution
closure, source isolation and collapse are the relevant prerequisites. The
existing organization preserves this dependency order; no alternative outline
is warranted.

## Comparison and repairs

| Anchor | Actual issue or check | Verified principle or independent rationale | Action/result |
| --- | --- | --- | --- |
| Challenge's five theorem types | Every hypothesis must remain visible in the declaration's complete type. | KLR §1 point 5, printed p.2, recommends self-contained theorem statements. | Universe/type parameters, closedness, nonderivability and relation hypotheses are explicit; exact comparison passes. |
| Correspondence account, opening and descent section | Raw syntax, generated equality and quotient equality must remain distinct. | KLR §1 points 10–11, printed p.2: connected exposition and complementary descriptions. | Define the grammar/equality first, then state the quotient relation and its proof. Preserve the separate pointwise relation correspondences. |
| Whole-arrow substitution and `Closed` | A reader must know that term and endpoint formulas are substituted together. | KLR §1 points 14–15 and §5, printed p.12, on notation and nearby definitions. | `σ : P→Formula P` and the typed `Term.subst` action precede `Closed`; prose explains both endpoint formulas. |
| Composition in Challenge/statement account | Operational order differs from manuscript composition notation. | Independent typing/notation rationale, supported by KLR §1 notation guidance. | Retain “composition applies its first argument first” and the explicit `f:A→B`, `g:B→C` explanation. Constructor endpoints and source correspondence agree. |
| Metadata's nonempty-variable hypothesis | The public wrapper retains a hypothesis unused by the stronger production theorem. | Independent fidelity rationale; no general ban on unused hypotheses is attributed to KLR. | Explain intentional specialization to printed Theorem 2.1. The identity witness and empty-hom theorem state their distinct hypotheses. |
| `PalomarCorrespondence.full` docstring | An early draft narrated the checking sequence and a later proof. | Supplementary skill requirement: keep process commentary outside mathematical prose. | Replace with the mathematical statement that a closed primitive congruence extends to a full proof congruence while preserving its relation. Proof-route reporting stays in the separate report. |
| Challenge introduction | An early draft appended reassurance that all definitions were concrete. | Supplementary economy rule, independent of a quoted KLR rule. | Remove the redundant sentence; the actual definitions express the content directly. |
| Metadata classification | The proposal's MSC list differed from the manuscript. | Independent bibliographic consistency rationale. | Use the manuscript's `03G30`, `03F07`, `18A32`; official taxonomy validation passes. No manuscript change. |
| README/status versus retained historical reports | New local kernel results must not retroactively change old checkpoint claims. | Independent temporal/provenance consistency rationale. | Add a dated current registration section; retain historical reports and the preceding continuation unchanged in history. |
| Whole new account | Tables should serve genuinely parallel comparisons; prose should explain inferences. | KLR §1 points 10–13, printed pp.2–3. | Keep the five-result table; explain descent and inverse relation laws in connected paragraphs. No gratuitous diagram was added. |

## Definition order, notation and economy

`Formula P`, `Term P A B`, composition, `Equation`, and `Derives` precede the
primitive congruence. Substitution on formulas and whole arrows precedes
`Closed`. `Total` quantifies over existing parallel terms, so it cannot be read
as asserting existence of arrows in empty hom-sets. The quotient account states
the map `ofTerm` and both source/target types before using distinctness. The
relation-level inverse claims are distinguished from equality of structure data.

The meaning of `Constant` remains the inherited positive letterless grammar;
formula negation and derived arrow negation are introduced in their respective
roles. Tagged sums preserve repeated occurrences, and `Empty` is retained at
top/bottom. No labels, endpoint types, quantifiers or converse directions were
removed for brevity. The five complete formal types also remain the authoritative
unambiguous statement of each selected result.

Section 4 of KLR, printed p.9, explicitly allows context-sensitive placement of
some definitions; Section 5, printed p.12, advises defining symbols before or
near their use. These were applied with judgment, not as a demand for a separate
dictionary before every familiar categorical term. The account introduces the
paper-specific raw relation and closure precisely where needed.

A continuous prose pass of the new mathematical account and docstrings retained
paragraphs that define objects, explain descent, prove a correspondence or
state its scope. Redundant reassurance and checking-process narration were
removed as recorded above. Verification histories and delivery details remain
in process reports, not the manuscript or theorem prose. The excerpted source
anchors and the positive-constant distinction remain because they identify
which generating presentation is formalized.

## Priority and verification scope

The required local repairs above are applied. No further manuscript revision is
justified by an exhibited defect in this packaging work. No replacement theorem
wording or alternative outline is needed after the corrections. Preserve the
complete finite presentation even though the Challenge exceeds the 300-line
warning: compressing its equations into opaque interfaces would make the
mathematics harder to inspect.

The exact Challenge and production wrappers compile; public Comparator,
extended type/value audit, proof-route checks, Lean, NanoDa and authenticated
con-ron pass. These checks substantiate formal fidelity, not a claim of human
mathematical certification. No TeX rebuild or PDF visual reinspection is claimed
for this stage: all 11 manuscript files are byte-identical, and the new reviewed
material is Lean/Markdown/YAML. Prior full-paper cloud reviews remain separately
attributed. Official full preflight, service editorial outcome and exhaustive
novelty assessment remain unperformed.
