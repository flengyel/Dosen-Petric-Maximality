# Author-side writing review — binary-input Reducibility integration

Latest upstream integration (edb86cb): retain the author's division of work,
correction procedure and tagged-substitution requirements. The new W6 analysis
is an instruction at its historical source anchor. The two-premise terminal-
source left family and all native binary producers compile here; the general
one-premise terminal-source left displayed families/ranks in its §3 remain
open as separately specified source constructions. Native one-premise repairs
and source singleton blockedness exclusions do not discharge those exact
source-rank statements. See the current continuation. No manuscript defect or
completed full-paper proof is inferred.

Upstream integration: accepted commits 0af6a0e, 810dcdb and e4f2f0b after
the checked proof commit f4bc6ff. They add manuscript v6 and the full-paper
contract, with no Lean-source changes. The current manuscript is v6; upstream
v5/v6 files are retained byte-for-byte, and v4 remains preserved. Both full
Reducibility and the broader v6 contract remain incomplete. The supplied
1e967bc instruction remains the exact immediate proof target.

The current report explains the binary-input results while retaining the
unproved full target. Its opening states that limitation. This is an author-side
editorial review of the integration report, current maps, continuation and
mathematical documentation of the new proofs. It is not independent certification
of correctness or a whole-manuscript review. No manuscript prose or source
comment was revised.

Governing source: Donald E. Knuth, Tracy Larrabee and Paul M. Roberts,
*Mathematical Writing*, verified course-report cache
`.codex-work/references/knuth-mathematical-writing-mit-9bf404c2.pdf`, SHA-256
`9bf404c2c75633a1f39aae97af0b2e9335ce6d83cf386c84906654589b4e82e6`.
Access succeeded; this review is source-grounded. Historical access failures
and provisional reports are preserved as historical records. Consulted §1,
especially points 5,10–15,17,24,26, and §4, printed p.9. The workflow and
judgments below are this review's application, not a format attributed to KLR.

## Actual outline and mathematical function

The report's existing sections are:

1. **Status and scope:** distinguish the requested full result from the proved
   binary-input result and identify the starting source state.
2. **Exact proved endpoints and hypotheses:** give typed producer signatures,
   expand ReducesL/R, and locate the main declarations.
3. **Published-source correspondence:** connect W1/W4/W5/W6 and source macro
   order to typed Lean constructions and state the unproved scope.
4. **Construction and rank checks:** explain indexed splitting, singleton-aware
   contraction, actual rank formulas and the blocked-middle bound.
5. **Verification results:** report commands, exits, measured counts, five
   actual negative-control rejections and unperformed checks.
6. **Evidence and immutable-source correspondence:** locate hashes, public
   types, logs, supplied originals and committed-byte checks.
7. **Remaining obligations and precise next theorem:** give the unrestricted
   exchange types and explain exactly why fixed-gap results do not supply them.
8. **Preservation, reviews and delivery:** state retained mathematical boundaries
   and the report/ref/byte verification procedure.

The central proved result is the pair BinaryReducer.left/right. Their
prerequisites are joint indexed selection splitting, actual categorical
naturality/component laws, the source blocked patterns, singleton-aware
operations, and the existing entry-uniqueness/ContractionBound infrastructure.
The full Reducibility statements require further unary constructions. That
logical distinction is the report's organizing question. No replacement
outline is needed: types precede rank formulas and verification follows the
mathematical claims.

## Comparison with the governing source

| Location | Issue checked | Source principle or independent rationale | Applied action |
| --- | --- | --- | --- |
| Report §§1–2; BinaryReducer public types | A restricted theorem can sound like the full theorem when its hypothesis is omitted. | KLR §1 point 5: theorem statements should carry their own assumptions. | State Binary and arity explicitly; expand the complete replacement quantifier and identify its address dependencies. |
| Report §4, W4 and W6 rank paragraphs | A list of unexplained formulas would conceal which syntactic proof is ranked. | KLR §1 points 10–11: connect formulas in prose and explain definitions in complementary ways. | Define n,m,S,δ before use; explain singleton/node counting and source/native differences. |
| Opening and report §7 | The next missing construction must be visible before a long dependency inventory. | KLR §1 points 12–13,24: reader motivation, readable prose around formulas and a direct opening. | Lead with noncompletion and proved binary coverage; give exact unrestricted exchange types as the next obligation. |
| Source correspondence and new terminal/native modules | “Inner”, “head”, “terminal” and “left” depend on conventions. | KLR §1 point 14; explicit typing is an independent editorial requirement. | Fix left-first composition; distinguish product precomposition from coproduct postcomposition and source macros from primitive proof constructors. |
| Module/declaration inventory | Repeated indices can obscure independent selections. | KLR §1 point 15: avoid needless indexed notation. | Use p,q and independent arities n,m, with file/line inventories for implementation detail. |
| Definition order | Informal previews need not contain every implementation detail. | KLR §4 printed p.9 treats definition placement contextually. | Keep the opening concise; define Reduces and selection data before using their exact formulas. |
| Current records versus historical records | An old label “current” can contradict the new scope. | Independent editorial consistency check. | Mark earlier checkpoint sections historical, archive the old continuation, and link the exact supplied 1e967bc instruction. |

These source principles are paraphrased; no invented quotation or rule number
is used. The remaining scope/evidence judgments are editorial applications.

## Definition-order and notation audit

- `Reduced.Hom`, the syntactic equality notion and left-first `comp` are stated
  before the producer signatures. Equality is not defined by an interpretation.
- `ContractionBlock` and its retained typed position are described before their
  use. Complete selected-copy lists and repeated tags are retained.
- `ReducesL/R` are explicitly definitions of the target, followed by declarations
  proving them for binary inputs. The report does not count a definition as a
  solution of the general problem.
- `Binary` is enumerated; the cut case is rejected through the existing
  reducibility hypothesis. The general theorem has no extra CutFree/Atomized,
  injectivity, nonempty-variable or coherence assumption.
- “Two copies” now means two parametric copies only where that is the actual
  hypothesis. The one-parametric-plus-fresh case is separately named and has
  the formula S+3, not a transplanted formula requiring an inner node.
- δ(n) and S are defined before the rank calculations. The source and native S
  use their stated premise coordinates. Rank belongs to syntactic proof
  occurrences, not Reduced equality classes.
- Source singleton exclusions concern actual terminal source macro terms.
  Their conclusion is blockedness, not a reducible native example. The
  source/native denotation comparison is never described as syntax identity.
- Whole-formula ancestry and tagged literal-occurrence relations are kept
  separate. Constants remain whole-formula positions even when their literal
  occurrence types are empty.

No confirmed missing definition in the reviewed current report needs a new
section. Basic category/Lean notation is addressed at the intended technical
level; the report is not expanded into a tutorial.

## Prioritized edits and retained wording

1. Retain the exact opening: **“Both full Reducibility Lemmata remain open.”**
   It prevents build success from being read as proof of the requested endpoint.
2. Retain the sentence: **“The binary theorem's Binary premise is a scope
   restriction; it has not been silently removed to claim the full lemma.”**
   The actual signatures substantiate this limitation.
3. Use **“one parametric copy plus the fresh compound”** for the new smallest
   right-W4 case. Use **“two parametric copies plus the fresh compound”** for
   the older lower-bound-two statement.
4. Use **“The obstruction is a missing formal construction; no mathematical
   impossibility or defect of the published lemma is asserted.”** This is an
   implementation-status statement outside manuscript prose.
5. Keep the large source/declaration inventory in provenance rather than
   burying the report's main mathematical endpoint in a list of filenames.

No stylistic change weakens a quantified conclusion or turns an open statement
into an axiom. The hostile review's unproved-endpoint finding is mathematical
scope, not an editorial defect repaired by more favorable language.

## Scope and delivery

Reviewed: actual new theorem statements/proof boundaries, the report outline,
current correspondence/maps/validation/continuation and relevant README links.
The pinned Došen–Petrić source and rendered p.252 support the local source
correspondence; no new literature/novelty claim is made. Lean strict verification,
public exported-type queries and the five negative controls passed for the
recorded inventory. The complete v6 TeX source, including both appendices, was read to understand
the upstream contract; no whole-paper mathematical review or new rendering, independent referee
certification or external Palomar verification was performed. The accepted v6/v5/v4 manuscript state
is preserved. Reviews and process commentary remain in separate reports.

Repository copies and verified conflict-preserving Downloads copies are part
of delivery. This review does not certify either missing full Reducibility
Lemma, Blocked-w, cut elimination, coherence or unconditional maximality.
