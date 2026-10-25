# Gentzen Reducibility follow-up

## Status and unchanged target

**The requested full Reducibility task is not complete. Both general
Reducibility Lemmata remain unproved.** This follow-up proves the entry
uniqueness inference, both addressed W4 cases, and both constructed
mixed-premise mix W5 cases with their complete post-replacement descendant
quantifiers. It also supplies positional extraction and native logical
comparison lemmas used toward the missing general producers. It does not
claim that these cases exhaust arbitrary ReducibleL/R data.

For arbitrary universe u, P : Type u, C : NormalForm P and contexts
Γ, Δ, Θ, Λ, U, V : List (NormalForm P), let
f : G P Γ (C::Δ), g : G P (C::Θ) Λ and w : G P U V.
The unchanged left target, from a : ProofAddress g w, x : At U C and
hr : ReducibleL f g a x, is an h : G P U V satisfying h.CutFree,
`ofTerm h.denote = ofTerm w.denote`, and, for every I J : List (NormalForm P),
v : G P I J, b : ProofAddress h v and y : At I C,

```text
ReducibleL f (a.replace h) ((a.inserted h).append b) y →
  v.rho .left y < w.rho .left x.
```

The separately typed right target has a : ProofAddress f w, x : At V C,
hr : ReducibleR f g a x, y : At J C and concludes
`ReducibleR (a.replace h) g ((a.inserted h).append b) y → v.rho .right y < w.rho .right x`.
No caller-supplied reduct, injectivity, coherence or rank conclusion may be
added. The earlier report's I,J,v binders are corrected; its historical
mathematical scope and evidence remain preserved.

## Baseline and preservation

Base and fetched SSH origin were 05c6bc8a86126fde494a9c9f2b42e693687b76d6,
whose retained strict receipt records 224 files / 8,602 declarations. That is
a historical baseline receipt, not a new clean-baseline run in this follow-up.
The initial working tree was clean. A later fetch found no intervening commit.
The new source state has 249 files / 8,919 declarations. The stash
`dedfd8fc8cd49930e9a162d5be585215b062a43c` and the prior reconciliation
archive/alternate drafts are preserved. No reset, clean, stash drop, branch
replacement, dependency change or visibility operation was performed.

The supplied instruction and checkpoint review are retained under docs/ and
docs/reviews/ respectively. SUPPLIED_ORIGINALS.tar.gz preserves exact original
bytes; SUPPLIED_IMPORTS.json records EOF-only text-import normalization and
both hashes. The previous continuation is retained byte for byte in
`docs/history/CODEX_NEXT_SESSION_05C6BC8.txt`. Prior access records remain.

## Proved declarations and exact scope

All names below have prefix DosenPetric.Reduced.Gentzen. PUBLIC_TYPES.txt
retains the exact Lean types and universe parameters. No result below requires
Nonempty P, DecidableEq P, enumeration, freshness, or occurrence faithfulness.

| Declarations / modules | Hypotheses and proved conclusion |
| --- | --- |
| ProofAddress.separation_of_collision; GentzenEntrySeparation | Two distinct positions ascending to one selected root yield an actual typed address factorization at their first separating contraction of C on the specified side. |
| BlockedL/R.premise_frame; EntryFrame.source_disj_left/right | All seven left and seven right blocked patterns give premise entry frames. The actual disjLLast input/output exchanges are included, not erased. |
| ReducibleL/R.entry_unique | Reducibility alone forces any local C position ascending to the distinguished cut entry to equal the selected position. No global InjectiveAscend premise. |
| W4.SelectedLogical.addressed_left | For its terminal selected-conjunction data and n≥2, any actual containing address and ReducibleL yield the stated newL, cut-freeness, local/rebuilt Reduced equality and every eligible-descendant strict bound. |
| RightLogicalRegression | P=Empty, A=B=bot, C=bot∨bot, gs=[[],[]], tail=[] gives inhabited cut-free old/terminal proofs. Both roots are reducible, retained ranks tie, and this terminal candidate fails the strict quantifier. This is not a counterexample to the existential lemma. |
| W4.HeadRight.denote; addressed_right | For terminal selected-disjunction data, n≥2 and arbitrary ReducibleR address, the constructed head-introduction repair has the same sequent/Reduced denotation, is cut-free, preserves rebuilt denotation and bounds every newly eligible descendant. |
| ContractionBound.bound; W4.HeadRight.repair_bound | A finite structural induction bounds unblocked contractions on the selected ancestry. The concrete repair constructs this argument internally; no caller-supplied bound appears in addressed_right. |
| ContractionSelection.extract, ext_selected | A nonempty strictly position-ordered list of C occurrences is exactly a syntactic selection's full selected list; two selections with the same endpoints/list coincide. Equal labels remain separate positions. |
| performL/R and rank lemmas | One selected copy is a context transport with zero extra proof nodes; ≥2 uses the existing contraction constructor. Denotation, counts, atomization and exact rank cost compile. |
| chain/merge/parallel components | Complete selected lists concatenate without deduplication. The two-retained-copy merge is an actual two-copy ContractionBlock. All route comparisons use product/coproduct component extensionality in Reduced.Hom. |
| W5.MixedPremiseMix.addressed_left/right | For arbitrary nonempty selections p : ContractionSelection C F K and q : ContractionSelection C U L, the constructed chained contraction over mix is replaced by independent premise contractions followed by the existing blocked gammaMix contraction. Both addressed results have the full eligible-descendant quantifier. Arity-one and unequal-arity cases are included. |
| Route.parallel_conjRight / parallel_disjLeft | Native conjunction-right is natural in its two antecedent routes; native disjunction-left is natural in its two succedent routes. These actual categorical equations do not provide the missing logical producers or source-macro ancestry/rank proofs. |

The mixed families preserve cutCount exactly, CutFree/Atomized equivalences
and complete tagged relations. The examples include inhabited constant proofs
over Empty, arities 2 and 3, both literal signs and actual cut-containing
premises. Neither equality of occurrence relations nor equality after full
inclusion is used to prove Reduced equality. The original presentation,
Reduced equations, G constructors, Positive, Atomized, CutFree, Topmost,
blocked/reducible predicates and all-node ranks are unchanged.

For the right-W4 repair put I=X++C::Y and L=rankInnerR. Its actual stages are
inner exchange I++[A,B]→[A,B]++I, head disjunction introduction, the existing
BlockedR.disjunction contraction with gaps [[],X] and tail Y, and the final
exchange to (X++Y)++[C]. The retained ranks compile as L+1, L+2, L+4, L+5;
oldR has L+n+1. The repaired root need not be rank-nonincreasing. The middle
contraction is blocked, administrative rules are not contractions, and the
fresh C has no predecessor at its introduction. Every remaining eligible
contraction on this ancestry has rank at most L, hence below L+n+1.

For mixed W5 let n=p.arity≥1, m=q.arity≥1, Sp and Sq be the complete original
selected-rank sums and δ(k)=1 if k≥2, otherwise 0. The exact old root rank is
`1+Sp+Sq+n+m`. The new rank is
`3+Sp+Sq+δ(n)+δ(m)`, at most the old rank since δ(k)+1≤k.
The new root is blocked; any eligible proper descendant has strictly lower
rank. This argument does not assert a global decreasing rank sum or
arbitrary-context termination.

## Source correspondence

Pinned Došen–Petrić, Proof-Theoretical Coherence, September 2007 source:
SHA-256 e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e.
Cached source access succeeded. Printed p.n is one-based PDF p.n+12.
Printed p.251 was rendered and inspected; pp.248–253 were extracted again.
No published equations or coherence conclusions were added as generators.

| Printed location | Source role | Lean correspondence / boundary |
| --- | --- | --- |
| 248–249, clusters/rank | Whole-formula ancestry; contraction branches to all selected copies | Existing Premise.parent/rho, successful address transport and first-separation proof; literal relations are a different interpretation. |
| 250, blocked patterns and Reducibility | Proper containing tied contractions must be blocked | All fourteen premise frames and entry_unique derive the distinguished-entry inference; they do not assert global injectivity. |
| 251 (W4), right analogue 252 | Isolate the introduced compound and contract parametric copies below it | Addressed left theorem and repaired right theorem. Source strictification/coherence appeals are replaced by actual route/logical component equations and visible exchange nodes. |
| 251–252 (W5), mixed mix display 252 | Contract each premise then merge two retained copies | Constructed p/q mixed families, direct route factorization and mix naturality; singleton selections add no artificial contraction node. |
| 252, logical W5 and W6 | Binary logical/source-macro producers with selected principal cases | Only the listed native context-route comparisons are new proofs; full logical producers and their eligible-path classifications remain open. |
| 253, Blocked-w | Finite multiset induction after both Reducibility Lemmata | Not established. No transfer from local ranks to a global termination measure. |

The source's earlier Semilattice Coherence appeal is not supplied as a Lean
hypothesis. No new source discrepancy is claimed; the terminal right candidate
failure concerns the repository's explicit syntax and rank, not a defect in
the published existential theorem or manuscript v5.

## Precise remaining inference and next construction

The missing step is an unconditional producer from **arbitrary** ReducibleL/R
data to a local construction with the complete descendant conclusion. The
selection classifier supplies seven regimes, not a reduct. extract supplies
actual gaps, but the branch splitting, source-macro comparisons and complete
eligible-path bounds have not been assembled for all regimes. No theorem in
this change closes that inference; the two governing targets above remain open.

A concrete next case is source p.252 (W6). Put C=disj A B. For nonempty
selections p : ContractionSelection C Γ K and q : ContractionSelection C Θ L,
f : G P (Γ++[A]) Δ and g : G P (Θ++[B]) Λ, let
`s := (p.chain q).chain (ContractionSelection.last [])`.
The old proof is s.block.applyL at its proved arity≥3 over
BlockedSource.disjLLast f g; its final antecedent is s.erased++[C].
For the nontrivial subcase p.arity,q.arity≥2, the existing operations give
`(p.block.extend [A]).applyL ... Δ f` and
`(q.block.extend [B]).applyL ... Λ g`. Construct the outer left3/disjunctionBoth
proof over their disjLLast, prove its endpoint equality
`s.erased++[C] = (p.erased++q.erased)++[C]`, its Reduced equality to the old
proof, and the full addressed descendant bound. Its three selected slots are
the two retained parametric copies and the fresh compound; all other equal
formulas are fixed positions. Then include singleton branches, one-selected-
premise W6 cases and the separately typed right analogue. Native disjL and
terminal disjLLast cannot be interchanged by endpoint equality; their actual
exchanges contribute to ranks. The compiled context-route lemmas are
insufficient by themselves to prove this producer. This is an unfinished
construction, not a refutation or an unavailable source statement.

Remaining ledger: logical W5/W6 producers and native/macro ancestry transport;
remaining W1 crossing-selected/multi-gap/absorption exchange regimes;
profile-to-actual-reducer dispatch; both complete Reducibility Lemmata;
outside-occurrence and containing-blockedness transport; finite multiset
induction/Blocked-w; clean-cut/cut elimination; restricted positive coherence,
PositiveCoherence, Reduced.Faithful, Boolean Coherence, intended congruence/
substitution bridges, unconditional maximality and Palomar preparation.

## Verification and retained evidence

Pinned Lean 4.35.0, Init-only dependencies. Final checked sources:
**249 files / 8,919 audited declarations**. All 47 new public type
queries passed in 1.489s; 47 selected prints were added
to the complete transitive audit. Permitted axioms are exactly propext,
Quot.sound and Classical.choice.

| Command label | Exit | Seconds |
| --- | --- | --- |
| strict | 0 | 12.514 |
| audit-boundaries | 0 | 9.315 |
| presentation-boundaries | 0 | 1.24 |
| manuscript | 0 | 0.027 |
| diff-check | 0 | 0.022 |
| cached-diff-check | 0 | 0.008 |

strict is `bash scripts/verify.sh`; the two boundary labels invoke their
corresponding Python scripts; manuscript is `(cd manuscript && sha256sum -c SHA256SUMS)`;
whitespace checks are `git diff --check` and `git diff --cached --check`.
All five negative controls rejected with exit 1: public custom axiom, unused
private axiom, hidden external dependency, reflexive identification of tagged
projections, and zero without a typed existing-arrow witness. Both scripts
returned 0 because these rejections were expected.

65 unsuccessful exploratory builds are retained honestly, including
failed dependent rewrites and arithmetic elaborations. Their diagnostics are
not final failures or extra proofs. Exact receipts and raw logs are in
provenance/wsl-gentzen-reducibility-followup/ (RAW_LOGS.tar.gz); source inventory
is CHECKED_SOURCES.sha256. FINAL_CHECKS.json/PUBLIC_TYPES_CHECK.json record
commands, exit codes, timings and log SHA-256 digests; PUBLIC_TYPES.txt gives
exact types; EXPLORATORY_CHECKS.json records every attempted build. BASELINE.json
records refs, stash and source hashes; EVIDENCE.sha256 hashes retained evidence.
The strict log hashes the checked source bytes, which are rechecked before
commit and against Git blob bytes afterward. No Lean changes follow the final
strict run. Subsequent record-only whitespace checks are retained separately.

No independent kernels, Comparator, official Palomar preflight/service,
publication, whole-manuscript review or rendering were performed. Manuscript
v4/v5 bytes and checksums are preserved; privacy is unchanged.

## Reviews and delivery

The hostile and mathematical-writing reports are author-side reviews, not
independent certification. They reject a complete Reducibility claim while
recording the precise new theorem scopes. The governing KLR course-report
cache was verified at SHA-256
9bf404c2c75633a1f39aae97af0b2e9335ce6d83cf386c84906654589b4e82e6;
§1 and §4 were consulted directly. Historical access failures are preserved.
No review or process commentary is inserted into manuscript text or comments.

Retained report: docs/GENTZEN_REDUCIBILITY_FOLLOWUP_REPORT.md.
Reviews: docs/reviews/GENTZEN_REDUCIBILITY_FOLLOWUP_HOSTILE.md and
GENTZEN_REDUCIBILITY_FOLLOWUP_WRITING.md. All three are delivered to Downloads
using conflict-preserving names and compared against committed Git blobs.
Post-commit/ref/delivery receipts are retained separately under .codex-work/.
