from pathlib import Path
import hashlib,json,shutil,subprocess
r=Path('/home/flengyel/src/Dosen-Petric-Maximality');p=r/'provenance/wsl-gentzen-reducibility'
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
summary=json.loads((p/'summary.json').read_text())
api=json.loads((p/'integrated-api.json').read_text())
shutil.copytree(r/'.codex-work/presentation-bridge/presentation-controls',p/'presentation-controls',dirs_exist_ok=True)
assert all(x['passed'] and x['exit_status']==1 for x in json.loads((p/'presentation-controls/report.json').read_text()))
ac=json.loads((p/'audit-controls/report.json').read_text())
assert all(x['passed'] and x['exit_status']==1 for x in ac['checks'][:3])
def write(n,s):
 q=r/n;assert not q.exists(),n;q.write_text(s)
checks='\n'.join('| '+x['name']+' | '+str(x['exit_status'])+' | '+str(x['seconds'])+' |' for x in summary['final']['checks'])
types=summary['types']['checks'][0]
report='''# Gentzen Reducibility: reconciliation and verified partial results

## Status and governing endpoint

**Both full Reducibility Lemmata remain unproved.** This checkpoint reconciles
the concurrent sources, proves replacement/cluster transport and conditional
descendant bounds, and connects terminal-left W4 to that bound. It also proves
two representation separations that prevent a direct reuse of the source case
analysis. It is not completed Reducibility, source-faithful reduction dispatch,
Blocked-w, or cut elimination.

The governing instruction is [the complete Reducibility task](CODEX_GENTZEN_REDUCIBILITY_2026-10-24.txt),
byte-identical to its Downloads copy (SHA-256
`6d33982103e1a0265a2d7ed02ed62dfd17ffd07811610eaee2b8a53e62491cc9`).
It supersedes the mixed-W5-only continuation. The supplied
[review of the preceding checkpoint](reviews/GENTZEN_REDUCIBILITY_REVIEW_2026-10-24.md)
is retained unchanged. The reviewed base is
`9075ecc343be5c07d38b7f5ba53676f8f8f32bea`, after the replacement/integration commit
`6b860df5fdb6e4c1c50dc583e0de0d04c102eb25`.

For arbitrary P, C, contexts and proofs
`f : G P Γ (C::Δ)`, `g : G P (C::Θ) Λ`,
`w : G P U V`, `a : ProofAddress g w`, `x : At U C`, the missing left theorem
must obtain from `ReducibleL f g a x` a proof `h : G P U V` such that
`h.CutFree`, `ofTerm h.denote = ofTerm w.denote`, and, for **every**
`b : ProofAddress h v` and `y : At I C`,

```text
ReducibleL f (a.replace h) ((a.inserted h).append b) y →
  v.rho .left y < w.rho .left x.
```

The right theorem places a in f, uses `ReducibleR`, and compares right ranks.
Neither theorem may require a caller-supplied reduct, coherence, injectivity,
or an assumed rank conclusion. The results below do not meet that full target.

## Preserved and combined source

Both sessions used the same checkout. The identified WSL2 writer PID 700028
exited; PID 3970616, the VS Code CLI, remained. Ten snapshots over twenty
seconds showed no further source/record/Git-state writes before continuation.
`WRITER_PROCESSES.json` records the later process observation. An observed
stable interval alone is not proof that every possible writer has stopped.

Before integration, tracked binary diffs, index state, all untracked bytes,
recent history, worktrees, stash refs and process working directories were
preserved. The archive `PRESERVED_RECONCILIATION.tar.gz` also retains the
overlapping exploratory implementations, including their original filenames
and hashes. They remain evidence outside the production import closure, not
discarded replacements or accepted proofs. The independent temporary candidate
was compared with 9075ecc: its ten modified Lean files match that commit.
The root import/audit differences in the live checkout were additive transport
registrations. Correctness and provenance were not inferred from Git status.

Four formerly untracked modules are incorporated **byte for byte**:
`GentzenAddressTracing`, `GentzenAddressPaths`, `GentzenClusterTransport`, and
`GentzenEntryFrames`. Four new modules add the checked boundary/W4/separation
results and examples. Only public imports and selected axiom prints change in
existing Lean files. No existing grammar, equation, predicate, rank, dependency,
or manuscript definition was changed. The integration stash
`dedfd8fc8cd49930e9a162d5be585215b062a43c` remains intact. No reset, clean,
stash drop, competing-file overwrite or work in another project was used.

The resulting combined baseline passed at **220 source files / 8,538 audited
declarations**, strict exit 0 in 8.509s, plus both boundary scripts and the
five expected negative rejections. These are measured results, not the older
216/8,406 checkpoint figures.

## Proved declarations and exact hypotheses

All names below are in `DosenPetric.Reduced.Gentzen`. The complete 75 public
queries and 59 selected theorem axiom prints are in `integrated-api.json`,
`PublicTypes.lean` and the retained output. These counts concern this task's
eight modules; the transitive audit covers the entire production closure.

| Declarations | Checked conclusion and hypotheses |
| --- | --- |
| `TraceNode.rank_eq_rho`, `edge_rank_lt`, `reach_rank_le/lt` | Cluster-node rank is the selected proof rank; immediate ancestry decreases it. Reachability gives ≤, or < when endpoint addresses differ. No denotation hypothesis. |
| `Branch.eq_of_branch`, `ProofSpine.eq_of_path`, `ProofAddress.eq_of_path` | Actual branch sequences identify typed proof occurrences with fixed endpoints. Equal proof values in different branches retain different addresses. |
| `ProofAddress.ascend`, `ascend_append/inserted`, `ascend_reach`, `ascend_rank_le/lt` | Partial whole-formula ascent along an actual address; strict rank bound requires a nonempty path and a successful ascent. |
| `cluster_iff_ascend`, `ascend_replacement`, `replacement_cluster_iff` | Membership in the rebuilt cluster is equivalent to an intermediate local position z with `b.ascend s y = some z` and `a.ascend s z = some x`. Formula, side, proof and position types are retained. |
| `EntryFrame.mono/index_reindex/of_index/immediate/unique_origins` | A finite separation frame bounds which root entries can reach a descendant contraction. `unique_origins` equates the root entry positions, not arbitrary descendant positions. An actual `EntryFrame` is a hypothesis; the source blocked-pattern instances have not been constructed. |
| `Premise.equal_parent_or_lower` | Two upper positions with the same parent are equal, or that parent is a lower contraction position. This follows from the established independent predecessor classification. |
| `ProofAddress.injective_root/down`, `noncontracting_injective` | Root ascent is injective; step preservation requires no lower contraction on the selected side in the parent. `NoncontractingPath` is an explicit sufficient syntactic condition, stronger than ReducibleL/R. |
| `ReducibilityBoundary.entry_unique_of_injective` and `_right` | Given ReducibleL/R and InjectiveAscend, any local position ascending to the cut position equals the chosen lower contraction position. The injectivity premise is not derived from reducibility. |
| `ReducibilityBoundary.descendants_left/right` | Given a blocked candidate h, a unique cut entry x at the original address, and `h.rho s x ≤ w.rho s x`, every post-replacement reducible descendant has rank < the original selected rank. No denotation equality or cut-freeness is assumed or inferred by these boundary lemmas. They do not construct h. |
| `G.reindex_trans`, `BlockedL.reindex`, `BlockedR.reindex` | Composition of actual equality transports and transport of the existing blocked predicates. No new exchange constructor is hidden in a cast. |
| `W4.SelectedLogical.new_blockedL` | The existing terminal-left W4 reduct is exactly the `(w∧1)` blocked pattern after proved endpoint transports, for arbitrary d, arity≥2, contexts and premise. |
| `addressed_left_of_injective` | For an arbitrary address to a terminal-left W4 old proof, `ReducibleL` **and** `InjectiveAscend .left` give a cut-free new proof, equal local/rebuilt Reduced denotations, and the full quantifier over all post-replacement reducible descendants. No atomicity assumption. |
| `addressed_left_noncontracting` | The descendant conclusion follows under ReducibleL and the stronger syntactic NoncontractingPath condition. This is a conditional specialization, not the full left lemma. |
| `two_copy_root_left` | For arbitrary A,B,P, a cut-left proof and a cut-free premise `G P [A∧B,A∧B,A,B] Δ`, constructs h at `[A∧B] ⊢ Δ`, with equal Reduced denotation and the complete post-replacement descendant bound. The containing address is root, so no injectivity premise is needed. |
| `ReducibilityObstructions.terminal_right_w4_unblocked` | Every existing terminal-right W4 reduct is **not** BlockedR. Its unary disjR premise has a nonempty fixed prefix. The current blocked unary right pattern has empty prefix. This does not refute existence of another suitable reduct. |
| `freshBoth_unblocked`, `splitMix_blocked` | The native three-copy disjL example is unblocked despite its proved selectedBoth profile; singleton/singleton mix is already a gammaMix blocked contraction. Neither observation is a counterexample to the classifier or the full Reducibility theorem. |

For the two-copy root W4 case, old and new retained endpoint ranks tie.
The proof excludes a reducible root because the new root is blocked; every
eligible proper descendant follows a nonempty ancestry path and therefore
has strictly smaller rank. This handles surviving old descendants as well as
newly created nodes. Under the additional injective-address hypothesis the
same reasoning works below arbitrary containing rules.

Compiled examples distinguish identical siblings by both address and selected
position, check their two different clusters, trace a surviving position
through an actual cut, cover both literal signs, and instantiate the root W4
existential over `P = Empty` with an inhabited constant premise. Existing
replacement identity/sibling/congruence/count proofs are reused unchanged.
No cut-count or proof-size comparison is converted into a cluster-rank claim.

## Source correspondence

The hash-verified September 2007 PDF is
`e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed n corresponds to PDF n+12, one-based. Printed pp.248–253 were
consulted; rendered p.250 was inspected again. Historical access records and
the cached PDF remain preserved. No new equation is attributed to the source.

| Source | Present construction | Remaining comparison |
| --- | --- | --- |
| pp.248–249: whole-formula basic sequences, cluster, all-node rank | Typed At positions, actual branches/paths, finite cluster and successful partial ascent; exact rank/reachability bridge | No rank invariance under arrow equality. |
| p.250: seven displayed blocked patterns and proper-containing reducibility | Existing BlockedL/R and ReducibleL/R retained; new blocked reindex laws and W4 `(w∧1)` instance | Macro adequacy for primitive disjL and right-retention/order remains unproved. |
| p.250: Reducibility Lemma; pp.251–252 case analysis | Full required quantifier appears in both boundary criteria and the scoped left W4 theorems | Criteria assume a candidate and entry/rank data. No general producer from ReducibleL/R exists. |
| p.251 W4, `(w∧1)` | `new_blockedL`, retained endpoint bound and all-descendant W4 specialization | General blocked-ancestor entry uniqueness is open. |
| p.252: right analogue after W6 | Separately typed right boundary criterion; terminal-right W4 mismatch proved by a syntactic prefix observer | The head/terminal comparison and its eligible-descendant rank bounds are open. |
| pp.251–252 W5 and p.252 W6 | Existing one-premise mix families reused; singleton/singleton blockedness checked | General mixed extraction, binary logical reducers and full dispatch are open. |
| p.253: Blocked-w multiset induction | No new claim | Outside-occurrence/blocked-ancestor transport, finite eligible-occurrence collection and well-founded multiset order remain to be constructed. |

The source's Semilattice Coherence appeals have not been installed as Lean
assumptions. Earlier local categorical equations use the existing Reduced
laws. Literal-occurrence equality follows from those equations where used;
it never proves syntactic arrow equality. Whole-formula ancestry is a separate
construction, including constants whose literal occurrence types are empty.

## Exact blocker and attempted repair

The first missing inference is the following **proposed sufficient lemma**,
not a production assumption or a claimed theorem:

```text
(hr : ReducibleL f g a x) →
  ∀ z : At U C,
    a.ascend .left z = some (At.here C Θ) → z = x
```

There is a separately typed right version. InjectiveAscend proves this
in a restricted class of containing contexts. General reducibility only says
that proper containing *tied* contractions are blocked. It does not state
that ascent is globally injective. Replacing that missing inference by global
injectivity would strengthen the target's hypotheses and is not accepted.

A concrete structural route is to prove, for all seven blocked left cases,
with `t : G P (repeated C gs ++ Θ) Δ`:

```text
BlockedL (G.contractL C gs Θ Δ hn t) →
  EntryFrame .left C t (fun z => z ∈ selectedCopies C gs Θ)
```

and the separately typed right schema. These finite frames must pass through
the actual disjLLast exchanges and source retention conventions. Combining
them with proper-ancestor blockedness and the proved `unique_origins` is the
attempted repair. Only the generic frame calculus is proved; these source
instances and the resulting uniqueness inference remain open.

The second demonstrated obstruction is **not** an unproved compiler goal:
`terminal_right_w4_unblocked` compiles. Put C=A∨B, X=gaps gs, Y=Θ and
I=X++C::Y. The current right W4 new proof contracts after a terminal
`disjR Γ I [] A B`, whose prefix has positive length. BlockedR.disjunction
recognizes `disjR Γ [] (X++C::Y) A B` instead. Equality of endpoints or
denotations cannot identify these proof constructors.

An explicit repair to investigate is to exchange the inner proof's output
`I++[A,B]` to `[A,B]++I`, introduce C at the head with disjR, contract the
head C with the parametric C using gaps `[[],X]` and tail Y, then exchange
the retained C across Y to reach `(X++Y)++[C]`. The middle contraction is
then the actual BlockedR.disjunction pattern. This requires a checked
Reduced comparison with the existing terminal composite and an ancestry
analysis through all explicit exchanges. It is not implemented or assumed.
The outer exchange is not a contraction; its rank cost cannot be erased.
A blocked-frontier descendant argument is needed rather than falsely
asserting that the entire wrapped proof is BlockedR or has a small root rank.

Thus the full target has not been proved and has not been refuted. The
checkpoint establishes where the attempted proof stops. Mixed W5 and logical
W5/W6 remain subordinate missing cases; no new research objective replaces
the governing Reducibility task.

## Verification and evidence

Final sources: **224 Lean files / 8,602 audited project declarations**.
Pinned Lean 4.35.0, Init-only closure and existing Lake manifest unchanged.
Final sequential commands after the last proof edit:

| Command | Exit | Seconds |
| --- | --- | --- |
'''+checks+'''

The strict row is `bash scripts/verify.sh`; boundary rows are the two named
Python scripts; manuscript is `(cd manuscript && sha256sum -c SHA256SUMS)`.
Exact command arrays, timestamps, logs and hashes are in `final-20261025T015738139434.json`.
The 75 public type queries passed (exit 0, '''+str(types['seconds'])+'''s).
The 59 selected axiom prints supplement the complete transitive audit;
permitted axioms remain propext, Quot.sound and Classical.choice.

All five expected controls rejected with Lean exit 1 and the expected diagnostic:
public custom axiom, unused private custom axiom, hidden external axiom
dependency, distinct tagged projections identified by rfl, and zero without
a correctly typed existing-arrow witness. Full local public import closure
passed. Evidence fixtures are deliberately invalid controls, not production proofs.

Six failed exploratory compilations are retained with commands, exits,
timings and diagnostics. They concern dependent pattern parameters, an unused
binder/namespace lookup, composed casts, an observer through transports, and
two root-address endpoint attempts. All were followed by passing checks;
there was no aborted new full build or overlapping heavy process in this phase.
The earlier concurrent checkpoint's failures and interrupted isolated attempt
remain historical evidence and are not relabelled as current success.

Evidence directory: `provenance/wsl-gentzen-reducibility/`.
Key SHA-256 values:

- Checked source/tool inventory: `'''+sha(p/'CHECKED_SOURCES.sha256')+'''`.
- Final strict log: `'''+sha(p/'strict-20261025T015738139434.log')+'''`.
- Exact public type output: `'''+sha(p/'types-20261025T015843537976.log')+'''`.
- Preserved reconciliation archive: `'''+sha(p/'PRESERVED_RECONCILIATION.tar.gz')+'''`.

`EVIDENCE_SHA256SUMS` inventories the retained evidence;
`REPORT_SHA256SUMS` and `RECORD_SHA256SUMS` identify reports and status records.
Post-commit receipts compare source bytes, all scoped committed files, refs and
delivered reports. They are separate from the pre-commit build identity.

## Remaining obligations and delivery

Next: construct the actual blocked-pattern entry frames and prove the
proper-ancestor-to-unique-entry inference, then remove InjectiveAscend from
the addressed left W4 theorem. In parallel dependency order, resolve the
explicit head/terminal right W4 comparison above; do not obtain it by
contravariant arrow negation or invisible exchanges. Both full Reducibility
Lemmata remain the acceptance criterion. Complete missing W1/W2/logical and
mixed W5/W6 cases only as branches of that target.

Blocked-w, arbitrary surrounding-context eligibility transport, cut elimination,
restricted positive coherence, PositiveCoherence, Reduced.Faithful, Boolean
Coherence, remaining congruence/substitution bridges and unconditional
maximality remain open. No manuscript defect follows from an unfinished proof
of a cited theorem. Palomar independent kernels/Comparator/preflight/service,
publication, fresh manuscript layout and independent peer review were not run.

The associated [hostile](reviews/GENTZEN_REDUCIBILITY_HOSTILE.md) and
[writing](reviews/GENTZEN_REDUCIBILITY_WRITING.md) reviews are AI-assisted
author-side reviews. They reject a full Reducibility completion claim.
Repository reports remain under docs/; conflict-preserving copies and the
updated continuation are delivered to `/mnt/c/Users/fleng/Downloads` and
compared byte for byte with committed Git blobs. Final SHA/ref/delivery
receipts are retained in `.codex-work/gentzen-reducibility/`.
'''
write('docs/GENTZEN_REDUCIBILITY_REPORT.md',report)
hostile='''# Author-side hostile review: reconciled Gentzen Reducibility work

This AI-assisted author-side audit reviews the eight integrated modules,
actual public types, correspondence additions and GENTZEN_REDUCIBILITY_REPORT.
It is not independent peer review or kernel certification. The acceptance
criterion is both full source-shaped Reducibility Lemmata, not another local
family. Source: hash-verified September 2007 text, §11.2 pp.248–253; p.250
rendered. Review conducted against the checked working sources recorded in
CHECKED_SOURCES.sha256. Manuscript v5 is not re-reviewed here.

## (A) Kill-shots / hard blockers

**A1 — Full Reducibility is unproved (major; repairable).** Anchor:
GENTZEN_REDUCIBILITY_REPORT, “Status and governing endpoint” and “Exact blocker”;
GentzenReducibilityLogical.addressed_left_of_injective; source p.250 Reducibility
Lemma and p.252 right analogue. Failure mode: unproved. Evidence: derivation
from the checked type. The local theorem requires InjectiveAscend, produces
only the terminal-left W4 candidate and has no general right producer.
The root two-copy result genuinely handles every eligible descendant, but
does not remove these restrictions. Claiming either full lemma would therefore
fail acceptance. The report accurately says both remain open.

**A2 — Direct right-W4 blockedness is false (major for this proof route).**
Anchor: GentzenReducibilityObstructions.terminal_right_w4_unblocked and
BlockedR.disjRightPrefix; report “Exact blocker”; source p.252 right analogue.
Failure mode: false if the current terminal reduct is claimed BlockedR.
Evidence: checked structural derivation for every Data P .disj and arity≥2.
Its contracted disjR has prefix I of positive length; the only matching blocked
unary right pattern requires prefix length zero. This refutes that particular
proposed correspondence, not the full existential theorem. Repair: prove the
typed head/terminal comparison with every exchange counted, or construct a
different suitable reduct. Definitions have not been enlarged to conceal it.

## (B) Major weaknesses

**B1 — Blocked ancestors do not yet supply the needed entry proof.** Anchor:
GentzenReducibilityBoundary.entry_unique_of_injective/_right and
GentzenEntryFrames.unique_origins; report proposed entry-frame schema.
Failure mode: unproved. Evidence: actual hypotheses. Global injectivity is
proved for a NoncontractingPath, while ReducibleL/R allows blocked containing
contractions. The source-pattern frame instances and the inference to local
unique entry are absent. unique_origins equates root origins; it must not be
misreported as injectivity at descendant positions. Severity major, repairable;
without it the arbitrary-address W4 branch still has an extra assumption.

**B2 — Native and source-order binary syntax remain distinct.** Anchor:
freshBoth_unblocked, splitMix_blocked, unchanged disjLLast; source p.250
(wγ3), (w∨1–3), pp.251–252 W5/W6. Failure mode: unproved correspondence.
Evidence: the native selectedBoth example is now compiled as unblocked, while
the singleton/singleton mix is compiled as blocked. Neither example establishes
a missing reducible case merely by its profile. Larger mixed selections,
logical reductions, actual selected extraction and dispatch remain unproved.
Severity major, repairable; report and continuation retain this boundary.

**B3 — No surrounding multiset theorem follows.** Anchor: report final section;
source p.253 Blocked-w. Failure mode: unsupported_generalization if local rank
bounds are promoted to termination. Evidence: structural argument; new boundary
theorems quantify only within h and assume entry/root data. They do not control
outside occurrences or changes to containing blocked ancestors. Severity major
for any Blocked-w claim, repairable after both replacement lemmata.

## (C) Minor issues

The report distinguishes the measured combined baseline (220/8,538), the final
candidate (224/8,602), and the base commit's older 216/8,406 evidence. The
declaration counts do not measure proof completion. The status maps lead with
the full-target failure and retain historical sections labelled as historical.
Exact public queries remove ambiguity about implicit contexts and address
orientation. No unsupported claim of canonical reduction or quotient rank
invariance remains in the new records.

## (D) Cross-section consistency failures

The preceding mixed-W5-only continuation was too narrow for the present task.
It is preserved as historical evidence and superseded in the current continuation
and README. New files identify the full governing task and retain its supplied
review verbatim. The scoped positive facts agree across code, report and maps:
reduced denotation equality is proved categorically; literal relation equality
may follow, while cluster/rank statements use syntactic ancestry. No circular
faithfulness, new presentation equation, global order/injectivity claim or
unwitnessed zero was found in the new production arguments.

## (E) Acceptance conditions, non-negotiable

1. Both full targets in the governing instruction must compile from only
   ReducibleL/R and the existing data. **Unmet; rejects completion.**
2. Remove the extra containing-address assumption by an actual entry/separation
   proof; instantiate source blocked frames with their real macros. **Unmet.**
3. Supply the native/source-order and right-retention comparisons with explicit
   ancestry and eligible-descendant rank inequalities. **Unmet.**
4. Complete certified case extraction/reducers, including mixed and logical
   W5/W6, under the full quantifier. **Unmet.**
5. Preserve code/axiom/import/source boundaries and checked/committed byte
   identity. Local checks passed; commit/ref/delivery receipts are checked
   separately. This condition alone does not satisfy 1–4.
6. Prove outside-eligibility transport and an actual finite multiset induction
   before claiming Blocked-w or cut elimination. **Unmet; remains separate.**

## (F) Not checked / uncertainty log

Reviewed the actual new proof texts, all 75 public types, retained failure
diagnostics, final strict/transitive audit and five rejection controls. The
four reconciled modules match their preserved original bytes. No independent
kernel replay, source reconstruction on another machine, Palomar run, fresh
manuscript rendering or third-party review was performed. The sufficient entry
schema may be provable; this review does not certify its truth without the
missing source-pattern derivation. No counterexample to the full target was
established. Observed process exit plus stable snapshots supports reconciliation;
it does not attribute authorship or rule out every possible future writer.

Strongest confirmed blocker: neither full replacement-and-rank lemma is proved;
the current terminal-right W4 reduct is provably unblocked.
Strongest suspected unconfirmed blocker: source-order administrative nodes may
require a more substantial blocked-frontier argument than a root-rank bound.
Most important unchecked item: provability of both exact targets for the current
unchanged blocked predicates. The completion rejection does not depend on
unavailable material. Final recommendation: **reject a Reducibility completion
claim; retain the verified scoped subresults and continue the full target.**
'''
write('docs/reviews/GENTZEN_REDUCIBILITY_HOSTILE.md',hostile)
writing='''# Author-side mathematical-writing review: Reducibility checkpoint

The finalized report states its principal limitation at the start: neither full
Reducibility Lemma is proved. Its exact hypotheses separate the general
ancestry results, the conditional addressed W4 theorem and the root instance.
This is an AI-assisted author-side editorial review, not independent mathematical
certification. It covers GENTZEN_REDUCIBILITY_REPORT, the new correspondence and
status passages, continuation and relevant declaration comments; no whole-paper
judgment about manuscript v5 or preserved v4 is made.

## Governing source and access

Consulted the verified MIT-hosted typeset Knuth–Larrabee–Roberts course report,
`.codex-work/references/knuth-mathematical-writing-mit-9bf404c2.pdf`, SHA-256
`9bf404c2c75633a1f39aae97af0b2e9335ce6d83cf386c84906654589b4e82e6`.
Section 1 printed pp.1–6 (PDF pp.3–8) and Section 4 printed p.9 (PDF p.11)
were consulted directly. Historical Stanford access failures and subsequent
MIT access records remain unchanged. No byte identity with the Stanford scan
or MAA edition is claimed. This review is source-grounded, not provisional.

## Actual outline and functions

1. Status and governing endpoint: question, exact full target and noncompletion.
2. Preserved and combined source: reconciliation and measured baseline evidence.
3. Proved declarations and exact hypotheses: definitions, theorem scope and proof idea.
4. Source correspondence: published anchors versus constructed/unproved comparisons.
5. Exact blocker and attempted repair: missing inference and concrete right mismatch.
6. Verification and evidence: actual commands, counts, failures and hashes.
7. Remaining obligations and delivery: dependencies, limitations and checkpoint procedure.

The central question is whether ReducibleL/R produces a replacement bounding
every eligible descendant. The current contribution is a checked transport
and sufficient-bound calculus, a scoped W4 instance, and precise representation
separations. The outline gives these results before verification statistics.
No alternative outline is needed.

## Comparison with the governing source

| Report anchor | Difficulty or distinction | Source principle / rationale | Implemented treatment |
| --- | --- | --- | --- |
| Opening and exact target | Successful builds could obscure mathematical noncompletion | Section 1 points 5 and 12: explicit theorem conditions and reader motivation; status judgment is this review's mathematical rationale | Both full lemmata remain unproved is the first claim. |
| Declaration table | InjectiveAscend and candidate/root hypotheses could disappear in prose | Section 1 point 5, printed p.2 | Hypotheses stated in the relevant rows; all 75 checked signatures retained. |
| Cluster transport versus descendant bound | Similar names can hide distinct assertions | Section 1 points 10–11, printed p.2: connected explanation and complementary definitions | Explain the intermediate position z, then give the blocked-root/nonempty-path proof. |
| Two-copy W4 paragraph | Endpoint equality does not itself imply strict descendant decrease | Section 1 points 11–13, printed pp.2–3, plus independent proof-status judgment | Explain why the root is ineligible and every eligible descendant follows a nonempty trace. |
| Exact blocker | A failed method is not a counterexample to the existential theorem | Independent mathematical rationale; Section 4 printed p.9 distinguishes kinds of mathematical assertions | State exactly which blockedness assertion is false and that the full theorem is neither proved nor refuted. |
| Reconciliation section | Committed/untracked status could be confused with provenance or correctness | Independent evidence-reporting rationale | Record byte comparisons and verified candidate, retain both implementations and no authorship inference. |
| Source map | An informal coherence citation could look like an implemented proof | Section 1 point 5 and independent source-correspondence rationale | Separate source citation, proved construction and remaining comparison. |

## Definition order and notation audit

P, contexts, the cut premises, w, a and x are introduced before the full target.
The declaration table defines successful ascent and explains EntryFrame before
the missing frame schema is used. Root entry positions and descendant positions
are distinguished explicitly; unique_origins is not called injectivity.
Proof address, proof value and selected formula position are separate. The
observer concerns syntactic disjR prefixes, not categorical equality.

Composition is execution order, as in the repository convention. Partial
whole-formula maps may return none at logical introductions; there is no
total map identifying the compound with its components. Internal literal tags
remain separate from whole-formula ancestry, including constants.
Section 4's contextual remarks about definition placement do not demand moving
elementary background into a dictionary. No confirmed missing definition in
the scoped report requires reorganization.

## Prioritized repairs applied

The final opening is “Both full Reducibility Lemmata remain unproved.”
The addressed W4 row explicitly says “and InjectiveAscend .left”. The root
instance is labelled two-copy and root rather than arbitrary-address
Reducer. The right mismatch says it “does not refute existence of another
suitable reduct.” These are necessary strength corrections, not optional style
changes. README and current maps use the same scope; historical reports are
preserved with their old evidence rather than silently rewritten.

The remaining repairs are mathematical: prove the general entry inference,
the right-order comparison and all full-target cases. No wording can discharge
them. No report, review-process note or LLM instruction was inserted into
manuscript prose or LaTeX comments. New editorial work is confined to records.

## Scope and recommendation

Read the scoped report and changed records, actual theorem statements and
source correspondence. Consulted the governing writing source directly.
No manuscript TeX/PDF rendering or whole-paper proof audit was performed; the
manuscript checksum check passed. The report's narrowed contributions are
described accurately, but the task's full mathematical acceptance remains
unmet. Retain this partial-checkpoint wording; do not promote it to completed
Reducibility, Blocked-w, coherence or unconditional maximality.
'''
write('docs/reviews/GENTZEN_REDUCIBILITY_WRITING.md',writing)

current='''Current reconciliation / Reducibility checkpoint (2026-10-25 UTC)
Read docs/CODEX_GENTZEN_REDUCIBILITY_2026-10-24.txt first: it governs the full
left and right replacement-and-all-descendant-rank targets and supersedes the
mixed-W5-only instruction. Both full lemmata remain OPEN. Read the new
GENTZEN_REDUCIBILITY_REPORT and its two author-side reviews, the supplied
GENTZEN_REDUCIBILITY_REVIEW_2026-10-24 review, current status maps and AGENTS.

The identified WSL2 writer exited. Both sessions' combined work was snapshotted;
four original transport modules are retained byte-for-byte and publicly audited.
Four new modules prove sufficient boundary criteria, a conditional addressed-left
W4 theorem, the two-copy root case with all eligible descendants, and concrete
primitive/macro separations. Final local checks: 224 files / 8,602 audited
declarations; all five expected controls rejected; 75 exact public type queries.
Stash dedfd8fc8cd49930e9a162d5be585215b062a43c remains. No reset/clean/drop.
Evidence: provenance/wsl-gentzen-reducibility/. Preserve the reconciliation
archive and alternate drafts; do not classify correctness by Git tracking status.

NEXT INFERENCE, NOT A NEW LOCAL-CATALOGUE OBJECTIVE:
Prove blocked contraction premise frames, using the actual selectedCopies:
  BlockedL (G.contractL C gs Θ Δ hn t) ->
    EntryFrame .left C t (fun z => z ∈ selectedCopies C gs Θ)
and the independently typed right version. Cover every actual blocked macro,
including disjLLast's exchanges. Use the frames, proper-containing blockedness
and unique_origins to prove from ReducibleL f g a x that every local z ascending
through a to the cut head equals x (and separately for ReducibleR). The existing
InjectiveAscend/NoncontractingPath lemmas are sufficient specializations, not
substitutes for that derivation. Remove the extra assumption from addressed W4.

RIGHT W4 REPAIR:
terminal_right_w4_unblocked proves the current terminal-right reduct is NOT
BlockedR. Do not assert its blockedness by duality. With C=A∨B, X=gaps gs,
Y=Θ and I=X++C::Y, investigate exchange of inner output I++[A,B] to [A,B]++I,
head disjR, the actual BlockedR.disjunction contraction (gaps [[],X], tail Y),
and final exchange to (X++Y)++[C]. Prove Reduced equality and the complete
eligible-descendant rank bounds through every explicit exchange. A surrounding
exchange is not a blocked contraction or a rank-transparent cast. This proposed
repair has not been constructed/verified. Do not add a new blocked pattern.

Continue to both full source-shaped Reducibility Lemmata. Mixed W5 is a
subordinate branch; singleton/singleton mix is already blocked (checked).
Native freshBoth selectedBoth remains unblocked (checked). Complete missing
case extraction, logical W5/W6, source-order comparisons and general dispatch.
Only after both lemmata prove outside-eligibility/blocked-ancestor transport,
an actual finite multiset collection and well-founded Blocked-w induction.
Do not weaken rho, predicates, hypotheses or the all-descendant quantifier.

Pinned Lean 4.35.0, Init-only, one heavy job at a time. Run only checks justified
by subsequent changes; compare checked and committed bytes. No proof holes,
custom mathematical axioms, native_decide, coherence assumption, relation
reflection or unwitnessed zero. Preserve manuscript v5/v4 and privacy. Task-
specific non-force SSH commit/push and verified conflict-preserving Downloads
delivery remain required. General Reducibility, Blocked-w, cut elimination,
positive/reduced/Boolean coherence and unconditional maximality remain open.

Historical pre-reconciliation continuation follows; its mixed-only NEXT TASK
and old "current" counts are superseded above, not new verification evidence.

'''
cns=r/'docs/CODEX_NEXT_SESSION.txt';old=cns.read_text();assert not old.startswith('Current reconciliation');cns.write_text(current+old)

correspondence='''## Current Reducibility correspondence: verified partial checkpoint

The governing endpoint is now [both full Reducibility Lemmata](CODEX_GENTZEN_REDUCIBILITY_2026-10-24.txt),
not completion of a selected-position profile or another isolated local family.
See [the reconciled report](GENTZEN_REDUCIBILITY_REPORT.md) and its author-side
[hostile](reviews/GENTZEN_REDUCIBILITY_HOSTILE.md) and [writing](reviews/GENTZEN_REDUCIBILITY_WRITING.md) reviews.

| Source §11.2 (printed pages) | New proved bridge | Exact limitation |
| --- | --- | --- |
| pp.248–249 clusters and rank | Address ascent iff finite-cluster membership; replacement factors through a typed intermediate position; nonempty successful paths strictly lower rho | No rank invariance under categorical equality. |
| p.250 seven blocked patterns; p.251 W4 | Existing terminal-left W4 reduct is the actual `(w∧1)` blocked pattern; all eligible descendant bounds at root/two copies and, conditionally, under injective containing ascent | General ReducibleL-to-entry-uniqueness is open. |
| p.252 right analogue | Separately typed sufficient boundary theorem; current terminal-right W4 reduct is proved unblocked because its disjR prefix is nonempty | Head/terminal/retention comparison and full eligible-descendant bounds remain open. |
| p.250 `(w∨3)` / p.252 W6 | Native freshBoth contraction proved unblocked despite selectedBoth | Macro profile correspondence is not certified dispatch. |
| p.250 `(wγ1)` / p.252 W5 | Singleton/singleton mix contraction is proved blocked | It cannot serve as an example of an unblocked reducible mixed input. |
| p.250 Reducibility Lemma; p.252 right analogue; p.253 Blocked-w | Sufficient transport/rank criteria and scoped left W4 instance only | Both full lemmata, remaining case construction and multiset induction stay open. |

These source anchors do not supply a Lean coherence proof. The conditional W4
theorem's InjectiveAscend hypothesis is explicit and is not part of the desired
full target. Reconciliation preserved all source variants; no blocked predicate,
rank or presentation equation was changed. Earlier records below are historical.

'''
q=r/'docs/PRESENTATION_CORRESPONDENCE.md';s=q.read_text();q.write_text(s.replace('## Objects and arrow grammar',correspondence+'## Objects and arrow grammar',1))
scope='''## Current Reducibility boundary after source reconciliation

The combined checkout is verified, but both full source-shaped Reducibility
Lemmata remain unproved. Address/cluster membership and replacement transport,
strict successful nonempty-path rank bounds, finite entry-frame calculus and
two-sided sufficient descendant criteria compile. Terminal-left W4 is proved
blocked. Its full post-replacement descendant quantifier is proved at a two-copy
root and at arbitrary addressed occurrences **under InjectiveAscend**; the
extra hypothesis has not been derived from ReducibleL. Terminal-right W4 is
proved unblocked for the current pattern representation, so a typed head/order
comparison is still required. Native selectedBoth and blocked singleton mix
boundaries are compiled. See [the exact report](GENTZEN_REDUCIBILITY_REPORT.md).

The governing target is [the full Reducibility instruction](CODEX_GENTZEN_REDUCIBILITY_2026-10-24.txt).
General blocked-ancestor entry uniqueness, macro comparisons and remaining
certified reducer cases are open. Mixed W5 remains subordinate. No change to
the three milestones, coherence assumptions, mathematical manuscript or later
Palomar status follows. Earlier local results below retain their proved scope.

'''
for n in ['MANUSCRIPT_COVERAGE.md','MANUSCRIPT_STATEMENTS.md']:
 q=r/'docs'/n;s=q.read_text();i=s.find('\n\n');q.write_text(s[:i+2]+scope+s[i+2:])
validation='''# Reconciled Reducibility checkpoint — current local validation

**Mathematical status: partial. Both full Reducibility Lemmata remain open.**
The identified WSL2 writer exited; current/untracked/index bytes and alternate
drafts were preserved before integration. Four original transport modules retain
their original bytes. The compared source state passes; tracking status was not
used to attribute authorship or correctness. Stash dedfd8fc remains unchanged.

Measured combined baseline: 220 Lean files / 8,538 declarations, strict exit 0
in 8.509s, then passing boundary/manuscript/whitespace checks. Final checked
sources: **224 files / 8,602 audited declarations**, strict exit 0 in 19.924s.
Both boundary scripts passed (28.958s / 3.039s) and all five expected controls
rejected with exit 1; manuscript SHA256SUMS passed (0.021s); diff/cached diff
checks passed (0.029s / 0.016s). All 75 public queries passed in 2.817s.
59 selected prints supplement the complete transitive audit. Allowed axioms:
propext, Quot.sound, Classical.choice. Six failed explorations are retained.
No proof changes follow this final run; later record-only diffs are checked
separately. Checked/committed bytes and SSH/Downloads receipts are separate.

The source state proves address/cluster replacement transport, conditional
two-sided descendant criteria and scoped W4 integration. The terminal-right
W4 blockedness shortcut is disproved, not repaired by changing a predicate.
The exact open entry and representation statements are in
[the report](GENTZEN_REDUCIBILITY_REPORT.md). Author-side
[hostile](reviews/GENTZEN_REDUCIBILITY_HOSTILE.md) and
[writing](reviews/GENTZEN_REDUCIBILITY_WRITING.md) reviews reject a full
completion claim. Full instruction: CODEX_GENTZEN_REDUCIBILITY_2026-10-24.txt.
Evidence: provenance/wsl-gentzen-reducibility/; preserve the reconciliation
archive, alternate drafts, source inventory and all diagnostics.

Pinned toolchain/Init-only policy, manuscript v4/v5, privacy, existing syntax,
equations, predicates, ranks and all prior scoped constructions are unchanged.
No independent kernels, Comparator, official preflight/service, whole-manuscript
rendering/review, publication or unconditional mathematical bridge was performed.
General Reducibility, Blocked-w, cut elimination and coherence remain open.

## Historical validation records

The records below report earlier checkpoints; they are not additional runs of
the present candidate. Their former "current" labels and next-task proposals
are superseded by the current section and governing full-target instruction.

'''
q=r/'docs/VALIDATION.md';q.write_text(validation+q.read_text())
q=r/'README.md';s=q.read_text()
start='The finite case ledger identifies mixed-premise\nW5 as the next demonstrated gap; one-premise W5 alone does not cover it.'
assert start in s
s=s.replace(start,'''The finite case ledger classifies profiles; it does not certify reduction.
The current objective is both source-shaped Reducibility Lemmata. Reconciled
address/cluster transport and sufficient descendant criteria now compile,
with a two-copy root W4 instance and an addressed-left W4 result conditional
on InjectiveAscend. The terminal-right W4 reduct is provably unblocked in the
current head-pattern representation; its required order comparison remains open.
Mixed W5 is a subordinate missing case, not the completion criterion.''')
s=s.replace('docs/reviews/GENTZEN_BLOCKED_CLASSIFICATION_HOSTILE.md','docs/reviews/GENTZEN_REDUCIBILITY_HOSTILE.md',1)
s=s.replace('docs/reviews/GENTZEN_BLOCKED_CLASSIFICATION_WRITING.md','docs/reviews/GENTZEN_REDUCIBILITY_WRITING.md',1)
s=s.replace('cover blocked/reducible encodings and the finite selection classification; they are','cover the actual transport/W4 subresults and the unproved full target; they are',1)
s=s.replace('The [current classification report and case ledger](docs/GENTZEN_BLOCKED_CLASSIFICATION_REPORT.md),\n[ready-to-paste mixed-W5 continuation](docs/CODEX_GENTZEN_MIXED_W5_DISPATCH.txt),','''The [current partial Reducibility report](docs/GENTZEN_REDUCIBILITY_REPORT.md),
[governing full-target instructions](docs/CODEX_GENTZEN_REDUCIBILITY_2026-10-24.txt),
[current continuation](docs/CODEX_NEXT_SESSION.txt),
[historical classification report and case ledger](docs/GENTZEN_BLOCKED_CLASSIFICATION_REPORT.md),
[superseded mixed-W5-only continuation](docs/CODEX_GENTZEN_MIXED_W5_DISPATCH.txt),''',1)
q.write_text(s)

shutil.copy2('/tmp/dp-reducibility-documents.py',p/'write-records.py')
reports=['docs/GENTZEN_REDUCIBILITY_REPORT.md','docs/reviews/GENTZEN_REDUCIBILITY_HOSTILE.md','docs/reviews/GENTZEN_REDUCIBILITY_WRITING.md']
(p/'REPORT_SHA256SUMS').write_text(''.join(sha(r/n)+'  '+n+'\n' for n in reports))
records=reports+['README.md','docs/CODEX_NEXT_SESSION.txt','docs/MANUSCRIPT_COVERAGE.md','docs/MANUSCRIPT_STATEMENTS.md','docs/PRESENTATION_CORRESPONDENCE.md','docs/VALIDATION.md','docs/CODEX_GENTZEN_REDUCIBILITY_2026-10-24.txt','docs/reviews/GENTZEN_REDUCIBILITY_REVIEW_2026-10-24.md']
(p/'RECORD_SHA256SUMS').write_text(''.join(sha(r/n)+'  '+n+'\n' for n in records))
(p/'EVIDENCE_SHA256SUMS').write_text(''.join(sha(q)+'  '+str(q.relative_to(p))+'\n' for q in sorted(p.rglob('*')) if q.is_file() and q.name!='EVIDENCE_SHA256SUMS'))
print(json.dumps(dict(reports=reports,records=records,evidence_hash=sha(p/'EVIDENCE_SHA256SUMS')),indent=2))
