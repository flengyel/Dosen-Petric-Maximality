# Došen–Petrić maximality in Lean

## Full-paper formalization target

The authorized target is the complete mathematical content of manuscript v6,
including its short structural-isomorphism proof, maximality for the actual
presentation with all dependencies proved, the model corollary, unnumbered
mathematical claims, and both appendices. The existing symmetric-fold proof
remains an alternative route. See the
[full-paper instructions](docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md) and
[immediate continuation](docs/CODEX_NEXT_SESSION.txt).

This expands the completion requirement; it reports no additional Lean theorem.
The conditional result and the open coherence and Reducibility obligations
retain the status recorded below.

## Current Reducibility follow-up (25 October 2026)

**Both full Reducibility Lemmata remain open.** From the unchanged ReducibleL/R
hypotheses, cut-entry uniqueness now compiles via all fourteen actual blocked
premise frames and a typed first-separation argument. Arbitrary-address left W4
no longer requires InjectiveAscend. The repaired right W4, including two copies,
now proves equality, cut-freeness and the complete eligible-descendant bound.
The old terminal right candidate has a compiled reducible-root rank-tie regression.
Mixed-premise mix W5 now has both addressed descendant theorems for constructed
chained selections, including singleton branches and independent multiplicities.
Native binary logical context-route comparisons are proved; logical W5/W6
producers, arbitrary selection/profile dispatch and remaining macro/primitive
comparisons are not. Blocked-w, cut elimination and coherence remain open.

See [the exact follow-up report](docs/GENTZEN_REDUCIBILITY_FOLLOWUP_REPORT.md),
[author-side hostile review](docs/reviews/GENTZEN_REDUCIBILITY_FOLLOWUP_HOSTILE.md),
and [writing review](docs/reviews/GENTZEN_REDUCIBILITY_FOLLOWUP_WRITING.md).
The immediate proof task is [the supplied continuation](docs/CODEX_AFTER_05C6BC8_REDUCIBILITY.txt),
with the unchanged full targets in CODEX_GENTZEN_REDUCIBILITY_2026-10-24.txt.
This is verified progress, not completion of that task. Final sources:
**249 Lean files / 8,919 audited declarations**. Earlier checkpoint
sections below retain their historical scope and are superseded where necessary.


Development for Florian Lengyel's *Maximality of the Došen–Petrić Boolean
Category*, manuscript v6. Its central target is maximality of the free
zero-identity Boolean category under substitution congruences; full-paper
completion also requires the remaining mathematical claims and appendices.

The WSL2 development uses pinned Lean 4.35.0 with an Init-only dependency
closure. Conditional contextual collapse, signed-literal isolation,
substitution transport and relative maximality are proved under explicit
inputs. A generated nonthin structural model instantiates every v5 §5 interface
field; it is separate from the actual source presentation.

The September 2007 presentation now has typed arrow syntax, a generated
syntactic quotient category, structural and zero-identity bridges,
substitution, double negation, normalization and a well-defined tagged
occurrence assignment with global signed-label preservation. Signed-literal
reduction is surjective on normal-form hom-sets. Contextual and common atomic
factorizations, complete occurrence support and the positive zero/union algebra
are proved. These constructions do not establish occurrence faithfulness.

Typed positive Gentzen syntax and existential representation with cuts,
Atomic-k thinning atomization, finite ancestor clusters/rank, and the two
opposite-side thinning and two opposite-side exchange instances of W1 compile.
The opposite-side contraction commutation also compiles as one pair with two
directed rank comparisons: each lowers its targeted side and raises the other.
The sum of these endpoint ranks is not a general decreasing measure.
Both opposite-side unary logical commutations (disjR/conjL) also compile, with
full selected-copy rank losses and introduced whole-formula principal ranks
2→1. These complete the specified opposite-side unary W1 families; same-side
exchange/contraction/logical parametric cases and binary rules remain separate.
Same-side thinning through contraction now compiles at fixed interior gaps and
terminal tails, with both duals, explicit positional routing and complete ordered
selected-copy transport even when the inserted formula equals the contracted
formula. Exact local rank losses and predicate/tagged-relation preservation
are proved; these instances do not establish all-site reducibility.
Four same-side exchange cases now compile for blocks wholly inside one fixed
gap or terminal tail, with both duals, actual positional squares, complete
selected-copy transport and exact local rank laws. Other fixed positions
have unchanged ranks; equal-labelled fixed tags still transpose. Exchanges
crossing selected copies, spanning several gaps or absorbed by contraction
remain separate/open.
Four fixed-parametric same-side unary logical commutations also compile:
conjunction-left and disjunction-right, each inside one fixed gap or terminal
tail. Partial whole-formula ancestry consumes both component slots; separate
categorical component proofs give denotation equality. Retained ranks lose
n−1, principal ranks fall 2→1, and other fixed ranks are unchanged. These
remain local transformations, with broader W1 and Reducibility open.
Two fixed-gap disjoint same-side contraction commutations now compile, with
complete selected-copy transports, actual copies/copies squares and singleton
fibers. Their independent arities give old ranks LC+n,LE+1 and new ranks
LC+1,LE+m: the targeted decrease accompanies an untargeted increase. The exact
sum balance and a checked unequal-arity increase rule out a general decreasing
sum claim. Both terminal-tail disjoint contraction cases also compile, using
a shared proved interface that is instantiated in the preserved interior case.
Their complete selected transports/fibers and independent rank table are proved;
the terminal retained order is C before E. Shared-selected W3 fusion and its
right dual now compile: one constructed contraction has n+m−1 selected copies,
exact Reduced equality and retained rank drop m. Complete positional fibers
and weighted sums preserve equal-labelled fixed tags; counts, predicates and
tagged relations are preserved. Terminal selected-thinning W2 and its right
dual now compile: complete ordered selection includes the new leaf, exact
contraction/endpoint losses are n+1/n, and other fixed ranks are unchanged.
Both cut counts and CutFree predicates are preserved; old Atomized iff
AtomicFormula C and f.Atomized, while new Atomized iff f.Atomized.
Terminal selected-logical W4 and its right dual now compile with actual
partial ancestry and both consumed component equations. The source contraction
loss is n+1; final retained ranks tie for n=2 and decrease for n≥3.
Other fixed same-side ranks increase by one. Counts, CutFree/Atomized and
tagged relations are preserved. Single-premise mix W5 now compiles when
all selected copies lie in g in G.mix f g, with its right dual, complete premise
fibers and n/n−1 rank losses. Fixed/opposite g ranks are unchanged at
2+rho; f ranks drop from 2+rho to 1+rho on both sides. This corrects
the continuation's omitted outer-node prediction. Counts, CutFree/Atomized
and tagged relations are preserved. The G.mix g f placement and its right
dual now compile with prefixed gaps, complete branch fibers and the same
rank table. Disjoint interleaving remains separate.
Typed proof-tree replacement now compiles at any chosen address, preserving
outer endpoints and siblings, denotation, inserted paths and exact cut/size
balances. Both other-placement W5 duals lift into arbitrary surrounding proofs;
actual nested signed-cut and Empty constant examples exercise the integration.
Source blocked-pattern encodings and typed reducible occurrences now compile,
with proper-ancestor laws and exhaustive selection profiles retaining actual
predecessor/premise tags. All fourteen blocked patterns and all seven profile
regimes have inhabited tests. The finite case ledger classifies profiles; it does not certify reduction.
The immediate objective remains both source-shaped Reducibility Lemmata.
Distinguished cut-entry uniqueness is now proved from ReducibleL/R via all
fourteen blocked premise frames. Both addressed W4 cases and both constructed
mixed-premise mix W5 cases prove their complete eligible-descendant bounds,
without caller-supplied injectivity. The old two-copy terminal right-W4
candidate fails by a compiled rank-tie regression; use the constructed head
repair. Complete native/source logical producers, selection dispatch,
outside-site transport, Blocked-w, cut elimination, coherence and actual
maximality remain open. The full task is not completed by these local results.
See [validation](docs/VALIDATION.md) for the maintained audited declaration
count, commands, evidence and limits of the local checks.

## WSL2 setup

The intended directory is `/home/flengyel/src/Dosen-Petric-Maximality`, on the
WSL2 Linux filesystem. With GitHub SSH authentication configured and Elan installed:

```bash
mkdir -p /home/flengyel/src
git clone git@github.com:flengyel/Dosen-Petric-Maximality.git /home/flengyel/src/Dosen-Petric-Maximality
cd /home/flengyel/src/Dosen-Petric-Maximality
bash scripts/setup-wsl.sh
```

If that directory already exists, inspect its Git status and origin before
updating it. See [WSL2 instructions](docs/WSL2_SETUP.md) for prerequisites.
The setup installs only the pinned project toolchain and runs verification;
it does not change Elan's global default. Local build and audit outcomes are recorded in validation.

Initial modules use Lean core only. The matching Mathlib release is recorded
at full commit `56a005855ea17e0b0958f73ec801ae140b0a1679`; it is not an active
dependency. The committed Lake manifest therefore has no dependency packages.

## Proof scope and continuation

1. Contextual collapse relative to explicit structural and faithful-interpretation data.
2. Maximality relative to explicit coherence, normalization, presentation, and substitution inputs.
3. Maximality for the actual Došen–Petrić presentation after those inputs are established.

The conditional theorems do not complete the intended-presentation milestone
gates. Many syntactic bridges above are constructed, while coherence and
remaining congruence/substitution interfaces are still required. Coherence
applies in the original category; zero arrows require a witness that the
hom-set is inhabited.
The [statement map](docs/MANUSCRIPT_STATEMENTS.md) and
[coverage map](docs/MANUSCRIPT_COVERAGE.md) record the precise boundary.
Use [the next-session prompt](docs/CODEX_NEXT_SESSION.txt) to continue in WSL2.

The current manuscript is v6: [TeX](manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v6.tex)
and [PDF](manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v6.pdf).
It gives a shorter contextual-collapse proof from the published structural
isomorphisms, distinguishes the result from Joyal's theorem, and describes the
conditional Lean formalization. No earlier explicit statement of the same
maximality theorem was found; derivability from older results does not establish
prior publication. The Lean sources and their open coherence obligations are unchanged.
See the [corrected novelty review](docs/DOSEN_PETRIC_MAXIMALITY_NOVELTY_REVIEW_2026-10-25.md),
[v6 hostile review](docs/reviews/V6_HOSTILE_REVIEW.md),
[writing review](docs/reviews/V6_WRITING_REVIEW.md),
[Lean scope check](docs/reviews/V6_LEAN_SCOPE.md), and
[validation](docs/V6_VALIDATION.md).
MSC2020: primary 03G30; secondary 03F07 and 18A32.
The v4 [TeX](manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v4.tex)
and [PDF](manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v4.pdf)
remain preserved, as do the v5
[TeX](manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v5.tex) and
[PDF](manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v5.pdf).
[SHA-256 checksums](manuscript/SHA256SUMS) cover all three versions.
The [v5 literature review](docs/LITERATURE_REVIEW_V5_2026-10-23.md),
[manuscript hostile review](docs/reviews/V5_HOSTILE_REVIEW.md),
[writing review](docs/reviews/V5_WRITING_REVIEW.md), and
[manuscript validation](docs/V5_VALIDATION.md) accompany v5.
The [earlier literature comparison](docs/LITERATURE_REVIEW.md) remains available.
The literature searches are bounded and make no exhaustive priority claim. The current [author-side hostile review](docs/reviews/GENTZEN_REDUCIBILITY_FOLLOWUP_HOSTILE.md)
and [mathematical-writing review](docs/reviews/GENTZEN_REDUCIBILITY_FOLLOWUP_WRITING.md)
cover entry uniqueness, addressed W4 and constructed mixed-W5 results and the unproved full target; they are
not independent certification. The [current partial Reducibility report](docs/GENTZEN_REDUCIBILITY_FOLLOWUP_REPORT.md),
[governing full-target instructions](docs/CODEX_GENTZEN_REDUCIBILITY_2026-10-24.txt),
[current continuation](docs/CODEX_NEXT_SESSION.txt),
[historical classification report and case ledger](docs/GENTZEN_BLOCKED_CLASSIFICATION_REPORT.md),
[superseded mixed-W5-only continuation](docs/CODEX_GENTZEN_MIXED_W5_DISPATCH.txt),
[preceding integration report](docs/GENTZEN_PROOF_REPLACEMENT_REPORT.md),
[preceding W5 report and track/drift audit](docs/GENTZEN_W5_OTHER_PREMISE_MIX_REPORT.md),
[preceding W5 report](docs/GENTZEN_W5_SINGLE_PREMISE_MIX_REPORT.md),
[preceding W4 report](docs/GENTZEN_W4_SELECTED_LOGICAL_REPORT.md),
[preceding W2 report](docs/GENTZEN_W2_SELECTED_THINNING_REPORT.md),
[preceding W3 report](docs/GENTZEN_W3_SHARED_SELECTED_CONTRACTION_REPORT.md),
[preceding terminal-tail report](docs/GENTZEN_W1_TERMINAL_TAIL_CONTRACTION_REPORT.md),
[preceding disjoint-contraction report](docs/GENTZEN_W1_DISJOINT_CONTRACTION_REPORT.md),
[preceding same-side logical report](docs/GENTZEN_W1_SAME_SIDE_LOGICAL_REPORT.md),
[preceding same-side exchange report](docs/GENTZEN_W1_SAME_SIDE_EXCHANGE_REPORT.md),
[preceding same-side thinning report](docs/GENTZEN_W1_SAME_SIDE_THINNING_REPORT.md),
[preceding logical report](docs/GENTZEN_W1_LOGICAL_REPORT.md),
[preceding contraction report](docs/GENTZEN_W1_CONTRACTION_REPORT.md),
[contraction review](docs/reviews/GENTZEN_W1_CONTRACTION_HOSTILE.md),
[preceding exchange report](docs/GENTZEN_W1_EXCHANGE_REPORT.md),
[exchange review](docs/reviews/GENTZEN_W1_EXCHANGE_HOSTILE.md),
[preceding thinning review](docs/reviews/GENTZEN_W1_THINNING_HOSTILE.md),
[historical contextual-collapse review](docs/reviews/CONTEXTUAL_COLLAPSE_HOSTILE.md)
and [initial review](docs/REVIEW.md) remain available.

## Verification and Palomar

Run `bash scripts/verify.sh`. CI uses the hash-checked official Lean release,
a strict build, source screening, and transitive axiom collection. Evidence
and its limitations are in [validation](docs/VALIDATION.md).

The [Palomar requirements](docs/PALOMAR_REQUIREMENTS.md) adapt the
FailureOfComposition procedure to the current toolchain and kernel policy.
Upstream policy snapshots and exact commits are in `provenance/`.
`bash scripts/fetch-palomar.sh` fetches the pinned verifier source for inspection.
Comparator packaging, independent kernel replay, and registry verification
remain to be implemented for a substantive theorem.

The repository is private. Public release, license selection, and registry
submission are later decisions. No submission has been made.

