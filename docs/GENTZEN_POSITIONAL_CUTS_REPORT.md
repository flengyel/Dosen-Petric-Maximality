# Selected cuts and least-rank atomic elimination

The continuation incorporates 1376bcb without resetting newer work or changing
the preserved stash. The author-requested errata appendix was completed first:
manuscript v7 and its evidence/reviews were committed at e113c00 and d3a2336,
pushed, and eight artifacts were delivered from committed bytes with SHA-256
checks. That bounded manuscript update is documented separately in
MANUSCRIPT_V7_ERRATA_REPORT.md.

The present Lean checkpoint adds 21 production modules and the public signature
check Checks/PositionalCuts.lean. The new proof reaches complete selected-rank-two
classification, cut-free atomized elimination of its atomic branch, selected
clean normalization, and opposite-side structural commuting equations. Global
cut elimination remains open. CutElimination and AtomizedCutElimination are
precise endpoint definitions, not proved theorems or caller-supplied fields.

## Exact mathematical scope

For arbitrary P, f : G P Γ Δ, g : G P Θ Λ, x : At Δ C and y : At Θ C,
PositionalCut.cut f x g y has sequent (y.erase ++ Γ) → (Λ ++ x.erase).
The macro uses the existing G.cut, exchange scripts and equality transports.
It adds no primitive Gentzen rule. At.erase removes exactly one tag, and
At.retain includes every other tag in its original order. The route sends x
to the head and every retained b to b.there. A head selection uses the identity
script. Head specialization, denotation congruence, cut count and Atomized
correspondence are proved, including empty residual lists.

PositionalCut.rank is f.rho .right x + g.rho .left y on the original premises.
It is at least two; equality is equivalent to both selected occurrences being
leaves. routed_rank_eq separately proves that native rank after routing adds
zero or one exchange for each selected side. These are different measures.
The proof never attributes a native exchange-free rank to a routed occurrence.

AllBlockedAt quantifies over every proof address and actual LowerContraction
whose whole-formula position ascends to the selected tag. allBlockedAt_iff_cluster
proves its exact cluster meaning. Both head specializations recover the existing
AllBlockedL/R. Address composition proves inheritance at any selected predecessor.
The clean_left/right_predecessor and rank_left/right_predecessor theorems give
cleanliness and a strict selected-rank decrease for the actual recursive premises.
They do not invoke a new unbounded clean normalization at unchanged degree.

PositionalCut.clean_premises routes the original premises, reuses completed
clean_cut_premises, and transports its same witnesses back by inverse exchanges.
Both original sequents, individual Reduced equalities, CutFree, Atomized and all
selected blockedness clauses are retained. It has no selected-rank bound.

RightLeaf/LeftLeaf and their completeness proofs classify every possible selected
leaf of an atomized G proof. Source arity excludes exchanges, contractions,
parametric logical positions, mix and cut from this classification. Atomic
thinnings cannot introduce compounds. rank_two_classification returns either
an atomic formula with an Eliminated witness, or one of the exact conjunction
and disjunction principal pairs. The latter branch is classified, not eliminated.

atomic_rank_two proves elimination for every literal (both signs) and top/bot
at selected rank two. It covers all nine identity/zero/fresh-thinning literal
combinations and all compatible constant cases. Every branch returns the same
cut-free atomized proof at the exact positional output, with Reduced equality.
The existing CutBase equations are reused. New selected-thinning equalities
justify actual routing and residual-context transports before those equations
are applied. No DecidableEq P or Nonempty P is assumed.

Fresh native principal occurrences have rank one and no tied lower contraction,
independently of their inner proofs. The fresh disjL/conjR rank comparisons use
only the unchanged side and the old side's rank greater than one. Source
BlockedSource.disjLLast includes exchanges and is not identified with this leaf.
The actual blocked reductions still require their own equations and transports.

splice isolates the categorical middle of contextual cut. Its input, output,
fixed-context and residual naturality laws are proved from Reduced laws.
StructuralProgram.prefixFixed and suffixFixed implement fixed-context transport
with actual rules, preserve every tag, CutFree and Atomic program conditions,
and satisfy the required fold comparison equations. CutCommutation.opposite_left
and opposite_right prove Reduced equality for all opposite-side structural
programs, including exchange, thinning and contraction. StructuralProgram.steps
and its opposite-side rho laws account for every unary node. These results do
not cover the remaining same-side, logical, binary or blocked commutations.

cutDegree gives literals degree zero, constants degree one, and compounds one
plus the two degrees. Each component is strictly smaller. The required outer
strong degree / inner all-ranks construction remains the governing plan.

## Verification and retained evidence

Strict verification passes with 464 screened Lean files and 11,310 audited
project declarations on pinned Lean 4.35.0, with Init-only production dependencies.
All four exact-signature files pass: PositionalCuts, CleanCuts, BlockedW and
Reducibility. All five negative controls reject with their expected messages;
public source closure, all v4/v5/v6/v7 manuscript hashes and whitespace pass.
No custom mathematical axiom, proof hole or native_decide is introduced.

provenance/wsl-gentzen-positional-cuts retains the checked-source inventory,
module and declaration anchors, commands with actual exits, compressed logs
with raw/gzip hashes, control sources/logs and final verification records.
Failed implementation attempts are retained, including a Lean elaborator panic
following malformed early definitions. Three follow-up signature launches were
rejected by the build lock before Lean started; all signature checks were then
run sequentially and passed. The initial sandbox wrapper write failure started
no Lean process. No failure is reclassified as a successful proof run.

This is local build/dependency verification and author-side mathematical/writing
review. Independent kernel replay, Comparator, official preflight, service
verification and publication remain separate and unperformed statuses.

## Remaining full-paper work and delivery

Continue with the actual compound principal reduction equations and smaller-degree
calls, all remaining parametric commutations, and all seven BlockedL and seven
BlockedR reductions. Prove exact contexts, Reduced equalities, inherited clean
hypotheses and selected-rank decreases. Complete the fixed-degree clean theorem
for all ranks before unrestricted cleaning at that degree. Assemble topmost and
global elimination, then continue coherence, actual presentation/congruence and
substitution bridges, the short q_A/e_A proof, maximality, model corollary and all
appendix claims. The three milestones retain their separately recorded statuses; the whole-paper
endpoint remains open. No caller eliminator or coherence premise closes
a missing proof. The concrete Appendix C blocked reductions remain open.

Retain this report under docs/ and its reviews under docs/reviews/. Deliver their
committed bytes to /mnt/c/Users/fleng/Downloads, preserving differing files.
The post-commit receipt records every path/hash, checked-versus-committed source
comparison, local/origin/live SSH agreement, clean status and the preserved stash:
.codex-work/gentzen-cut-elimination/POSITIONAL_POST_COMMIT_DELIVERY.json.
