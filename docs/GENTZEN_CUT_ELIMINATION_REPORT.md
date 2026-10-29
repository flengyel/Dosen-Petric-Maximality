# Unrestricted Gentzen cut elimination

The actual `cut_elimination : CutElimination P` and
`atomized_cut_elimination : AtomizedCutElimination P` are proved for every type P.
Every G proof has a cut-free representative at its exact original sequent with
the same Reduced arrow. The second theorem also supplies Atomized. Neither theorem
requires caller-supplied handlers, degree hypotheses, cleanliness or a bound on
the input rank. Coherence, intended-presentation maximality and the full-paper
endpoint remain separate continuing obligations.

## Complete dispatch at original occurrences

Let C be a normal form, f:G Γ Δ, x:At Δ C, g:G Θ Λ and y:At Θ C.
PositionalCut.Eliminated f x g y means an actual G proof at
(y.erase++Γ) ⊢ (Λ++x.erase), with CutFree, Atomized and Reduced equality to the
selected cut. Composition applies its first argument first.

The two blocked dispatchers cover all seven constructors of each blocked
predicate. They compare the selected lower-contraction tag to the canonical
retained tag using lowerContraction_index_unique and At.compare. Consequently,
equal formula labels do not identify different occurrences. The left gammaDisj
case uses node-free context association, with proved preservation of rank,
Clean and Eliminated. No contraction is added by that equality transport.

The two parametric dispatchers inspect every actual G constructor. Exchange uses
its inverse and unique fiber; thinning distinguishes its inserted leaf from old
positions; contraction distinguishes its selected lower cluster from fixed tags.
Unary logical prefix/suffix cases use the existing deletion equations. All twelve
binary branches retain their original tag conventions, including mix's reversed
blocks. CutFree excludes cut roots; source leaves cannot be parametric. Each
recursive call uses the original child, the unchanged opposite premise, full
Clean and strict original selected rank before reconstruction programs.

clean_rank_step classifies the left selected position as leaf, parametric or
lower contraction. Parametric and lower cases use those actual dispatchers.
Only in the leaf case is the right selected position classified. A second leaf
gives rank two and the proved exhaustive atomic/principal degree step. Clean
supplies root blockedness directly through its root proof address; it is not a
new input field. The fourteen completed local blocked reductions and all earlier
principal, structural, unary and binary proofs are reused unchanged.

## Nested induction and arbitrary proofs

clean_elimination uses strong induction on the original selected rank at one
fixed formula degree, under strict DegreeBelow. cutFree_degree_step first obtains
simultaneously atomized and blocked representatives, then applies that completed
all-ranks theorem. It uses no rank bound on the cleaned representatives.

head_cut_elimination discharges DegreeBelow by strong induction on cutDegree.
Smaller-degree cuts permit arbitrary ranks. Literals have degree zero and both
constants have degree one. The principal conjunction reduction retains A-then-B;
the principal disjunction reduction retains B-then-A.

G.cut_free_normalization then uses structural induction on every arbitrary G
proof. It normalizes children, rebuilds each structural/logical rule with its
actual arrow congruence, and eliminates each cut by head_cut_elimination on the
normalized children. This covers cuts below rules and nested cuts, without an
input CutFree assumption. Final cut-free structural atomization supplies the
second interface and preserves the original sequent and arrow. Returned ranks
and output blockedness are not promised.

## Verification and preserved scope

Eight new production modules contain the dispatch, equality transports and
induction. Exact general public signatures and actual global-eliminator witnesses
cover arbitrary P, signed literals, negative zero, Empty/constants, a cut below
thinning and duplicated arbitrary contexts. These witnesses use the global theorem,
not bottom-source initiality as a substitute for that theorem. Positive checks
retain the constants' degree one and literals' degree zero.

Pinned Lean 4.35.0 strict verification, all public checks, full project dependency
closure and 44 expected negative-control rejections are required for this report.
Actual counts, commands, exits, hashes and any earlier failed development attempts
are in provenance/wsl-gentzen-global-induction/FINAL_VERIFICATION.json and
COMMANDS.json. Focused controls reject syntactic identification of a cut with its
normal form, reversed output sequents and assigning degree zero to either
constant, in addition to all preceding tag/rank/repair controls. Only propext,
Classical.choice and Quot.sound are allowed. Checked source bytes are archived,
read back and compared with committed bytes before delivery.

Both required argument/map/writing reviews are local author-side reviews.
Independent kernel replay, Comparator, official/service verification and publication
are separate unperformed statuses. The manuscript's nine blobs, both Appendix C
source/rank correspondences, prior results, stash and prior receipts remain
unchanged. No new manuscript defect was established; unchanged TeX is not rebuilt.
Committed-byte reports/reviews and changed records are delivered with conflict
preservation and byte verification; DELIVERY_REGISTER.json records exact paths.

## Continuing full-paper contract

Next prove restricted mix/positive/reduced/Boolean coherence and instantiate the
intended-presentation and uniform-substitution/congruence bridges. Continue the
short q_A/e_A proof, the preserved symmetric-fold route, actual-presentation
maximality, model corollary and every mathematical claim in all three v7 appendices.
The three milestones and the complete-paper endpoint remain distinct. This
cut-elimination theorem closes its own previous global obligation only.
