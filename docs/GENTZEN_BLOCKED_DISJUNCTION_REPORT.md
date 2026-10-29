# BlockedR.disjunction: sequential cut reconstruction

`CutCommutation.blockedR_disjunction_rank_step` proves the actual sequential
right-contraction case, including both instantiated recursion calls. All twelve
binary branches and eight of fourteen blocked families are proved. Six logical
blocked families, global induction, unrestricted elimination and the full-paper
endpoint remain open. The contract still covers v7 and all three appendices,
with its three milestones kept separate.

## Original source, selected tags and exact output

Let A,B be normal forms and C=A∨B. Let F,X,Y,I,J be lists. The original child
is f:G F (A::B::(X++C::Y)); the unchanged right premise is h:G I J with z:At I C.
`BlockedDisjunction.parent_source` identifies the actual BlockedSource.right2
contraction on `G.disjR F [] (X++C::Y) A B f`. The fresh principal is first;
the parametric C lies in X++C::Y. They are distinct tagged occurrences.
`block.keep` is the original lower selected tag. The eliminated proof has exact
sequent `G (z.erase++F) (J++block.keep.erase)`.

The contraction retains the last selected copy. `fresh_get`, `parametric_get`,
`retained_fixed` and `residue_retained` compare every selected and retained
position, including other equal-labelled formulas. All contexts may be empty;
no Nonempty or DecidableEq hypothesis is used. Composition applies its first
argument first.

## Native arrow equation and actual construction

Move the original parametric C to the native child's output head, obtaining
f₀:G F (C::A::B::D), where D is the original residual output. `body f₀` is
`G.disjR F [C] D A B f₀`; `parent f₀` contracts its two leading Cs. For
h₀:G (C::T) J, SequentialDisjunction.native_equation proves, at actual Reduced
denotations,

```
G.cut (parent f₀) h₀
  = prefixRepair (G.cut (fresh (G.cut f₀ h₀)) h₀).
```

`fresh k` moves the consumed A/B components below a native G.disjR with empty
prefix. The only transport following that rule is equality reindexing of its
residual list; it adds no Gentzen node. Its rank and leaf proof are checked
through that transport. No exchange is placed above the new principal for
the second induction call.

The derivation uses the completed ContractionSplice.head_right_binary arrow
equation, the actual HeadRouting.front_split comparison, and existing unary
commutation and G.disjR_toHead. New generic coordinate identities prove both
prefix duplicate repairs against actual folds and units. prefixRouted adds the
original output-residue program. Count and congruence laws are proved.

front_contraction_factor compares the actual fresh-head and parametric-tail
coordinates. The existing LogicalDeletion.tail_square lifts the logical rule.
SequentialDisjunction.source_denote, BlockedDisjunction.selected_parent and
source_equation give the arbitrary-tag comparison and complete original cut
equality. No general proof duality, graph reflection or artificial-formula
induction call is assumed.

## Original recursion and fresh Clean

original_descent crosses the original right contraction and the original
parametric disjR predecessor. It inherits all six Clean facts and strict original
selected rank for f at the exact tag `there (there parametric)`, with unchanged
h/z. The first ih is called there, before any routing. The completed unique-fiber
structural replacement adapts that returned witness to the native child.

For every returned cut-free atomized k, fresh_rho proves the new principal's
one-sided rank is one, and fresh_blocked proves all required selected
descendants blocked. fresh_clean proves the full invariant. fresh_rank_lt
compares `1+h.rho .left z` with the original contracted rank, using original
child descent and positivity. It assumes no bound on k's rank. The second ih
occurs before context repair; prefixRouted_count and final G.atomize give the
cut-free Atomized witness at the original exact output and preserve its equation.

## Verification, reviews and retained scope

The pinned Lean 4.35.0 strict build, source screen and transitive audit, all
22 public check files and 29 expected control rejections are recorded in
provenance/wsl-gentzen-sequential-disjunction/FINAL_VERIFICATION.json. The phase
adds twelve modules and 53 source declarations; 726 Lean files are screened.
Only propext, Classical.choice and Quot.sound are allowed by the audit.

Exact public signatures check the original source, equation, descent, fresh
Clean/rank and final rank step. Four actual Eliminated witnesses cover general
signed literals, negative zero, Empty with constants and populated repeated
contexts. These initial-output smoke witnesses use initiality; they are not an
instantiation of an unavailable global ih. General source/rank proofs check the
sequential construction. Focused rejections protect prefix repair, distinct
same-labelled coordinates and the false returned-proof rank calculation, in
addition to all preceding controls. Actual logs/exits and proof-development
failures are retained separately from expected negative controls.

Both required reviews apply to the actual argument and map as local author-side
reviews. Independent replay, Comparator, official/service verification,
independent peer review and publication were not performed. Checked-source
manifests and the read-back verified archive are rechecked against committed
bytes before Downloads delivery. Differing existing files receive commit suffixes;
DELIVERY_REGISTER.json records every exact path/hash and any failure.

All nine manuscript blobs and the stash are preserved. No new manuscript
erratum was established and unchanged TeX is not rebuilt. Appendix C p.260 stays
closed. Its p.262 right-premise fresh-disjunction correspondence stays open:
this BlockedR branch instead proves a fresh disjunction in the left premise.
The corresponding BlockedL.disjunctionFirst source case is still required.

## Continuation

Complete BlockedL.disjunctionFirst/Second/Both and
BlockedR.conjunctionFirst/Second/Both, preserving two/three-copy source arities,
original Clean/ranks before adapters, components below fresh native principals
and final structural atomization. Then discharge exhaustive constructor/tag
assembly, fixed-degree all-ranks Clean under strict DegreeBelow, arbitrary-premise
cleaning, strong degree induction and arbitrary-G normalization. Export actual
unrestricted CutElimination and AtomizedCutElimination inhabitants, and continue
coherence, intended-presentation and uniform-substitution/congruence bridges,
both maximality routes, the model corollary and every mathematical claim in all
three appendices. All preceding results, corrections and deliveries remain.
