# Blocked right gamma-conjunction: local construction report

`CutCommutation.blockedR_gammaConj_rank_step` proves the sixth actual blocked
reduction. All six gamma families and all twelve binary branches are now
complete through their equations, reconstructions and original-rank steps.
Eight sequential logical blocked cases, global induction and the later
full-paper obligations remain open.

## Source, selected positions and exact result

For normal forms A, B, C, contexts Γ, Θ, X, Y, Z, T, I, J, take
f : Γ ⊢ A :: (X ++ C :: Y), g : Θ ⊢ B :: (Z ++ C :: T), h : I ⊢ J and
z : At I C. The actual source is conjunction-right followed by a two-copy
right contraction, keeping the newly introduced A∧B as a fixed leading tag.
`BlockedRightConj.gammaParent_source` identifies it with
`BlockedSource.right2 C (Γ++Θ) (A∧B::X) (Y++Z) T`, including its source cast.
`gammaBlock_route` and `gammaBlock_keep` prove the common residual route and
the exact retained occurrence after that fixed principal.

`gamma_equation` equates the original positional cut with `parallel` applied
to the two original child cuts. The first selects
`(BlockedMix.firstTag C X Y).there` in f; the second selects
`(BlockedMix.firstTag C Z T).there` in g. The parent selects the retained C
under A∧B. The result has exact input z.erase ++ (Γ++Θ) and output
J ++ (A∧B :: x.erase), where x is the original residual contraction tag.
The first child uses gammaSecondRoute and the second gammaFirstRoute, as
required by the established gammaBlock parameter order.

## Native equation and Gentzen reconstruction

Composition comp p q applies p first. `ContractionSplice.source_codiagonal`
uses the previously proved explicit section of the source comparison.
`duplicate_input` calculates two copies of the same original right premise.
`right_binary` applies the completed principal disjunction arrow equation;
`head_right_binary` proves its head-selected form with every swap and merge
accounted for. This is an arrow calculation, not an induction call on C∨C.

`DoubleConjSplice.first` and `second` use the existing
conjR_left_first_core/conjR_left_second_core on their respective exact selected
outputs. `between_square` proves the five-slot output correspondence. Explicit
product and coproduct coordinate equations merge the repeated input and output.
`DoubleConjSplice.equation`, `body_merged` and
`BlockedRightConj.canonical_equation` give the complete particular native
equation. `shared_equation` permits arbitrary residual output routes. No general
G-proof duality, occurrence-graph reflection or unproved coherence is used.

The actual `headParent` contracts the two residual output contexts below a
selected head exchange. `parallel` moves the retained A/B of each returned
cut to its constructor head, rebuilds conjunction-right, contracts the duplicated
opposite input and output contexts and restores the original principal order.
`headParent_denote`, `child_denote`, `output_square` and `parallel_denote` prove
all append, exchange and route comparisons, including empty contexts.
`headParent_equation` proves the actual Gentzen equality.

`Rules.conjRight_output_nat` and the already completed positional route-vector
factorization supply `source_denote` for arbitrary selected tags. The existing
`BinaryLogical.leftFirstChild_factor` identifies each normalized child with the
original positional cut. `gamma_equation` instantiates the actual contraction
and those child equalities. The leading A∧B remains a fixed tag even if its
formula equals C; the exact-index public example and a focused rejection test
check that distinction.

## Original recursion and atomization

`gamma_first_descent` and `gamma_second_descent` traverse the actual contraction
and original conjunction-right child. Both inherit full Clean and a strict
selected-rank inequality with the unchanged h/z. The ih applications in
`blockedR_gammaConj_rank_step` use the original f and g at those exact tags,
before any routing or reconstruction. No returned-proof rank bound is assumed.

`parallel_count` adds the two returned cut counts, and `parallel_congr` transports
their Reduced equalities. The eliminated wrapper constructs a cut-free proof
at the exact output sequent and then applies completed structural atomization.
It proves the required Atomized witness and equation. Output blockedness is
not part of this Eliminated interface.

## Verification, corrections and delivery

Nineteen new production modules contain 65 source declarations. Strict local
verification passes for 698 Lean files, with the complete transitive axiom audit
covering 12,737 project declarations. Twenty public files check exact signatures
and actual witnesses. The new witnesses cover arbitrary signed literals,
negative 0, Empty atom type with empty fixed/input contexts and all-populated
same-label blocks. Seventeen focused malformed constructions and the five
boundary controls are rejected as expected. All heavy checks run sequentially
under the project lock. Real exits, failed development attempts, exact source
and archive hashes are retained in
`provenance/wsl-gentzen-right-gamma-conj/FINAL_VERIFICATION.json` and linked logs.
The public literal check's initially omitted implicit context names were fixed;
its final exact witness and all checks pass. No mathematical axiom or proof hole
was introduced; dependencies are limited to propext, Classical.choice and
Quot.sound where reported by the audit.

Appendix C's concrete p.260 correspondence remains proved by the preceding left
gamma-disjunction source equation and both strict original-rank descents.
The p.262 sequential fresh-right-principal correspondence remains open. Two
older live prose passages still described both correspondences as open; those
current statements were corrected together and superseded checkpoint text was
explicitly labeled historical. This is a correspondence-record correction,
not a new manuscript erratum. V7 and all nine manuscript blobs match the base;
unchanged TeX was not rebuilt. The three milestones remain distinct.

Base: 2f66237d124bb7949718a39354aa614498af73e2. All successor/intervening work and
stash dedfd8fc8cd49930e9a162d5be585215b062a43c are preserved. Checked sources
are archived and compared with committed bytes before Downloads delivery.
Every new report/review and changed record is copied from committed bytes,
preserving differing destinations; exact paths and hashes are retained in
DELIVERY_REGISTER.json and DELIVERY_RECEIPT.json. Earlier receipts persist.
Independent replay, Comparator, official/service verification and publication
were not performed.

## Continuation

Complete BlockedL.conjunction and BlockedR.disjunction, then the First, Second
and Both logical families on each side. Preserve actual two/three-copy arities,
route component contexts below each fresh native principal, and prove its leaf,
one-sided rank one and full Clean before the sequential call. Compare with the
original contracted rank and retain exact source/native adapters. Then discharge
constructor dispatch, fixed-degree all-ranks Clean under strict DegreeBelow,
simultaneous cleaning, strong degree induction and arbitrary-G normalization.
Export actual unrestricted elimination inhabitants, then continue coherence,
intended-presentation and substitution/congruence bridges, both maximality
proofs, model corollary and all three v7 appendices under the unchanged contract.
