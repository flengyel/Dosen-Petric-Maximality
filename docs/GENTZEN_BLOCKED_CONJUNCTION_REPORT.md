# BlockedL.conjunction: sequential cut reconstruction

`CutCommutation.blockedL_conjunction_rank_step` proves the actual selected
contraction case, with both recursion calls instantiated. All twelve binary
branches and seven of fourteen blocked families are now proved. Seven blocked
families, the global inductions, unrestricted cut elimination and the remaining
full-paper obligations are open. This report concerns manuscript v7 and all
three appendices; it does not certify the whole paper or any of its three
separate milestones.

## Original source and exact result

Let A and B be normal forms, put C=A∧B, and let X,Y,D,I,J be lists of normal
forms. The original premises are f:G ((X++C::Y)++[A,B]) D and h:G I J, with
z:At J C. `BlockedConjunction.parametric A B X Y` is the tagged C in X++C::Y.
`block A B X Y` contracts that C with the freshly introduced terminal C after
`BlockedSource.conjLLast`. Its selected lower tag is `block.keep`.
`parent_source` identifies this parent with the exact `BlockedSource.left2`
term, including its association transports. The result sequent is
`G (block.keep.erase++I) (D++z.erase)`.

The parametric C and fresh terminal C are distinct tags even though their
formulas are equal. The source contraction retains the last C. Empty X/Y,
repeated labels, signed literals and empty atom types require no extra
hypothesis. Composition `comp f g` applies f first.

## Native equation and source lift

Write F for the residual input after moving the parametric C to the head.
The native child is f₀:G (C::A::B::F) D. Define body f₀ by the native conjunction
rule with prefix [C], and parent f₀ by contracting its two leading Cs. For
h₀:G I (C::R), `SequentialConjunction.native_equation` proves

```
G.cut h₀ (parent f₀)
  = repair (G.cut h₀ (fresh (G.cut h₀ f₀)))
```

Here equality means equality of the actual denoted Reduced arrows. `fresh k`
is literally `G.conjL [] (F++I) (D++R) A B k`. Component routes occur below
this rule. `repair` contracts the duplicated I and R contexts; its input and
output routes are proved against the actual append folds, including units.
`routed` additionally restores the original residual input context. Its exact
cut count and congruence are proved.

The arrow derivation reuses `ContractionSplice.binary`, proved from the
principal conjunction arrow equation, and the existing unary commutation.
It introduces no induction call on an artificial formula. The new
`terminal_logical_head_square`, `principal_square` and
`duplicated_head_terminal` compare all parametric, component and terminal tags.
`SequentialConjunction.source_denote` proves the arbitrary selected source
comparison. `BlockedConjunction.selected_parent` instantiates it at the actual
contraction route, and `source_equation` proves the whole original cut equal
to the routed two-cut construction.

## Original recursion, fresh Clean and final witness

`original_descent` first crosses the original selected contraction, then the
original parametric conjunction predecessor. It inherits all six Clean facts
and proves strict rank decrease for the original child f, at its exact tag,
with the unchanged h and z. The first ih call occurs there, before routing.
`native_child_eliminated` reuses the completed unique-fiber structural
replacement to adapt the returned cut-free atomized witness.

For every returned k, `fresh_clean_and_rank` proves full Clean for the next
cut against `fresh k`. The selected fresh principal is a leaf and has one-sided
rank one; its total rank is `h.rho .right z+1`. Original-child descent and rho
positivity prove that this is strictly less than the original contracted rank.
There is no hypothesis on the returned proof's rank. The second ih call is
made before duplicate repair. `routed_count` proves the reconstruction cut-free,
and final `G.atomize` supplies Atomized at the exact result sequent and preserves
the actual Reduced equation.

## Verification and correspondence limits

Pinned Lean 4.35.0, serial builds and the required strict verification are
recorded in `provenance/wsl-gentzen-sequential-blocked/FINAL_VERIFICATION.json`.
That record supplies final screened-source/declaration totals, every public
check exit and 26 expected rejections. The phase adds fourteen production
modules. Checks repeat exact original source, descent, fresh Clean/rank and
rank-step signatures. Four actual Eliminated witnesses cover arbitrary signed
literals, negative zero, Empty with constants, and populated repeated contexts.
Those terminal-output smoke witnesses use terminality; they do not instantiate
a nonexistent unrestricted induction hypothesis. The production source equation
and rank-step proof check the sequential algorithm itself. Positive coordinate
checks and focused rejected variants test both selected copies, duplicate repair,
missing second-cut typing, false equality of equal-labelled tags and the false
returned-rank calculation.

Every proof-development failure and actual exit is retained. Expected negative
controls are separate from failed candidates. The full transitive audit permits
only propext, Classical.choice and Quot.sound. Source manifests and a read-back
verified archive identify checked bytes; delivery rechecks their committed
bytes. No independent kernel replay, Comparator, official/service verification
or publication was performed.

All nine manuscript blobs are preserved; unchanged TeX is not rebuilt. Appendix
C p.260 remains closed by the preceding actual gammaDisj source equation and
both descents. Its p.262 sequential disjunction correspondence remains open:
the present conjunction branch does not close that different source case.
The existing stash is preserved. New reports, reviews and current records are
delivered from committed bytes with conflict-preserving Downloads filenames;
exact paths and SHA-256 values are in DELIVERY_REGISTER.json.

## Continuation

Next prove BlockedR.disjunction, then BlockedL.disjunctionFirst/Second/Both and
BlockedR.conjunctionFirst/Second/Both. Preserve two/three-copy arities, original
Clean and strict original selected ranks before adapters, fresh native principals
and final structural atomization. Complete constructor/tag dispatch, fixed-degree
all-ranks Clean under strict DegreeBelow, arbitrary-premise cleaning, strong
degree induction and arbitrary-G normalization. Then continue restricted coherence,
actual intended-presentation and uniform-substitution/congruence bridges, both
maximality routes, the model corollary and every mathematical claim in all three
appendices. All earlier results, corrections and delivery receipts persist.
