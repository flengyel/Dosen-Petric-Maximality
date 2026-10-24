# Coverage and next proof obligations

The conditional collapse, isolation, transport, and `relative_maximality` proofs
are unchanged. The actual September 2007 arrow presentation now has typed
syntax, generated equational equality, a quotient category, and proved
structural and constructed-zero instances. Its occurrence interpretation is
well defined. Faithfulness remains open. The three milestones remain separate.
The reduced signed-literal syntactic category and existential inclusion
representation are now constructed; reduced faithfulness remains open.
The contextual gη/gε identities and their composed forms are now unconditional
reduced theorems, with typed context and occurrence actions.
Common atomic factorization and complete support are now proved; the remaining
coherence input is stated precisely as PositiveCoherence P.
Thinning atomization (Atomic-k) now preserves denotation and any existing
CutFree proof, with complete unchanged-endpoint occurrence equality.
See [the common atomic report](COMMON_ATOMIC_FACTORIZATION_REPORT.md),
[the contextual report](CONTEXTUAL_FACTORIZATION_REPORT.md),
[the source map](PRESENTATION_CORRESPONDENCE.md),
[reduction report](SIGNED_LITERAL_REDUCTION_REPORT.md),
[signed-label report](SIGNED_LABEL_REPORT.md),
[normalization report](NORMALIZATION_REPORT.md), the historical
[presentation report](PRESENTATION_BRIDGE_REPORT.md), and [validation](VALIDATION.md).

| Milestone | Required endpoint | Current status |
| --- | --- | --- |
| I | Contextual collapse, relation calculations, and the complete structural/faithful-interpretation interface for the intended nonthin category | Conditional collapse proved. The generated fragment still instantiates all §5 fields. The actual source quotient now has `Structure`, constructed `ZeroIdentity`, a well-defined operation-preserving occurrence map, distinct projections for p : P, and an empty Hom(top,bot). Its faithful-interpretation field remains open, so milestone I is not declared complete. |
| II | Maximality conditional on explicit coherence, normalization, presentation, and substitution inputs | `relative_maximality` proved. The source quotient supplies `Substitution`, `DoubleNegation`, and now `Normalization`, including signed occurrence coordinates and transport. Global signed-label preservation is now proved directly for occurrenceMap. The signed-literal reduction, surjective inclusion on normal-form hom-sets and conditional coherence transfer are now proved. Reduced faithfulness, Boolean Coherence and the full congruence correspondence remain open; no intended instance of the conditional theorem is claimed. |
| III | Maximality for the actual Došen–Petrić presentation with all bridges proved | Open. The syntax/category/structural bridge is constructed; Boolean Coherence and the remaining intended instances are not proved. |

## The unchanged conditional argument and fragment check

`Structure` gives products, coproducts, terminal and initial arrows, and the
typed distributor. `Congruence` gives equivalence and compatibility with
composition, pairing, and copairing, as used by §5. `OccurrenceInterpretation`
includes faithfulness in the original category. Its derived fold, swap,
first-injection, and second-block equations feed `ContextualCollapse.total`.
No quotient faithfulness or cancellation of j_A is used.

`GeneratedModel` instantiates every §5 interface field with relations denoted
by typed terms of the structural fragment. It proves distinct projections and
an empty Hom(top,bot). It establishes consistency and nonthinness of that full
§5 interface, including empty occurrence sets. It omits the full Boolean arrow
signature and is not an identification with B(P). Its fragment truth invariant
treats negation atomically; the new full-presentation invariant instead uses
propositional negation. No substitution instance for the fragment is claimed.

`Isolation` gives selectors/coselectors and exact single-edge relations for
signed normal forms. `Normalization`, signed labels, arrow substitution, and
double negation were explicit inputs of the conditional result. Normalization,
arrow substitution, and double negation now have source-quotient instances.
The global signed-label invariant for occurrenceMap is now proved separately;
the faithful interpretation remains open. The old SignedLabelPreservation
definition is unchanged and can be adapted once that interpretation exists.

## Actual-presentation constructions

| Obligation | Declaration / status |
| --- | --- |
| Exact primitive grammar and typed endpoints | `Presentation.Term`; only composition, ∧, and ∨ are primitive arrow operations. Negation on arrows is derived in the source and unconstructed here. |
| Published defining equations | `Presentation.Equation`: 71 constructor schemas with a complete source index. `Op` packages both connectives. No relation-kernel equality is a generator; the two `(m e)` laws removed by §11.5 are omitted. |
| Generated equivalence and congruence | `Derives`, `termSetoid`; equivalence, composition, and tensor congruence. |
| Quotient category and operation descent | `Hom`, `ofTerm`, `comp`, `tensor`, `Laws`, `category`. Derived pair/copair/unit/dR/medial/zero composites are typed definitions. |
| Products, coproducts, terminality, initiality | `operations`; `DiagonalData.diag_projections` derives product eta, with coproduct laws by duality. Universal properties are not extra generators. |
| Source zero formula and law | `zeroConstruction_eq`, `zeroIdentity`; the constructed `(0ηε)` composite equals primitive zero and satisfies `(0I)`. Zero arrows between different objects still require an existing-arrow witness. |
| Occurrence equation preservation | `Term.relation`, `Term.relation_distRight`, `Equation.relation`, `Derives.relation`; every defining schema preserves the assigned relation, including empty unit cases. |
| Quotient occurrence map and operations | `occurrenceMap`, `occurrence_id`, `occurrence_comp`, `occurrence_tensor_conj`, `occurrence_tensor_disj`, projection/injection/pair/copair/top/bot/dist/zero/eta/epsilon images. Well-defined covariant assignment to relations; faithfulness open. |
| Nonthinness and empty hom-sets | `nonthin p` for p : P; `empty_hom P` for every P. These require no coherence hypothesis. |
| Whole-arrow substitution and defining-congruence closure | `Term.subst`, `Constant.subst`, `Equation.subst`, `Derives.subst`, `substitute`, `substitution`. Source `(su)` is admissible with substituted endpoints. |
| Double negation | `doubleNegation`, using `Laws.dnOut_in/out`; both inverse equations compiled without coherence. |
| Signed-literal reduced syntax and representation | `Reduced.Term/Equation/Derives/Hom/category` gives the source p.318 syntactic quotient, with exactly atomic eta/epsilon. Inclusion respects equations/operations; duality and compound witnesses compile; red_sound and representation prove transport compatibility and existential hom-set surjectivity for normal-form endpoints. |
| Reduced occurrence assignment and transfer | Independent raw tagged relation, quotient descent and inclusion/normalizer compatibility compile. `normal_faithful_of_reduced/global_faithful_of_reduced` explicitly require the unproved `Reduced.Faithful P`. |
| Typed one-hole contexts and contextual factorization | `Context.plug/mapTerm/map_derives/map`, raw and quotient id/comp laws; source gConj/gDisj, naturality/unit components; unconditional gEta/gEpsilon/gEta_comp/gEpsilon_comp inside Reduced. Reduced zero/uniqueness and required structural unit/d identities are directly derived. Tagged fixed/hole coordinates and well-typed composed relation comparisons compile. No general positive-core coherence is assumed. |
| Common atomic factorization and complete support | `Term.Positive` is the recursive eta/epsilon-free arrow predicate, with signed objects unrestricted. `atomicFactor` terminates by atomicCount and records exact lists; `commonAtomicFactor` supplies shared endpoints/outer factors and two positive raw middles with complete support through common tagged embeddings, independently of relation equality. Source padding and separated iterated-factor laws compile. |
| Positive-fragment zero and derived union algebra | `Reduced.tensor_zero/tensor_zeroOf`, zero witness/absorption laws, raw/quotient union, all requested algebra and pointwise occurrence formulas compile without coherence. Both zeros are required for the tensor law; union-unit is derived by the direct p.291 argument. |
| Typed positive Gentzen syntax and representation (G0/G1) | `Reduced.Gentzen.G` has 16 genuine rule/leaf schemas with positive denotation, actual structural comparisons and source-order operations. `gentzenization` and decoded/occurrence counterparts cover all 19 Positive schemas. Empty contexts remain top/bot and G [] [] is impossible. Representation may contain cuts; no quotient translation or elimination is claimed. |
| Atomic-k thinning atomization | `G.atomization/atomization_cutFree/atomization_occurrences` compile for arbitrary P, with unchanged contexts and all sixteen G schemas. Positional formula-recursive helpers cover the four compound cases, contract all duplicated context positions and introduce no cuts. Existing analysis definitions and generating equations are unchanged. The cluster/rank prerequisite is now proved below; blocked-contraction transformations and the rest of G2 remain open. |
| Typed Gentzen cluster/rank prerequisite (G2) | Independent parent routing and complete predecessor enumeration/classification; finite typed cluster root/edge/reachability/address proofs; all-node rho, exact contraction sums, strict child bounds and cut ranks compile for arbitrary P and proofs containing cuts. Reindex/cut-free/topmost specializations and tied-site characterizations compile. Blocked/reducibility transformations and decreasing elimination measures are open. |
| Opposite-side W1 thinning | `W1.denoteL/R`, predicate/count/relation preservation, exact contraction loss n and whole selected-endpoint loss n−1 compile for arbitrary P and premises, including cuts. These are two local instances only; other W1 cases and all-site reducibility remain open. |
| Opposite-side W1 exchange | `W1.Exchange` derives both commutations with Reduced equality, exact rank losses n/n−1, proof-predicate/count and tagged-relation preservation. Opposite-side predecessor is the exact same At singleton even for empty blocks. Only two local exchange instances are claimed; other W1 and all-site replacement remain open. |
| Opposite-side W1 contractions | `W1.Contraction` constructs one pair, equal Reduced denotations and two directed rank comparisons. Four ranks L+n,L+1,R+1,R+m use independent arities and complete selected-copy sums. Each targeted decrease has an other-side increase; S(outerL)+m=S(outerR)+n. No global decrease/termination or all-site replacement is claimed. |
| Opposite-side W1 unary logical rules | `W1.Logical` proves both unary disjR/conjL commutations, targeted n/n−1 contraction/endpoint losses and principal ranks 2→1, empty principal predecessor lists and predicate/count/full tagged relation preservation. No new atomicity condition. Together with prior thinning/exchange/contraction these complete the specified opposite-side unary families; other same-side exchange/contraction/logical cases remain open. |
| Fixed-position same-side W1 thinning | Four concrete interior/terminal L/R results compile with explicit G/At/Route casts, the proved structural square, complete ordered selected transport and index exclusion even E=C. Full rank equations give n/n−1 losses and fixed inserted 2→1; predicates/count/tagged relations preserved, exact AtomicFormula E boundary retained. Other W1/W2 and all-site reducibility remain open. |
| Fixed-parametric same-side W1 exchange | Four concrete interior-gap/terminal-tail L/R results compile with exact casts and structural squares, ordered selected transport using interval exclusion, retained and fixed singleton correspondence. Contraction/retained endpoint losses n/n−1 and unchanged fixed ranks 2+rho compile, including empty blocks. Count/predicates/tagged relations preserved; both Atomized predicates equal f.Atomized. Crossing-selected, multi-gap and absorption configurations remain open. |
| Fixed-parametric same-side unary logical W1 | Four concrete interior/terminal conjL/disjR cases compile with actual partial ancestry, both consumed slots none, complete ordered selected transport plus survival/lengths, separate categorical A/B component calculations and actual toTerm squares. Retained n/n−1, principal 2→1 and other fixed 2+rho ranks compile; count/predicates/tagged relations preserved. No extra atomicity or coherence. Other W1/W2–W6 and general reducibility remain open. |
| Fixed-gap disjoint same-side W1 contractions | Two concrete left/right results compile with eight actual context equalities and casts, all-position copies/copies and categorical squares, complete ordered selected transports and genuine same-side fixed fibers. Independent n,m: old ranks LC+n,LE+1; new LC+1,LE+m. Sum balance, actual unequal-arity increase, other fixed 2+rho and count/predicate/full tagged relations compile. General reducibility/coherence remain open; W3 is now supplied below. |
| Terminal-tail disjoint same-side W1 contractions | Two concrete terminalTail_left/right results compile with eight actual context equalities/casts, a concrete copies/copies square, full ordered selected transports, positional separation even C=E and complete fibers. Retained xC<xE; independent n,m give old=(LC+n,LE+1), new=(LC+1,LE+m), exact balances and S(old)+m=S(new)+n. Other same-side ranks are 2+rho at the unique common original. Count/predicates/full tagged relations and inhabited examples compile. Disjoint interleaving and general reducibility/coherence remain open; W3 is now supplied below. |
| W3 shared-selected contraction fusion | `W3.SharedContraction.fusion_left/right` prove exact G P K Δ / G P Γ K outputs for original C,gs,hs,Θ,Λ, intermediate hI and shared-position membership, independent n,m≥2. Computed single contraction has n+m−1 ordered selected originals, full retained/fixed fibers and universal-component Reduced equality. Complete fiber permutations/sums give retained and contraction-subterm drop exactly m; other final same-side positions have old=2+rho, flat=1+rho. Count/predicates/full tagged relations and inhabited boundaries compile. Arbitrary-context Reducibility, cut elimination and coherence remain open. |
| Terminal selected-thinning W2 | `W2.SelectedThinning.terminal_left/right` compile for original C,gs,Θ, n≥2 and existing premises at exact K endpoints. Concrete old-position square, complete ordered n+1 selection including the new leaf, full outer versus n-member original composite fibers and unique fixed originals give component/Reduced equality. Exact contraction/endpoint losses n+1/n and unchanged other fixed ranks compile. Counts/CutFree/tagged relations preserved; old Atomized iff AtomicFormula C and f.Atomized, new iff f.Atomized. Inhabited constants/compounds/signed cuts compile. General Reducibility/coherence remain open. |
| Terminal selected-logical W4 | `W4.SelectedLogical.terminal_left/right` compile from original A,B,gs,Θ,n≥2 and existing f. Actual conjL/disjR and contraction constructors, complete ordered n/n+1/two-copy families, consumed A/B slots, principal empty fibers, complete retained/fixed fibers and both consumed component calculations give exact Reduced equality. Source contraction loss n+1; final endpoint LC+n+1 versus LC+3 gives n=2 tie and n≥3 decrease. Other fixed ranks increase one. Counts/CutFree/Atomized/full tagged relations and inhabited boundaries compile. General Reducibility/Blocked-w/coherence remain open. |
| Positive-fragment coherence input | `PositiveCoherence P` quantifies only over positive raw terms and concludes equality in Reduced.Hom. `faithful_of_positive_coherence` is proved conditionally from that explicit, unsupplied premise. This does not supply Reduced.Faithful or Boolean Coherence. |
| Boolean Coherence / faithful interpretation | Open: `occurrenceMap f = occurrenceMap g → f = g` for every parallel pair. Reduced faithfulness and its earlier positive-core coherence inputs are unproved. No complete `OccurrenceInterpretation` instance. Equality reflection and full red-equation preservation remain open. |
| Normalization and occurrence correspondence | `Presentation.normalization` constructs the existing record for every P by simultaneous sign recursion and source n/r/rho arrows. Both inverse laws, inverse occurrence coordinates, both graph laws, literal/label/polarity correspondence, repeated-tag injectivity, Empty cases, and transport formulas compile. No coherence or arrow-negation premise. |
| Global signed-label preservation | `Term.relation_signedLabel`, `occurrence_signedLabel`, `occurrence_literal`: all source terms/arrows preserve complete signed literals along edges; letter/polarity and opposite-sign exclusions, plus normalized transport, compile without coherence. `diag_copies/codiag_merges` preserve the copying/merging boundary. No faithful-interface instance is fabricated. |
| Derived contravariant negation | Open: the exact source clauses, descent, functor laws, and n-r/rho naturality / eta-epsilon dinaturality. |
| Additional congruences | Open: package restriction of every full-presentation proof congruence and its separately assumed substitution closure. Do not infer closure from one valuation kernel. |
| Substitution-schema / Appendix A laws | Open: identity/composition with endpoint identifications, profiles, finite ordinals, renaming, and block-coordinate correspondence. |
| Actual maximality and every-interpretation corollary | Open; do not promote the conditional theorem. |

## Next concrete proof task

Terminal selected-logical W4 and its right dual are complete. See
[the W4 report](GENTZEN_W4_SELECTED_LOGICAL_REPORT.md).

Next prove source W5 single-premise mix with every selected C in g in
G.mix f g, and its right dual. For n=gs.length≥2 set F=repeated C gs++Θ,
K=gaps gs++C::Θ. On the left f:G P Φ Ψ, g:G P F Δ; mix gives
G P (F++Φ) (Δ++Ψ). Old contracts gs with tail Θ++Φ; new mixes f with
the direct contraction of g. Both outputs must have G P (K++Φ) (Δ++Ψ).
On the right f:G P Φ Ψ, g:G P Δ F; both outputs have
G P (Δ++Φ) (K++Ψ). Actual mix puts the second argument's contexts first.

Prove actual endpoint casts, binary positional/component equations, complete
ordered selected transport, both premise fibers and fixed common originals.
If LC is the inner contraction rank on g, target old outer rank LC+n,
new retained rank LC+1 and contraction/endpoint losses n/n−1. Compute
other ranks by premise and side; opposite-side g positions can increase.
Prove exact count, CutFree/Atomized and tagged-relation laws with actual
Empty/compound/equal-label/signed-cut examples. These are next proof targets,
not completed W5 claims. See
[CODEX_W5_SINGLE_PREMISE_MIX.txt](CODEX_W5_SINGLE_PREMISE_MIX.txt).

Mixed-premise W5, other mix placement, binary logical W5/W6, remaining
W1/W2 and disjoint interleaving/exchange, arbitrary-context replacement,
Reducibility, Blocked-w, cut elimination, restricted coherence inputs,
PositiveCoherence, Reduced.Faithful, Boolean Coherence, unconditional maximality
and Palomar preparation remain separate/open. Existing conditional transfers
and three milestone boundaries are unchanged. An unfinished reconstruction
of published results does not establish a manuscript defect.

## Verification boundary

The strict local build, transitive axiom audit, local import closure, three
axiom-injection negative controls, and two presentation boundary controls ran
successfully for the source recorded in the report. Independent
Challenge/Solution statement/shared-definition comparison, independent kernel
replay, official preflight, service verification, publication, and an
independent source-transcription review have not run.
