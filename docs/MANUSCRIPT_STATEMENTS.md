# Manuscript v6: statements and formal scope

## Current full Reducibility checkpoint (26 October 2026)

Both `DosenPetric.Reduced.Gentzen.reducibility_left` and
`reducibility_right` compile for arbitrary P, contexts, proofs and selected
positions, with the unchanged complete `ReducesL/R` conclusions. No Binary or
Unary premise, caller reduct/decomposition, coherence or reflection assumption.
The source-terminal one-premise W6 packages, unrestricted exchange and every
remaining unary/basis input are internally covered. Outside transport for all
incomparable addresses preserves actual proof values, paths, ancestry and
whole-formula cluster membership.

Checked: **398 Lean files / 10,606 audited project declarations**. Only propext,
Quot.sound and Classical.choice are permitted. Strict build, exact public types,
all five negative controls, import closure and manuscript checksums passed.
Exact hypotheses, commands, hashes, construction and limitations:
[GENTZEN_FULL_REDUCIBILITY_REPORT.md](GENTZEN_FULL_REDUCIBILITY_REPORT.md),
[author-side hostile review](reviews/GENTZEN_FULL_REDUCIBILITY_HOSTILE.md),
[author-side writing review](reviews/GENTZEN_FULL_REDUCIBILITY_WRITING.md).
Evidence: `provenance/wsl-gentzen-full-reducibility/`.

The next missing result is preservation of a blocked contraction containing a
proper lower-contraction replacement, on each side. Outside cluster transport
alone does not preserve the entire Reducible predicate. Finite multiset descent,
Blocked-w, clean-cut/cut elimination, positive/reduced/Boolean coherence, actual
instances/maximality, model corollary and the entire v6 appendix ledger remain
open. Generic routing repairs preserve CutFree; no general Atomized witness is
claimed. All accepted corrections and the full-paper contract remain active.

| Claim / source | Exact compiled declaration | Hypotheses / status |
| --- | --- | --- |
| §11.2 p.250 Reducibility and p.252 right analogue | `DosenPetric.Reduced.Gentzen.reducibility_left/right` in GentzenReducibility.lean | Arbitrary P and all contexts; exact ReducesL/R. Completed prerequisite to G2, not G2/cut elimination. |
| p.252 source one-premise W6 | `W6.TerminalOne.reducesFirst/Second` | Nonempty selection, arbitrary actual contexts and containing address; source macro ranks proved. |
| p.251 arbitrary cL/cR placement | `UnrestrictedExchange.left/right` | Actual arbitrary ContractionBlock with at least two selected copies, no outside-interval restriction. |
| Outside replacement | `ProofAddress.outside_of_incomparable`, `outside_cluster` | Paths mutually non-prefix; constructs actual surviving address internally. |

## Retained historical records

The following snapshots describe their own earlier commits; open-status text
below is historical and is superseded by the current checkpoint above.

Latest upstream integration (edb86cb): retain the author's division of work,
correction procedure and tagged-substitution requirements. The new W6 analysis
is an instruction at its historical source anchor. The two-premise terminal-
source left family and all native binary producers compile here; the general
one-premise terminal-source left displayed families/ranks in its §3 remain
open as separately specified source constructions. Native one-premise repairs
and source singleton blockedness exclusions do not discharge those exact
source-rank statements. See the current continuation. No manuscript defect or
completed full-paper proof is inferred.

## Full-paper claim coverage

[The full-paper instructions](CODEX_FULL_MANUSCRIPT_FORMALIZATION.md) require
exact checked counterparts for the entire mathematical content of v6, including
the short proof, the model corollary, unnumbered assertions and both appendices.
Expand this map into a complete claim ledger as implementation proceeds, using
the contract's section-by-section inventory. Record hypotheses and actual
source-presentation instances; do not count a conditional or weaker theorem as
the printed claim. The update changes the target, not the proof status below.

## Historical binary-input integration (25 October 2026)

**Both full Reducibility Lemmata remain open.** Every actual contraction over
native `mix`, `conjR` or `disjL` now has a left and a right producer, with internal
positional selection matching and the complete eligible-descendant bound.
`BinaryReducer.left/right` assemble these cases; a binary cut premise is ruled
out by the cut-freeness already contained in reducibility. The right-W4 repair
now includes one parametric copy plus the fresh compound, using a node-free
singleton inner operation. Source W6, native/source repairs and all three
source singleton blockedness exclusions compile. General unary dispatch,
including exchanges crossing selected copies, is still missing. Outside-site
transport, multiset descent, Blocked-w, cut elimination and coherence remain open.

Measured checked sources: **330 Lean source files / 9,737 audited project
declarations** (818 additional audited declarations, including generated
helpers; this is not a count of new mathematical theorems). Exact results:
[GENTZEN_REDUCIBILITY_INTEGRATION_REPORT.md](GENTZEN_REDUCIBILITY_INTEGRATION_REPORT.md),
[author-side hostile review](reviews/GENTZEN_REDUCIBILITY_INTEGRATION_HOSTILE.md),
[author-side writing review](reviews/GENTZEN_REDUCIBILITY_INTEGRATION_WRITING.md).
The governing instruction is [CODEX_AFTER_1E967BC_REDUCIBILITY.txt](CODEX_AFTER_1E967BC_REDUCIBILITY.txt).
This checked integration does **not** complete that instruction's final target.

## Historical follow-up at 1e967bc (superseded above)

The [concrete W6 instruction](CODEX_W6_CONSTRUCTION.md) now specifies six
left/right selected-principal constructions, their rank targets and complete
addressed conclusions. This is a construction analysis for local Codex;
implementation and verification remain open. See its
[hostile audit](reviews/W6_CONSTRUCTION_HOSTILE.md) and
[writing review](reviews/W6_CONSTRUCTION_WRITING.md). No proof status below
is advanced by this instruction update.

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

See [the exact follow-up report](GENTZEN_REDUCIBILITY_FOLLOWUP_REPORT.md),
[author-side hostile review](reviews/GENTZEN_REDUCIBILITY_FOLLOWUP_HOSTILE.md),
and [writing review](reviews/GENTZEN_REDUCIBILITY_FOLLOWUP_WRITING.md).
The immediate proof task is [the supplied continuation](CODEX_AFTER_05C6BC8_REDUCIBILITY.txt),
with the unchanged full targets in CODEX_GENTZEN_REDUCIBILITY_2026-10-24.txt.
This is verified progress, not completion of that task. Final sources:
**249 Lean files / 8,919 audited declarations**. Earlier checkpoint
sections below retain their historical scope and are superseded where necessary.

Source: Florian Lengyel, *Maximality of the Došen–Petrić Boolean Category*,
v6, 25 October 2026, in `manuscript/`. The maximality theorem and model corollary are unchanged.
The contextual-collapse proof now uses two structural isomorphisms from
Došen–Petrić, §12.5, p.294; the proof of Lemma 7 in their 2012 isomorphism
paper supplies another source. Section 3 distinguishes the category from the
cartesian closed hypotheses of Joyal's theorem. Section 6 describes the
conditional Lean formalization, which retains the earlier symmetric-fold proof.
The new isomorphism-based proof has not been implemented in Lean. Appendices A
and B are unchanged. Review and verification records remain outside the paper.
Labels below refer to the manuscript rather than independently assigned numbering.

Let P be a nonempty set of variables. The target category B(P) is the free
zero-identity Boolean category of Došen–Petrić, *Proof-Theoretical Coherence*,
September 2007 revision, §§14.2–14.3. A proof congruence is an equivalence on
each hom-set preserved by every specified arrow operation. A substitution
congruence additionally preserves every uniform formula substitution on arrow
terms and their endpoint types.

The target statement is: for every such congruence θ, if there exist objects
A,C and distinct f,g : A → C with f θ g, then for every X,Y and every
a,b : X → Y, a θ b. The existential pair and universal conclusion range over
the actual presentation. The final semantic corollary quantifies over every
interpretation of variables, not one fixed valuation.

`Category.comp f g` means first f, then g. Thus manuscript g ∘ f is
`Category.comp f g`, or `f ≫ g` after a Mathlib bridge.

| Manuscript definition or result | Formal counterpart | Exact scope or remaining input |
| --- | --- | --- |
| §2 category operations | `DosenPetric.Category`, `Presentation.Term`, `Equation`, `Derives`, `category` | The source quotient is built from the September 2007 primitive grammar and published equations; see `PRESENTATION_CORRESPONDENCE.md`. Composition and both tensors descend by generated congruence. |
| `eq:zero-identity` | `Presentation.zeroConstruction_structural`, `zeroConstruction_eq`, `zeroIdentity` | The source unit-isomorphism composite equals the manuscript pairing/copairing formula and primitive zero; the constructed zero satisfies the required law. |
| `eq:zero-law` | `DosenPetric.ZeroIdentity.law` | For all parallel f,g : A → B, `comp (zero A) f = comp g (zero B)`. |
| §2 zero arrow | `ZeroIdentity.zeroOf` | Requires f : Hom A B. No arrow is supplied to an empty hom-set. |
| §2 witness independence and absorption | `zeroOf_independent`, `commute`, `postcompose`, `precompose`, `zero_idempotent` | All categories with the explicit zero-identity law. `Presentation.zeroConstruction_eq` now proves that formula equals primitive zero in the source quotient; `Presentation.zeroIdentity` uses the construction. |
| §3 formulas and positions | `Formula`, `Formula.Occ`, `Formula.label`, `Formula.subst` | Arbitrary variable types; negation preserves positions; each connective uses Sum tags; constants have Empty positions. |
| `eq:occ-substitution` | `Formula.expand`, `contract`, `contract_expand`, `expand_contract` | For every substitution σ : P → Formula Q and formula A, mutually inverse maps between Occ(A[σ]) and Σ x : Occ(A), Occ(σ(label A x)). No nonemptiness assumption is needed. |
| §3 repeated variables | `Formula.repeated_positions_distinct` | The two positions in p ∧ p are distinct even though their labels coincide. |
| §3 relation operations | `Relations.comp`, `graph`, `sumMap`, `fstRel`, `sndRel`, `copair`, `reassoc` | Binary relations on types. These operations apply in particular to finite occurrence types. `Presentation.occurrenceMap` now descends from the source equation quotient and preserves identity, composition, and the specified operations; faithfulness remains open. |
| `eq:first-injection` | `Relations.first_injection`, `OccurrenceInterpretation.first_injection` | The relation equation is unconditional; its original-category counterpart is derived under the typed faithful-interpretation input. |
| §6 symmetric fold (v5 `lem:symmetric`) | `Relations.hRel_eq_fold`, `hRel_independent`, `hRel_swap`; `OccurrenceInterpretation.fold_independent`, `fold_swap` | The relation fold is calculated from operations; categorical independence and swap invariance follow by original-category faithfulness. The manuscript identifies this map as mix followed by the codiagonal. |
| §6 formal collapse argument (v5 `eq:second-block`) | `Relations.second_block`, `OccurrenceInterpretation.second_block` | The relation equation discards the first source block; the categorical equation follows by original-category faithfulness. This calculation belongs to the retained formal proof, not the replacement §5 proof. |
| `lem:structural-isos` | Not implemented as this lemma | The manuscript derives the specified q_A and e_A isomorphisms from the published structural isomorphisms using original-category coherence and uniform substitution. |
| §3 distinct projections | `Relations.projections_distinct`, `GeneratedModel.nonthin`, `Presentation.nonthin` | Every v5 §5 interface field is instantiated in a generated structural-fragment model, with distinct categorical projections and `GeneratedModel.empty_hom`. This does not identify the fragment model with B(P). Separately, `Presentation.nonthin p` proves distinct projections in the equation-generated source quotient; `Presentation.empty_hom` proves its Hom(top,bot) empty. |
| `thm:coherence` | `OccurrenceInterpretation.faithful` is explicit input; `Reduced.normal_faithful_of_reduced/global_faithful_of_reduced` are conditional transfers | Boolean Coherence remains unproved. Reduced syntactic inclusion is now surjective on normal-form hom-sets, with occurrence compatibility. Faithfulness of Reduced.occurrenceMap is an explicit unproved premise, not an axiom or instance. GeneratedModel faithfulness remains fragment-only. |
| §14.2 source signed-literal reduction used toward §3 coherence | `Reduced.Term/Equation/Derives/Hom/category`, `inclusion`, `red_sound`, `representation` | Genuine restricted syntactic quotient on NormalForm P; 21 term/61 inherited equation schemas, atomic eta/epsilon only. Every full raw term has a reduced representative equal after inclusion to normalization transport; every full normal-form arrow is in the inclusion image. Equality reflection and quotient descent of red are not proved. |
| §14.2 contextual factorizations toward §3 coherence | `Reduced.Context`, `gConj/gDisj`, `gEta/gEpsilon`, `gEta_comp/gEpsilon_comp`; tagged context and composed occurrence laws | Unconditional equalities in Reduced.Hom for arbitrary P, all one-hole contexts and existing top-domain/bottom-codomain arrows (atomic η/ε specializations give (gη)/(gε)/(gηf)/(gεf)). Needed positive identities are directly derived from the unchanged equations. Common atomic factorization is now proved; §12.5 positive-fragment coherence remains open. |
| §14.2 common atomic factorization toward §3 coherence | `Term.Positive`, `atomicFactor`, `supportedAtomicFactor`, `commonAtomicFactor`, common support and `relations_equal` | For every arbitrary P and parallel raw pair, shared expanded endpoints/outer factors and positive raw middles with complete tagged support compile unconditionally. Exact repeated-occurrence lists are concatenated. `faithful_of_positive_coherence` is conditional on the unsupplied eta/epsilon-free PositiveCoherence P; §12.5 coherence remains open. |
| §12.5 algebra toward positive coherence | `Reduced.tensor_zero/tensor_zeroOf`, derived `Term.union/Derives.union/union`, union algebra and occurrence formulas | Unconditional for arbitrary P and existing reduced arrows; positive raw closure is explicit. Union-unit follows the direct p.291 structural proof. No new equation, empty-hom-set zero, coherence or fullness is assumed. Positive Gentzenization is now proved below; cut elimination and restricted coherence remain open. |
| Positive Gentzenization toward §12.5 coherence | `Reduced.Gentzen.G/denote/denote_positive`, `gentzenization`, `gentzenization_decode`, `gentzenization_occurrences` | G0/G1 compile for arbitrary P and every positive raw term, with atomic/constant leaves only, visible contextual cuts, actual singleton units and tagged occurrence coordinates. All 19 Positive schemas are covered. This is existential representation with cuts; Atomic-k is now proved below, while elimination and coherence remain open. |
| Atomic-k toward G2 cut elimination | `Reduced.Gentzen.G.atomization`, `atomization_cutFree`, `atomization_occurrences`; positional `atomThinL/R` and actual mixed-map consequences | Unconditional for arbitrary P and every G proof at unchanged contexts: atomized representative, equal Reduced denotation, preservation of existing CutFree and complete tagged relation equality. All sixteen schemas and four compound-thinning cases compile. The cluster/rank prerequisite is now proved below; blocked-contraction transformations and the rest of G2 remain open. |
| Gentzen clusters/rank prerequisite within G2 | `G.predecessors_correct/sourceArity_correct/position_classification`, `cluster_correct/cluster_address`, `rho_node_list/rho_child_lt`, `contractionRankL_eq/R_eq`, `cutRank_two_iff_leaves` | Unconditional typed finite tracing/rank for arbitrary P and every G proof, including cuts; all sixteen rules, full separated contraction copies and source leaves covered. Reindex and topmost/cut-free specializations compile. Tied sites are characterized; blocked transformations, Reducibility and cut elimination remain open. |
| Two opposite-side W1 thinning instances | `W1.denoteL/R`, `contraction_lossL/R`, `endpoint_rankL/R`, `endpoint_lossL/R`, both strict decreases; CutFree/Atomized equivalences, exact cutCount and relation equality | Unconditional for arbitrary P,C,D and premise f with hn ≥ 2. Contraction rank loses n = gs.length; whole selected endpoint loses n−1. The dual is separately checked. Other W1 cases, all-site rank control, Reducibility and cut elimination remain open. |
| Two opposite-side W1 exchange instances | `W1.Exchange.denoteL/R`, singleton predecessors and rho equations, complete contraction sums and both exact rank losses; CutFree/Atomized/count/relation preservation | For arbitrary P and premises, including cuts, n=gs.length ≥ 2 gives contraction loss n and whole selected-endpoint loss n−1, including empty blocks. No new atomicity condition or coherence premise. General W1, arbitrary-context rank control and Reducibility remain open. |
| Opposite-side W1 contraction commutation | `W1.Contraction.denote/reverse`, opposite-side singleton predecessor/rho laws, four endpoint equations, directed balances/decreases/increases, endpointSum balance, predicate/count/relation preservation | One pair at arbitrary independent n,m≥2: outerL has ranks L+n,R+1; outerR has L+1,R+m. Each directed move lowers its targeted side and raises the other. Sum preserved for n=m; no general decreasing measure, arbitrary-context result or full Reducibility. |
| Opposite-side W1 unary logical commutations | `W1.Logical.denoteL/R`, exact opposite-side predecessors/rho and full selected-copy sums; principal Leaf/empty predecessors, old/new ranks 2/1; predicate/count/relation preservation | Arbitrary P,A,B,C and premises, including cuts: contraction loses n, whole selected endpoint n−1 for n≥2. Compound principal formulas are allowed in Atomized. Opposite-side unary W1 families complete at their local scopes; other same-side exchange/contraction/logical and binary cases, all-site decrease and broader Reducibility remain open. |
| Fixed-position same-side W1 thinning (four cases) | `W1.SameSideThinning.interior_left/right`, `terminal_left/right`; proved copies/thinning square, ordered selected transport, retained/inserted coordinates, exact rank and preservation laws | Arbitrary P,C,E, lists and cut-containing premises with n≥2. Exact Reduced equality uses universal component extensionality, not faithfulness. Every selected copy stays parametric even E=C. Contraction loss n, whole selected endpoint loss n−1, inserted fixed rank 2→1; both Atomized predicates equal AtomicFormula E ∧ f.Atomized. Other W1/W2, all-site decrease and Reducibility remain open. |
| Four fixed-parametric same-side W1 exchange commutations | `W1.SameSideExchange.interior_left/right`, `terminal_left/right`; all-position copies/exchange square, complete ordered selected transport, retained/fixed fibers, exact ranks and preservation | Arbitrary P, formulas/lists/premise, n≥2; exchange entirely inside one fixed gap or terminal tail. Contraction loss n, retained endpoint loss n−1; other same-side fixed positions have unchanged 2+rho ranks. Both Atomized predicates equal f.Atomized. Crossing selected positions, multi-gap and absorption configurations remain open, as do general W1 and Reducibility. |
| Four fixed-parametric same-side W1 unary logical cases | `W1.SameSideLogical.interior_left/right`, `terminal_left/right`; partial ancestry with both consumed slots none, complete selected transport/survival, separate component equations, Reduced squares/equality and exact ranks | Arbitrary P,A,B,C, lists/premise, n≥2; logical rule wholly inside one fixed gap or terminal tail. Retained n/n−1 losses, principal 2→1, all other final fixed ranks unchanged 2+rho. Both Atomized predicates equal f.Atomized. No coherence premise, label disequality or total A/B→D whole-formula map. Other W1/W2–W6 and general Reducibility remain open. |
| Fixed-gap disjoint same-side W1 contractions | `W1.DisjointContraction.fixedGap_left/right`, all eight context equalities, copies/copies squares, both complete ordered selected transports, retained/fixed fibers, four-rank tables and preservation | Arbitrary P,C,E, lists and existing premises; independent n,m≥2, including C=E and cuts. Exact final context K=(gaps pre++U)++gaps es++E::(V++(gaps post++C::Θ)). Old=(LC+n,LE+1), new=(LC+1,LE+m); S(old)+m=S(new)+n. Other fixed ranks unchanged; no global measure or W3/coherence claim. |
| Terminal-tail disjoint same-side W1 contractions | `W1.DisjointContraction.terminalTail_left/right`, concrete eight context identities, copies/copies square, ordered selected transports and complete fixed fibers; both exact rank tables and preservation | Arbitrary P,C,E,gs,hs,H,U,V and existing premises; independent n,m≥2, including C=E and cuts. Final K=(gaps gs++C::U)++gaps es++E::V. Retained xC<xE; old=(LC+n,LE+1), new=(LC+1,LE+m), S(old)+m=S(new)+n. Disjoint interleaving, all-site rank control and general Reducibility remain open; W3 is supplied below. |
| W3 shared-selected contraction fusion | `W3.SharedContraction.fusion_left/right`; computed flat gaps/tail, complete ordered selected originals/fibers, structural squares and exact rank laws | Arbitrary P,C,gs/hs,Θ/Λ with typed hI and genuine shared-position membership, independent n,m≥2 and existing cut-containing premises. Actual single contraction of arity n+m−1 at G P K Δ or G P Γ K; old retained/outer rank = flat rank+m, other final same-side ranks 2+rho versus 1+rho. No coherence or all-site Reducibility conclusion. |
| Terminal selected-thinning W2 | `W2.SelectedThinning.terminal_left/right`; actual thinning/outer contraction versus direct contraction/exchange, complete ordered selected transport/fibers, structural squares and exact ranks | Arbitrary P,C,gs,Θ, n≥2 and existing cut-containing premises at exact G P K Δ / G P Γ K. Full outer selection has n+1 positions; composite fibers from F have n. Contraction/endpoint losses n+1/n; other fixed ranks unchanged. Counts/CutFree/tagged relations preserved. Old Atomized iff AtomicFormula C and f.Atomized; new iff f.Atomized. Atomicity is not required for equality/ranks. No all-site Reducibility/coherence conclusion. |
| Terminal selected-logical W4 | `W4.SelectedLogical.terminal_left/right`; actual logical introduction/outer contraction versus inner contraction/introduction/two-copy contraction; complete partial ancestry/fibers and component equalities | Arbitrary P,A,B,gs,Θ, n≥2 and existing cut-containing f, C=conj A B / disj A B. Exact G P K Δ / G P Γ K outputs. Both A/B slots consumed, selected n/n+1/two-copy families and all fixed originals/fibers constructed. Old outer rank LC+n+1 versus inner LC; new endpoint LC+3. Final n=2 tie, n≥3 strict decrease, other fixed rank increase one. Counts/CutFree/Atomized/full tagged relations preserved, no atomicity/coherence input. General Reducibility/Blocked-w/coherence open. |
| W5 single-premise mix, selected g in G.mix f g | `W5.SinglePremiseMix.single_premise_left/right`; actual contraction/mix constructors, component extension/naturality, complete branch fibers and exact ranks | Arbitrary P,C,gs,Θ,n≥2 and existing f/g, including cuts. Exact outputs G P (K++Φ) (Δ++Ψ) / G P (Δ++Φ) (K++Ψ). Complete ordered selection from g, same-label f exclusion, retained/fixed/suffix fibers and unique originals. Old outer LC+n, new retained LC+1; exact n/n−1 losses. Fixed/opposite g ranks both 2+rho; f old 2+rho/new 1+rho on both sides, correcting the historical missing-node target. Counts/CutFree/Atomized/full relations preserved. The other placement is now proved below; mixed-premise W5 and general Reducibility/coherence open. |
| W5 other single-premise mix, selected g in G.mix g f | `W5.OtherPremiseMix.other_premise_left/right`; derived prefix data/components, complete branch fibers and ranks | Arbitrary original P,C,gs,Θ,n≥2 and existing f/g including cuts. Exact outputs G P (Φ++K) (Ψ++Δ) / G P (Φ++Δ) (Ψ++K); raw gaps (Ξ++H)::hs derived from gs=H::hs. Complete shifted g selection; equal-label f exclusion, retained/fixed/prefix fibers and unique originals. Old outer LC+n, new retained LC+1; n/n−1 losses. Fixed/opposite g both 2+rho; f old 2+rho/new 1+rho on both sides. Counts/predicates/full relations preserved. Proof-occurrence replacement is now proved below; mixed-premise/binary W5–W6 and global elimination/coherence remain open. |
| Proof-occurrence replacement and W5 integration toward G2 | `Premise.rebuild/inserted`, `ProofAddress.replace/inserted/append`, recovery/composition/congruence/preservation; `OtherPremiseMix.replace_denote/count/cutFree/atomizedL/R` | Arbitrary existing root, proof occurrence/address and replacement at the exact same sequent. Outer endpoints/siblings preserved; inserted address keeps its path; complete Reduced congruence and tagged relation consequence. Exact additive cutCount/proofSize balances; root/replacement CutFree or Atomized imply rebuilt predicate. Existing W5 duals lift at any address, with nested signed-cut/Empty examples. Blocked/Reducible encodings and finite profiles are now proved below; certified rewrite dispatch, tied-site ranks and global G2/G3 remain open. |
| Blocked/reducible occurrences and finite selection classification | `BlockedL/R`, `ReducibleL/R`, `ProofAddress.ProperContains`, `PortOrigin`, `ContractionBlock.classificationL/R` and source-order macros | Seven actual source left patterns and separately typed canonical right encodings with explicit first-retention comparisons. Reducibility retains topmost-cut, cluster/address/position, unblocked and proper blocked-ancestor conditions. Every arity≥2 cut-free input has a unique seven-regime selected profile with complete per-position origin evidence; basis/cut excluded by proof. This is classification, not a reducer. Constructed mixed-premise mix W5 now has both addressed descendant theorems. Full profile dispatch, logical W5/W6, remaining local cases, outside-site ranks and global G2 remain open; see the follow-up report. |
| Normalization, §3 | `Presentation.normalization`; `NegationNormalization.forward_backward/backward_forward`, `forward_graph/backward_graph`, `transport_apply` | Actual source-quotient instance for every P, with signed-leaf normal forms, both inverse arrows, inverse tagged coordinates, literal/label/polarity correspondence, Empty cases, and relation transport. Recovery/injectivity reuse the existing theorems. No coherence or naturality premise. |
| Global signed-label preservation, §3 | `Presentation.Term.relation_signedLabel`, `occurrence_signedLabel`, `occurrence_literal` | Proved directly for every raw term and quotient arrow, with no nonemptiness, decidable-equality or coherence hypothesis. Complete literal equality, letter/polarity consequences, opposite-sign exclusion and normalized transport compile. The unchanged `SignedLabelPreservation` definition still takes the separately unconstructed faithful interpretation; no instance is fabricated. |
| `lem:isolation` | `Isolation.selector_edge`, `coselector_edge`, `isolate_edge`, `normalized_literal_context` | Normal-form witness equations and the normalized contextual consequence under faithful interpretation, normalization, and signed-label inputs. The full original-category witness formulation is not a separate declaration; no actual presentation is inferred. |
| `prop:all-contexts` | `ContextualCollapse.context_retract`, `all_contexts` | Typed substitution on arrows and endpoints, separate congruence closure, positive substitution, and negative substitution followed by double-negation transport. |
| `lem:collapse` | `ContextualCollapse.total` | Same conclusion by different proofs: v6 §5 uses q_A and e_A; Lean retains the symmetric-fold argument described in §6. Both concern existing arrows and use no quotient faithfulness or cancellation of j_A. |
| `thm:main` | `relative_maximality` is the conditional counterpart | The actual-presentation theorem remains open. The conditional theorem quantifies over every compatible congruence with explicit substitution closure. |
| `cor:models` | Not implemented | All interpretations; use nonempty P to choose a variable and interpret it as an arbitrary object. |
| Appendix A | Partial; full coverage required | Tagged block bijection is implemented. Complete profiles, gamma/chi maps and all squares, ordinal bijections and block locator, delta and the book-operation bridge, skeleton/profile reconstruction, the worked example, and renaming with shared variables; connect the specializations to Proposition 4.2. |
| Appendix B | Exact diagram correspondence required | Reuse the proved first-injection, constructed-zero and zero-law equations to certify the three displayed typed path equalities in the actual presentation. Record exact declaration links; the existence of the diagrams alone is not a Lean proof. |

The structural record fields are hypotheses of the conditional theorems.
They are not substitute definitions of the free Boolean category. Adding fields
such as “every contextual equation implies thinness” would assume the central
obligation rather than formalize its proof.

`Structure` gives the bicartesian universal equations, truth-constant arrows,
and distributor with all endpoints. `OccurrenceInterpretation` gives the
operation-level relation laws. `fold_independent`, `fold_swap`,
`first_injection`, and `second_block` derive the corresponding categorical
equations by faithfulness in the original category. The `GeneratedModel`
checks the entire v5 §5 interface, but includes no full Boolean presentation.
`Congruence` records the compatibility needed by this argument; a bridge must
restrict each actual proof congruence to it.

`Substitution.map σ f` has type `Hom (A.subst σ) (B.subst σ)` for
`f : Hom A B`. Its per-substitution functor/operation laws are inputs;
composition and identity laws for substitution schemas themselves have not
been formalized. No closure under substitution is inferred from one
interpretation kernel. The model corollary still requires every interpretation.

## Source-presentation instances

The [source correspondence](PRESENTATION_CORRESPONDENCE.md) gives printed pages,
equation labels, constructors, and derived arrows for the exact September 2007
revision. `Presentation.operations` constructs `Structure` for the syntactic
quotient. `Presentation.zeroIdentity` uses the displayed `(0ηε)` composite;
`zeroConstruction_eq` proves equality with primitive zero. Empty hom-sets are
preserved, with `Presentation.empty_hom` for every variable type P.

`Term.subst`, `Equation.subst`, and `Derives.subst` establish whole-arrow and
endpoint substitution and its preservation of the source-generated equality.
`Presentation.substitution` instantiates the existing per-substitution
`Substitution` interface, including the constructed zero.
`Presentation.doubleNegation` instantiates `DoubleNegation` from the two n-arrows
and their inverse equations. These instances use no coherence hypothesis.
Schema identity/composition with endpoint identifications and occurrence-block
transport remain separate obligations. No arbitrary extra congruence is thereby
proved substitution closed.

`Presentation.Equation.relation`, `Derives.relation`, and `occurrenceMap` prove
well-definedness of the occurrence interpretation and the operation images.
Faithfulness remains open, so no complete `OccurrenceInterpretation` instance
or intended `relative_maximality` instance is claimed. `Presentation.normalization`
now constructs the existing normalization record with occurrence graphs and
signed coordinate correspondence. `Presentation.occurrence_signedLabel` now
proves global signed-label preservation directly, with normal-form literal
and transport consequences. Derived contravariant arrow negation/naturality,
congruence restriction, and the remaining Appendix A/model correspondences are
still open. The reduced signed-literal syntax and existential representation
bridge are now constructed, with occurrence compatibility and conditional
coherence transfer; reduced faithfulness remains open. See the
[reduction report](SIGNED_LITERAL_REDUCTION_REPORT.md),
[signed-label report](SIGNED_LABEL_REPORT.md),
[normalization report](NORMALIZATION_REPORT.md), and the historical
[presentation report](PRESENTATION_BRIDGE_REPORT.md) for exact hypotheses,
source references, commands, evidence, and review boundaries.

The [contextual factorization report](CONTEXTUAL_FACTORIZATION_REPORT.md) records
the next completed source step. The context functor descends through Derives;
its occurrence action fixes surrounding tags and acts on the distinguished hole.
The two “same pairs” comparisons use explicit Sum.inl endpoint embeddings.
Neither these identities nor the earlier representation theorem proves reduced
faithfulness. The source's common atomic factorization and complete support are now proved.
The §12.5 positive-fragment coherence input remains an obligation.

The [common atomic report](COMMON_ATOMIC_FACTORIZATION_REPORT.md) records the
shared factorization and full auxiliary-edge exclusion. Positive describes the
arrow grammar, including zero, rather than literal polarity. Its precise
PositiveCoherence premise is not an axiom or supplied instance. Neither the
factorization nor relation support alone is Boolean Coherence.

The [positive zero/union report](POSITIVE_ZERO_UNION_REPORT.md) records the proved
algebra and separate interpretation formulas. Its dependency table specifies the
then-pending Gentzenization theorem and later coherence inputs; the current G0/G1 status is recorded below.

The [Gentzenization report](POSITIVE_GENTZENIZATION_REPORT.md) records completed
G0/G1 and its historical Atomic-k continuation target. The
[Atomic-k report](POSITIVE_THINNING_ATOMIZATION_REPORT.md) now proves that exact
target, with CutFree preservation and tagged occurrence equality. The
cluster/rank prerequisite is now proved below; the remaining G2 transformations
come next.
The representation is existential and supplies no quotient translation.

The [cluster/rank report](GENTZEN_CLUSTER_RANK_REPORT.md) records the completed
prerequisite. The [W1 thinning report](GENTZEN_W1_THINNING_REPORT.md) now
proves the two opposite-side thinning instances, with distinct contraction
and endpoint rank losses. Other W1 cases and all-site reducibility remain open.
No rank invariance under equal denotations or quotient descent is asserted.

The [W1 exchange report](GENTZEN_W1_EXCHANGE_REPORT.md) proves the two
opposite-side exchange instances after thinning. The contraction pair is now proved in
[the contraction report](GENTZEN_W1_CONTRACTION_REPORT.md), with its two
directed rank comparisons. The [logical report](GENTZEN_W1_LOGICAL_REPORT.md) now proves the two unary
logical instances and principal 2→1 ranks. The [same-side thinning report](GENTZEN_W1_SAME_SIDE_THINNING_REPORT.md)
now proves interior-gap and terminal-tail insertion and both duals, with every
selected copy parametric even E=C. The [same-side exchange report](GENTZEN_W1_SAME_SIDE_EXCHANGE_REPORT.md)
now proves four fixed-gap/tail exchange cases. The [same-side logical report](GENTZEN_W1_SAME_SIDE_LOGICAL_REPORT.md) now
proves all four fixed-gap/tail unary logical cases. The [disjoint-contraction report](GENTZEN_W1_DISJOINT_CONTRACTION_REPORT.md) proves both fixed-gap same-side cases. The [terminal-tail report](GENTZEN_W1_TERMINAL_TAIL_CONTRACTION_REPORT.md) now proves both terminal-tail cases with explicit xC<xE ordering and the independently directed rank table. The [W3 report](GENTZEN_W3_SHARED_SELECTED_CONTRACTION_REPORT.md) now proves shared-selected fusion and its right dual, including exact retained rank drop m. The [W2 report](GENTZEN_W2_SELECTED_THINNING_REPORT.md) now proves terminal selected thinning and its right dual, including distinct n+1/n losses and the asymmetric Atomized boundary. The [W4 report](GENTZEN_W4_SELECTED_LOGICAL_REPORT.md) now proves terminal selected logical introduction and its right dual, with n+1 source contraction loss, n=2 endpoint tie and other fixed-rank increases. The [single-premise W5 report](GENTZEN_W5_SINGLE_PREMISE_MIX_REPORT.md) now proves the G.mix f g placement and right dual, including n/n−1 losses and corrected opposite-side ranks. The [other-placement W5 report](GENTZEN_W5_OTHER_PREMISE_MIX_REPORT.md)
proves G.mix g f and its right dual with actual prefixed gaps and the same
complete rank table. The [proof-replacement report](GENTZEN_PROOF_REPLACEMENT_REPORT.md) now
constructs typed replacement and integrates both W5 duals at arbitrary addresses,
with exact count/predicate laws and actual nested examples. The [classification report](GENTZEN_BLOCKED_CLASSIFICATION_REPORT.md) now
encodes those patterns and proves finite selected-ancestry coverage. Its ledger
identifies mixed-premise W5 as the next unproved regime.
Disjoint interleaving, mixed-premise/binary W5–W6, remaining exchange/W1/W2,
complete rewrite dispatch, macro/tied-site ranks and broader elimination/coherence stay open.
