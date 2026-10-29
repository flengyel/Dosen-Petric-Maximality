# Positive, Reduced and Boolean coherence

`Gentzen.positive_coherence : PositiveCoherence P`, `Reduced.faithful : Faithful P`
and `Presentation.coherence` are proved for arbitrary P. The complete
`Presentation.interpretation P` now instantiates the occurrence interface in the
actual equation-generated category, with its signed-literal invariant. Its
nonthin instance at P=Nat and the preserved empty Hom(top,bot) are checked.
This completes milestone I's intended faithful-interface requirement. The
conditional maximality theorem remains proved; the full source substitution-
congruence correspondence, actual maximality instantiation, short proof, model
corollary and remaining full-paper claims are continuing obligations.

## Atomic normal forms and exact occurrence tags

Pure o A means that the only binary connective in A is o; both constants and
signed literals are allowed. PureContext quantifies over every whole-formula
context tag. positive_cutFree_represented uses the actual unrestricted eliminator
to obtain one CutFree/Atomized Gentzen witness at the original singleton sequents
with complete occurrence correspondence. mixOnly_of_pure proves that a cut-free
proof with pure conjunctive input and pure disjunctive output has no conjR,
disjL or cut node. positive_mix_represented supplies this actual mix proof.

PurePort records a signed literal path through one connective, with distinct
left/right tags. ofPosition, position_ofPosition and position_injective give exact
correspondence with the original occurrences. Context embeddings factor through
the actual projection/injection component. route_factor and logical_factor
transport every port through structural routes and unary logical comparisons,
including both consumed components and all fixed tags. Equal labels do not
identify ports; constants have no ports.

A PureEdge consists of one signed label and independent source and target ports.
Its arrow is the product projection followed by the coproduct injection, in
left-first composition order. projection_relation, injection_relation and relation
prove its singleton relation at exactly those two original tags. ext_positions
proves uniqueness from those positions.

finiteUnion uses a supplied existing arrow for its empty zero. Witness independence,
append, repeated-summand absorption, equality from equal membership, pre/post
composition and exact relation support are proved. No arrow is introduced into
an empty hom-set. PureEdge.evaluate_faithful shows that relation equality determines
finite atomic unions: each edge's original coordinate pair detects membership,
and idempotent commutative union removes order and duplication.

HasPureNormalForm is proved for actual G mix proofs. Structural and unary rules
transport each port before rebuilding the finite union. Native mix is explicitly
the union of its two routed children, retaining reversed input/output blocks.
The identity basis has its actual literal edge; atomic zero and both constant
leaves use witnessed zeros and the existing uniqueness laws. Induction over every
MixOnly constructor proves G.mix_normal_form. Thus G.pure_cutFree_faithful and
pure_positive_coherence have actual normal-form constructions, without supplied
normalization handlers or relation-reflection assumptions.

## DNF/CNF and unrestricted coherence

DNF is a disjunction of pure conjunctions; CNF is a conjunction of pure
disjunctions. normal_positive_coherence follows from the actual coproduct/product
universal properties, with pure_positive_coherence as its base. Both constants
and repeated signed occurrences remain included.

NormalRetract A B carries represented arrows forward:A→B and backward:B→A
with forward;backward=id_A. It does not assert the other composite is identity.
The right/left distributive expansions use the existing proved
DistributiveEpi.section_comparison and DistributiveMono.comparison_retraction,
actual sourceConj/mixedDisj terms, tensors, pairs/copairs and swaps. Every map's
Represented witness is constructed. dnf_product/cnf_sum and structural formula
induction give dnf_expansion/cnf_expansion for every A, with explicit represented
recovery maps. No distributive isomorphism is assumed.

represented_coherence precomposes with the DNF comparison and postcomposes with
the CNF comparison, applies normal_represented_coherence, and cancels only the
proved one-sided recoveries. positive_coherence supplies the formerly open input.
The unchanged common atomic factorization gives Reduced.faithful. The unchanged
normal-form representation and normalization transport give Boolean coherence in
the original presentation. All fields of Presentation.interpretation and its
signed-label theorem are instantiated. Coherence is applied only in that original
category for the continuing maximality argument.

## Verification, reviews and continuing duties

Eighteen new production modules implement this argument. Pinned Lean 4.35.0 strict
verification, all thirty public check files, transitive source/dependency closure,
actual intended-interface/nonthin/empty-hom/constant/signed-tag witnesses and 48
expected negative-control rejections are required. Actual counts, exits, hashes,
checked/committed-byte source archives and development failures are retained in
provenance/wsl-gentzen-positive-coherence/FINAL_VERIFICATION.json and COMMANDS.json.
Only propext, Classical.choice and Quot.sound are allowed. Negative controls protect
repeated ports, crossed target edges, comparison variance and witnessed empty
unions, in addition to every earlier rank/tag/repair/boundary control.

Both reviews are local author-side argument/map/writing reviews. Independent
kernel replay, Comparator, official/service verification and publication remain
separate unperformed statuses. All nine manuscript blobs, both Appendix C rows,
previous results, stash and delivery receipts are preserved. No manuscript defect
was established. The source's distributive comparisons are one-sided recoveries;
this accepted mathematical distinction is retained in every new declaration/map.
Reports, reviews and changed records are delivered from committed bytes with
conflict preservation and exact verification; DELIVERY_REGISTER.json records paths.

Continue the full source congruence/uniform-substitution bridges and instantiate
actual maximality; formalize the short q_A/e_A route as well as retaining the
symmetric-fold proof. Complete the model corollary and every remaining mathematical
claim, construction, equation, example and diagram identity in all three v7
appendices. Milestones II/III and the full-paper endpoint retain their exact
separate scopes. This coherence milestone does not close that whole contract.
