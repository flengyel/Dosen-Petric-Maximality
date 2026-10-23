# Positive-fragment zero and union report

The two-zero tensor laws and the full requested derived union algebra are
proved in Reduced.Hom, with raw positive representatives and occurrence
compatibility. These proofs use the existing syntactically generated equality.
PositiveCoherence, Reduced.Faithful and Boolean Coherence remain open.

Starting checkpoint: `16f5d10aea3f1087659a8eddef38fbf428aec4fd`, clean main.
SSH origin was fetched and local/tracking main agreed. No unrelated work,
reset, dependency change or reconstruction of common factorization was needed.
Lean 4.35.0, Init-only dependencies, old Lean sources and historical reports,
21 raw constructors, 61 equation schemas, 19 positive schemas and manuscript
v4 are unchanged. Three new modules provide this checkpoint.

## Exact proved endpoints and hypotheses

Let P : Type u be arbitrary and all objects below be NormalForm P. No
Nonempty P, DecidableEq P, enumeration, freshness or coherence hypothesis is
used. Composition `f ; g := comp f g` executes f first.

For every existing f : Hom A C and g : Hom B D, define
`z_f := zero A ; f`. Witness independence states z_f = z_w for every
existing same-type witness w. Zero commutes with every arrow, is idempotent,
and composing z_f on either side gives the zero associated with that existing
composite. No zero is constructed in an empty hom-set. For ξ = ∧ and ∨:

```
zero A ξ zero B = zero (A ξ B)
z_f ξ z_g = z_(f ξ g).
```

The first is tensor_zero; the second is tensor_zeroOf. Product/coproduct
extensionality follows from the existing reduced diagonal derivations.
`Term.zeroOf` and `Term.Positive.zeroOf` give a positive raw representative
when f has a positive raw representative; `Positive.tensor_zero` supplies
the two-zero raw tensor. The zero endomorphism itself is already positive.
The law is not asserted for only one zero tensor factor.

For any parallel raw f,g : Term P A B, union is defined by the path

```
A --diag--> A ∧ A --f ∧ g--> B ∧ B --mix--> B ∨ B --codiag--> B.
```

Term.Positive.union proves closure, Derives.union proves congruence before
Quotient.liftOn₂ defines Reduced.union, and union_ofTerm identifies the result
on representatives. No primitive constructor or generating equation is added.
For arbitrary parallel quotient f,g,h : Hom A B, k : Hom X A,
l : Hom B C and existing same-type witness w, the following compile:

```
union f g = union g f
union (union f g) h = union f (union g h)
union f f = f
comp k (union f g) = union (comp k f) (comp k g)
comp (union f g) l = union (comp f l) (comp g l)
union (id A) (zero A) = id A
union f (zeroOf w) = f
union (zeroOf w) f = f.
```

The algebra is proved for all existing Reduced arrows, so restricting to
eta/epsilon-free raw representatives is immediate from positive closure.
“Positive” describes arrow constructors, not literal signs. No semilattice
instance or bottom element for an empty hom-set is installed.

Let f,g : Term P A B be raw terms and F,G : Hom A B be quotient arrows.
For every tagged x : A.formula.Occ and y : B.formula.Occ:

```
(f.union g).relation x y ↔ f.relation x y ∨ g.relation x y
occurrenceMap (union F G) x y ↔ occurrenceMap F x y ∨ occurrenceMap G x y
f.zeroOf.relation = Relations.empty
occurrenceMap (zeroOf F) = Relations.empty.
```

The first/third are raw calculations, the second/fourth quotient statements.
Negative literals, repeated tags and both constants are unrestricted. The
proofs quantify directly over occurrence types and do not choose an element;
they also cover Empty endpoints. Equal labels never identify distinct tags.
No relation equality is used to infer syntactic arrow equality.

## Source correspondence and direct proof

Source: Došen–Petrić, Proof-Theoretical Coherence, September 2007 revision,
[author-hosted PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf).
SHA-256 `e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
Printed page n corresponds to one-based PDF n+12. The precise equation/type
index is the new “Positive-fragment zero and derived union algebra” section
of PRESENTATION_CORRESPONDENCE.md.

Section 12.5 p.288 gives the witnessed definition, independence, (00), and
(0I ξ) as consequences of (0I). tensor_zero derives the conjunction case by
both projections and the disjunction case by both injections, using only
naturality, zero commutation and the already derived universal properties.
tensor_zeroOf then uses tensor composition. No zero arrow is inferred from
an empty relation or full-Presentation uniqueness.

Section 10.1 p.219 gives (wm); p.220 defines union in ML by
`diag_A ; mix_(A,A) ; (f ∨ g) ; codiag_B`. union_source proves agreement of
that convention with the chosen raw term by mix naturality. The p.220 union
laws are axioms of the alternative GML syntax, but consequences in ML.
The new proofs derive those consequences directly. merge_A := mix_AA ;
codiag_A is natural, symmetric, and associative with the typed associator,
by (m nat), (c m), (b m) and the codiagonal laws. Pair associativity uses
diagonal associativity/naturality. These give union associativity and
commutativity; (wm) gives idempotence. This replaces the source's appeal to
Lattice Coherence for these particular laws only.

Union unit is assumed for ZIML on p.289 but derived in ZIDL on pp.290–291.
The rendered p.291 calculation was checked. union_id_zero follows its direct
structural alternative: expand mix by (d m), §11.1 p.234; after diag and
id ∧ zero the typed path is

```
A ∧ A --id ∧ inr--> A ∧ (A ∨ A) --d--> (A ∧ A) ∨ A
      --fst ∨ id--> A ∨ A --codiag--> A.
```

(0I) replaces zero_A ; inr by zero_A ; inl. Then (d k∨) contracts
(id ∧ inl) ; d to inl_(A∧A,A). Injection naturality moves fst before that
injection. Projection naturality and diag ; fst = id remove the unused zero
branch; inl ; codiag = id finishes. General union_zeroOf follows by
postcomposition and witness independence; the opposite order uses commutativity.
No lattice/positive/Boolean coherence theorem or new union-unit equation is used.

The raw relation proof expands diag, tensor, mix and codiag with disjoint
Sum tags. It gives pointwise disjunction. Zero composition has empty relation.
These calculations are separate from the preceding syntactic proofs. There
is no fullness assumption or realization claim for all signed-label-preserving
relations. No new source discrepancy was confirmed in the target calculations;
previous p.319/p.321 discrepancies remain documented.

## Proved declaration inventory

| Module | Definitions and proved declarations |
| --- | --- |
| ReducedZeroAlgebra | zeroIdentity, zeroOf, zeroOf_independent, zero_commute, zero_idempotent, zeroOf_pre/post/id/zero, conj_ext, disj_ext, tensor_zero, tensor_zeroOf, Term.zeroOf and both positive membership lemmas, ofTerm_zeroOf. |
| ReducedUnion | Term.union and Positive.union, Derives.union, quotient union and union_ofTerm/def/source; merge and merge_nat/swap/assoc; codiag_assoc_forward; pair_pre/post/assoc; union_pre/post/comm/idem/assoc/id_zero/zeroOf and zeroOf_union. |
| ReducedUnionOccurrences | Term.relation_union, Term.relation_zeroOf, occurrence_union, occurrence_zero, occurrence_zeroOf. |

The retained DECLARATIONS.txt gives all explicit declarations with source lines.
The strict environment audit counts generated declarations as well.

## Verification and retained evidence

The clean baseline strict check exited 0: 46 Lean files, 2816 audited project
declarations. Final verification completed at 2026-10-23T01:05:13.813458+00:00.
One heavy build/audit ran at a time with LEAN_NUM_THREADS=1. WSL2 memory was
inspected: 15 GiB RAM, about 13 GiB available, no swap. No clean rebuild or
cross-project artifact reuse was needed. Development typing/rewriting errors
were corrected before the retained final successful run.

| Actual command | Exit and observed result |
| --- | --- |
| `bash scripts/verify.sh` | 0; **49 Lean source files, 2875 audited project declarations**, strict build and transitive axiom audit under pinned Lean 4.35.0. |
| `python3 scripts/check-audit-boundaries.py` | 0; public import closure passed; direct-axiom, private-axiom and hidden-dependency each rejected with Lean exit 1 and expected unpermitted-axiom diagnostics. |
| `python3 scripts/check-presentation-boundaries.py` | 0; identified-projections rejected with Lean exit 1 (`rfl` failed); zero-without-arrow-witness rejected with Lean exit 1 (type mismatch). |
| `cd manuscript && sha256sum -c SHA256SUMS` | 0; unchanged v4 TeX/PDF checksums passed. |
| `git diff --check` | 0; repeated after documentation/staging. |

All five expected negative rejections are retained with exact fixture commands,
sources, exit codes, diagnostics and hashes. Only propext, Quot.sound and
Classical.choice are permitted globally. Selected new syntactic laws print
Quot.sound only; positive membership and raw union/congruence construction
print no axioms; occurrence declarations print propext and Quot.sound. No
selected new declaration uses Classical.choice. No production proof holes,
custom mathematical axioms, native_decide, new equations or coherence instance.

Evidence: `provenance/wsl-positive-zero-union/`, with matching runtime records
under `.codex-work/positive-zero-union/`. SOURCE_SHA256SUMS covers all checked
Lean files, audit files, toolchain, manifest and verification scripts.
Its SHA-256 is `3b7587132d2892aa8ad3e18615d832abbdcf8261d10340d69b33d6203e3bd443`.
EVIDENCE_SHA256SUMS covers raw logs, exact command/result JSON, five rejected
fixtures, declaration inventory, source consultation and historical boundaries;
its SHA-256 is `a2b7be0046a4eb8b147936b4790a66db0628ad613ecb1e647844e43e44b4dde8`. REPORT_SHA256SUMS identifies the three reports;
RECORD_SHA256SUMS identifies the updated correspondence/statement/coverage/
validation/continuation documents. These manifests exclude themselves.
The source book and writing-cache hashes are pinned in source-consultation.json;
the rendered p.291 evidence is retained in the ignored runtime directory.

The strict log names baseline HEAD and exact working-source hashes, rather
than mislabelling a dirty-source build as a build of that commit. The final
committed-source equality, SSH ref agreement and byte-verified Downloads
receipts are recorded separately at runtime; the completion response gives
the integration commit. Historical sources/reports and manuscript integrity
are checked against the baseline in boundaries.json. Author-side hostile and
source-grounded writing reviews are retained beside this report, using the
verified cached governing text. They are not independent certification.

No independent kernel replay, independent source-transcription audit,
Challenge/Solution or Comparator comparison, official preflight/service check,
new manuscript compilation/layout review, publication, license or visibility
change was performed. Earlier access records and provisional reviews remain.

## Remaining positive-coherence dependency table

This is a construction plan with typed targets, not a list of supplied Lean
proofs. All proposed syntax is parameterized by arbitrary P. For a concrete
non-strict implementation, take sequent contexts Γ,Δ : List (NormalForm P),
`ante Γ := Γ.foldr NormalForm.conj .top` and
`succ Δ := Δ.foldr NormalForm.disj .bot`. Proposed
`G P Γ Δ : Type u` has the source Gentzen rules (exchange, thinning,
contraction, mix, both logical rules, and cut), atomic id/zero at each
`l : Literal P`, and the two constant basis terms. It is not the raw Term
grammar renamed: d and general composition must be expressed by the rules.
`G.denote g : Term P (ante Γ) (succ Δ)` uses actual unit/association arrows;
`G.rel g := (G.denote g).relation`. Equality below is always ambient Reduced.Hom.
This explicit bracketing avoids assuming a strictification theorem. The typed
unit/associativity simulations replacing strict equalities must themselves be
proved, including empty contexts; none is supplied merely by this convention.

For restricted coherence, proposed `MixTerm P A B` is the structural raw
fragment with zero and mix but without d, eta or epsilon, together with both
tensors/composition, and `MixTerm.denote : MixTerm P A B → Term P A B`.
DNF permits disjunctions of conjunction-only formulas; CNF is dual, with the
source's constant cases (§9.6, pp.211–212; §10.3). `Settled P A B` is the
bracket normal syntax, not a relation quotient. `Atomic P A B` is its
projection/injection path syntax, with literal id/zero and constant bases.
`ZeroAtomic` selects the zero and constant bases. These types/predicates,
including exact DNF/CNF constant clauses, remain to be defined. The following
statements therefore specify proposed interfaces rather than compiling code.

| ID / source and hypotheses | Proposed typed target / exact endpoint | Predecessors | Status |
| --- | --- | --- | --- |
| Z: §12.5 p.288 (0I ξ), pp.290–291 (∪0); any P and existing arrows | `tensor_zero o A B`; `tensor_zeroOf o f g`; `union_id_zero A`; all seven union algebra laws and witnessed zero unit | Existing Reduced.Laws, product/coproduct derivations | **Proved here**; interpretation and positive raw membership are separate proved declarations. |
| G0: §11.1 pp.238–243; §11.5 p.272; §12.5 p.291 | Define `G`, `G.denote`; `∀ g : G P Γ Δ, (G.denote g).Positive`; typed interpretation of every rule, including cut as the source d/structural composite and empty contexts | Existing category/units/context laws, Z; no faithfulness | **Open**, first construction. Binary folds require explicit simulations of the source's strictified sequence equations. |
| G1: §11.1 Gentzenization pp.245–246; §11.5 pp.272–273; §12.5 p.291 zero extension using (0I ξ) | `∀ (t : Term P A B), t.Positive → ∃ g : G P [A] [B], ofTerm (G.denote g) = comp (rightOut .conj A) (comp (ofTerm t) (rightIn .disj B))` | G0; typed rules for each of the 19 positive constructor schemas; zeros expanded recursively with Z; constant identity/zero laws already in ReducedStructure | **Open**, next theorem. Representation is existential; no quotient function is inferred. |
| G2: §11.2 pp.247–253 Atomic-k, Reducibility, Blocked-w and clean-cut definitions | For proposed `TopCut g`, `∃ h : G P Γ Δ, Clean h ∧ ofTerm (G.denote h) = ofTerm (G.denote g)`; prove every local rewrite reduces the source rank/multiset measure | G0, source structural/d equations; exact cut-formula positions, clusters and ranks; Z for zero leaves | **Open**. This is normalization of a topmost cut, not arbitrary equality by its relation. |
| G3: §11.2 pp.253–263 Cut-Elimination; §11.5 p.273 constants; §12.5 pp.291–292 zero atomic cases | `∀ g : G P Γ Δ, ∃ h : G P Γ Δ, CutFree h ∧ ofTerm (G.denote h) = ofTerm (G.denote g)` | G2; well-founded clean-cut complexity and blocked contractions; constant cut cases, (00), zero naturality | **Open**. Source five new zero cases must be derived at actual endpoint folds; unit terms are not arbitrary zeros. |
| M0: §10.2 pp.223–226; §10.3 pp.229–230; §12.5 pp.289–290 | Define MixTerm/Atomic/Settled; `∀ t : MixTerm P A B, DNF A → CNF B → ∃ n : Settled P A B, ofTerm n.denote = ofTerm t.denote` | Z union laws; cut/composition elimination for the smaller Gentzen lattice syntax, extending §9.4/§9.6; atomic bracket normal forms | **Open**. Smaller-system composition elimination is a real proof obligation, not supplied by the new algebra. |
| M1: §10.3 pp.229–230 zero constants; §12.5 p.290 zero atomic components | `∀ a : Atomic P A B, ZeroAtomic a → ofTerm a.denote = zeroOf (ofTerm a.denote)`; hence any two such same-type components are equal | Atomic path syntax; zeroOf_pre/post/independent, zero_top/bot and terminal/initial uniqueness; constant bases | **Open** for the proposed syntax; its categorical zero and unit ingredients are already proved. No general empty-relation equality is used. |
| M2: §10.2 pp.225–227 molecular/atomic correspondence; §10.3 p.230; §12.5 p.290 | `∀ n m : Settled P A B, n.denote.relation = m.denote.relation → ofTerm n.denote = ofTerm m.denote` | M0/M1, path/tag equality, finite union commutation/idempotence/zero deletion; atomic uniqueness must be proved from paths or the earlier restricted dicartesian theorem, itself unformalized | **Open**. Distinct equal-labelled tags are separate paths. An empty molecular block needs an existing zero atomic component, not a fabricated arrow. |
| M3: Restricted Zero-Identity Mix-Dicartesian Coherence, §12.5 p.290 inheriting §10.3 pp.229–230 | `∀ f g : MixTerm P A B, DNF A → CNF B → f.denote.relation = g.denote.relation → ofTerm f.denote = ofTerm g.denote` | M0/M1/M2, interpretation preservation | **Open**. Restricted object hypotheses are essential; no unrestricted mix coherence is assumed. |
| R0: §11.3 pp.264–265; §11.5 pp.270–271 derivation of omitted (m e) and unit cases | Construct DNF/CNF objects and positive arrows `sA : Hom A (dnf A)`, `tA : Hom (dnf A) A`, `tB : Hom B (cnf B)`, `sB : Hom (cnf B) B` with `comp sA tA = id A`, `comp tB sB = id B` | Explicit distribution composites, diagonal/codiagonal/product laws, and derived (m e) instances; §11.5's use of earlier coherence must be replaced by proved structural lemmas | **Open**. Distribution is a retraction, not an isomorphism; the reverse composites are not asserted identities. |
| R1: §11.3 p.265 Proposition/Normal-Form Lemma; §11.5 p.274; §12.5 p.292 | For positive `t : Term P A B`, `∃ m : MixTerm P (dnf A) (cnf B), ofTerm m.denote = comp tA (comp (ofTerm t) tB)` | G1/G3; cut-free terms between conjunction-only and disjunction-only endpoints give MixTerm representatives; product/coproduct recursion and R0 | **Open**. Cut elimination connects distributive syntax to the restricted mix syntax; the two grammars are not identified by fiat. |
| C: §11.3 p.266, §11.5 p.274, §12.5 pp.291–292 | `PositiveCoherence P`, exactly as defined in PositiveFragment.lean | R0/R1/M3, composition interpretation, then cancel the proved retractions | **Open**. Only positive raw terms are quantified; conclusion is Reduced.Hom equality. |
| F: §14.2 p.321 common-factor argument | `PositiveCoherence P → Faithful P` | Completed commonAtomicFactor, positive middles and full support | **Already proved**, `faithful_of_positive_coherence`; premise remains unsupplied. |

The shorter structural merge/pair argument in this checkpoint replaces only
the §10.1 coherence appeal for union algebra. No shortcut replaces G0–C.
One may implement the source's strictified category instead of explicit folds,
but that route also requires proved equivalence/transport of the relevant
operations; it cannot be assumed. Neither route asserts fullness or realization
of every signed-label-preserving relation. No proposed unproved declaration
above was inserted into production Lean.

## Remaining obligations and next concrete theorem

There is no blocker to the requested zero/union checkpoint: all required
algebra and occurrence endpoints compile unconditionally. The next theorem
is G1, typed positive Gentzenization, after defining G0 and its denotation.
Then prove cut elimination and restricted zero-identity mix-dicartesian
coherence with explicit atomic zero/constant cases before PositiveCoherence P.
The dependency table identifies these open statements; no published reference
is treated as a supplied Lean proof.

Reduced.Faithful, Boolean Coherence, faithful OccurrenceInterpretation,
inclusion equality reflection, full raw reduction's equation preservation and
quotient descent, source equivalence, contravariant arrow negation/laws,
congruence restriction and the remaining substitution-schema/Appendix A
bridges, actual maximality and the every-interpretation corollary remain open.
The existing conditional transfer and relative maximality are reused unchanged.
No milestone is promoted by this algebraic checkpoint.
