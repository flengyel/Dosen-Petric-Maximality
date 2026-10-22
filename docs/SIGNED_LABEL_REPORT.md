# Global signed-label preservation

The actual presentation now has a proved signed-edge invariant for every raw
term and every quotient arrow. Every edge joins occurrences with equal complete
signed literals. The result specializes to normal forms and to the existing
normalization transport. It does not prove Boolean Coherence.

Starting checkpoint: `45a34c8d939aa1d931a8946de209721991750921`, clean main.
SSH fetch left main and origin/main equal. Completed presentation and
normalization constructions were reused unchanged. The only new production
file is `DosenPetric/PresentationSignedLabels.lean` (172 physical lines);
the library import and selected axiom-print declarations are also updated.
No grammar, equation, quotient, normalization, or faithful-interface definition
was changed. Manuscript v4 is unchanged.

## Exact statements and hypotheses

All preservation statements quantify over arbitrary `P : Type u`, with no
inhabitant, decidable equality, finite enumeration, or coherence premise.
The raw theorem is exactly:

```
Term.relation_signedLabel
  {A B : Formula P} (t : Term P A B) (x : A.Occ) (y : B.Occ)
  (h : t.relation x y) : A.signedLabel x = B.signedLabel y
```

The quotient theorem `occurrence_signedLabel` has the same endpoints and
positions, with `f : Hom A B` and `h : occurrenceMap f x y`. The conclusion
is unchanged. `Formula.signedLabel` records the variable and parity of all
negations on the path to the tagged occurrence. Its type is `Literal P`,
not just P. A term/arrow witness is always present; no arrow is supplied to
an empty hom-set. `comp f g` applies f before g.

For normal forms A,B, `occurrence_literal A B f x y h` proves
`A.literalAt x = B.literalAt y`, for every `f : Hom A.formula B.formula`.
This is the edge conclusion needed by the old `SignedLabelPreservation`
definition, stated directly for `occurrenceMap`. That definition still takes
a faithful `OccurrenceInterpretation`, whose instance is not available; it
was neither weakened nor fabricated. A later adapter needs an interpretation
with the same map, in addition to its separately proved faithful field.

## Proof and source correspondence

Source: Došen–Petrić, *Proof-Theoretical Coherence*, September 2007 revision,
[author-hosted PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf),
SHA-256 `e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e`.
All following pages are printed; zero-based PDF page = printed page + 11.
The primitive grammar and relation assignment are those already pinned in
`PRESENTATION_CORRESPONDENCE.md`. This proof is a direct induction on all 31
constructor schemas, not an invocation of the source's coherence/equivalence.

| Source family / anchor | Lean proof case and reason |
| --- | --- |
| Identity, composition, tensors; §2.7 and §14.2 p.316 | Identity substitutes equal positions. Composition supplies z with both constituent edges; combine the two inductive equalities through its signed label. Tensors split both tags: matching branches use the corresponding child invariant and crossed branches are False. |
| b,c; source map §§4.4,5.1,6.2–6.4 | `assocR/assocL/swap`: substitute the graph equality and split source tags; the same signed subformula label remains. |
| w-k; §§9.1,9.4,9.6 | `diag/codiag/fst/snd/inl/inr`: split tags and graph equalities. Copying and merging retain labels, not unique coordinates. |
| delta/sigma units; §§4.6,6.4,9.6 | `rightOut/rightIn/leftOut/leftIn`: the retained branch has the same label; the unit branch has Empty positions for either connective. |
| m,d; §§8.2,8.4,7.2; p.316 | `mix/dist`: identity/reassociation graphs preserve the tagged signed subformula label. |
| n/r; §14.1 p.310; G clause p.314 | Both double-negation directions use full-literal `Literal.flip_flip`. Both De Morgan directions split branches; the parity flip of the child label agrees definitionally on each side. |
| rho; p.312, G clause p.314 | All four constant comparison endpoints have Empty occurrence types. |
| 0,eta,epsilon; §12.5 and §14.2 pp.316–317 | The assigned relations are empty, so the edge hypothesis eliminates to False. No absorption/coherence assumption is needed for this invariant. |
| Manuscript v4 §3 signed-literal paragraph | `occurrence_literal` rewrites the raw signed-label conclusion with `NormalForm.signedLabel_eq_literalAt`; it does not assume the source's reduced-presentation equivalence. |

`occurrence_signedLabel` uses quotient induction and explicitly rewrites by
`occurrence_ofTerm`. The already proved well-definedness of occurrenceMap is
reused; no defining-equation proof is repeated. Arrow equality remains the
published equation-generated quotient, never equality of relations.

## Proved declarations

The following fifteen theorems are under `DosenPetric.Presentation`:

| Declaration | Proved content |
| --- | --- |
| `Term.relation_signedLabel` | Raw-term invariant above. |
| `occurrence_signedLabel` | Quotient-arrow invariant above. |
| `occurrence_label`, `occurrence_polarity` | Every edge preserves the underlying letter and full negation parity. |
| `no_edge_of_polarity_ne` | Any unequal endpoint polarities exclude an edge. |
| `no_edge_opposite_literals`, `no_edge_negative_positive_literals` | For a supplied p and endpoint label equations, exclude positive-to-negative and negative-to-positive edges of that same variable. |
| `occurrence_literal` | Equality of complete literals at normal-form endpoints. |
| `occurrence_literal_letter`, `occurrence_literal_polarity` | The corresponding letter and sign consequences for normal forms. |
| `no_edge_of_literal_ne` | Unequal complete normal-form literals exclude an edge, without deciding equality in P. |
| `diag_copies`, `codiag_merges` | For any supplied p, explicit edges copy/merge between two provably distinct tags. |
| `NegationNormalization.transport_literal` | Every edge of a transported arrow joins equal normal-form literals. |
| `NegationNormalization.transport_literal_coordinates` | Every original edge gives equal literals at its two forward normalizer coordinates. |

For f : Hom A B and normal-form positions x,y, `transport_literal` uses the
existing equivalence `transport_apply` to obtain an original edge between
`fromOcc A x` and `fromOcc B y`. Apply the new global theorem, then use the
existing `literal_fromOcc` on both sides. The coordinate version uses the
existing `transport_coordinates` theorem. Forward/backward graph identities,
inverse coordinates, recovery, and transport injectivity are reused unchanged.

Signed-label equality does not identify tags. For a supplied p,
`diag_copies p` exhibits edges from () to both inl() and inr(), and proves
the target tags unequal. `codiag_merges p` exhibits edges from both unequal
source tags to (). Thus an individual occurrence relation need not be
functional or injective. Faithfulness instead asks whether the relation
distinguishes parallel arrows; that different assertion remains unproved.

## Verification and evidence

Baseline strict verification at the clean checkpoint passed: 25 source files,
1601 project declarations. Integrated checks finished at 2026-10-22T16:43:07.271047+00:00.
Pinned Lean 4.35.0, the dependency-free manifest, and Init-only production
closure are unchanged. WSL memory was 15 GiB total, about 12 GiB available,
with no swap. One build/audit ran at a time with LEAN_NUM_THREADS=1; the
completed presentation and normalization proof artifacts were reused.

| Command | Actual outcome |
| --- | --- |
| `bash scripts/verify.sh` | Exit 0: **26 Lean source files**, **1616 project declarations**, strict build, source screening, and transitive axiom audit. |
| `python3 scripts/check-audit-boundaries.py` | Exit 0; all three controls rejected with Lean exit 1 for the expected direct public, private-name, or hidden external illicit axiom. Public import closure passed. |
| `python3 scripts/check-presentation-boundaries.py` | Exit 0; projection equality via rfl and zero without a correctly typed existing-arrow witness each rejected with Lean exit 1 and the expected diagnostic. |
| `sha256sum -c SHA256SUMS`, cwd `manuscript/` | Exit 0 for unchanged v4 TeX/PDF. |
| `git diff --check` | Exit 0. |

Permitted axioms are exactly `propext`, `Quot.sound`, and `Classical.choice`.
The new raw invariant prints `[propext]`; the fourteen other new theorems
print `[propext, Quot.sound]`. No new theorem uses Classical.choice. No custom
axiom, proof hole, `native_decide`, new dependency, or new presentation equation
was added. The audit checks visible project declarations transitively,
including private names, rather than serving as an independent kernel replay.

Evidence is retained in `provenance/wsl-signed-label/`, including command
statuses, raw logs, negative-control sources/logs, source inventory, environment,
and reference metadata. Runtime records are in `.codex-work/signed-label/`.
The strict log records the baseline HEAD and dirty working source; exact
hashes identify the code actually checked. Integration SHA, post-commit checks,
Downloads receipts, and live SSH ref equality are recorded separately at
completion to avoid self-referential committed report hashes.

| Evidence | SHA-256 |
| --- | --- |
| `strict.log.txt` | `cc30af0e666164d0ffe722145f28c6f58200a9c14c7c2c174d2bdca6dcb97800` |
| `audit-boundaries.log.txt` | `377643b2b8fc2ff8c9b228992b82e2fd82c36bf57a7c3914aa71572ffbf89ac0` |
| `presentation-boundaries.log.txt` | `306041f8b1c343270cc1f8c841a6a6f6aa03451e17bb5f034cd495d3b5f49f66` |
| `source-SHA256SUMS` | `834eda733c31b36b2ad93e44440c78c8fbddb6649d8c03194ecaadf56cb01a52` |
| `evidence-SHA256SUMS` | `bfcbbb7d2d59c4350de3858c59bf8009300fe8207ac38bff69c242454042d00e` |
| `DosenPetric/PresentationSignedLabels.lean` | `01fbc357fa420010ee352b65cb0f25bbd92ec3f92b914fb2de9fe729ee526e8b` |
| `docs/reviews/SIGNED_LABEL_HOSTILE.md` | `9916b7a8338035cd580d77ab383cab2a6d9abddacac85713633dec47e613e846` |
| `docs/reviews/SIGNED_LABEL_WRITING.md` | `55344661fe11e85b3ef0904ecc69f999799b27a4d2fd060e90d60fc15f8bdf8d` |

Final report hashes are retained in `report-SHA256SUMS`. All finalized reports
are copied to Downloads and checked byte for byte against their repository
copies under AGENTS.md's conflict-preserving delivery procedure.

## Reviews and limitations

The [hostile-referee audit](reviews/SIGNED_LABEL_HOSTILE.md) addresses the
actual induction, quotient descent, source map, and boundary examples. It
found no confirmed defect in the scoped invariant; it is author-side work,
not independent peer review.

The [writing review](reviews/SIGNED_LABEL_WRITING.md) directly consults the
governing Knuth–Larrabee–Roberts text via its accessible MIT-hosted PDF and
includes the requested source-grounded normalization follow-up. Its SHA-256
is `9bf404c2c75633a1f39aae97af0b2e9335ce6d83cf386c84906654589b4e82e6`.
The previous provisional normalization review and access record remain
unchanged. Current Stanford requests still failed, but the identified course
text was read directly; the scoped follow-up is no longer provisional.
No byte identity with the Stanford scan or MAA edition is claimed.

No independent kernel replay, independent source-transcription review,
Challenge/Solution comparison, Comparator, official Palomar preflight/service
verification, novelty review, new manuscript compilation, whole-document
layout review, or publication was performed. Visibility and license were not
changed. Local source/import/axiom checks do not constitute those other checks.

## Remaining obligations and next proof

The signed-label invariant is closed for occurrenceMap. The faithful
OccurrenceInterpretation instance, Boolean Coherence, derived contravariant
arrow negation and naturality/dinaturality, restriction of all full proof
congruences and their separate substitution closure, substitution-schema
identity/composition and Appendix A correspondence, intended actual maximality,
and the every-interpretation model corollary remain open. All three coverage
milestones retain their distinct scope.

Next concrete proof endpoint: for arbitrary signed normal forms A,B and
f,g : Hom A.formula B.formula, prove `occurrenceMap f = occurrenceMap g → f = g`
in the actual equation quotient. Begin by constructing the source's §14.2
reduction to its signed-literal presentation (pp.318–321), with typed arrow
maps and occurrence compatibility; keep its unproved identities explicit.
The existing normalization transport/recovery then provides the route from
normal-form faithfulness to global coherence. Label preservation alone proves
neither normal-form faithfulness nor that reduction.
