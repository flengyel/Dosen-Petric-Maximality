# The manuscript's short q_A/e_A proof

The particular q_A and e_A maps in v7 Lemma 5.1 now have explicit primitive-arrow
inverses and both original-category inverse equations. The short collapse proof
of Lemma 5.2 is proved directly modulo a proof congruence and is connected to
actual-presentation maximality by `Presentation.short_maximality`. The previously
completed symmetric-fold route remains unchanged. The model corollary and
remaining operation, occurrence-coordinate and appendix claims continue under
the full-paper contract.

## The particular isomorphisms

`PresentationShortQ.lean` defines qTerm as the copair of fst;inl and inr, exactly
q_A : (A∧bot)∨top → A∨top. Its inverse copairs inr with the path
A → A∧top → A∧(bot∨top) → (A∧bot)∨top, using rightIn, identity tensor inr, and the
original distributor. `q_definition` identifies the manuscript map, and
`q_qInverse`/`qInverse_q` prove both inverse equations for every formula A.

`PresentationShortE.lean` defines eTerm as identity tensor inl, exactly
 e_A : A∧A → A∧(A∨top). `sourceConjTerm` is the actual mixed conjunction
comparison at arbitrary formula endpoints; `sectionTerm` first duplicates its
fixed factor. The inverse of e_A follows that section by the copair of identity
and the witnessed zero with explicit witness fst;diag : A∧top → A∧A. Thus the
extra copy in the unused summand contributes no path. `e_definition`,
`e_eInverse` and `eInverse_e` prove exact correspondence and both inverse laws.

These are concrete arrow constructions in the unchanged equation-generated
presentation. Their equalities use the already proved original-category
coherence and explicit complete relation calculations. No theorem infers
invertibility from a merely bijective occurrence graph. Distribution itself is
not claimed to be an isomorphism. All formulas, including constants, negative
literals and repeated occurrences, are allowed. Each raw construction and its
quotient arrow commutes with whole-arrow substitution; the ten equations in
`PresentationShortSubstitution.lean` allow different source/target variable
universes and preserve exact endpoint types.

## Collapse directly modulo the congruence

`PresentationShortTerminal.lean` proves the relevant witnessed zero equals the
path through top in the original category. Copairing K_A with the unchanged
second injection gives q_A equivalent to the terminal path. Precomposition with
q_A's proved inverse yields identity on E=A∨top equivalent to !_E;inr.
`terminal_hom` and `terminal_pair` prove uniqueness modulo the congruence of
existing arrows into E. This step does not use the symmetric-fold collapse.

`PresentationShortProjection.lean` sets r=fst : A∧E → A and
 i=pair(id_A,!_A;inr). The original equation i;r=id_A is proved; quotient-terminal
uniqueness gives r;i equivalent to identity. The original equation e_A;r=fst
transports this through e_A and its proved inverse. With u=i;e_A^{-1},
`projection_id` gives identity on A∧A equivalent to fst;u. Precomposition with
diag gives diag equivalent to u. Substitution in that equation and postcomposition
with snd equate the two projections. Precomposition with pair(f,g) equates every
existing parallel pair. `ShortProof.total` needs exactly all K_A and congruence
closure; coherence is never used in the quotient and j_A is never canceled.

`Presentation.short_maximality` obtains a signed literal K from the completed
isolation theorem, transports it to every formula using actual whole-arrow
substitution and double negation, and invokes this new short collapse. All
interfaces are actual source data. It has the same full proof-congruence and
substitution-closure hypotheses as the retained `Presentation.maximality`.
Both proof routes therefore reach the actual source quotient.

## Verification, review and delivery

Pinned Lean 4.35.0, strict verify.sh, full transitive allowed-axiom/source closure,
all 32 public check files, both boundary suites and 55 expected rejection controls
are required. New controls reject canceling the first injection, supplying only
one K_A and using e_A as an inverse in the wrong direction. Failed development
attempts remain separate from these expected rejections. Actual counts, commands,
exits and hashes are in provenance/wsl-short-proof/FINAL_VERIFICATION.json.
The checked archive is read back and compared with committed bytes.

The local hostile and writing reviews concern this actual argument and its
correspondence map. No new manuscript defect was established; all nine manuscript
blobs, three appendices, ten diagrams, accepted corrections and the stash remain
preserved. Reports and changed records are delivered from committed bytes with
conflict preservation and byte verification. DELIVERY_REGISTER.json and
DELIVERY_RECEIPT.json retain exact repository and Downloads paths. Independent
replay, Comparator, official/service verification and publication were not done.
The full paper remains unfinished: continue the universal-model corollary,
negation/substitution compatibility, original isolation witnesses, remaining
operation laws, non-cartesian-closure argument and all appendix correspondences.
