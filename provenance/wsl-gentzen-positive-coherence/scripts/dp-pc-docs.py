for src,dst in [('report','GENTZEN_COHERENCE_REPORT.md'),('hostile','reviews/GENTZEN_COHERENCE_HOSTILE.md'),('writing','reviews/GENTZEN_COHERENCE_WRITING.md')]:
 (root/'docs'/dst).write_bytes(Path('/tmp/dp-pc-'+src+'.md').read_bytes())
active='''## Current Positive, Reduced and Boolean coherence (29 October 2026)

`Gentzen.positive_coherence : PositiveCoherence P`, `Reduced.faithful : Faithful P`
and `Presentation.coherence` are proved for arbitrary P. The full intended
`Presentation.interpretation P` and its signed-label invariant are instantiated.
The public Nat instance is nonthin; Empty/constants and the original empty
Hom(top,bot) are preserved. Milestone I's complete intended faithful-interface
requirement is met. The conditional maximality theorem remains proved; the full
source congruence/substitution correspondence and actual maximality instantiation
remain to be completed. The three milestones and full-paper endpoint are distinct.

| Claim / source scope | Actual declarations | Exact status |
| --- | --- | --- |
| Positive cut-free representation | positive_cutFree_represented; positive_mix_represented | Actual CutFree/Atomized witnesses, exact original tags, pure-endpoint mix fragment. |
| Signed atomic paths | PurePort.position_ofPosition/position_injective; PureEdge.relation | Independent source/target positions; singleton relation; constants have no ports. |
| Finite atomic normal forms | finiteUnion laws; PureEdge.evaluate_faithful; G.mix_normal_form | Witnessed empty union, exact rule constructions and reversed-block mix; no assumed normalizer. |
| Restricted positive coherence | pure_positive_coherence; normal_positive_coherence | Pure base, then DNF source/CNF target via actual universal properties. |
| General formula expansions | NormalRetract; dnf_expansion/cnf_expansion | Explicit represented maps with only forward;backward=id_original. No distributive isomorphism. |
| Unrestricted positive coherence | Gentzen.represented_coherence; positive_coherence | Complete actual normal-form argument for arbitrary P. |
| Full Reduced coherence | Reduced.faithful | Existing common atomic factorization instantiated with proved PositiveCoherence. |
| Boolean coherence of the source quotient | Reduced.boolean_coherence; Presentation.coherence | Existing signed reduction, representation and original normalization transfers instantiated. |
| Intended full occurrence interface | Presentation.interpretation; interpretation_signedLabel | Every field is constructed in the equation-generated category, including faithfulness. |

All unrestricted cut elimination, twelve binary branches, fourteen blocked families,
Reducibility, Blocked-w, simultaneous cleaning and both Appendix C concrete rows
remain proved. All nine manuscript blobs, source decisions, stash and receipts
are preserved. No new manuscript defect was found. Coherence is used in the
original category; a fixed-valuation kernel is not assumed substitution-closed.

See [report](GENTZEN_COHERENCE_REPORT.md),
[hostile review](reviews/GENTZEN_COHERENCE_HOSTILE.md),
[writing review](reviews/GENTZEN_COHERENCE_WRITING.md).
Evidence: provenance/wsl-gentzen-positive-coherence/. Strict pinned verification,
all thirty public check files and 48 expected rejections have exact counts,
commands, exits and hashes in FINAL_VERIFICATION.json. Checked source archives
are read back and compared with committed bytes; DELIVERY_REGISTER.json retains
verified conflict-preserving repository/Downloads paths. Reviews are local
author-side; independent replay, Comparator, official/service verification and
publication remain separate unperformed statuses.

Next complete the full source congruence/uniform-substitution correspondence,
instantiate actual maximality, formalize the short q_A/e_A proof while retaining
the symmetric-fold route, and finish the model corollary and every remaining
mathematical claim in all three v7 appendices. Continue under the existing full-
paper authorization. Retained checkpoints below keep their historical scope;
this current table supersedes their earlier open coherence/normalization statuses.

'''
for rel in ['docs/MANUSCRIPT_STATEMENTS.md','docs/MANUSCRIPT_COVERAGE.md','docs/VALIDATION.md','docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md','README.md','docs/PRESENTATION_CORRESPONDENCE.md']:
 p=root/rel;s=p.read_text();a=s.index('\n')+1
 block=active if rel!='README.md' else active.replace('](GENTZEN_','](docs/GENTZEN_').replace('](reviews/','](docs/reviews/')
 s=s[:a]+'\n'+block+s[a:]
 s=s.replace('## Current unrestricted Gentzen cut elimination', '## Retained unrestricted Gentzen cut elimination checkpoint')
 if rel=='docs/PRESENTATION_CORRESPONDENCE.md':
  s=s.replace('## Current opposite logical checkpoint','## Retained opposite logical checkpoint').replace('## Current Reducibility correspondence: verified partial follow-up','## Retained Reducibility correspondence: verified partial follow-up')
  s=s.replace('correspondence. Boolean Coherence (§14.2, conclusion p.321) remains open.', 'correspondence. Boolean Coherence (§14.2, conclusion p.321) is now proved by\nPresentation.coherence through actual positive/reduced coherence. The original\nquotient remains generated equational equality; it is not redefined as relation equality.\nPresentation.interpretation supplies the full intended faithful interface. Full\nsource congruence/substitution correspondence and maximality remain continuing duties.')
 p.write_text(s)
# Reconcile the live milestone table rather than changing historical evidence.
p=root/'docs/MANUSCRIPT_COVERAGE.md';s=p.read_text();lines=s.splitlines()
for i,t in enumerate(lines):
 if t.startswith('| I | '):lines[i]='| I | Contextual collapse, relation calculations, and the complete structural/faithful-interpretation interface for the intended nonthin category | Complete: Presentation.interpretation P instantiates every field in the actual equation-generated category, with interpretation_signedLabel, the existing nonthin p theorem (public Nat witness) and preserved empty Hom(top,bot). The generated fragment remains preserved. |'
 if t.startswith('| II | '):lines[i]='| II | Maximality conditional on explicit coherence, normalization, presentation, and substitution inputs | relative_maximality remains proved. Actual source coherence, normalization, signed labels, substitution and double negation are now constructed; the full source congruence/uniform-substitution correspondence and explicit final instantiation remain continuing duties. |'
 if t.startswith('| III | '):lines[i]='| III | Maximality for the actual Došen–Petrić presentation with all bridges proved | Open: coherence and the intended occurrence interface are now proved. Complete the full source congruence/substitution correspondence and actual maximality theorem. This does not certify the full paper. |'
s='\n'.join(lines)+'\n';s=s.replace('Its occurrence interpretation is\nwell defined. Faithfulness remains open. The three milestones remain separate.', 'Its occurrence interpretation is now faithful by Presentation.coherence, and\nPresentation.interpretation is constructed. The three milestones remain separate.').replace('representation are now constructed; reduced faithfulness remains open.', 'representation and actual Reduced.faithful are now constructed.').replace('the remaining\ncoherence input is stated precisely as PositiveCoherence P.', 'the formerly open\nPositiveCoherence P input is now proved by Gentzen.positive_coherence.')
p.write_text(s)
p=root/'docs/MANUSCRIPT_STATEMENTS.md';s=p.read_text();lines=s.splitlines()
for i,t in enumerate(lines):
 if t.startswith('| `thm:coherence` |'):lines[i]='| `thm:coherence` | Presentation.coherence; Reduced.faithful/boolean_coherence; Presentation.interpretation | Boolean coherence is proved for the actual equation-generated presentation through actual PositiveCoherence, common atomic factorization and existing normalization transfers. Full intended faithful interface and signed-label invariant are instantiated. |'
 if t.startswith('| §14.2 common atomic factorization toward §3 coherence |'):lines[i]='| §14.2 common atomic factorization toward §3 coherence | commonAtomicFactor; faithful_of_positive_coherence; Reduced.faithful | Complete shared supported factorization is instantiated with Gentzen.positive_coherence, giving full Reduced faithfulness without additional mathematical inputs. |'
 if t.startswith('| Global signed-label preservation, §3 |'):lines[i]='| Global signed-label preservation, §3 | Presentation.occurrence_literal; interpretation_signedLabel | The direct signed-label theorem now instantiates the invariant of the actual Presentation.interpretation P, for arbitrary P and every source arrow. |'
p.write_text('\n'.join(lines)+'\n')
p=root/'docs/CODEX_FULL_MANUSCRIPT_FORMALIZATION.md';s=p.read_text();a=s.index('811eceeb and all successor reviews',s.index('## Immediate continuation'));b=s.index('At unchanged degree',a)
s=s[:a]+'''811eceeb and all successor reviews are incorporated. All unrestricted cut-
elimination interfaces and actual Positive, Reduced and Boolean coherence are now
proved. Presentation.interpretation P instantiates the full intended occurrence
interface, with signed labels and a nonthin Nat witness. Milestone I's intended
interface requirement is closed. Reuse every completed proof. Complete the full
source congruence/uniform-substitution correspondence and instantiate actual
maximality, then the short q_A/e_A route, model corollary and all remaining v7
claims under the unchanged full-paper endpoint. Preserve the accepted recursion
contract below as the already discharged cut-elimination argument.

'''+s[b:];p.write_text(s)
p=root/'AGENTS.md';s=p.read_text().replace('Continue restricted mix/positive/reduced/Boolean coherence and the full-paper bridges.', 'Actual PositiveCoherence, Reduced faithfulness and Boolean coherence now\ninstantiate Presentation.interpretation P with signed labels in the intended\ncategory. Continue full source congruence/uniform-substitution correspondence,\nactual maximality, both proof routes, model corollary and full-paper obligations.');p.write_text(s)
p=root/'docs/GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md';s=p.read_text();s+='''
## Actual coherence continuation (29 October 2026)

All unrestricted elimination interfaces remain complete. The actual positive,
Reduced and Boolean coherence argument and intended occurrence interpretation
are now proved; see GENTZEN_COHERENCE_REPORT.md. Finite atomic mix normal forms,
DNF/CNF comparison maps and one-sided recovery are constructed. Full source
congruence/substitution correspondence, maximality, model and remaining full-paper
claims continue; constructor coverage is not the full-paper certificate.
''';p.write_text(s)
p=root/'docs/MANUSCRIPT_CORRECTIONS.md';s=p.read_text();a=s.index('\n')+1;s=s[:a]+'''
## Actual coherence and intended interface continuation (29 October 2026)

Actual PositiveCoherence, Reduced faithfulness and Boolean coherence now supply
the full Presentation.interpretation P with signed-label preservation. Milestone
I's intended nonthin-interface requirement is closed by the actual Nat witness;
the source category and its empty hom-sets are unchanged. Explicit DNF/CNF
expansions use only the source's one-sided recovery laws, never distributive
isomorphisms. Tagged literal paths retain repeated positions and both signs;
empty unions retain existing-arrow witnesses. Current maps and milestone statuses
are reconciled together. No new manuscript defect was established; all nine
manuscript blobs and both Appendix C rows remain unchanged. A concrete public
coordinate check exposed inefficient automatic well-founded reduction; port
positions now use explicit structural matches for each connective. This is an
implementation correction, verified through the affected source and checks,
not a manuscript correction. Full congruence/maximality/model/appendix duties persist.
'''+s[a:];p.write_text(s)
p=root/'docs/CODEX_NEXT_SESSION.txt';old=p.read_bytes();history=root/'docs/history/CODEX_NEXT_SESSION_75B8E48.txt';assert not history.exists() or history.read_bytes()==old
if not history.exists():history.write_bytes(old)
s=old.decode().replace('CONTINUE V7 AFTER UNRESTRICTED CUT ELIMINATION: PROVE COHERENCE','CONTINUE V7 AFTER BOOLEAN COHERENCE: COMPLETE SOURCE MAXIMALITY BRIDGES')
s=s.replace('Read GENTZEN_CUT_ELIMINATION_REPORT.md', 'Read GENTZEN_COHERENCE_REPORT.md and its hostile/writing reviews, reusing\nGENTZEN_CUT_ELIMINATION_REPORT.md')
s=s.replace('Prior continuation: history/CODEX_NEXT_SESSION_263C452.txt, archived verbatim.', 'Prior continuation: history/CODEX_NEXT_SESSION_75B8E48.txt, archived verbatim.\nThe 263C452 continuation remains preserved.')
a=s.index('Current local evidence:');b=s.index('\nCONCRETE CONTINUATION',a)
s=s[:a]+'''Actual coherence is now proved: pure_positive_coherence, normal_positive_coherence,
explicit dnf_expansion/cnf_expansion with represented one-sided recovery,
Gentzen.positive_coherence, Reduced.faithful/boolean_coherence and
Presentation.coherence/interpretation/interpretation_signedLabel. G.mix_normal_form
constructs actual finite atomic forms; PurePort coordinates and singleton edge
relations are exact. finiteUnion requires an existing-arrow witness for its empty
case. Mix's reversed blocks, repeated tags, signs and constants are preserved.
Milestone I's full intended interface is instantiated and a Nat nonthin witness
is checked; the empty Hom(top,bot) persists. Full source congruence/substitution
correspondence and final actual maximality instantiation remain continuing duties.

Current local evidence: eighteen production modules; all thirty public files,
actual intended-interface/nonthin/empty/constant/signed-tag witnesses and 48
expected rejections; full strict source/dependency audit and checked/committed
source archive in provenance/wsl-gentzen-positive-coherence/. Actual counts,
exits/hashes and delivery paths are retained there. Prior results and all receipts
persist. Reviews are local author-side; independent replay, Comparator and
official/service checks were not performed.
'''+s[b:]
s=s.replace('1. Continue restricted mix/positive/reduced/Boolean coherence, actual intended-\npresentation and uniform-substitution/congruence bridges, the short q_A/e_A proof,', '1. Complete full source proof-congruence and uniform-substitution correspondence,\ninstantiate actual-presentation maximality, and formalize the short q_A/e_A proof,')
s=s.replace('44 controls.', '48 controls.')
s=s.replace('proof/receipt 80b9472 / 263c452. Deliver', 'proof/receipt 80b9472 / 263c452 and unrestricted cut-elimination proof/receipt\n852502b / 75b8e48. Deliver')
p.write_text(s)
print('Reconciled actual coherence and milestone I; source congruence/maximality and full-paper duties continue')
