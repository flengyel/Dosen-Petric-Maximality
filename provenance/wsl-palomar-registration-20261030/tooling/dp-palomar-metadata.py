import yaml
p=rc/'formalization.yaml'
y=yaml.safe_load((rc/'docs/palomar/formalization.proposed.yaml').read_text())
y['classification']['msc2020']=['03G30','03F07','18A32']
y['project']['description']=y['project']['description'].replace('proposed registry selection','registry selection')
y['status']['scope']='The full-paper production development is complete at mathematical source 630c4b6e47da16a1434476a211fd29ce6adc5569 and completion head 6a66b14b382aac214b52c055b8bf281b35302239. This candidate selects five actual-source statements: two maximality proofs, the congruence dichotomy, a nonzero literal identity, and an empty hom-set. The retained complete-paper claim map covers the additional coherence, model and appendix results. The exact local build, definition comparison and independent replay outcomes are recorded in docs/PALOMAR_REGISTRATION_LOCAL_REPORT.md. Official full preflight, service verification, editorial outcome and registration remain pending.'
y['fidelity']['divergences']='The three maximality statements retain the manuscript\'s nonempty-variable hypothesis; the underlying production theorems are stronger. The compact primitive congruence acts on actual typed raw terms and contains all generating equations. Uniform substitution acts on terms and both endpoints. PalomarCorrespondence proves descent to the actual quotient, the inverse restriction of full proof congruences, pointwise relation correspondence, substitution closure, totality and distinctness correspondence, and admissibility of derived negation. Its closed-class extension uses the previously proved fragment dichotomy. The selected short proof instead uses the fragment directly, actual source isolation, uniform contextual collapse and ShortProof.total with the particular q/e arrows. Empty hom-sets and distinct occurrence tags are preserved. No new priority or exhaustive novelty assessment was performed during packaging.'
y['review']['notes']='The full development has AI-assisted author-side reviews in docs/reviews/FULL_PAPER_6A66B14_REVIEW.md and docs/reviews/FULL_PAPER_6A66B14_WRITING.md. The new statement, definition correspondence and metadata are reviewed separately in docs/reviews/PALOMAR_REGISTRATION_REVIEW.md and docs/reviews/PALOMAR_REGISTRATION_WRITING.md. These are agent reviews, not external human peer review or Palomar acceptance. Independent-kernel outcomes are recorded separately in the local report.'
notes=[
'The source/fold proof uses the fully instantiated actual equation-generated presentation through fragment_maximality. Raw/quotient correspondence is proved in PalomarCorrespondence.',
'The actual q/e proof uses normalized_literal_context, all_contexts and ShortProof.total directly, without invoking the fold maximality theorem or manufacturing totality through the full-congruence extension.',
'Generated equality is Derives; quotient equality, full congruence relations and totality have proved correspondence.',
'The actual quotient witness identity_ne_primitive_zero rules out generated equality with zero at each supplied variable.',
'The actual source truth interpretation proves that no raw term inhabits the terminal-to-initial hom-set.'
]
for a,n in zip(y['alignment']['statements'],notes):a['status']='proved';a['note']=n
p.write_text('# Release candidate: Apache-2.0 and public release await the author\'s concrete decision.\n# yaml-language-server: $schema=https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/99c678e569c7c4c0772db297c5ddd5e4c9b6322e/schema/formalization.schema.json\n'+yaml.safe_dump(y,allow_unicode=True,sort_keys=False,width=100))
(rc/'LICENSE').write_bytes((rc/'docs/palomar/LICENSE.Apache-2.0.proposed.txt').read_bytes())
w=rc/'.github/workflows/palomar-preflight.yml';w.parent.mkdir(parents=True,exist_ok=True)
w.write_bytes((rc/'docs/palomar/palomar-preflight.yml.example').read_bytes())
# Correct reference enumeration without changing any original evidence bytes.
p=ev/'HISTORICAL_SOURCE_RELOCATIONS.json';j=json.loads(p.read_text())
texts=[]
for q in rc.rglob('*'):
 rel=q.relative_to(rc)
 if q.is_file() and not any(x in rel.parts for x in ['.git','.lake','.codex-work']) and q.suffix in ['.md','.txt','.json','.tsv','.sha256'] and q!=p:
  try:texts.append((str(rel),q.read_text()))
  except UnicodeError:pass
for r in j['relocations']:r['historical_references']=[q for q,t in texts if r['original'] in t]
p.write_text(json.dumps(j,indent=2)+'\n')
print('Candidate metadata, proposed license and manual-only workflow installed; reference mapping updated')
