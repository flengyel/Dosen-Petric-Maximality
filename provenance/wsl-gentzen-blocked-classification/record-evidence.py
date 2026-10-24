from pathlib import Path
import datetime,hashlib,json,re,shutil,subprocess
r=Path('/home/flengyel/src/Dosen-Petric-Maximality')
w=r/'.codex-work/gentzen-blocked-classification'
p=r/'provenance/wsl-gentzen-blocked-classification'
base='6b860df5fdb6e4c1c50dc583e0de0d04c102eb25'
hashbytes=lambda x:hashlib.sha256(x).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=r)
reports=['docs/GENTZEN_BLOCKED_CLASSIFICATION_REPORT.md','docs/reviews/GENTZEN_BLOCKED_CLASSIFICATION_HOSTILE.md','docs/reviews/GENTZEN_BLOCKED_CLASSIFICATION_WRITING.md']
records=['README.md','docs/MANUSCRIPT_STATEMENTS.md','docs/MANUSCRIPT_COVERAGE.md','docs/PRESENTATION_CORRESPONDENCE.md','docs/VALIDATION.md','docs/CODEX_NEXT_SESSION.txt','docs/CONTINUATION.txt','docs/CODEX_GENTZEN_MIXED_W5_DISPATCH.txt']
allowed={'DosenPetric.lean','Checks/Axioms.lean',*records}
tracked_changes=git('diff','--name-only',base).decode().splitlines()
older_tracked=set(git('ls-tree','-r','--name-only',base).decode().splitlines())
assert all(n not in older_tracked or n in allowed for n in tracked_changes),tracked_changes
assert git('rev-parse','refs/stash').decode().strip()=='dedfd8fc8cd49930e9a162d5be585215b062a43c'
assert not git('ls-files','--others','--exclude-standard','--','*.lean').decode().strip()
final_path=w/'final-20261024T224230269059.json'
final=json.loads(final_path.read_text());assert len(final['checks'])==6 and all(x['exit_status']==0 for x in final['checks'])
strict=r/final['checks'][0]['log'];text=strict.read_text()
assert 'PASS: 216 source files;' in text
assert 'PASS: transitive axiom checks for 8406 project declarations' in text
sources=[]
for line in text.splitlines():
 m=re.fullmatch(r'([0-9a-f]{64}) (\S+\.lean)',line)
 if m:
  expected,name=m.groups();assert hashbytes((r/name).read_bytes())==expected,name
  sources.append(name)
assert len(sources)==216,len(sources)
sources+=['lean-toolchain','lakefile.toml','lake-manifest.json','scripts/verify.sh','scripts/check-source.py','scripts/check-audit-boundaries.py','scripts/check-presentation-boundaries.py']
assert len(sources)==223
assert not p.exists()
# Preserve command attempts and metadata. Unowned concurrent source snapshots stay ignored.
shutil.copytree(w,p,ignore=shutil.ignore_patterns('concurrent-work-snapshot'))
for source,dest in [('/tmp/dp-blocked-classification-run.py','run-verification.py'),('/tmp/dp-blocked-candidate-run.py','run-isolated-attempt.py'),('/tmp/dp-blocked-classification-records.py','record-evidence.py')]:shutil.copy2(source,p/dest)
shutil.copytree(r/'.codex-work/contextual-collapse/checks',p/'audit-controls')
shutil.copytree(r/'.codex-work/presentation-bridge/presentation-controls',p/'presentation-controls')
audit=json.loads((p/'audit-controls/report.json').read_text())
controls=audit['checks'][:3]+json.loads((p/'presentation-controls/report.json').read_text())
assert len(controls)==5 and all(x['passed'] and x['exit_status']==1 for x in controls)
assert audit['checks'][3]['passed']
source_access=p/'source-access';source_access.mkdir()
old=r/'provenance/wsl-gentzen-proof-replacement/source-access'
for f in old.iterdir():
 if f.is_file():shutil.copy2(f,source_access/f.name)
shutil.copy2(w/'source-p250.png',source_access/'dp-blocked-classification-p250.png')
source_record={'source':{'revision':'September 2007','url':'https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf','sha256':'e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e','printed_pages':'248-253; seven blocked patterns and proper-ancestor reducibility p.250; W1-W6 pp.251-253 and right analogue','pdf_pages_one_based':'260-265','rendered_page':'printed 250 / PDF 262; retained pp.251-252'},'writing':{'cache':'.codex-work/references/knuth-mathematical-writing-mit-9bf404c2.pdf','sha256':'9bf404c2c75633a1f39aae97af0b2e9335ce6d83cf386c84906654589b4e82e6','consulted':'Section 1 printed pp.1-6/PDF pp.3-8 and section 4 definition placement, printed p.9/PDF p.11','edition':'MIT-hosted typeset report; no byte identity with Stanford scan/MAA asserted'},'new_source_discrepancies':[],'source_encoding_boundary':'Explicit terminal disjL exchange macro and canonical last-retaining right contraction; source first retention is an exchange macro. No global macro/rank transport or strictification supplied.'}
for cache,key in [('.codex-work/references/dosen-petric-coh-september-2007-e285235f.pdf','source'),('.codex-work/references/knuth-mathematical-writing-mit-9bf404c2.pdf','writing')]:assert hashbytes((r/cache).read_bytes())==source_record[key]['sha256']
(p/'SOURCE_CONSULTATION.json').write_text(json.dumps(source_record,indent=2)+'\n')
mods=(w/'NEW_MODULES.txt').read_text().splitlines();declarations=[]
for module in mods:
 name='DosenPetric/'+module+'.lean';scopes=[]
 for num,line in enumerate((r/name).read_text().splitlines(),1):
  m=re.match(r'namespace (\S+)',line)
  if m:scopes.append(('namespace',m.group(1)));continue
  m=re.match(r'section(?: (\S+))?$',line)
  if m:scopes.append(('section',m.group(1)));continue
  if re.match(r'end(?: |$)',line):
   assert scopes,(name,num,line)
   scopes.pop();continue
  m=re.match(r'(?:noncomputable )?(def|abbrev|theorem|structure|inductive) (\S+)',line)
  if m:
   kind,local=m.groups();ns='.'.join(value for k,value in scopes if k=='namespace')
   declarations.append({'name':ns+'.'+local,'kind':kind,'path':name,'line':num,'source':line})
assert len(declarations)==123,len(declarations)
(p/'DECLARATIONS.json').write_text(json.dumps(declarations,indent=2)+'\n')
(p/'DECLARATIONS.txt').write_text(''.join(f"{x['path']}:{x['line']} {x['name']}\n{x['source']}\n\n" for x in declarations).rstrip()+'\n')
for dest,names in [('SOURCE_SHA256SUMS',sources),('REPORT_SHA256SUMS',reports),('RECORD_SHA256SUMS',records)]:
 (p/dest).write_text(''.join(f'{hashbytes((r/name).read_bytes())}  {name}\n' for name in sorted(names)))
for name in reports+records:
 assert not re.search(r'__(?:FINAL|CURRENT|REVIEW|WRITING)_', (r/name).read_text()),name
 for match in re.finditer(r'\[[^\]]*\]\(([^)]+)\)',(r/name).read_text()):
  link=match.group(1)
  if '://' not in link and not link.startswith('#'):assert ((r/name).parent/link.split('#',1)[0]).resolve().exists(),(name,link)
types=json.loads(max(w.glob('types-*.json')).read_text());assert types['checks'][0]['exit_status']==0
assert (w/'PublicTypes.lean').read_text().count('#check')==137
shutil.copy2(r/types['checks'][0]['log'],p/'PUBLIC_TYPES.txt')
selected=(w/'SELECTED_NAMES.txt').read_text().splitlines();assert len(selected)==83
axiom_lines=[line for line in text.splitlines() if any(line.startswith("'"+name+"'") for name in selected)]
assert len(axiom_lines)==83,len(axiom_lines)
(p/'SELECTED_AXIOMS.txt').write_text('\n'.join(axiom_lines)+'\n')
baseline=json.loads((w/'baseline-20261024T220112983252.json').read_text())
assert all(x['exit_status']==0 for x in baseline['checks'])
summary={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'base_commit':base,'baseline':baseline,'final':final,'public_types':types,'baseline_files':208,'baseline_declarations':7972,'final_files':216,'final_declarations':8406,'new_modules':mods,'explicit_source_declarations':len(declarations),'extra_constructor_type_queries':14,'selected_axiom_prints':len(selected),'all_five_negative_controls_rejected':True,'public_import_closure_passed':True,'checked_source_inventory_entries':len(sources),'frozen_baseline_paths_unchanged':True,'intentional_modified_baseline_paths':sorted(set(tracked_changes)&older_tracked),'all_proof_bytes_match_final_strict_inventory':True,'optional_isolated_build':'Interrupted exit 130; not acceptance. Final successful checks use original checkout after frozen proof comparison and no extra Lean sources.','concurrent_work':'Transient untracked overlapping sources left untouched; ignored snapshots not copied into committed evidence. Shared work directory contains other command attempts; preserve logs without attributing all of them to this proof candidate.','reviews':'Author-side AI-assisted hostile and source-grounded writing reviews; not independent certification','next_task':'Mixed-premise W5, including singleton branches, exact selected profile extraction, full fibers/ranks and nested proof replacement; global reduction/rank control remains open','commit_ref_and_delivery_receipts':'.codex-work/gentzen-blocked-classification/'}
(p/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
inventory=[]
for f in sorted(p.rglob('*')):
 if f.is_file() and f.name!='EVIDENCE_SHA256SUMS':inventory.append(f'{hashbytes(f.read_bytes())}  {f.relative_to(p)}\n')
(p/'EVIDENCE_SHA256SUMS').write_text(''.join(inventory))
print(json.dumps({'source_entries':len(sources),'explicit_declarations':len(declarations),'new_selected_axiom_prints':len(selected),'retained_evidence_files':len(inventory),'final_counts':[216,8406],'baseline_preservation_verified':True},indent=2))
