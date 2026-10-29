import gzip,io,tarfile,re
command(['git','diff','--check'],lock=False,name='diff-check')
base_commit='d8dc710e19504f82b540c18e586c9ece491c3977'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()==base_commit
assert subprocess.check_output(['git','stash','list','--format=%H'],cwd=root,text=True).strip()=='dedfd8fc8cd49930e9a162d5be585215b062a43c'
sourcepaths=sorted([root/'DosenPetric.lean',*root.glob('DosenPetric/**/*.lean'),*root.glob('Checks/**/*.lean')])
lean_count=len(sourcepaths);assert lean_count==847,lean_count
sourcepaths += [root/p for p in ['AGENTS.md','lean-toolchain','lakefile.toml','lake-manifest.json','scripts/verify.sh','scripts/check-source.py','scripts/check-audit-boundaries.py','scripts/check-presentation-boundaries.py']]
evidence.mkdir(parents=True,exist_ok=True)
manifest=''.join(sha(p.read_bytes())+'  '+str(p.relative_to(root))+'\n' for p in sourcepaths)
(evidence/'CHECKED_SOURCES.sha256').write_text(manifest)
archive=io.BytesIO()
with tarfile.open(fileobj=archive,mode='w') as tar:
 for p in sourcepaths:
  b=p.read_bytes();info=tarfile.TarInfo(str(p.relative_to(root)));info.size=len(b);info.mode=0o644;info.mtime=0;tar.addfile(info,io.BytesIO(b))
b=gzip.compress(archive.getvalue(),mtime=0);(evidence/'CHECKED_SOURCES.tar.gz').write_bytes(b)
with tarfile.open(fileobj=io.BytesIO(gzip.decompress(b)),mode='r:') as tar:
 assert len(tar.getmembers())==len(sourcepaths)
 for m in tar.getmembers():assert tar.extractfile(m).read()==(root/m.name).read_bytes()
(evidence/'SOURCE_ARCHIVE.json').write_text(json.dumps(dict(source_count=len(sourcepaths),screened_lean_files=lean_count,archive_sha256=sha(b),manifest_sha256=sha(manifest.encode()),base_commit=base_commit,byte_verified=True),indent=2)+'\n')
rows=[]
for p in sorted(local.glob('*.json')):
 try:j=json.loads(p.read_text())
 except Exception:continue
 if isinstance(j,dict) and 'command' in j:rows.append(j)
(evidence/'COMMANDS.json').write_text(json.dumps(rows,indent=2)+'\n')
logs=evidence/'logs';logs.mkdir(exist_ok=True)
archived=[]
for p in sorted(local.glob('*.log')):
 b=p.read_bytes();target=logs/(p.name+'.gz');target.write_bytes(gzip.compress(b,mtime=0));assert gzip.decompress(target.read_bytes())==b
 archived.append(dict(original=str(p.relative_to(root)),retained=str(target.relative_to(root)),sha256=sha(b),gzip_sha256=sha(target.read_bytes())))
(evidence/'LOG_ARCHIVES.json').write_text(json.dumps(archived,indent=2)+'\n')
for name,src in [('AUDIT_CONTROLS','.codex-work/contextual-collapse/checks/report.json'),('PRESENTATION_CONTROLS','.codex-work/presentation-bridge/presentation-controls/report.json'),('FOCUSED_CONTROLS','.codex-work/full-paper-claims/FOCUSED_CONTROLS.json')]:
 (evidence/(name+'.json')).write_bytes((root/src).read_bytes())
focused=json.loads((evidence/'FOCUSED_CONTROLS.json').read_text());assert len(focused)==56 and all(r['passed'] for r in focused)
for row in focused:
 for key in ['source','log']:
  p=root/row[key];target=evidence/'controls'/p.name;target.parent.mkdir(exist_ok=True);target.write_bytes(p.read_bytes())
for rel in ['.codex-work/contextual-collapse/checks','.codex-work/presentation-bridge/presentation-controls']:
 for p in (root/rel).iterdir():
  if p.suffix in ['.lean','.log']:
   target=evidence/'controls'/p.name;target.parent.mkdir(exist_ok=True);target.write_bytes(p.read_bytes())
mods=sorted(p for p in (root/'DosenPetric').glob('*.lean') if subprocess.run(['git','cat-file','-e',base_commit+':'+str(p.relative_to(root))],cwd=root,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode!=0)
assert len(mods)==14
anchors=[]
for p in mods:
 ns=[]
 for line,t in enumerate(p.read_text().splitlines(),1):
  if t.startswith('namespace '):ns.append(t[len('namespace '):])
  if t.startswith('end ') and ns:ns.pop()
  m=re.match(r'(?:@\[[^]]+\]\s+)?(?:noncomputable\s+)?(?:theorem|def|structure|inductive|abbrev|instance) (\w+)',t)
  if m:anchors.append('\t'.join(['.'.join(ns+[m.group(1)]),str(p.relative_to(root)),str(line)]))
(evidence/'DECLARATION_ANCHORS.tsv').write_text('declaration\tpath\tline\n'+'\n'.join(anchors)+'\n')
(evidence/'MODULES.tsv').write_text('module\tsha256\tlines\n'+''.join(p.stem+'\t'+sha(p.read_bytes())+'\t'+str(len(p.read_text().splitlines()))+'\n' for p in mods))
manuscript=[]
for p in sorted((root/'manuscript').iterdir()):
 if p.is_file():
  rel=str(p.relative_to(root));old=subprocess.check_output(['git','show',base_commit+':'+rel],cwd=root);assert old==p.read_bytes();manuscript.append(dict(path=rel,sha256=sha(old),unchanged=True))
assert len(manuscript)==9
(evidence/'MANUSCRIPT_HASHES.json').write_text(json.dumps(manuscript,indent=2)+'\n')
final={}
checknames=['signature-'+p.stem for p in sorted((root/'Checks').glob('*.lean')) if p.stem!='Axioms']
assert len(checknames)==33,len(checknames)
for name in ['strict',*checknames,'audit-boundaries','presentation-boundaries','diff-check']:
 paths=sorted(local.glob(name+'-*.json'));assert paths,name;j=json.loads(paths[-1].read_text());assert j['exit_status']==0,j;final[name]=j
final.update(screened_lean_files=lean_count,audited_project_declarations=int(re.search(r'PASS: transitive axiom checks for (\d+) project declarations',(root/final['strict']['log']).read_text())[1]),new_production_modules=len(mods),new_source_declarations=len(anchors),exact_check_files=len(checknames),negative_controls_rejected=61,preserved_stash='dedfd8fc8cd49930e9a162d5be585215b062a43c',independent_kernel_replay=False,comparator=False,official_service_verification=False,publication=False,full_paper_complete=False)
(evidence/'FINAL_VERIFICATION.json').write_text(json.dumps(final,indent=2)+'\n')
(evidence/'OPEN_OBLIGATIONS.json').write_text(json.dumps(dict(completed_binary_branches=12,completed_blocked_reductions=14,remaining_logical_branches=0,remaining_blocked_reductions=0,global_constructor_tag_dispatch_complete=True,global_clean_rank_induction_complete=True,strong_degree_induction_complete=True,arbitrary_G_normalization_complete=True,unrestricted_cut_elimination_complete=True,atomized_cut_elimination_complete=True,coherence_complete=True,positive_coherence_complete=True,reduced_faithful_complete=True,boolean_coherence_complete=True,intended_occurrence_interface_complete=True,milestone_I_complete=True,full_source_substitution_congruence_correspondence_complete=True,actual_presentation_maximality_complete=True,derived_negation_complete=True,negation_naturality_complete=True,quotient_reduction_functor_complete=True,quotient_recovery_complete=True,negation_substitution_compatibility_complete=True,original_isolation_witnesses_complete=True,cartesian_closure_obstruction_complete=True,appendix_B_complete=True,displayed_symmetric_fold_complete=True,whole_arrow_block_square_complete=True,substitution_label_square_complete=True,formula_substitution_identity_composition_complete=True,arrow_substitution_action_composition_complete=False,appendix_A_profiles_ordinals_complete=False,manuscript_scope_refresh_complete=False,short_q_e_proof_complete=True,model_corollary_complete=False,full_paper_complete=False,next_obligation='full_source_model_corollary_and_remaining_appendix_A_action_and_scope_claims'),indent=2)+'\n')
(evidence/'CHECK_ATTEMPT_STATUS.json').write_text(json.dumps(dict(failed_development_checks=[r for r in rows if r['exit_status']!=0],counted_as_expected_rejection=False,final_checks='FINAL_VERIFICATION.json'),indent=2)+'\n')
for name in ['run','integrate','controls','docs','records','deliver','polish']:
 script=Path('/tmp/dp-'+('first' if name=='run' else 'fp')+'-'+name+'.py')
 if script.exists():
  target=evidence/'scripts'/script.name;target.parent.mkdir(exist_ok=True);target.write_bytes(script.read_bytes())
print(json.dumps({k:v for k,v in final.items() if not isinstance(v,dict)},indent=2))
