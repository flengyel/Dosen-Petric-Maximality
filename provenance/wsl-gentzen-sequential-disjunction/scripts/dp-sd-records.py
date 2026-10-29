import gzip,io,tarfile,re
command(['git','diff','--check'],lock=False,name='diff-check')
assert subprocess.check_output(['git','stash','list','--format=%H'],cwd=root,text=True).strip()=='dedfd8fc8cd49930e9a162d5be585215b062a43c'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip().startswith('668fb50')
sourcepaths=sorted([root/'DosenPetric.lean',*root.glob('DosenPetric/**/*.lean'),*root.glob('Checks/**/*.lean')])
assert len(sourcepaths)==726
sourcepaths+= [root/p for p in ['AGENTS.md','lean-toolchain','lakefile.toml','lake-manifest.json','scripts/verify.sh','scripts/check-source.py','scripts/check-audit-boundaries.py','scripts/check-presentation-boundaries.py']]
manifest=''.join(sha(p.read_bytes())+'  '+str(p.relative_to(root))+'\n' for p in sourcepaths)
evidence.mkdir(parents=True,exist_ok=True)
(evidence/'CHECKED_SOURCES.sha256').write_text(manifest)
archive=io.BytesIO()
with tarfile.open(fileobj=archive,mode='w') as tar:
 for p in sourcepaths:
  b=p.read_bytes();info=tarfile.TarInfo(str(p.relative_to(root)));info.size=len(b);info.mode=0o644;info.mtime=0;tar.addfile(info,io.BytesIO(b))
b=gzip.compress(archive.getvalue(),mtime=0);(evidence/'CHECKED_SOURCES.tar.gz').write_bytes(b)
(evidence/'SOURCE_ARCHIVE.json').write_text(json.dumps(dict(source_count=len(sourcepaths),screened_lean_files=726,archive_sha256=sha(b),manifest_sha256=sha(manifest.encode()),base_commit='668fb50',byte_verified=True),indent=2)+'\n')
rows=[]
logdirs=[local,root/'.codex-work/gentzen-binary-cuts']
commandpaths=sorted(local.glob('*.json'))
for p in commandpaths:
 try:j=json.loads(p.read_text())
 except Exception:continue
 if isinstance(j,dict) and 'command' in j:rows.append(j)
(evidence/'COMMANDS.json').write_text(json.dumps(rows,indent=2)+'\n')
logs=evidence/'logs';logs.mkdir(exist_ok=True)
archived=[]
for p in sorted(local.glob('*.log')):
 b=p.read_bytes();target=logs/(p.name+'.gz');target.write_bytes(gzip.compress(b,mtime=0))
 assert gzip.decompress(target.read_bytes())==b
 archived.append(dict(original=str(p.relative_to(root)),retained=str(target.relative_to(root)),sha256=sha(b),gzip_sha256=sha(target.read_bytes())))
(evidence/'LOG_ARCHIVES.json').write_text(json.dumps(archived,indent=2)+'\n')
for name,src in [('AUDIT_CONTROLS','.codex-work/contextual-collapse/checks/report.json'),('PRESENTATION_CONTROLS','.codex-work/presentation-bridge/presentation-controls/report.json'),('FOCUSED_CONTROLS','.codex-work/gentzen-sequential-disjunction/FOCUSED_CONTROLS.json')]:
 (evidence/(name+'.json')).write_bytes((root/src).read_bytes())
# Retain actual control inputs and outputs separately from production source.
controlpaths=[*local.glob('equal-label-collapse.*'),*local.glob('mix-conventional-order.*'),*local.glob('missing-first-input-exchange.*'),*local.glob('missing-retained-B.*'),*local.glob('missing-conj-output-exchange.*'),*local.glob('missing-retained-A.*'),*local.glob('missing-second-output-exchange.*'),*local.glob('missing-disj-output-exchange.*'),*local.glob('missing-disj-retained-input.*'),*local.glob('missing-parallel-input-contraction.*'),*local.glob('missing-parallel-output-contraction.*'),*local.glob('blocked-equal-label-fixed-tag.*'),*local.glob('missing-terminal-*'),*local.glob('terminal-equal-label-principal-tag.*'),*local.glob('terminal-principal-is-fixed-copy.*'),*local.glob('conjunction-principal-is-fixed-copy.*'),*local.glob('missing-sequential-*'),*local.glob('sequential-*'),*local.glob('missing-prefix-*'),*local.glob('prefix-*'),*local.glob('fresh-disjunction-*')]
for rel in ['.codex-work/contextual-collapse/checks','.codex-work/presentation-bridge/presentation-controls']:
 controlpaths += [p for p in (root/rel).iterdir() if p.suffix in ['.lean','.log']]
for p in controlpaths:
 target=evidence/'controls'/p.name;target.parent.mkdir(exist_ok=True);target.write_bytes(p.read_bytes())
# Declaration anchors for all new production source, with actual namespace/name.
mods=sorted(p for p in (root/'DosenPetric').glob('Gentzen*.lean') if subprocess.run(['git','cat-file','-e','668fb50:'+str(p.relative_to(root))],cwd=root,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode!=0)
anchors=[]
for p in mods:
 ns=[]
 for line,t in enumerate(p.read_text().splitlines(),1):
  if t.startswith('namespace '):ns.append(t[len('namespace '):])
  if t.startswith('end ') and ns:ns.pop()
  m=re.match(r'(?:theorem|def|structure) (\w+)',t)
  if m:anchors.append('\t'.join(['.'.join(ns+[m.group(1)]),str(p.relative_to(root)),str(line)]))
(evidence/'DECLARATION_ANCHORS.tsv').write_text('declaration\tpath\tline\n'+'\n'.join(anchors)+'\n')
(evidence/'MODULES.tsv').write_text('module\tsha256\tlines\n'+''.join(p.stem+'\t'+sha(p.read_bytes())+'\t'+str(len(p.read_text().splitlines()))+'\n' for p in mods))
# Compare all manuscript bytes to incorporated successor, without rebuilding TeX.
manuscript=[]
for p in sorted((root/'manuscript').iterdir()):
 if p.is_file():
  rel=str(p.relative_to(root));old=subprocess.check_output(['git','show','668fb50:'+rel],cwd=root);assert old==p.read_bytes();manuscript.append(dict(path=rel,sha256=sha(old),unchanged=True))
(evidence/'MANUSCRIPT_HASHES.json').write_text(json.dumps(manuscript,indent=2)+'\n')
final={}
for name in ['strict','signature-BlockedDisjunction','signature-BlockedConjunction','signature-BlockedRightConj','signature-BlockedLeftDisj','signature-BlockedDisj','signature-BlockedGamma','signature-DisjBinaryCuts','signature-ConjLeftSecond','signature-ConjLeftFirst','signature-ConjRightFirst','signature-LogicalBinaryCuts','signature-BinaryMixCuts','signature-MixUnion','signature-BlockedW','signature-CleanCuts','signature-OppositeLogicalCuts','signature-PositionalCuts','signature-PrincipalConjunction','signature-PrincipalDisjunction','signature-Reducibility','signature-SameSideLogicalCuts','signature-StructuralCuts','audit-boundaries','presentation-boundaries','diff-check']:
 paths=sorted(local.glob(name+'-*.json'));assert paths,name;j=json.loads(paths[-1].read_text());assert j['exit_status']==0,j;final[name]=j
final.update(screened_lean_files=726,audited_project_declarations=int(re.search(r'PASS: transitive axiom checks for (\d+) project declarations', (root/final['strict']['log']).read_text())[1]),new_production_modules=len(mods),new_source_declarations=len(anchors),exact_check_files=22,negative_controls_rejected=29,preserved_stash='dedfd8fc8cd49930e9a162d5be585215b062a43c',independent_kernel_replay=False,comparator=False,official_service_verification=False,publication=False,full_paper_complete=False)
(evidence/'FINAL_VERIFICATION.json').write_text(json.dumps(final,indent=2)+'\n')
print(json.dumps({k:v for k,v in final.items() if not isinstance(v,dict)},indent=2))

assert len(mods)==12 and len(anchors)==53,(len(mods),len(anchors))
assert len(sourcepaths)==734
for p in sorted(local.glob('*.lean')):
 if not any(p.name.startswith(k) for k in ['missing-','equal-label','mix-conventional','blocked-equal','terminal-equal','terminal-principal','conjunction-principal','sequential-','prefix-','fresh-disjunction-']):
  target=evidence/'open'/p.name;target.parent.mkdir(exist_ok=True);target.write_bytes(p.read_bytes())
# All binary diagrams, including the formerly retained disjL candidate, are proved.
(evidence/'OPEN_OBLIGATIONS.json').write_text(json.dumps(dict(
 completed_binary_branches=12,remaining_logical_branches=0,
 completed_blocked_reductions=8,remaining_blocked_reductions=6,next_family='BlockedL.disjunctionFirst',remaining_families=dict(BlockedL=['disjunctionFirst','disjunctionSecond','disjunctionBoth'],BlockedR=['conjunctionFirst','conjunctionSecond','conjunctionBoth']),
 global_clean_rank_induction_complete=False,unrestricted_cut_elimination_complete=False,
 full_paper_complete=False),indent=2)+'\n')
for name in ['run','integrate','controls','docs','records','deliver']:
 script=Path('/tmp/dp-'+('first' if name=='run' else 'sd')+'-'+name+'.py')
 if script.exists():
  target=evidence/'scripts'/script.name;target.parent.mkdir(exist_ok=True);target.write_bytes(script.read_bytes())

# A lock rejection is a command that did not elaborate, not a proof failure/control.
(evidence/'CHECK_ATTEMPT_STATUS.json').write_text(json.dumps(dict(
 lock_rejections=[r for r in rows if r['exit_status'] and r['seconds']<0.02 and r['sha256']==sha(b'')],
 production_checks_final='FINAL_VERIFICATION.json',
 next_diagram_attempts_are_open_obligations=False),indent=2)+'\n')

# Read the archive back and verify every retained member's exact bytes.
with tarfile.open(fileobj=io.BytesIO(gzip.decompress((evidence/'CHECKED_SOURCES.tar.gz').read_bytes())),mode='r:') as tar:
 assert len(tar.getmembers())==len(sourcepaths)
 for m in tar.getmembers():assert tar.extractfile(m).read()==(root/m.name).read_bytes()

(evidence/'RESOLVED_DIAGRAM.json').write_text(json.dumps(dict(
 native_equation='SequentialDisjunction.native_equation',
 original_source_equation='BlockedDisjunction.source_equation',
 original_rank_step='CutCommutation.blockedR_disjunction_rank_step',
 appendix_c_p260_complete=True,appendix_c_p262_complete=False),indent=2)+'\n')
