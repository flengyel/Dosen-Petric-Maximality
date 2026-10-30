exec(Path('/tmp/dp-palomar-common.py').read_text())
import fcntl
root=work/'package-controls-v2';root.mkdir(exist_ok=True)
base_config=v.load_comparator_config(rc/'comparator.json')
targets=json.loads((ev/'SELECTED_EXPORT_TARGETS.json').read_text())
original=(rc/'Challenge.lean').read_text()
final=json.loads((ev/'CANONICAL_CHALLENGE.json').read_text())
for a in final['artifacts']:tools[Path(a['path'])]=a['sha256']
for name in ['CHALLENGE','SOLUTION']:
 r=json.loads((ev/(name+'_SELECTED_EXPORT_HASH.json')).read_text());p=Path(r['path']);assert sha(p.read_bytes())==r['sha256'];tools[p]=r['sha256']
rows=json.loads((ev/'PACKAGE_CONTROLS_PARTIAL.json').read_text()) if (ev/'PACKAGE_CONTROLS_PARTIAL.json').exists() else []
fixture_dir=ev/'controls';fixture_dir.mkdir(exist_ok=True)
def fixture(path,text):
 path.write_text(text)
 dest=fixture_dir/(path.parent.name+'-'+path.name+'.txt');dest.write_text(text)
 return dict(repository_path=str(dest.relative_to(rc)),sha256=sha(text.encode()))
def judge(name,config,ch,sol,needle):
 p=v.judge_exports(lake=bins['lake'],config=config,challenge_export=ch,solution_export=sol,scratch=root/('judge-'+name),bwrap=bwrap,lean_prefix=prefix,environment=base_env,tools=tools,timeout=v.EXECUTION_BUDGET_SECONDS)
 rec=proc_record('CONTROL_'+name.upper(),p);log=p.stdout+'\n'+p.stderr
 assert p.returncode!=0 and needle in log,(name,p.returncode,log)
 verdict=v.comparator_verdict(p.returncode,log)
 assert verdict is not None and verdict.code in ['comparator.rejected','comparator.illegal_axiom'], verdict
 return dict(name=name,status='rejected_as_required',reason=needle,verdict=verdict.code,**rec)
def control_challenge(name,text,needle):
 if any(r['name']==name for r in rows):return
 d=root/name
 if d.exists():d.rename(root/(name+'-failed-'+str(time.time_ns())))
 d.mkdir();src=d/'Challenge.lean';source=fixture(src,text)
 cfg=v.protected_comparator_config(rc/'comparator.json',d/'protected.json',kernels=kernels)
 alias=json.loads(cfg.read_text())['challenge_module']
 canonical,deps,paths=v.compile_canonical_challenge(d,d,checkout=d,challenge_source=src,challenge_module='Challenge',published_module=alias,lean=bins['lean'],lean_prefix=prefix,allowlist={},environment=base_env,readable_paths=[rc,root,*v.system_readable_paths()],executable_paths=exe,tools=tools)
 env=dict(base_env,LEAN_PATH=os.pathsep.join([str(d/'canonical-challenge'),str(prefix/'lib/lean')]))
 output=d/'Challenge.export'
 p=v.export_module(alias,targets,output=output,leanexport=bins['leanexport'],cwd=rc,environment=env,readable_paths=[rc,root,*v.system_readable_paths()],executable_paths=exe,tools=tools,timeout=v.EXECUTION_BUDGET_SECONDS)
 assert p.returncode==0,p.stderr
 tools[output]=sha(output.read_bytes())
 row=judge(name,cfg,output,work/'Solution-selected.export',needle);row.update(fixture=source,compiled=True,exported=True,challenge_export_sha256=tools[output]);rows.append(row)
def control_solution(name,text,needle):
 if any(r['name']==name for r in rows):return
 d=root/name
 if d.exists():d.rename(root/(name+'-failed-'+str(time.time_ns())))
 d.mkdir();lib=d/'lib';lib.mkdir();src=d/(name+'.lean');source=fixture(src,text)
 env=dict(base_env,LEAN_PATH=os.pathsep.join([str(lib),str(work/'canonical-challenge'),str(rc/'.lake/build/lib/lean'),str(prefix/'lib/lean')]))
 p=v.sandboxed_run([str(bins['lean']),'-o',str(lib/(name+'.olean')),str(src)],cwd=d,environment=env,writable_directories=[lib],readable_paths=[rc,work,*v.system_readable_paths()],executable_paths=exe,tools=tools)
 proc_record('CONTROL_'+name.upper()+'_COMPILE',p)
 output=d/'Solution.export'
 p=v.export_module(name,targets,output=output,leanexport=bins['leanexport'],cwd=d,environment=env,readable_paths=[rc,work,*v.system_readable_paths()],executable_paths=exe,tools=tools,timeout=v.EXECUTION_BUDGET_SECONDS)
 assert p.returncode==0,p.stderr
 tools[output]=sha(output.read_bytes())
 row=judge(name,work/'protected-comparator.json',work/'Challenge-selected.export',output,needle);row.update(fixture=source,compiled=True,exported=True,solution_export_sha256=tools[output]);rows.append(row)
with (main/'.codex-work/build.lock').open('a') as build_lock:
 fcntl.flock(build_lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 changed=original.replace('| constant_swap (o : Op) (C : Formula P) (h : Constant C)', '| constant_swap (o : Op) (C : Formula P) (h : Constant C ∧ True)',1)
 assert changed!=original
 control_challenge('ChangedEquation',changed,"Const does not match between challenge and target 'DosenPetric.Presentation.Equation")
 save('PACKAGE_CONTROLS_PARTIAL.json',rows)
 changed=original.replace('(hne : ¬ Derives f g)', '(hne : ¬ Derives g f)',1);assert changed!=original
 control_challenge('ChangedSelectedType',changed,'Challenge and solution theorem statement do not match')
 save('PACKAGE_CONTROLS_PARTIAL.json',rows)
 solution=(rc/'DosenPetric/PalomarMaximality.lean').read_text()
 solution=solution.replace('variable {P : Type u}', 'variable {P : Type u}\n\naxiom illicitFalse : False\nprivate theorem hiddenFalse : False := illicitFalse',1)
 a=solution.index(' := by',solution.index('theorem maximality'))+len(' := by');b=solution.index('/-- The same raw',a)
 solution=solution[:a]+'\n  exact False.elim hiddenFalse\n\n'+solution[b:]
 control_solution('IllicitAxiomHelper',solution,'Illegal axiom detected:')
 save('PACKAGE_CONTROLS_PARTIAL.json',rows)
 control_solution('SelectedChallengeHole','module\n\npublic import '+final['module']+'\n',"Illegal axiom detected: 'sorryAx'")
 save('PACKAGE_CONTROLS_PARTIAL.json',rows)
 # Headers are parsed without elaboration: neither duplicate declarations nor
 # missing compiled modules can be the cause of these import-policy rejections.
 for name,transitive in [('DirectForbiddenImport',False),('TransitiveForbiddenImport',True)]:
  if any(r['name']==name for r in rows):continue
  d=root/name
  if d.exists():d.rename(root/(name+'-failed-'+str(time.time_ns())))
  d.mkdir();src=d/'Challenge.lean'
  text=original.replace('public import Init','public import '+('Bridge' if transitive else 'DosenPetric.Formula'),1)
  source=fixture(src,text)
  if transitive:bridge=fixture(d/'Bridge.lean','module\n\npublic import DosenPetric.Formula\n')
  chain=['Challenge'];cur=src
  while True:
   header=v.lean_header(d,lean_source=cur,lean=bins['lean'],environment=base_env,writable_directories=[],readable_paths=[rc,root,*v.system_readable_paths()],executable_paths=exe,tools=tools)
   assert header.is_module
   imports=list(header.imports);assert len(imports)==1
   nxt=imports[0];chain.append(nxt)
   if nxt.startswith('DosenPetric.'):
    assert (rc/(nxt.replace('.','/')+'.lean')).is_file();break
   assert nxt=='Bridge';cur=d/'Bridge.lean';assert cur.is_file()
  row=dict(name=name,status='rejected_as_required',reason='Challenge source closure contains a forbidden candidate project import',parsed_headers=True,elaboration_attempted=False,dependency_chain=chain,fixture=source)
  if transitive:row['helper_fixture']=bridge
  rows.append(row);save('PACKAGE_CONTROLS_PARTIAL.json',rows)
 save('PACKAGE_CONTROLS.json',dict(status='pass',required_rejections=len(rows),controls=rows,unrelated_parser_or_missing_module_errors_counted=False))
 print(json.dumps(rows,indent=2),flush=True)
