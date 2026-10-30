exec(Path('/tmp/dp-palomar-common.py').read_text())
import fcntl
archive=ev/'attempts/expanded-export-kernel';archive.mkdir(parents=True,exist_ok=True)
for name in ['COMPARATOR_ACTUAL.json']:
 p=ev/name
 if p.exists() and not (archive/name).exists():(archive/name).write_bytes(p.read_bytes())
(archive/'DIAGNOSTIC.json').write_text(json.dumps(dict(Lean='accepted',NanoDa='parser panic on DefinitionSafety::Partial',extra_unselected_compiler_definitions=['DosenPetric.Formula.Occ._unsafe_rec','DosenPetric.Formula.subst._unsafe_rec','DosenPetric.Presentation.Term.subst._unsafe_rec'],repair='Use the exact comparator_export_targets for the public configuration in kernel replay. Keep the expanded all-declaration exports for the separate definition/value audit.',proof_or_statement_changed=False),indent=2)+'\n')
final=json.loads((ev/'CANONICAL_CHALLENGE.json').read_text())
for a in final['artifacts']:tools[Path(a['path'])]=a['sha256']
targets=v.comparator_export_targets(v.load_comparator_config(rc/'comparator.json'),primitives)
save('SELECTED_EXPORT_TARGETS.json',targets)
with (main/'.codex-work/build.lock').open('a') as build_lock:
 fcntl.flock(build_lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 for module,name,paths in [(final['module'],'Challenge',[work/'canonical-challenge',prefix/'lib/lean']),('Solution','Solution',[rc/'.lake/build/lib/lean',prefix/'lib/lean'])]:
  env=dict(base_env,LEAN_PATH=os.pathsep.join(map(str,paths)))
  output=work/(name+'-selected.export')
  p=v.export_module(module,targets,output=output,leanexport=bins['leanexport'],cwd=rc,environment=env,readable_paths=[rc,work,*v.system_readable_paths()],executable_paths=exe,tools=tools,timeout=v.EXECUTION_BUDGET_SECONDS)
  proc_record(name.upper()+'_SELECTED_EXPORT',p)
  assert p.returncode==0,p.stderr
  tools[output]=sha(output.read_bytes());v.verify_export(output)
  save(name.upper()+'_SELECTED_EXPORT_HASH.json',dict(path=str(output),sha256=tools[output],bytes=output.stat().st_size))
 print('Judging exact public-configuration export closure with Lean and NanoDa',flush=True)
 p=v.judge_exports(lake=bins['lake'],config=work/'protected-comparator.json',challenge_export=work/'Challenge-selected.export',solution_export=work/'Solution-selected.export',scratch=work/'judge-exact-selected',bwrap=bwrap,lean_prefix=prefix,environment=base_env,tools=tools,timeout=v.EXECUTION_BUDGET_SECONDS)
 proc_record('COMPARATOR_SELECTED',p)
 verdict=v.comparator_verdict(p.returncode,p.stdout+'\n'+p.stderr)
 if verdict is not None:raise verdict
 assert p.returncode==0 and 'Your solution is okay!' in p.stdout+p.stderr
 save('MANDATORY_REPLAY.json',dict(status='pass',Lean='accepted',NanoDa='accepted',official_full_preflight=False,export_scope='exact public configuration and its complete proof dependency closure'))
 print('Mandatory kernels accepted; attempting authenticated con-ron replay',flush=True)
 replay=v.replay_con_ron(binary=bins['con-ron'],solution_export=work/'Solution-selected.export',scratch=work/'con-ron-exact-selected',lean_prefix=prefix,environment=base_env,tools=tools,timeout=v.CON_RON_REPLAY_SECONDS)
 save('CON_RON_REPLAY.json',replay)
 assert replay['status'] in ['accepted','declined'], replay
 print(json.dumps(replay),flush=True)
