exec(Path('/tmp/dp-palomar-common.py').read_text())
import fcntl
j=json.loads((ev/'CANONICAL_CHALLENGE.json').read_text())
for a in j['artifacts']:tools[Path(a['path'])]=a['sha256']
canonical_env=dict(base_env,LEAN_PATH=os.pathsep.join([str(work/'canonical-challenge'),str(prefix/'lib/lean')]))
solution_env=dict(base_env,LEAN_PATH=os.pathsep.join([str(rc/'.lake/build/lib/lean'),str(prefix/'lib/lean')]))
readable=[rc,work,*v.system_readable_paths()]
audit_source=rc/'scripts/PalomarClosureAudit.lean'
old_audit=rc/'scripts/PalomarClosureAudit.lean.txt'
if old_audit.exists():old_audit.unlink()
audit_source.write_bytes(Path('/tmp/PalomarClosureAudit.lean').read_bytes())
with (main/'.codex-work/build.lock').open('a') as build_lock:
 fcntl.flock(build_lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 p=v.sandboxed_run([str(bins['lean']),'--run',str(audit_source),'names',j['module'],str(work/'presentation-names.json')],cwd=rc,environment=canonical_env,writable_directories=[work],readable_paths=readable,executable_paths=exe,tools=tools)
 proc_record('DECLARATION_ENUMERATION',p)
 names=json.loads((work/'presentation-names.json').read_text())
 (ev/'PRESENTATION_DECLARATIONS.json').write_bytes((work/'presentation-names.json').read_bytes())
 config=json.loads((rc/'comparator.json').read_text());targets=v.comparator_export_targets(config,primitives)
 targets=list(dict.fromkeys([*targets,*[x[0] for x in names]]))
 save('EXPORT_TARGETS.json',targets)
 for module,env,name in [(j['module'],canonical_env,'Challenge'),('Solution',solution_env,'Solution')]:
  print('Exporting',name,'and its full declaration closure',flush=True)
  output=work/(name+'.export')
  old_hash=ev/(name.upper()+'_EXPORT_HASH.json')
  if old_hash.is_file() and output.exists():
   row=json.loads(old_hash.read_text());assert row['path']==str(output) and row['sha256']==sha(output.read_bytes())
   tools[output]=row['sha256'];v.verify_export(output)
  else:
   p=v.export_module(module,targets,output=output,leanexport=bins['leanexport'],cwd=rc,environment=env,readable_paths=readable,executable_paths=exe,tools=tools,timeout=v.EXECUTION_BUDGET_SECONDS)
   proc_record(name.upper()+'_EXPORT',p)
   if p.returncode:raise v.export_failure(p,module=module,palomar_owned=name=='Challenge',configured_targets=set(targets))
   v.verify_export(output);tools[output]=sha(output.read_bytes())
   save(name.upper()+'_EXPORT_HASH.json',dict(path=str(output),sha256=tools[output],bytes=output.stat().st_size))
 print('Comparing all concrete presentation declarations, selected types, universes, constructors and values',flush=True)
 p=v.sandboxed_run([str(bins['lean']),'--load-dynlib='+str(prefix/'lib/lean/libLake_shared.so'),'--run',str(audit_source),'compare',str(work/'Challenge.export'),str(work/'Solution.export'),str(work/'presentation-names.json'),str(work/'definition-audit.json')],cwd=rc,environment=canonical_env,writable_directories=[work],readable_paths=readable,executable_paths=exe,tools=tools,timeout=v.EXECUTION_BUDGET_SECONDS)
 proc_record('DEFINITION_AUDIT',p)
 (ev/'DEFINITION_AUDIT_RESULT.json').write_bytes((work/'definition-audit.json').read_bytes())
 print('Running protected release Comparator with mandatory Lean and NanoDa',flush=True)
 p=v.judge_exports(lake=bins['lake'],config=work/'protected-comparator.json',challenge_export=work/'Challenge.export',solution_export=work/'Solution.export',scratch=work/'judge-actual',bwrap=bwrap,lean_prefix=prefix,environment=base_env,tools=tools,timeout=v.EXECUTION_BUDGET_SECONDS)
 proc_record('COMPARATOR_ACTUAL',p)
 verdict=v.comparator_verdict(p.returncode,p.stdout+'\n'+p.stderr)
 if verdict is not None:raise verdict
 assert p.returncode==0 and 'Your solution is okay!' in p.stdout+p.stderr
 save('MANDATORY_REPLAY.json',dict(status='pass',Lean='accepted',NanoDa='accepted',official_full_preflight=False))
 print('Replaying the protected export with authenticated con-ron',flush=True)
 replay=v.replay_con_ron(binary=bins['con-ron'],solution_export=work/'Solution.export',scratch=work/'con-ron-actual',lean_prefix=prefix,environment=base_env,tools=tools,timeout=v.CON_RON_REPLAY_SECONDS)
 save('CON_RON_REPLAY.json',replay)
 assert replay['status'] in ['accepted','declined'], replay
 print(json.dumps(replay),flush=True)
