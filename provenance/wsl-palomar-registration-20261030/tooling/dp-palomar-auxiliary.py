exec(Path('/tmp/dp-palomar-common.py').read_text())
import fcntl
audit_source=rc/'scripts/PalomarClosureAudit.lean';audit_source.write_bytes(Path('/tmp/PalomarClosureAudit.lean').read_bytes())
for n in ['CHALLENGE','SOLUTION']:
 row=json.loads((ev/(n+'_EXPORT_HASH.json')).read_text());p=Path(row['path']);assert sha(p.read_bytes())==row['sha256'];tools[p]=row['sha256']
shared=prefix/'lib/lean/libLake_shared.so';tools[shared]=sha(shared.read_bytes())
with (main/'.codex-work/build.lock').open('a') as build_lock:
 fcntl.flock(build_lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 p=v.sandboxed_run([str(bins['lean']),'--load-dynlib='+str(shared),'--run',str(audit_source),'compare',str(work/'Challenge.export'),str(work/'Solution.export'),str(work/'presentation-names.json'),str(work/'definition-audit.json')],cwd=rc,environment=dict(base_env,LEAN_PATH=str(prefix/'lib/lean')),writable_directories=[work],readable_paths=[rc,work,*v.system_readable_paths()],executable_paths=exe,tools=tools,timeout=v.EXECUTION_BUDGET_SECONDS)
 proc_record('DEFINITION_AUDIT_FINAL',p)
 (ev/'DEFINITION_AUDIT_RESULT.json').write_bytes((work/'definition-audit.json').read_bytes())
 save('AUXILIARY_TOOL.json',dict(source=str(audit_source.relative_to(rc)),sha256=sha(audit_source.read_bytes()),native_sdk_library=str(shared),native_library_sha256=tools[shared],main_comparator_unmodified=True,extra_audit_alpha_conversion='bound universe parameter names only; arity, order and every type/value use retained'))
 print(p.stdout,flush=True)
