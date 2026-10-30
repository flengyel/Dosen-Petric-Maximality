exec(Path('/tmp/dp-palomar-common.py').read_text())
p=rc/'DosenPetric/PalomarCorrespondence.lean';old=p.read_text();new='\n'.join(s.rstrip() for s in old.splitlines())+'\n';assert old!=new and len(old.splitlines())==len(new.splitlines())
p.write_text(new);Path('/tmp/dp-palomar-correspondence.lean').write_text(new)
save('WHITESPACE_REPAIR.json',dict(path=str(p.relative_to(rc)),before_sha256=sha(old.encode()),after_sha256=sha(new.encode()),change='Remove trailing spaces on two lines only; no token, declaration, type or mathematical proof change.'))
row=command(['bash','scripts/verify.sh'],'strict-final-source')
save('STRICT_VERIFICATION.json',row)
row=command(['lake','build','Solution'],'solution-final-source')
save('SOLUTION_FINAL_BUILD.json',row)
import fcntl
with (main/'.codex-work/build.lock').open('a') as build_lock:
 fcntl.flock(build_lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 old=json.loads((ev/'SOLUTION_SELECTED_EXPORT_HASH.json').read_text())
 output=work/'Solution-final.export'
 targets=json.loads((ev/'SELECTED_EXPORT_TARGETS.json').read_text())
 env=dict(base_env,LEAN_PATH=os.pathsep.join([str(rc/'.lake/build/lib/lean'),str(prefix/'lib/lean')]))
 p=v.export_module('Solution',targets,output=output,leanexport=bins['leanexport'],cwd=rc,environment=env,readable_paths=[rc,work,*v.system_readable_paths()],executable_paths=exe,tools=tools,timeout=v.EXECUTION_BUDGET_SECONDS)
 proc_record('SOLUTION_FINAL_EXPORT',p);assert p.returncode==0,p.stderr
 digest=sha(output.read_bytes())
 save('FINAL_EXPORT_IDENTITY.json',dict(status='pass' if digest==old['sha256'] else 'changed_requires_replay',final_export=str(output),final_sha256=digest,verified_kernel_export=old['path'],verified_sha256=old['sha256'],byte_identical=digest==old['sha256'],reason='Strictly rebuilt final source; unchanged exported proof bytes reuse the already successful three kernel replays.'))
 assert digest==old['sha256'], 'New export changed; replay required'
 print('PASS: rebuilt final source exports byte-for-byte identical verified proof closure',flush=True)
exec(Path('/tmp/dp-palomar-source-audit.py').read_text())
