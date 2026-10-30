exec(Path('/tmp/dp-palomar-common.py').read_text())
import fcntl
for n in ['CHALLENGE','SOLUTION']:
 row=json.loads((ev/(n+'_EXPORT_HASH.json')).read_text());p=Path(row['path']);assert sha(p.read_bytes())==row['sha256'];tools[p]=row['sha256']
with (main/'.codex-work/build.lock').open('a') as build_lock:
 fcntl.flock(build_lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
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
