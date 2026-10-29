from pathlib import Path
import datetime,hashlib,json,os,subprocess,sys,time
root=Path('/home/flengyel/src/Dosen-Petric-Maximality')
local=root/'.codex-work/gentzen-conjr-right-first'
evidence=root/'provenance/wsl-gentzen-conjr-right-first'
action=sys.argv[2]
rb_phase=action.startswith('rb-')
rs_phase=action.startswith('rs-')
rf_phase=action.startswith('rf-')
lb_phase=action.startswith('lb-')
ls_phase=action.startswith('ls-')
lf_phase=action.startswith('lf-')
sd_phase=action.startswith('sd-')
sq_phase=action.startswith('sq-')
rc_phase=action.startswith('rc-')
lg_phase=action.startswith('lg-')
bd_phase=action.startswith('bd-')
blocked_phase=action.startswith('blocked-')
left_phase=action.startswith('left-')
second_phase=action.startswith('second-')
disj_phase=action.startswith('disj-')
if rb_phase:
 local=root/'.codex-work/gentzen-blocked-right-conj-both'
 evidence=root/'provenance/wsl-gentzen-blocked-right-conj-both'
 action=action[3:]
if rs_phase:
 local=root/'.codex-work/gentzen-blocked-right-conj-second'
 evidence=root/'provenance/wsl-gentzen-blocked-right-conj-second'
 action=action[3:]
if rf_phase:
 local=root/'.codex-work/gentzen-blocked-right-conj-first'
 evidence=root/'provenance/wsl-gentzen-blocked-right-conj-first'
 action=action[3:]
if lb_phase:
 local=root/'.codex-work/gentzen-blocked-left-disj-both'
 evidence=root/'provenance/wsl-gentzen-blocked-left-disj-both'
 action=action[3:]
if ls_phase:
 local=root/'.codex-work/gentzen-blocked-left-disj-second'
 evidence=root/'provenance/wsl-gentzen-blocked-left-disj-second'
 action=action[3:]
if lf_phase:
 local=root/'.codex-work/gentzen-blocked-left-disj-first'
 evidence=root/'provenance/wsl-gentzen-blocked-left-disj-first'
 action=action[3:]
if sd_phase:
 local=root/'.codex-work/gentzen-sequential-disjunction'
 evidence=root/'provenance/wsl-gentzen-sequential-disjunction'
 action=action[3:]
if sq_phase:
 local=root/'.codex-work/gentzen-sequential-blocked'
 evidence=root/'provenance/wsl-gentzen-sequential-blocked'
 action=action[3:]
if rc_phase:
 local=root/'.codex-work/gentzen-right-gamma-conj'
 evidence=root/'provenance/wsl-gentzen-right-gamma-conj'
 action=action[3:]
if lg_phase:
 local=root/'.codex-work/gentzen-left-gamma-disj'
 evidence=root/'provenance/wsl-gentzen-left-gamma-disj'
 action=action[3:]
if bd_phase:
 local=root/'.codex-work/gentzen-blocked-disj'
 evidence=root/'provenance/wsl-gentzen-blocked-disj'
 action=action[3:]
if blocked_phase:
 local=root/'.codex-work/gentzen-blocked-cuts'
 evidence=root/'provenance/wsl-gentzen-blocked-cuts'
 action=action[8:]
if disj_phase:
 local=root/'.codex-work/gentzen-disjl-cuts'
 evidence=root/'provenance/wsl-gentzen-disjl-cuts'
 action=action[5:]
if second_phase:
 local=root/'.codex-work/gentzen-conjr-left-second'
 evidence=root/'provenance/wsl-gentzen-conjr-left-second'
 action=action[7:]
if action.startswith('left-'):
 local=root/'.codex-work/gentzen-conjr-left-first'
 evidence=root/'provenance/wsl-gentzen-conjr-left-first'
 action=action[5:]
def sha(b):return hashlib.sha256(b).hexdigest()
def command(cmd,name='check',lock=True):
 local.mkdir(parents=True,exist_ok=True);stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%f')
 actual=['flock','-n',str(root/'.codex-work/build.lock'),*cmd] if lock else cmd
 log=local/(name+'-'+stamp+'.log');start=time.monotonic()
 with log.open('w') as f:p=subprocess.run(actual,cwd=root,env=dict(os.environ,LEAN_NUM_THREADS='1'),stdout=f,stderr=subprocess.STDOUT)
 row=dict(command=cmd,actual_command=actual,cwd=str(root),exit_status=p.returncode,seconds=round(time.monotonic()-start,3),log=str(log.relative_to(root)),sha256=sha(log.read_bytes()))
 log.with_suffix('.json').write_text(json.dumps(row,indent=2)+'\n');print(json.dumps(row),flush=True)
 if p.returncode:print(log.read_text()[-18000:]);raise SystemExit(p.returncode)
 return row
if action=='build':command(['lake','build',*sys.argv[3:]],name='build-'+sys.argv[3].split('.')[-1])
elif action=='lean':command(['lake','env','lean','-DwarningAsError=true',*sys.argv[3:]],name='lean')
elif action=='deliver-successor':
 commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip();rows=[]
 for rel in ['docs/CODEX_AFTER_77199AC_LOGICAL_BINARY_CUTS.txt','docs/reviews/GENTZEN_77199AC_REVIEW.md','docs/reviews/GENTZEN_77199AC_WRITING.md']:
  b=subprocess.check_output(['git','show',commit+':'+rel],cwd=root);assert b==(root/rel).read_bytes();dst=Path('/mnt/c/Users/fleng/Downloads')/Path(rel).name
  if dst.exists() and dst.read_bytes()!=b:dst=dst.with_name(dst.stem+'-'+commit[:12]+dst.suffix)
  assert not dst.exists() or dst.read_bytes()==b;dst.write_bytes(b);assert dst.read_bytes()==b
  rows.append(dict(repository=rel,downloads=str(dst),source_commit=commit,sha256=sha(b),bytes=len(b)))
 evidence.mkdir(exist_ok=True);(evidence/'SUCCESSOR_DELIVERY.json').write_text(json.dumps(dict(deliveries=rows,preserved_stash=subprocess.check_output(['git','stash','list','--format=%H'],cwd=root,text=True).strip()),indent=2)+'\n');print(json.dumps(rows,indent=2))
elif action=='integrate':exec(Path('/tmp/dp-'+('rb' if rb_phase else 'rs' if rs_phase else 'rf' if rf_phase else 'lb' if lb_phase else 'ls' if ls_phase else 'lf' if lf_phase else 'sd' if sd_phase else 'sq' if sq_phase else 'rc' if rc_phase else 'lg' if lg_phase else 'bd' if bd_phase else 'blocked' if blocked_phase else 'disj' if disj_phase else 'second' if second_phase else 'left' if left_phase else 'first')+'-integrate.py').read_text())
elif action=='reports-final':
 for src,dst in [('report','GENTZEN_BLOCKED_GAMMA_REPORT.md'),('hostile','reviews/GENTZEN_BLOCKED_GAMMA_HOSTILE.md'),('writing','reviews/GENTZEN_BLOCKED_GAMMA_WRITING.md')]:
  (root/'docs'/dst).write_bytes(Path('/tmp/dp-blocked-'+src+'.md').read_bytes())
elif action=='diagnostics':
 ps=subprocess.check_output(['ps','-eo','pid,etime,rss,args'],text=True)
 print('\n'.join(t for t in ps.splitlines() if any(x in t for x in ['lean','verify.sh','build.lock']) and 'codex-linux' not in t))
 print(subprocess.check_output(['free','-m'],text=True))
elif action=='verify':command(['bash','scripts/verify.sh'],name='strict',lock=False)
elif action=='checks':
 for p in sorted((root/'Checks').glob('*.lean')):
  if p.stem!='Axioms':command(['lake','env','lean','-DwarningAsError=true',str(p.relative_to(root))],name='signature-'+p.stem)
elif action=='boundaries':
 command(['python3','scripts/check-audit-boundaries.py'],name='audit-boundaries')
 command(['python3','scripts/check-presentation-boundaries.py'],name='presentation-boundaries')
elif action=='left-core':
 local.mkdir(parents=True,exist_ok=True)
 prior=local/'next-conjr-left-first.lean'
 if prior.exists():
  old=prior.read_bytes();(local/('next-conjr-left-first-'+sha(old)[:12]+'.lean')).write_bytes(old)
 prior.write_bytes(Path('/tmp/dp-first-left-core.lean').read_bytes())
 command(['lake','env','lean','-DwarningAsError=true',str(local/'next-conjr-left-first.lean')],name='left-core')
elif action=='focused':exec(Path('/tmp/dp-'+('rb' if rb_phase else 'rs' if rs_phase else 'rf' if rf_phase else 'lb' if lb_phase else 'ls' if ls_phase else 'lf' if lf_phase else 'sd' if sd_phase else 'sq' if sq_phase else 'rc' if rc_phase else 'lg' if lg_phase else 'bd' if bd_phase else 'blocked' if blocked_phase else 'disj' if disj_phase else 'second' if second_phase else 'left' if left_phase else 'first')+'-controls.py').read_text())
elif action=='documents':exec(Path('/tmp/dp-'+('rb' if rb_phase else 'rs' if rs_phase else 'rf' if rf_phase else 'lb' if lb_phase else 'ls' if ls_phase else 'lf' if lf_phase else 'sd' if sd_phase else 'sq' if sq_phase else 'rc' if rc_phase else 'lg' if lg_phase else 'bd' if bd_phase else 'blocked' if blocked_phase else 'disj' if disj_phase else 'second' if second_phase else 'left' if left_phase else 'first')+'-docs.py').read_text())
elif action=='polish':exec(Path('/tmp/dp-'+('rb' if rb_phase else 'rs' if rs_phase else 'rf' if rf_phase else 'lb' if lb_phase else 'ls' if ls_phase else 'lf' if lf_phase else 'sd' if sd_phase else 'sq' if sq_phase else 'rc' if rc_phase else 'lg' if lg_phase else 'first')+'-polish.py').read_text())
elif action=='records':exec(Path('/tmp/dp-'+('rb' if rb_phase else 'rs' if rs_phase else 'rf' if rf_phase else 'lb' if lb_phase else 'ls' if ls_phase else 'lf' if lf_phase else 'sd' if sd_phase else 'sq' if sq_phase else 'rc' if rc_phase else 'lg' if lg_phase else 'bd' if bd_phase else 'blocked' if blocked_phase else 'disj' if disj_phase else 'second' if second_phase else 'left' if left_phase else 'first')+'-records.py').read_text())
elif action=='review-polish':
 (root/'docs/reviews/GENTZEN_CONJR_RIGHT_FIRST_HOSTILE.md').write_bytes(Path('/tmp/dp-first-hostile.md').read_bytes())
elif action=='deliver':exec(Path('/tmp/dp-'+('rb' if rb_phase else 'rs' if rs_phase else 'rf' if rf_phase else 'lb' if lb_phase else 'ls' if ls_phase else 'lf' if lf_phase else 'sd' if sd_phase else 'sq' if sq_phase else 'rc' if rc_phase else 'lg' if lg_phase else 'bd' if bd_phase else 'blocked' if blocked_phase else 'disj' if disj_phase else 'second' if second_phase else 'left' if left_phase else 'first')+'-deliver.py').read_text())
elif action=='next-disjl':
 local.mkdir(parents=True,exist_ok=True)
 (local/'next-disjl-left-second.lean').write_bytes(Path('/tmp/dp-second-next-disjl.lean').read_bytes())
 command(['lake','env','lean','-DwarningAsError=true',str(local/'next-disjl-left-second.lean')],name='next-disjl')
elif action=='next-second':
 local.mkdir(parents=True,exist_ok=True)
 (local/'next-conjr-left-second.lean').write_bytes(Path('/tmp/dp-left-next-second.lean').read_bytes())
 command(['lake','env','lean','-DwarningAsError=true',str(local/'next-conjr-left-second.lean')],name='next-second')
else:raise SystemExit(action)
