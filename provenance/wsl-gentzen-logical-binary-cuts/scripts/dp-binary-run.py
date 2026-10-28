from pathlib import Path
import datetime,hashlib,json,os,subprocess,sys,time
root=Path('/home/flengyel/src/Dosen-Petric-Maximality')
local=root/'.codex-work/gentzen-binary-cuts';evidence=root/'provenance/wsl-gentzen-binary-cuts'
action=sys.argv[2]
logical_phase=action.startswith('logical-')
if action.startswith('logical-'):
 local=root/'.codex-work/gentzen-logical-binary-cuts'
 evidence=root/'provenance/wsl-gentzen-logical-binary-cuts'
 action=action[8:]
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
 for rel in ['docs/CODEX_AFTER_B8FCD28_BINARY_CUTS.txt','docs/reviews/GENTZEN_B8FCD28_REVIEW.md','docs/reviews/GENTZEN_B8FCD28_WRITING.md']:
  b=subprocess.check_output(['git','show',commit+':'+rel],cwd=root);assert b==(root/rel).read_bytes();dst=Path('/mnt/c/Users/fleng/Downloads')/Path(rel).name
  if dst.exists() and dst.read_bytes()!=b:dst=dst.with_name(dst.stem+'-'+commit[:12]+dst.suffix)
  assert not dst.exists() or dst.read_bytes()==b;dst.write_bytes(b);assert dst.read_bytes()==b
  rows.append(dict(repository=rel,downloads=str(dst),source_commit=commit,sha256=sha(b),bytes=len(b)))
 evidence.mkdir(exist_ok=True);(evidence/'SUCCESSOR_DELIVERY.json').write_text(json.dumps(dict(deliveries=rows,preserved_stash=subprocess.check_output(['git','stash','list','--format=%H'],cwd=root,text=True).strip()),indent=2)+'\n');print(json.dumps(rows,indent=2))
elif action=='coverage':
 (root/'docs/GENTZEN_CUT_CONSTRUCTOR_COVERAGE.md').write_bytes(Path('/tmp/dp-binary-coverage.md').read_bytes())
elif action=='integrate':exec(Path('/tmp/dp-'+('logical' if logical_phase else 'binary')+'-integrate.py').read_text())
elif action=='final-local':
 command(['bash','scripts/verify.sh'],name='strict',lock=False)
 for p in sorted((root/'Checks').glob('*.lean')):
  if p.stem!='Axioms':command(['lake','env','lean','-DwarningAsError=true',str(p.relative_to(root))],name='signature-'+p.stem)
 command(['git','diff','--check'],lock=False,name='diff-check')
elif action=='verify':command(['bash','scripts/verify.sh'],name='strict',lock=False)
elif action=='checks':
 for p in sorted((root/'Checks').glob('*.lean')):
  if p.stem!='Axioms':command(['lake','env','lean','-DwarningAsError=true',str(p.relative_to(root))],name='signature-'+p.stem)
elif action=='boundaries':
 command(['python3','scripts/check-audit-boundaries.py'],name='audit-boundaries')
 command(['python3','scripts/check-presentation-boundaries.py'],name='presentation-boundaries')
elif action=='focused':exec(Path('/tmp/dp-'+('logical' if logical_phase else 'binary')+'-controls.py').read_text())
elif action=='documents':exec(Path('/tmp/dp-'+('logical' if logical_phase else 'binary')+'-docs.py').read_text())
elif action=='records':exec(Path('/tmp/dp-'+('logical' if logical_phase else 'binary')+'-records.py').read_text())
elif action=='polish':exec(Path('/tmp/dp-logical-polish.py').read_text())
elif action=='reconcile':exec(Path('/tmp/dp-binary-reconcile.py').read_text())
elif action=='deliver':exec(Path('/tmp/dp-'+('logical' if logical_phase else 'binary')+'-deliver.py').read_text())
elif action=='next-native':
 local.mkdir(parents=True,exist_ok=True)
 prior=local/'next-native-first.lean'
 if prior.exists():
  oldbytes=prior.read_bytes();(local/('next-native-first-'+sha(oldbytes)[:12]+'.lean')).write_bytes(oldbytes)
 prior.write_bytes(Path('/tmp/dp-logical-next-native.lean').read_bytes())
 command(['lake','env','lean','-DwarningAsError=true',str(local/'next-native-first.lean')],name='next-native')
elif action=='open-diagram':
 local.mkdir(parents=True,exist_ok=True)
 (local/'next-distributor-symmetry.lean').write_bytes(Path('/tmp/dp-logical-open-diagram.lean').read_bytes())
 command(['lake','env','lean','-DwarningAsError=true',str(local/'next-distributor-symmetry.lean')],name='open-diagram')
else:raise SystemExit(action)
