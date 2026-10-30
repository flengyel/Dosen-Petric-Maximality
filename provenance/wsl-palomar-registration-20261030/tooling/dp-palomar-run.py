from pathlib import Path
import subprocess,os,json,hashlib,datetime,time,sys
main=Path('/home/flengyel/src/Dosen-Petric-Maximality')
stage=main/'.codex-work/palomar-registration-20261030'
rc=stage/'candidate'
logs=stage/'logs';logs.mkdir(parents=True,exist_ok=True)
ev=rc/'provenance/wsl-palomar-registration-20261030'
site=stage/'tooling/python/lib/python3.13/site-packages'
if site.is_dir():sys.path.insert(0,str(site))
action=sys.argv[1]
def sha(b):return hashlib.sha256(b).hexdigest()
def command(cmd,name='command',cwd=rc,lock=True,extra_env=None):
 stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%f')
 path=logs/(name+'-'+stamp+'.log');env=dict(os.environ,LEAN_NUM_THREADS='1');env.update(extra_env or {})
 actual=['flock','-n',str(main/'.codex-work/build.lock'),*map(str,cmd)] if lock else list(map(str,cmd))
 start=time.monotonic()
 with path.open('w') as f:p=subprocess.run(actual,cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT)
 row=dict(command=list(map(str,cmd)),actual_command=actual,cwd=str(cwd),exit_status=p.returncode,seconds=round(time.monotonic()-start,3),log=str(path.relative_to(main)),sha256=sha(path.read_bytes()))
 path.with_suffix('.json').write_text(json.dumps(row,indent=2)+'\n');print(json.dumps(row),flush=True)
 if p.returncode:
  print(path.read_text()[-18000:],flush=True);raise SystemExit(p.returncode)
 return row
if action=='fetch':command(['bash','scripts/fetch-palomar.sh'],'fetch-palomar',cwd=main,lock=False)
elif action=='build':command(['lake','build',*sys.argv[2:]],'build-'+('-'.join(sys.argv[2:]) or 'baseline'))
elif action=='lean':command(['lake','env','lean','-DwarningAsError=true',*sys.argv[2:]],'lean')
elif action=='build-config':exec(Path('/tmp/dp-palomar-build-config.py').read_text())
elif action=='edit':exec(Path('/tmp/dp-palomar-edit.py').read_text())
elif action=='final-checks':exec(Path('/tmp/dp-palomar-final-checks.py').read_text())
elif action=='verify':command(['bash','scripts/verify.sh'],'strict')
elif action=='status':
 ps=subprocess.check_output(['ps','-eo','pid,etime,rss,comm,args'],text=True)
 print('\n'.join(t for t in ps.splitlines() if any((' '+x+' ') in t for x in ['lean','lake','leanexport','leanchecker','nanoda_bin','con-ron'])))
 print(subprocess.check_output(['free','-m'],text=True))
elif action=='python-tooling':exec(Path('/tmp/dp-palomar-python-tooling.py').read_text())
elif action=='tooling':exec(Path('/tmp/dp-palomar-tooling.py').read_text())
elif action=='upstream':exec(Path('/tmp/dp-palomar-upstream.py').read_text())
elif action=='probe':exec(Path('/tmp/dp-palomar-probe.py').read_text())
elif action=='challenge':exec(Path('/tmp/dp-palomar-challenge.py').read_text())
elif action=='selected-replay':exec(Path('/tmp/dp-palomar-selected-replay.py').read_text())
elif action=='replay':exec(Path('/tmp/dp-palomar-replay.py').read_text())
elif action=='compare':exec(Path('/tmp/dp-palomar-compare.py').read_text())
elif action=='auxiliary':exec(Path('/tmp/dp-palomar-auxiliary.py').read_text())
elif action=='controls':exec(Path('/tmp/dp-palomar-controls.py').read_text())
elif action=='final-layout':exec(Path('/tmp/dp-palomar-final-layout.py').read_text())
elif action=='layout':exec(Path('/tmp/dp-palomar-layout.py').read_text())
elif action=='source-audit':exec(Path('/tmp/dp-palomar-source-audit.py').read_text())
elif action=='audit':exec(Path('/tmp/dp-palomar-audit.py').read_text())
elif action=='metadata-validate':exec(Path('/tmp/dp-palomar-metadata-validate.py').read_text())
elif action=='metadata':exec(Path('/tmp/dp-palomar-metadata.py').read_text())
elif action=='reviews':exec(Path('/tmp/dp-palomar-reviews.py').read_text())
elif action=='reports':exec(Path('/tmp/dp-palomar-reports.py').read_text())
elif action=='documents':exec(Path('/tmp/dp-palomar-documents.py').read_text())
elif action=='records':exec(Path('/tmp/dp-palomar-records.py').read_text())
elif action=='polish':exec(Path('/tmp/dp-palomar-polish.py').read_text())
elif action=='precommit':exec(Path('/tmp/dp-palomar-precommit.py').read_text())
elif action=='commit-source':exec(Path('/tmp/dp-palomar-commit-source.py').read_text())
elif action=='deliver':exec(Path('/tmp/dp-palomar-deliver.py').read_text())
else:raise SystemExit('Unknown action '+action)
