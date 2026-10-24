from pathlib import Path
import datetime,hashlib,json,os,subprocess,sys,time
r=Path('/home/flengyel/src/Dosen-Petric-Maximality')
w=r/'.codex-work/gentzen-w5-single-premise-mix';w.mkdir(parents=True,exist_ok=True)
mode=sys.argv[1]
commands={
 'types':[('public-types',['lake','env','lean','-DwarningAsError=true',str(w/'PublicTypes.lean')],r)],
 'versions':[('lean-version',['lake','env','lean','--version'],r),('lake-version',['lake','--version'],r),('git-version',['git','--version'],r),('python-version',['python3','--version'],r)],
 'baseline':[('environment',['uname','-a'],r),('memory',['free','-h'],r),('baseline',['bash','scripts/verify.sh'],r)],
 'final':[('strict',['bash','scripts/verify.sh'],r),('audit-boundaries',['python3','scripts/check-audit-boundaries.py'],r),('presentation-boundaries',['python3','scripts/check-presentation-boundaries.py'],r),('manuscript',['sha256sum','-c','SHA256SUMS'],r/'manuscript'),('diff-check',['git','diff','--check'],r),('cached-diff-check',['git','diff','--cached','--check'],r)]}
if mode=='build':
 module=sys.argv[2];mode='build-'+module.rsplit('.',1)[-1]
 commands[mode]=[(mode,['lake','build',module],r)]
rows=[];stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%f')
for name,cmd,cwd in commands[mode]:
 log=w/(name+'-'+stamp+'.log');start=time.monotonic()
 with log.open('w') as f:q=subprocess.run(cmd,cwd=cwd,env=dict(os.environ,LEAN_NUM_THREADS='1'),stdout=f,stderr=subprocess.STDOUT)
 row=dict(name=name,command=cmd,cwd=str(cwd),exit_status=q.returncode,seconds=round(time.monotonic()-start,3),log=str(log.relative_to(r)),log_sha256=hashlib.sha256(log.read_bytes()).hexdigest())
 rows.append(row)
 (w/(mode+'-'+stamp+'.json')).write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),checks=rows),indent=2)+'\n')
 print(json.dumps(row),flush=True)
 if q.returncode:
  print(log.read_text()[-16000:]);raise SystemExit(q.returncode)
