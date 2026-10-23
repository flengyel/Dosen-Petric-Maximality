from pathlib import Path
import datetime, hashlib, json, os, shutil, subprocess, sys, time
r=Path('/home/flengyel/src/Dosen-Petric-Maximality')
w=r/'.codex-work/gentzen-w1-contraction';w.mkdir(parents=True,exist_ok=True)
mode=sys.argv[1]
commands={
 'explore':[('explore',['lake','build','DosenPetric.GentzenContractionCommutationExamples'],r)],
 'baseline':[('environment',['uname','-a'],r),('memory',['free','-h'],r),('baseline',['bash','scripts/verify.sh'],r)],
 'verify':[('strict',['bash','scripts/verify.sh'],r),('audit-boundaries',['python3','scripts/check-audit-boundaries.py'],r),
           ('presentation-boundaries',['python3','scripts/check-presentation-boundaries.py'],r),
           ('manuscript',['sha256sum','-c','SHA256SUMS'],r/'manuscript'),('diff-check',['git','diff','--check'],r)]}
rows=[]
for name,cmd,cwd in commands[mode]:
    start=time.monotonic();log=w/(name+'.log')
    if log.exists():
        stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S');old=w/(name+'-'+stamp+'.log');shutil.copy2(log,old)
        if (w/(mode+'.json')).exists():shutil.copy2(w/(mode+'.json'),w/(mode+'-'+stamp+'.json'))
    with log.open('w') as f:q=subprocess.run(cmd,cwd=cwd,env=dict(os.environ,LEAN_NUM_THREADS='1'),stdout=f,stderr=subprocess.STDOUT)
    rows.append(dict(name=name,command=cmd,cwd=str(cwd),exit_status=q.returncode,seconds=round(time.monotonic()-start,3),log_sha256=hashlib.sha256(log.read_bytes()).hexdigest()))
    (w/(mode+'.json')).write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),checks=rows),indent=2)+'\n')
    print(name,q.returncode,flush=True)
    if q.returncode:raise SystemExit(log.read_text())
if mode=='verify':
    shutil.copytree(r/'.codex-work/contextual-collapse/checks',w/'audit-controls',dirs_exist_ok=True)
    shutil.copytree(r/'.codex-work/presentation-bridge/presentation-controls',w/'presentation-controls',dirs_exist_ok=True)
