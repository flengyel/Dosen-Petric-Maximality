from pathlib import Path
import subprocess,sys,hashlib,json,datetime,os,time,re
r=Path('/home/flengyel/src/Dosen-Petric-Maximality');w=r/'.codex-work/gentzen-reducibility';w.mkdir(parents=True,exist_ok=True)
base='9075ecc343be5c07d38b7f5ba53676f8f8f32bea'
mode=sys.argv[1]
if mode=='integrate':
 assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=r).decode().strip()==base
 mods=['GentzenAddressTracing','GentzenAddressPaths','GentzenClusterTransport','GentzenEntryFrames']
 initial=Path(Path('/tmp/dp-reducibility-reconciliation-latest.txt').read_text().strip())
 saved=json.loads((initial/'reconciliation.json').read_text())
 hashes={x['path']:x['sha256'] for x in saved['untracked']}
 names=[]
 for mod in mods:
  p=r/'DosenPetric'/(mod+'.lean');assert hashlib.sha256(p.read_bytes()).hexdigest()==hashes[str(p.relative_to(r))],mod
  ns=[]
  for line in p.read_text().splitlines():
   m=re.match(r'namespace (\S+)',line)
   if m:ns.append(m[1]);continue
   if ns and line=='end '+ns[-1]:ns.pop();continue
   m=re.match(r'theorem (\S+)',line)
   if m:names.append('.'.join(ns+[m[1]]))
 root=r/'DosenPetric.lean';axioms=r/'Checks/Axioms.lean'
 assert root.read_bytes()==subprocess.check_output(['git','show',base+':DosenPetric.lean'],cwd=r)
 assert axioms.read_bytes()==subprocess.check_output(['git','show',base+':Checks/Axioms.lean'],cwd=r)
 root.write_text(root.read_text()+''.join('public import DosenPetric.'+m+'\n' for m in mods))
 axioms.write_text(axioms.read_text()+''.join('#print axioms '+n+'\n' for n in names))
 (w/'combined-source.json').write_text(json.dumps(dict(base=base,modules=mods,new_selected_axiom_prints=names,snapshot=str(initial),action='Appended root imports/axiom prints; original transport sources retained byte-for-byte'),indent=2)+'\n')
 print(json.dumps(dict(modules=mods,theorems=len(names)),indent=2));sys.exit(0)
cmds={
 'baseline':[('strict',['bash','scripts/verify.sh'],r)],
 'final':[('strict',['bash','scripts/verify.sh'],r),('audit-boundaries',['python3','scripts/check-audit-boundaries.py'],r),('presentation-boundaries',['python3','scripts/check-presentation-boundaries.py'],r),('manuscript',['sha256sum','-c','SHA256SUMS'],r/'manuscript'),('diff-check',['git','diff','--check'],r),('cached-diff-check',['git','diff','--cached','--check'],r)],
 'types':[('types',['lake','env','lean','-DwarningAsError=true',str(w/'PublicTypes.lean')],r)],
 'reconcile-checks':[('audit-boundaries',['python3','scripts/check-audit-boundaries.py'],r),('presentation-boundaries',['python3','scripts/check-presentation-boundaries.py'],r),('manuscript',['sha256sum','-c','SHA256SUMS'],r/'manuscript'),('diff-check',['git','diff','--check'],r),('cached-diff-check',['git','diff','--cached','--check'],r)]}
if mode=='build':
 m=sys.argv[2];mode='build-'+m.rsplit('.',1)[-1];cmds[mode]=[(mode,['lake','build',m],r)]
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%f');rows=[]
for name,cmd,cwd in cmds[mode]:
 run=cmd if name in ['strict','manuscript','diff-check','cached-diff-check'] else ['flock','-n',str(r/'.codex-work/build.lock'),*cmd]
 log=w/(name+'-'+stamp+'.log');start=time.monotonic();code=None
 try:
  with log.open('w') as out:q=subprocess.run(run,cwd=cwd,env=dict(os.environ,LEAN_NUM_THREADS='1'),stdout=out,stderr=subprocess.STDOUT)
  code=q.returncode
 except KeyboardInterrupt:code=130
 row=dict(name=name,command=cmd,actual_command=run,cwd=str(cwd),exit_status=code,seconds=round(time.monotonic()-start,3),log=str(log.relative_to(r)),log_sha256=hashlib.sha256(log.read_bytes()).hexdigest());rows.append(row)
 (w/(mode+'-'+stamp+'.json')).write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),checks=rows),indent=2)+'\n')
 print(json.dumps(row),flush=True)
 if code:
  print(log.read_text()[-14000:]);sys.exit(code)
