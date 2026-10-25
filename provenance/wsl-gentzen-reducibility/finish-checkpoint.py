from pathlib import Path
import datetime,hashlib,json,os,subprocess,sys,time
r=Path('/home/flengyel/src/Dosen-Petric-Maximality');w=r/'.codex-work/gentzen-reducibility';p=r/'provenance/wsl-gentzen-reducibility'
base='9075ecc343be5c07d38b7f5ba53676f8f8f32bea'
stash='dedfd8fc8cd49930e9a162d5be585215b062a43c'
def sha(b):return hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=r)
def inventory(path,root):
 rows=[]
 for line in path.read_text().splitlines():
  h,n=line.split('  ',1);assert sha((root/n).read_bytes())==h,n;rows.append(n)
 return rows
def run(name,cmd,cwd=r):
 start=time.monotonic();q=subprocess.run(cmd,cwd=cwd,capture_output=True,text=True)
 log=w/(name+'.log');log.write_text(q.stdout+q.stderr)
 row=dict(name=name,command=cmd,cwd=str(cwd),exit_status=q.returncode,seconds=round(time.monotonic()-start,3),log=str(log.relative_to(r)),log_sha256=sha(log.read_bytes()))
 assert q.returncode==0,(row,q.stdout,q.stderr)
 return row
mode=sys.argv[1]
if mode=='prepare':
 assert git('rev-parse','HEAD').decode().strip()==base
 assert git('rev-parse','origin/main').decode().strip()==base
 assert stash in git('stash','list','--format=%H').decode().splitlines()
 inventory(p/'CHECKED_SOURCES.sha256',r)
 records=inventory(p/'RECORD_SHA256SUMS',r)
 inventory(p/'EVIDENCE_SHA256SUMS',p)
 rows=[run('post-record-diff',['git','diff','--check']),run('post-record-cached-diff',['git','diff','--cached','--check'])]
 (p/'POST_RECORD_CHECKS.json').write_text(json.dumps(rows,indent=2)+'\n')
 shutil_source=Path('/tmp/dp-reducibility-finish.py').read_bytes();(p/'finish-checkpoint.py').write_bytes(shutil_source)
 source_mods=json.loads((p/'integrated-api.json').read_text())['modules']
 scope=['DosenPetric.lean','Checks/Axioms.lean',*['DosenPetric/'+m+'.lean' for m in source_mods],*records,'provenance/wsl-gentzen-reducibility']
 scope=list(dict.fromkeys(scope))
 (p/'SCOPED_PATHS.json').write_text(json.dumps(scope,indent=2)+'\n')
 (p/'EVIDENCE_SHA256SUMS').write_text(''.join(sha(q.read_bytes())+'  '+str(q.relative_to(p))+'\n' for q in sorted(p.rglob('*')) if q.is_file() and q.name!='EVIDENCE_SHA256SUMS' and q.suffix!='.log'))
 q=subprocess.run(['git','add','--',*scope],cwd=r);assert q.returncode==0
 rows.append(run('staged-diff-check',['git','diff','--cached','--check']))
 staged=git('diff','--cached','--name-only','-z').decode().split('\0')
 staged=[x for x in staged if x]
 assert all(x in scope or x.startswith('provenance/wsl-gentzen-reducibility/') for x in staged)
 assert not git('diff','--name-only').strip(),'Unstaged changes remain; inspect before committing'
 (w/'STAGED_INVENTORY.json').write_text(json.dumps([dict(path=n,sha256=sha((r/n).read_bytes())) for n in staged],indent=2)+'\n')
 print(json.dumps(dict(staged_files=len(staged),source_inventory_matches=True,record_inventory_matches=True,stash_preserved=True,checks=rows),indent=2))
elif mode=='commit':
 assert git('rev-parse','HEAD').decode().strip()==base
 rows=json.loads((w/'STAGED_INVENTORY.json').read_text())
 for row in rows:
  assert sha((r/row['path']).read_bytes())==row['sha256'],row['path']
  assert sha(git('show',':'+row['path']))==row['sha256'],row['path']
 check=run('commit',['git','commit','-m','Reconcile Gentzen tracing and prove scoped reducibility bounds'])
 head=git('rev-parse','HEAD').decode().strip()
 assert git('branch','--show-current').decode().strip()=='main'
 for row in rows:assert sha(git('show',head+':'+row['path']))==row['sha256'],row['path']
 for line in (p/'CHECKED_SOURCES.sha256').read_text().splitlines():
  h,n=line.split('  ',1);assert sha(git('show',head+':'+n))==h,n
 assert stash in git('stash','list','--format=%H').decode().splitlines()
 (w/('COMMITTED_'+head[:12]+'.json')).write_text(json.dumps(dict(commit=head,verified_scoped_files=len(rows),checked_source_inventory_matches=True,stash_preserved=True,command=check),indent=2)+'\n')
 print(json.dumps(dict(commit=head,scoped_files=len(rows),committed_bytes_match=True),indent=2))
elif mode=='push':
 assert git('remote','get-url','origin').decode().strip()=='git@github.com:flengyel/Dosen-Petric-Maximality.git'
 assert not git('status','--porcelain=v1').strip()
 head=git('rev-parse','main').decode().strip()
 assert (w/('COMMITTED_'+head[:12]+'.json')).exists()
 result=run('push',['git','push','origin','main'])
 local=git('rev-parse','main').decode().strip();origin=git('rev-parse','origin/main').decode().strip()
 live=git('ls-remote','git@github.com:flengyel/Dosen-Petric-Maximality.git','refs/heads/main').decode().split()[0]
 assert local==origin==live==head
 receipt=dict(commit=head,local_main=local,origin_main=origin,live_ssh_main=live,visibility_action='none',push=result,working_tree=git('status','--porcelain=v1').decode(),stash=git('stash','list','--format=%H %s').decode())
 (w/('REFS_'+head[:12]+'.json')).write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt,indent=2))
elif mode=='deliver':
 head=git('rev-parse','main').decode().strip();assert (w/('REFS_'+head[:12]+'.json')).exists()
 files=['docs/GENTZEN_REDUCIBILITY_REPORT.md','docs/reviews/GENTZEN_REDUCIBILITY_HOSTILE.md','docs/reviews/GENTZEN_REDUCIBILITY_WRITING.md','docs/CODEX_NEXT_SESSION.txt']
 dest=Path('/mnt/c/Users/fleng/Downloads');assert dest.is_dir()
 rows=[];stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
 for n in files:
  b=git('show',head+':'+n);assert b==(r/n).read_bytes()
  out=dest/Path(n).name
  if out.exists() and out.read_bytes()!=b:out=dest/(out.stem+'_'+stamp+'_'+head[:12]+out.suffix)
  if out.exists():assert out.read_bytes()==b
  else:
   with out.open('xb') as f:f.write(b)
  assert out.read_bytes()==b
  rows.append(dict(repository=str(r/n),downloads=str(out),sha256=sha(b),matches_committed_bytes=True))
 assert not git('status','--porcelain=v1').strip()
 receipt=dict(commit=head,reports_and_continuation=rows,working_tree='clean')
 (w/('DELIVERY_'+head[:12]+'.json')).write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt,indent=2))
else:raise SystemExit(mode)
