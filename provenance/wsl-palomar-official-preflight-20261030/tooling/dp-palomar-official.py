from pathlib import Path
import subprocess,hashlib,json,datetime,time,sys,os
root=Path('/home/flengyel/src/Dosen-Petric-Maximality')
repo='flengyel/Dosen-Petric-Maximality'
source='2e771844077fd8cebfbe365230f13d4dd13a75b1'
pin='14aa8d6b3c2f14a8540605e37144560b9a00e7e7'
stash='dedfd8fc8cd49930e9a162d5be585215b062a43c'
gh=Path('/mnt/c/Program Files/GitHub CLI/gh.exe')
stage=root/'.codex-work/palomar-official-preflight-20261030';stage.mkdir(exist_ok=True)
ev=root/'provenance/wsl-palomar-official-preflight-20261030'
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(data):return hashlib.sha256(data).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=root,text=True).strip()
def save(path,data):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(json.dumps(data,indent=2)+'\n')
def run(argv,label,stdin=None,check=True):
 start=time.monotonic();stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%f')
 p=subprocess.run(list(map(str,argv)),cwd=root,input=stdin,capture_output=True,text=True)
 row=dict(command=list(map(str,argv)),exit_status=p.returncode,seconds=round(time.monotonic()-start,3),stdout=p.stdout,stderr=p.stderr,utc=now())
 save(stage/'logs'/(label+'-'+stamp+'.json'),row)
 if check and p.returncode:print(json.dumps(row,indent=2),flush=True);raise SystemExit(p.returncode)
 return p

def api(path,label='api',method=None,data=None):
 argv=[gh,'api',path]
 if method:argv+=['--method',method]
 if data is not None:argv+=['--input','-']
 p=run(argv,label,stdin=json.dumps(data) if data is not None else None)
 return json.loads(p.stdout) if p.stdout.strip() else None

def check_source():
 manifest=json.loads((root/'provenance/wsl-palomar-registration-20261030/RELEASE_CANDIDATE.json').read_text())
 assert manifest['verified_source_commit']==source
 for row in manifest['critical_files']:assert sha((root/row['path']).read_bytes())==row['sha256'],row['path']
 assert (root/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.35.0'
 assert git('stash','list','--format=%H')==stash
 assert subprocess.run(['git','merge-base','--is-ancestor',source,'HEAD'],cwd=root).returncode==0
 return manifest

action=sys.argv[1]
if action=='publish':
 check_source();assert git('status','--porcelain')==''
 assert git('rev-list','--left-right','--count','main...origin/main')=='0\t0'
 user=api('user','authenticated-user');assert user['login']=='flengyel'
 approval=dict(utc=now(),author_response='Yes.',confirmation='Adopt Apache-2.0 including the original manuscript and retained history; publish flengyel/Dosen-Petric-Maximality for verified source 2e771844077fd8cebfbe365230f13d4dd13a75b1 and run official full preflight.',repository=repo,verified_source_commit=source,comparator_config_path='comparator.json',maintainer='Florian Lengyel',authorization_relationship='I am a responsible author or maintainer',license='Apache-2.0',approval='explicitly approved in conversation',registration_of_unseen_review_authorized=False)
 save(stage/'RELEASE_AUTHORIZATION.json',approval)
 before=api('repos/'+repo,'repository-before')
 assert before['full_name']==repo and before['permissions']['admin']
 if before['private']:
  run([gh,'repo','edit',repo,'--visibility','public','--accept-visibility-change-consequences'],'make-public')
 after=api('repos/'+repo,'repository-after')
 assert after['private'] is False and after['visibility']=='public'
 record=dict(utc=now(),repository=repo,url=after['html_url'],visibility=after['visibility'],was_private=before['private'],verified_source_commit=source,main_head_before_release=git('rev-parse','HEAD'),license='Apache-2.0',github_license=after.get('license'),authenticated_user=dict(login=user['login'],id=user['id']),publication_status='public',root_license_sha256=sha((root/'LICENSE').read_bytes()))
 save(stage/'PUBLIC_RELEASE.json',record)
 print(json.dumps(record,indent=2),flush=True)
elif action=='dispatch':
 assert not (stage/'DISPATCH_ACCEPTED.json').exists(), 'Dispatch already recorded; inspect the existing run instead of duplicating it'
 check_source()
 approval=json.loads((stage/'RELEASE_AUTHORIZATION.json').read_text());assert approval['verified_source_commit']==source
 current=api('repos/'+repo,'repository-before-dispatch');assert current['visibility']=='public' and not current['private']
 workflow=api('repos/'+repo+'/actions/workflows/palomar-preflight.yml','prepared-workflow');assert workflow['state']=='active'
 previous=api('repos/'+repo+'/actions/workflows/palomar-preflight.yml/runs?event=workflow_dispatch&per_page=10','runs-before-dispatch')
 ids={r['id'] for r in previous.get('workflow_runs',[])}
 save(stage/'DISPATCH_REQUEST.json',dict(utc=now(),repository=repo,workflow='palomar-preflight.yml',workflow_id=workflow['id'],ref='main',inputs=dict(commit=source),pipeline_commit=pin,mode='full',execution_profile='palomar-standard-v1',request_id='preflight001',comparator_config_path='comparator.json',authorization_relationship='I am a responsible author or maintainer',previous_run_ids=sorted(ids)))
 api('repos/'+repo+'/actions/workflows/palomar-preflight.yml/dispatches','dispatch-full-preflight',method='POST',data=dict(ref='main',inputs=dict(commit=source)))
 save(stage/'DISPATCH_ACCEPTED.json',dict(utc=now(),status='GitHub dispatch accepted',verified_source_commit=source))
 runs=api('repos/'+repo+'/actions/workflows/palomar-preflight.yml/runs?event=workflow_dispatch&per_page=10','runs-after-dispatch')
 new=[r for r in runs.get('workflow_runs',[]) if r['id'] not in ids]
 if new:
  record=new[0];save(stage/'WORKFLOW_RUN.json',record);print(json.dumps({k:record.get(k) for k in ['id','html_url','status','conclusion','head_sha','created_at']},indent=2),flush=True)
 else:print('Dispatch accepted; workflow run has not appeared in the listing yet',flush=True)
elif action=='status':
 p=stage/'WORKFLOW_RUN.json'
 if p.exists():run_id=json.loads(p.read_text())['id']
 else:
  old=set(json.loads((stage/'DISPATCH_REQUEST.json').read_text())['previous_run_ids'])
  runs=api('repos/'+repo+'/actions/workflows/palomar-preflight.yml/runs?event=workflow_dispatch&per_page=10','discover-run')
  new=[r for r in runs.get('workflow_runs',[]) if r['id'] not in old];assert new,'Run not listed yet'
  run_id=new[0]['id']
 record=api('repos/'+repo+'/actions/runs/'+str(run_id),'workflow-status');save(p,record)
 jobs=api('repos/'+repo+'/actions/runs/'+str(run_id)+'/jobs?per_page=100','workflow-jobs');save(stage/'WORKFLOW_JOBS.json',jobs)
 print(json.dumps(dict(run={k:record.get(k) for k in ['id','html_url','status','conclusion','head_sha','created_at','updated_at']},jobs=[dict(id=j['id'],name=j['name'],status=j['status'],conclusion=j['conclusion'],active_steps=[s['name'] for s in j.get('steps',[]) if s['status']=='in_progress'],failed_steps=[s['name'] for s in j.get('steps',[]) if s.get('conclusion')=='failure'],completed_steps=sum(s['status']=='completed' for s in j.get('steps',[]))) for j in jobs.get('jobs',[])]),indent=2),flush=True)
else:
 exec(Path('/tmp/dp-palomar-official-'+action+'.py').read_text())
