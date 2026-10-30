import zipfile,io
workflow=json.loads((stage/'WORKFLOW_RUN.json').read_text());rid=workflow['id']
workflow=api('repos/'+repo+'/actions/runs/'+str(rid),'completed-run');save(stage/'WORKFLOW_RUN.json',workflow)
assert workflow['status']=='completed','Official workflow is still running'
artifacts=api('repos/'+repo+'/actions/runs/'+str(rid)+'/artifacts?per_page=100','mechanical-artifacts')
save(stage/'WORKFLOW_ARTIFACTS.json',artifacts)
items=[a for a in artifacts.get('artifacts',[]) if a['name']=='mechanical-report-preflight001' and not a['expired']]
assert len(items)==1,items
artifact=items[0]
argv=[str(gh),'api','repos/'+repo+'/actions/artifacts/'+str(artifact['id'])+'/zip']
p=subprocess.run(argv,cwd=root,capture_output=True);assert p.returncode==0,p.stderr.decode(errors='replace')
data=p.stdout;digest=sha(data)
expected=artifact.get('digest')
if expected:assert expected=='sha256:'+digest,(expected,digest)
archive=stage/'mechanical-report.zip';archive.write_bytes(data)
with zipfile.ZipFile(io.BytesIO(data)) as z:
 files=[x for x in z.infolist() if not x.is_dir()]
 assert len(files)==1 and Path(files[0].filename).name=='mechanical-report.json',[x.filename for x in files]
 content=z.read(files[0]);report=json.loads(content)
(stage/'mechanical-report.json').write_bytes(content)
assert report['source']['commit']==source,report.get('source')
assert report['source']['repository'].lower()==repo.lower()
assert report['execution_profile']=='palomar-standard-v1'
assert report.get('workflow_url')==workflow['html_url']
log=report.get('comparator_log_tail','')
accepted=report['status']=='pass'
if accepted:
 assert report['phase']=='verification',report.get('phase')
 assert workflow['conclusion']=='success'
 assert 'Lean default kernel accepts the solution' in log,log
 assert 'nanoda kernel accepts the solution' in log,log
 assert any(x['name']=='nanoda' for x in report.get('kernels',[]))
record=dict(utc=now(),verified_source_commit=source,workflow_run_id=rid,workflow_url=workflow['html_url'],workflow_conclusion=workflow['conclusion'],mechanical_status=report['status'],phase=report['phase'],stage=report['stage'],execution_profile=report['execution_profile'],artifact_id=artifact['id'],artifact_name=artifact['name'],artifact_zip_sha256=digest,github_digest=expected,mechanical_report_sha256=sha(content),mandatory_Lean_and_NanoDa_acceptance_confirmed=accepted,kernels=report.get('kernels',[]),kernel_attempts=report.get('kernel_attempts',[]),errors=report.get('errors',[]),diagnostics=report.get('diagnostics',[]),warnings=report.get('warnings',[]),resource_usage=report.get('resource_usage'),verification_profile=report.get('verification_profile'))
save(stage/'MECHANICAL_RESULT.json',record)
# Workflow logs are public. Retain complete bytes for actionable diagnostics.
for job in json.loads((stage/'WORKFLOW_JOBS.json').read_text()).get('jobs',[]):
 path='repos/'+repo+'/actions/jobs/'+str(job['id'])+'/logs'
 p=subprocess.run([str(gh),'api',path],cwd=root,capture_output=True)
 if p.returncode==0:(stage/('job-'+str(job['id'])+'.log')).write_bytes(p.stdout)
 else:save(stage/('job-'+str(job['id'])+'-log-error.json'),dict(exit_status=p.returncode,stderr=p.stderr.decode(errors='replace')))
print(json.dumps(dict(result=record,report_keys=list(report),toolchain=report.get('toolchain'),source=report['source'],comparator_log_tail=log[-5000:]),indent=2),flush=True)
