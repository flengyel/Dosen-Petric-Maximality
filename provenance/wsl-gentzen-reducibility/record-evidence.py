from pathlib import Path
import datetime,hashlib,json,os,re,shutil,subprocess,tarfile,time
r=Path('/home/flengyel/src/Dosen-Petric-Maximality');w=r/'.codex-work/gentzen-reducibility'
p=r/'provenance/wsl-gentzen-reducibility';p.mkdir(parents=True,exist_ok=True)
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def verify_inventory(path):
 for line in path.read_text().splitlines():
  h,n=line.split('  ',1);assert sha(r/n)==h,n
verify_inventory(w/'CHECKED_SOURCES.sha256')
for f in w.iterdir():
 if f.is_file():shutil.copy2(f,p/f.name)
for source,target in [('contextual-collapse/checks','audit-controls'),('presentation-bridge/checks','presentation-controls')]:
 src=r/'.codex-work'/source
 if src.exists():shutil.copytree(src,p/target,dirs_exist_ok=True)
snap=r/'.codex-work/reducibility-reconciliation/20261025T013921Z'
archive=p/'PRESERVED_RECONCILIATION.tar.gz'
assert not archive.exists()
with tarfile.open(archive,'w:gz') as tar:
 tar.add(snap,arcname='20261025T013921Z')
 for q in [Path('/tmp/dp-reducibility-candidate-comparison.json'),Path('/tmp/dp-reducibility-writer-observation.json')]:
  tar.add(q,arcname=q.name)
for n in ['candidate-comparison','writer-observation']:
 shutil.copy2(Path('/tmp/dp-reducibility-'+n+'.json'),p/(n+'.json'))
rows=[]
for name,cmd in [('lean-version',['lean','--version']),('lake-version',['lake','--version']),('git-version',['git','--version']),('python-version',['python3','--version']),('memory',['free','-h']),('status',['git','status','--porcelain=v1']),('stashes',['git','stash','list','--format=%H %s']),('worktrees',['git','worktree','list','--porcelain'])]:
 start=time.monotonic();q=subprocess.run(cmd,cwd=r,capture_output=True,text=True)
 (p/(name+'.txt')).write_text(q.stdout+q.stderr)
 rows.append(dict(name=name,command=cmd,exit_status=q.returncode,seconds=round(time.monotonic()-start,3)))
 assert q.returncode==0,name
presence={}
for pid in [700028,3970616]:
 try:os.kill(pid,0);presence[str(pid)]='present'
 except ProcessLookupError:presence[str(pid)]='absent'
(p/'WRITER_PROCESSES.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),observed_pid_presence=presence,qualification='The identified WSL2 writer PID is absent. Stability observations are separate evidence; neither proves absence of every possible future writer.'),indent=2)+'\n')
assert presence['700028']=='absent'
cache=r/'.codex-work/references'
sources={'book':('dosen-petric-coh-september-2007-e285235f.pdf','e285235f956214b115c4bea5e8b4a33546ea0ddad2507a0ed76fe333ed3ac16e'),
 'writing':('knuth-mathematical-writing-mit-9bf404c2.pdf','9bf404c2c75633a1f39aae97af0b2e9335ce6d83cf386c84906654589b4e82e6')}
for n,(f,h) in sources.items():assert sha(cache/f)==h
(p/'SOURCE_CONSULTATION.json').write_text(json.dumps(dict(sources=sources,book_printed_pages='248-253',book_pdf_pages_one_based='260-265',rendered='Existing source-p250.png inspected; historical access records preserved',writing='MIT-hosted typeset course report, Section 1 printed pp.1-6 (PDF pp.3-8) and Section 4; no edition byte identity claimed',book_url='https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf',writing_url='https://jmlr.csail.mit.edu/reviewing-papers/knuth_mathematical_writing.pdf'),indent=2)+'\n')
strict=(p/'strict-20261025T015738139434.log').read_text()
assert '224 source files' in strict and '8602 project declarations' in strict
final=json.loads((p/'final-20261025T015738139434.json').read_text())
assert all(x['exit_status']==0 for x in final['checks'])
types=json.loads((p/'types-20261025T015843537976.json').read_text());assert types['checks'][0]['exit_status']==0
api=json.loads((p/'integrated-api.json').read_text())
failed=[dict(file=q.name,checks=json.loads(q.read_text())['checks']) for q in p.glob('build-*.json') if any(x['exit_status'] for x in json.loads(q.read_text())['checks'])]
summary=dict(base='9075ecc343be5c07d38b7f5ba53676f8f8f32bea',status='Verified partial checkpoint; both full Reducibility Lemmata remain open',baseline_files=220,baseline_declarations=8538,final_files=224,final_declarations=8602,public_type_queries=len(api['public_queries']),selected_axiom_prints=len(api['selected_axiom_prints']),final=final,types=types,failed_attempts=failed,environment_commands=rows,source_inventory_sha256=sha(p/'CHECKED_SOURCES.sha256'),preserved_archive_sha256=sha(archive))
(p/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
shutil.copy2('/tmp/dp-reducibility-run.py',p/'run-verification.py')
shutil.copy2('/tmp/dp-reducibility-integrate.py',p/'register-imports.py')
shutil.copy2('/tmp/dp-reducibility-reconcile.py',p/'preserve-working-state.py')
shutil.copy2('/tmp/dp-reducibility-records.py',p/'record-evidence.py')
print(json.dumps(dict(files=224,declarations=8602,queries=75,selected=59,failed_attempts=len(failed),archive_sha256=sha(archive)),indent=2))
