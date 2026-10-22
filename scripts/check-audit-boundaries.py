from pathlib import Path
import datetime,hashlib,json,os,re,subprocess
root=Path(__file__).resolve().parent.parent
out=root/'.codex-work/contextual-collapse/checks'
out.mkdir(parents=True,exist_ok=True)
env=dict(os.environ,LEAN_NUM_THREADS='1')
audit=(root/'Checks/Axioms.lean').read_text()
controls={
'direct-axiom': ('public axiom DosenPetric.AuditNegative.direct : False\n', 'DosenPetric.AuditNegative.direct'),
'private-axiom': ('axiom DosenPetric.AuditNegative.privateInput : False\n', 'DosenPetric.AuditNegative.privateInput'),
'hidden-dependency': ('axiom AuditNegative.external : False\npublic theorem DosenPetric.AuditNegative.hidden : False := AuditNegative.external\n', 'AuditNegative.external'),
}
rows=[]
for name,(declarations,expected) in controls.items():
    path=out/(name+'.lean')
    path.write_text(audit.replace('run_elab do',declarations+'\nrun_elab do',1))
    command=['lake','env','lean','-DwarningAsError=true',str(path)]
    run=subprocess.run(command,cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log=out/(name+'.log');log.write_text(run.stdout)
    passed=run.returncode!=0 and 'Unpermitted axiom' in run.stdout and expected in run.stdout
    rows.append(dict(name=name,command=command,exit_status=run.returncode,expected='nonzero; Unpermitted axiom '+expected,passed=passed,source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),log_sha256=hashlib.sha256(log.read_bytes()).hexdigest()))
    print(name, 'PASS (rejected)' if passed else 'FAIL',run.returncode)
    if not passed: raise SystemExit(run.stdout)
seen=set()
def visit(path):
    if path in seen:return
    seen.add(path)
    for name in re.findall(r'^(?:public )?import (DosenPetric(?:\.[A-Za-z]+)*)$',(root/path).read_text(),re.M):
        visit(Path(name.replace('.','/')+'.lean'))
visit(Path('DosenPetric.lean'))
expected={Path('DosenPetric.lean'),*root.glob('DosenPetric/*.lean')}
expected={p.relative_to(root) if p.is_absolute() else p for p in expected}
if seen!=expected:raise SystemExit(f'Import closure differs: {seen ^ expected}')
rows.append(dict(name='public-import-closure',passed=True,source_files=sorted(map(str,seen)),boundary='local library imports; not a Challenge/Solution comparison'))
report=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),base_commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),checks=rows)
(out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
print('PASS: all production modules reachable from public library; controls rejected')
