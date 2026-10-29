s=Path('/tmp/dp-blocked-controls.py').read_text()
exec(s[:s.index('rows=[]')])
controls.update({
 'missing-terminal-input-contraction': '''example (k : G Empty [.top,.top] [.bot]) (l : G Empty [.top,.top] [.bot]) :
    G Empty [.top,.disj .top .top] [.bot,.bot] := BlockedSource.disjLLast k l\n''',
 'missing-terminal-output-contraction': '''example (k : G Empty [.top] [.bot,.top]) (l : G Empty [.top] [.bot,.top]) :
    G Empty [.disj .top .top] [.bot,.top,.top] := BlockedSource.disjLLast k l\n''',
 'terminal-equal-label-principal-tag': '''example :
    (Route.toTail [.top] (.top : NormalForm Empty)).get (.here .top [.top]) =
      .here .top [.top] := by rfl\n'''
})
rows=[]
for name,body in controls.items():
 path=local/(name+'.lean');path.write_text('module\nimport DosenPetric\nopen DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen\n'+body)
 log=local/(name+'.log');cmd=['lake','env','lean','-DwarningAsError=true',str(path)]
 with log.open('w') as f:
  p=subprocess.run(['flock','-n',str(root/'.codex-work/build.lock'),*cmd],cwd=root,env=dict(os.environ,LEAN_NUM_THREADS='1'),stdout=f,stderr=subprocess.STDOUT)
 content=log.read_text();expected='type mismatch' if name.startswith('missing-') else 'Tactic `rfl` failed'
 assert p.returncode!=0 and expected in (content.lower() if name.startswith('missing-') else content),content
 row=dict(name=name,command=cmd,exit_status=p.returncode,expected_rejection=True,passed=True,source=str(path.relative_to(root)),source_sha256=sha(path.read_bytes()),log=str(log.relative_to(root)),log_sha256=sha(log.read_bytes()))
 rows.append(row);print(json.dumps(row))
(local/'FOCUSED_CONTROLS.json').write_text(json.dumps(rows,indent=2)+'\n')
