s=Path('/tmp/dp-rc-controls.py').read_text()
exec(s[:s.index('\nrows=[]')])
controls.update({
 'missing-sequential-second-cut': '''example (f : G Empty [.top,.top,.top] [.top]) : G Empty [.top] [.top] :=
    SequentialRepair.repair f
''',
 'missing-sequential-repair': '''example (f : G Empty [[.top].head! , .top, .top] [.top,.top,.top]) :
    G Empty [.top,.top] [.top,.top] := f
''',
 'sequential-returned-rank': '''example :
    (G.conjL [] [] [.top] .top .top (G.thinL [] [.top] [.top] .top (G.topIdentity (P:=Empty)))).rho
      .left (.here (.conj .top .top) []) =
      (G.thinL [] [.top] [.top] .top (G.topIdentity (P:=Empty))).rho .left (.here .top [.top])+1 := by rfl
''',
 'sequential-distinct-parametric-principal': '''example :
    (At.here (.conj .top .top : NormalForm Empty) [.conj .top .top]) =
      .there (.here (.conj .top .top) []) := by rfl
'''
})
controls['missing-sequential-repair'] = '''example (f : G Empty [.top,.top,.top] [.top,.top,.top]) :
    G Empty [.top,.top] [.top,.top] := f
'''
rows=[]
for name,body in controls.items():
 path=local/(name+'.lean');path.write_text('module\nimport DosenPetric\nopen DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen\n'+body)
 log=local/(name+'.log');cmd=['lake','env','lean','-DwarningAsError=true',str(path)]
 with log.open('w') as f:
  p=subprocess.run(['flock','-n',str(root/'.codex-work/build.lock'),*cmd],cwd=root,env=dict(os.environ,LEAN_NUM_THREADS='1'),stdout=f,stderr=subprocess.STDOUT)
 content=log.read_text();expected='type mismatch' if name.startswith('missing-') else 'Tactic `rfl` failed'
 assert p.returncode!=0 and expected in (content.lower() if name.startswith('missing-') else content),content
 row=dict(name=name,command=cmd,exit_status=p.returncode,expected_rejection=True,passed=True,source=str(path.relative_to(root)),source_sha256=sha(path.read_bytes()),log=str(log.relative_to(root)),log_sha256=sha(log.read_bytes()))
 rows.append(row);print(json.dumps(row),flush=True)
assert len(rows)==21
(local/'FOCUSED_CONTROLS.json').write_text(json.dumps(rows,indent=2)+'\n')
