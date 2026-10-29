s=Path('/tmp/dp-lg-controls.py').read_text()
exec(s[:s.index('\nrows=[]')])
controls.update({
 'terminal-principal-is-fixed-copy': '''example :
    ((BlockedMix.gammaBlock (.disj .top .top : NormalForm Empty) [] [] [] []).extend [.disj .top .top]).route.get
      (At.shift ([.disj .top .top]++[.disj .top .top]) (.here (.disj .top .top) [])) =
    (BlockedMix.gammaBlock (.disj .top .top) [] [] [] []).keep.before [.disj .top .top] := by rfl
'''
})
controls['conjunction-principal-is-fixed-copy'] = """example :
    (BlockedRightConj.gammaBlock (.top : NormalForm Empty) .top (.conj .top .top) [] [] [] []).route.get
      (.here (.conj .top .top) [.conj .top .top,.conj .top .top]) =
    (BlockedRightConj.gammaBlock .top .top (.conj .top .top) [] [] [] []).keep := by rfl
"""

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
assert len(rows)==17
(local/'FOCUSED_CONTROLS.json').write_text(json.dumps(rows,indent=2)+'\n')
