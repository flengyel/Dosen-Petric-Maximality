s=Path('/tmp/dp-sd-controls.py').read_text()
exec(s[:s.index('\nrows=[]')])
controls.update({
 'fresh-right-total-rank-one': '''example :
    PositionalCut.rank (P:=Empty)
      (G.disjR [] [] [] .top .bot (G.thinR [] [.top] [] .bot G.topI)) (.here (.disj .top .bot) [])
      (G.disjL G.topIdentity G.botIdentity) (.here (.disj .top .bot) []) = 1 := by
  unfold PositionalCut.rank
  rw [G.rho_disjR_principal,G.rho_disjL_principal]
  rfl
''',
 'source-wrapper-native-rank-one': '''example :
    (BlockedSource.disjLLast (Γ:=[]) (Θ:=[]) (G.topIdentity (P:=Empty)) G.topIdentity).rho
      .left (.here (.disj .top .top) []) = 1 := by
  rw [BlockedSource.disjLLast_rank_principal]
  rfl
'''
})
controls['sequential-returned-rank'] = r"""example :
    (G.conjL [] [] [.top] .top .top (G.thinL [] [.top] [.top] .top (G.topIdentity (P:=Empty)))).rho
      .left (.here (.conj .top .top) []) =
      (G.thinL [] [.top] [.top] .top (G.topIdentity (P:=Empty))).rho .left (.here .top [.top])+1 := by
  have hf : (G.conjL [] [] [.top] .top .top
      (G.thinL [] [.top] [.top] .top (G.topIdentity (P:=Empty)))).rho .left (.here (.conj .top .top) []) = 1 :=
    G.rho_conjL_principal [] [] [.top] .top .top _
  have hk : (G.thinL [] [.top] [.top] .top (G.topIdentity (P:=Empty))).rho .left (.here .top [.top]) = 1 :=
    G.rho_thinL_principal [] [.top] [.top] .top _
  rw [hf,hk]
  rfl
"""
controls['fresh-disjunction-returned-rank'] = r"""example :
    (G.disjR [.top] [] [] .top .top (G.thinR [.top] [] [.top] .top (G.topIdentity (P:=Empty)))).rho
      .right (.here (.disj .top .top) []) =
      (G.thinR [.top] [] [.top] .top (G.topIdentity (P:=Empty))).rho .right (.here .top [.top])+1 := by
  have hf : (G.disjR [.top] [] [] .top .top
      (G.thinR [.top] [] [.top] .top (G.topIdentity (P:=Empty)))).rho .right (.here (.disj .top .top) []) = 1 :=
    G.rho_disjR_principal [.top] [] [] .top .top _
  have hk : (G.thinR [.top] [] [.top] .top (G.topIdentity (P:=Empty))).rho .right (.here .top [.top]) = 1 :=
    G.rho_thinR_principal [.top] [] [.top] .top _
  rw [hf,hk]
  rfl
"""
controls['fresh-right-total-rank-one'] = r"""example :
    PositionalCut.rank (P:=Empty)
      (G.disjR [] [] [] .top .bot (G.thinR [] [.top] [] .bot G.topI)) (.here (.disj .top .bot) [])
      (G.disjL G.topIdentity G.botIdentity) (.here (.disj .top .bot) []) = 1 := by
  have hf : (G.disjR [] [] [] .top .bot (G.thinR [] [.top] [] .bot (G.topI (P:=Empty)))).rho
      .right (.here (.disj .top .bot) []) = 1 := G.rho_disjR_principal [] [] [] .top .bot _
  have hg : (G.disjL (G.topIdentity (P:=Empty)) G.botIdentity).rho
      .left (.here (.disj .top .bot) []) = 1 := G.rho_disjL_principal _ _
  unfold PositionalCut.rank
  rw [hf,hg]
  rfl
"""
controls['source-wrapper-native-rank-one'] = r"""example :
    (BlockedSource.disjLLast (Γ:=[]) (Θ:=[]) (G.topIdentity (P:=Empty)) G.topIdentity).rho
      .left (.here (.disj .top .top) []) = 1 := by
  have hr : (BlockedSource.disjLLast (Γ:=[]) (Θ:=[]) (G.topIdentity (P:=Empty)) G.topIdentity).rho
      .left (.here (.disj .top .top) []) = 2 := BlockedSource.disjLLast_rank_principal _ _
  rw [hr]
  rfl
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
 rows.append(row);print(json.dumps(row),flush=True)
assert len(rows)==26
(local/'FOCUSED_CONTROLS.json').write_text(json.dumps(rows,indent=2)+'\n')
