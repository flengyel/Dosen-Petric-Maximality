controls={
 'missing-parallel-input-contraction': """example (k : G Empty [.top] [.top]) (l : G Empty [.top] [.top]) :
    G Empty [.top] [.top,.top] := G.mix k l\n""",
 'missing-parallel-output-contraction': """example (k : G Empty [.top] [.top,.bot]) (l : G Empty [.top] [.top,.bot]) :
    G Empty [.top,.top] [.top,.top,.bot] := G.mix k l\n""",
 'blocked-equal-label-fixed-tag': """example :
    (BlockedMix.gammaFirstRoute (.top : NormalForm Empty) [.top] [.top] [.top] [.top]).get
      (.here .top [.top]) = .here .top [.top,.top,.top] := by rfl\n""",
 'missing-disj-output-exchange': """example (k : G Empty [.top] [.top,.bot]) (g : G Empty [.top] [.top]) :
    G Empty [.disj .top .top] [.top,.top,.bot] := G.disjL k g\n""",
 'missing-disj-retained-input': """example (k : G Empty [.bot,.top] [.top]) (g : G Empty [.top] [.top]) :
    G Empty [.disj .top .top,.bot] [.top,.top] := G.disjL k g\n""",
 'missing-second-output-exchange': '''example (f : G Empty [] [.top,.top]) (k : G Empty [] [.top,.bot]) :
    G Empty [] [.top,.conj .top .bot,.top] :=
   G.conjR f ((HeadRouting.front [.top] [] .bot).right k)\n''',
 'missing-retained-A': '''example (k : G Empty [] [.top,.bot]) (g : G Empty [] [.top]) :
   G Empty [] [.conj .bot .top,.top] := G.conjR k g\n''',
 'missing-conj-output-exchange': '''example (k : G Empty [.top] [.top,.bot]) (g : G Empty [.top] [.top,.top]) :
   G Empty [.top,.top] [.conj .top .top,.top,.bot] := G.conjR k g\n''',
 'missing-retained-B': '''example (f : G Empty [.top] [.top]) (k : G Empty [.bot] [.bot]) :
   G Empty [.top,.bot] [.conj .top .top] := G.conjR f k\n''',
 'missing-first-input-exchange': '''example (k : G Empty [.bot] [.top]) (g : G Empty [.top] [.top]) :
   G Empty [.bot,.top] [.top,.top] := G.mix k g\n''',
 'equal-label-collapse': '''example :
   (LogicalDeletion.headBefore (.there (.here (.top : NormalForm Nat) [])) [.top]).get
     (.here .top [.top,.top]) = .here .top [.top,.top] := by rfl\n''',
 'mix-conventional-order': '''example :
   (Premise.mix_left (G.identity (P := Nat) (.neg 0)) (G.identity (.neg 0))).parent .right
     (.here (.lit (.neg 0)) []) = some (.here (.lit (.neg 0)) [.lit (.neg 0)]) := by rfl\n'''
}
rows=[]
for name,body in controls.items():
 path=local/(name+'.lean');path.write_text('module\nimport DosenPetric\nopen DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen\n'+body)
 # Preserve a genuine expected rejection without treating it as a runner failure.
 log=local/(name+'.log');start=time.monotonic();cmd=['lake','env','lean','-DwarningAsError=true',str(path)]
 with log.open('w') as f:
  p=subprocess.run(['flock','-n',str(root/'.codex-work/build.lock'),*cmd],cwd=root,env=dict(os.environ,LEAN_NUM_THREADS='1'),stdout=f,stderr=subprocess.STDOUT)
 content=log.read_text();expected='type mismatch' if name in ['missing-first-input-exchange','missing-retained-B','missing-conj-output-exchange','missing-retained-A','missing-second-output-exchange','missing-disj-output-exchange','missing-disj-retained-input','missing-parallel-input-contraction','missing-parallel-output-contraction'] else 'Tactic `rfl` failed'
 assert p.returncode!=0 and expected in (content.lower() if name in ['missing-first-input-exchange','missing-retained-B','missing-conj-output-exchange','missing-retained-A','missing-second-output-exchange','missing-disj-output-exchange','missing-disj-retained-input','missing-parallel-input-contraction','missing-parallel-output-contraction'] else content),content
 row=dict(name=name,command=cmd,exit_status=p.returncode,expected_rejection=True,passed=True,source=str(path.relative_to(root)),source_sha256=sha(path.read_bytes()),log=str(log.relative_to(root)),log_sha256=sha(log.read_bytes()))
 rows.append(row);print(json.dumps(row))
(local/'FOCUSED_CONTROLS.json').write_text(json.dumps(rows,indent=2)+'\n')
