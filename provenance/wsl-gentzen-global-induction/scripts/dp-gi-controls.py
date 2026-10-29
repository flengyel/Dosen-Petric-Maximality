gi_controls_loop=Path('/tmp/dp-ls-controls.py').read_text()
gi_all_prior=Path('/tmp/dp-rb-controls.py').read_text()
exec(gi_all_prior[:gi_all_prior.index('\nexec(rb_controls_source[rb_controls_source.index(')])
controls['global-source-equality-is-not-syntax']='''example :
    G.cut (G.identity (P:=Nat) (.neg 0)) (G.identity (.neg 0)) = G.identity (.neg 0) := by rfl
'''
controls['missing-original-output-sequent']='''example {P : Type} {Γ Δ : List (NormalForm P)} (t : G P Γ Δ) :
    G P Δ Γ := Classical.choose (atomized_cut_elimination t)
'''
controls['global-top-degree-zero']='''example : cutDegree (.top : NormalForm Empty) = 0 := by rfl
'''
controls['global-bottom-degree-zero']='''example : cutDegree (.bot : NormalForm Empty) = 0 := by rfl
'''
exec(gi_controls_loop[gi_controls_loop.index('\nrows=[]'):].replace('len(rows)==27','len(rows)==39'))
