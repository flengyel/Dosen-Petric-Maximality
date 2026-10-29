rb_controls_source=Path('/tmp/dp-ls-controls.py').read_text()
rb_prior_source=Path('/tmp/dp-rs-controls.py').read_text()
exec(rb_prior_source[:rb_prior_source.index('\nexec(rs_controls_source[rs_controls_source.index(')])
controls['right-three-copy-original-tags']='''example (C : NormalForm Empty) :
    (selectedCopies C [[],[C],[C,C]] [C]).map At.index = [0,2,2] := by rfl
'''
controls['missing-right-third-repair']='''example {P : Type} (Y D E Γ Θ I J : List (NormalForm P))
    (p : Route Y D) (q : Route Y E)
    (m : G P (I++((I++Γ)++(I++Θ))) (J++((J++D)++(J++E)))) :
    G P (I++(Γ++Θ)) (J++Y) := m
'''
exec(rb_controls_source[rb_controls_source.index('\nrows=[]'):].replace('len(rows)==27','len(rows)==35'))
