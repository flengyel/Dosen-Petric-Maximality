qe_sp=Path('/tmp/dp-sp-controls.py').read_text()
exec(qe_sp[:qe_sp.index('\nexec(pc_controls_loop[pc_controls_loop.index(')])
controls['missing-short-cancel-first-injection']='''example {P : Type} (Q : Congruence (Presentation.operations P))
    {A B : Formula P} (f g : Presentation.Hom A B)
    (h : Q.Rel (Presentation.comp f (Presentation.inl B .top))
      (Presentation.comp g (Presentation.inl B .top))) : Q.Rel f g := h
'''
controls['missing-short-all-contexts']='''example {P : Type} (Q : Congruence (Presentation.operations P))
    (A : Formula P) (h : ContextualCollapse.K Q (Z := Presentation.zeroIdentity P) A) : Q.Total :=
  Presentation.ShortProof.total Q h
'''
controls['missing-short-inverse-direction']='''example {P : Type} (A : Formula P) :
    Presentation.Hom (.conj A (.disj A .top)) (.conj A A) := Presentation.ShortProof.e A
'''
exec(pc_controls_loop[pc_controls_loop.index('\nrows=[]'):].replace('len(rows)==27','len(rows)==50'))
