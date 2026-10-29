sp_pc=Path('/tmp/dp-pc-controls.py').read_text()
exec(sp_pc[:sp_pc.index('\nexec(pc_controls_loop[pc_controls_loop.index(')])
controls['missing-full-source-substitution-closure']='''example {P : Type} (Q : Presentation.ProofCongruence P)
    {A B : Formula P} (f g : Presentation.Hom A B) (hne : f ≠ g) (hfg : Q.Rel f g) : Q.Total :=
  Presentation.maximality Q f g hne hfg
'''
controls['missing-dual-involution-endpoint-casts']='''example {P : Type} {A B : NormalForm P} (f : Hom A B) : Hom A B :=
  dualHom (dualHom f)
'''
controls['missing-negation-reversed-composition']='''example {P : Type} (A : Formula P) (f g : Presentation.Hom A A) :
    Presentation.negate (Presentation.comp f g) =
      Presentation.comp (Presentation.negate f) (Presentation.negate g) := Presentation.negate_comp f g
'''
controls['dual-repeated-port-crossing']='''example (l : Literal Nat) :
    (Term.fst (.lit l) (.lit l)).dual = Term.inr (.lit l.flip) (.lit l.flip) := by rfl
'''
exec(pc_controls_loop[pc_controls_loop.index('\nrows=[]'):].replace('len(rows)==27','len(rows)==47'))
