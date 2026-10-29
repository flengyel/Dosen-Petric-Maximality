fp_qe=Path('/tmp/dp-qe-controls.py').read_text()
exec(fp_qe[:fp_qe.index('\nexec(pc_controls_loop[pc_controls_loop.index(')])
controls['substituted-inner-crossing']='''example : Presentation.occurrenceMap
    (Presentation.substitute (fun _ : Nat => (Formula.conj (.var 0) (.var 0) : Formula Nat))
      (Presentation.id (.var 0))) (Sum.inl ()) (Sum.inr ()) := by rfl
'''
controls['substituted-old-repeated-tag-collapse']='''example :
    (Formula.expand (fun p : Nat => Formula.var p) (Formula.conj (.var 0) (.var 0)) (Sum.inl ())).1 =
    (Formula.expand (fun p : Nat => Formula.var p) (Formula.conj (.var 0) (.var 0)) (Sum.inr ())).1 := by rfl
'''
controls['missing-empty-substitution-block-point']='''example :
    ((Formula.var 0 : Formula Nat).subst (fun _ : Nat => (Formula.top : Formula Empty))).Occ := ()
'''
controls['missing-original-isolation-endpoint-transport']='''example {P : Type} (A : Formula P)
    (x : (Presentation.NegationNormalization.normal A).formula.Occ) :
    Presentation.Hom (.conj ((Presentation.NegationNormalization.normal A).literalAt x).formula .bot) A :=
  Isolation.selector (Presentation.operations P) (Presentation.NegationNormalization.normal A) x
'''
controls['missing-negate-substitute-variance']='''example {P R : Type} (σ : P → Formula R) {A B : Formula P} (f : Presentation.Hom A B) :
    Presentation.Hom (.neg (A.subst σ)) (.neg (B.subst σ)) := Presentation.substitute σ (Presentation.negate f)
'''
controls['missing-variable-for-cartesian-obstruction']='''example :
    ¬ (∀ A B : Formula Empty, Nonempty (ExponentialData (Presentation.operations Empty) A B)) :=
  Presentation.not_cartesian_closed (P:=Empty) ()
'''
exec(pc_controls_loop[pc_controls_loop.index('\nrows=[]'):].replace('len(rows)==27','len(rows)==56'))
