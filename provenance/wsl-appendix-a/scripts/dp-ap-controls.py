s=Path('/tmp/dp-md-controls.py').read_text()
exec(s[:s.index('\nloop=')])
controls['ordinal-empty-block-locator']='''example :
    (FiniteBlocks.decode (fun i : Fin 3 => if i.val=1 then 0 else 1) (1 : Fin 2)).1 = (1 : Fin 3) := by rfl
'''
controls['ordinal-example-one-based-shift']='''example : (PatternProfiles.Example.delta 1).val+1=2 := by rfl
'''
controls['profile-repeated-source-tags']='''example :
    PatternProfiles.Example.profiles.a 0 (1 : Fin 3) = PatternProfiles.Example.profiles.a 2 (1 : Fin 3) := by rfl
'''
controls['missing-action-endpoint-transport']='''example {P R T : Type} (σ : P → Formula R) (τ : R → Formula T)
    {A B : Formula P} (f : Presentation.Hom A B) :
    Presentation.substitute τ (Presentation.substitute σ f) = Presentation.substitute (fun p => (σ p).subst τ) f := by rfl
'''
controls['missing-action-substitution-order']='''example {P R T : Type} (σ : P → Formula R) (τ : R → Formula T)
    {A B : Formula P} (f : Presentation.Hom A B) :
    Presentation.Hom (A.subst σ) (B.subst σ) := Presentation.substitute σ (Presentation.substitute τ f)
'''
controls['missing-negative-context-double-negation']='''example {P : Type} (p : P) (A : Formula P) : Presentation.Hom (.conj A .bot) (.disj A .top) :=
    Presentation.substitute (fun _ : P => .neg A) (Presentation.ManuscriptSubstitution.context (.neg (.var p)))
'''
controls['missing-quotient-hom-witness']='''example (Q : Presentation.ProofCongruence Nat) : Q.fragment.QuotientHom .top .bot := Q.fragment.classOf (Presentation.id .top)
'''
controls['noninjective-renaming-keeps-positions']='''example :
    Formula.renameOcc (fun _ : Nat => ()) (Formula.conj (.var 0) (.var 1)) (Sum.inl ()) =
    Formula.renameOcc (fun _ : Nat => ()) (Formula.conj (.var 0) (.var 1)) (Sum.inr ()) := by rfl
'''
loop=pc_controls_loop[pc_controls_loop.index('\nrows=[]'):].replace('len(rows)==27','len(rows)==69')
loop=loop.replace("expected='type mismatch' if name.startswith('missing-') else 'Tactic `rfl` failed'", "expected='failed to synthesize' if name=='model-missing-nonempty-variables' else ('type mismatch' if name.startswith('missing-') else 'tactic `rfl` failed')")
loop=loop.replace("(content.lower() if name.startswith('missing-') else content)", "content.lower()")
exec(loop)
