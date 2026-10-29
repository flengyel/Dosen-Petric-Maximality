fp=Path('/tmp/dp-fp-controls.py').read_text()
exec(fp[:fp.index("\nexec(pc_controls_loop[pc_controls_loop.index(")])
controls['model-missing-nonempty-variables']='''example {X : Type} {C : Category X} {O : PresentationSemantics.Objects X}
    {S : PresentationSemantics.Primitives C O} (M : PresentationSemantics.Model Empty S)
    {A B : Formula Empty} (f g : Presentation.Hom A B) (hne : f ≠ g)
    (h : ∀ α : Empty → X, S.evaluateHom M.equations α f = S.evaluateHom M.equations α g) :
    ∀ {Y Z : X} (a b : C.Hom Y Z), a = b := PresentationSemantics.model_corollary M f g hne h
'''
controls['missing-model-one-valuation-kernel']='''example {X : Type} {C : Category X} {O : PresentationSemantics.Objects X}
    {S : PresentationSemantics.Primitives C O} (M : PresentationSemantics.Model Nat S)
    {A B : Formula Nat} (f g : Presentation.Hom A B) (hne : f ≠ g) (α : Nat → X)
    (h : S.evaluateHom M.equations α f = S.evaluateHom M.equations α g) :
    ∀ {Y Z : X} (a b : C.Hom Y Z), a = b := PresentationSemantics.model_corollary M f g hne h
'''
controls['missing-model-substitution-precomposition-variance']='''example {X : Type} {C : Category X} {O : PresentationSemantics.Objects X}
    {S : PresentationSemantics.Primitives C O} (F : PresentationSemantics.Interpretation S Empty)
    (σ : Nat → Formula Empty) : PresentationSemantics.Interpretation S Empty := F.precompose σ
'''
controls['missing-model-evaluation-reverses-endpoints']='''example {X : Type} {C : Category X} {O : PresentationSemantics.Objects X}
    {S : PresentationSemantics.Primitives C O} (M : PresentationSemantics.Model Nat S) (α : Nat → X)
    {A B : Formula Nat} (f : Presentation.Hom A B) :
    C.Hom (PresentationSemantics.formula O α B) (PresentationSemantics.formula O α A) :=
  S.evaluateHom M.equations α f
'''
controls['missing-model-missing-generating-equations']='''example {X : Type} {C : Category X} {O : PresentationSemantics.Objects X}
    {S : PresentationSemantics.Primitives C O} (α : Nat → X) :
    Functor (Presentation.category Nat) C := S.evaluationFunctor True.intro α
'''
loop=pc_controls_loop[pc_controls_loop.index('\nrows=[]'):].replace('len(rows)==27','len(rows)==61')
loop=loop.replace("expected='type mismatch' if name.startswith('missing-') else 'Tactic `rfl` failed'", "expected='failed to synthesize' if name=='model-missing-nonempty-variables' else ('type mismatch' if name.startswith('missing-') else 'tactic `rfl` failed')")
loop=loop.replace("(content.lower() if name.startswith('missing-') else content)", "content.lower()")
exec(loop)
