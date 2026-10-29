pc_controls_loop=Path('/tmp/dp-ls-controls.py').read_text()
pc_global_prior=Path('/tmp/dp-gi-controls.py').read_text()
exec(pc_global_prior[:pc_global_prior.index('\nexec(gi_controls_loop[gi_controls_loop.index(')])
controls['pure-port-repeated-label-collapse']='''example (l : Literal Nat) :
    (PurePort.left (.lit l) (PurePort.here l) : PurePort .conj (.conj (.lit l) (.lit l)) l).position =
    (PurePort.right (.lit l) (PurePort.here l) : PurePort .conj (.conj (.lit l) (.lit l)) l).position := by rfl
'''
controls['pure-edge-crossed-target']='''example (l : Literal Nat) :
    occurrenceMap (PureEdge.arrow (P:=Nat) (A:=.lit l) (B:=.disj (.lit l) (.lit l))
      ⟨l,.here l,.left (.lit l) (.here l)⟩) l.point (Sum.inr l.point) := by
  rw [PureEdge.relation]
  constructor <;> rfl
'''
controls['missing-normal-retraction-direction']='''example {P : Type} (X A B : NormalForm P) :
    Hom (.disj (.conj X A) (.conj X B)) (.conj X (.disj A B)) :=
  (NormalRetract.dnfRight X A B).forward
'''
controls['missing-normal-form-zero-witness']='''example {P : Type} (A B : NormalForm P) : Hom A B := finiteUnion (id A) []
'''
exec(pc_controls_loop[pc_controls_loop.index('\nrows=[]'):].replace('len(rows)==27','len(rows)==43'))
