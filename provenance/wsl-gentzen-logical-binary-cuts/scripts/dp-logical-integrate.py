import re
base=root/'DosenPetric'
mods=[*sorted(base.glob('GentzenBinaryLogical*.lean')),*sorted(base.glob('GentzenConjRightSecond*.lean')),base/'GentzenMixedDisjSymmetry.lean']
p=root/'DosenPetric.lean';s=p.read_text()
for m in mods:
 line='public import DosenPetric.'+m.stem+'\n'
 if line not in s:s+=line
p.write_text(s)
source=(base/'GentzenConjRightSecondSelected.lean').read_text()
checks='''module

import DosenPetric

set_option autoImplicit false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
open DosenPetric.Reduced.Gentzen.BinaryLogical
'''
for name,ns,args in [
 ('conjRRightSecond_equation','BinaryLogical','f g h z a'),
 ('conjRRightSecond_count','BinaryLogical','f a k'),
 ('conjRRightSecond_atomized','BinaryLogical','f a k'),
 ('conjRRightSecond_congr','BinaryLogical',"f a k k' hk"),
 ('conjR_right_second_rank_step','CutCommutation','f g h z a hc ih')]:
 match=re.search(r'^theorem '+name+r'\s([\s\S]*?) := by\n',source,re.M);assert match,name
 checks+='\nexample {P : Type u} '+match[1]+' :=\n  '+ns+'.'+name+' '+args+'\n'
checks+='''
theorem literalChild (l : Literal Nat) : PositionalCut.Eliminated (G.identity l) (.here (.lit l) [])
    (G.identity l) (.here (.lit l) []) :=
  ⟨G.identity l,rfl,True.intro,(CutBase.identity_identity l).symm⟩

-- Equal formula labels occupy two distinct inputs in this actual reconstruction.
example (l : Literal Nat) : PositionalCut.Eliminated
    (G.identity l) (.here (.lit l) [])
    (G.conjR (G.identity l) (G.identity l)) (.there (.here (.lit l) [])) :=
  CutCommutation.conjR_right_second_eliminated _ _ _ _ _ rfl True.intro (literalChild l)

example : PositionalCut.Eliminated (P := Nat)
    (G.identity (.neg 0)) (.here (.lit (.neg 0)) [])
    (G.conjR (G.identity (.neg 0)) (G.identity (.neg 0))) (.there (.here (.lit (.neg 0)) [])) :=
  CutCommutation.conjR_right_second_eliminated _ _ _ _ _ rfl True.intro (literalChild (.neg 0))

theorem constantChild : PositionalCut.Eliminated (P := Empty) G.topI (.here .top [])
    G.topIdentity (.here .top []) :=
  PositionalCut.top_thin [] [] [.top] G.topI rfl True.intro

example : PositionalCut.Eliminated (P := Empty) G.topI (.here .top [])
    (G.conjR G.topI G.topIdentity) (.here .top []) :=
  CutCommutation.conjR_right_second_eliminated _ _ _ _ _ rfl True.intro constantChild
'''
p=root/'Checks/Axioms.lean';audit=p.read_text()
for ns,names in [('CutCommutation',['conjR_right_second_rank_step']),('BinaryLogical',['conjRRightSecond_equation','mixedDisj_swap'])]:
 for name in names:
  checks+='\n#print axioms '+ns+'.'+name+'\n'
  line='#print axioms DosenPetric.Reduced.Gentzen.'+ns+'.'+name+'\n'
  if line not in audit:audit+=line
p.write_text(audit);(root/'Checks/LogicalBinaryCuts.lean').write_text(checks)
print('Integrated',len(mods),'logical modules and expanded exact reconstruction/witness checks')
