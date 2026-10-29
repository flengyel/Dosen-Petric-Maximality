import re
base=root/'DosenPetric'
mods=sorted(p for p in base.glob('Gentzen*.lean') if subprocess.run(['git','cat-file','-e','f04b638:'+str(p.relative_to(root))],cwd=root,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode)
assert len(mods)==13,len(mods)
p=root/'DosenPetric.lean';s=p.read_text()
for m in mods:
 line='public import DosenPetric.'+m.stem+'\n'
 if line not in s:s+=line
p.write_text(s)
checks='''module

import DosenPetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
namespace BlockedDisjChecks
'''
s=(base/'GentzenBlockedGammaDisj.lean').read_text()
for name,ns,call in [('gamma_equation','BlockedDisj','f g h z'),('blockedR_gammaDisj_rank_step','CutCommutation','f g h z hc ih')]:
 m=re.search(r'^theorem '+name+r'\s([\s\S]*?) := by\n',s,re.M);assert m,name
 checks+='\nsection\nopen BlockedDisj\nexample {P : Type u} '+m[1]+' :=\n  '+ns+'.'+name+' '+call+'\nend\n'
s=(root/'Checks/DisjBinaryCuts.lean').read_text();start=s.index('theorem identityChild');end=s.index('\nexample (l : Literal Nat)',start)
checks+='\n'+s[start:end]+'''
theorem constantChild : PositionalCut.Eliminated (P := Empty) G.topIdentity (.here .top [])
    G.topIdentity (.here .top []) :=
  PositionalCut.endomorphism_thin (Γ := []) (Θ := []) (Λ := [.top])
    .top G.topIdentity G.topI rfl True.intro True.intro

example (l : Literal Nat) : PositionalCut.Eliminated
    (BlockedDisj.gammaParent (F := []) (U := []) (X := []) (Y := []) (Z := []) (T := [])
      (G.identity l) (G.identity l))
    (BlockedMix.gammaBlock (.lit l) [] [] [] []).keep (G.identity l) (.here (.lit l) []) :=
  CutCommutation.blockedR_gammaDisj_eliminated (F := []) (U := []) (X := []) (Y := []) (Z := []) (T := [])
    (G.identity l) (G.identity l) (G.identity l) (.here (.lit l) []) (identityChild l) (identityChild l)

example : PositionalCut.Eliminated
    (BlockedDisj.gammaParent (F := []) (U := []) (X := []) (Y := []) (Z := []) (T := [])
      (G.identity (P := Nat) (.neg 0)) (G.identity (.neg 0)))
    (BlockedMix.gammaBlock (.lit (.neg 0)) [] [] [] []).keep
    (G.identity (.neg 0)) (.here (.lit (.neg 0)) []) :=
  CutCommutation.blockedR_gammaDisj_eliminated (F := []) (U := []) (X := []) (Y := []) (Z := []) (T := [])
    (G.identity (.neg 0)) (G.identity (.neg 0)) (G.identity (.neg 0)) (.here (.lit (.neg 0)) [])
    (identityChild (.neg 0)) (identityChild (.neg 0))

example : PositionalCut.Eliminated (P := Empty)
    (BlockedDisj.gammaParent (F := []) (U := []) (X := []) (Y := []) (Z := []) (T := [])
      G.topIdentity G.topIdentity)
    (BlockedMix.gammaBlock .top [] [] [] []).keep G.topIdentity (.here .top []) :=
  CutCommutation.blockedR_gammaDisj_eliminated (F := []) (U := []) (X := []) (Y := []) (Z := []) (T := [])
    G.topIdentity G.topIdentity G.topIdentity (.here .top []) constantChild constantChild

example : PositionalCut.Eliminated (P := Empty)
    (BlockedDisj.gammaParent (F := [.top]) (U := [.top])
      (X := [.top]) (Y := [.top]) (Z := [.top]) (T := [.top]) leftPop leftPop)
    (BlockedMix.gammaBlock .top [.top] [.top] [.top] [.top]).keep topPair (.here .top [.top]) :=
  CutCommutation.blockedR_gammaDisj_eliminated (F := [.top]) (U := [.top])
    (X := [.top]) (Y := [.top]) (Z := [.top]) (T := [.top])
    leftPop leftPop topPair (.here .top [.top]) leftPopChild leftPopChild

end BlockedDisjChecks
'''
p=root/'Checks/Axioms.lean';s=p.read_text()
for ns,name in [('BlockedDisj','right_shared_splice'),('BlockedDisj','headParent_equation'),('BlockedDisj','gamma_equation'),('CutCommutation','blockedR_gammaDisj_rank_step')]:
 line='#print axioms DosenPetric.Reduced.Gentzen.'+ns+'.'+name+'\n'
 if line not in s:s+=line
 checks+='\n#print axioms DosenPetric.Reduced.Gentzen.'+ns+'.'+name+'\n'
p.write_text(s);(root/'Checks/BlockedDisj.lean').write_text(checks)
print('Integrated',len(mods),'modules, two exact public types and four actual eliminated witnesses')
