import re
base=root/'DosenPetric'
mods=sorted(p for p in base.glob('Gentzen*.lean') if subprocess.run(['git','cat-file','-e','26e6d8d:'+str(p.relative_to(root))],cwd=root,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode)
assert len(mods)==20,len(mods)
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
namespace BlockedGammaChecks
'''
for stem,ns,tag in [('GentzenBlockedGammaMix','BlockedMix','blockedL_gammaMix'),('GentzenBlockedRightGammaMix','BlockedMix','blockedR_gammaMix'),('GentzenBlockedGammaConj','BlockedConj','blockedL_gammaConj')]:
 s=(base/(stem+'.lean')).read_text()
 eq='gamma_right_equation' if stem=='GentzenBlockedRightGammaMix' else 'gamma_equation'
 for name,nspace,call in [(eq,ns,'f g h z'),(tag+'_rank_step','CutCommutation','f g h z hc ih')]:
  m=re.search(r'^theorem '+name+r'\s([\s\S]*?) := by\n',s,re.M);assert m,name
  checks+='\nsection\nopen '+ns+'\nexample {P : Type u} '+m[1]+' :=\n  '+nspace+'.'+name+' '+call+'\nend\n'
# Reuse the already checked actual literal, constant-only and populated child cuts.
s=(root/'Checks/DisjBinaryCuts.lean').read_text();start=s.index('theorem identityChild');end=s.index('\nexample (l : Literal Nat)',start)
checks+='\n'+s[start:end]+'''
theorem constantChild : PositionalCut.Eliminated (P := Empty) G.topI (.here .top [])
    G.topIdentity (.here .top []) :=
  PositionalCut.top_thin [] [] [.top] G.topI rfl True.intro
'''
for ns,parent,method in [('BlockedMix','gammaParent','blockedL_gammaMix'),('BlockedConj','gammaParent','blockedL_gammaConj')]:
 checks+='''
example (l : Literal Nat) : PositionalCut.Eliminated (G.identity l) (.here (.lit l) [])
    ('''+ns+'.'+parent+''' (X := []) (Y := []) (Z := []) (T := []) (G.identity l) (G.identity l))
    (BlockedMix.gammaBlock (.lit l) [] [] [] []).keep :=
  CutCommutation.'''+method+'''_eliminated (G.identity l) (G.identity l)
    (G.identity l) (.here (.lit l) []) (identityChild l) (identityChild l)
'''
 checks+='''
example : PositionalCut.Eliminated (G.identity (P := Nat) (.neg 0)) (.here (.lit (.neg 0)) [])
    ('''+ns+'.'+parent+''' (X := []) (Y := []) (Z := []) (T := [])
      (G.identity (.neg 0)) (G.identity (.neg 0)))
    (BlockedMix.gammaBlock (.lit (.neg 0)) [] [] [] []).keep :=
  CutCommutation.'''+method+'''_eliminated (G.identity (.neg 0)) (G.identity (.neg 0))
    (G.identity (.neg 0)) (.here (.lit (.neg 0)) []) (identityChild (.neg 0)) (identityChild (.neg 0))
'''
 checks+='''
example : PositionalCut.Eliminated (P := Empty) G.topI (.here .top [])
    ('''+ns+'.'+parent+''' (X := []) (Y := []) (Z := []) (T := []) G.topIdentity G.topIdentity)
    (BlockedMix.gammaBlock .top [] [] [] []).keep :=
  CutCommutation.'''+method+'''_eliminated G.topIdentity G.topIdentity G.topI (.here .top [])
    constantChild constantChild
'''
 checks+='''
example : PositionalCut.Eliminated twoTops (.here .top [.top])
    ('''+ns+'.'+parent+''' (X := [.top]) (Y := [.top]) (Z := [.top]) (T := [.top]) rightPop rightPop)
    (BlockedMix.gammaBlock .top [.top] [.top] [.top] [.top]).keep :=
  CutCommutation.'''+method+'''_eliminated rightPop rightPop twoTops (.here .top [.top])
    rightPopChild rightPopChild
'''
checks+='''
example (l : Literal Nat) : PositionalCut.Eliminated
    (BlockedMix.gammaRightParent (X := []) (Y := []) (Z := []) (T := []) (G.identity l) (G.identity l))
    (BlockedMix.gammaBlock (.lit l) [] [] [] []).keep (G.identity l) (.here (.lit l) []) :=
  CutCommutation.blockedR_gammaMix_eliminated (G.identity l) (G.identity l)
    (G.identity l) (.here (.lit l) []) (identityChild l) (identityChild l)

example : PositionalCut.Eliminated
    (BlockedMix.gammaRightParent (X := []) (Y := []) (Z := []) (T := [])
      (G.identity (P := Nat) (.neg 0)) (G.identity (.neg 0)))
    (BlockedMix.gammaBlock (.lit (.neg 0)) [] [] [] []).keep
    (G.identity (.neg 0)) (.here (.lit (.neg 0)) []) :=
  CutCommutation.blockedR_gammaMix_eliminated (G.identity (.neg 0)) (G.identity (.neg 0))
    (G.identity (.neg 0)) (.here (.lit (.neg 0)) []) (identityChild (.neg 0)) (identityChild (.neg 0))

example : PositionalCut.Eliminated (P := Empty)
    (BlockedMix.gammaRightParent (X := []) (Y := []) (Z := []) (T := []) G.topI G.topI)
    (BlockedMix.gammaBlock .top [] [] [] []).keep G.topIdentity (.here .top []) :=
  CutCommutation.blockedR_gammaMix_eliminated G.topI G.topI G.topIdentity (.here .top [])
    constantChild constantChild

example : PositionalCut.Eliminated
    (BlockedMix.gammaRightParent (X := [.top]) (Y := [.top]) (Z := [.top]) (T := [.top]) leftPop leftPop)
    (BlockedMix.gammaBlock .top [.top] [.top] [.top] [.top]).keep topPair (.here .top [.top]) :=
  CutCommutation.blockedR_gammaMix_eliminated leftPop leftPop topPair (.here .top [.top])
    leftPopChild leftPopChild

end BlockedGammaChecks
'''
lines=[]
for line in checks.splitlines():
 if 'CutCommutation.blocked' in line and '_eliminated ' in line:
  v='[.top]' if any(n in line for n in ['rightPop rightPop','leftPop leftPop']) else '[]'
  args=' '.join('('+n+' := '+v+')' for n in ['X','Y','Z','T'])
  line=line.replace('_eliminated ','_eliminated '+args+' ',1)
 lines.append(line)
checks='\n'.join(lines)+'\n'
p=root/'Checks/Axioms.lean';s=p.read_text()
for ns,name in [('BlockedMix','gamma_equation'),('BlockedMix','gamma_right_equation'),('BlockedConj','gamma_equation'),('BlockedConj','lifted_pair')]+[('CutCommutation',n+'_rank_step') for n in ['blockedL_gammaMix','blockedR_gammaMix','blockedL_gammaConj']]:
 line='#print axioms DosenPetric.Reduced.Gentzen.'+ns+'.'+name+'\n'
 if line not in s:s+=line
 checks+='\n#print axioms '+ns+'.'+name+'\n'
p.write_text(s);(root/'Checks/BlockedGamma.lean').write_text(checks)
print('Integrated',len(mods),'modules, six exact public types and twelve actual eliminated witnesses')
