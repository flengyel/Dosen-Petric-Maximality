import re
base=root/'DosenPetric'
mods=sorted(p for p in base.glob('Gentzen*.lean') if subprocess.run(['git','cat-file','-e','ecfe8da:'+str(p.relative_to(root))],cwd=root,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode)
assert len(mods)==32,len(mods)
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
namespace BlockedLeftDisjChecks
'''
for file,name,ns,call in [('GentzenBlockedLeftGammaDisj','gammaParent_source','BlockedLeftDisj','f g'),('GentzenBlockedLeftGammaDisjRank','gamma_first_descent','BlockedLeftDisj','f g h z hc'),('GentzenBlockedLeftGammaDisjRank','gamma_second_descent','BlockedLeftDisj','f g h z hc'),('GentzenBlockedLeftGammaDisj','gamma_equation','BlockedLeftDisj','f g h z'),('GentzenBlockedLeftGammaDisjRank','blockedL_gammaDisj_rank_step','CutCommutation','f g h z hc ih')]:
 s=(base/(file+'.lean')).read_text();m=re.search(r'^theorem '+name+r'\s([\s\S]*?) := by\n',s,re.M);assert m,name
 checks+='\nsection\nopen BlockedLeftDisj\nexample {P : Type u} '+m[1]+' :=\n  '+ns+'.'+name+' '+call+'\nend\n'
checks+='''
def literalChild (l : Literal Nat) : G Nat [.lit l,.lit l] [.lit l] :=
  G.thinL [] [.lit l] [.lit l] (.lit l) (G.identity l)

theorem literalChildCut (l : Literal Nat) : PositionalCut.Eliminated
    (G.identity l) (.here (.lit l) []) (literalChild l) (.here (.lit l) [.lit l]) :=
  PositionalCut.endomorphism_thin (Γ:=[]) (Θ:=[.lit l]) (Λ:=[.lit l]) (.lit l)
    (G.identity l) (G.identity l) rfl True.intro True.intro

def constantChild : G Empty [.top,.top] [.top] :=
  G.thinL [] [.top] [.top] .top G.topIdentity

theorem constantChildCut : PositionalCut.Eliminated (P:=Empty)
    G.topI (.here .top []) constantChild (.here .top [.top]) :=
  PositionalCut.top_thin [] [.top] [.top] G.topIdentity rfl ⟨True.intro,True.intro⟩

def twoTops : G Empty [.top] [.top,.top] := G.thinR [.top] [] [.top] .top G.topIdentity

def topPair : G Empty [.top,.top] [.top,.top] := G.thinL [] [.top] [.top,.top] .top twoTops

def threeTops : G Empty [.top,.top,.top] [.top,.top] :=
  G.thinL [.top] [.top] [.top,.top] .top topPair

def fourTops : G Empty [.top,.top,.top,.top] [.top,.top] :=
  G.thinL [.top] [.top,.top] [.top,.top] .top threeTops

theorem populatedChildCut : PositionalCut.Eliminated twoTops (.here .top [.top])
    fourTops (.there (.here .top [.top,.top])) :=
  PositionalCut.thin_thin [.top] [] [.top] [.top] [.top,.top] [.top,.top] .top G.topIdentity threeTops
    rfl rfl ⟨True.intro,True.intro⟩ (by repeat constructor)

example (l : Literal Nat) : PositionalCut.Eliminated (G.identity l) (.here (.lit l) [])
    (BlockedLeftDisj.gammaParent (X:=[]) (Y:=[]) (Z:=[]) (T:=[]) (literalChild l) (literalChild l))
    ((BlockedMix.gammaBlock (.lit l) [] [] [] []).keep.before [.disj (.lit l) (.lit l)]) :=
  CutCommutation.blockedL_gammaDisj_eliminated (X:=[]) (Y:=[]) (Z:=[]) (T:=[])
    (literalChild l) (literalChild l) (G.identity l) (.here (.lit l) []) (literalChildCut l) (literalChildCut l)

example : PositionalCut.Eliminated (G.identity (P:=Nat) (.neg 0)) (.here (.lit (.neg 0)) [])
    (BlockedLeftDisj.gammaParent (X:=[]) (Y:=[]) (Z:=[]) (T:=[])
      (literalChild (.neg 0)) (literalChild (.neg 0)))
    ((BlockedMix.gammaBlock (.lit (.neg 0)) [] [] [] []).keep.before [.disj (.lit (.neg 0)) (.lit (.neg 0))]) :=
  CutCommutation.blockedL_gammaDisj_eliminated (X:=[]) (Y:=[]) (Z:=[]) (T:=[])
    (literalChild (.neg 0)) (literalChild (.neg 0)) (G.identity (.neg 0)) (.here (.lit (.neg 0)) [])
    (literalChildCut (.neg 0)) (literalChildCut (.neg 0))

example : PositionalCut.Eliminated (P:=Empty) G.topI (.here .top [])
    (BlockedLeftDisj.gammaParent (X:=[]) (Y:=[]) (Z:=[]) (T:=[]) constantChild constantChild)
    ((BlockedMix.gammaBlock .top [] [] [] []).keep.before [.disj .top .top]) :=
  CutCommutation.blockedL_gammaDisj_eliminated (X:=[]) (Y:=[]) (Z:=[]) (T:=[])
    constantChild constantChild G.topI (.here .top []) constantChildCut constantChildCut

example : PositionalCut.Eliminated twoTops (.here .top [.top])
    (BlockedLeftDisj.gammaParent (X:=[.top]) (Y:=[.top]) (Z:=[.top]) (T:=[.top]) fourTops fourTops)
    ((BlockedMix.gammaBlock .top [.top] [.top] [.top] [.top]).keep.before [.disj .top .top]) :=
  CutCommutation.blockedL_gammaDisj_eliminated (X:=[.top]) (Y:=[.top]) (Z:=[.top]) (T:=[.top])
    fourTops fourTops twoTops (.here .top [.top]) populatedChildCut populatedChildCut

example :
    (((BlockedMix.gammaBlock (.disj .top .top : NormalForm Empty) [] [] [] []).extend [.disj .top .top]).route.get
      (At.shift ([.disj .top .top]++[.disj .top .top]) (.here (.disj .top .top) []))).index = 1 := by rfl

end BlockedLeftDisjChecks
'''
p=root/'Checks/Axioms.lean';s=p.read_text()
for ns,name in [('ContractionSplice','binary'),('DoubleDisjSplice','equation'),('BlockedLeftDisj','canonical_equation'),('BlockedLeftDisj','headParent_equation'),('BlockedLeftDisj','selected_equation'),('BlockedLeftDisj','gamma_equation'),('BlockedLeftDisj','gamma_first_descent'),('BlockedLeftDisj','gamma_second_descent'),('CutCommutation','blockedL_gammaDisj_rank_step')]:
 line='#print axioms DosenPetric.Reduced.Gentzen.'+ns+'.'+name+'\n'
 if line not in s:s+=line
 checks+='\n'+line
p.write_text(s);(root/'Checks/BlockedLeftDisj.lean').write_text(checks)
print('Integrated',len(mods),'modules, exact original-source/rank signatures and four actual witnesses')
