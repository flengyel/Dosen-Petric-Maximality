import re
base=root/'DosenPetric'
mods=sorted(p for p in base.glob('Gentzen*.lean') if subprocess.run(['git','cat-file','-e','2f66237:'+str(p.relative_to(root))],cwd=root,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode)
assert len(mods)==19,len(mods)
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
namespace BlockedRightConjChecks
'''
for file,name,ns,call in [('GentzenBlockedRightGammaConj','gammaParent_source','BlockedRightConj','f g'),('GentzenBlockedRightGammaConj','gamma_equation','BlockedRightConj','f g h z'),('GentzenBlockedRightGammaConjRank','gamma_first_descent','BlockedRightConj','f g h z hc'),('GentzenBlockedRightGammaConjRank','gamma_second_descent','BlockedRightConj','f g h z hc'),('GentzenBlockedRightGammaConjRank','blockedR_gammaConj_rank_step','CutCommutation','f g h z hc ih')]:
 s=(base/(file+'.lean')).read_text();m=re.search(r'^theorem '+name+r'\s([\s\S]*?) := by\n',s,re.M);assert m,name
 checks+='\nsection\nopen BlockedRightConj\nexample {P : Type u} '+m[1]+' :=\n  '+ns+'.'+name+' '+call+'\nend\n'
checks+='''
def literalChild (l : Literal Nat) : G Nat [.lit l] [.lit l,.lit l] :=
  G.thinR [.lit l] [.lit l] [] (.lit l) (G.identity l)

theorem literalChildCut (l : Literal Nat) : PositionalCut.Eliminated
    (literalChild l) (.there (.here (.lit l) [])) (G.identity l) (.here (.lit l) []) :=
  PositionalCut.thin_endomorphism (Γ:=[.lit l]) (Δ:=[.lit l]) (Λ:=[]) (.lit l)
    (G.identity l) (G.identity l) rfl True.intro True.intro

def constantChild : G Empty [] [.top,.top] := G.thinR [] [.top] [] .top G.topI

theorem constantChildCut : PositionalCut.Eliminated (P:=Empty)
    constantChild (.there (.here .top [])) G.topIdentity (.here .top []) :=
  PositionalCut.thin_thin [] [.top] [] [] [] [.top] .top G.topI G.topI rfl rfl True.intro True.intro

def twoTops : G Empty [.top] [.top,.top] := G.thinR [.top] [] [.top] .top G.topIdentity

def topPair : G Empty [.top,.top] [.top,.top] := G.thinL [] [.top] [.top,.top] .top twoTops

def threeTops : G Empty [.top,.top] [.top,.top,.top] :=
  G.thinR [.top,.top] [.top] [.top] .top topPair

def fourTops : G Empty [.top,.top] [.top,.top,.top,.top] :=
  G.thinR [.top,.top] [.top,.top] [.top] .top threeTops

theorem populatedChildCut : PositionalCut.Eliminated fourTops (.there (.there (.here .top [.top])))
    topPair (.here .top [.top]) :=
  PositionalCut.thin_thin [.top,.top] [.top,.top] [.top] [] [.top] [.top,.top] .top threeTops twoTops
    rfl rfl (by repeat constructor) (by repeat constructor)

example (l : Literal Nat) : PositionalCut.Eliminated
    (BlockedRightConj.gammaParent (X:=[]) (Y:=[]) (Z:=[]) (T:=[]) (literalChild l) (literalChild l))
    (At.there (B:=.conj (.lit l) (.lit l)) (BlockedMix.gammaBlock (.lit l) [] [] [] []).keep)
    (G.identity l) (.here (.lit l) []) :=
  CutCommutation.blockedR_gammaConj_eliminated (X:=[]) (Y:=[]) (Z:=[]) (T:=[])
    (literalChild l) (literalChild l) (G.identity l) (.here (.lit l) []) (literalChildCut l) (literalChildCut l)

example : PositionalCut.Eliminated
    (BlockedRightConj.gammaParent (X:=[]) (Y:=[]) (Z:=[]) (T:=[])
      (literalChild (.neg 0)) (literalChild (.neg 0)))
    (At.there (B:=.conj (.lit (.neg 0)) (.lit (.neg 0)))
      (BlockedMix.gammaBlock (.lit (.neg 0)) [] [] [] []).keep)
    (G.identity (.neg 0)) (.here (.lit (.neg 0)) []) :=
  CutCommutation.blockedR_gammaConj_eliminated (X:=[]) (Y:=[]) (Z:=[]) (T:=[])
    (literalChild (.neg 0)) (literalChild (.neg 0)) (G.identity (.neg 0)) (.here (.lit (.neg 0)) [])
    (literalChildCut (.neg 0)) (literalChildCut (.neg 0))

example : PositionalCut.Eliminated (P:=Empty)
    (BlockedRightConj.gammaParent (X:=[]) (Y:=[]) (Z:=[]) (T:=[]) constantChild constantChild)
    (At.there (B:=.conj .top .top) (BlockedMix.gammaBlock .top [] [] [] []).keep)
    G.topIdentity (.here .top []) :=
  CutCommutation.blockedR_gammaConj_eliminated (X:=[]) (Y:=[]) (Z:=[]) (T:=[])
    constantChild constantChild G.topIdentity (.here .top []) constantChildCut constantChildCut

example : PositionalCut.Eliminated
    (BlockedRightConj.gammaParent (X:=[.top]) (Y:=[.top]) (Z:=[.top]) (T:=[.top]) fourTops fourTops)
    (At.there (B:=.conj .top .top) (BlockedMix.gammaBlock .top [.top] [.top] [.top] [.top]).keep)
    topPair (.here .top [.top]) :=
  CutCommutation.blockedR_gammaConj_eliminated (X:=[.top]) (Y:=[.top]) (Z:=[.top]) (T:=[.top])
    fourTops fourTops topPair (.here .top [.top]) populatedChildCut populatedChildCut

example :
    ((BlockedRightConj.gammaBlock (.top : NormalForm Empty) .top (.conj .top .top) [] [] [] []).route.get
      (.here (.conj .top .top) [.conj .top .top,.conj .top .top])).index = 0 := by rfl

end BlockedRightConjChecks
'''
p=root/'Checks/Axioms.lean';s=p.read_text()
for ns,name in [('ContractionSplice','head_right_binary'),('DoubleConjSplice','equation'),('BlockedRightConj','canonical_equation'),('BlockedRightConj','headParent_equation'),('BlockedRightConj','gamma_equation'),('BlockedRightConj','gamma_first_descent'),('BlockedRightConj','gamma_second_descent'),('CutCommutation','blockedR_gammaConj_rank_step')]:
 line='#print axioms DosenPetric.Reduced.Gentzen.'+ns+'.'+name+'\n'
 if line not in s:s+=line
 checks+='\n'+line
p.write_text(s);(root/'Checks/BlockedRightConj.lean').write_text(checks)
print('Integrated',len(mods),'modules, exact original source/rank signatures and four actual witnesses')
