import re
base=root/'DosenPetric'
mods=[*sorted(base.glob('GentzenConjFirst*.lean')),*sorted(base.glob('GentzenLastBlock*.lean'))]
p=root/'DosenPetric.lean';s=p.read_text()
for m in mods:
 line='public import DosenPetric.'+m.stem+'\n'
 if line not in s:s+=line
p.write_text(s)
checks='''module

import DosenPetric

set_option autoImplicit false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
open DosenPetric.Reduced.Gentzen.BinaryLogical
namespace ConjFirstChecks
'''
src=(base/'GentzenConjFirstSelected.lean').read_text()
for name,ns,args in [
 ('conjRRightFirst_equation','BinaryLogical','f g h z a'),
 ('conjRRightFirst_count','BinaryLogical','a g k'),
 ('conjRRightFirst_atomized','BinaryLogical','a g k'),
 ('conjRRightFirst_congr','BinaryLogical',"a g k k' hk"),
 ('conjR_right_first_rank_step','CutCommutation','f g h z a hc ih')]:
 m=re.search(r'^theorem '+name+r'\s([\s\S]*?) := by\n',src,re.M);assert m,name
 checks+='\nexample {P : Type u} '+m[1]+' :=\n  '+ns+'.'+name+' '+args+'\n'
checks+='''
-- This is the exact retained native candidate, with its original two exchanges.
def retainedFirstNative {P : Type u} {Γ Θ Δ Λ I D : List (NormalForm P)} {A B : NormalForm P}
    (k : G P (Γ ++ I) (A :: (Δ ++ D))) (g : G P Θ (B :: Λ)) :
    G P ((Γ ++ Θ) ++ I) ((.conj A B :: (Δ ++ Λ)) ++ D) :=
  ((ExchangeScript.exchange (.conj A B :: Δ) D Λ []).reindex
    (by simp only [List.append_nil,List.cons_append,List.append_assoc])
    (by simp only [List.append_nil,List.cons_append,List.append_assoc])).right
      (((ExchangeScript.exchange Γ I Θ []).reindex
        (by simp only [List.append_nil,List.append_assoc])
        (by simp only [List.append_nil,List.append_assoc])).left (G.conjR k g))

example {P : Type u} {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (C :: Γ) (A :: Δ)) (g : G P Θ (B :: Λ)) (h : G P I (C :: D)) :
    ofTerm (G.cut h (G.conjR f g)).denote =
      ofTerm (retainedFirstNative (G.cut h f) g).denote :=
  conjFirstNative_equation f g h

theorem literalChild (l : Literal Nat) : PositionalCut.Eliminated (G.identity l) (.here (.lit l) [])
    (G.identity l) (.here (.lit l) []) :=
  ⟨G.identity l,rfl,True.intro,(CutBase.identity_identity l).symm⟩

example (l : Literal Nat) : PositionalCut.Eliminated
    (G.identity l) (.here (.lit l) [])
    (G.conjR (G.identity l) (G.identity l)) (.here (.lit l) [.lit l]) :=
  CutCommutation.conjR_right_first_eliminated (G.identity l) (G.identity l)
    (G.identity l) (.here (.lit l) []) (.here (.lit l) []) rfl True.intro (literalChild l)

example : PositionalCut.Eliminated (P := Nat)
    (G.identity (.neg 0)) (.here (.lit (.neg 0)) [])
    (G.conjR (G.identity (.neg 0)) (G.identity (.neg 0))) (.here (.lit (.neg 0)) [.lit (.neg 0)]) :=
  CutCommutation.conjR_right_first_eliminated (G.identity (.neg 0)) (G.identity (.neg 0))
    (G.identity (.neg 0)) (.here (.lit (.neg 0)) []) (.here (.lit (.neg 0)) [])
    rfl True.intro (literalChild (.neg 0))

theorem emptyChild : PositionalCut.Eliminated (P := Empty) G.topI (.here .top [])
    G.topIdentity (.here .top []) :=
  PositionalCut.top_thin [] [] [.top] G.topI rfl True.intro

example : PositionalCut.Eliminated (P := Empty) G.topI (.here .top [])
    (G.conjR G.topIdentity G.topI) (.here .top []) :=
  CutCommutation.conjR_right_first_eliminated G.topIdentity G.topI G.topI
    (.here .top []) (.here .top []) rfl True.intro emptyChild

def twoTops : G Empty [.top] [.top,.top] := G.thinR [.top] [] [.top] .top G.topIdentity

theorem populatedChild : PositionalCut.Eliminated twoTops (.here .top [.top])
    G.topIdentity (.here .top []) :=
  PositionalCut.thin_thin [.top] [] [.top] [] [] [.top] .top G.topIdentity G.topI
    rfl rfl ⟨True.intro,True.intro⟩ True.intro

-- Both input exchange blocks and both output exchange blocks are nonempty.
example : PositionalCut.Eliminated twoTops (.here .top [.top])
    (G.conjR G.topIdentity twoTops) (.here .top [.top]) :=
  CutCommutation.conjR_right_first_eliminated G.topIdentity twoTops twoTops
    (.here .top [.top]) (.here .top []) rfl ⟨True.intro,⟨True.intro,True.intro⟩⟩ populatedChild

-- The original selected occurrence need not be at the child's head.
example (l : Literal Nat) :
    ofTerm (PositionalCut.cut (G.identity l) (.here (.lit l) [])
      (G.conjR (G.thinL [] [.lit l] [.lit l] .top (G.identity l)) (G.identity l))
        (.there (.here (.lit l) [.lit l]))).denote =
    ofTerm (conjRRightFirst (.there (.here (.lit l) [])) (G.identity l)
      (PositionalCut.cut (G.identity l) (.here (.lit l) [])
        (G.thinL [] [.lit l] [.lit l] .top (G.identity l)) (.there (.here (.lit l) [])))).denote := by
  simpa only [At.before,List.nil_append] using conjRRightFirst_equation
    (G.thinL [] [.lit l] [.lit l] .top (G.identity l)) (G.identity l) (G.identity l)
    (.here (.lit l) []) (.there (.here (.lit l) []))

end ConjFirstChecks
'''
p=root/'Checks/Axioms.lean';s=p.read_text()
for ns,name in [('BinaryLogical','product_left_splice'),('BinaryLogical','mixed_first_residual'),('BinaryLogical','conjFirstNative_equation'),('BinaryLogical','conjRRightFirst_equation'),('CutCommutation','conjR_right_first_rank_step')]:
 line='#print axioms DosenPetric.Reduced.Gentzen.'+ns+'.'+name+'\n'
 if line not in s:s+=line
 checks+='\n#print axioms '+ns+'.'+name+'\n'
p.write_text(s);(root/'Checks/ConjRightFirst.lean').write_text(checks)
print('Integrated',len(mods),'production modules and exact native/selected/witness checks')
