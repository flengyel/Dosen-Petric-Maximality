import re
base=root/'DosenPetric';mods=sorted(base.glob('GentzenConjLeft*.lean'))
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
namespace ConjLeftFirstChecks
'''
src=(base/'GentzenConjLeftSelected.lean').read_text()
for name,ns,args in [
 ('conjRLeftFirst_equation','BinaryLogical','f g a h z'),
 ('conjRLeftFirst_count','BinaryLogical','a g k'),
 ('conjRLeftFirst_atomized','BinaryLogical','a g k'),
 ('conjRLeftFirst_congr','BinaryLogical',"a g k k' hk"),
 ('conjR_left_first_rank_step','CutCommutation','f g a h z hc ih')]:
 m=re.search(r'^theorem '+name+r'\s([\s\S]*?) := by\n',src,re.M);assert m,name
 checks+='\nexample {P : Type u} '+m[1]+' :=\n  '+ns+'.'+name+' '+args+'\n'
checks+='''
def doubled (l : Literal Nat) : G Nat [.lit l] [.lit l,.lit l] :=
  G.thinR [.lit l] [.lit l] [] (.lit l) (G.identity l)

theorem literalChild (l : Literal Nat) : PositionalCut.Eliminated (doubled l)
    (.there (.here (.lit l) [])) (G.identity l) (.here (.lit l) []) :=
  PositionalCut.thin_endomorphism (Γ := [.lit l]) (Δ := [.lit l]) (Λ := []) (.lit l) (G.identity l) (G.identity l) rfl True.intro True.intro

example (l : Literal Nat) : PositionalCut.Eliminated
    (G.conjR (doubled l) (G.identity l)) (.there (.here (.lit l) []))
    (G.identity l) (.here (.lit l) []) :=
  CutCommutation.conjR_left_first_eliminated (doubled l) (G.identity l) (.here (.lit l) [])
    (G.identity l) (.here (.lit l) []) rfl True.intro (literalChild l)

example : PositionalCut.Eliminated
    (G.conjR (doubled (.neg 0)) (G.identity (.neg 0))) (.there (.here (.lit (.neg 0)) []))
    (G.identity (.neg 0)) (.here (.lit (.neg 0)) []) :=
  CutCommutation.conjR_left_first_eliminated (doubled (.neg 0)) (G.identity (.neg 0))
    (.here (.lit (.neg 0)) []) (G.identity (.neg 0)) (.here (.lit (.neg 0)) []) rfl True.intro (literalChild (.neg 0))

def constantF : G Empty [] [.top,.top] := G.thinR [] [.top] [] .top G.topI

theorem constantChild : PositionalCut.Eliminated constantF (.there (.here .top []))
    G.topIdentity (.here .top []) :=
  PositionalCut.thin_thin [] [.top] [] [] [] [.top] .top G.topI G.topI rfl rfl True.intro True.intro

example : PositionalCut.Eliminated (G.conjR constantF G.topI) (.there (.here .top []))
    G.topIdentity (.here .top []) :=
  CutCommutation.conjR_left_first_eliminated constantF G.topI (.here .top [])
    G.topIdentity (.here .top []) rfl True.intro constantChild

def twoTops : G Empty [.top] [.top,.top] := G.thinR [.top] [] [.top] .top G.topIdentity
def populatedF : G Empty [.top] [.top,.top,.top] := G.thinR [.top] [.top] [.top] .top twoTops
def populatedH : G Empty [.top,.top] [.top,.top] := G.thinL [] [.top] [.top,.top] .top twoTops

theorem populatedChild : PositionalCut.Eliminated populatedF (.there (.here .top [.top]))
    populatedH (.here .top [.top]) :=
  PositionalCut.thin_thin [.top] [.top] [.top] [] [.top] [.top,.top] .top twoTops twoTops
    rfl rfl ⟨True.intro,⟨True.intro,True.intro⟩⟩ ⟨True.intro,⟨True.intro,True.intro⟩⟩

example : PositionalCut.Eliminated (G.conjR populatedF twoTops) (.there (.here .top [.top,.top]))
    populatedH (.here .top [.top]) :=
  CutCommutation.conjR_left_first_eliminated populatedF twoTops (.here .top [.top])
    populatedH (.here .top [.top]) rfl ⟨True.intro,⟨True.intro,True.intro⟩⟩ populatedChild

-- A fixed output lies between the retained principal and selected occurrence.
example (l : Literal Nat) :
    ofTerm (PositionalCut.cut
      (G.conjR (G.thinR [.lit l] [.lit l] [.lit l] .top (doubled l)) (G.identity l))
      (.there (.there (.here (.lit l) []))) (G.identity l) (.here (.lit l) [])).denote =
    ofTerm (conjRLeftFirst (.there (.here (.lit l) [])) (G.identity l)
      (PositionalCut.cut (G.thinR [.lit l] [.lit l] [.lit l] .top (doubled l))
        (.there (.there (.here (.lit l) []))) (G.identity l) (.here (.lit l) []))).denote := by
  simpa only [At.before,List.append_nil,List.nil_append] using conjRLeftFirst_equation
    (G.thinR [.lit l] [.lit l] [.lit l] .top (doubled l)) (G.identity l)
    (.there (.here (.lit l) [])) (G.identity l) (.here (.lit l) [])

example {P : Type u} {Γ Θ D Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: C :: D)) (g : G P Θ (B :: Λ)) (h : G P (C :: T) J) :
    ofTerm (G.cut ((HeadRouting.front [.conj A B] (D ++ Λ) C).right
      (G.conjR (Δ := C :: D) (Λ := Λ) f g)) h).denote =
      ofTerm (conjLeftFirstNative (G.cut ((HeadRouting.front [A] D C).right f) h) g).denote :=
  conjLeftFirstNative_equation f g h

end ConjLeftFirstChecks
'''
p=root/'Checks/Axioms.lean';s=p.read_text()
for ns,name in [('BinaryLogical','splice_distRight'),('BinaryLogical','selectedMixed_eq'),('BinaryLogical','conjR_left_first_core'),('BinaryLogical','conjLeftFirstNative_equation'),('BinaryLogical','conjRLeftFirst_equation'),('CutCommutation','conjR_left_first_rank_step')]:
 line='#print axioms DosenPetric.Reduced.Gentzen.'+ns+'.'+name+'\n'
 if line not in s:s+=line
 checks+='\n#print axioms '+ns+'.'+name+'\n'
p.write_text(s);(root/'Checks/ConjLeftFirst.lean').write_text(checks)
print('Integrated',len(mods),'left-first production modules and actual exact/witness checks')
