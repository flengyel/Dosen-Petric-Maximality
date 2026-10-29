import re
base=root/'DosenPetric';mods=sorted(base.glob('GentzenConjSecond*.lean'))+[base/'GentzenFirstBlockExchange.lean']
p=root/'DosenPetric.lean';s=p.read_text()
for m in mods:
 line='public import DosenPetric.'+m.stem+'\n'
 if line not in s:s+=line
p.write_text(s)
checks="""module

import DosenPetric

set_option autoImplicit false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
open DosenPetric.Reduced.Gentzen.BinaryLogical
namespace ConjLeftSecondChecks
"""
src=(base/'GentzenConjSecondSelected.lean').read_text()
for name,ns,args in [
 ('conjRLeftSecond_equation','BinaryLogical','f g a h z'),
 ('conjRLeftSecond_count','BinaryLogical','f a k'),
 ('conjRLeftSecond_atomized','BinaryLogical','f a k'),
 ('conjRLeftSecond_congr','BinaryLogical',"f a k k' hk"),
 ('conjR_left_second_rank_step','CutCommutation','f g a h z hc ih')]:
 m=re.search(r'^theorem '+name+r'\s([\s\S]*?) := by\n',src,re.M);assert m,name
 checks+='\nexample {P : Type u} '+m[1]+' :=\n  '+ns+'.'+name+' '+args+'\n'
checks+="""
def retainedSecondNative {P : Type u} {Γ Θ Δ E T J : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A :: Δ)) (k : G P (T ++ Θ) (J ++ (B :: E))) :
    G P (T ++ (Γ ++ Θ)) (J ++ (.conj A B :: (Δ ++ E))) :=
  (HeadRouting.front J (Δ ++ E) (.conj A B)).inverse.right
    (((BinaryMix.swapBlocks Δ J E).consFixed (.conj A B)).right
      ((BinaryMix.swapBlocks Γ T Θ).left
        (G.conjR f ((HeadRouting.front J E B).right k))))

example {P : Type u} {Γ Θ Δ E T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: C :: E)) (h : G P (C :: T) J) :
    ofTerm (G.cut ((HeadRouting.front (.conj A B :: Δ) E C).right
      (G.conjR (Δ := Δ) (Λ := C :: E) f g)) h).denote =
      ofTerm (retainedSecondNative f (G.cut ((HeadRouting.front [B] E C).right g) h)).denote :=
  conjLeftSecondNative_equation f g h

def doubled (l : Literal Nat) : G Nat [.lit l] [.lit l,.lit l] :=
  G.thinR [.lit l] [.lit l] [] (.lit l) (G.identity l)

theorem literalChild (l : Literal Nat) : PositionalCut.Eliminated (doubled l)
    (.there (.here (.lit l) [])) (G.identity l) (.here (.lit l) []) :=
  PositionalCut.thin_endomorphism (Γ := [.lit l]) (Δ := [.lit l]) (Λ := []) (.lit l)
    (G.identity l) (G.identity l) rfl True.intro True.intro

example (l : Literal Nat) : PositionalCut.Eliminated
    (G.conjR (G.identity l) (doubled l)) (.there (.here (.lit l) []))
    (G.identity l) (.here (.lit l) []) :=
  CutCommutation.conjR_left_second_eliminated (G.identity l) (doubled l) (.here (.lit l) [])
    (G.identity l) (.here (.lit l) []) rfl True.intro (literalChild l)

example : PositionalCut.Eliminated
    (G.conjR (G.identity (.neg 0)) (doubled (.neg 0))) (.there (.here (.lit (.neg 0)) []))
    (G.identity (.neg 0)) (.here (.lit (.neg 0)) []) :=
  CutCommutation.conjR_left_second_eliminated (G.identity (.neg 0)) (doubled (.neg 0))
    (.here (.lit (.neg 0)) []) (G.identity (.neg 0)) (.here (.lit (.neg 0)) []) rfl True.intro (literalChild (.neg 0))

def constantG : G Empty [] [.top,.top] := G.thinR [] [.top] [] .top G.topI

theorem constantChild : PositionalCut.Eliminated constantG (.there (.here .top []))
    G.topIdentity (.here .top []) :=
  PositionalCut.thin_thin [] [.top] [] [] [] [.top] .top G.topI G.topI rfl rfl True.intro True.intro

example : PositionalCut.Eliminated (G.conjR G.topI constantG) (.there (.here .top []))
    G.topIdentity (.here .top []) :=
  CutCommutation.conjR_left_second_eliminated G.topI constantG (.here .top [])
    G.topIdentity (.here .top []) rfl True.intro constantChild

def twoTops : G Empty [.top] [.top,.top] := G.thinR [.top] [] [.top] .top G.topIdentity
def populatedG : G Empty [.top] [.top,.top,.top] := G.thinR [.top] [.top] [.top] .top twoTops
def populatedH : G Empty [.top,.top] [.top,.top] := G.thinL [] [.top] [.top,.top] .top twoTops

theorem populatedChild : PositionalCut.Eliminated populatedG (.there (.here .top [.top]))
    populatedH (.here .top [.top]) :=
  PositionalCut.thin_thin [.top] [.top] [.top] [] [.top] [.top,.top] .top twoTops twoTops
    rfl rfl ⟨True.intro,⟨True.intro,True.intro⟩⟩ ⟨True.intro,⟨True.intro,True.intro⟩⟩

example : PositionalCut.Eliminated (G.conjR twoTops populatedG) (.there (.there (.here .top [.top])))
    populatedH (.here .top [.top]) :=
  CutCommutation.conjR_left_second_eliminated twoTops populatedG (.here .top [.top])
    populatedH (.here .top [.top]) rfl ⟨True.intro,⟨True.intro,True.intro⟩⟩ populatedChild

-- The selected second-child tag is below another fixed residual output.
example (l : Literal Nat) :
    ofTerm (PositionalCut.cut
      (G.conjR (G.identity l) (G.thinR [.lit l] [.lit l] [.lit l] .top (doubled l)))
      (.there (.there (.here (.lit l) []))) (G.identity l) (.here (.lit l) [])).denote =
    ofTerm (conjRLeftSecond (G.identity l) (.there (.here (.lit l) []))
      (PositionalCut.cut (G.thinR [.lit l] [.lit l] [.lit l] .top (doubled l))
        (.there (.there (.here (.lit l) []))) (G.identity l) (.here (.lit l) []))).denote := by
  simpa only [At.shift] using conjRLeftSecond_equation
    (G.identity l) (G.thinR [.lit l] [.lit l] [.lit l] .top (doubled l))
    (.there (.here (.lit l) [])) (G.identity l) (.here (.lit l) [])

end ConjLeftSecondChecks
"""
p=root/'Checks/Axioms.lean';s=p.read_text()
for ns,name in [('BinaryLogical','selectedMixedSecond_swap'),('BinaryLogical','conjR_left_second_core'),('BinaryMix','swapBlocks_split'),('BinaryLogical','conjLeftSecondNative_equation'),('BinaryLogical','conjRLeftSecond_equation'),('CutCommutation','conjR_left_second_rank_step')]:
 line='#print axioms DosenPetric.Reduced.Gentzen.'+ns+'.'+name+'\n'
 if line not in s:s+=line
 checks+='\n#print axioms '+ns+'.'+name+'\n'
p.write_text(s);(root/'Checks/ConjLeftSecond.lean').write_text(checks)
print('Integrated',len(mods),'second-child production modules and exact/witness checks')
