import re
base=root/'DosenPetric'
mods=sorted(p for p in base.glob('Gentzen*.lean') if subprocess.run(['git','cat-file','-e','263c452:'+str(p.relative_to(root))],cwd=root,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode)
assert len(mods)==8,len(mods)
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
open PositionalCut
namespace GlobalCutEliminationChecks
example {P : Type u} : CutElimination P := cut_elimination
example {P : Type u} : AtomizedCutElimination P := atomized_cut_elimination
example {P : Type u} {Γ Δ : List (NormalForm P)} (t : G P Γ Δ) :
    ∃ h : G P Γ Δ, h.CutFree ∧ h.Atomized ∧ ofTerm h.denote = ofTerm t.denote :=
  atomized_cut_elimination t
'''
names=[('GentzenBlockedRankDispatch','CutCommutation','blocked_right_rank_step','f x g y hb hx hc ih'),('GentzenBlockedLeftRankDispatch','CutCommutation','blocked_left_rank_step','h z g x hb hx hc ih'),('GentzenParametricRightDispatch','CutCommutation','parametric_right_rank_step','f x g y hp hc ih'),('GentzenParametricLeftDispatch','CutCommutation','parametric_left_rank_step','h z g x hp hc ih'),('GentzenCleanRankInduction','PositionalCut','clean_rank_step','hd f x g y hc ih'),('GentzenCleanRankInduction','PositionalCut','clean_elimination','hd f x g y hc'),('GentzenCleanRankInduction','PositionalCut','cutFree_degree_step','hd f x g y hf hg'),('GentzenDegreeInduction','','head_cut_elimination','C f g hf hg'),('GentzenDegreeInduction','PositionalCut','cutFree_elimination','f x g y hf hg')]
for file,ns,name,call in names:
 s=(base/(file+'.lean')).read_text();m=re.search(r'^theorem '+name+r'\s([\s\S]*?) := by\n',s,re.M);assert m,name
 checks+='\nexample {P : Type u} '+m[1]+' :=\n  '+(ns+'.' if ns else '')+name+' '+call+'\n'
checks+='''
/-- These witnesses use the actual global eliminator, including a cut below thinning. -/
example {P : Type u} (l : Literal P) :
    ∃ h : G P [.lit l] [.lit l], h.CutFree ∧ h.Atomized ∧
      ofTerm h.denote = ofTerm (G.cut (G.identity l) (G.zero l)).denote :=
  atomized_cut_elimination (G.cut (G.identity l) (G.zero l))
example : ∃ h : G Empty [.bot] [.top,.top], h.CutFree ∧ h.Atomized ∧
    ofTerm h.denote = ofTerm (G.thinR [.bot] [] [.top] .top
      (G.cut (G.thinR [.bot] [] [] .top G.botE) (G.identityNF .top))).denote :=
  atomized_cut_elimination _
example : ∃ h : G Nat [.lit (.neg 0)] [.conj (.lit (.neg 0)) .top],
    h.CutFree ∧ h.Atomized ∧ ofTerm h.denote = ofTerm
      (G.cut (G.conjR (G.identity (.neg 0)) G.topI)
        (G.identityNF (.conj (.lit (.neg 0)) .top))).denote :=
  atomized_cut_elimination _
example {P : Type u} {Γ Δ : List (NormalForm P)} (t : G P Γ Δ) :
    ∃ h : G P (Γ++Γ) (Δ++Δ), h.CutFree ∧ h.Atomized ∧
      ofTerm h.denote = ofTerm (G.mix t t).denote := atomized_cut_elimination _
example : cutDegree (.top : NormalForm Empty) = 1 := rfl
example : cutDegree (.bot : NormalForm Empty) = 1 := rfl
example (l : Literal Nat) : cutDegree (.lit l) = 0 := rfl
end GlobalCutEliminationChecks
'''
axioms=[(ns,name) for _,ns,name,_ in names]+[('G','cut_free_normalization'),('','cut_elimination'),('','atomized_cut_elimination')]
p=root/'Checks/Axioms.lean';s=p.read_text()
for ns,name in axioms:
 line='#print axioms DosenPetric.Reduced.Gentzen.'+(ns+'.' if ns else '')+name+'\n'
 if line not in s:s+=line
 checks+='\n'+line
p.write_text(s);(root/'Checks/GlobalCutElimination.lean').write_text(checks)
print('Integrated eight production modules, exact general signatures and actual global witnesses')
