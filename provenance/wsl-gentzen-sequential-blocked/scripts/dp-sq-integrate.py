import re
base=root/'DosenPetric'
mods=sorted(p for p in base.glob('Gentzen*.lean') if subprocess.run(['git','cat-file','-e','787ee6c:'+str(p.relative_to(root))],cwd=root,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode)
assert len(mods)==14,len(mods)
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
namespace BlockedConjunctionChecks
'''
for file,ns,name,call in [
 ('GentzenBlockedConjunctionData','BlockedConjunction','parent_source','f'),
 ('GentzenBlockedConjunctionEquation','BlockedConjunction','source_equation','f h z'),
 ('GentzenBlockedConjunctionDescent','BlockedConjunction','original_descent','f h z hc'),
 ('GentzenBlockedConjunctionDescent','BlockedConjunction','fresh_clean_and_rank','f h z hc k hk ak'),
 ('GentzenBlockedConjunctionRank','CutCommutation','blockedL_conjunction_rank_step','f h z hc ih')]:
 s=(base/(file+'.lean')).read_text();m=re.search(r'^theorem '+name+r'\s([\s\S]*?) := by\n',s,re.M);assert m,name
 checks+='\nsection\nopen BlockedConjunction\nexample {P : Type u} '+m[1]+' :=\n  '+ns+'.'+name+' '+call+'\nend\n'
checks+='''
def topContext {P : Type u} : (F : List (NormalForm P)) → G P F [.top]
  | [] => G.topI
  | A::F => G.headThinL A (topContext F)
theorem topContext_cf {P : Type u} (F : List (NormalForm P)) : (topContext F).CutFree := by
  induction F with
  | nil => rfl
  | cons A F ih => exact G.headThinL_cutFree A _ ih
theorem topContext_atomized {P : Type u} (F : List (NormalForm P)) : (topContext F).Atomized := by
  induction F with
  | nil => trivial
  | cons A F ih => exact G.headThinL_atomized A _ ih

theorem terminal_eliminated {P : Type u} {C : NormalForm P} {F I : List (NormalForm P)}
    (h : G P I [C]) (g : G P F [.top]) (a : At F C) :
    PositionalCut.Eliminated h (.here C []) g a := by
  refine ⟨topContext (a.erase++I),topContext_cf _,topContext_atomized _,?_⟩
  have he := ((conjDiagonal P).toUnit_unique
    (comp (ofTerm (topContext (a.erase++I)).denote) (rightOut .disj .top))).trans
    ((conjDiagonal P).toUnit_unique
      (comp (ofTerm (PositionalCut.cut h (.here C []) g a).denote) (rightOut .disj .top))).symm
  have hh := congrArg (fun k => comp k (rightIn .disj .top)) he
  simp only [Laws.assoc,Laws.rightOut_In,Laws.comp_id] at hh
  exact hh.trans (Laws.comp_id _)

theorem literal_source (l : Literal Nat) (X Y : List (NormalForm Nat)) :
    PositionalCut.Eliminated (G.identityNF (.conj (.lit l) (.lit l))) (.here _ [])
      (BlockedConjunction.parent (X:=X) (Y:=Y)
        (topContext ((X++.conj (.lit l) (.lit l)::Y)++[.lit l,.lit l])))
      (BlockedConjunction.block (.lit l) (.lit l) X Y).keep :=
  terminal_eliminated _ _ _
example : PositionalCut.Eliminated (G.identityNF (.conj (.lit (.neg 0)) (.lit (.neg 0)))) (.here _ [])
    (BlockedConjunction.parent (X:=[]) (Y:=[])
      (topContext [.conj (.lit (.neg 0)) (.lit (.neg 0)),.lit (.neg 0),.lit (.neg 0)]))
    (BlockedConjunction.block (.lit (.neg 0)) (.lit (.neg 0)) [] []).keep :=
  literal_source (.neg 0) [] []
example : PositionalCut.Eliminated (P:=Empty) (G.identityNF (.conj .top .bot)) (.here _ [])
    (BlockedConjunction.parent (X:=[]) (Y:=[]) (topContext [.conj .top .bot,.top,.bot]))
    (BlockedConjunction.block .top .bot [] []).keep := terminal_eliminated _ _ _
example : PositionalCut.Eliminated (P:=Empty) (G.identityNF (.conj .top .top)) (.here _ [])
    (BlockedConjunction.parent (X:=[.conj .top .top]) (Y:=[.conj .top .top])
      (topContext [.conj .top .top,.conj .top .top,.conj .top .top,.top,.top]))
    (BlockedConjunction.block .top .top [.conj .top .top] [.conj .top .top]).keep :=
  terminal_eliminated _ _ _

example : (SequentialRepair.headBlock (.conj .top .top : NormalForm Empty) []).route.get
    (.here _ [.conj .top .top]) = .here _ [] := by rfl
example : (SequentialRepair.headBlock (.conj .top .top : NormalForm Empty) []).route.get
    (.there (.here _ [])) = .here _ [] := by rfl
example : (SequentialRepair.tailRoute (P:=Empty) [.top] [.top]).get
    (.there (.there (.here .top []))) = .there (.here .top []) := by rfl
end BlockedConjunctionChecks
'''
p=root/'Checks/Axioms.lean';s=p.read_text()
for ns,name in [('SequentialConjunction','native_equation'),('SequentialConjunction','source_denote'),('BlockedConjunction','source_equation'),('BlockedConjunction','original_descent'),('BlockedConjunction','fresh_clean_and_rank'),('CutCommutation','blockedL_conjunction_rank_step')]:
 line='#print axioms DosenPetric.Reduced.Gentzen.'+ns+'.'+name+'\n'
 if line not in s:s+=line
 checks+='\n'+line
p.write_text(s);(root/'Checks/BlockedConjunction.lean').write_text(checks)
print('Integrated',len(mods),'modules; exact signatures, four actual terminal-output witnesses and coordinate controls')
