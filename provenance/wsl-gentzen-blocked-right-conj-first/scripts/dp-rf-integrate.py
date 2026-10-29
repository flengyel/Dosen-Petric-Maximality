import re
base=root/'DosenPetric'
mods=sorted(p for p in base.glob('Gentzen*.lean') if subprocess.run(['git','cat-file','-e','1a89a84:'+str(p.relative_to(root))],cwd=root,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode)
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
namespace BlockedConjFirstChecks
'''
for file,ns,name,call in [
 ('GentzenSequentialConjFirstNative','SequentialConjFirst','native_equation','f g h'),
 ('GentzenBlockedConjFirstData','BlockedConjFirst','parent_source','f g'),
 ('GentzenBlockedConjFirstEquation','BlockedConjFirst','source_equation','f g h z'),
 ('GentzenBlockedConjFirstDescent','BlockedConjFirst','original_descent','f g h z hc'),
 ('GentzenBlockedConjFirstRank','BlockedConjFirst','fresh_clean_and_rank','f g h z hc k hk ak'),
 ('GentzenBlockedConjFirstRank','CutCommutation','blockedR_conjunctionFirst_rank_step','f g h z hc ih')]:
 s=(base/(file+'.lean')).read_text();m=re.search(r'^theorem '+name+r'\s([\s\S]*?) := by\n',s,re.M);assert m,name
 checks+='\nsection\nopen '+('SequentialConjFirst' if ns=='SequentialConjFirst' else 'BlockedConjFirst')+'\nexample {P : Type u} '+m[1]+' :=\n  '+ns+'.'+name+' '+call+'\nend\n'
checks+='''
def botOutput {P : Type u} : (D : List (NormalForm P)) → G P [.bot] D
  | [] => G.botE
  | E::D => G.headThinR E (botOutput D)
theorem botOutput_cf {P : Type u} (D : List (NormalForm P)) : (botOutput D).CutFree := by
  induction D with
  | nil => rfl
  | cons E D ih => exact G.headThinR_cutFree E _ ih
theorem botOutput_atomized {P : Type u} (D : List (NormalForm P)) : (botOutput D).Atomized := by
  induction D with
  | nil => trivial
  | cons E D ih => exact G.headThinR_atomized E _ ih

theorem initial_eliminated {P : Type u} {C : NormalForm P} {D J : List (NormalForm P)}
    (f : G P [.bot] D) (x : At D C) (h : G P [C] J) : PositionalCut.Eliminated f x h (.here C []) := by
  refine ⟨botOutput (J++x.erase),botOutput_cf _,botOutput_atomized _,?_⟩
  have he := ((disjDiagonal P).toUnit_unique
    (comp (rightIn .conj .bot) (ofTerm (botOutput (J++x.erase)).denote))).trans
    ((disjDiagonal P).toUnit_unique
      (comp (rightIn .conj .bot) (ofTerm (PositionalCut.cut f x h (.here C [])).denote))).symm
  have hh := congrArg (fun k => comp (rightOut .conj .bot) k) he
  simp only [← Laws.assoc,Laws.rightOut_In,Laws.id_comp] at hh
  exact hh

def topTail {P : Type u} : (U : List (NormalForm P)) → G P [] (.top::U)
  | [] => G.topI
  | E::U => G.thinR [] [.top] U E (topTail U)

theorem literal_source (l : Literal Nat) (X Y U : List (NormalForm Nat)) :
    PositionalCut.Eliminated
      (BlockedConjFirst.parent (Γ:=[.bot]) (Θ:=[]) (X:=X) (Y:=Y) (U:=U)
        (botOutput (.lit l::(X++.conj (.lit l) .top::Y))) (topTail U))
      (BlockedConjFirst.block (.lit l) .top X Y U).keep
      (G.identityNF (.conj (.lit l) .top)) (.here _ []) := initial_eliminated _ _ _
example : PositionalCut.Eliminated
    (BlockedConjFirst.parent (Γ:=[.bot]) (Θ:=[]) (X:=[]) (Y:=[]) (U:=[])
      (botOutput [.lit (.neg 0),.conj (.lit (.neg 0)) .top]) (topTail []))
    (BlockedConjFirst.block (.lit (.neg 0)) .top [] [] []).keep
    (G.identityNF (.conj (.lit (.neg 0)) .top)) (.here _ []) := literal_source (.neg 0) [] [] []
example : PositionalCut.Eliminated (P:=Empty)
    (BlockedConjFirst.parent (Γ:=[.bot]) (Θ:=[]) (X:=[]) (Y:=[]) (U:=[])
      (botOutput [.bot,.conj .bot .top]) (topTail []))
    (BlockedConjFirst.block .bot .top [] [] []).keep
    (G.identityNF (.conj .bot .top)) (.here _ []) := initial_eliminated _ _ _
example : PositionalCut.Eliminated (P:=Empty)
    (BlockedConjFirst.parent (Γ:=[.bot]) (Θ:=[]) (X:=[.conj .bot .top]) (Y:=[.conj .bot .top]) (U:=[.conj .bot .top])
      (botOutput [.bot,.conj .bot .top,.conj .bot .top,.conj .bot .top]) (topTail [.conj .bot .top]))
    (BlockedConjFirst.block .bot .top [.conj .bot .top] [.conj .bot .top] [.conj .bot .top]).keep
    (G.identityNF (.conj .bot .top)) (.here _ []) := initial_eliminated _ _ _
example : ((BlockedConjFirst.block (.bot : NormalForm Empty) .top [] [] [.conj .bot .top]).route.get
    (.there (.there (.here (.conj .bot .top) [])))).index = 1 := by rfl
end BlockedConjFirstChecks
'''
p=root/'Checks/Axioms.lean';s=p.read_text()
for ns,name in [('SequentialAdapters','right_equation'),('SequentialConjFirst','native_equation'),('BlockedConjFirst','source_equation'),('BlockedConjFirst','original_descent'),('BlockedConjFirst','fresh_clean_and_rank'),('CutCommutation','blockedR_conjunctionFirst_rank_step')]:
 line='#print axioms DosenPetric.Reduced.Gentzen.'+ns+'.'+name+'\n'
 if line not in s:s+=line
 checks+='\n'+line
p.write_text(s);(root/'Checks/BlockedConjFirst.lean').write_text(checks)
print('Integrated',len(mods),'modules, exact source/rank signatures and four initial-output smoke witnesses')
