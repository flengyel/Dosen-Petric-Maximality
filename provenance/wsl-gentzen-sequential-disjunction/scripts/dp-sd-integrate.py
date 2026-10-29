import re
base=root/'DosenPetric'
mods=sorted(p for p in base.glob('Gentzen*.lean') if subprocess.run(['git','cat-file','-e','668fb50:'+str(p.relative_to(root))],cwd=root,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode)
assert len(mods)==12,len(mods)
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
namespace BlockedDisjunctionChecks
'''
for file,ns,name,call in [
 ('GentzenBlockedDisjunctionData','BlockedDisjunction','parent_source','f'),
 ('GentzenBlockedDisjunctionEquation','BlockedDisjunction','source_equation','f h z'),
 ('GentzenBlockedDisjunctionDescent','BlockedDisjunction','original_descent','f h z hc'),
 ('GentzenFreshDisjunctionRecursion','SequentialDisjunction','fresh_clean','k h z hk ak hh ah bh'),
 ('GentzenFreshDisjunctionRecursion','SequentialDisjunction','fresh_rank_lt','k h z old x hold'),
 ('GentzenBlockedDisjunctionRank','CutCommutation','blockedR_disjunction_rank_step','f h z hc ih')]:
 s=(base/(file+'.lean')).read_text();m=re.search(r'^theorem '+name+r'\s([\s\S]*?) := by\n',s,re.M);assert m,name
 checks+='\nsection\nopen '+('SequentialDisjunction' if ns=='SequentialDisjunction' else 'BlockedDisjunction')+'\nexample {P : Type u} '+m[1]+' :=\n  '+ns+'.'+name+' '+call+'\nend\n'
checks+='''
def bottomContext {P : Type u} : (D : List (NormalForm P)) → G P [.bot] D
  | [] => G.botE
  | A::D => G.headThinR A (bottomContext D)
theorem bottomContext_cf {P : Type u} (D : List (NormalForm P)) : (bottomContext D).CutFree := by
  induction D with
  | nil => rfl
  | cons A D ih => exact G.headThinR_cutFree A _ ih
theorem bottomContext_atomized {P : Type u} (D : List (NormalForm P)) : (bottomContext D).Atomized := by
  induction D with
  | nil => trivial
  | cons A D ih => exact G.headThinR_atomized A _ ih

theorem initial_eliminated {P : Type u} {C : NormalForm P} {D J : List (NormalForm P)}
    (g : G P [.bot] D) (a : At D C) (h : G P [C] J) :
    PositionalCut.Eliminated g a h (.here C []) := by
  refine ⟨bottomContext (J++a.erase),bottomContext_cf _,bottomContext_atomized _,?_⟩
  have he := ((disjDiagonal P).toUnit_unique
    (comp (rightIn .conj .bot) (ofTerm (bottomContext (J++a.erase)).denote))).trans
    ((disjDiagonal P).toUnit_unique
      (comp (rightIn .conj .bot) (ofTerm (PositionalCut.cut g a h (.here C [])).denote))).symm
  have hh := congrArg (fun k => comp (rightOut .conj .bot) k) he
  simpa only [← Laws.assoc,Laws.rightOut_In,Laws.id_comp] using hh

theorem literal_source (l : Literal Nat) (X Y : List (NormalForm Nat)) :
    PositionalCut.Eliminated
      (BlockedDisjunction.parent (X:=X) (Y:=Y)
        (bottomContext (.lit l::.lit l::(X++.disj (.lit l) (.lit l)::Y))))
      (BlockedDisjunction.block (.lit l) (.lit l) X Y).keep
      (G.identityNF (.disj (.lit l) (.lit l))) (.here _ []) :=
  initial_eliminated _ _ _
example : PositionalCut.Eliminated
    (BlockedDisjunction.parent (X:=[]) (Y:=[])
      (bottomContext [.lit (.neg 0),.lit (.neg 0),.disj (.lit (.neg 0)) (.lit (.neg 0))]))
    (BlockedDisjunction.block (.lit (.neg 0)) (.lit (.neg 0)) [] []).keep
    (G.identityNF (.disj (.lit (.neg 0)) (.lit (.neg 0)))) (.here _ []) :=
  literal_source (.neg 0) [] []
example : PositionalCut.Eliminated (P:=Empty)
    (BlockedDisjunction.parent (X:=[]) (Y:=[]) (bottomContext [.top,.bot,.disj .top .bot]))
    (BlockedDisjunction.block .top .bot [] []).keep
    (G.identityNF (.disj .top .bot)) (.here _ []) := initial_eliminated _ _ _
example : PositionalCut.Eliminated (P:=Empty)
    (BlockedDisjunction.parent (X:=[.disj .top .top]) (Y:=[.disj .top .top])
      (bottomContext [.top,.top,.disj .top .top,.disj .top .top,.disj .top .top]))
    (BlockedDisjunction.block .top .top [.disj .top .top] [.disj .top .top]).keep
    (G.identityNF (.disj .top .top)) (.here _ []) := initial_eliminated _ _ _

example : (SequentialRepair.headRoute (P:=Empty) [.top] [.top]).get
    (.here .top [.top,.top]) = .here .top [.top] := by rfl
example : (SequentialRepair.headRoute (P:=Empty) [.top] [.top]).get
    (.there (.here .top [.top])) = .here .top [.top] := by rfl
example : (BlockedDisjunction.block (.top : NormalForm Empty) .top [] []).route.get
    (.here (.disj .top .top) [.disj .top .top]) = (BlockedDisjunction.block .top .top [] []).keep := by rfl
end BlockedDisjunctionChecks
'''
p=root/'Checks/Axioms.lean';s=p.read_text()
for ns,name in [('SequentialDisjunction','native_equation'),('SequentialDisjunction','source_denote'),('SequentialDisjunction','fresh_rho'),('SequentialDisjunction','fresh_clean'),('SequentialDisjunction','fresh_rank_lt'),('BlockedDisjunction','source_equation'),('BlockedDisjunction','original_descent'),('CutCommutation','blockedR_disjunction_rank_step')]:
 line='#print axioms DosenPetric.Reduced.Gentzen.'+ns+'.'+name+'\n'
 if line not in s:s+=line
 checks+='\n'+line
p.write_text(s);(root/'Checks/BlockedDisjunction.lean').write_text(checks)
print('Integrated',len(mods),'modules, exact original source/rank signatures and four initial-output witnesses')
