import re
base=root/'DosenPetric'
mods=sorted(p for p in base.glob('Gentzen*.lean') if subprocess.run(['git','cat-file','-e','0cef4a4:'+str(p.relative_to(root))],cwd=root,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode)
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
namespace BlockedDisjFirstChecks
'''
for file,ns,name,call in [
 ('GentzenBlockedDisjFirstData','BlockedDisjFirst','parent_source','f g'),
 ('GentzenBlockedDisjFirstEquation','BlockedDisjFirst','source_equation','f g h z'),
 ('GentzenBlockedDisjFirstDescent','BlockedDisjFirst','original_descent','f g h z hc'),
 ('GentzenBlockedDisjFirstRank','BlockedDisjFirst','fresh_clean_and_rank','f g h z hc k hk ak'),
 ('GentzenAppendixCFreshRight','BlockedDisjFirst','fresh_principal_rank','g k'),
 ('GentzenAppendixCFreshRight','BlockedDisjFirst','fresh_total_rank','g h z k'),
 ('GentzenAppendixCFreshRight','BlockedDisjFirst','fresh_total_rank_ge_two','g h z k'),
 ('GentzenBlockedDisjFirstRank','CutCommutation','blockedL_disjunctionFirst_rank_step','f g h z hc ih')]:
 s=(base/(file+'.lean')).read_text();m=re.search(r'^theorem '+name+r'\s([\s\S]*?) :=(?: by)?\n',s,re.M);assert m,name
 checks+='\nsection\nopen BlockedDisjFirst\nexample {P : Type u} '+m[1]+' :=\n  '+ns+'.'+name+' '+call+'\nend\n'
old=Path('/tmp/dp-sq-integrate.py').read_text();a=old.index('def topContext');b=old.index('\ntheorem literal_source',a)
checks+='\n'+old[a:b]
checks+='''
def botTail {P : Type u} : (Z : List (NormalForm P)) → G P (Z++[.bot]) []
  | [] => G.botE
  | A::Z => G.headThinL A (botTail Z)
theorem botTail_cf {P : Type u} (Z : List (NormalForm P)) : (botTail Z).CutFree := by
  induction Z with
  | nil => rfl
  | cons A Z ih => exact G.headThinL_cutFree A _ ih
theorem botTail_atomized {P : Type u} (Z : List (NormalForm P)) : (botTail Z).Atomized := by
  induction Z with
  | nil => trivial
  | cons A Z ih => exact G.headThinL_atomized A _ ih

theorem literal_source (l : Literal Nat) (X Y Z : List (NormalForm Nat)) :
    PositionalCut.Eliminated (G.identityNF (.disj (.lit l) .bot)) (.here _ [])
      (BlockedDisjFirst.parent (X:=X) (Y:=Y) (Z:=Z)
        (topContext ((X++.disj (.lit l) .bot::Y)++[.lit l])) (botTail Z))
      (BlockedDisjFirst.block (.lit l) .bot X Y Z).keep :=
  terminal_eliminated _ _ _
example : PositionalCut.Eliminated (G.identityNF (.disj (.lit (.neg 0)) .bot)) (.here _ [])
    (BlockedDisjFirst.parent (X:=[]) (Y:=[]) (Z:=[])
      (topContext [.disj (.lit (.neg 0)) .bot,.lit (.neg 0)]) (botTail []))
    (BlockedDisjFirst.block (.lit (.neg 0)) .bot [] [] []).keep :=
  literal_source (.neg 0) [] [] []
example : PositionalCut.Eliminated (P:=Empty) (G.identityNF (.disj .top .bot)) (.here _ [])
    (BlockedDisjFirst.parent (X:=[]) (Y:=[]) (Z:=[]) (topContext [.disj .top .bot,.top]) (botTail []))
    (BlockedDisjFirst.block .top .bot [] [] []).keep := terminal_eliminated _ _ _
example : PositionalCut.Eliminated (P:=Empty) (G.identityNF (.disj .top .bot)) (.here _ [])
    (BlockedDisjFirst.parent (X:=[.disj .top .bot]) (Y:=[.disj .top .bot]) (Z:=[.disj .top .bot])
      (topContext [.disj .top .bot,.disj .top .bot,.disj .top .bot,.top]) (botTail [.disj .top .bot]))
    (BlockedDisjFirst.block .top .bot [.disj .top .bot] [.disj .top .bot] [.disj .top .bot]).keep :=
  terminal_eliminated _ _ _
example : (BlockedSource.disjLLast (Γ:=[]) (Θ:=[]) (G.topIdentity (P:=Empty)) G.topIdentity).rho
    .left (.here (.disj .top .top) []) = 2 :=
  BlockedSource.disjLLast_rank_principal _ _
example : (G.disjL (G.topIdentity (P:=Empty)) G.topIdentity).rho
    .left (.here (.disj .top .top) []) = 1 := G.rho_disjL_principal _ _
end BlockedDisjFirstChecks
'''
p=root/'Checks/Axioms.lean';s=p.read_text()
for ns,name in [('SequentialDisjFirst','native_equation'),('BlockedDisjFirst','source_equation'),('BlockedDisjFirst','original_descent'),('BlockedDisjFirst','fresh_clean_and_rank'),('BlockedDisjFirst','fresh_principal_rank'),('BlockedDisjFirst','fresh_total_rank'),('BlockedDisjFirst','fresh_total_rank_ge_two'),('CutCommutation','blockedL_disjunctionFirst_rank_step')]:
 line='#print axioms DosenPetric.Reduced.Gentzen.'+ns+'.'+name+'\n'
 if line not in s:s+=line
 checks+='\n'+line
p.write_text(s);(root/'Checks/BlockedDisjFirst.lean').write_text(checks)
print('Integrated',len(mods),'modules, exact original source/rank/Appendix C signatures and four actual witnesses')
