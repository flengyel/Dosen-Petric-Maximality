import re
base=root/'DosenPetric'
mods=sorted(p for p in base.glob('Gentzen*.lean') if subprocess.run(['git','cat-file','-e','d59cb83:'+str(p.relative_to(root))],cwd=root,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode)
assert len(mods)==6,len(mods)
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
namespace BlockedDisjSecondChecks
'''
for file,ns,name,call in [
 ('GentzenBlockedDisjSecondData','BlockedDisjSecond','parent_source','f g'),
 ('GentzenBlockedDisjSecondEquation','BlockedDisjSecond','source_equation','f g h z'),
 ('GentzenBlockedDisjSecondDescent','BlockedDisjSecond','original_descent','f g h z hc'),
 ('GentzenBlockedDisjSecondRank','BlockedDisjSecond','fresh_clean_and_rank','f g h z hc k hk ak'),
 ('GentzenBlockedDisjSecondRank','CutCommutation','blockedL_disjunctionSecond_rank_step','f g h z hc ih')]:
 s=(base/(file+'.lean')).read_text();m=re.search(r'^theorem '+name+r'\s([\s\S]*?) := by\n',s,re.M);assert m,name
 checks+='\nsection\nopen BlockedDisjSecond\nexample {P : Type u} '+m[1]+' :=\n  '+ns+'.'+name+' '+call+'\nend\n'
old=Path('/tmp/dp-sq-integrate.py').read_text();a=old.index('def topContext');b=old.index('\ntheorem literal_source',a);checks+='\n'+old[a:b]
old=Path('/tmp/dp-lf-integrate.py').read_text();a=old.index('def botTail');b=old.index('\ntheorem literal_source',a);checks+='\n'+old[a:b]
checks+='''
theorem literal_source (l : Literal Nat) (X Z T : List (NormalForm Nat)) :
    PositionalCut.Eliminated (G.identityNF (.disj .bot (.lit l))) (.here _ [])
      (BlockedDisjSecond.parent (X:=X) (Z:=Z) (T:=T) (botTail X)
        (topContext ((Z++.disj .bot (.lit l)::T)++[.lit l])))
      (BlockedDisjSecond.block .bot (.lit l) X Z T).keep := terminal_eliminated _ _ _
example : PositionalCut.Eliminated (G.identityNF (.disj .bot (.lit (.neg 0)))) (.here _ [])
    (BlockedDisjSecond.parent (X:=[]) (Z:=[]) (T:=[]) (botTail [])
      (topContext [.disj .bot (.lit (.neg 0)),.lit (.neg 0)]))
    (BlockedDisjSecond.block .bot (.lit (.neg 0)) [] [] []).keep := literal_source (.neg 0) [] [] []
example : PositionalCut.Eliminated (P:=Empty) (G.identityNF (.disj .bot .top)) (.here _ [])
    (BlockedDisjSecond.parent (X:=[]) (Z:=[]) (T:=[]) (botTail []) (topContext [.disj .bot .top,.top]))
    (BlockedDisjSecond.block .bot .top [] [] []).keep := terminal_eliminated _ _ _
example : PositionalCut.Eliminated (P:=Empty) (G.identityNF (.disj .bot .top)) (.here _ [])
    (BlockedDisjSecond.parent (X:=[.disj .bot .top]) (Z:=[.disj .bot .top]) (T:=[.disj .bot .top])
      (botTail [.disj .bot .top]) (topContext [.disj .bot .top,.disj .bot .top,.disj .bot .top,.top]))
    (BlockedDisjSecond.block .bot .top [.disj .bot .top] [.disj .bot .top] [.disj .bot .top]).keep :=
  terminal_eliminated _ _ _
example : ((BlockedDisjSecond.block (.bot : NormalForm Empty) .top [.disj .bot .top] [] []).route.get
    (.here (.disj .bot .top) [.disj .bot .top,.disj .bot .top])).index = 0 := by rfl
end BlockedDisjSecondChecks
'''
p=root/'Checks/Axioms.lean';s=p.read_text()
for ns,name in [('LogicalDeletion','headShift_cons_arrow'),('SequentialDisjSecond','native_equation'),('BlockedDisjSecond','source_equation'),('BlockedDisjSecond','original_descent'),('BlockedDisjSecond','fresh_clean_and_rank'),('CutCommutation','blockedL_disjunctionSecond_rank_step')]:
 line='#print axioms DosenPetric.Reduced.Gentzen.'+ns+'.'+name+'\n'
 if line not in s:s+=line
 checks+='\n'+line
p.write_text(s);(root/'Checks/BlockedDisjSecond.lean').write_text(checks)
print('Integrated',len(mods),'modules, exact second-child source/rank signatures and four actual witnesses')
