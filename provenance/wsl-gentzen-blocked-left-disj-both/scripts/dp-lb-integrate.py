import re
base=root/'DosenPetric'
mods=sorted(p for p in base.glob('Gentzen*.lean') if subprocess.run(['git','cat-file','-e','8a7ee15:'+str(p.relative_to(root))],cwd=root,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode)
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
namespace BlockedDisjBothChecks
'''
for file,ns,name,call in [
 ('GentzenSequentialDisjBothEquation','SequentialDisjBoth','native_equation','p q h f g'),
 ('GentzenBlockedDisjBothData','BlockedDisjBoth','parent_source','f g'),
 ('GentzenBlockedDisjBothEquation','BlockedDisjBoth','source_equation','f g h z'),
 ('GentzenBlockedDisjBothDescent','BlockedDisjBoth','first_descent','f g h z hc'),
 ('GentzenBlockedDisjBothDescent','BlockedDisjBoth','second_descent','f g h z hc'),
 ('GentzenBlockedDisjBothRank','BlockedDisjBoth','fresh_clean_and_rank','f g h z hc k l hk ak hl al'),
 ('GentzenBlockedDisjBothRank','CutCommutation','blockedL_disjunctionBoth_rank_step','f g h z hc ih')]:
 s=(base/(file+'.lean')).read_text();m=re.search(r'^theorem '+name+r'\s([\s\S]*?) := by\n',s,re.M);assert m,name
 checks+='\nsection\nopen BlockedDisjBoth SequentialDisjBoth\nexample {P : Type u} '+m[1]+' :=\n  '+ns+'.'+name+' '+call+'\nend\n'
old=Path('/tmp/dp-sq-integrate.py').read_text();a=old.index('def topContext');b=old.index('\ntheorem literal_source',a);checks+='\n'+old[a:b]
old=Path('/tmp/dp-lf-integrate.py').read_text();a=old.index('def botTail');b=old.index('\ntheorem literal_source',a);checks+='\n'+old[a:b]
checks+='''
theorem literal_source (l : Literal Nat) (X Y Z T : List (NormalForm Nat)) :
    PositionalCut.Eliminated (G.identityNF (.disj .bot (.lit l))) (.here _ [])
      (BlockedDisjBoth.parent (X:=X) (Y:=Y) (Z:=Z) (T:=T)
        (botTail (X++.disj .bot (.lit l)::Y))
        (topContext ((Z++.disj .bot (.lit l)::T)++[.lit l])))
      (BlockedDisjBoth.block .bot (.lit l) X Y Z T).keep := terminal_eliminated _ _ _
example : PositionalCut.Eliminated (G.identityNF (.disj .bot (.lit (.neg 0)))) (.here _ [])
    (BlockedDisjBoth.parent (X:=[]) (Y:=[]) (Z:=[]) (T:=[]) (botTail [.disj .bot (.lit (.neg 0))])
      (topContext [.disj .bot (.lit (.neg 0)),.lit (.neg 0)]))
    (BlockedDisjBoth.block .bot (.lit (.neg 0)) [] [] [] []).keep := literal_source (.neg 0) [] [] [] []
example : PositionalCut.Eliminated (P:=Empty) (G.identityNF (.disj .bot .top)) (.here _ [])
    (BlockedDisjBoth.parent (X:=[]) (Y:=[]) (Z:=[]) (T:=[]) (botTail [.disj .bot .top])
      (topContext [.disj .bot .top,.top]))
    (BlockedDisjBoth.block .bot .top [] [] [] []).keep := terminal_eliminated _ _ _
example : PositionalCut.Eliminated (P:=Empty) (G.identityNF (.disj .bot .top)) (.here _ [])
    (BlockedDisjBoth.parent (X:=[.disj .bot .top]) (Y:=[.disj .bot .top])
      (Z:=[.disj .bot .top]) (T:=[.disj .bot .top])
      (botTail [.disj .bot .top,.disj .bot .top,.disj .bot .top])
      (topContext [.disj .bot .top,.disj .bot .top,.disj .bot .top,.top]))
    (BlockedDisjBoth.block .bot .top [.disj .bot .top] [.disj .bot .top]
      [.disj .bot .top] [.disj .bot .top]).keep := terminal_eliminated _ _ _
example : ((BlockedDisjBoth.block (.bot : NormalForm Empty) .top [.disj .bot .top] [] [] []).route.get
    (.here (.disj .bot .top) [.disj .bot .top,.disj .bot .top,.disj .bot .top])).index = 0 := by rfl
example (C : NormalForm Empty) :
    (BlockedSource.selected3_indices C [C] [C,C] [C] []).map (fun n => n) = [1,4,6] := by rfl
end BlockedDisjBothChecks
'''
# The explicit index computation uses the actual selectedCopies value.
checks=checks.replace('(BlockedSource.selected3_indices C [C] [C,C] [C] []).map (fun n => n)', '(selectedCopies C [[C],[C,C],[C]] []).map At.index')
p=root/'Checks/Axioms.lean';s=p.read_text()
for ns,name in [('SequentialDisjBoth','native_equation'),('SequentialDisjBoth','source_denote'),('BlockedDisjBoth','source_equation'),('BlockedDisjBoth','first_descent'),('BlockedDisjBoth','second_descent'),('BlockedDisjBoth','fresh_clean_and_rank'),('CutCommutation','blockedL_disjunctionBoth_rank_step')]:
 line='#print axioms DosenPetric.Reduced.Gentzen.'+ns+'.'+name+'\n'
 if line not in s:s+=line
 checks+='\n'+line
p.write_text(s);(root/'Checks/BlockedDisjBoth.lean').write_text(checks)
print('Integrated',len(mods),'modules, exact three-copy signatures and four actual witnesses')
