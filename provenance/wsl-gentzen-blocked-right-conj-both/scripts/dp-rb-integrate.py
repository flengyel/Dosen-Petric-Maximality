import re
base=root/'DosenPetric'
mods=sorted(p for p in base.glob('Gentzen*.lean') if subprocess.run(['git','cat-file','-e','19b3002:'+str(p.relative_to(root))],cwd=root,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode)
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
namespace BlockedConjBothChecks
'''
for file,ns,name,call in [
 ('GentzenSequentialConjBothNative','SequentialConjBoth','native_equation','p q f g h'),
 ('GentzenBlockedConjBothData','BlockedConjBoth','parent_source','f g'),
 ('GentzenBlockedConjBothEquation','BlockedConjBoth','source_equation','f g h z'),
 ('GentzenBlockedConjBothDescent','BlockedConjBoth','first_descent','f g h z hc'),
 ('GentzenBlockedConjBothDescent','BlockedConjBoth','second_descent','f g h z hc'),
 ('GentzenBlockedConjBothRank','BlockedConjBoth','fresh_clean_and_rank','f g h z hc k l hk ak hl al'),
 ('GentzenBlockedConjBothRank','CutCommutation','blockedR_conjunctionBoth_rank_step','f g h z hc ih')]:
 s=(base/(file+'.lean')).read_text();m=re.search(r'^theorem '+name+r'\s([\s\S]*?) := by\n',s,re.M);assert m,name
 checks+='\nsection\nopen '+('SequentialConjBoth' if ns=='SequentialConjBoth' else 'BlockedConjBoth')+'\nexample {P : Type u} '+m[1]+' :=\n  '+ns+'.'+name+' '+call+'\nend\n'
old=Path('/tmp/dp-rf-integrate.py').read_text();a=old.index('def botOutput');b=old.index('\ntheorem literal_source',a);checks+='\n'+old[a:b]
checks+='''
theorem literal_source (l : Literal Nat) (X Y Z T : List (NormalForm Nat)) :
    PositionalCut.Eliminated
      (BlockedConjBoth.parent (Γ:=[.bot]) (Θ:=[]) (X:=X) (Y:=Y) (Z:=Z) (T:=T)
        (botOutput (.lit l::(X++.conj (.lit l) .top::Y))) (topTail (Z++.conj (.lit l) .top::T)))
      (BlockedConjBoth.block (.lit l) .top X Y Z T).keep
      (G.identityNF (.conj (.lit l) .top)) (.here _ []) := initial_eliminated _ _ _
example : PositionalCut.Eliminated
    (BlockedConjBoth.parent (Γ:=[.bot]) (Θ:=[]) (X:=[]) (Y:=[]) (Z:=[]) (T:=[])
      (botOutput [.lit (.neg 0),.conj (.lit (.neg 0)) .top]) (topTail [.conj (.lit (.neg 0)) .top]))
    (BlockedConjBoth.block (.lit (.neg 0)) .top [] [] [] []).keep
    (G.identityNF (.conj (.lit (.neg 0)) .top)) (.here _ []) := literal_source (.neg 0) [] [] [] []
example : PositionalCut.Eliminated (P:=Empty)
    (BlockedConjBoth.parent (Γ:=[.bot]) (Θ:=[]) (X:=[]) (Y:=[]) (Z:=[]) (T:=[])
      (botOutput [.bot,.conj .bot .top]) (topTail [.conj .bot .top]))
    (BlockedConjBoth.block .bot .top [] [] [] []).keep
    (G.identityNF (.conj .bot .top)) (.here _ []) := initial_eliminated _ _ _
example : PositionalCut.Eliminated (P:=Empty)
    (BlockedConjBoth.parent (Γ:=[.bot]) (Θ:=[]) (X:=[.conj .bot .top]) (Y:=[.conj .bot .top])
      (Z:=[.conj .bot .top]) (T:=[.conj .bot .top])
      (botOutput [.bot,.conj .bot .top,.conj .bot .top,.conj .bot .top])
      (topTail [.conj .bot .top,.conj .bot .top,.conj .bot .top]))
    (BlockedConjBoth.block .bot .top [.conj .bot .top] [.conj .bot .top] [.conj .bot .top] [.conj .bot .top]).keep
    (G.identityNF (.conj .bot .top)) (.here _ []) := initial_eliminated _ _ _
example : ((BlockedConjBoth.block (.bot : NormalForm Empty) .top [.conj .bot .top] [] [] []).route.get
    (.there (.here (.conj .bot .top) [.conj .bot .top,.conj .bot .top]))).index = 0 := by rfl
example (C : NormalForm Empty) : (selectedCopies C [[],[C],[C,C]] [C]).map At.index = [0,2,5] := by rfl
end BlockedConjBothChecks
'''
p=root/'Checks/Axioms.lean';s=p.read_text()
for ns,name in [('SequentialConjBoth','native_equation'),('SequentialConjBoth','source_denote'),('BlockedConjBoth','source_equation'),('BlockedConjBoth','first_descent'),('BlockedConjBoth','second_descent'),('BlockedConjBoth','fresh_clean_and_rank'),('CutCommutation','blockedR_conjunctionBoth_rank_step')]:
 line='#print axioms DosenPetric.Reduced.Gentzen.'+ns+'.'+name+'\n'
 if line not in s:s+=line
 checks+='\n'+line
p.write_text(s);(root/'Checks/BlockedConjBoth.lean').write_text(checks)
print('Integrated',len(mods),'modules, exact three-copy source/rank signatures and four actual witnesses')
