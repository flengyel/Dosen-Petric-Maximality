import re
base=root/'DosenPetric'
mods=sorted(p for p in base.glob('Gentzen*.lean') if subprocess.run(['git','cat-file','-e','375356f:'+str(p.relative_to(root))],cwd=root,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode)
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
namespace BlockedConjSecondChecks
'''
for file,ns,name,call in [
 ('GentzenSequentialConjSecondNative','SequentialConjSecond','native_equation','f g h'),
 ('GentzenBlockedConjSecondData','BlockedConjSecond','parent_source','f g'),
 ('GentzenBlockedConjSecondEquation','BlockedConjSecond','source_equation','f g h z'),
 ('GentzenBlockedConjSecondDescent','BlockedConjSecond','original_descent','f g h z hc'),
 ('GentzenBlockedConjSecondRank','BlockedConjSecond','fresh_clean_and_rank','f g h z hc k hk ak'),
 ('GentzenBlockedConjSecondRank','CutCommutation','blockedR_conjunctionSecond_rank_step','f g h z hc ih')]:
 s=(base/(file+'.lean')).read_text();m=re.search(r'^theorem '+name+r'\s([\s\S]*?) := by\n',s,re.M);assert m,name
 checks+='\nsection\nopen '+('SequentialConjSecond' if ns=='SequentialConjSecond' else 'BlockedConjSecond')+'\nexample {P : Type u} '+m[1]+' :=\n  '+ns+'.'+name+' '+call+'\nend\n'
old=Path('/tmp/dp-rf-integrate.py').read_text();a=old.index('def botOutput');b=old.index('\ntheorem literal_source',a);checks+='\n'+old[a:b]
checks+='''
theorem literal_source (l : Literal Nat) (F Z T : List (NormalForm Nat)) :
    PositionalCut.Eliminated
      (BlockedConjSecond.parent (Γ:=[.bot]) (Θ:=[]) (F:=F) (Z:=Z) (T:=T)
        (botOutput (.lit l::F)) (topTail (Z++.conj (.lit l) .top::T)))
      (BlockedConjSecond.block (.lit l) .top F Z T).keep
      (G.identityNF (.conj (.lit l) .top)) (.here _ []) := initial_eliminated _ _ _
example : PositionalCut.Eliminated
    (BlockedConjSecond.parent (Γ:=[.bot]) (Θ:=[]) (F:=[]) (Z:=[]) (T:=[])
      (botOutput [.lit (.neg 0)]) (topTail [.conj (.lit (.neg 0)) .top]))
    (BlockedConjSecond.block (.lit (.neg 0)) .top [] [] []).keep
    (G.identityNF (.conj (.lit (.neg 0)) .top)) (.here _ []) := literal_source (.neg 0) [] [] []
example : PositionalCut.Eliminated (P:=Empty)
    (BlockedConjSecond.parent (Γ:=[.bot]) (Θ:=[]) (F:=[]) (Z:=[]) (T:=[])
      (botOutput [.bot]) (topTail [.conj .bot .top]))
    (BlockedConjSecond.block .bot .top [] [] []).keep
    (G.identityNF (.conj .bot .top)) (.here _ []) := initial_eliminated _ _ _
example : PositionalCut.Eliminated (P:=Empty)
    (BlockedConjSecond.parent (Γ:=[.bot]) (Θ:=[]) (F:=[.conj .bot .top]) (Z:=[.conj .bot .top]) (T:=[.conj .bot .top])
      (botOutput [.bot,.conj .bot .top]) (topTail [.conj .bot .top,.conj .bot .top,.conj .bot .top]))
    (BlockedConjSecond.block .bot .top [.conj .bot .top] [.conj .bot .top] [.conj .bot .top]).keep
    (G.identityNF (.conj .bot .top)) (.here _ []) := initial_eliminated _ _ _
example : ((BlockedConjSecond.block (.bot : NormalForm Empty) .top [.conj .bot .top] [] []).route.get
    (.there (.here (.conj .bot .top) [.conj .bot .top]))).index = 0 := by rfl
end BlockedConjSecondChecks
'''
p=root/'Checks/Axioms.lean';s=p.read_text()
for ns,name in [('SequentialConjSecond','native_equation'),('BlockedConjSecond','source_equation'),('BlockedConjSecond','original_descent'),('BlockedConjSecond','fresh_clean_and_rank'),('CutCommutation','blockedR_conjunctionSecond_rank_step')]:
 line='#print axioms DosenPetric.Reduced.Gentzen.'+ns+'.'+name+'\n'
 if line not in s:s+=line
 checks+='\n'+line
p.write_text(s);(root/'Checks/BlockedConjSecond.lean').write_text(checks)
print('Integrated',len(mods),'modules, exact second-child source/rank signatures and four actual witnesses')
