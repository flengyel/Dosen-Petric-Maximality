import re
base=root/'DosenPetric'
mods=sorted(p for p in base.glob('Gentzen*.lean') if subprocess.run(['git','cat-file','-e','fa5b380:'+str(p.relative_to(root))],cwd=root,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode)
assert len(mods)==33,len(mods)
p=root/'DosenPetric.lean';s=p.read_text()
for m in mods:
 line='public import DosenPetric.'+m.stem+'\n'
 if line not in s:s+=line
p.write_text(s)
checks='''module

import DosenPetric

set_option autoImplicit false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
open DosenPetric.Reduced.Gentzen.DisjLogical
namespace DisjBinaryChecks
'''
for side,index,stem in [('left','first','GentzenDisjFirst'),('left','second','GentzenDisjSecond'),('right','first','GentzenDisjRightFirst'),('right','second','GentzenDisjRightSecond')]:
 s=(base/(stem+'Selected.lean')).read_text();builder='disjL'+side.title()+index.title();args='a g' if index=='first' else 'f a'
 for name,ns,call in [(builder+'_equation','DisjLogical','f g a h z' if side=='left' else 'f g h z a'),(builder+'_count','DisjLogical',args+' k'),(builder+'_atomized','DisjLogical',args+' k'),(builder+'_congr','DisjLogical',args+" k k' hk"),('disjL_'+side+'_'+index+'_rank_step','CutCommutation','f g a h z hc ih' if side=='left' else 'f g h z a hc ih')]:
  m=re.search(r'^theorem '+name+r'\s([\s\S]*?) := by\n',s,re.M);assert m,name
  checks+='\nexample {P : Type u} '+m[1]+' :=\n  '+ns+'.'+name+' '+call+'\n'
 s=(base/(stem+'Equation.lean')).read_text();name=('disj'+index.title()+'Native_equation') if side=='left' else ('disjRight'+index.title()+'Native_equation')
 m=re.search(r'^theorem '+name+r'\s([\s\S]*?) :=\n',s,re.M);assert m,name
 checks+='\nexample {P : Type u} '+m[1]+' :=\n  '+name+' f g h\n'
checks+='''
theorem identityChild (l : Literal Nat) : PositionalCut.Eliminated (G.identity l) (.here (.lit l) [])
    (G.identity l) (.here (.lit l) []) :=
  ⟨G.identity l,rfl,True.intro,(CutBase.identity_identity l).symm⟩

def doubled (l : Literal Nat) : G Nat [.lit l] [.lit l,.lit l] :=
  G.thinR [.lit l] [] [.lit l] (.lit l) (G.identity l)
def repeatedInput (l : Literal Nat) : G Nat [.lit l,.lit l] [.lit l] :=
  G.thinL [.lit l] [] [.lit l] (.lit l) (G.identity l)

theorem repeatedChild (l : Literal Nat) : PositionalCut.Eliminated (doubled l) (.here (.lit l) [.lit l])
    (repeatedInput l) (.there (.here (.lit l) [])) :=
  PositionalCut.thin_thin [.lit l] [] [.lit l] [.lit l] [] [.lit l] (.lit l)
    (G.identity l) (G.identity l) rfl rfl True.intro True.intro

def twoTops : G Empty [.top] [.top,.top] := G.thinR [.top] [] [.top] .top G.topIdentity
def topPair : G Empty [.top,.top] [.top,.top] := G.thinL [] [.top] [.top,.top] .top twoTops
def leftPop : G Empty [.top,.top] [.top,.top,.top] := G.thinR [.top,.top] [.top] [.top] .top topPair
def rightPop : G Empty [.top,.top,.top] [.top,.top] := G.thinL [.top] [.top] [.top,.top] .top topPair

theorem leftConstantChild : PositionalCut.Eliminated twoTops (.here .top [.top])
    G.topIdentity (.here .top []) :=
  PositionalCut.thin_thin [.top] [] [.top] [] [] [.top] .top G.topIdentity G.topI
    rfl rfl ⟨True.intro,True.intro⟩ True.intro

theorem rightConstantChild : PositionalCut.Eliminated (P := Empty) G.topI (.here .top [])
    (G.thinL [.top] [] [.top] .top G.topIdentity) (.there (.here .top [])) :=
  PositionalCut.top_thin [.top] [] [.top] G.topIdentity rfl ⟨True.intro,True.intro⟩

theorem leftPopChild : PositionalCut.Eliminated leftPop (.there (.here .top [.top]))
    topPair (.here .top [.top]) :=
  PositionalCut.thin_thin [.top,.top] [.top] [.top] [] [.top] [.top,.top] .top topPair twoTops rfl rfl
    ⟨True.intro,⟨True.intro,⟨True.intro,True.intro⟩⟩⟩ ⟨True.intro,⟨True.intro,True.intro⟩⟩

theorem rightPopChild : PositionalCut.Eliminated twoTops (.here .top [.top])
    rightPop (.there (.here .top [.top])) :=
  PositionalCut.thin_thin [.top] [] [.top] [.top] [.top] [.top,.top] .top G.topIdentity topPair rfl rfl
    ⟨True.intro,True.intro⟩ ⟨True.intro,⟨True.intro,⟨True.intro,True.intro⟩⟩⟩
'''
for idx in ['first','second']:
 name='disjL_left_'+idx+'_eliminated'
 f='G.identity l';g='G.identity l';a='.here (.lit l) []';h='G.identity l';z=a
 tag='(.here (.lit l) [.lit l])' if idx=='first' else '(.there (.here (.lit l) []))'
 checks+='\nexample (l : Literal Nat) : PositionalCut.Eliminated\n    (G.disjL ('+f+') ('+g+')) '+tag+' ('+h+') ('+z+') :=\n  CutCommutation.'+name+' ('+f+') ('+g+') ('+a+') ('+h+') ('+z+') rfl True.intro (identityChild l)\n'
 checks+='\nexample : PositionalCut.Eliminated\n    (G.disjL (G.identity (P := Nat) (.neg 0)) (G.identity (.neg 0))) '+re.sub(r'\bl\b','(.neg 0)',tag)+'\n    (G.identity (.neg 0)) (.here (.lit (.neg 0)) []) :=\n  CutCommutation.'+name+' (G.identity (.neg 0)) (G.identity (.neg 0)) (.here (.lit (.neg 0)) [])\n    (G.identity (.neg 0)) (.here (.lit (.neg 0)) []) rfl True.intro (identityChild (.neg 0))\n'
 f='twoTops' if idx=='first' else 'G.topIdentity';g='G.topIdentity' if idx=='first' else 'twoTops'
 tag='(.here .top [.top,.top])' if idx=='first' else '(.there (.here .top [.top]))'
 checks+='\nexample : PositionalCut.Eliminated (G.disjL '+f+' '+g+') '+tag+' G.topIdentity (.here .top []) :=\n  CutCommutation.'+name+' '+f+' '+g+' (.here .top [.top]) G.topIdentity (.here .top [])\n    rfl ⟨True.intro,True.intro⟩ leftConstantChild\n'
 f='leftPop' if idx=='first' else 'topPair';g='topPair' if idx=='first' else 'leftPop'
 tag='((At.there (.here .top [.top])).before [.top,.top])' if idx=='first' else '(At.shift [.top,.top] (.there (.here .top [.top])))'
 checks+='\nexample : PositionalCut.Eliminated (G.disjL '+f+' '+g+') '+tag+' topPair (.here .top [.top]) :=\n  CutCommutation.'+name+' '+f+' '+g+' (.there (.here .top [.top])) topPair (.here .top [.top])\n    rfl ⟨True.intro,⟨True.intro,⟨True.intro,True.intro⟩⟩⟩ leftPopChild\n'
for idx in ['first','second']:
 name='disjL_right_'+idx+'_eliminated';f='repeatedInput l' if idx=='first' else 'G.identity l';g='G.identity l' if idx=='first' else 'repeatedInput l'
 tag='(.there (.here (.lit l) []))'
 checks+='\nexample (l : Literal Nat) : PositionalCut.Eliminated (doubled l) (.here (.lit l) [.lit l])\n    (G.disjL ('+f+') ('+g+')) '+tag+' :=\n  CutCommutation.'+name+' ('+f+') ('+g+') (doubled l) (.here (.lit l) [.lit l]) (.here (.lit l) [])\n    rfl True.intro (repeatedChild l)\n'
 checks+='\nexample : PositionalCut.Eliminated (doubled (.neg 0)) (.here (.lit (.neg 0)) [.lit (.neg 0)])\n    (G.disjL ('+re.sub(r'\bl\b','(.neg 0)',f)+') ('+re.sub(r'\bl\b','(.neg 0)',g)+')) '+re.sub(r'\bl\b','(.neg 0)',tag)+' :=\n  CutCommutation.'+name+' ('+re.sub(r'\bl\b','(.neg 0)',f)+') ('+re.sub(r'\bl\b','(.neg 0)',g)+')\n    (doubled (.neg 0)) (.here (.lit (.neg 0)) [.lit (.neg 0)]) (.here (.lit (.neg 0)) []) rfl True.intro (repeatedChild (.neg 0))\n'
 f='(G.thinL [.top] [] [.top] .top G.topIdentity)' if idx=='first' else 'G.topIdentity';g='G.topIdentity' if idx=='first' else '(G.thinL [.top] [] [.top] .top G.topIdentity)'
 checks+='\nexample : PositionalCut.Eliminated (P := Empty) G.topI (.here .top [])\n    (G.disjL '+f+' '+g+') (.there (.here .top [])) :=\n  CutCommutation.'+name+' '+f+' '+g+' G.topI (.here .top []) (.here .top [])\n    rfl ⟨True.intro,True.intro⟩ rightConstantChild\n'
 f='rightPop' if idx=='first' else 'topPair';g='topPair' if idx=='first' else 'rightPop';tag='(.there ((At.here .top [.top]).before [.top]))' if idx=='first' else '(At.shift [.disj .top .top,.top] (.here .top [.top]))'
 checks+='\nexample : PositionalCut.Eliminated twoTops (.here .top [.top]) (G.disjL '+f+' '+g+') '+tag+' :=\n  CutCommutation.'+name+' '+f+' '+g+' twoTops (.here .top [.top]) (.here .top [.top])\n    rfl ⟨True.intro,⟨True.intro,⟨True.intro,True.intro⟩⟩⟩ rightPopChild\n'
checks+='\nend DisjBinaryChecks\n'
p=root/'Checks/Axioms.lean';s=p.read_text()
for ns,name in [('DisjLogical','disjL_left_first_core'),('DisjLogical','sourceConj_swap'),('DisjLogical','disjL_right_second_core'),('DisjLogical','disjL_right_first_core')]+[(ns,'disjL_'+side+'_'+idx+'_rank_step') for ns in ['CutCommutation'] for side in ['left','right'] for idx in ['first','second']]+[('DisjLogical','disjL'+side.title()+idx.title()+'_equation') for side in ['left','right'] for idx in ['first','second']]:
 line='#print axioms DosenPetric.Reduced.Gentzen.'+ns+'.'+name+'\n'
 if line not in s:s+=line
 checks+='\n#print axioms '+ns+'.'+name+'\n'
p.write_text(s);(root/'Checks/DisjBinaryCuts.lean').write_text(checks)
print('Integrated',len(mods),'production modules; exact types and sixteen actual witness checks')
