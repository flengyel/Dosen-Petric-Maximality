import re
parts=[]
s=(rc/'DosenPetric/Formula.lean').read_text()
a=s.index('inductive Formula');b=s.index('\nnamespace Formula',a);formula=s[a:b]
a=s.index('/-- Tagged positions');b=s.index('\ndef label',a);occ=s[a:b]
a=s.index('def subst ');b=s.index('\n/-- An old position',a);subst=s[a:b]
parts.append('namespace DosenPetric\nuniverse u v\n'+formula+'\nnamespace Formula\nvariable {P : Type u} {Q : Type v}\n'+occ+'\n'+subst+'\nend Formula\nend DosenPetric\n')
for name in ['PresentationSyntax','PresentationEquations']:
 s=(rc/'DosenPetric'/(name+'.lean')).read_text();parts.append(s[s.index('namespace DosenPetric.Presentation'):])
s=(rc/'DosenPetric/PresentationSubstitution.lean').read_text();a=s.index('def subst {P');b=s.index('\nend Term',a)
parts.append('namespace DosenPetric.Presentation.Term\nuniverse u v\n'+s[a:b]+'\nend DosenPetric.Presentation.Term\n')
s=(rc/'DosenPetric/PalomarDefinitions.lean').read_text();parts.append(s[s.index('namespace DosenPetric.Palomar'):])
body='\n'.join(parts)
endpoints=(rc/'DosenPetric/PalomarMaximality.lean').read_text()
public='namespace DosenPetric.Palomar\nuniverse u\nopen Presentation\nvariable {P : Type u}\n\n'
for name in ['maximality','short_maximality','congruence_dichotomy','identity_ne_zero','no_top_to_bot']:
 pos=endpoints.index('theorem '+name+' ')
 posend=endpoints.index(' := by',pos)
 statement=endpoints[pos:posend]
 public+=statement+' := by\n  sorry\n\n'
public+='end DosenPetric.Palomar\n'
challenge='''module

public import Init

/-! The equation-generated Boolean arrow presentation and uniform raw
substitution congruences. Composition applies its first argument first.
The five results concern actual generated equality and existing parallel
arrows. -/

@[expose] public section
set_option autoImplicit false

'''+body+'\n'+public
assert challenge.count('  sorry\n')==5
assert len(challenge.encode())<=100*1024 and len(challenge.splitlines())<=1000
(rc/'Challenge.lean').write_text(challenge)
(rc/'Solution.lean').write_text('module\n\npublic import DosenPetric.PalomarMaximality\n')
(rc/'comparator.json').write_bytes((rc/'docs/palomar/comparator.proposed.json').read_bytes())
ev.mkdir(parents=True,exist_ok=True)
(ev/'STATEMENT_EXTRACTION.json').write_text(json.dumps(dict(challenge_lines=len(challenge.splitlines()),challenge_bytes=len(challenge.encode()),challenge_sha256=sha(challenge.encode()),source_paths=['DosenPetric/Formula.lean','DosenPetric/PresentationSyntax.lean','DosenPetric/PresentationEquations.lean','DosenPetric/PresentationSubstitution.lean','DosenPetric/PalomarDefinitions.lean','DosenPetric/PalomarMaximality.lean'],intentional_holes=5,definition_holes=0,challenge_imports=['Init']),indent=2)+'\n')
print('Challenge:',len(challenge.splitlines()),'lines,',len(challenge.encode()),'bytes; five selected theorem holes, no definition holes')
