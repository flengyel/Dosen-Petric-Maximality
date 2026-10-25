from pathlib import Path
import hashlib,json,re,subprocess
r=Path('/home/flengyel/src/Dosen-Petric-Maximality')
w=r/'.codex-work/gentzen-reducibility'
mods=['GentzenAddressTracing','GentzenAddressPaths','GentzenClusterTransport','GentzenEntryFrames',
      'GentzenReducibilityBoundary','GentzenReducibilityLogical','GentzenReducibilityObstructions','GentzenReducibilityExamples']
base='9075ecc343be5c07d38b7f5ba53676f8f8f32bea'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip()==base
snap=r/'.codex-work/reducibility-reconciliation/20261025T013921Z'
saved=json.loads((snap/'reconciliation.json').read_text())
for row in saved['untracked']:
 p=r/row['path'];assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256'],str(p)
names=[];theorems=[]
for mod in mods:
 ns=[]
 for line in (r/'DosenPetric'/(mod+'.lean')).read_text().splitlines():
  m=re.match(r'namespace (\S+)',line)
  if m:ns.append(m[1]);continue
  if ns and line=='end '+ns[-1]:ns.pop();continue
  m=re.match(r'(theorem|def|abbrev|inductive) (\S+)',line)
  if m:
   n='.'.join(ns+[m[2]]);names.append(n)
   if m[1]=='theorem':theorems.append(n)
root=r/'DosenPetric.lean';axioms=r/'Checks/Axioms.lean'
old=json.loads((w/'combined-source.json').read_text())
assert root.read_text()==subprocess.check_output(['git','show',base+':DosenPetric.lean'],cwd=r,text=True)+''.join('public import DosenPetric.'+m+'\n' for m in mods[:4])
assert axioms.read_text()==subprocess.check_output(['git','show',base+':Checks/Axioms.lean'],cwd=r,text=True)+''.join('#print axioms '+n+'\n' for n in old['new_selected_axiom_prints'])
root.write_text(root.read_text()+''.join('public import DosenPetric.'+m+'\n' for m in mods[4:]))
axioms.write_text(axioms.read_text()+''.join('#print axioms '+n+'\n' for n in theorems if n not in old['new_selected_axiom_prints']))
(w/'PublicTypes.lean').write_text('module\nimport DosenPetric\n'+''.join('#check '+n+'\n' for n in names))
(w/'integrated-api.json').write_text(json.dumps(dict(modules=mods,public_queries=names,selected_axiom_prints=theorems),indent=2)+'\n')
paths=[r/'DosenPetric.lean',*r.glob('DosenPetric/**/*.lean'),*r.glob('Checks/**/*.lean'),*r.glob('scripts/*.py'),*r.glob('scripts/*.sh'),r/'lakefile.toml',r/'lean-toolchain',r/'lake-manifest.json']
(w/'CHECKED_SOURCES.sha256').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(p.relative_to(r))+'\n' for p in sorted(paths)))
print(json.dumps(dict(modules=len(mods),queries=len(names),selected_axiom_prints=len(theorems),preserved_inputs_verified=True),indent=2))
