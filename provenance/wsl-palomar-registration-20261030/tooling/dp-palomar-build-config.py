p=rc/'lakefile.toml';t=p.read_text();assert 'name = "Challenge"' not in t
p.write_text(t+'\n[[lean_lib]]\nname = "Challenge"\nleanOptions = { warningAsError = false }\n\n[[lean_lib]]\nname = "Solution"\n')
p=rc/'DosenPetric.lean';t=p.read_text();t+='\npublic import DosenPetric.PalomarDefinitions\npublic import DosenPetric.PalomarCorrespondence\npublic import DosenPetric.PalomarMaximality\n';p.write_text(t)
p=rc/'Checks/Axioms.lean';t=p.read_text();t+='\n'+''.join('#print axioms DosenPetric.Palomar.'+n+'\n' for n in ['maximality','short_maximality','congruence_dichotomy','identity_ne_zero','no_top_to_bot']);p.write_text(t)
p=rc/'scripts/check-source.py';t=p.read_text().replace("paths = sorted([root / 'DosenPetric.lean',", "paths = sorted([root / 'DosenPetric.lean', root / 'Solution.lean',");p.write_text(t)
(rc/'scripts/PalomarClosureAudit.lean.txt').write_bytes(Path('/tmp/PalomarClosureAudit.lean').read_bytes())
print('Production import/axiom audit and independent Challenge/Solution build configuration installed')
