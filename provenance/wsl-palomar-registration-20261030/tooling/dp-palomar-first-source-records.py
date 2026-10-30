archive=ev/'attempts/first-source-closure';archive.mkdir(parents=True,exist_ok=True)
for n in ['CANONICAL_CHALLENGE.json','PRESENTATION_DECLARATIONS.json','EXPORT_TARGETS.json','CHALLENGE_EXPORT.json','CHALLENGE_EXPORT_HASH.json','SOLUTION_EXPORT.json']:
 p=ev/n
 if p.exists():(archive/n).write_bytes(p.read_bytes())
(archive/'CORRECTION.json').write_text(json.dumps(dict(failure='The compiler reused Formula.Occ.match_1 in the actual Formula.subst._f, while the initial excerpt generated Formula.subst.match_1.',evidence='Both exported Formula.subst._f value closures were inspected. The auxiliary all-declaration export identified the missing generated helper in Solution.',repair='Include the original concrete Formula.Occ definition immediately before Formula.subst in Challenge, preserving the original compilation context and matching the complete value closure.',production_mathematics_changed=False,failed_exports_retained_under=str(stage/'verification')),indent=2)+'\n')
print('First source-closure failure and exact corrective reason archived')
