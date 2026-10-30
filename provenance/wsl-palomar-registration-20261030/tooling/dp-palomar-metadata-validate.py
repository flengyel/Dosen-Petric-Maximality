exec(Path('/tmp/dp-palomar-common.py').read_text())
import yaml,jsonschema,tomllib
from scripts import submission_contract
p=rc/'formalization.yaml';metadata=submission_contract.load_formalization_metadata(p)
jsonschema.validate(metadata,json.loads((rc/'provenance/palomar-registration-2026-10-30/formalization-v0.4.schema.json').read_text()))
provenance=submission_contract.normalized_provenance(metadata)
config=v.load_comparator_config(rc/'comparator.json');assert set(config)=={'challenge_module','solution_module','theorem_names','definition_names','permitted_axioms'}
assert config['definition_names']==[] and set(config['permitted_axioms'])==v.STANDARD_AXIOMS
cfg=tomllib.loads((rc/'lakefile.toml').read_text());assert cfg['leanOptions']['warningAsError'] is True
assert [x for x in cfg['lean_lib'] if x['name']=='Challenge'][0]['leanOptions']['warningAsError'] is False
assert all(x['name']=='Challenge' or x.get('leanOptions',{}).get('warningAsError',True) for x in cfg['lean_lib'])
workflow=(rc/'.github/workflows/palomar-preflight.yml').read_text()
for t in ['submission.yml@14aa8d6b3c2f14a8540605e37144560b9a00e7e7','pipeline_commit: 14aa8d6b3c2f14a8540605e37144560b9a00e7e7','request_id: preflight001','mode: full','execution_profile: palomar-standard-v1','I am a responsible author or maintainer','comparator.json']:
 assert t in workflow,t
assert 'pull_request:' not in workflow and '\n  push:' not in workflow
assert sha((rc/'LICENSE').read_bytes())==sha((rc/'docs/palomar/LICENSE.Apache-2.0.proposed.txt').read_bytes())
assert not (main/'LICENSE').exists()
assert json.loads(Path('/tmp/dp-palomar-repository.json').read_text())['visibility']=='private'
(ev/'REPOSITORY_METADATA.json').write_bytes(Path('/tmp/dp-palomar-repository.json').read_bytes())
save('METADATA_VALIDATION.json',dict(status='pass',official_loader_pin=up.name,schema_sha256=sha((rc/'provenance/palomar-registration-2026-10-30/formalization-v0.4.schema.json').read_bytes()),metadata_sha256=sha(p.read_bytes()),comparator_sha256=sha((rc/'comparator.json').read_bytes()),license_sha256=sha((rc/'LICENSE').read_bytes()),workflow_sha256=sha(workflow.encode()),taxonomy=metadata['classification'],taxonomy_matches_manuscript=True,provenance=provenance,repository_visibility='private',license_proposal_only=True,production_warning_as_error=True,challenge_exception_only=True))
print('PASS: official metadata loader, pinned schema/taxonomy, public Comparator config, strict-production exception and pinned manual-only workflow',flush=True)
