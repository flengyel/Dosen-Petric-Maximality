commit=(stage/'SOURCE_COMMIT.txt').read_text().strip()
assert commit=='2e771844077fd8cebfbe365230f13d4dd13a75b1'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=rc,text=True).strip()==commit
headers=json.loads((ev/'SOURCE_HEADERS.json').read_text())
paths=[r['path'] for r in headers]
tracked=subprocess.check_output(['git','ls-tree','-r','--name-only',commit],cwd=rc,text=True).splitlines()
assert {p for p in tracked if p.endswith('.lean')}==set(paths) and len(paths)==1870
critical=['Challenge.lean','Solution.lean','DosenPetric/PalomarDefinitions.lean','DosenPetric/PalomarCorrespondence.lean','DosenPetric/PalomarMaximality.lean','DosenPetric.lean','Checks/Axioms.lean','comparator.json','formalization.yaml','LICENSE','lean-toolchain','lakefile.toml','lake-manifest.json','.github/workflows/palomar-preflight.yml','scripts/PalomarClosureAudit.lean','scripts/check-source.py','scripts/verify.sh']
want=list(dict.fromkeys(paths+critical))
blob=subprocess.check_output(['git','cat-file','--batch'],cwd=rc,input=('\n'.join(commit+':'+p for p in want)+'\n').encode())
import io
stream=io.BytesIO(blob);rows=[];by_path={r['path']:r for r in headers}
for path in want:
 head=stream.readline().decode().strip().split();assert len(head)==3 and head[1]=='blob',head
 data=stream.read(int(head[2]));assert stream.read(1)==b'\n'
 digest=sha(data)
 if path in by_path:assert digest==by_path[path]['sha256'],path
 assert data==(rc/path).read_bytes(),path
 rows.append(dict(path=path,git_blob=head[0],sha256=digest,bytes=len(data)))
assert stream.read()==b''
whole=json.loads((ev/'WHOLE_SOURCE_AUDIT.json').read_text());assert whole['main_status']==''
source_tree=subprocess.check_output(['git','rev-parse',commit+'^{tree}'],cwd=rc,text=True).strip()
critical_rows=[r for r in rows if r['path'] in critical]
manifest=dict(schema_version=1,verified_source_commit=commit,source_tree=source_tree,repository='flengyel/Dosen-Petric-Maximality',private_branch='palomar/registration-20261030',all_committed_lean_files_checked_against_verified_source=1870,critical_files=critical_rows,local_verification='pass',independent_kernels=dict(Lean='accepted',NanoDa='accepted',con_ron='accepted'),public_comparator='comparator.json',definition_holes=0,selected_theorems=json.loads((rc/'comparator.json').read_text())['theorem_names'],license_proposal='Apache-2.0, including the contained original manuscript',publication_scope='The substantive flengyel/Dosen-Petric-Maximality repository, this exact source commit, and retained repository history/manuscript/evidence; no visibility change performed.',maintainer='Florian Lengyel',authorization_relationship='I am a responsible author or maintainer',approval='pending',official_full_preflight='not run',service_verification='not requested',editorial_outcome='not requested',registration='not requested',source_immutable_after_verification=True,evidence_commit_policy='Subsequent commits contain reports/evidence only and do not replace verified_source_commit.')
(ev/'RELEASE_CANDIDATE.json').write_text(json.dumps(manifest,indent=2)+'\n')
(ev/'COMMITTED_SOURCE_AUDIT.json').write_text(json.dumps(dict(source_commit=commit,source_tree=source_tree,status='pass',files=rows),indent=2)+'\n')
stage_record=json.loads((ev/'REGISTRATION_STAGE.json').read_text());stage_record['verified_source_commit']=commit;stage_record['source_tree']=source_tree
(ev/'REGISTRATION_STAGE.json').write_text(json.dumps(stage_record,indent=2)+'\n')
report=f'''# Verified Palomar release candidate

Verified immutable source: **`{commit}`**.

Private repository: `flengyel/Dosen-Petric-Maximality`.
Private branch: `palomar/registration-20261030`.
[Exact source tree](https://github.com/flengyel/Dosen-Petric-Maximality/tree/{commit}).
Git tree: `{source_tree}`.

The source was committed and pushed after the local checks passed. All 1,870
committed Lean files were then read from the Git object database and matched
against the checked source hashes. The critical submission files were checked
from committed bytes as well. The final strictly rebuilt Solution export is
byte-for-byte identical to the export accepted by Lean, NanoDa and authenticated
con-ron. Later report/evidence/delivery commits do not change this source identity.

The five selected statements are the actual-source fold maximality, actual q/e
short maximality, congruence dichotomy, nonzero literal identity, and empty
top-to-bottom hom-set, all under `DosenPetric.Palomar`. The primitive/full
quotient congruence correspondence is proved, including derived negation for
closed relations. The retained complete-paper scope remains unchanged.

## Verification and exact inputs

| Check | Result |
| --- | --- |
| Independent core-only Challenge and actual-source Solution | Pass |
| Exact public Comparator/type/definition closure | Pass |
| Expanded 360-declaration/five-type comparison and proof-route audit | Pass |
| Lean / NanoDa / authenticated con-ron | Accepted / accepted / accepted |
| Focused packaging controls | Six required rejections |
| Strict production checks | 887 files, 14,907 declaration audits |
| All-source headers/layout/import closures | 1,870 files; pass |
| Manuscript preservation | All 11 files unchanged |
| Metadata official loader/schema/taxonomy and pinned workflow | Pass |
| Commit-byte/source correspondence | Pass |
| Official full preflight / service / editorial / registration | Not performed |

| Submission input | SHA-256 |
| --- | --- |
'''+''.join('| `'+r['path']+'` | `'+r['sha256']+'` |\n' for r in critical_rows)+f'''
Machine records: `provenance/wsl-palomar-registration-20261030/RELEASE_CANDIDATE.json`
and `COMMITTED_SOURCE_AUDIT.json`. The [local report](PALOMAR_REGISTRATION_LOCAL_REPORT.md)
retains the mathematical scope, tools, outcomes and corrected first failures.
The source, original cloud reports, current reviews and instructions are retained
in this private worktree; committed-byte Downloads receipts are recorded separately.

## Concrete release decision

The proposed decision is to adopt **Apache-2.0, including the contained original
manuscript**, and publish the substantive repository
**`flengyel/Dosen-Petric-Maximality`**, including its retained source history,
manuscripts and evidence, for the exact candidate
**`{commit}`**, using root **`comparator.json`**.
The author/maintainer is **Florian Lengyel**, with the authorization relationship
**“I am a responsible author or maintainer.”**

This decision is pending. The repository remains private, main is clean at
`2c8e0968ad4fa3d318b98bcab4e531bb728b86cd`, and the stash remains
`dedfd8fc8cd49930e9a162d5be585215b062a43c`. The candidate's root license is the
reviewable proposal; no license adoption or visibility change has been effected
on main.

This gate comes from `AGENTS.md`, “Complete authorized reversible preparation
before presenting the exact publication/license/submission decision,” and
`docs/CODEX_PALOMAR_REGISTRATION.txt` §3, which states that the retained license
proposal is not the repository's currently adopted license. General preparation
authorization therefore does not silently supply this concrete release choice.

## After that decision

Use the prepared manual-only reusable workflow, with both `uses` and
`pipeline_commit` pinned to `14aa8d6b3c2f14a8540605e37144560b9a00e7e7`, exact
source `{commit}`, mode `full`, profile `palomar-standard-v1`, request
`preflight001`, and root `comparator.json`. Require mechanical status `pass`
before intake. Recheck current upstream/service instructions and use the exact
repository/commit/configuration/relationship agreement. Existing SSH access is
not by itself the service's API authentication proof.

The eventual private service review must be shown to the author before any
registration of that review's digest. No unseen review is approved here. This
release-candidate preparation does not claim a service verdict or registry entry.
'''
(rc/'docs/PALOMAR_RELEASE_CANDIDATE.md').write_text(report)
# Reconcile current reports with the actually assigned immutable source.
p=rc/'docs/PALOMAR_REGISTRATION_LOCAL_REPORT.md';t=p.read_text();a=t.index('The immutable candidate SHA');b=t.index('\n\n## Selected mathematics',a)
t=t[:a]+f'''Verified immutable candidate: `{commit}`, pushed to the isolated private
branch. All 1,870 committed Lean files and the critical submission inputs were
matched against the checked bytes from the Git object database. The exact source
tree and file hashes are recorded in `RELEASE_CANDIDATE.json` and
`COMMITTED_SOURCE_AUDIT.json`. Later evidence/delivery commits retain this
verified source identity. No public release, repository visibility change,
service intake or registration was performed.'''+t[b:];p.write_text(t)
p=rc/'docs/PALOMAR_REGISTRATION_STATUS.md';t=p.read_text();a=t.index('The immutable source SHA,');b=t.index('\n\nUpstream pins',a)
t=t[:a]+f'''The verified immutable source is `{commit}`. Exact file hashes and release
fields are in [the release-candidate report](PALOMAR_RELEASE_CANDIDATE.md) and
`provenance/wsl-palomar-registration-20261030/RELEASE_CANDIDATE.json`. All committed
Lean source bytes match the checked source. Later evidence/delivery commits do
not replace that candidate. The original cloud status is preserved verbatim in
`docs/history/PALOMAR_REGISTRATION_STATUS_2C8E096.md` and is included in delivery.'''+t[b:];p.write_text(t)
p=rc/'docs/CODEX_NEXT_SESSION.txt';t=p.read_text().replace('Exact immutable candidate\nidentity and hashes are recorded in the release-candidate evidence after the\nsource commit.',f'Verified immutable source: {commit}.\nExact file hashes are recorded in docs/PALOMAR_RELEASE_CANDIDATE.md and\nprovenance/wsl-palomar-registration-20261030/RELEASE_CANDIDATE.json.');p.write_text(t)
# Retain commit/push command evidence without modifying any submission input.
dst=ev/'logs'
for pat in ['commit-source-*','push-private-candidate-*','final-diff-check-*']:
 for p in logs.glob(pat):
  if p.is_file():(dst/p.name).write_bytes(p.read_bytes())
for p in Path('/tmp').glob('dp-palomar-*.py'):(ev/'tooling'/p.name).write_bytes(p.read_bytes())
changed=subprocess.check_output(['git','diff','--name-only',commit],cwd=rc,text=True).splitlines()
assert all(p.startswith(('docs/','provenance/wsl-palomar-registration-20261030/')) for p in changed),changed
command(['git','add','docs','provenance/wsl-palomar-registration-20261030'],'stage-release-evidence',lock=False)
raw=[str(p.relative_to(rc)) for p in dst.glob('commit-source-*.log')]+[str(p.relative_to(rc)) for p in dst.glob('push-private-candidate-*.log')]+[str(p.relative_to(rc)) for p in dst.glob('final-diff-check-*.log')]
if raw:command(['git','add','-f',*raw],'retain-push-evidence',lock=False)
command(['git','diff','--cached','--check','--','docs'],'release-report-diff-check',lock=False)
command(['git','commit','-m','Record immutable Palomar candidate and committed-source verification'],'commit-release-evidence',lock=False)
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=rc,text=True).strip();(stage/'REPORT_COMMIT.txt').write_text(head+'\n')
command(['git','push','origin','HEAD:refs/heads/palomar/registration-20261030'],'push-release-evidence',lock=False)
print('Verified source:',commit,'; committed report snapshot:',head,flush=True)
