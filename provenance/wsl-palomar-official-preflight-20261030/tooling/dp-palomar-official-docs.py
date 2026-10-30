check_source()
release=json.loads((stage/'PUBLIC_RELEASE.json').read_text())
approval=json.loads((stage/'RELEASE_AUTHORIZATION.json').read_text())
request=json.loads((stage/'DISPATCH_REQUEST.json').read_text())
workflow=json.loads((stage/'WORKFLOW_RUN.json').read_text())
url=workflow['html_url'];rid=workflow['id'];state=workflow['status']
ev.mkdir(exist_ok=True)
for name in ['PUBLIC_RELEASE.json','RELEASE_AUTHORIZATION.json','DISPATCH_REQUEST.json','DISPATCH_ACCEPTED.json','WORKFLOW_RUN.json','WORKFLOW_JOBS.json']:
 p=stage/name
 if p.exists():(ev/name).write_bytes(p.read_bytes())
record=dict(utc=now(),repository=repo,repository_visibility='public',license='Apache-2.0',author_approval='Yes; exact release question accepted',verified_submission_commit=source,pipeline_commit=pin,workflow_run_id=rid,workflow_url=url,workflow_caller_head_sha=workflow['head_sha'],mode='full',execution_profile='palomar-standard-v1',request_id='preflight001',toolchain='leanprover/lean4:v4.35.0',local_verification_reused=True,official_full_preflight_status=state,mechanical_report_status='not yet available',palomar_service_intake='not requested',palomar_registration='not performed',arxiv_submission='not performed; only after Palomar registration',next_project='Local connectedness in recursion categories and essential incompleteness; after arXiv',stash=stash)
save(ev/'OFFICIAL_PREFLIGHT_STAGE.json',record)
# Reconcile all active process records. Mathematical source/metadata/workflow stay fixed.
old=root/'provenance/wsl-palomar-registration-20261030'
r=json.loads((old/'REGISTRATION_STAGE.json').read_text())
r['repository'].update(visibility='public',license='Apache-2.0 adopted with explicit author approval, including original manuscript and retained history')
r['publication_or_service_action_performed']=True
r['stages']['official_full_preflight']=dict(status=state,workflow_url=url,run_id=rid,verified_source_commit=source,mechanical_report_status='not yet available')
r['publication']=dict(status='public',approval_record=str((ev/'RELEASE_AUTHORIZATION.json').relative_to(root)),license='Apache-2.0')
r['publication_order']=['Palomar Registry registration','arXiv submission','Local connectedness project']
r['service_intake_scope']='Bring official preflight result to author before proceeding with intake'
save(old/'REGISTRATION_STAGE.json',r)
m=json.loads((old/'RELEASE_CANDIDATE.json').read_text())
m['approval']='explicitly approved by author';m['publication_status']='public';m['license_adopted']='Apache-2.0'
m['publication_scope']='Substantive repository, original manuscript and retained history made public with explicit author approval; verified submission commit remains fixed.'
m['approval_record']=str((ev/'RELEASE_AUTHORIZATION.json').relative_to(root));m['official_full_preflight']=dict(status=state,run_id=rid,url=url)
m['preparation_branch']=m.get('private_branch','palomar/registration-20261030')
save(old/'RELEASE_CANDIDATE.json',m)
p=root/'README.md';t=p.read_text();a=t.index('The root metadata, license text');b=t.index('\n## Current complete',a)
t=t[:a]+f'''The author approved Apache-2.0 publication, including the original manuscript
and retained history, on 30 October 2026. The repository is public. Its immutable
submission SHA remains `{source}`. Lean stays at 4.35.0.
[Official full preflight]({url}) is running with the pinned standard profile;
the [stage report](docs/PALOMAR_OFFICIAL_PREFLIGHT_REPORT.md) distinguishes its
result from local verification, service intake and final registration. The
publication order is Palomar Registry registration first, then arXiv submission.
'''+t[b:]
a=t.index('The complete verified package is merged into main.',t.index('The [current requirements]'))
t=t[:a]+f'''The verified package is merged into main and publicly released under the
author-approved Apache-2.0 license, including the original manuscript and retained
history. Original proposals remain under `docs/palomar/` as historical materials.
The verified source remains `{source}`. Official full preflight is running;
service verification and registration remain subsequent stages. ArXiv submission
follows successful Palomar registration.
''';p.write_text(t)
p=root/'AGENTS.md';t=p.read_text();t=t.replace('family are now complete. Official/service checks and publication remain separate\nsubsequent stages.', 'family are now complete. The author has approved Apache-2.0 public release,\nincluding the original manuscript and retained history, and the repository is\npublic. Official preflight and service/registration remain separate stages.',1)
a=t.index('The full-paper mathematical endpoint remains complete.',t.index('## Palomar registration phase'))
t=t[:a]+f'''The full-paper mathematical endpoint remains complete. The independent
Challenge/Solution package, correspondence, local kernel verification and
metadata are complete and merged into main. The author explicitly approved
Apache-2.0 publication of the repository, original manuscript and retained history;
the repository is now public. Verified submission source: {source}.
Keep Lean at 4.35.0 and reuse the completed local verification. Official full
preflight is running at {url}.

Preserve the verified source commit; later reports/evidence do not replace it.
Bring the official mechanical result to the author before proceeding with service
intake. Final registration requires the author to see and approve the actual
service review and digest. Do not automate browser sign-in or treat release
approval as consent to an unseen review.

The author clarified the publication order: Palomar Registry registration first,
then arXiv submission, then work on Local connectedness in recursion categories
and essential incompleteness. Do not submit to arXiv before Palomar registration.
Do not reopen the completed proof-development or local packaging sequence.
''';p.write_text(t)
p=root/'docs/PALOMAR_RELEASE_CANDIDATE.md';t=p.read_text().replace('Private repository:', 'Public repository:',1)
a=t.index('The proposed decision is to adopt');b=t.index('## Toolchain and next required check',a)
t=t[:a]+f'''The author explicitly approved **Apache-2.0**, including the original manuscript
and retained history, and public release of **`{repo}`**, for the exact source
**`{source}`**, using root **`comparator.json`**. Florian Lengyel is the
responsible author/maintainer. The approval and completed visibility change are
recorded in `provenance/wsl-palomar-official-preflight-20261030/`.

The repository is public. Main includes the candidate and receipts through
`23ec1bc` and subsequent documentation/evidence. The stash remains
`{stash}`. No service intake or final registration has occurred.

'''+t[b:]
t=t.replace('Official full preflight is the next verification stage.',f'Official full preflight is running at [run {rid}]({url}).',1)
t=t.replace('An authenticated Windows GitHub CLI session for `flengyel` and the registered\nmanual-only workflow are available. Publication and dispatch can proceed after\nthe explicit release confirmation.', 'The authenticated Windows GitHub CLI session for `flengyel` performed the\napproved visibility change and dispatched the registered manual-only workflow.',1)
t=t.replace('## After that decision','## Official workflow and publication order',1)
t+='\nThe author specified Palomar Registry registration before arXiv submission.\nAfter the official mechanical result is reviewed with the author, service intake\nmay proceed. Final registration still requires approval of the actual service\nreview. The later Local connectedness project follows arXiv submission.\n';p.write_text(t)
p=root/'docs/PALOMAR_REGISTRATION_LOCAL_REPORT.md';t=p.read_text().replace('This is a verified private release\ncandidate; official full preflight and service registration have not run.', 'This is a locally verified release candidate, now publicly released with the\nauthor\'s Apache-2.0 approval. Official full preflight is running; service\nregistration has not occurred.',1)
a=t.index('## Release and delivery boundary');t=t[:a]+f'''## Release and delivery boundary

The author explicitly approved Apache-2.0 publication, including the original
manuscript and retained history. The root release package is on main and the
repository is public. The verified submission remains `{source}`.
[Official full preflight]({url}) is running for that exact commit. Its outcome
is recorded separately in `PALOMAR_OFFICIAL_PREFLIGHT_REPORT.md`; the local
proof, comparison and kernel evidence above is reused without a Lean upgrade.

No service intake or final registration has occurred. Bring the official result
to the author before intake. The actual service review must be shown to the
author before registration of its digest. The agreed publication order is
Palomar Registry registration, then arXiv submission, then the Local connectedness
project. Earlier private/release-proposal states remain in the immutable history.

Every finalized report/review and requested instruction is delivered from
committed bytes to Windows Downloads, preserving differing existing files.
Delivery registers distinguish each source commit and version; no local or
preflight log is treated as a registry result.
''';p.write_text(t)
status=f'''# Palomar registration status — 30 October 2026

The repository is public under the author-approved Apache-2.0 license, including
the original manuscript and retained history. The complete verified package is
merged into main. The immutable submission source remains **`{source}`**.
The preparation branch and original stash are preserved.

| Stage | Actual current status |
| --- | --- |
| Complete-paper mathematics | Complete at the recorded endpoint; claim map and all manuscript versions preserved. |
| Local package / comparison / independent kernels | Complete; Lean, NanoDa and authenticated con-ron accepted. |
| Strict production and whole-source audits | Complete: 887 files / 14,907 declarations; all 1,870 source headers and closures checked. |
| Publication and license | Explicit author approval received; repository public under Apache-2.0, including manuscript/history. |
| Official full preflight | Running: [run {rid}]({url}); pinned pipeline `{pin}`, full mode, standard profile, `preflight001`, exact source `{source}`. |
| Service intake / verification | Not requested. Bring official preflight result to author before proceeding. |
| Service review / final registration | Not performed. Actual service review and digest require author approval. |
| ArXiv | Not submitted; follows successful Palomar Registry registration. |
| Following project | Local connectedness in recursion categories and essential incompleteness; after arXiv. |

Keep Lean pinned at **4.35.0**, supported by the current checker policy. Reuse
the completed local verification; the official run is the next verification
stage. Its caller head is `{workflow['head_sha']}` while the submitted proof
source is `{source}`. These are distinct fields.

See [release record](PALOMAR_RELEASE_CANDIDATE.md),
[official stage report](PALOMAR_OFFICIAL_PREFLIGHT_REPORT.md),
[local evidence](PALOMAR_REGISTRATION_LOCAL_REPORT.md), and the current machine
record in `provenance/wsl-palomar-official-preflight-20261030/`.
The five-name selection remains distinct from the broader complete-paper scope.
Historical private/proposal states and earlier byte-verified deliveries remain
preserved in Git and the delivery registers.
'''
(root/'docs/PALOMAR_REGISTRATION_STATUS.md').write_text(status)
next_text=f'''Current task: monitor the approved official full Palomar preflight.

Verified immutable submission: {source}.
Repository: {repo}, now public under author-approved Apache-2.0, including
the original manuscript and retained history. Candidate and receipts are on main;
the preparation branch and stash remain preserved. Do not ask for release/license
approval again. Approval records are in
provenance/wsl-palomar-official-preflight-20261030/RELEASE_AUTHORIZATION.json.

Official workflow: {url}
Run ID: {rid}. Pipeline pin: {pin}.
Mode full; profile palomar-standard-v1; request preflight001; root comparator.json.
The workflow caller head is {workflow['head_sha']}, distinct from the immutable
submission SHA above. Read the actual mechanical report; require status pass.
Preserve diagnostics and fix only the indicated cause. Do not invent a passed
replay from an OOM, infrastructure error, or green setup job.

Keep Lean at 4.35.0. Reuse the completed local package/comparison/kernel/source
verification; do not restart the full-paper proof sequence or change the fixed
source for unchanged-input workflow issues. See docs/PALOMAR_OFFICIAL_PREFLIGHT_REPORT.md,
docs/PALOMAR_REGISTRATION_STATUS.md and docs/CODEX_PALOMAR_REGISTRATION.txt.

Bring the official result to the author before proceeding with Palomar service
intake. No service intake or final registration has occurred. The existing Windows
GitHub CLI session is authenticated as flengyel. Do not automate browser sign-in
or expose tokens/private service review in the public repository. The author must
see and approve the actual service review and digest before final registration.

Publication order, explicitly clarified by the author: Palomar Registry
registration first, then arXiv submission, then Local connectedness in recursion
categories and essential incompleteness. Do not submit the paper to arXiv before
Palomar registration. Keep reports/evidence/Downloads deliveries byte-verified
and preserve differing prior copies and all completed mathematical results.
'''
(root/'docs/CODEX_NEXT_SESSION.txt').write_text(next_text)
report=f'''# Official Palomar full preflight

The author approved Apache-2.0 publication, including the original manuscript
and retained history, and official full preflight for the fixed verified source
`{source}`. The repository is now public:
https://github.com/{repo}.

**Current official run: [run {rid}]({url}), {state}.**
A mechanical result has not yet been collected. Local verification is complete
and reused; it is not relabelled as this official outcome. Lean stays at 4.35.0.

| Exact field | Value |
| --- | --- |
| Verified submission | `{source}` |
| Comparator | `comparator.json` |
| Relationship | I am a responsible author or maintainer |
| Pipeline | `{pin}` |
| Workflow | `.github/workflows/palomar-preflight.yml` |
| Mode | `full` |
| Profile | `palomar-standard-v1` |
| Request | `preflight001` |
| Caller head | `{workflow['head_sha']}` |
| Actual GitHub run | `{rid}` |

The repository visibility change and GitHub dispatch were checked through the
existing authenticated Windows GitHub CLI session for `flengyel`. GitHub reports
the license as Apache-2.0. No credential was created or extracted. Public release
and dispatch records are retained under
`provenance/wsl-palomar-official-preflight-20261030/`. Raw user-profile responses
and any future service token/review are excluded from public evidence.

The author asked whether the agent was registering on their behalf. The scope
was clarified and accepted: public release and official preflight are being
handled; no Palomar intake or registration has occurred. Bring the official
result to the author before proceeding with intake. Final registration requires
the author to read and approve the actual service review and digest.

The publication order is **Palomar Registry registration first, then arXiv**.
The Local connectedness in recursion categories and essential incompleteness
project follows arXiv submission. No arXiv submission has occurred.

The verified source and all 17 critical input hashes remain unchanged. The stash
is preserved. Earlier private/proposal states and delivery copies remain valid
historical records; this report records the subsequent approved public stage.
'''
(root/'docs/PALOMAR_OFFICIAL_PREFLIGHT_REPORT.md').write_text(report)
check_source()
changed=git('diff','--name-only').splitlines()
assert all(p in ['AGENTS.md','README.md'] or p.startswith(('docs/','provenance/')) for p in changed)
subprocess.run(['git','diff','--check'],cwd=root,check=True)
run(['git','add','AGENTS.md','README.md','docs','provenance/wsl-palomar-registration-20261030/REGISTRATION_STAGE.json','provenance/wsl-palomar-registration-20261030/RELEASE_CANDIDATE.json','provenance/wsl-palomar-official-preflight-20261030'],'stage-public-stage')
run(['git','commit','-m','Record approved Apache-2.0 public release and official full preflight'],'commit-public-stage')
commit=git('rev-parse','HEAD');(stage/'PUBLIC_STAGE_COMMIT.txt').write_text(commit+'\n')
run(['git','push','origin','main'],'push-public-stage')
assert git('status','--porcelain')==''
print(json.dumps(dict(status='recorded',commit=commit,verified_source=source,workflow_url=url,official_status=state,publication_order=['Palomar registration','arXiv submission'],service_intake='not requested'),indent=2),flush=True)
