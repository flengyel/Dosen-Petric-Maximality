check_source()
result=json.loads((stage/'MECHANICAL_RESULT.json').read_text())
report=json.loads((stage/'mechanical-report.json').read_text())
assert result['mechanical_status']=='pass' and report['phase']=='verification' and report['stage']=='complete'
assert report['source']['commit']==source and report['lean_toolchain']=='leanprover/lean4:v4.35.0'
assert report['con_ron_checker']['binary_sha256']=='4e5616d94374cae37324dad2594f6230c2bb2297240249fc78ff508f3bc5acef'
assert result['artifact_zip_sha256']==result['github_digest'].removeprefix('sha256:')
alarms=[r for r in report['resource_usage'] if r.get('deadline_fired') or r.get('supervisor_timeout') or any(r.get('memory_events',{}).values())]
assert alarms==[],alarms
rid=result['workflow_run_id'];url=result['workflow_url'];rsha=result['mechanical_report_sha256'];zsha=result['artifact_zip_sha256']
assert result['kernel_attempts'][0]['status']=='accepted'
ev.mkdir(exist_ok=True)
for name in ['mechanical-report.json','mechanical-report.zip','MECHANICAL_RESULT.json','WORKFLOW_RUN.json','WORKFLOW_JOBS.json','WORKFLOW_ARTIFACTS.json']:
 (ev/name).write_bytes((stage/name).read_bytes())
for p in stage.glob('job-*.log'):(ev/p.name).write_bytes(p.read_bytes())
state=json.loads((ev/'OFFICIAL_PREFLIGHT_STAGE.json').read_text())
state.update(utc=now(),official_full_preflight_status='pass',mechanical_report_status='pass',mechanical_report_sha256=rsha,artifact_zip_sha256=zsha,mandatory_Lean='accepted',mandatory_NanoDa='accepted',protected_con_ron='accepted',resource_alarm_count=0,warnings=report['warnings'],service_intake='not requested',registration='not performed',arxiv='not submitted; after Palomar registration')
save(ev/'OFFICIAL_PREFLIGHT_STAGE.json',state)
old=root/'provenance/wsl-palomar-registration-20261030'
r=json.loads((old/'REGISTRATION_STAGE.json').read_text())
r['stages']['official_full_preflight']=dict(status='pass',phase='verification',stage='complete',workflow_url=url,run_id=rid,verified_source_commit=source,mechanical_report_sha256=rsha,Lean='accepted',NanoDa='accepted',con_ron='accepted')
save(old/'REGISTRATION_STAGE.json',r)
m=json.loads((old/'RELEASE_CANDIDATE.json').read_text());m['official_full_preflight']=r['stages']['official_full_preflight'];save(old/'RELEASE_CANDIDATE.json',m)
p=root/'README.md';t=p.read_text().replace(f'[Official full preflight]({url}) is running with the pinned standard profile;',f'[Official full preflight]({url}) passed with the pinned standard profile;',1).replace('Official full preflight is running;\nservice verification and registration remain subsequent stages.', 'Official full preflight passed;\nservice verification and registration remain subsequent stages.',1);p.write_text(t)
p=root/'AGENTS.md';t=p.read_text().replace('Official full\npreflight is running at '+url+'.', 'Official full\npreflight passed at '+url+'.',1);p.write_text(t)
p=root/'docs/PALOMAR_RELEASE_CANDIDATE.md';t=p.read_text().replace(f'Official full preflight is running at [run {rid}]({url}).',f'Official full preflight passed at [run {rid}]({url}); the mechanical report\nrecords status `pass`, phase `verification`, and stage `complete`.',1)
t=t.replace('| Official full preflight / service / editorial / registration | Not performed |', '| Official full preflight | Pass for the exact verified submission; Lean, NanoDa and con-ron accepted. |\n| Service intake / editorial / registration | Not performed. |',1)
t=t.replace('The proposed decision is to adopt', 'The approved decision is to adopt',1)
p.write_text(t)
p=root/'docs/PALOMAR_REGISTRATION_LOCAL_REPORT.md';t=p.read_text().replace('Official full preflight is running; service\nregistration has not occurred.', 'Official full preflight passed; service\nregistration has not occurred.',1).replace(f'[Official full preflight]({url}) is running for that exact commit.',f'[Official full preflight]({url}) passed for that exact commit.',1)
t=t.replace('| Official full preflight | Not run. The pinned manual-only full workflow is prepared. |', f'| Official full preflight | Pass: [run {rid}]({url}), exact immutable source; Lean, NanoDa and con-ron accepted. |',1)
p.write_text(t)
p=root/'docs/PALOMAR_REGISTRATION_STATUS.md';t=p.read_text().replace(f'| Official full preflight | Running: [run {rid}]({url});',f'| Official full preflight | **Pass**: [run {rid}]({url});',1).replace('the completed local verification; the official run is the next verification\nstage.', 'the completed local verification; the official full run has now passed.',1);p.write_text(t)
p=root/'docs/CODEX_NEXT_SESSION.txt';t=p.read_text().replace('Current task: monitor the approved official full Palomar preflight.', 'Current task: present the passed official full preflight result before Palomar intake.',1)
t=t.replace(f'Run ID: {rid}. Pipeline pin:',f'Run ID: {rid}; completed successfully. Mechanical report: pass, verification, complete.\nLean, NanoDa and protected con-ron accepted. Pipeline pin:',1)
t=t.replace('The workflow caller head is', 'Official report and digest:\nprovenance/wsl-palomar-official-preflight-20261030/mechanical-report.json\nSHA-256: '+rsha+'.\nThe workflow caller head is',1)
t=t.replace('Read the actual mechanical report; require status pass.', 'The actual mechanical report was retrieved and its artifact digest verified.',1);p.write_text(t)
# A standalone result with exact statements, scope, warning and measured diagnostics.
summary=f'''# Official full Palomar preflight — passed

**Official mechanical status: `pass`; phase: `verification`; stage: `complete`.**
[GitHub run {rid}]({url}) completed successfully for the immutable submission
`{source}`. The repository is public under the author-approved Apache-2.0
license, including the original manuscript and retained history.

## Exact run and evidence

| Field | Verified value |
| --- | --- |
| Repository | `{repo}` |
| Submitted proof source | `{source}` |
| Comparator path | `comparator.json` |
| Pipeline pin | `{pin}` |
| Mode / profile | `full` / `palomar-standard-v1` |
| Request | `preflight001` |
| Workflow caller head | `{result.get('workflow_caller_head_sha',json.loads((stage/'WORKFLOW_RUN.json').read_text())['head_sha'])}` |
| Lean toolchain | `leanprover/lean4:v4.35.0` |
| Lean toolchain commit | `{report['toolchain_commit']}` |
| Official mechanical report SHA-256 | `{rsha}` |
| Artifact ZIP SHA-256 | `{zsha}` |
| GitHub artifact | `{result['artifact_name']}`, ID `{result['artifact_id']}` |

The downloaded ZIP's SHA-256 matches GitHub's advertised artifact digest. Its
single `mechanical-report.json` was retained byte-for-byte and checked for the
exact repository, immutable source, workflow URL, standard profile and full
verification phase. The caller head identifies the workflow launch, while the
submitted proof source above identifies what was checked. `preflight001` is the
workflow request identifier, not a Palomar service submission or registry ID.

## Mechanical outcomes

| Check | Actual official result |
| --- | --- |
| Source and license | Exact source fetched; Apache-2.0 declared and detected. |
| Whole-source policy | All 1,870 regular Lean sources checked with `lean --deps-json`; module/line policy passed. |
| Challenge provenance | High trust; no project imports, no untrusted sources; one core source dependency. |
| Independent Challenge | 562 lines, 23,920 bytes; concrete definitions and five intended statement-proof placeholders. |
| Solution build | Fresh build passed: 758 build jobs. |
| Public Comparator | Exact five selected types and their required definition closure matched; definition holes `[]`; only `propext`, `Quot.sound`, `Classical.choice` permitted. |
| Lean kernel | Accepted. |
| NanoDa | Accepted. |
| Protected authenticated con-ron | Accepted 9,639 declarations in `--verified` mode. |
| Resource outcome | No OOM/OOM-kill, deadline or supervisor timeout event. |

The protected con-ron binary is SHA-256
`{report['con_ron_checker']['binary_sha256']}`, from the policy-authenticated
v4.36.0-rc1 checker update for the submitted Lean 4.35.0 toolchain. **The Lean
compiler was not upgraded.** Its output records two inductive blocks modelled
in-process (Lean.Syntax and DosenPetric.TraceTree; 51 generated records checked
as declarations) and the two pinned Nat-operation hoists. These actual outcomes
are retained, not inferred from the earlier local replay.

The sole official warning is that the Challenge exceeds the preferred
300-line/32-KiB review surface. Its 562 lines exceed the preferred line count;
its 23,920 bytes are below 32 KiB. Both hard limits, 1,000 lines and 100 KiB,
are satisfied. The finite concrete presentation is preserved.

The standard GitHub-hosted runner reported 4 CPUs and 16,760,332,288 bytes of
host memory. Measured solution build time was 282.559 seconds, Solution export
5.621 seconds, Comparator 39.781 seconds, and con-ron 26.059 seconds. These are
observed phase measurements, not estimates of proof-development cost or total
job duration. Supervised proof phases returned success. Deliberate confinement
negative probes have expected nonzero exits; they are not failed proof phases.
Full resource records, tool digests and complete public job logs are retained.

## Source and publication scope

The author approved the concrete public-release question with “Yes.” The source,
root Comparator and all 17 critical input hashes remain fixed. The completed
local package, strict audit, expanded definition audit and focused controls were
reused. No local proof rewrite, new mathematical assumption or Lean upgrade was
introduced for this official run. The complete-paper claim map and manuscripts
remain preserved; the registry selection is the five-statement maximality family
and its two structural witnesses.

The release authorization, public visibility check, dispatch inputs, run/job
records, artifact listing, original mechanical JSON and ZIP, and tool digests are
retained under `provenance/wsl-palomar-official-preflight-20261030/`.

## Next stages and author control

No Palomar service intake, editorial review or final registration has occurred.
The agreed scope is to bring this official result to the author before intake.
When proceeding, use repository `{repo}`, exact source `{source}`, root
`comparator.json`, and the responsible author/maintainer relationship for Florian
Lengyel. Recheck current service instructions and registration identity before
intake; do not reuse another project's registry ID or automate browser sign-in.

The actual private service review must be shown to the author, with its digest
and what registration publishes, before final registration. Public-release
approval does not approve an unseen review. Keep service tokens and private
review material out of public Git history.

The author explicitly specified **Palomar Registry registration first, then
arXiv submission**. No arXiv submission has occurred. The Local connectedness in
recursion categories and essential incompleteness project follows arXiv.

## Delivery

Final reports and principal machine evidence are delivered from committed Git
bytes to `/mnt/c/Users/fleng/Downloads`. Differing prior files are preserved.
The official-preflight delivery receipt records exact source commits, repository
paths, Downloads paths and hashes; the evidence source commit does not replace
the verified submission SHA above.
'''
(root/'docs/PALOMAR_OFFICIAL_PREFLIGHT_REPORT.md').write_text(summary)
# Keep only relevant public command records; never copy the raw user-profile API response.
logdir=ev/'logs';logdir.mkdir(exist_ok=True)
for p in (stage/'logs').glob('*.json'):
 if p.name.startswith('authenticated-user-'):continue
 (logdir/p.name).write_bytes(p.read_bytes())
# Reproduction scripts contain no credentials and are evidence, not proof inputs.
tooling=ev/'tooling';tooling.mkdir(exist_ok=True)
for p in Path('/tmp').glob('dp-palomar-official*.py'):(tooling/p.name).write_bytes(p.read_bytes())
save(ev/'ARTIFACT_REGISTER.json',dict(workflow_run_id=rid,artifact_id=result['artifact_id'],original_zip_sha256=zsha,original_json_sha256=rsha,sha256_verified_against_github=True,files=[dict(path=str(p.relative_to(root)),sha256=sha(p.read_bytes()),bytes=p.stat().st_size) for p in sorted(ev.iterdir()) if p.is_file()]))
check_source()
subprocess.run(['git','diff','--check'],cwd=root,check=True)
run(['git','add','AGENTS.md','README.md','docs','provenance/wsl-palomar-registration-20261030/REGISTRATION_STAGE.json','provenance/wsl-palomar-registration-20261030/RELEASE_CANDIDATE.json','provenance/wsl-palomar-official-preflight-20261030'],'stage-official-pass')
raw=[str(p.relative_to(root)) for p in ev.glob('job-*.log')]
if raw:run(['git','add','-f',*raw],'retain-official-job-logs')
run(['git','diff','--cached','--check','--','AGENTS.md','README.md','docs'],'final-public-report-check')
run(['git','commit','-m','Record passing official full Palomar preflight for immutable source'],'commit-official-pass')
commit=git('rev-parse','HEAD');(stage/'FINAL_REPORT_COMMIT.txt').write_text(commit+'\n')
run(['git','push','origin','main'],'push-official-pass')
assert git('status','--porcelain')==''
print(json.dumps(dict(status='pass',report_commit=commit,verified_source=source,workflow_url=url,Lean='accepted',NanoDa='accepted',con_ron='accepted',resource_alarms=0,service_intake='not requested',registration='not performed',arxiv='after Palomar registration'),indent=2),flush=True)
