check_source()
assert git('status','--porcelain')==''
commit=git('rev-parse','HEAD');assert commit=='9309c0d949f7754fbe2451c56cf2cfd9de9bb5d1'
downloads=Path('/mnt/c/Users/fleng/Downloads');assert downloads.is_dir()
def blob(rev,path):return subprocess.check_output(['git','show',rev+':'+path],cwd=root)
def destination(name,data):
 p=downloads/name
 if not p.exists() or p.read_bytes()==data:return p
 p=downloads/(Path(name).stem+'-20261030-'+commit[:7]+Path(name).suffix)
 if p.exists() and p.read_bytes()!=data:
  p=downloads/(Path(name).stem+'-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%f')+Path(name).suffix)
 assert not p.exists() or p.read_bytes()==data
 return p
def deliver(rev,path,name=None):
 data=blob(rev,path);dest=destination(name or Path(path).name,data)
 existed=dest.exists()
 if not existed:
  with dest.open('xb') as f:f.write(data)
 assert dest.read_bytes()==data
 return dict(repository_path=path,source_commit=rev,downloads_path=str(dest),sha256=sha(data),bytes=len(data),byte_verified=True,already_identical=existed)
paths=['AGENTS.md','README.md','docs/CODEX_NEXT_SESSION.txt','docs/PALOMAR_RELEASE_CANDIDATE.md','docs/PALOMAR_REGISTRATION_STATUS.md','docs/PALOMAR_REGISTRATION_LOCAL_REPORT.md','docs/PALOMAR_OFFICIAL_PREFLIGHT_REPORT.md','docs/PALOMAR_PREFLIGHT_METADATA_CORRECTION.md']
for name in ['RELEASE_AUTHORIZATION.json','PUBLIC_RELEASE.json','DISPATCH_REQUEST.json','DISPATCH_ACCEPTED.json','WORKFLOW_RUN.json','WORKFLOW_JOBS.json','WORKFLOW_ARTIFACTS.json','mechanical-report.json','mechanical-report.zip','MECHANICAL_RESULT.json','OFFICIAL_PREFLIGHT_STAGE.json','ARTIFACT_REGISTER.json']:
 paths.append(str((ev/name).relative_to(root)))
for name in ['REGISTRATION_STAGE.json','RELEASE_CANDIDATE.json']:
 paths.append('provenance/wsl-palomar-registration-20261030/'+name)
rows=[deliver(commit,p) for p in paths]
assert len(rows)==22
receipt_md=root/'docs/PALOMAR_OFFICIAL_PREFLIGHT_DELIVERY.md'
receipt_json=ev/'DELIVERY_REGISTER.json'
# Unique names selected before commit. Preserve any differing earlier receipt.
md_name='Dosen-Petric-Palomar-Official-Preflight-Delivery-20261030-'+commit[:7]+'.md'
json_name='Dosen-Petric-Palomar-Official-Preflight-Delivery-20261030-'+commit[:7]+'.json'
for name in [md_name,json_name]:assert not (downloads/name).exists(),name
save(receipt_json,dict(utc=now(),verified_submission_commit=source,evidence_source_commit=commit,workflow_run_id=41129351329,workflow_url='https://github.com/flengyel/Dosen-Petric-Maximality/actions/runs/41129351329',official_full_preflight='pass',service_intake='not performed',registration='not performed',arxiv='after Palomar registration; not submitted',copy_policy='Committed Git blobs only; SHA-256 and bytes checked; differing earlier files preserved.',files=rows,receipt_downloads_paths=[str(downloads/md_name),str(downloads/json_name)],receipt_policy='Both receipts are copied and byte-verified after their own commit; that final verification is retained in ignored local staging to avoid a self-referential manifest.'))
t='''# Official full Palomar preflight delivery receipt

Official full preflight passed at [run 41129351329](https://github.com/flengyel/Dosen-Petric-Maximality/actions/runs/41129351329).
Immutable verified proof source: `'''+source+'''`.
Delivered evidence and report source: `'''+commit+'''` on main.
No Palomar service intake or registration has occurred. Palomar registration
precedes arXiv, as the author specified.

All 22 files below were read from committed Git blobs and copied to Downloads.
Every copy was compared byte for byte and by SHA-256. Differing earlier files
were preserved using dated or commit-suffixed names. The two receipt files are
also delivered from their own subsequent commit and byte-verified; their final
verification is retained locally to avoid a self-referential manifest.

Repository copies remain under `/home/flengyel/src/Dosen-Petric-Maximality/`.
The JSON register records each file's exact source SHA, size and SHA-256.

| Repository path | Verified Downloads path |
| --- | --- |
'''
for row in rows:t+='| `'+row['repository_path']+'` | `'+row['downloads_path']+'` |\n'
t+='\nReceipt copies:\n\n- `'+str(downloads/md_name)+'`\n- `'+str(downloads/json_name)+'`\n'
t+='\nRetained receipt paths:\n\n- `docs/PALOMAR_OFFICIAL_PREFLIGHT_DELIVERY.md`\n- `provenance/wsl-palomar-official-preflight-20261030/DELIVERY_REGISTER.json`\n'
receipt_md.write_text(t)
# Keep the exact delivery implementation with the evidence.
(ev/'tooling'/'dp-palomar-official-deliver.py').write_bytes(Path('/tmp/dp-palomar-official-deliver.py').read_bytes())
run(['git','diff','--check'],'check-official-delivery-receipt')
run(['git','add',str(receipt_md.relative_to(root)),str(receipt_json.relative_to(root)),str((ev/'tooling'/'dp-palomar-official-deliver.py').relative_to(root))],'stage-official-delivery-receipt')
run(['git','commit','-m','Record byte-verified official-preflight Downloads deliveries'],'commit-official-delivery-receipt')
receipt_commit=git('rev-parse','HEAD')
run(['git','push','origin','main'],'push-official-delivery-receipt')
receipt_rows=[deliver(receipt_commit,str(receipt_md.relative_to(root)),md_name),deliver(receipt_commit,str(receipt_json.relative_to(root)),json_name)]
for row in rows+receipt_rows:
 assert (root/row['repository_path']).read_bytes()==blob(row['source_commit'],row['repository_path'])
 assert (downloads/Path(row['downloads_path']).name).read_bytes()==blob(row['source_commit'],row['repository_path'])
check_source();assert git('status','--porcelain')==''
assert git('rev-list','--left-right','--count','main...origin/main')=='0\t0'
remote=run(['git','ls-remote','origin','refs/heads/main'],'final-main-remote').stdout.split()[0]
assert remote==receipt_commit
save(stage/'FINAL_DELIVERY_VERIFICATION.json',dict(utc=now(),receipt_commit=receipt_commit,evidence_source_commit=commit,verified_submission_commit=source,all_deliveries=rows+receipt_rows,count=24,source_preserved=True,stash_preserved=True,main_clean=True,origin_main=remote))
print(json.dumps(dict(receipt_commit=receipt_commit,evidence_source_commit=commit,verified_submission_commit=source,byte_verified_deliveries=24,principal_report=next(r for r in rows if r['repository_path']=='docs/PALOMAR_OFFICIAL_PREFLIGHT_REPORT.md'),metadata_correction=next(r for r in rows if r['repository_path']=='docs/PALOMAR_PREFLIGHT_METADATA_CORRECTION.md'),receipt_downloads=receipt_rows,stash_preserved=True,main_clean=True,origin_main=remote),indent=2),flush=True)
