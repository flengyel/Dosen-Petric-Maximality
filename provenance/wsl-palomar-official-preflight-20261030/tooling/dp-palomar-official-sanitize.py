# Remove sensitive repository metadata without changing proof inputs or history.
check_source()
assert git('status','--porcelain')==''
logrel='provenance/wsl-palomar-official-preflight-20261030/logs/repository-before-20261030T211223140602.json'
p=root/logrel
row=json.loads(p.read_text());payload=json.loads(row['stdout']);secret=payload['temp_clone_token']
assert isinstance(secret,str) and secret and len(secret)==29
first_commit=git('log','--diff-filter=A','--format=%H','--',logrel).splitlines()[0]
first_time=git('show','-s','--format=%cI',first_commit)
logged=datetime.datetime.fromisoformat(row['utc']);published=datetime.datetime.fromisoformat(first_time)
assert logged+datetime.timedelta(minutes=5)<published
tracked=git('ls-files','-z').split('\0')
matches=[f for f in tracked if f and (root/f).is_file() and secret.encode() in (root/f).read_bytes()]
assert matches==[logrel],matches
sensitive={'token','access_token','refresh_token','temp_clone_token','client_secret','authorization','password'}
def redact(x):
 if isinstance(x,dict):return {k:('[REDACTED]' if k.lower() in sensitive and v else redact(v)) for k,v in x.items()}
 if isinstance(x,list):return [redact(v) for v in x]
 return x
for target in [p,stage/'logs'/p.name]:
 x=json.loads(target.read_text());x['stdout']=json.dumps(redact(json.loads(x['stdout'])),separators=(',',':'))+'\n'
 x['sensitive_metadata_redacted']=['temp_clone_token'];save(target,x)
# Sanitize command-capture JSON before it reaches a durable log in future runs.
runner=Path('/tmp/dp-palomar-official.py')
t=runner.read_text()
old="def run(argv,label,stdin=None,check=True):\n"
new='''def redact_capture(value):
 sensitive={'token','access_token','refresh_token','temp_clone_token','client_secret','authorization','password'}
 def walk(x):
  if isinstance(x,dict):return {k:('[REDACTED]' if k.lower() in sensitive and v else walk(v)) for k,v in x.items()}
  if isinstance(x,list):return [walk(v) for v in x]
  return x
 try:return json.dumps(walk(json.loads(value)),separators=(',',':'))+'\\n'
 except (ValueError,TypeError):return value

def run(argv,label,stdin=None,check=True):
'''
assert old in t;t=t.replace(old,new,1)
old='stdout=p.stdout,stderr=p.stderr,utc=now())'
assert old in t;t=t.replace(old,'stdout=redact_capture(p.stdout),stderr=redact_capture(p.stderr),utc=now())',1)
runner.write_text(t)
(ev/'tooling'/runner.name).write_bytes(runner.read_bytes())
(ev/'tooling'/'dp-palomar-official-sanitize.py').write_bytes(Path('/tmp/dp-palomar-official-sanitize.py').read_bytes())
# Explain the actual scope and dates; never record the credential or its hash.
text=f'''# Official-preflight metadata correction

A final evidence audit found a nonempty `temp_clone_token` field in one retained
GitHub repository-metadata command log. That response was mistakenly included
with public provenance. The field is now redacted in the current repository and
local staging copies, and the capture helper now redacts credential fields in
JSON before writing command logs.

GitHub's [Get a repository documentation](https://docs.github.com/en/rest/repos/repos#get-a-repository)
states that this credential grants read-only Git access to that repository,
expires five minutes after generation, and cannot push changes. The response
was logged at `{row['utc']}`. Its first public commit was
`{first_commit}` at `{first_time}`, more than eighteen minutes later.
Under that documented lifetime it had already expired before the commit that
published the log. No claim of independent token revocation or testing is made;
the value was neither printed nor used during this audit.

The audit searched every tracked current file for the discovered value and
found it only in that metadata log. After redaction it appears in no tracked
current file. The expired value remains in historical commit `{first_commit}`;
history was preserved without a reset or force-push. The Windows GitHub CLI
account credential was not included in the metadata field or extracted by this
process. This correction does not change the proof source, any Comparator
input, the official report, or the downloaded official ZIP.

Immutable submission: `{source}`.
Official mechanical JSON SHA-256:
`b21cdb78ae39b47b11e96be06a388787cd8d6d8ace045e4d403fb50cd14db8c9`.
Official artifact ZIP SHA-256:
`d6b0921b4b8d6b237a39c8d47e760fbb3a47b435877ff59dcd6d06a3957e36ff`.

No Palomar service token, intake, private review or registration was involved.
Publication order remains Palomar registration first, then arXiv.
'''
(root/'docs/PALOMAR_PREFLIGHT_METADATA_CORRECTION.md').write_text(text)
p=root/'docs/PALOMAR_OFFICIAL_PREFLIGHT_REPORT.md';t=p.read_text()
t=t.replace('remain preserved; the registry selection is the five-statement maximality family\nand its two structural witnesses.','remain preserved; the five selected statements are the two maximality routes,\nthe maximality dichotomy, and two structural witnesses.')
t=t.replace('## Delivery\n','## Metadata correction\n\nOne temporary clone-credential field in a repository-metadata log was redacted\nafter the final audit. GitHub documents a five-minute lifetime; the credential\nhad expired before the log was committed. The original official report and ZIP\nremain byte-identical. See [the correction record](PALOMAR_PREFLIGHT_METADATA_CORRECTION.md).\n\n## Delivery\n')
p.write_text(t)
for f in tracked:
 if f and (root/f).is_file():assert secret.encode() not in (root/f).read_bytes(),f
assert sha((ev/'mechanical-report.json').read_bytes())=='b21cdb78ae39b47b11e96be06a388787cd8d6d8ace045e4d403fb50cd14db8c9'
assert sha((ev/'mechanical-report.zip').read_bytes())=='d6b0921b4b8d6b237a39c8d47e760fbb3a47b435877ff59dcd6d06a3957e36ff'
check_source()
run(['git','diff','--check'],'check-metadata-correction')
run(['git','add',logrel,'docs/PALOMAR_PREFLIGHT_METADATA_CORRECTION.md','docs/PALOMAR_OFFICIAL_PREFLIGHT_REPORT.md',str((ev/'tooling').relative_to(root))],'stage-metadata-correction')
run(['git','commit','-m','Redact expired clone metadata and document evidence correction'],'commit-metadata-correction')
commit=git('rev-parse','HEAD');(stage/'FINAL_REPORT_COMMIT.txt').write_text(commit+'\n')
run(['git','push','origin','main'],'push-metadata-correction')
assert git('status','--porcelain')==''
print(json.dumps(dict(correction_commit=commit,credential_current_tree_matches=0,expired_before_first_commit=True,history_preserved=True,submission_source=source,official_artifact_bytes_unchanged=True)),flush=True)
