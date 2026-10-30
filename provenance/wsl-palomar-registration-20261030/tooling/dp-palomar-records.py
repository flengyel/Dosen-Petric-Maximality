exec(Path('/tmp/dp-palomar-common.py').read_text())
actual=json.loads((ev/'CANONICAL_CHALLENGE.json').read_text())
positive=v.audit_challenge_sources(rc,checkout=rc,dependency_sources=[Path(p) for p in actual['dependencies']],lean_prefix=prefix,allowlist={},writable_directories=[])
assert not positive['untrusted_sources']
controls=json.loads((ev/'PACKAGE_CONTROLS.json').read_text())
negative=[]
for row in controls['controls']:
 if row['name'] in ['DirectForbiddenImport','TransitiveForbiddenImport']:
  paths=[rc/'DosenPetric/Formula.lean']
  if row['name']=='TransitiveForbiddenImport':paths.insert(0,work/'package-controls-v2/TransitiveForbiddenImport/Bridge.lean')
  check=v.audit_challenge_sources(rc,checkout=rc,dependency_sources=paths,lean_prefix=prefix,allowlist={},writable_directories=[])
  assert check['untrusted_sources'] and str(rc/'DosenPetric/Formula.lean') in check['untrusted_sources']
  row['official_source_policy_result']=check
  negative.append(dict(name=row['name'],result=check))
save('PACKAGE_CONTROLS.json',controls)
save('CHALLENGE_SOURCE_POLICY.json',dict(status='pass',actual_challenge=positive,negative_controls=negative,official_policy_pin=up.name))
# Preserve exact captured command streams, successful and failed attempts alike.
dst=ev/'logs';dst.mkdir(exist_ok=True)
recursion=[]
for p in logs.iterdir():
 if not p.is_file():continue
 if p.suffix=='.json':
  try:row=json.loads(p.read_text())
  except ValueError:row={}
  if 'maximum recursion depth' in str(row.get('error','')):
   recursion.append(p);continue
 (dst/p.name).write_bytes(p.read_bytes())
if recursion:
 import tarfile,io
 target=ev/'attempts/logging-wrapper-recursion';target.mkdir(parents=True,exist_ok=True)
 archive=target/'logs.tar.gz';index=[]
 with tarfile.open(archive,'w:gz') as tar:
  for p in sorted(recursion):
   blob=p.read_bytes();entry=tarfile.TarInfo(p.name);entry.size=len(blob);entry.mtime=0;entry.mode=0o644;tar.addfile(entry,io.BytesIO(blob))
   index.append(dict(member=p.name,sha256=sha(blob),bytes=len(blob)))
 with tarfile.open(archive,'r:gz') as tar:
  for r in index:assert sha(tar.extractfile(r['member']).read())==r['sha256']
 save('LOG_ARCHIVE_REGISTER.json',dict(archive=str(archive.relative_to(rc)),sha256=sha(archive.read_bytes()),reason='Repeated initialization of the local logging adapter caused self-recursion before a source-header subprocess launched. Idempotent initialization fixed; final source audit rerun separately passed.',members=index,all_original_log_bytes_verified=True))
# Source-path records distinguish local scratch from retained committed evidence.
register=[]
for p in sorted(dst.iterdir()):register.append(dict(path=str(p.relative_to(rc)),sha256=sha(p.read_bytes()),bytes=p.stat().st_size))
save('LOG_REGISTER.json',register)
dst=ev/'tooling';dst.mkdir(exist_ok=True)
for p in sorted(Path('/tmp').glob('dp-palomar-*.py')):(dst/p.name).write_bytes(p.read_bytes())
# Every copied production/library input matches the source closure that was checked.
source_closure=json.loads((ev/'SOURCE_CLOSURES.json').read_text())
assert all(sha((rc/path).read_bytes())==digest for path,digest in source_closure['source_sha256'].items())
assert subprocess.check_output(['git','stash','list','--format=%H'],cwd=main,text=True).strip()=='dedfd8fc8cd49930e9a162d5be585215b062a43c'
assert not subprocess.check_output(['git','status','--porcelain'],cwd=main,text=True).strip()
print('Official source-policy positive/negative checks passed; full command streams and tooling retained; checked source bytes and stash unchanged')

p=rc/'docs/history/PALOMAR_REGISTRATION_STATUS_2C8E096.md'
p.write_bytes(subprocess.check_output(['git','show','2c8e096:docs/PALOMAR_REGISTRATION_STATUS.md'],cwd=rc))
