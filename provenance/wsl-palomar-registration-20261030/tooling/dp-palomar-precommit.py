# No production input has changed since the passing source and kernel checks.
closure=json.loads((ev/'SOURCE_CLOSURES.json').read_text())
assert all(sha((rc/p).read_bytes())==h for p,h in closure['source_sha256'].items())
assert subprocess.check_output(['git','branch','--show-current'],cwd=rc,text=True).strip()=='palomar/registration-20261030'
command(['git','add','-A'],'stage-candidate',lock=False)
logfiles=[str(p.relative_to(rc)) for p in (ev/'logs').glob('*.log')]
if logfiles:command(['git','add','-f',*logfiles],'stage-raw-verification-logs',lock=False)
p=subprocess.run(['git','diff','--cached','--check','--','.',':(exclude)provenance/**'],cwd=rc,capture_output=True,text=True)
print('Whitespace check:',p.returncode,p.stdout,p.stderr,flush=True)
rows=subprocess.check_output(['git','diff','--cached','--name-status'],cwd=rc,text=True)
print('Staged',len(rows.splitlines()),'paths; mathematical source, wrappers, metadata, reports, mapped historical fixtures and evidence',flush=True)
old_check=ev/'STAGED_DIFF_CHECK.json'
if old_check.exists() and json.loads(old_check.read_text()).get('exit_status'):
 archive=ev/'attempts/staged-whitespace';archive.mkdir(parents=True,exist_ok=True);(archive/'STAGED_DIFF_CHECK.json').write_bytes(old_check.read_bytes())
(ev/'STAGED_DIFF_CHECK.json').write_text(json.dumps(dict(exit_status=p.returncode,stdout=p.stdout,stderr=p.stderr,scope='Production source, docs, configuration and scripts; byte-preserved provenance excluded'),indent=2)+'\n')
if p.returncode:raise SystemExit(p.returncode)
