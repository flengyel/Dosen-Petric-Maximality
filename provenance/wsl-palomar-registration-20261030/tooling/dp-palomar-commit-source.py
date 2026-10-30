# Freeze all submission inputs and reports on the isolated private branch.
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=rc,text=True).strip()=='2c8e0968ad4fa3d318b98bcab4e531bb728b86cd'
assert subprocess.check_output(['git','branch','--show-current'],cwd=rc,text=True).strip()=='palomar/registration-20261030'
source=json.loads((ev/'SOURCE_CLOSURES.json').read_text())
assert all(sha((rc/p).read_bytes())==h for p,h in source['source_sha256'].items())
assert json.loads((ev/'FINAL_EXPORT_IDENTITY.json').read_text())['byte_identical']
command(['git','add','-A'],'stage-final-candidate',lock=False)
raw=[str(p.relative_to(rc)) for p in (ev/'logs').glob('*.log')]
if raw:command(['git','add','-f',*raw],'retain-full-raw-logs',lock=False)
command(['git','diff','--cached','--check','--','.',':(exclude)provenance/**'],'final-diff-check',lock=False)
command(['git','commit','-m','Prepare independently verified Palomar maximality release candidate'],'commit-source',lock=False)
commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=rc,text=True).strip()
(stage/'SOURCE_COMMIT.txt').write_text(commit+'\n')
for p,h in source['source_sha256'].items():assert sha(subprocess.check_output(['git','show',commit+':'+p],cwd=rc))==h
assert subprocess.check_output(['git','stash','list','--format=%H'],cwd=main,text=True).strip()=='dedfd8fc8cd49930e9a162d5be585215b062a43c'
assert not subprocess.check_output(['git','status','--porcelain'],cwd=main,text=True).strip()
print('Verified immutable candidate:',commit,flush=True)
command(['git','push','-u','origin','HEAD:refs/heads/palomar/registration-20261030'],'push-private-candidate',lock=False)
remote=subprocess.check_output(['git','ls-remote','origin','refs/heads/palomar/registration-20261030'],cwd=rc,text=True).split()[0]
assert remote==commit
print('Private candidate pushed and exact remote SHA verified:',commit,flush=True)
