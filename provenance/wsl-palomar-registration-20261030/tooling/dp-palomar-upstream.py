import sys
up=main/'.codex-work/upstream/PalomarSubmission-14aa8d6b3c2f14a8540605e37144560b9a00e7e7'
sys.path.insert(0,str(up))
from scripts.checker_updates import materialize_checker
prefix=Path('/home/flengyel/.elan/toolchains/leanprover--lean4---v4.35.0')
bundled=prefix/'bin/con-ron';original=sha(bundled.read_bytes())
os.environ['PATH']=str(stage/'tooling/zstd/usr/bin')+os.pathsep+os.environ['PATH']
dest=stage/'checkers/con-ron-v4.36.0-rc1-authenticated'
if not dest.exists():
 binary,provenance=materialize_checker('leanprover/lean4:v4.35.0',bundled,dest)
else:
 binary=dest/'con-ron';provenance=json.loads((ev/'CON_RON_CHECKER.json').read_text())['provenance']
assert sha(binary.read_bytes())=='4e5616d94374cae37324dad2594f6230c2bb2297240249fc78ff508f3bc5acef'
assert sha(bundled.read_bytes())==original
j=dict(executable=str(binary),sha256=sha(binary.read_bytes()),provenance=provenance,bundled_sha256=original,bundled_unchanged=True,global_toolchain_modified=False)
ev.mkdir(parents=True,exist_ok=True);(ev/'CON_RON_CHECKER.json').write_text(json.dumps(j,indent=2)+'\n')
revisions={}
for repo in ['PalomarRegistry/PalomarSubmission','PalomarRegistry/PalomarPolicy','mathlib-initiative/formalization.yaml']:
 p=subprocess.run(['git','ls-remote','https://github.com/'+repo+'.git','HEAD'],capture_output=True,text=True)
 revisions[repo]=dict(exit_status=p.returncode,head=p.stdout.split()[0] if p.returncode==0 else None,error=p.stderr.strip())
(ev/'UPSTREAM_RECHECK.json').write_text(json.dumps(revisions,indent=2)+'\n')
print(json.dumps(dict(checker=j,upstream=revisions),indent=2))
