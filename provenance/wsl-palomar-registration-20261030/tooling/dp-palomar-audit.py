import re
files=subprocess.check_output(['git','ls-files','-z'],cwd=rc).decode().split('\0');files=[x for x in files if x]
lean=[x for x in files if x.endswith('.lean')]
bad=[]
for rel in lean:
 p=rc/rel;b=p.read_bytes();lines=b.count(b'\n')+(not b.endswith(b'\n'))
 if p.is_symlink() or lines>10000 or not b.startswith(b'module\n'):
  bad.append(dict(path=rel,lines=lines,module_header=b.startswith(b'module\n'),symlink=p.is_symlink(),sha256=sha(b)))
prebuilt=[x for x in files if Path(x).suffix in ['.olean','.ilean','.o','.a','.so','.dll','.dylib']]
submodules=[t for t in subprocess.check_output(['git','ls-files','--stage'],cwd=rc,text=True).splitlines() if t.startswith('160000 ')]
lfs=[]
for rel in files:
 p=rc/rel
 if p.is_file() and p.stat().st_size<4096 and p.read_bytes().startswith(b'version https://git-lfs.github.com/spec/'):lfs.append(rel)
ev.mkdir(parents=True,exist_ok=True)
j=dict(tracked_lean_files=len(lean),invalid_regular_lean=bad,prebuilt_artifacts=prebuilt,submodules=submodules,lfs_pointers=lfs,stash=subprocess.check_output(['git','stash','list','--format=%H'],cwd=main,text=True).strip())
(ev/'INITIAL_SOURCE_AUDIT.json').write_text(json.dumps(j,indent=2)+'\n')
print(json.dumps(j,indent=2))
