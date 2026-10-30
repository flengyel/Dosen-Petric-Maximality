exec(Path('/tmp/dp-palomar-common.py').read_text())
import fcntl
with (main/'.codex-work/build.lock').open('a') as build_lock:
 fcntl.flock(build_lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 policy,issues=v.inspect_lean_sources(rc)
 if issues:raise issues[0]
 files=v.lean_source_files(rc);headers={};rows=[]
 for start in range(0,len(files),64):
  batch=files[start:start+64]
  p=v.sandboxed_run([str(bins['lean']),'--deps-json',*map(str,batch)],cwd=rc,environment=base_env,writable_directories=[],readable_paths=[rc,*v.system_readable_paths()],executable_paths=exe,tools=tools)
  entries=json.loads(p.stdout)['imports'];assert len(entries)==len(batch)
  for path,entry in zip(batch,entries,strict=True):
   header=v.parse_lean_header(json.dumps({'imports':[entry]}));assert header.is_module,str(path)
   rel=str(path.relative_to(rc));headers[rel]=list(header.imports)
   b=path.read_bytes();rows.append(dict(path=rel,sha256=sha(b),bytes=len(b),physical_lines=b.count(b'\n')+int(bool(b) and not b.endswith(b'\n')),imports=list(header.imports)))
 save('SOURCE_HEADERS.json',rows)
 def source_closure(root):
  pending=[root];seen=set();local=[];core=[];edges=[]
  while pending:
   mod=pending.pop()
   if mod in seen:continue
   seen.add(mod);rel=mod.replace('.','/')+'.lean'
   if rel in headers:
    local.append(rel)
    for dep in headers[rel]:edges.append([mod,dep]);pending.append(dep)
   else:
    p=prefix/'lib/lean'/(mod.replace('.','/')+'.olean');assert p.is_file(),mod
    core.append(dict(module=mod,sha256=sha(p.read_bytes())))
  return dict(local=sorted(local),trusted_sdk=sorted(core,key=lambda r:r['module']),edges=sorted(edges))
 challenge=source_closure('Challenge');solution=source_closure('Solution')
 assert challenge['local']==['Challenge.lean'] and headers['Challenge.lean']==[]
 assert 'Challenge.lean' not in solution['local'] and all('PalomarCanonical' not in b for _,b in solution['edges'])
 selected_hashes={r['path']:r['sha256'] for r in rows if r['path'] in solution['local'] or r['path']=='Challenge.lean'}
 save('SOURCE_CLOSURES.json',dict(status='pass',challenge=challenge,solution=solution,source_sha256=selected_hashes,dependency_packages=json.loads((rc/'lake-manifest.json').read_text())['packages']))
 files=subprocess.check_output(['git','ls-files','--cached','--others','--exclude-standard','-z'],cwd=rc).decode().split('\0')
 files=sorted({s for s in files if s and (rc/s).is_file()})
 prebuilt=[s for s in files if Path(s).suffix in ['.olean','.ilean','.ir','.o','.a','.so','.dll','.dylib','.bc']]
 symlinks=[s for s in files if (rc/s).is_symlink()]
 submods=[s for s in subprocess.check_output(['git','ls-files','--stage'],cwd=rc,text=True).splitlines() if s.startswith('160000 ')]
 lfs=[]
 for s in files:
  with (rc/s).open('rb') as f:head=f.read(1024)
  if head.startswith(b'version https://git-lfs.github.com/spec/'):lfs.append(s)
 assert not prebuilt and not symlinks and not submods and not lfs
 indexed_lean={s for s in files if s.endswith('.lean')};assert indexed_lean=={r['path'] for r in rows}
 original_manuscripts=subprocess.check_output(['git','ls-tree','-r','--name-only','2c8e096','--','manuscript'],cwd=rc,text=True).splitlines();manuscripts=[]
 for rel in original_manuscripts:
  original=subprocess.check_output(['git','show','2c8e096:'+rel],cwd=rc)
  assert (rc/rel).read_bytes()==original,rel
  manuscripts.append(dict(path=rel,sha256=sha(original)))
 save('PRESERVED_MANUSCRIPTS.json',manuscripts)
 mapping=json.loads((ev/'HISTORICAL_SOURCE_RELOCATIONS.json').read_text())
 for row in mapping['relocations']:
  assert not (rc/row['original']).exists() and sha((rc/row['retained']).read_bytes())==row['sha256']
 save('WHOLE_SOURCE_AUDIT.json',dict(status='pass',policy=policy,regular_lean_files=len(rows),maximum_physical_lines=max(r['physical_lines'] for r in rows),prebuilt_artifacts=prebuilt,symlinks=symlinks,submodules=submods,lfs_pointers=lfs,dependency_packages=0,unchanged_manuscript_files=len(manuscripts),historical_relocations=4,main_head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=main,text=True).strip(),main_status=subprocess.check_output(['git','status','--porcelain'],cwd=main,text=True),stash=subprocess.check_output(['git','stash','list','--format=%H'],cwd=main,text=True).strip()))
 print('PASS:',len(rows),'regular Lean files; compiler-parsed headers, complete local import closures, limits, artifact/LFS/submodule checks and preserved manuscript bytes',flush=True)
