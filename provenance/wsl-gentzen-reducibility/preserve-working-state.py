from pathlib import Path
import os,subprocess,datetime,json,hashlib,shutil
r=Path('/home/flengyel/src/Dosen-Petric-Maximality')
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
out=r/'.codex-work/reducibility-reconciliation'/stamp;out.mkdir(parents=True)
def git(*a,cwd=r):return subprocess.check_output(['git',*a],cwd=cwd).decode()
def sha(b):return hashlib.sha256(b).hexdigest()
for label,args in [('status',['status','--porcelain=v2','--branch']),('unstaged',['diff','--binary']),('staged',['diff','--cached','--binary']),('worktrees',['worktree','list','--porcelain']),('stashes',['stash','list','--format=%H %s']),('log',['log','-12','--format=%H %s']),('remotes',['remote','-v'])]:
 (out/(label+'.txt')).write_text(git(*args))
files=[]
for raw in subprocess.check_output(['git','ls-files','--others','--exclude-standard','-z'],cwd=r).split(b'\0'):
 if not raw:continue
 p=Path(os.fsdecode(raw));src=r/p;dest=out/'untracked'/p;dest.parent.mkdir(parents=True,exist_ok=True)
 shutil.copy2(src,dest);b=src.read_bytes();assert dest.read_bytes()==b
 files.append(dict(path=str(p),bytes=len(b),sha256=sha(b)))
tracked=[]
for raw in subprocess.check_output(['git','ls-files','-z'],cwd=r).split(b'\0'):
 if raw:
  p=Path(os.fsdecode(raw));tracked.append(dict(path=str(p),sha256=sha((r/p).read_bytes())))
(out/'tracked-inventory.json').write_text(json.dumps(tracked,indent=2)+'\n')
draft=Path('/tmp/dp-blocked-exploratory-alternate')
if draft.is_dir():
 shutil.copytree(draft,out/'alternate-exploration')
 p=Path('/tmp/dp-blocked-principal-first-draft.lean')
 if p.exists():shutil.copy2(p,out/'alternate-exploration'/p.name)
processes=[]
for proc in Path('/proc').iterdir():
 if not proc.name.isdigit():continue
 try:
  comm=(proc/'comm').read_text().strip();cwd=os.readlink(proc/'cwd')
  if comm not in ['codex','node','bash','lean','lake','python3']:continue
  if not (cwd.startswith(str(r)) or comm=='codex'):continue
  args=(proc/'cmdline').read_bytes().split(b'\0');words=[os.fsdecode(x) for x in args if x]
  role=''
  if comm=='codex':role='Codex server' if 'app-server' in words else 'Codex CLI'
  elif comm=='node':role='VS Code process' if any('vscode' in x.lower() for x in words) else 'Node process'
  elif comm in ['lean','lake']:role='Lean verification'
  else:role='shell/helper'
  processes.append(dict(pid=int(proc.name),comm=comm,cwd=cwd,role=role))
 except (PermissionError,FileNotFoundError,ProcessLookupError):pass
checkouts=[]
for p in [r,Path('/tmp/dp-blocked-candidate-20261024T2228')]:
 if (p/'.git').exists():
  checkouts.append(dict(path=str(p),head=git('rev-parse','HEAD',cwd=p).strip(),status=git('status','--short',cwd=p)))
receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),repository=str(r),head=git('rev-parse','HEAD').strip(),untracked=files,tracked_diff_empty=git('diff')=='' and git('diff','--cached')=='',process_workdirs=processes,checkouts=checkouts,backup_stashes=git('stash','list','--format=%H %s').splitlines(),actions='Read/copy only; no reset, clean, overwrite, staging, commit or process interruption',snapshot=str(out))
(out/'reconciliation.json').write_text(json.dumps(receipt,indent=2)+'\n')
Path('/tmp/dp-reducibility-reconciliation-latest.txt').write_text(str(out)+'\n')
print(json.dumps(receipt,indent=2))
