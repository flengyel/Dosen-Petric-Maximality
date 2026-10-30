import shutil,sys,traceback
up=main/'.codex-work/upstream/PalomarSubmission-14aa8d6b3c2f14a8540605e37144560b9a00e7e7'
sys.path.insert(0,str(up))
from scripts import verify_submission as v
prefix=Path('/home/flengyel/.elan/toolchains/leanprover--lean4---v4.35.0')
bwrap=Path(shutil.which('bwrap')).resolve();v._BWRAP=bwrap
bins=v.toolchain_tools(prefix)
bins['con-ron']=stage/'checkers/con-ron-v4.36.0-rc1-authenticated/con-ron'
tools={p:sha(p.read_bytes()) for p in [*bins.values(),bwrap]}
base_env={**os.environ,'LEAN_NUM_THREADS':'1','LEAN_ABORT_ON_PANIC':'1','PATH':str(prefix/'bin')+os.pathsep+'/usr/bin:/bin'}
exe=[prefix,Path('/usr'),Path('/bin').resolve(),Path('/lib').resolve(),Path('/lib64').resolve(),bwrap]
readable=[rc,*v.system_readable_paths()]
kernels={k:val for k,val in v.protected_kernels(bins).items() if k!='con-ron'}
primitives=v.primitive_targets(prefix)
work=stage/'verification-v2';work.mkdir(exist_ok=True)
def save(name,j):
 (ev/name).write_text(json.dumps(j,indent=2,default=str)+'\n')
def proc_record(name,proc):
 log=logs/(name+'.log');log.write_text(proc.stdout+'\n'+proc.stderr)
 j=dict(exit_status=proc.returncode,log=str(log.relative_to(main)),sha256=sha(log.read_bytes()))
 save(name+'.json',j);return j
# Record unabridged captured phase streams and commands without changing any verifier result.
_original_run=getattr(v,'_dp_original_run',v.run)
v._dp_original_run=_original_run
def logged_run(argv,_run_impl=_original_run,**kwargs):
 start=time.monotonic();stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%f')
 p=logs/('protected-'+stamp+'.json')
 try:
  proc=_run_impl(argv,**kwargs)
  p.write_text(json.dumps(dict(command=argv,cwd=str(kwargs.get('cwd')),exit_status=proc.returncode,seconds=round(time.monotonic()-start,3),stdout=proc.stdout,stderr=proc.stderr),indent=2)+'\n')
  return proc
 except Exception as e:
  p.write_text(json.dumps(dict(command=argv,cwd=str(kwargs.get('cwd')),seconds=round(time.monotonic()-start,3),error=str(e),detail=getattr(e,'detail',None)),indent=2)+'\n');raise
v.run=logged_run
