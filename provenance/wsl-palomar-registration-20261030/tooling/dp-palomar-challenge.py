exec(Path('/tmp/dp-palomar-common.py').read_text())
import fcntl
with (main/'.codex-work/build.lock').open('a') as build_lock:
 fcntl.flock(build_lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 if not (ev/'COMPARATOR_TOOL_CONTROLS.json').exists():
  v.comparator_preflight(work,lean=bins['lean'],leanexport=bins['leanexport'],lake=bins['lake'],lean_prefix=prefix,bwrap=bwrap,kernels=kernels,primitives=primitives,environment=base_env,executable_paths=exe,tools=tools,timeout=600,con_ron_binary=bins['con-ron'])
  save('COMPARATOR_TOOL_CONTROLS.json',dict(status='pass'))
 print('Compiling independent core-only Challenge; completed tool controls retained',flush=True)
 config=v.protected_comparator_config(rc/'comparator.json',work/'protected-comparator.json',kernels=kernels)
 alias=json.loads(config.read_text())['challenge_module']
 canonical,deps,leanpaths=v.compile_canonical_challenge(work,rc,checkout=rc,challenge_module='Challenge',published_module=alias,lean=bins['lean'],lean_prefix=prefix,allowlist={},environment=base_env,readable_paths=readable,executable_paths=exe,tools=tools)
 assert not any(p.is_relative_to(rc) and p.resolve()!=(rc/'Challenge.lean').resolve() for p in deps)
 j=dict(status='pass',module=alias,canonical=str(canonical),dependencies=[str(p) for p in deps],trusted_lean_paths=[str(p) for p in leanpaths],artifacts=[dict(path=str(p),sha256=sha(p.read_bytes())) for p in v.canonical_challenge_artifacts(canonical,module_system=True)],source_sha256=sha((rc/'Challenge.lean').read_bytes()),independent_core_only=True)
 save('CANONICAL_CHALLENGE.json',j)
 save('TOOL_DIGESTS.json',v.tool_digests(bins,bwrap))
 print(json.dumps(j),flush=True)
