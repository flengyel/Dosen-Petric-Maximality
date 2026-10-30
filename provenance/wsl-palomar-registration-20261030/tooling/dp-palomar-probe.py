exec(Path('/tmp/dp-palomar-common.py').read_text())
root=work/'comparator-preflight'
vv=dict(base_env,HOME=str(root/'home'),TMPDIR=str(root/'tmp'),LEAN_PATH=os.pathsep.join([str(root/'lib'),str(prefix/'lib/lean')]))
p=v.export_module('PalomarPreflightChallenge',v.comparator_export_targets(json.loads((root/'comparator.json').read_text()),primitives),output=root/'exports/Challenge-diagnostic.export',leanexport=bins['leanexport'],cwd=root,environment=vv,readable_paths=sorted({root.resolve(),*v.system_readable_paths()}),executable_paths=exe,tools=tools,timeout=600)
print(p.returncode,p.stdout,p.stderr,flush=True)
save('FIRST_PROTECTED_EXPORT_DIAGNOSTIC.json',dict(exit_status=p.returncode,stdout=p.stdout,stderr=p.stderr))
