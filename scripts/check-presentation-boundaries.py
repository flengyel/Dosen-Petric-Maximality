#!/usr/bin/env python3
"""Check that two tempting boundary violations remain ill typed or unproved."""
from pathlib import Path
import hashlib, json, os, subprocess
root = Path(__file__).resolve().parent.parent
out = root / '.codex-work/presentation-bridge/presentation-controls'
out.mkdir(parents=True, exist_ok=True)
prefix = '''module
import DosenPetric
open DosenPetric DosenPetric.Presentation
'''
controls = {
    'identified-projections': (
        'example : fst (.var ()) (.var ()) = snd (.var ()) (.var ()) := by rfl\n',
        'Tactic `rfl` failed'),
    'zero-without-arrow-witness': (
        'example : Hom (P := Unit) .top .bot := (zeroIdentity Unit).zeroOf ((category Unit).id .top)\n',
        'Type mismatch'),
}
rows = []
for name, (body, expected) in controls.items():
    source = out / (name + '.lean')
    source.write_text(prefix + body)
    command = ['lake', 'env', 'lean', '-DwarningAsError=true', str(source)]
    run = subprocess.run(command, cwd=root, env=dict(os.environ, LEAN_NUM_THREADS='1'),
                         text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = out / (name + '.log')
    log.write_text(run.stdout)
    passed = run.returncode != 0 and expected.lower() in run.stdout.lower()
    rows.append(dict(name=name, command=command, exit_status=run.returncode,
                     expected=expected, passed=passed,
                     source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                     log_sha256=hashlib.sha256(log.read_bytes()).hexdigest()))
    print(name, 'PASS (rejected)' if passed else 'FAIL', run.returncode)
    if not passed:
        raise SystemExit(run.stdout)
(out / 'report.json').write_text(json.dumps(rows, indent=2) + '\n')
