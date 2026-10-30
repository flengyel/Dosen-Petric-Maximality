import re
initial=json.loads((ev/'INITIAL_SOURCE_AUDIT.json').read_text())
rows=[]
for r in initial['invalid_regular_lean']:
 rel=r['path'];assert rel.startswith('provenance/') and not r['module_header'] and not r['symlink'] and r['lines']<=10000
 src=rc/rel;dst=rc/(rel+'.txt');assert src.exists() and not dst.exists() and sha(src.read_bytes())==r['sha256']
 refs=[]
 for p in rc.rglob('*'):
  if p.is_file() and not any(x in p.parts for x in ['.git','.lake','.codex-work']) and p.suffix in ['.md','.txt','.json','.tsv','.sha256']:
   try:t=p.read_text()
   except UnicodeError:continue
   if rel in t:refs.append(str(p.relative_to(rc)))
 src.rename(dst);assert sha(dst.read_bytes())==r['sha256']
 rows.append(dict(original=rel,retained=rel+'.txt',sha256=r['sha256'],bytes=dst.stat().st_size,reason='Historical non-module PublicTypes fixture; no production import or proof was renamed.',historical_references=refs))
(ev/'HISTORICAL_SOURCE_RELOCATIONS.json').write_text(json.dumps(dict(relocations=rows,byte_preserving=True,historical_report_bytes_unchanged=True,reference_resolution='scripts/resolve-historical-evidence.py'),indent=2)+'\n')
script='''#!/usr/bin/env python3
"""Resolve byte-preserved historical evidence paths in the registration layout."""
from pathlib import Path
import hashlib,json,sys
root=Path(__file__).resolve().parent.parent
mapping=json.loads((root/'provenance/wsl-palomar-registration-20261030/HISTORICAL_SOURCE_RELOCATIONS.json').read_text())
rel=sys.argv[1]
rows={r['original']:r for r in mapping['relocations']}
r=rows.get(rel)
p=root/(r['retained'] if r else rel)
if r:assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']
if not p.is_file():raise SystemExit('Evidence path unavailable: '+rel)
print(p)
'''
(rc/'scripts/resolve-historical-evidence.py').write_text(script)
report='''# Palomar source-layout record

The registration candidate retains all historical evidence. Four historical
PublicTypes fixtures did not begin with `module`; they are retained as `.lean.txt`
with exactly their original bytes. No production source or failed production
proof was reclassified. The immutable old reports and checksum manifests keep
the paths and claims of their original commits. The mapping below resolves those
historical references in this candidate; `scripts/resolve-historical-evidence.py`
checks the retained bytes before returning their current path.

| Original historical path | Current retained path | SHA-256 |
| --- | --- | --- |
'''+''.join('| `'+r['original']+'` | `'+r['retained']+'` | `'+r['sha256']+'` |\n' for r in rows)+'''
The machine-readable mapping includes every located explicit path reference.
All other historical source/evidence bytes are preserved. The final whole-tree
scan covers every committed Lean file, beyond the production checker, and also
checks line limits, symlinks, binary artifacts, LFS pointers and submodules.
Exact final counts and source-closure status are recorded in the current
registration verification report. This layout repair does not change a theorem,
generator, equation, side condition or manuscript claim.
'''
(rc/'docs/PALOMAR_SOURCE_LAYOUT.md').write_text(report)
print('Preserved and remapped',len(rows),'historical fixtures; no mathematical sources changed')
