#!/usr/bin/env python3
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
