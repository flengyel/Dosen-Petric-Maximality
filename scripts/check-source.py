#!/usr/bin/env python3
"""Conservative source hygiene; the Lean dependency audit checks actual proof axioms."""
import hashlib
import pathlib
import re

root = pathlib.Path(__file__).resolve().parent.parent
paths = sorted([root / 'DosenPetric.lean', *root.glob('DosenPetric/**/*.lean'),
                *root.glob('Checks/**/*.lean')])
errors = []
for path in paths:
    text = path.read_text(encoding='utf-8')
    if not text.startswith('module\n'):
        errors.append(f'{path.relative_to(root)}: module header missing')
    if len(text.splitlines()) > 10000:
        errors.append(f'{path.relative_to(root)}: exceeds 10,000 lines')
    if re.search(r'\b(sorry|admit|axiom|native_decide)\b', text):
        # Comments and strings may mention axioms, so inspect only lines starting declarations
        # or containing actual proof-hole tokens. This is a screening check, not a Lean parser.
        for i, line in enumerate(text.splitlines(), 1):
            if re.search(r'\b(sorry|admit|native_decide)\b', line) or re.match(r'\s*(?:public\s+)?axiom\s', line):
                errors.append(f'{path.relative_to(root)}:{i}: forbidden proof token')
    if path.is_symlink():
        errors.append(f'{path}: source symlink')
    print(hashlib.sha256(path.read_bytes()).hexdigest(), path.relative_to(root))
if errors:
    raise SystemExit('\n'.join(errors))
print(f'PASS: {len(paths)} source files; no proof holes or custom axiom declarations')
