"""Verify the unchanged v5 inputs and review-production evidence."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
from pypdf import PdfReader

root = Path(__file__).resolve().parents[1]
source = root.parent / 'url-v5/manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v5.tex'
original = source.with_suffix('.pdf')
expected = {
    'tex': '1e828807a1351be5aba3d446a6e275c6699d23c9fbdde73ea0d121fac054e2e2',
    'pdf': '482b75840f70d9808ecc213dbb66cc8ec19a277ad2d14e859375aae449537906',
}
for ext, digest in expected.items():
    assert hashlib.sha256(source.with_suffix('.' + ext).read_bytes()).hexdigest() == digest
text = source.read_text()
cites = set(sum((x.split(',') for x in re.findall(r'\\cite(?:\[[^\]]*\])?\{([^}]+)\}', text)), []))
entries = set(re.findall(r'\\bibitem\{([^}]+)\}', text))
assert cites == entries and len(entries) == 9
assert not re.search(r'\busual\b', text)
assert '%' not in text
log = (root / 'build' / (source.stem + '.log')).read_text()
assert not any(word in log for word in ['Warning', 'Overfull', 'Underfull', 'Undefined'])
rebuilt = root / 'build' / (source.stem + '.pdf')
assert len(PdfReader(rebuilt).pages) == 10
for pdf, output in [(original, 'original-extracted.txt'), (rebuilt, 'rebuilt-extracted.txt')]:
    subprocess.run(['pdftotext', '-layout', str(pdf), str(root / 'evidence' / output)], check=True)
assert (root / 'evidence/original-extracted.txt').read_bytes() == (root / 'evidence/rebuilt-extracted.txt').read_bytes()
url = 'https://github.com/flengyel/notes/blob/main/logic/The-Unbearable-Notation-of-Logic_v8.pdf'
urls = [a.get_object().get('/A', {}).get('/URI') for p in PdfReader(original).pages for a in p.get('/Annots', [])]
assert url in urls
reports = sorted((root / 'docs/reviews').glob('*.md'))
assert len(reports) == 2
hostile = next(p for p in reports if 'HOSTILE' in p.name).read_text()
assert re.findall(r'^# \(([A-F])\)', hostile, re.M) == list('ABCDEF')
subprocess.run(['python3', str(root / 'evidence/check_appendix_coordinates.py')], check=True)
print(json.dumps({'status': 'passed', 'pages': 10, 'citations': 9, 'unchanged_manuscript': True,
                  'rebuild_text_identical': True, 'exact_url': True, 'reports': [p.name for p in reports]}, indent=2))
