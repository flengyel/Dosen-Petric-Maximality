from pathlib import Path
import hashlib,json,tarfile,shutil
r=Path('/home/flengyel/src/Dosen-Petric-Maximality');p=r/'provenance/wsl-gentzen-reducibility';w=r/'.codex-work/gentzen-reducibility'
def sha(b):return hashlib.sha256(b).hexdigest()
raws=['docs/CODEX_GENTZEN_REDUCIBILITY_2026-10-24.txt','docs/reviews/GENTZEN_REDUCIBILITY_REVIEW_2026-10-24.md']
rows=[]
with tarfile.open(p/'PRESERVED_RECONCILIATION.tar.gz','r:gz') as tar:
 for n in raws:
  b=(r/n).read_bytes()
  members=[m for m in tar.getmembers() if m.isfile() and m.name.endswith(n)]
  assert len(members)==1 and tar.extractfile(members[0]).read()==b,n
  cleaned=b.rstrip(b'\n')+b'\n';assert b.endswith(b'\n\n')
  rows.append(dict(path=n,original_sha256=sha(b),tracked_sha256=sha(cleaned),change='Remove redundant final blank line only; exact original in PRESERVED_RECONCILIATION.tar.gz'))
  (r/n).write_bytes(cleaned)
q=p/'worktrees.txt';raw=q.read_bytes();q.write_bytes(raw.rstrip(b'\n')+b'\n')
(p/'FORMAT_ONLY_IMPORTS.json').write_text(json.dumps(rows,indent=2)+'\n')
q=r/'docs/GENTZEN_REDUCIBILITY_REPORT.md';s=q.read_text()
s=s.replace('byte-identical to its Downloads copy (SHA-256','imported from its Downloads copy (original SHA-256')
s=s.replace('is retained unchanged. The reviewed base is','is retained, with only its redundant EOF blank line removed in the tracked import.\nExact original bytes of both supplied files remain in the reconciliation archive;\nFORMAT_ONLY_IMPORTS.json records the before/after hashes. The reviewed base is')
s=s.replace('Six failed exploratory compilations are retained with commands, exits,','The first staged whitespace check rejected redundant EOF blank lines in the\ntwo imported files and a worktree listing (exit 2). Originals are archived;\nonly the imported/captured copies were normalized before repeating that check.\nRaw logs, including this diagnostic, are retained byte-for-byte in RAW_LOGS.tar.gz;\nextract it in this evidence directory to reproduce their recorded paths.\n\nSix failed exploratory compilations are retained with commands, exits,')
q.write_text(s)
q=r/'docs/reviews/GENTZEN_REDUCIBILITY_HOSTILE.md';s=q.read_text().replace('review verbatim.','review with only its redundant final blank line removed; exact original bytes\nremain archived.');q.write_text(s)
q=r/'docs/VALIDATION.md';s=q.read_text().replace('separately. Checked/committed bytes and SSH/Downloads receipts are separate.','separately. The first staged check rejected imported EOF blank lines (exit 2);\noriginal bytes were archived and import copies normalized before retry. Raw\nlogs are retained exactly in RAW_LOGS.tar.gz. Checked/committed bytes and\nSSH/Downloads receipts are separate.');q.write_text(s)
(p/'staged-whitespace-failure.log').write_bytes((w/'staged-diff-check.log').read_bytes())
archive=p/'RAW_LOGS.tar.gz';assert not archive.exists()
with tarfile.open(archive,'w:gz') as tar:
 for f in sorted(p.rglob('*.log')):tar.add(f,arcname=str(f.relative_to(p)))
readme='''# Evidence use

The checked source inventory and command JSON files identify the exact proof
candidate. RAW_LOGS.tar.gz preserves every raw log byte, including failed
elaborations and the first staged whitespace rejection. Extract this archive
in this directory before checking individual log hashes from the command JSON.
Raw .log files remain available locally but are ignored by Git; the archive
is the committed representation. EVIDENCE_SHA256SUMS inventories the committed
metadata, controls and archives, excluding its own bytes and the raw logs.

PRESERVED_RECONCILIATION.tar.gz preserves original competing drafts, status,
diffs and untracked input files. FORMAT_ONLY_IMPORTS.json records the sole
format change made to the imported instruction and supplied review: removing
redundant blank lines at EOF. Their exact original bytes remain archived.
No production Lean source changed after the passing final build.
'''
(p/'README.md').write_text(readme)
shutil.copy2('/tmp/dp-reducibility-format-records.py',p/'format-import-records.py')
for name in ['REPORT_SHA256SUMS','RECORD_SHA256SUMS']:
 q=p/name
 files=[line.split('  ',1)[1] for line in q.read_text().splitlines()]
 q.write_text(''.join(sha((r/n).read_bytes())+'  '+n+'\n' for n in files))
(p/'EVIDENCE_SHA256SUMS').write_text(''.join(sha(q.read_bytes())+'  '+str(q.relative_to(p))+'\n' for q in sorted(p.rglob('*')) if q.is_file() and q.name!='EVIDENCE_SHA256SUMS' and q.suffix!='.log'))
print(json.dumps(dict(format_only_changes=rows,raw_logs_archive_sha256=sha(archive.read_bytes())),indent=2))
