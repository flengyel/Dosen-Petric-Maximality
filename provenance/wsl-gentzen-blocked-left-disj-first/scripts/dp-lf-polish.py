for src,dst in [('report','GENTZEN_BLOCKED_DISJ_FIRST_REPORT.md'),('hostile','reviews/GENTZEN_BLOCKED_DISJ_FIRST_HOSTILE.md'),('writing','reviews/GENTZEN_BLOCKED_DISJ_FIRST_WRITING.md')]:
 (root/'docs'/dst).write_bytes(Path('/tmp/dp-lf-'+src+'.md').read_bytes())
(local/'attempts'/'dp-lf-normalization-backup.py').write_bytes(Path('/tmp/dp-lf-normalization-backup.py').read_bytes())
print('Kept rank-control process evidence in the review/report verification passages')
