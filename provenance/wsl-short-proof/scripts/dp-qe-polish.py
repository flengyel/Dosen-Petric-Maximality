p=root/'docs/CODEX_NEXT_SESSION.txt';s=p.read_text().replace('operation-law duty, alongside the short proof/model/remaining appendix claims.', 'operation-law duty, alongside model/remaining appendix claims. The short proof\nis now complete as recorded below.');p.write_text(s)
p=root/'docs/MANUSCRIPT_STATEMENTS.md';s=p.read_text().replace('Appendix A/model correspondences and the short proof are still open.', 'Appendix A/model correspondences remain open. The distinct short proof is now\ncomplete by Presentation.short_maximality.');p.write_text(s)
p=root/'docs/PRESENTATION_CORRESPONDENCE.md';s=p.read_text().replace('The short proof, model, remaining substitution/operation laws and appendix\ncorrespondences stay separate duties.', 'The short q/e proof is now separately completed by Presentation.short_maximality.\nThe model, remaining substitution/operation laws and appendix correspondences\nstay separate duties.');p.write_text(s)
print('Reconciled remaining live short-proof paragraphs without rewriting dated evidence')

p=local/'record-preparation-first-attempt.log'
if not p.exists():
 p.write_text('qe-records exited 1 at FOCUSED_CONTROLS assertion: the draft evidence script read the prior phase full-source-bridges controls (47), while the required current short-proof controls have 50 passing entries. Assertion prevented acceptance of the wrong phase. Script path corrected; no mathematical source or check result changed.\n')
 p.with_suffix('.json').write_text(json.dumps(dict(command=['python3','/tmp/dp-cut-elimination-records.py','after_77199','qe-records'],exit_status=1,log=str(p.relative_to(root)),sha256=sha(p.read_bytes()),kind='evidence_preparation',resolved='Corrected the focused-controls input to the current short-proof phase.'),indent=2)+'\n')
