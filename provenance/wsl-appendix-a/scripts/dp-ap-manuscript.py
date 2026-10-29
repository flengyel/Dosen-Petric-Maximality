import re
stem='Maximality_of_the_Dosen_Petric_Boolean_Category_v'
src=root/'manuscript'/(stem+'7.tex');dest=root/'manuscript'/(stem+'8.tex')
s=src.read_text();old=s
changes=[('''A Lean formalization proves the maximality argument
relative to explicit coherence and structural inputs.''','''A Lean formalization proves coherence for the equation-generated
presentation and verifies maximality, the model corollary, and the
occurrence-coordinate constructions.'''),('''Section~\\ref{sec:formalization} describes the Lean formalization and
its explicit coherence inputs.''','''Section~\\ref{sec:formalization} describes the Lean formalization,
including the proved inputs to its general maximality theorem.'''),('''The contextual-collapse theorem uses the symmetric
map''','''An alternative contextual-collapse theorem uses the symmetric
map'''),('''For the equation-generated Do\\v{s}en--Petri\\'c presentation, the
development proves that the occurrence interpretation is well defined
and preserves signed labels. Faithfulness of this
interpretation remains unproved in Lean, and the full presentation has
not yet been supplied as an instance of all the hypotheses of
\\texttt{relative\\_maximality}.''','''For the equation-generated Do\\v{s}en--Petri\\'c presentation, cut
elimination and Boolean Coherence are proved in Lean. The development
constructs normalization, signed-label preservation, and uniform
whole-arrow substitution, and supplies the full presentation as an
instance of every hypothesis of \\texttt{relative\\_maximality}. The theorem
\\texttt{Presentation.maximality} gives the resulting maximality statement.

The theorem \\texttt{Presentation.short\\_maximality} formalizes the proof
in Section~\\ref{sec:collapse}, with explicit inverses for $q_A$ and $e_A$.
The model corollary is proved using full structure-preserving
interpretations and their composition with substitution. The formalization
also verifies the occurrence-profile and finite-ordinal constructions of
Appendix~\\ref{app:substitution}, the diagram identities of
Appendix~\\ref{app:structural-diagrams}, and the concrete source reductions
and rank comparisons recorded in Appendix~\\ref{app:cut-errata}.''')]
for a,b in changes:
 assert s.count(a)==1,(a,s.count(a));s=s.replace(a,b)
s=s.replace('\\date{October 28, 2026}','\\date{October 29, 2026}')
assert s.count('\\begin{tikzcd}')==old.count('\\begin{tikzcd}')==10
assert s[s.index('\\appendix'):]==old[old.index('\\appendix'):]
assert re.findall(r'\\(?:begin|end)\{(?:equation|align|tikzcd)\}',s)==re.findall(r'\\(?:begin|end)\{(?:equation|align|tikzcd)\}',old)
assert not dest.exists() or dest.read_text()==s
dest.write_text(s)
local.mkdir(parents=True,exist_ok=True)
build=local/'tex-v8';build.mkdir(exist_ok=True)
for passno in range(1,4):
 command(['pdflatex','-interaction=nonstopmode','-halt-on-error','-output-directory='+str(build),str(dest)],name='tex-v8-pass'+str(passno))
 pdf=build/(stem+'8.pdf')
 assert pdf.exists()
final=local/'tex-v8-final.log';final.write_bytes((build/(stem+'8.log')).read_bytes())
textlog=final.read_text()
assert 'undefined references' not in textlog.lower() and 'undefined citations' not in textlog.lower()
assert 'LaTeX Warning: Label(s) may have changed' not in textlog
out=root/'manuscript'/(stem+'8.pdf');out.write_bytes(pdf.read_bytes())
command(['pdftotext','-layout',str(out),str(local/'manuscript-v8.txt')],name='pdf-v8-text',lock=False)
command(['pdfinfo',str(out)],name='pdf-v8-info',lock=False)
text=(local/'manuscript-v8.txt').read_text();assert 'remains unproved in Lean' not in text
for t in ['Presentation.maximality','model corollary','Two corrections to the cut-elimination proof']:
 assert t in text,t
assert 'Overfull' not in textlog,textlog[textlog.find('Overfull')-40:textlog.find('Overfull')+250]
manifest=root/'manuscript/SHA256SUMS';ms=manifest.read_text()
for p in [dest,out]:
 line=sha(p.read_bytes())+'  '+p.name+'\n'
 assert p.name not in ms
 ms+=line
manifest.write_text(ms)
(evidence).mkdir(parents=True,exist_ok=True)
(evidence/'MANUSCRIPT_SCOPE_REFRESH.json').write_text(json.dumps(dict(correction='FP-SCOPE-20261029',prior_tex=str(src.relative_to(root)),current_tex=str(dest.relative_to(root)),current_pdf=str(out.relative_to(root)),tex_sha256=sha(dest.read_bytes()),pdf_sha256=sha(out.read_bytes()),appendices_byte_identical=True,preserved_diagrams=10,prior_version_files_unchanged=True,publication=False,visual_inspection_pending=True),indent=2)+'\n')
print('Built v8 scope refresh; v7 and every appendix/diagram preserved. PDF visual inspection still required.')
