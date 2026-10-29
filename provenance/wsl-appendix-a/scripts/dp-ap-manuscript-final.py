import re
proof_commit=Path('/tmp/dp-ap-proof-commit.txt').read_text().strip()
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()==proof_commit
stem='Maximality_of_the_Dosen_Petric_Boolean_Category_v'
dest=root/'manuscript'/(stem+'8.tex');s=dest.read_text()
oldfull='1e967bcb913a74ae590dde940f246acaddce1fba'
assert (s.count(oldfull)==1 and s.count('1e967bcb913a}')==1) or (s.count(proof_commit)==1 and s.count(proof_commit[:12]+'}')==1)
s=s.replace(oldfull,proof_commit).replace('1e967bcb913a}',proof_commit[:12]+'}')
dest.write_text(s)
prior=[]
for p in sorted((root/'manuscript').glob('*_v[4567].*')):
 rel=str(p.relative_to(root));old=subprocess.check_output(['git','show','37cce28:'+rel],cwd=root);assert old==p.read_bytes();prior.append(dict(path=rel,sha256=sha(old),unchanged=True))
assert len(prior)==8
old=(root/'manuscript'/(stem+'7.tex')).read_text()
assert s[s.index('\\appendix'):s.index('\\section*{Use of AI tools}')]==old[old.index('\\appendix'):old.index('\\section*{Use of AI tools}')]
assert s[s.index('\\appendix'):].replace(proof_commit,oldfull).replace(proof_commit[:12]+'}','1e967bcb913a}')==old[old.index('\\appendix'):]
assert s.count('\\begin{tikzcd}')==10
build=local/'tex-v8'
for passno in range(1,4):command(['pdflatex','-interaction=nonstopmode','-halt-on-error','-output-directory='+str(build),str(dest)],name='tex-v8-citation-pass'+str(passno))
textlog=(build/(stem+'8.log')).read_text()
assert all(t not in textlog.lower() for t in ['undefined references','undefined citations','overfull','label(s) may have changed'])
out=root/'manuscript'/(stem+'8.pdf');out.write_bytes((build/out.name).read_bytes())
command(['pdftotext','-layout',str(out),str(local/'manuscript-v8-final.txt')],name='pdf-v8-final-text',lock=False)
a=(local/'manuscript-v8.txt').read_text().split('\f');b=(local/'manuscript-v8-final.txt').read_text().split('\f')
assert len(a)==len(b)==14
assert a[:12]==b[:12]
assert proof_commit[:12] in b[12] and '1e967bcb913a' not in b[12]
links=command(['pdftohtml','-xml','-stdout',str(out)],name='pdf-v8-final-links',lock=False)
assert '/tree/'+proof_commit in (root/links['log']).read_text()
command(['pdftoppm','-png','-r','70',str(out),'/tmp/dp-v8-final-page'],name='pdf-v8-final-render',lock=False)
from PIL import Image
visual=[]
for i in range(1,14):
 p=Path('/tmp/dp-v8-final-page-'+str(i).zfill(2)+'.png');im=Image.open(p).convert('RGB')
 old=Image.open('/tmp/dp-v8-page-'+str(i).zfill(2)+'.png').convert('RGB')
 same=im.size==old.size and im.tobytes()==old.tobytes()
 if i<=12:assert same,i
 visual.append(dict(page=i,png=str(p),png_sha256=sha(p.read_bytes()),pixel_identical_to_inspected_pre_citation=i<=12 and same))
manifest=root/'manuscript/SHA256SUMS';ms=manifest.read_text().splitlines()
for p in [dest,out]:
 matched=[i for i,t in enumerate(ms) if t.endswith('  '+p.name)];assert len(matched)==1
 ms[matched[0]]=sha(p.read_bytes())+'  '+p.name
manifest.write_text('\n'.join(ms)+'\n')
prior_ms=subprocess.check_output(['git','show','37cce28:manuscript/SHA256SUMS'],cwd=root)
assert manifest.read_bytes().startswith(prior_ms)
(evidence/'MANUSCRIPT_SCOPE_REFRESH.json').write_text(json.dumps(dict(correction='FP-SCOPE-20261029',citation_correction='FP-CITATION-20261029',mathematical_source_commit=proof_commit,current_tex=str(dest.relative_to(root)),current_pdf=str(out.relative_to(root)),tex_sha256=sha(dest.read_bytes()),pdf_sha256=sha(out.read_bytes()),appendices_byte_identical=True,preserved_diagrams=10,prior_version_files=prior,prior_hash_manifest_prefix_preserved=True,pages=13,visual=visual,prior_all_pages_inspected=True,final_citation_page_visual_inspection_pending=True,full_pdf_citation_link_verified=True,publication=False),indent=2)+'\n')
print('Final v8 citation built and embedded full immutable source link verified. Pages1–12 pixel-identical to inspected PDF; inspect final page13 next.')
