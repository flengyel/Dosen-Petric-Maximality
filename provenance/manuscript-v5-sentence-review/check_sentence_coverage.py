from pathlib import Path
import hashlib,json,re
root=Path(__file__).resolve().parents[2]
e=Path(__file__).parent
p=root/'manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v5.tex'
s=p.read_text(); ledger=json.loads((e/'final-ledger.json').read_text());assert hashlib.sha256(p.read_bytes()).hexdigest()==ledger['source_sha256']
ns=re.sub(r'\s+','',s);covered=set()
for entry in ledger['entries']:
 assert re.sub(r'\s+','',entry['text']) in ns,entry['id']
 lo,hi=entry['source_lines'];assert re.sub(r'\s+','',entry['text']) in re.sub(r'\s+','','\n'.join(s.splitlines()[lo-1:hi])),entry['id']
 covered.update(range(lo,hi+1))
uncovered=[]
for i,line in enumerate(s.splitlines(),1):
 if i<16 or not line.strip() or i in covered:continue
 if re.fullmatch(r'\\(?:begin|end)\{[^}]+\}.*|\\(?:maketitle|medskip|smallskip|small|clearpage)|\\setlength.*',line.strip()):continue
 uncovered.append([i,line])
assert not uncovered,uncovered
print(json.dumps({'units':len(ledger['entries']),'uncovered_authored_lines':uncovered,'status':'all exact-text and coverage assertions passed'}))
