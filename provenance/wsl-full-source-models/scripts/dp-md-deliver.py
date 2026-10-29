commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
origin=subprocess.check_output(['git','rev-parse','origin/main'],cwd=root,text=True).strip()
live=subprocess.check_output(['git','ls-remote','origin','refs/heads/main'],cwd=root,text=True).split()[0]
assert commit==origin==live
assert not subprocess.check_output(['git','status','--porcelain'],cwd=root,text=True).strip()
checked=[]
for line in (evidence/'CHECKED_SOURCES.sha256').read_text().splitlines():
 digest,rel=line.split('  ',1);b=subprocess.check_output(['git','show',commit+':'+rel],cwd=root);assert sha(b)==digest and b==(root/rel).read_bytes();checked.append(rel)
assert len(checked)==868
changed=subprocess.check_output(['git','diff','--name-only','b257325',commit,'--','docs'],cwd=root,text=True).splitlines()
files=changed+['README.md','AGENTS.md']+['provenance/wsl-full-source-models/'+n for n in ['CHECKED_SOURCES.sha256','CHECKED_SOURCES.tar.gz','FINAL_VERIFICATION.json','COMMANDS.json']]
rows=[]
for relative in files:
 b=subprocess.check_output(['git','show',commit+':'+relative],cwd=root);assert b==(root/relative).read_bytes()
 target=Path('/mnt/c/Users/fleng/Downloads')/(('Dosen_Petric_Full_Source_Models_'+Path(relative).name) if relative.startswith('provenance/') else Path(relative).name)
 if target.exists() and target.read_bytes()!=b:target=target.with_name(target.stem+'-'+commit[:12]+target.suffix)
 assert not target.exists() or target.read_bytes()==b
 target.write_bytes(b);assert target.read_bytes()==b
 rows.append(dict(repository=relative,downloads=str(target),sha256=sha(b),bytes=len(b),source_commit=commit))
for row in rows:
 b=Path(row['downloads']).read_bytes();assert sha(b)==row['sha256']
 assert b==subprocess.check_output(['git','show',row['source_commit']+':'+row['repository']],cwd=root)
receipt=dict(deliveries=rows,proof_commit=commit,all_byte_verified=True,checked_committed_files=len(checked),origin_main=origin,live_ssh_main=live,preserved_stash=subprocess.check_output(['git','stash','list','--format=%H'],cwd=root,text=True).strip())
assert receipt['preserved_stash']=='dedfd8fc8cd49930e9a162d5be585215b062a43c'
register=evidence/'DELIVERY_REGISTER.json';b=(json.dumps(receipt,indent=2)+'\n').encode();register.write_bytes(b)
target=Path('/mnt/c/Users/fleng/Downloads')/('Dosen_Petric_Full_Source_Models_DELIVERY_REGISTER-'+commit[:12]+'.json');assert not target.exists() or target.read_bytes()==b;target.write_bytes(b);assert target.read_bytes()==b
(evidence/'DELIVERY_RECEIPT.json').write_text(json.dumps(dict(register=str(register.relative_to(root)),downloads=str(target),sha256=sha(b),registered_deliveries=len(rows),register_byte_verified=True,proof_commit=commit),indent=2)+'\n')
print(json.dumps(dict(source_commit=commit,registered_deliveries=len(rows),downloads_register=str(target),register_sha256=sha(b),failures=[]),indent=2))
