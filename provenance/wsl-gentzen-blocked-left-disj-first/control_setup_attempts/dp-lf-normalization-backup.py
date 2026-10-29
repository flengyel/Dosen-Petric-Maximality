backup=local/'attempts';backup.mkdir(exist_ok=True)
for suffix in ['lean','log']:
 p=local/('sequential-returned-rank.'+suffix)
 target=backup/('sequential-returned-rank-normalization-setup.'+suffix)
 assert not target.exists() or target.read_bytes()==p.read_bytes()
 target.write_bytes(p.read_bytes())
(backup/'STATUS.json').write_text(json.dumps(dict(command=['lake','env','lean','-DwarningAsError=true',str((local/'sequential-returned-rank.lean').relative_to(root))],exit_status=1,classification='control normalization setup failure, not expected semantic rejection',source_sha256=sha((backup/'sequential-returned-rank-normalization-setup.lean').read_bytes()),log_sha256=sha((backup/'sequential-returned-rank-normalization-setup.log').read_bytes())),indent=2)+'\n')
print('Preserved the failed normalization-control setup source, log and exit; excluded from expected rejections')
