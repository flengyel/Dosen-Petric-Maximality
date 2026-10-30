import shutil
packages=stage/'tooling/packages';packages.mkdir(parents=True,exist_ok=True)
command(['apt-get','download','zstd'],'download-zstd',cwd=packages,lock=False)
fs=list(packages.glob('zstd*.deb'));assert len(fs)==1
prefix=stage/'tooling/zstd';prefix.mkdir(parents=True,exist_ok=True)
command(['dpkg-deb','-x',str(fs[0]),str(prefix)],'unpack-zstd',cwd=packages,lock=False)
command([str(prefix/'usr/bin/zstd'),'--version'],'zstd-version',lock=False)
ev.mkdir(parents=True,exist_ok=True)
(ev/'TOOLING.json').write_text(json.dumps(dict(zstd_package=str(fs[0]),package_sha256=sha(fs[0].read_bytes()),binary=str(prefix/'usr/bin/zstd'),binary_sha256=sha((prefix/'usr/bin/zstd').read_bytes()),system_installation_modified=False,first_checker_install_failure=dict(exit_status=1,cause='tar exit 2: zstd: Cannot exec: No such file or directory',checker_archive_authenticated_before_unpack=True)),indent=2)+'\n')
