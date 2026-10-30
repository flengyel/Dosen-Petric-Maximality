for src,name in [('definitions','PalomarDefinitions'),('correspondence','PalomarCorrespondence'),('endpoints','PalomarMaximality')]:
 (rc/'DosenPetric'/(name+'.lean')).write_bytes(Path('/tmp/dp-palomar-'+src+'.lean').read_bytes())
exec(Path('/tmp/dp-palomar-generate.py').read_text())
