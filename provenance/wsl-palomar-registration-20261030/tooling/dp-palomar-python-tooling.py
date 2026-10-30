venv=stage/'tooling/python'
command(['python3','-m','venv',str(venv)],'python-venv',lock=False)
command([str(venv/'bin/python'),'-m','pip','install','PyYAML==6.0.3','jsonschema==4.25.1'],'python-tools',lock=False)
p=subprocess.run([str(venv/'bin/python'),'-m','pip','freeze'],capture_output=True,text=True,check=True)
(ev/'PYTHON_TOOLING.txt').write_text(p.stdout)
print(p.stdout)
