"""Package the current review changes against HEAD and verify reconstructed bytes.

Run from the repository root: python3 scripts/package_review_revision.py
Does not commit, push, or modify staging. Compiled/binary evidence is separate.
"""
from pathlib import Path
import hashlib, io, json, subprocess, tarfile, tempfile
root=Path.cwd()
out=root/'artifacts/review_revision'
source_ext={'.v','.py','.sh','.tex','.sty','.md','.json','.yml','.yaml','.toml','.cff','.ml','.mli','.bsv'}
changed=subprocess.check_output(['git','diff','HEAD','--name-only','-z']).decode().split('\0')
untracked=subprocess.check_output(['git','ls-files','--others','--exclude-standard','-z']).decode().split('\0')
excluded={'artifacts/review_revision/source.patch','artifacts/review_revision/source_manifest.json'}
def wanted(name):
 p=Path(name)
 return bool(name) and name not in excluded and (p.suffix in source_ext or (p.suffix == '.txt' and str(p.parent) == 'artifacts/review_revision') or p.name in {'.gitignore','.gitmodules','LICENSE','Makefile','Makefile.local','_CoqProject','contract_report.txt','counter_contract_report.txt'})
tracked=[n for n in changed if wanted(n)]
new=[n for n in untracked if wanted(n)]
patch=subprocess.check_output(['git','diff','HEAD','--binary','--',*tracked])
for name in new:
 r=subprocess.run(['git','diff','--no-index','--binary','--','/dev/null',name],capture_output=True)
 if r.returncode != 1: raise RuntimeError((name,r.returncode,r.stderr.decode()))
 patch+=r.stdout
(out/'source.patch').write_bytes(patch)
head=set(subprocess.check_output(['git','ls-tree','-r','--name-only','HEAD']).decode().splitlines())
files=sorted(set(tracked+new))
base_paths=[n for n in files if n in head]
archive=subprocess.check_output(['git','archive','HEAD','--',*base_paths])
with tempfile.TemporaryDirectory(prefix='thiele-review-reproduction-') as tmp:
 with tarfile.open(fileobj=io.BytesIO(archive)) as tar:tar.extractall(tmp,filter='data')
 subprocess.run(['git','apply','--whitespace=nowarn',str(out/'source.patch')],cwd=tmp,check=True)
 records=[]
 for name in files:
  current=root/name; reproduced=Path(tmp)/name
  if current.exists():
   assert reproduced.read_bytes()==current.read_bytes(),name
   records.append({'path':name,'sha256':hashlib.sha256(current.read_bytes()).hexdigest()})
  else:
   assert not reproduced.exists(),name
   records.append({'path':name,'deleted':True})
manifest={'base_commit':subprocess.check_output(['git','rev-parse','HEAD']).decode().strip(),
 'branch':subprocess.check_output(['git','branch','--show-current']).decode().strip(),
 'patch_sha256':hashlib.sha256(patch).hexdigest(),
 'patch_bytes':len(patch),
 'scope':'Changed source/configuration files and review contracts. Compiled proof objects, PDFs, binaries and historical generated reports are excluded.',
 'reproduction_check':'Applied to an archive of the base commit; every listed file matched the working source byte for byte.',
 'files':records}
(out/'source_manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(f'Patch: {len(patch)} bytes; {len(records)} files reproduced byte for byte.')
