"""Rebuild both documents from the repository root, publishing after three passes.

Usage: python artifacts/assessment_2026_09_10/rebuild_documents.py
Requires pdflatex and pdftotext. Full build logs remain in the printed directory.
"""
from pathlib import Path
import subprocess,tempfile,shutil,json
root=Path.cwd();out=Path(tempfile.mkdtemp(prefix='thiele-repaired-docs-'));results=[]
for stem,plain in [('monograph','monograph.txt'),('thiele_machine_math_spec','math_spec_plaintext.txt')]:
 for n in range(1,4):
  with (out/f'{stem}-pass{n}.log').open('w') as log:
   r=subprocess.run(['pdflatex','-interaction=nonstopmode','-halt-on-error',f'-output-directory={out}',f'{stem}.tex'],cwd=root/'monograph',stdout=log,stderr=subprocess.STDOUT)
  if r.returncode: print('FAILED',stem,n,out,flush=True);raise SystemExit(r.returncode)
 for ext in ['pdf','toc','out']:
  if (out/f'{stem}.{ext}').exists():shutil.copy2(out/f'{stem}.{ext}',root/'monograph'/f'{stem}.{ext}')
 subprocess.run(['pdftotext','-layout',str(out/f'{stem}.pdf'),str(root/'monograph'/plain)],check=True)
 warnings=[line for line in (out/f'{stem}.log').read_text().splitlines() if line.startswith('LaTeX Warning:') and ('undefined' in line or 'Rerun' in line)]
 results.append({'document':stem,'passes':3,'warnings':warnings})
print(json.dumps({'directory':str(out),'results':results},indent=2))
