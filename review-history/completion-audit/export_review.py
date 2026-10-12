from pathlib import Path
import subprocess, shutil, fitz, json, re, difflib
R=Path(__file__).parent
repo=Path('/workspace/The-Thiele-Machine-book-design');m=repo/'monograph'
for source,target in [
    (m/'page-composition/The-Thiele-Machine-book-design.pdf','The-Thiele-Machine.pdf'),
    (m/'monograph.pdf','The-Thiele-Machine-A4.pdf'),
    (m/'monograph.tex','The-Thiele-Machine.tex'),
    (m/'monograph.txt','The-Thiele-Machine-A4.txt'),
    (m/'thiele_machine_math_spec.pdf','Math-specification.pdf'),
    (m/'math_spec_plaintext.txt','Math-specification.txt'),
]:shutil.copyfile(source,R/target)
for options,name in [(['-layout'],'The-Thiele-Machine.txt'),(['-nopgbrk'],'The-Thiele-Machine-reading.txt')]:
    subprocess.run(['pdftotext',*options,str(R/'The-Thiele-Machine.pdf'),str(R/name)],check=True)
verification=[]
for name in ['The-Thiele-Machine','The-Thiele-Machine-A4','Math-specification']:
    pdf=fitz.open(R/f'{name}.pdf');off=[]
    assert pdf.metadata['author']=='Devon Thiele'
    for i,p in enumerate(pdf):
        for block in p.get_text('dict')['blocks']:
            for line in block.get('lines',[]):
                for span in line['spans']:
                    q=fitz.Rect(span['bbox'])
                    if q.x0 < -1 or q.y0 < -1 or q.x1>p.rect.width+1 or q.y1>p.rect.height+1:off.append([i+1,span['text']])
    assert not off,(name,off[:5])
    verification.append(dict(document=name,pages=len(pdf),author=pdf.metadata['author'],off_page_text=off))
source=(m/'monograph.tex').read_text()
before=(R/'before/monograph/monograph.tex').read_text()
labels=lambda s:re.findall(r'\\label\{([^}]+)\}',s)
headings=lambda s:re.findall(r'\\(?:sub)*section\*?\{[^\n]+',s)
assert labels(before)==labels(source)
assert headings(before)==headings(source)
verification.append(dict(source_labels_preserved=len(labels(source)),headings_preserved=True))
(R/'artifact-verification.json').write_text(json.dumps(verification,indent=2)+'\n')
changes=json.loads((R/'document-edits.json').read_text())
previous=json.loads((R.parent/'meaning-audit/edits.json').read_text())
text=['THE THIELE MACHINE — AUDIT CORRECTIONS','Author: Devon Thiele','',
      'This review file records corrections; it is not part of the book.',
      'Part I: 91 manuscript corrections from the full meaning audit.',
      'Part II: completion audit, companion documents and source corrections.','']
text.append((R.parent/'meaning-audit/Changed-passages.txt').read_text())
text+=['','PART II — COMPLETION AUDIT','']
for i,c in enumerate(changes,1):
    text += [f'{i}. {c["file"]}',c['reason'],'BEFORE',c['before'],'AFTER',c['after'],'']
(R/'Changes.txt').write_text('\n'.join(text))
patch=[]
for snap in sorted((R/'before').rglob('*')):
    if not snap.is_file():continue
    rel=snap.relative_to(R/'before')
    patch+=difflib.unified_diff(snap.read_text().splitlines(True),(repo/rel).read_text().splitlines(True),fromfile='before/'+str(rel),tofile='after/'+str(rel))
(R/'Completion-audit.patch').write_text(''.join(patch))
shutil.copyfile(R.parent/'meaning-audit/coverage.json',R/'manuscript-coverage.json')
shutil.copyfile(R.parent/'meaning-audit/mathematical-checks.json',R/'mathematical-checks.json')
doc=fitz.open(R/'The-Thiele-Machine.pdf')
for anchor in ['Hales started the Flyspeck project','Press release, 2 October 2002']:
    found=[i for i,p in enumerate(doc) if anchor.lower() in ' '.join(p.get_text().lower().split())]
    assert found,anchor
    i=found[-1];doc[i].get_pixmap(matrix=fitz.Matrix(1.25,1.25)).save(R/f'page-{i+1}.png')
print(json.dumps(verification,indent=2))
