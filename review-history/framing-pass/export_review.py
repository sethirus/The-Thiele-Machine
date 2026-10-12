from pathlib import Path
import subprocess,shutil,fitz,json
R=Path(__file__).parent;repo=Path('/workspace/The-Thiele-Machine-book-design');m=repo/'monograph'
# The publications build regenerates this unchanged document; retain its original bytes.
original=subprocess.check_output(['git','show','HEAD:monograph/thiele_machine_math_spec.pdf'],cwd=repo)
old=fitz.open(stream=original,filetype='pdf');new=fitz.open(m/'thiele_machine_math_spec.pdf')
assert [p.get_text() for p in old]==[p.get_text() for p in new]
(m/'thiele_machine_math_spec.pdf').write_bytes(original)
shutil.copyfile(m/'page-composition/The-Thiele-Machine-book-design.pdf',R/'The-Thiele-Machine.pdf')
shutil.copyfile(m/'monograph.pdf',R/'The-Thiele-Machine-A4.pdf')
shutil.copyfile(m/'monograph.tex',R/'The-Thiele-Machine.tex')
shutil.copyfile(m/'monograph.txt',R/'The-Thiele-Machine-A4.txt')
subprocess.run(['pdftotext','-layout',str(R/'The-Thiele-Machine.pdf'),str(R/'The-Thiele-Machine.txt')],check=True)
subprocess.run(['pdftotext','-nopgbrk',str(R/'The-Thiele-Machine.pdf'),str(R/'The-Thiele-Machine-reading.txt')],check=True)
shutil.copyfile(m/'page-composition/verification.json',R/'design-verification.json')
doc=fitz.open(R/'The-Thiele-Machine.pdf')
anchors=['Structure is something a machine can hold','The book in one paragraph','The structural results leave a choice open','There are two counts to keep apart','Put the triangle, the cups','structure held as state, acted on']
found={}
for anchor in anchors:
 pages=[i for i,p in enumerate(doc) if anchor.lower() in ' '.join(p.get_text().lower().split())]
 assert pages,anchor
 i=pages[-1];found[anchor]=i+1
 doc[i].get_pixmap(matrix=fitz.Matrix(1.4,1.4)).save(R/f'page-{i+1}.png')
# Check both settings for text outside the physical page and build failures.
for name in ['The-Thiele-Machine','The-Thiele-Machine-A4']:
 pdf=fitz.open(R/f'{name}.pdf');off=[]
 for i,p in enumerate(pdf):
  for block in p.get_text('dict')['blocks']:
   for line in block.get('lines',[]):
    for span in line['spans']:
     q=fitz.Rect(span['bbox'])
     if q.x0< -1 or q.y0< -1 or q.x1>p.rect.width+1 or q.y1>p.rect.height+1:off.append([i+1,span['text']])
 assert not off,off[:5]
 print(name,len(pdf),'pages; author',pdf.metadata['author'],'; off-page spans',len(off))
(R/'preview-pages.json').write_text(json.dumps(found,indent=2)+'\n');print(json.dumps(found,indent=2))
