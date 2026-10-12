from pathlib import Path
import fitz,re,unicodedata,difflib
R=Path(__file__).parent;doc=fitz.open(R/'The-Thiele-Machine.pdf')
text=unicodedata.normalize('NFKC','\n\n'.join(b[4] for p in doc for b in p.get_text('blocks') if len(b)>4))
spans=[('Pencils','Put two equal-length pencils','Write those four readings'),('Signed cards','The next question is harder:','Write the swap as'),('Copying a cup','Try copying a cup with three beans.','Addition, multiplication by a fixed'),('The old check','Run a case that catches more than a wrong sum.','At the head, registers 0, 1 and 3')]
parts=[]
for title,start,end in spans:
 pat=lambda x:re.compile(re.escape(x).replace(r'\ ',r'\s+'))
 a=pat(start).search(text);assert a,start
 b=pat(end).search(text,a.end());assert b,end
 sample=text[a.start():b.start()].strip();sample=re.sub(r'\n\d{1,3}\n','\n',sample)
 sample=re.sub(r'corner of\s+a sheet','corner of a sheet',sample)
 sample=re.sub(r'ends where\s+it began','ends where it began',sample)
 sample=sample.replace('(2 · 4 + 1)21 = 18','(2 × 4 + 1) × 2^1 = 18')
 sample=re.sub(r'\n{3,}','\n\n',sample)
 parts.append(title.upper()+'\n\n'+sample)
(R/'Selected-passages.txt').write_text('\n\n\n'.join(parts)+'\n')
if (R/'Passages-for-review.txt').exists():(R/'Passages-for-review.txt').replace(R/'Changed-source-passages.txt')
a=(R/'before.tex').read_text().splitlines(True);b=(R/'working.tex').read_text().splitlines(True)
(R/'changes.patch').write_text(''.join(difflib.unified_diff(a,b,fromfile='before.tex',tofile='monograph.tex')))
print('Selected readable passages extracted from the final PDF.')
