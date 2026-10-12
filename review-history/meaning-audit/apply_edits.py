from pathlib import Path
import json,re
R=Path(__file__).parent;src=Path('/workspace/The-Thiele-Machine-book-design/monograph/monograph.tex');before=(R/'before.tex').read_text();assert src.read_text()==before,'Source changed during review; reconcile first'
es=json.loads((R/'edits.json').read_text());ranges=sorted((before.index(e['before']),before.index(e['before'])+len(e['before']),e['tag']) for e in es)
for a,b in zip(ranges,ranges[1:]):assert a[1]<=b[0],('overlap',a[2],b[2])
s=before
for e in es:
 assert s.count(e['before'])==1,e['tag'];s=s.replace(e['before'],e['after'])
pat=r'\\(?:part|section|subsection)\*?\{[^\n]*'
assert re.findall(pat,before)==re.findall(pat,s),'Section organization changed'
assert re.findall(r'\\label\{([^}]+)\}',before)==re.findall(r'\\label\{([^}]+)\}',s),'Labels changed'
src.write_text(s);(R/'after.tex').write_text(s)
(R/'Changed-passages.txt').write_text('\n\n'.join(f"{i}. {e['tag']}\nReason: {e['reason']}\n\nBEFORE\n{e['before']}\n\nAFTER\n{e['after']}" for i,e in enumerate(es,1))+'\n')
print('Applied',len(es),'nonoverlapping corrections; chapter/section order and labels preserved.')
