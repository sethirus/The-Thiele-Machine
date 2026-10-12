from pathlib import Path
import re
R=Path(__file__).parent
p=R/'working.tex';s=p.read_text()
s=s.replace('guest\\ncodes','guest\ncodes').replace('around.\\nThe','around.\nThe').replace('unbounded\\nintegers','unbounded\nintegers').replace('and\\ndivision','and\ndivision').replace('remain\\nimplementation','remain\nimplementation')
s=s.replace(r'\code{MM2\_undec.v}',r'\code{vendor/coq-undecidability/theories/MinskyMachines/MM2\_undec.v}')
s=s.replace('the word Landauer in a file name suggests.', 'the name Landauer might suggest.')
s=s.replace('Part V was how to\ncheck it and how to break it.', 'Part V was where to challenge it and what would break it.')
removed=[]
for name in ['Coq development team','Thierry Coquand and Christine Paulin-Mohring',"Thierry Coquand and G\\'erard Huet",'Christine Paulin-Mohring. Wikipedia.','The Rocq Prover. About']:
 pat=r'\\noindent '+re.escape(name)+r'[\s\S]*?\\par\\medskip\n'
 m=re.search(pat,s);assert m,name;removed.append(m.group());s=s[:m.start()]+s[m.end():]
(R/'companion-tool-history-sources.tex').write_text('\n'.join(removed))
s=re.sub(r'\n{3,}','\n\n',s)
p.write_text(s)
print('Final text cleanup applied')
