from pathlib import Path
import re,json
R=Path(__file__).parent;s=(R/'before.tex').read_text()
ms=list(re.finditer(r'\\section\*?\{([^}]+)\}',s));entries=[]
for i,m in enumerate(ms):
 end=ms[i+1].start() if i+1<len(ms) else len(s)
 t=s[m.start():end];n=i+1
 (R/f'section-{n:02d}.tex').write_text(t)
 entries.append(dict(id=n,title=m[1],start=s.count('\n',0,m.start())+1,end=s.count('\n',0,end)+1,words=len(t.split()),status='pending'))
(R/'coverage.json').write_text(json.dumps(entries,indent=2)+'\n')
print('\n'.join(f"{x['id']:02d} {x['title']} ({x['words']} words)" for x in entries))
