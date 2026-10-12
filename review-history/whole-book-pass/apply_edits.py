from pathlib import Path
import json,re,difflib
R=Path(__file__).parent; p=Path('/workspace/The-Thiele-Machine-book-design/monograph/monograph.tex')
s=(R/'before.tex').read_text();assert p.read_text()==s,'Source changed since baseline'
es=json.loads((R/'edits.json').read_text());spans=[]
for e in es:
 assert s.count(e['before'])==1,e['tag'];start=s.index(e['before']);spans.append((start,start+len(e['before']),e))
spans.sort(key=lambda x:x[0])
for a,b in zip(spans,spans[1:]):assert a[1]<=b[0],(a[2]['tag'],b[2]['tag'])
n=s
for a,b,e in reversed(spans):n=n[:a]+e['after']+n[b:]
heads=lambda t:re.findall(r'\\(?:part|section|subsection|subsubsection)\*?\{([^}]+)\}',t)
assert heads(s)==heads(n)
assert re.findall(r'\\label\{([^}]+)\}',s)==re.findall(r'\\label\{([^}]+)\}',n)
labels=set(re.findall(r'\\label\{([^}]+)\}',n));refs=set(re.findall(r'\\(?:ref|eqref|pageref)\{([^}]+)\}',n));assert refs<=labels,refs-labels
p.write_text(n);(R/'working.tex').write_text(n)
(R/'changes.patch').write_text(''.join(difflib.unified_diff(s.splitlines(True),n.splitlines(True),fromfile='before.tex',tofile='working.tex')))
(R/'Changed-passages.txt').write_text('\n\n'.join(f"{i}. {e['tag']}\nReason: {e['reason']}\n\nBEFORE\n{e['before']}\n\nAFTER\n{e['after']}" for i,(_,_,e) in enumerate(spans,1)))
print(len(es),'edits applied;',len(heads(s)),'headings and all',len(labels),'labels preserved; all internal references resolved.')
