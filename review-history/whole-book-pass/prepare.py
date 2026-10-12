from pathlib import Path
import re,json
R=Path(__file__).parent;s=(R/'before.tex').read_text();lines=s.splitlines(True)
# Preserve every source line in numbered, reasonably sized reading chunks.
chunks=[];buf=[];words=0;start=1
for n,line in enumerate(lines,1):
 buf.append(line);words+=len(line.split())
 if words>=5700 and not line.strip():
  chunks.append((start,n,''.join(buf)));buf=[];words=0;start=n+1
if buf:chunks.append((start,len(lines),''.join(buf)))
manifest=[]
for i,(a,b,t) in enumerate(chunks,1):
 name=f'read-{i:02}.tex';(R/name).write_text(t)
 headings=re.findall(r'\\(?:part|section|subsection)\*?\{([^}]+)\}',t)
 manifest.append(dict(id=i,file=name,start=a,end=b,words=len(t.split()),headings=headings,status='unread'))
assert ''.join(t for _,_,t in chunks)==s
(R/'coverage.json').write_text(json.dumps(manifest,indent=2)+'\n')
(R/'edits.json').write_text('[]\n')
(R/'reading-notes.txt').write_text('Whole-book tangible-reasoning audit. Coverage refers to source read, not keyword matches.\n\nFor each section: what the reader can do or reconstruct; what follows; what would fail; whether the concrete case carries the abstraction; whether analogy, mathematical demonstration and physical evidence are distinguished. Preserve sound prose and organization. Reference entries are read for their role rather than turned into demonstrations.\n')
print(len(chunks),'chunks;',sum(x['words'] for x in manifest),'words')
for x in manifest:print(x['id'],x['start'],x['end'],x['words'],', '.join(x['headings'][:3]))
