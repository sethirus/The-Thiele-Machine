from pathlib import Path
import json
R=Path(__file__).parent

def note(i,text):
 m=json.loads((R/'coverage.json').read_text());x=m[i-1];assert x['id']==i
 x['status']='read';x['assessment']=text
 (R/'coverage.json').write_text(json.dumps(m,indent=2)+'\n')
 with (R/'reading-notes.txt').open('a') as f:f.write(f'CHUNK {i} (lines {x["start"]}–{x["end"]})\n{text}\n\n')

def edit(tag,old,new,why):
 s=(R/'before.tex').read_text();assert s.count(old)==1,(tag,s.count(old))
 es=json.loads((R/'edits.json').read_text());assert not any(x['tag']==tag for x in es)
 es.append(dict(tag=tag,before=old,after=new,reason=why));(R/'edits.json').write_text(json.dumps(es,indent=2,ensure_ascii=False)+'\n')
