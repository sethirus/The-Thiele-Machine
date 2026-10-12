from pathlib import Path
import json
R=Path(__file__).parent

def edit(tag,old,new,reason):
 s=(R/'before.tex').read_text();assert s.count(old)==1,(tag,s.count(old))
 p=R/'edits.json';es=json.loads(p.read_text()) if p.exists() else []
 assert not any(x['tag']==tag for x in es),tag
 es.append(dict(tag=tag,before=old,after=new,reason=reason));p.write_text(json.dumps(es,indent=2,ensure_ascii=False)+'\n')
def span(tag,start,end,new,reason):
 s=(R/'before.tex').read_text();assert s.count(start)==1,(tag,'start')
 a=s.index(start);b=s.index(end,a);edit(tag,s[a:b].rstrip(),new.strip(),reason)
def note(i,assessment):
 p=R/'coverage.json';c=json.loads(p.read_text());assert c[i-1]['id']==i
 c[i-1].update(status='assessed',assessment=assessment);p.write_text(json.dumps(c,indent=2,ensure_ascii=False)+'\n')
