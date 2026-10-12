from pathlib import Path
import json,re,html
r=Path(__file__).parent;es=json.loads((r/'doi-results.json').read_text())
norm=lambda s:re.sub(r'[^a-z0-9 ]','',re.sub('<[^>]*>','',html.unescape(s)).lower())
flags=[]
for e in es:
 if e['status']!='retrieved':flags.append(dict(id=e['id'],issue='FETCH',book=e['book'],error=e.get('error')));continue
 title=' '.join(e['title']);words=set(norm(title).split())-{'a','an','the','of','in','on','and','for','to','with'};bw=set(norm(e['book'].split('\\href')[0]).split());score=len(words&bw)/max(1,len(words));years={d['date-parts'][0][0] for d in e['dates'].values()};year=re.search(r'\((\d{4})\)',e['book']);err=[]
 if score<.75:err.append('TITLE '+str(round(score,2)))
 if year and int(year[1]) not in years:err.append('YEAR '+str(years))
 if err:flags.append(dict(id=e['id'],issue=', '.join(err),book=e['book'],title=title))
print('flags',len(flags))
for x in flags:print(x['id'],x['issue'],x['book'][:195],x.get('title',''))
(r/'doi-flags.json').write_text(json.dumps(flags,indent=2))
