from pathlib import Path
import json,re,unicodedata,html
r=Path(__file__).parent
norm=lambda s:re.sub(r'[^a-z0-9 ]',' ',unicodedata.normalize('NFKD',html.unescape(re.sub('<[^>]*>','',s))).encode('ascii','ignore').decode().lower())
stop=set('a an of the in and on for to as with at by from'.split());results=[]
for p in sorted((r/'unlinked-metadata').glob('*.json'),key=lambda p:int(p.stem)):
 e=json.loads(p.read_text());ws=set(norm(e['book']).split())-stop;cs=[]
 for m in e.get('items',[]):
  ts=set(norm(' '.join(m.get('title',[]))).split())-stop;score=len(ts&ws)/max(len(ts),1)
  authors=m.get('author',[]);families=[norm(a.get('family','')) for a in authors];author_match=sum(bool(a and a in norm(e['book'])) for a in families)/max(1,len(families))
  years={m[k]['date-parts'][0][0] for k in ['published','published-print','published-online'] if k in m};book_years={int(x) for x in re.findall(r'\b(?:18|19|20)\d{2}\b',e['book'])}
  total=.6*score+.3*author_match+.1*bool(years&book_years);cs.append((total,score,author_match,years,m))
 if not cs:results.append(dict(id=e['id'],status='no metadata',book=e['book']));continue
 total,sc,ac,ys,m=max(cs,key=lambda x:x[0]);status='consistent metadata' if sc>=.85 and ac>=.5 and bool(ys&book_years) else 'edition or identification review'
 results.append(dict(id=e['id'],status=status,title_score=sc,author_score=ac,book=e['book'],candidate=m))
 if sc>=.85 and ac>=.5 and not ys&book_years:print('DATE',e['id'],e['book'][:160],m['title'],ys)
 if sc>=.85 and ac>=.5:
  pm=re.fullmatch(r'(\d+)-(\d+)',m.get('page','') or '');bm=re.search(r'pp?\.\s*(\d+)--(\d+)',e['book'])
  if pm and bm and (int(pm[1]),int(pm[2]))!=(int(bm[1]),int(bm[2])):print('PAGES',e['id'],e['book'][:160],m['page'])
(r/'unlinked-review.json').write_text(json.dumps(results,indent=2));print('Entries',len(results),'consistent candidates',sum(e['status']=='consistent metadata' for e in results))
