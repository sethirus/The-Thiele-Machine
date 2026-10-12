from pathlib import Path
import urllib.request,urllib.parse,json,time,concurrent.futures,re
r=Path(__file__).parent;out=r/'unlinked-metadata';out.mkdir(exist_ok=True)
es=[e for e in json.loads((r/'sources.json').read_text()) if not e['urls']]
def get(e):
 p=out/(str(e['id'])+'.json')
 if p.exists():return
 q=e['text'].split('\\href')[0][:310];q=re.sub(r'\\[A-Za-z]+',' ',q)
 u='https://api.crossref.org/works?'+urllib.parse.urlencode({'query.bibliographic':q,'rows':3})
 d=dict(id=e['id'],book=e['text'])
 for n in range(3):
  try:
   with urllib.request.urlopen(u,timeout=25) as f:items=json.load(f)['message']['items']
   d['items']=[{k:m[k] for k in ['title','author','published','published-print','published-online','container-title','volume','issue','page','DOI'] if k in m} for m in items];break
  except Exception as ex:d['error']=str(ex);time.sleep(3)
 p.write_text(json.dumps(d,indent=2));time.sleep(1)
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:list(pool.map(get,es))
print('Completed',len(es),'bibliographic searches')
