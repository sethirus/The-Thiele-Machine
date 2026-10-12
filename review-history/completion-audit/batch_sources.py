from pathlib import Path
import urllib.request,urllib.parse,json,time
r=Path(__file__).parent;es=[e for e in json.loads((r/'sources.json').read_text()) if e['doi']]
for start in range(0,len(es),25):
 batch=es[start:start+25];ds=[e['doi'][0].replace(r'\%','%').replace(r'\_','_') for e in batch]
 url='https://api.crossref.org/works?'+urllib.parse.urlencode({'filter':','.join('doi:'+d for d in ds),'rows':100})
 for attempt in range(3):
  try:
   with urllib.request.urlopen(url,timeout=35) as f:items=json.load(f)['message']['items']
   break
  except Exception as ex:
   print('retry',start,str(ex),flush=True);time.sleep(5)
 else:continue
 lookup={m['DOI'].lower():m for m in items}
 for e,doi in zip(batch,ds):
  if doi.lower() not in lookup:continue
  meta=lookup[doi.lower()];out=dict(id=e['id'],doi=doi,book=e['text'],status='retrieved',title=meta.get('title',[]),authors=meta.get('author',[]),dates={k:meta[k] for k in ['published','published-print','published-online','issued'] if k in meta},container=meta.get('container-title'),volume=meta.get('volume'),issue=meta.get('issue'),page=meta.get('page'),links=meta.get('link',[]))
  (r/'crossref'/f"{e['id']}.json").write_text(json.dumps(out,indent=2))
 print(start,len(items),flush=True);time.sleep(1)
