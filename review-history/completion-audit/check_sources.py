from pathlib import Path
import json, urllib.request,urllib.parse,concurrent.futures,re,time,difflib
r=Path(__file__).parent;entries=json.loads((r/'sources.json').read_text());cache=r/'crossref';cache.mkdir(exist_ok=True)
def get(e):
 doi=e['doi'][0].replace(r'\%','%').replace(r'\_','_');p=cache/(str(e['id'])+'.json')
 if p.exists():return json.loads(p.read_text())
 result=dict(id=e['id'],doi=doi,book=e['text'])
 try:
  url='https://api.crossref.org/works/'+urllib.parse.quote(doi,safe='')
  req=urllib.request.Request(url,headers={'User-Agent':'ThieleBookCitationReview/1.0','Accept':'application/json'})
  with urllib.request.urlopen(req,timeout=25) as f:meta=json.load(f)['message']
  result.update(status='retrieved',title=meta.get('title',[]),authors=meta.get('author',[]),dates={k:meta[k] for k in ['published','published-print','published-online','issued'] if k in meta},container=meta.get('container-title'),volume=meta.get('volume'),issue=meta.get('issue'),page=meta.get('page'),links=meta.get('link',[]))
 except Exception as ex:result.update(status='error',error=str(ex))
 p.write_text(json.dumps(result,indent=2));return result
with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
 results=list(pool.map(get,[e for e in entries if e['doi']]))
(r/'doi-results.json').write_text(json.dumps(results,indent=2))
lines=[]
for e in results:
 lines.append(f"[{e['id']}] {e['status']} {e['doi']}\nBOOK: {e['book']}\nSOURCE: {e.get('title')} | {e.get('dates')} | {e.get('container')} {e.get('volume')}({e.get('issue')}) {e.get('page')}\n")
(r/'doi-review.txt').write_text('\n'.join(lines))
print('DOI entries',len(results),'retrieved',sum(e['status']=='retrieved' for e in results),'errors',sum(e['status']=='error' for e in results))
