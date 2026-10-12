from pathlib import Path
import json,re,urllib.request,urllib.parse,concurrent.futures,hashlib,threading,time,subprocess
from html.parser import HTMLParser
r=Path(__file__).parent;cache=r/'linked-sources';cache.mkdir(exist_ok=True)
es=json.loads((r/'sources.json').read_text());urls={}
for e in es:
 for u in e['urls']:
  if 'doi.org/' in u:continue
  u=re.sub(r'\\([%_&#])',r'\1',u);u=urllib.parse.quote(u,safe=":/?=&%#@+~,;()[]!$'*-.")
  urls.setdefault(u,[]).append(e['id'])
locks={h:threading.Lock() for h in {urllib.parse.urlsplit(u).netloc for u in urls}}
class Text(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['script','style']:self.skip+=1
  if t in ['p','div','br','h1','h2','h3','li','tr']:self.out.append('\n')
 def handle_endtag(self,t):
  if t in ['script','style']:self.skip=max(0,self.skip-1)
 def handle_data(self,d):
  if not self.skip:self.out.append(d)
def fetch(pair):
 u,ids=pair;key=hashlib.sha256(u.encode()).hexdigest()[:16];p=cache/(key+'.json')
 if p.exists():return json.loads(p.read_text())
 out=dict(url=u,entries=ids,key=key)
 try:
  host=urllib.parse.urlsplit(u).netloc
  with locks[host]:
   req=urllib.request.Request(u,headers={'User-Agent':'Mozilla/5.0 (compatible; scholarly reference review)'})
   with urllib.request.urlopen(req,timeout=25) as f:
    out.update(final_url=f.url,content_type=f.headers.get('Content-Type',''),status=f.status)
    data=f.read(16*1024*1024+1)
   time.sleep(3 if 'arxiv.org' in host else .25)
  if len(data)>16*1024*1024:out['note']='Content exceeds saved-file limit'
  elif data.startswith(b'%PDF'):
   pp=cache/(key+'.pdf');pp.write_bytes(data)
   proc=subprocess.run(['pdftotext',str(pp),str(cache/(key+'.txt'))],capture_output=True,timeout=30);out['text_extracted']=proc.returncode==0
  else:
   s=data.decode('utf-8',errors='replace');(cache/(key+'.html')).write_text(s)
   parser=Text();parser.feed(s);(cache/(key+'.txt')).write_text(re.sub(r'\n[ \t\n]+','\n',''.join(parser.out)))
 except Exception as ex:out.update(status='error',error=str(ex))
 p.write_text(json.dumps(out,indent=2));return out
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool:results=list(pool.map(fetch,urls.items()))
(r/'link-results.json').write_text(json.dumps(results,indent=2));print(len(results),'links',sum(isinstance(e['status'],int) for e in results),'retrieved',flush=True)
