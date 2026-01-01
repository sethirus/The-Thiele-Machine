#!/usr/bin/env python3
import json,os,re

ROOT='/workspaces/The-Thiele-Machine'
SEARCH_DIRS=['thielecpu','src','scripts','tools','coq','thielemachine','thieleuniversal']

def find_hits(keyword):
    pat=re.compile(r'\b'+re.escape(keyword)+r'\b', re.IGNORECASE)
    hits=[]
    for d in SEARCH_DIRS:
        base=os.path.join(ROOT,d)
        if not os.path.isdir(base):
            continue
        for dirpath,_,filenames in os.walk(base):
            for fn in filenames:
                path=os.path.join(dirpath,fn)
                try:
                    with open(path,'r',encoding='utf-8',errors='ignore') as f:
                        for i,line in enumerate(f,1):
                            if pat.search(line):
                                hits.append(f"{os.path.relpath(path,ROOT)}:{i}:{line.strip()}")
                                if len(hits)>=20:
                                    return hits
                except Exception:
                    continue
    return hits

def main():
    claims=json.load(open(os.path.join(ROOT,'artifacts/thesis_claims.json'),encoding='utf-8'))
    mappings=[]
    stop=set(['the','and','that','this','with','for','are','was','were','have','has','had','not','but','from','which','when','where','what','who','why','how','all','can','may','will','our','we','they','their','its','is','in','on','a','an'])
    for c in claims:
        words=re.findall(r"[A-Za-z]{6,}", c['text'])
        words=[w.lower() for w in words if w.lower() not in stop]
        keywords=words[:6]
        hits={}
        for k in keywords:
            hits[k]=find_hits(k)
        mappings.append({'claim_id':c['id'],'keywords':keywords,'hits':hits})
    os.makedirs(os.path.join(ROOT,'artifacts'),exist_ok=True)
    json.dump(mappings, open(os.path.join(ROOT,'artifacts/claim_mappings.json'),'w',encoding='utf-8'), indent=2)
    print('WROTE artifacts/claim_mappings.json')

if __name__=='__main__':
    main()
