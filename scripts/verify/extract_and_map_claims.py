#!/usr/bin/env python3
import re, json, os

def extract_claims(thesis_path):
    text=open(thesis_path,'r',encoding='utf-8').read()
    sents=re.split(r'(?<=[\.\?!])\s+', text)
    keywords=['demonstrate','prove','show','claim','achieve','exhibit','break','replace','transcend','recover','verify','falsify','require','demonstrated','demonstrates','advantage','RSA','Shor','Thiele']
    claims=[]
    for i,s in enumerate(sents):
        s2=s.strip().replace('\n',' ')
        low=s2.lower()
        if any(k.lower() in low for k in keywords):
            claims.append({'id':i+1,'text':s2})
    if not claims:
        paras=[p.strip() for p in text.split('\n\n') if p.strip()]
        for i,p in enumerate(paras[:50]):
            claims.append({'id':i+1,'text':p})
    return claims

def find_hits(keyword, root='.'): 
    hits=[]
    pat=re.compile(r'\b'+re.escape(keyword)+r'\b', re.IGNORECASE)
    for dirpath,dirnames,filenames in os.walk(root):
        # skip .git and node_modules
        if '.git' in dirpath.split(os.sep):
            continue
        if 'node_modules' in dirpath.split(os.sep):
            continue
        for fn in filenames:
            path=os.path.join(dirpath,fn)
            # skip certain binary/build extensions
            if fn.endswith(('.vo','.vio','.glob','.vo~')):
                continue
            try:
                with open(path,'r',encoding='utf-8',errors='ignore') as f:
                    for ln, line in enumerate(f,1):
                        if pat.search(line):
                            hits.append(f"{path}:{ln}:{line.strip()}")
                            if len(hits)>=20:
                                return hits
            except Exception:
                continue
    return hits

def map_claims(claims):
    stop=set(['the','and','that','this','with','for','are','was','were','have','has','had','not','but','from','which','when','where','what','who','why','how','all','can','may','will','our','we','they','their','its','is','in','on','a','an'])
    mappings=[]
    for c in claims:
        words=re.findall(r"[A-Za-z]{6,}", c['text'])
        words=[w.lower() for w in words if w.lower() not in stop]
        keywords=words[:6]
        hits={}
        for k in keywords:
            hits[k]=find_hits(k,'.')
        mappings.append({'claim_id':c['id'],'keywords':keywords,'hits':hits})
    return mappings

if __name__=='__main__':
    os.makedirs('artifacts',exist_ok=True)
    claims=extract_claims('thesis_plaintext.txt')
    with open('artifacts/thesis_claims.json','w',encoding='utf-8') as f:
        json.dump(claims,f,indent=2)
    print('WROTE artifacts/thesis_claims.json',len(claims),'claims')
    mappings=map_claims(claims)
    with open('artifacts/claim_mappings.json','w',encoding='utf-8') as f:
        json.dump(mappings,f,indent=2)
    print('WROTE artifacts/claim_mappings.json')
