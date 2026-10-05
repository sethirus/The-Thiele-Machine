import re,sys
def segments(s):
    # yield (is_comment, text) with nested Coq comments
    out=[];i=0;n=len(s);buf=[];depth=0;start=0
    cur_code_start=0
    res=[]
    i=0
    while i<n:
        if s.startswith('(*',i):
            if depth==0:
                res.append((False,s[cur_code_start:i])); cstart=i
            depth+=1; i+=2; continue
        if s.startswith('*)',i) and depth>0:
            depth-=1; i+=2
            if depth==0:
                res.append((True,s[cstart:i])); cur_code_start=i
            continue
        if s[i]=='"' and depth==0:
            j=s.index('"',i+1); i=j+1; continue
        i+=1
    res.append((False,s[cur_code_start:]))
    return res
for p in sys.argv[1:]:
    s=open(p,encoding='utf-8').read()
    segs=segments(s)
    assert ''.join(t for _,t in segs)==s
    out=[]
    for c,t in segs:
        if c:
            t=re.sub(r"\bpu_([a-z]+)\b",r"\1",t)
        out.append(t)
    open(p,'w',encoding='utf-8',newline='\n').write(''.join(out))
