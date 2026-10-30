import sys,re
def inline(p):
    p=' '.join(l.strip() for l in p.split('\n'))
    p=re.sub(r'"([^"]*)"',r"``\1''",p)
    p=p.replace('...',r'\ldots{}')
    return p
SPECIAL={}
def convert(md, label, special):
    paras=re.split(r'\n\s*\n', md.strip())
    out=[]
    title=paras[0].strip()
    out+=['%'+'='*75, '\\section{%s}'%title, '\\label{%s}'%label, '%'+'='*75, '']
    for p in paras[1:]:
        raw=p
        if raw.startswith('  '):
            key=raw.strip().split()[0:3]
            hit=None
            for k,v in special.items():
                if raw.strip().startswith(k): hit=v
            if hit is None: raise SystemExit('no special for: '+raw[:60])
            if hit=='SKIP': continue
            out+=[hit,'']; continue
        lines=raw.strip().split('\n')
        if len(lines)==1 and not re.search(r'[.!:,"]$',lines[0]) and len(lines[0])<60:
            out+=['\\subsection{%s}'%lines[0].strip(),'']; continue
        out+=[inline(raw),'']
    return '\n'.join(out)
