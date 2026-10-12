from pathlib import Path
import re,json,hashlib,difflib

ROOT=Path(__file__).parent
source=(ROOT/'manuscript-before.tex').read_text()
s=source
changes=[]
def replace(old,new,why):
    global s
    assert s.count(old)==1,(why,old[:150],s.count(old))
    s=s.replace(old,new)
    changes.append(dict(reason=why,before=old,after=new))
def cut(first,last,name):
    global s
    a=s.index(first);b=s.index(last,a)
    (ROOT/name).write_text(s[a:b])
    replace(s[a:b],'',name)

# The complete prior material remains archived for provenance; it is not part of the book.
cut(r'\section{What the checks establish}',r'\section{How to break this}','companion-methodology-original.tex')
cut(r'\section{The exact words of twenty-one results}',r'\section{The CHSH derivation, in full}','companion-source-statements.tex')
cut(r'\subsection{Coq, in just enough detail}',r'\subsection{Category theory beyond Part I}','companion-notation-original.tex')
cut(r'\subsection{Foundations of the formalization}',r"\section{What's mine, and what isn't}",'companion-foundations-original.tex')
for file in ['original-edits.json']:
    if (ROOT/file).exists():
        for e in json.loads((ROOT/file).read_text()):replace(e['before'],e['after'],e['reason'])

code=r'\\(?:code|texttt)\{[^{}]*\}'
vfile=r'(?:[A-Za-z0-9_/-]+/)*[A-Za-z0-9_\\-]+\.v\b'
sourcewords=set('and or as in with the same file files both also checked name named names defined definitions theorem theorems lemma lemmas packaging run level floor its their for it all these those three four five six seven eight nine ten of from respectively'.split())
def source_only(t):
    if not (re.search(code,t) or re.search(vfile,t)):return False
    x=re.sub(code,' ',t)
    x=re.sub(vfile,' ',x)
    x=re.sub(r'\\(?:allowbreak|footnotesize)\b|[{}]',' ',x)
    words=re.findall(r'[A-Za-z]+',x.lower())
    return all(w in sourcewords for w in words) and not re.search(r'[$=<>]|\\(?:ref|mathrm|math)',x)

# Keep the established result/source index and bibliography literal.
start=s.index(r'\section{Every result and where it is checked}')
end=s.index(r'\section{The CHSH derivation, in full}',start)
index=s[start:end]
s=s[:start]+'@@SOURCE_INDEX@@\n\n'+s[end:]
start=s.index(r'\section{Sources and mathematical dependencies}')
bibliography=s[start:];s=s[:start]

def parentheses(t):
    spans=[];stack=[]
    for i,c in enumerate(t):
        if c=='(':stack.append(i)
        elif c==')' and stack:
            a=stack.pop()
            if not stack:spans.append((a,i+1))
    for a,b in reversed(spans):
        if source_only(t[a+1:b-1]):t=t[:a]+t[b:]
    return t
s=parentheses(s)
# Only delete citation sentences that contain no mathematical prose after removing names.
for m in list(re.finditer(r'(?:Checked as|Defined as|Checked name:|The formal counterparts are in)\s+[\s\S]*?\.(?=\s|$)',s))[::-1]:
    if source_only(m.group()):s=s[:m.start()]+s[m.end():]
# The first pass can leave "Checked as NAME ." where the filename was parenthesized.
s=re.sub(r'(?m)^[ \t]+$','',s)
s=re.sub(r' +([,.;:])',r'\1',s)
s=re.sub(r'\n{3,}','\n\n',s)
if (ROOT/'clean-edits.json').exists():
    for e in json.loads((ROOT/'clean-edits.json').read_text()):replace(e['before'],e['after'],e['reason'])

# A single modest note holds the explanation of tool use. The detailed procedures live with the sources.
note=r'''\section{Methodology note}
\label{sec:methodology}
\label{sec:coq}
\label{sec:coq-reproduce}

I used a proof assistant to constrain the formal derivations produced with language models
and to catch errors. The arguments are presented here for the reader to examine. The
companion sources record that checking work.

The source index identifies the companion formalizations. Their definitions, dependencies,
build instructions and executable tests are in the repository. The proof assistant checks
derivations within its logic; it does not establish that a definition captures the intended
idea, that a mathematical model describes a physical device, or that a result matters.

Companion sources: \url{https://github.com/sethirus/The-Thiele-Machine}, release
\texttt{v4.0.0}. The editorial revision in this book changes the presentation, not those
mathematical sources. Detailed reproduction instructions accompany the repository in
\texttt{monograph/COMPANION\_CHECKS.txt}.

'''
s+=note+bibliography
s=s.replace('@@SOURCE_INDEX@@',index.rstrip())
if (ROOT/'final-edits.json').exists():
    for e in json.loads((ROOT/'final-edits.json').read_text()):
        if e.get('all'):
            assert e['before'] in s
            s=s.replace(e['before'],e['after']);changes.append(e)
        else:replace(e['before'],e['after'],e['reason'])
s=re.sub(r'[ \t]*\n[ \t]*([,.;:])',r'\1',s)
s=re.sub(r' +([,.;:])',r'\1',s)
s=re.sub(r'\n{3,}','\n\n',s)
if (ROOT/'source-supplement.tex').exists():
    anchor=r'\section{The CHSH derivation, in full}'
    s=s.replace(anchor,(ROOT/'source-supplement.tex').read_text()+anchor)

s=s.replace('The last field is the \\emph{recursion theorem}', 'The last condition is the \\emph{recursion theorem}')
s=s.replace('( It implies merge pricing,', '(It implies merge pricing,')
s=re.sub(r'[ \t]+$', '', s, flags=re.M)

(ROOT/'working.tex').write_text(s)
(ROOT/'change-log.json').write_text(json.dumps(changes,indent=2,ensure_ascii=False)+'\n')
# Report every remaining implementation passage outside the source index, note and bibliography.
check=s[:s.index(r'\section{Methodology note}')]
a=check.index(r'\section{Every result and where it is checked}');b=check.index(r'\section{The CHSH derivation, in full}',a)
check=check[:a]+check[b:]
hits=[]
for m in re.finditer(r'\S[\s\S]*?(?=\n\s*\n|\Z)',check):
    t=m.group()
    if re.search(r'\\code\{|\bCoq\b|\bGallina\b|[\w-]+\.v\b|proof assistant|proof checker|checked record|proof field|record field|Inquisitor|coq-statements|sec:coq',t,re.I):
        hits.append(dict(id=len(hits),text=t))
(ROOT/'remaining.json').write_text(json.dumps(hits,indent=2))
for k in range(0,len(hits),25):
    (ROOT/f'remaining-{k//25+1}.txt').write_text('\n\n'.join(f"R{p['id']}\n{p['text']}" for p in hits[k:k+25]))
print('Remaining passages',len(hits),'words',len(s.split()))
