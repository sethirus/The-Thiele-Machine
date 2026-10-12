from pathlib import Path
import re,json
R=Path(__file__).parent;s=(R/'working.tex').read_text();old=(R/'manuscript-before.tex').read_text()
a=s.index(r'\section{Every result and where it is checked}');b=s.index(r'\section{The CHSH derivation, in full}',a)
index=s[a:b]
index=index.replace(r'\S\ref{sec:straight}',r'p.~\pageref{sec:straight}')
ix=index.index(r'\subsection{Additional source locators}')
index=index[:ix]+index[ix:].replace(r'\textbf{Sec.}',r'\textbf{Place}')
heads=lambda t:{m.group(3):(m.group(1),m.group(2)) for m in re.finditer(r'\\begin\{(\w+)\}\[([^\n]*)\]\\label\{([^}]+)\}',t)}
orig=heads(old);new=heads(s);changes=[]
for label,(kind,title) in new.items():
 if label not in orig or orig[label][1]==title:continue
 lines=index.splitlines(True)
 for i,line in enumerate(lines):
  if '\\ref{'+label+'}:' in line:
   lhs,*tail=line.split(' & ',1)
   if orig[label][1] in lhs:
    changed=lhs.replace(orig[label][1],title)
    lines[i]=' & '.join([changed]+tail);changes.append(label)
 index=''.join(lines)
s=s[:a]+index+s[b:]
(R/'working.tex').write_text(s)
print('Source index titles synchronized:',len(changes))
