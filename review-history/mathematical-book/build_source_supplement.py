from pathlib import Path
import re,json,sys,collections
R=Path(__file__).parent
repo=Path('/workspace/The-Thiele-Machine-book-design')
sys.path.insert(0,str(repo/'scripts'))
import audit_monograph_citations as audit
src=(R/'manuscript-before.tex').read_text()
index=src[src.index(r'\section{Every result and where it is checked}'):src.index(r'\section{The exact words of twenty-one results}')]
# Sections removed wholesale are preserved with their full original source separately.
for a,b in [(r'\section{What the checks establish}',r'\section{How to break this}'),(r'\section{Every result and where it is checked}',r'\section{The CHSH derivation, in full}'),(r'\subsection{Coq, in just enough detail}',r'\subsection{Category theory beyond Part I}'),(r'\subsection{Foundations of the formalization}',r"\section{What's mine, and what isn't}")]:
 i=src.index(a);j=src.index(b,i);src=src[:i]+src[j:]
src=src[:src.index(r'\section{Sources and mathematical dependencies}')]
def tokens(t):return [(m.start(),m.group(1).replace(r'\_', '_')) for m in re.finditer(r'\\(?:code|texttt)\{([^{}]+)\}',t)]
existing={t for _,t in tokens(index)}
decls=audit.find_top_level_decls([repo/'coq',repo/'minimal'])
sections=list(re.finditer(r'\\(?:section|subsection)\*?\{[^\n]*\}\s*\\label\{([^{}]+)\}',src))
remaining=set();rows=[];ambiguous=[];seen=set()
for pos,t in tokens(src):
 if t in existing or t in seen or t not in decls:continue
 seen.add(t)
 section=next((m.group(1) for m in reversed(sections) if m.start()<pos),None)
 if not section:continue
 paths=sorted({p.rsplit(':',1)[0] for p in decls[t]})
 # A name explicitly paired with a filename in its paragraph has an unambiguous local source.
 a=src.rfind('\n\n',0,pos)+2;b=src.find('\n\n',pos)
 p=src[a:b if b>=0 else len(src)]
 localfiles={v for _,v in tokens(p) if v.endswith('.v')}
 matching=[v for v in paths if Path(v).name in localfiles or v in localfiles]
 if len(matching)==1:paths=matching
 elif len(paths)>1:
  ambiguous.append(dict(name=t,section=section,paths=paths))
  continue
 rows.append(dict(name=t,section=section,file=paths[0]))
# Preserve all ambiguous names in a plaintext companion concordance; no guessed associations.
(R/'supplement-map.json').write_text(json.dumps(dict(rows=rows,ambiguous=ambiguous),indent=2))
def code(t):return r'\code{'+t.replace('_',r'\_')+'}'
out=[r'''\subsection{Additional source locators}

The following names were previously cited in the prose. They are collected here for
readers consulting the companion sources; the mathematical statements remain in the
sections named. Further lookup information is in the companion citation concordance.

\begingroup\small
\begin{longtable}{@{}p{0.08\linewidth}>{\raggedright\arraybackslash}p{0.49\linewidth}>{\raggedright\arraybackslash}p{0.36\linewidth}@{}}
\toprule
\textbf{Sec.} & \textbf{Name} & \textbf{File} \\
\midrule
\endhead
''']
for r in rows:
 out.append(r'\S\ref{'+r['section']+'} & '+code(r['name'])+' & '+code(Path(r['file']).name)+r' \\'+'\n')
out.append('\\bottomrule\n\\end{longtable}\n\\endgroup\n\n')
(R/'source-supplement.tex').write_text(''.join(out))
print('Names already in index:',len(existing),'additional:',len(rows),'ambiguous:',len(ambiguous))
print('Ambiguous:',[(r['name'],len(r['paths'])) for r in ambiguous])
