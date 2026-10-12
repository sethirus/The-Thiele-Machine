from pathlib import Path
import re,json,collections
R=Path(__file__).parent
old=(R/'manuscript-before.tex').read_text();new=(R/'working.tex').read_text()
def envs(s):
 return [(m.group(1),m.group(0)) for m in re.finditer(r'\\begin\{(definition|theorem|lemma|corollary|proposition|conjecture|observation|remark|premise|thesis|proof)\}[\s\S]*?\\end\{\1\}',s)]
labels=lambda s:set(re.findall(r'\\label\{([^{}]+)\}',s))
refs=lambda s:set(re.findall(r'\\(?:ref|eqref|pageref)\{([^{}]+)\}',s))
report={'labels_removed':sorted(labels(old)-labels(new)),'labels_added':sorted(labels(new)-labels(old)),'undefined_references':sorted(refs(new)-labels(new)),'original_environments':dict(collections.Counter(k for k,t in envs(old))),'revised_environments':dict(collections.Counter(k for k,t in envs(new)))}
# Record all changed labelled theorem bodies for manual review.
changes=[]
for kind,t in envs(old):
 ls=labels(t)
 if not ls:continue
 matches=[v for k,v in envs(new) if labels(v)&ls]
 if len(matches)==1 and matches[0]!=t:changes.append({'kind':kind,'labels':sorted(ls),'before':t,'after':matches[0]})
report['changed_labelled_environments']=len(changes)
(R/'mathematical-changes.json').write_text(json.dumps(changes,indent=2))
(R/'structure-check.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
# Distinguish unchanged displays from changed displays. Removed tool chapters are not part of this comparison.
for a,b in [(r'\section{What the checks establish}',r'\section{How to break this}'),(r'\section{The exact words of twenty-one results}',r'\section{The CHSH derivation, in full}'),(r'\subsection{Coq, in just enough detail}',r'\subsection{Category theory beyond Part I}'),(r'\subsection{Foundations of the formalization}',r"\section{What's mine, and what isn't}")]:
 i=old.index(a);j=old.index(b,i);old=old[:i]+old[j:]
displays=lambda s:[re.sub(r'\s+','',m.group()) for m in re.finditer(r'(?<!\\)\\\[[\s\S]*?\\\]',s)]
before=collections.Counter(displays(old));after=collections.Counter(displays(new));missing=list((before-after).elements())
print('Displays before',sum(before.values()),'after',sum(after.values()),'removed or altered',len(missing))
(R/'changed-displays.txt').write_text('\n\n'.join(missing))
