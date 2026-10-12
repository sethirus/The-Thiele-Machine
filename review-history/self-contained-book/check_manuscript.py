from pathlib import Path
import re,json,hashlib
R=Path(__file__).parent
old=(R/'before.tex').read_text();new=(R/'working.tex').read_text()
numbered=r'\\begin\{(theorem|lemma|proposition|corollary|definition|observation|remark|example|premise|thesis)\}(?:\[[^\]]*\])?\s*\\label\{([^}]+)\}'
a=re.findall(numbered,old);b=re.findall(numbered,new)
assert a==b,(len(a),len(b))
# Source-locator appendix is deliberately removed, but mathematical displays elsewhere remain.
oldarg=old[:old.index(r'\section{Companion source index}')]+old[old.index(r'\section{The CHSH derivation, in full}'):]
norm=lambda t:re.sub(r'\s+','',t)
displays=re.findall(r'(?<!\\)\\\[(.*?)\\\]',oldarg,re.S)
missing=[v for v in displays if norm(v) not in norm(new)]
assert not missing,[v[:120] for v in missing[:3]]
labels=set(re.findall(r'\\label\{([^}]+)\}',new));refs=set(re.findall(r'\\(?:ref|eqref|pageref)\{([^}]+)\}',new))
assert refs<=labels
body=new.split(r'\begin{document}',1)[1].split(r'\section{Sources}',1)[0]
assert not re.search(r'\bCoq\b|\bGallina\b|[A-Z][A-Za-z0-9_]+\.v\b',body)
assert 'Companion source index' not in body
report=dict(numbered_mathematical_items_same_order=len(a),previous_displays_preserved=len(displays),proof_environments_before=old.count(r'\begin{proof}'),proof_environments_after=new.count(r'\begin{proof}'),unresolved_internal_references=list(refs-labels),implementation_citations_in_argument=False,source_index_in_book=False,sha256=hashlib.sha256(new.encode()).hexdigest())
(R/'manuscript-verification.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
