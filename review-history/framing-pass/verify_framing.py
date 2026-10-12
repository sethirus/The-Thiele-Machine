from pathlib import Path
import json,re,hashlib
R=Path(__file__).parent
old=(R/'before.tex').read_text();new=Path('/workspace/The-Thiele-Machine-book-design/monograph/monograph.tex').read_text();es=json.loads((R/'edits.json').read_text())
expected=old
for e in sorted(es,key=lambda e:old.index(e['before']),reverse=True):
 assert old.count(e['before'])==1
 a=old.index(e['before']);expected=expected[:a]+e['after']+expected[a+len(e['before']):]
assert expected==new==(R/'working.tex').read_text()
heads=lambda s:re.findall(r'\\(?:part|section|subsection|subsubsection)\*?\{([^}]+)\}',s)
labels=lambda s:re.findall(r'\\label\{([^}]+)\}',s)
assert heads(old)==heads(new);assert labels(old)==labels(new)
assert set(re.findall(r'\\(?:ref|eqref|pageref)\{([^}]+)\}',new))<=set(labels(new))
counts={}
for env in ('theorem','lemma','proposition','corollary','observation','definition','premise','conjecture','thesis','remark','proof','tabular','longtable','tikzpicture','equation','align'):
 p=r'\\begin\{'+env+r'\}(.*?)\\end\{'+env+r'\}'
 a=re.findall(p,old,re.S);b=re.findall(p,new,re.S)
 assert a==b,env
 counts[env]=len(a)
assert re.findall(r'(?<!\\)\\\[(.*?)(?<!\\)\\\]',old,re.S)==re.findall(r'(?<!\\)\\\[(.*?)(?<!\\)\\\]',new,re.S)
# These were explicit competing statements of the book's purpose.
for phrase in ('The strongest thing in this book first','The headline result is this.',"That's the one lamp I set",'the six are the idea','the one question this book is about:', 'why is a quantum game in a book about records'):
 assert phrase in old and phrase not in new,phrase
# Keep concrete performance evidence and non-execution limits.
for text in ('402,654,059','25,953,317','around $10^{18}$ years','never run','has not been produced'):
 assert text in old and text in new,text
report=dict(edits=len(es),headings_preserved=len(heads(new)),labels_preserved=len(labels(new)),unchanged_environments=counts,displayed_equations_unchanged=True,internal_references_resolve=True,word_count_before=len(old.split()),word_count_after=len(new.split()),source_sha256=hashlib.sha256(new.encode()).hexdigest(),scope='Framing and explanatory prose; mathematical statements, definitions, proofs, tables, diagrams and organization unchanged. This does not measure reader response.')
(R/'framing-verification.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
