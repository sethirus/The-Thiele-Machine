from pathlib import Path
import re,json
from fractions import Fraction
R=Path(__file__).parent
old=(R/'before.tex').read_text();new=(R/'working.tex').read_text()
anchor=r'\subsection{The four-vector construction}'
assert old[:old.index(anchor)]==new[:new.index(anchor)]
assert old[old.index(r'\section{Methodology note}'):]==new[new.index(r'\section{Methodology note}'):]
pat=r'\\begin\{(theorem|lemma|proposition|corollary|definition|observation|remark|premise|thesis)\}(?:\[[^\]]*\])?\s*\\label\{([^}]+)\}'
assert re.findall(pat,old)==re.findall(pat,new)
norm=lambda x:re.sub(r'\s+','',x)
displays=re.findall(r'(?<!\\)\\\[(.*?)\\\]',old,re.S)
assert all(norm(v) in norm(new) for v in displays)
assert re.findall(r'\\(?:part|section|subsection|subsubsection)\*?\{([^}]+)\}',old)==re.findall(r'\\(?:part|section|subsection|subsubsection)\*?\{([^}]+)\}',new)
# The examples have explicit arithmetic, order, and failure conditions.
for n in [0,3,5,20]:
 a,b,c=n,0,0
 while a:a-=1;b+=1;c+=1
 while c:c-=1;a+=1
 assert (a,b,c)==(n,n,0)
assert divmod(7,3)==(2,1) and divmod(2,3)==(0,2)
assert 18==2*3**2 and 36==2**2*3**2 and 12==2**2*3 and 4==2**2
assert divmod(4,3)==(1,1)
assert Fraction(10)*Fraction(22,5)==44 and Fraction(44)*Fraction(7,11)==28
for a,b in [(1,1),(2,3),(-2,5),(0,1)]:
 X=lambda pair:(pair[1],pair[0]);Z=lambda pair:(pair[0],-pair[1])
 assert X(Z((a,b)))==tuple(-v for v in Z(X((a,b))))
 assert X(X((a,b)))==(a,b) and Z(Z((a,b)))==(a,b)
assert (2*4+1)*2**1==18
labels=set(re.findall(r'\\label\{([^}]+)\}',new));refs=set(re.findall(r'\\(?:ref|eqref|pageref)\{([^}]+)\}',new));assert refs<=labels
report={'main_chapters_unchanged':True,'headings_and_order_unchanged':True,'numbered_items_unchanged':len(re.findall(pat,new)),'existing_displayed_equations_preserved':len(displays),'worked_arithmetic_and_card_operations_checked':True,'unresolved_references':sorted(refs-labels)}
(R/'verification.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
