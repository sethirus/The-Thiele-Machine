from itertools import product,combinations
from math import log2,isclose,ceil
from pathlib import Path
import json,re
R=Path(__file__).parent
cases=flips=halvings=0
for n in range(1,5):
 for f in product(range(n),repeat=n):
  for reading in product((False,True),repeat=n):
   cases+=1
   yes={x for x in range(n) if reading[x]}
   if not all(f[x] in yes for x in yes):continue
   for entering in set(range(n))-yes:
    if f[entering] not in yes:continue
    flips+=1;domain=yes|{entering}
    assert len({f[x] for x in domain})<len(domain)
  largest=max(sum(f[x]==y for x in range(n)) for y in range(n))
  for cost in range(ceil(log2(n))+1):
   finite_list_bound=True
   for mask in range(1,1<<n):
    xs=[x for x in range(n) if mask>>x&1]
    finite_list_bound &= len(xs)<=2**cost*len({f[x] for x in xs})
   assert finite_list_bound==(largest<=2**cost)
   halvings+=1

def entropy(p):return -sum(x*log2(x) for x in p if x)
def loss(f,p):
 q=[0.]*len(p)
 for x,prob in enumerate(p):q[f[x]]+=prob
 return entropy(p)-entropy(q)
f=(1,2,2)
assert len({x for x in range(3) if f[x]==f[0]})==1
assert f[1]==f[2] and f[0]!=f[1]
assert isclose(loss(f,(1,0,0)),0,abs_tol=1e-12)
assert isclose(loss(f,(0,.5,.5)),1)
assert isclose(loss(f,(1/3,1/3,1/3)),2/3)
assert isclose(loss((0,)*8,(1/8,)*8),3)
assert 8>2**1*1 # One merge mark does not imply the halving rule.
a=(R/'before.tex').read_text();b=(R/'after.tex').read_text()
for pat in (r'\\(?:part|section|subsection)\*?\{[^\n]*',r'\\label\{([^}]+)\}'):
 assert re.findall(pat,a)==re.findall(pat,b)
labels=set(re.findall(r'\\label\{([^}]+)\}',b))
refs=set(re.findall(r'\\(?:ref|pageref|eqref|autoref)\{([^}]+)\}',b))
assert not refs-labels,refs-labels
report=dict(finite_map_reading_cases=cases,permanent_flip_cases=flips,halving_equivalence_cases=halvings,explicit_counterexamples='entering state without collision; point-mass zero loss; colliding pair one bit; uniform three-state loss; eight-to-one merge/halving separation',section_order_preserved=True,labels_preserved=len(labels),unresolved_source_references=sorted(refs-labels),scope='Finite exhaustive checks and targeted counterexamples; not a proof of all manuscript results or a physical experiment.')
(R/'mathematical-checks.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
