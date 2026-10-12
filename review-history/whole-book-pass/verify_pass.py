from pathlib import Path
import json,re,math,itertools,hashlib
from fractions import Fraction as F
R=Path(__file__).parent
old=(R/'before.tex').read_text();new=Path('/workspace/The-Thiele-Machine-book-design/monograph/monograph.tex').read_text()
c=json.loads((R/'coverage.json').read_text());es=json.loads((R/'edits.json').read_text())
assert len(c)==46 and all(x['status']=='read' for x in c)
assert ''.join((R/x['file']).read_text() for x in c)==old
expected=old
for x in sorted(es,key=lambda x:old.index(x['before']),reverse=True):
 assert old.count(x['before'])==1
 a=old.index(x['before']);expected=expected[:a]+x['after']+expected[a+len(x['before']):]
assert new==expected==(R/'working.tex').read_text()
heads=lambda t:re.findall(r'\\(?:part|section|subsection|subsubsection)\*?\{([^}]+)\}',t)
labels=lambda t:re.findall(r'\\label\{([^}]+)\}',t)
assert heads(old)==heads(new) and labels(old)==labels(new)
statement_counts={}
for name in ('theorem','lemma','proposition','corollary','observation'):
 pattern=r'\\begin\{'+name+r'\}(.*?)\\end\{'+name+r'\}'
 xs=re.findall(pattern,old,re.S);ys=re.findall(pattern,new,re.S)
 assert xs==ys,name
 statement_counts[name]=len(xs)
assert set(re.findall(r'\\(?:ref|eqref|pageref)\{([^}]+)\}',new))<=set(labels(new))
assert list(itertools.accumulate([1,2,3,4,5]))==[1,3,6,10,15]
assert list(itertools.accumulate([1,3,3,4,5]))==[1,4,7,11,16]
assert sum([1,3,2,4,5])==15
H=lambda ps:-sum(p*math.log2(p) for p in ps if p)
assert H([.25]*4)==2 and H([.5,.25,.25])==1.5
assert F(1,1-F(9,10))==10 and F(1,1-F(1,10))==F(10,9)
assert F(9,10)*F(1,10)==F(1,10)*F(9,10)==F(9,100)
assert abs(sum(k/2**k for k in range(1,100))-2)<1e-12
assert len({(a,b^a) for a,b in itertools.product((0,1),repeat=2)})==4
assert 2**1*3**2*(6*2+5)==306
assert 306*2==612 and 612//3==204 and 204//(4*3)==17
assert abs(math.log(2)/2-math.log(2)/6-math.log(2)/3)<1e-14
# Enumerate every fresh-slot write sequence over three values up to length eight.
gas_cases=0
for seq in itertools.product(range(3),repeat=8):
 current=0; net=0
 for nxt in seq:
  gas=20000 if current==0 and nxt!=0 else 100
  refund=19900 if current!=0 and nxt==0 else 0
  net+=gas-refund;current=nxt
  assert net>=0 and (current==0 or net>=20000)
  gas_cases+=1
# Independent recursive tree/path construction against the printed iterative checks.
leaf=lambda i:('leaf',i)
node=lambda a,b:('node',a,b)
def split(n):return 1<<((n-1).bit_length()-1)
def root(xs):
 if len(xs)==1:return xs[0]
 k=split(len(xs));return node(root(xs[:k]),root(xs[k:]))
def path(xs,m):
 if len(xs)==1:return []
 k=split(len(xs))
 return path(xs[:k],m)+[root(xs[k:])] if m<k else path(xs[k:],m-k)+[root(xs[:k])]
def subproof(xs,m,b=True):
 if m==len(xs):return [] if b else [root(xs)]
 k=split(len(xs))
 return subproof(xs[:k],m,b)+[root(xs[k:])] if m<=k else subproof(xs[k:],m-k,False)+[root(xs[:k])]
def include(N,m,r,ps,claimed):
 if not 0<=m<N:return False
 f,s=m,N-1
 for p in ps:
  if s==0:return False
  if f%2 or f==s:
   r=node(p,r)
   while f and not f%2:f//=2;s//=2
  else:r=node(r,p)
  f//=2;s//=2
 return s==0 and r==claimed
def consistent(M,N,u,v,ps):
 if not 0<M<N:return False
 ps=([u] if M&(M-1)==0 else [])+ps
 if not ps:return False
 a=b=ps[0];f,s=M-1,N-1
 while f%2:f//=2;s//=2
 for p in ps[1:]:
  if s==0:return False
  if f%2 or f==s:
   a=node(p,a);b=node(p,b)
   while f and not f%2:f//=2;s//=2
  else:b=node(b,p)
  f//=2;s//=2
 return s==0 and a==u and b==v
inclusions=consistencies=0
for n in range(1,33):
 xs=[leaf(i) for i in range(n)];r=root(xs)
 for m in range(n):
  ps=path(xs,m);assert include(n,m,xs[m],ps,r)
  assert not include(n,m,leaf(-1),ps,r)
  assert not include(n,m,xs[m],ps+[leaf(-1)],r)
  inclusions+=1
 assert not include(n,n,leaf(n),[],r)
 for m in range(1,n):
  u=root(xs[:m]);ps=subproof(xs,m)
  assert consistent(m,n,u,r,ps),(m,n)
  assert not consistent(m,n,u,leaf(-1),ps)
  consistencies+=1
xs=[leaf(i) for i in range(7)];assert path(xs,3)==[xs[2],root(xs[:2]),root(xs[4:])]
assert subproof(xs,4)==[root(xs[4:])]
# Exhaustive one-counter programs, including jumps to halt, for k <= 4.
# INC falls through; DEC jumps to its target on positive input, falls through at zero.
programs=runs=0
for k in range(5):
 ops=[('inc',None)]+[('dec',j) for j in range(k+1)]
 for code in itertools.product(ops,repeat=k):
  programs+=1
  for initial in range(6):
   pc=0;v=initial;steps=0;seen=set();bound=k*(initial+k+1)
   while pc<k and (pc,v) not in seen and steps<=max(1000,bound*10):
    seen.add((pc,v));op,j=code[pc]
    if op=='inc':v+=1;pc+=1
    elif v:v-=1;pc=j
    else:pc+=1
    steps+=1
   if pc>=k:assert steps<=bound,(code,initial,steps,bound)
   runs+=1
report=dict(coverage_chunks=len(c),baseline_lines=len(old.splitlines()),baseline_words=len(old.split()),edits=len(es),headings_preserved=len(heads(old)),labels_preserved=len(labels(old)),unchanged_mathematical_statements=statement_counts,all_internal_references_resolve=True,source_sha256=hashlib.sha256(new.encode()).hexdigest(),worked_arithmetic_checks=True,fresh_storage_transitions=gas_cases,merkle_inclusion_paths=inclusions,merkle_consistency_paths=consistencies,one_counter_programs=programs,one_counter_runs=runs,scope='Finite examples and structural checks support review; they do not independently prove every theorem or validate physical realizations.')
(R/'pass-verification.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
