from itertools import product
import math, random, json
import sympy as s
from pathlib import Path
X=s.Matrix([[0,1],[1,0]]); Z=s.diag(1,-1); I=s.eye(2)
G=[s.kronecker_product(X,I,I),s.kronecker_product(Z,X,I),s.kronecker_product(Z,Z,X),s.kronecker_product(Z,Z,Z)]
for i,A in enumerate(G):
 assert A.T==A and A*A==s.eye(8) and s.trace(A)==0
 for j,B in enumerate(G):
  assert s.trace(A.T*B)==(8 if i==j else 0)
  if i!=j: assert A*B+B*A==s.zeros(8)
a=s.symbols('a:4',real=True); A=sum((a[i]*G[i] for i in range(4)),s.zeros(8))
assert s.simplify(A*A-s.eye(8)*sum(v*v for v in a))==s.zeros(8)
t,x,z=s.symbols('t x z',real=True)
p=lambda a,b,c:(1+t*a*b+x*a*c+z*b*c)/8
signs=(-1,1)
assert s.simplify(sum(p(*v) for v in product(signs,repeat=3)))==1
assert s.simplify(sum(v[0]*v[2]*p(*v) for v in product(signs,repeat=3)))==x
assert s.simplify(sum(v[1]*v[2]*p(*v) for v in product(signs,repeat=3)))==z
for a,b in product(signs,repeat=2):
 assert s.simplify(sum(p(a,b,c) for c in signs)-(1+t*a*b)/4)==0
rng=random.Random(20261011); accepted=0; endpoints=0
cases=list(product((-1.,0.,1.),repeat=4))+[tuple(rng.uniform(-1,1) for _ in range(4)) for _ in range(10000)]
for vals in cases:
 x,y,z,w=vals; ax,ay,az,aw=map(math.asin,vals)
 lo=max(abs(ax-ay),abs(az-aw));hi=min(math.pi-abs(ax+ay),math.pi-abs(az+aw))
 inequalities=max(abs(ax+ay+az-aw),abs(ax+ay-az+aw),abs(ax-ay+az+aw),abs(-ax+ay+az+aw))<=math.pi+1e-12
 assert inequalities==(lo<=hi+1e-12)
 if not inequalities:continue
 accepted+=1;d=(lo+hi)/2
 if abs(math.sin(d))<1e-12:
  endpoints+=1;assert abs(y-x*math.cos(d))<1e-12 and abs(w-z*math.cos(d))<1e-12
 else:
  c0=(y-x*math.cos(d))/math.sin(d);c1=(w-z*math.cos(d))/math.sin(d)
  assert 1-x*x-c0*c0>=-1e-10 and 1-z*z-c1*c1>=-1e-10
  assert abs(x*math.cos(d)+c0*math.sin(d)-y)<1e-10
  assert abs(z*math.cos(d)+c1*math.sin(d)-w)<1e-10
 lo=max(-1+abs(x+z),-1+abs(y+w));hi=min(1-abs(x-z),1-abs(y-w))
 local=max(abs(x+y+z-w),abs(x+y-z+w),abs(x-y+z+w),abs(-x+y+z+w))<=2+1e-12
 assert local==(lo<=hi+1e-12)
 if local:
  tv=(lo+hi)/2
  def triple(a,b,c,e,f):return (1+tv*a*b+e*a*c+f*b*c)/8
  probs=[]
  for a,b,c,d in product(signs,repeat=4):
   pa=(1+tv*a*b)/4;p0=triple(a,b,c,x,z);p1=triple(a,b,d,y,w)
   assert p0>=-1e-12 and p1>=-1e-12
   probs.append(((a,b,c,d),p0*p1/pa if pa>1e-14 else 0))
  assert abs(sum(p for _,p in probs)-1)<1e-10
  for (i,j),expected in zip(((0,2),(0,3),(1,2),(1,3)),vals):
   assert abs(sum(v[i]*v[j]*p for v,p in probs)-expected)<1e-10
report=dict(exact_Clifford_and_trace_identities=True,exact_triple_marginals=True,numerical_cases=len(cases),feasible_quantum_cases=accepted,degenerate_angle_cases=endpoints,note='Exact identities and finite numerical checks supplement the printed arguments; numerical checks are not proofs of the characterizations.')
Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
