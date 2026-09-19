"""External exact-arithmetic candidate checks; does not execute the VM or its checker."""
from fractions import Fraction as F
for t in range(1,101):
    a=((4*t,t),(9*t,t))
    b=((a[0][0]+77*t,a[0][1]+8*t),(a[1][0],a[1][1]+35*t))
    assert b==((81*t,9*t),(9*t,36*t))
    s=9*t
    a2=((b[0][0]+7*s,b[0][1]+3*s),(b[1][0]+35*s,b[1][1]))
    assert a2==((144*t,36*t),(324*t,36*t))
for u in range(5):
 for v in range(5):
  for a in range(5):
   for b in range(5):
    x=F(6*(u-v)+8*(a-b),10*(u+v+a+b+1))
    y=F(8*(u-v)-6*(a-b),10*(u+v+a+b+1))
    assert x*x+y*y<1
    for c,d,zero in [(F(3,5),F(4,5),u==v),(F(4,5),F(-3,5),a==b)]:
     p=1-x*x-c*c; q=1-y*y-d*d; r=x*y+c*d
     assert (p>=0 and q>=0 and p*q>=r*r)==zero
print('100 scale transitions and 1250 rational selector checks passed (external arithmetic only).')
