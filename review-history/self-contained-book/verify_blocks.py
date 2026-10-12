from pathlib import Path
import json
DATA=json.loads(Path('/workspace/The-Thiele-Machine-book-design/thiele_small/data/programs.json').read_text())
def inc(r):return [[0,r,0]]
def dec(r,p):return [[1,r,p]]
def jump(a,p,o):return inc(a)+dec(a,p)
def zero(x,o):return dec(x,o)
def jz(x,p,o):return dec(x,o+3)+jump(x,p,o+1)+inc(x)
def move(x,y,o):return jump(x,o+3,o)+inc(y)+dec(x,o+2)
def move2(x,y,z,o):return jump(x,o+4,o)+inc(y)+inc(z)+dec(x,o+2)
def copy(x,y,t,o):return zero(y,o)+zero(t,o+1)+move2(x,y,t,o+2)+move(t,x,o+7)
def half(a,x,p,o):return zero(a,o)+move(x,a,o+1)+jump(a,o+8,o+5)+inc(x)+dec(a,o+11)+jump(a,p,o+9)+dec(a,o+7)
def pack(a,x,y,o):return zero(a,o)+move2(x,a,a,o+1)+inc(a)+move(a,x,o+7)+jump(a,o+22,o+11)+move2(x,a,a,o+13)+move(a,x,o+18)+dec(y,o+13)
def unpack(a,x,y,o):return jz(x,0,o)+zero(y,o+4)+jump(a,o+8,o+5)+inc(y)+half(a,x,o+7,o+8)
def select(x,t,targets,o):
 out=[]
 for i,p in enumerate(targets):out+=dec(x,o+3*i+3)+jump(t,p,o+3*i+1)
 return out
def equal(x,y,t1,t2,u,p,o):return copy(x,t1,u,o)+copy(y,t2,u,o+11)+dec(t1,o+29)+jz(t2,p,o+23)+jump(u,o+32,o+27)+dec(t2,o+22)+jump(u,o+32,o+30)+zero(t1,o+32)+zero(t2,o+33)
def fetch(q,l,w,k,h,a,t,p0,pe,o):return copy(q,w,t,o)+copy(l,k,t,o+11)+jz(k,p0,o+22)+dec(k,o+27)+jz(w,pe,o+27)+unpack(a,w,h,o+31)+jz(k,o+56,o+51)+dec(k,o+27)
def generate(priced=False):
 shift=3 if priced else 0
 base=[1,98,109,117,169,221,249,309,369,397,1419,2441,2469,3097,3725]
 labels=[1]+[x+shift for x in base[1:]];H=1;K=labels[1]
 code=[];lengths=[]
 def emit(block):
  o=len(code)+1;assert o==labels[len(lengths)],(o,labels[len(lengths)]);code.extend(block(o));lengths.append(len(code)+1-o)
 handlers=[labels[i] for i in [2,5,1,8,11,14]]+([3732] if priced else [])
 emit(lambda o:fetch(2,3,4,5,6,7,8,K,K,o)+zero(4,o+56)+unpack(7,6,9,o+57)+select(9,8,handlers,o+77)+jump(8,K,o+77+3*len(handlers)))
 emit(lambda o:sum([zero(4+i,o+i) for i in range(10)],[])+[[2,0,0]])
 def bank(a,b,split,o):return (unpack(7,6,10,o)+select(10,8,[a,b],o+20)+jump(8,K,o+26)) if split else select(6,8,[a,b],o)+jump(8,K,o+6)
 def bumps(c,o):return sum([inc(48+16*c+k)+dec(48+16*c+k,o+3*k+2)+zero(16+16*c+k,o+3*k+2) for k in range(16)],[])
 emit(lambda o:bank(labels[3],labels[4],False,o))
 for c in [0,1]:emit(lambda o,c=c:inc(c)+bumps(c,o+1)+inc(3)+jump(8,H,o+50))
 emit(lambda o:bank(labels[6],labels[7],True,o))
 for c in [0,1]:emit(lambda o,c=c:dec(c,o+5)+inc(3)+zero(6,o+2)+jump(8,H,o+3)+bumps(c,o+5)+zero(3,o+53)+move(6,3,o+54)+jump(8,H,o+58))
 emit(lambda o:bank(labels[9],labels[10],True,o))
 def cks(c,k,o):
  sl=48+16*c+k;mp=16+16*c+k
  return copy(c,12,8,o)+copy(6,13,8,o+11)+pack(7,12,13,o+22)+move(12,sl,o+45)+[[3,sl,0]]+zero(mp,o+50)+move(6,mp,o+51)+inc(mp)+inc(14+c)+inc(3)+jump(8,H,o+58)
 def ckh(c,o):return copy(14+c,11,8,o)+select(11,8,[o+62+60*k for k in range(16)],o+11)+[[3,80,0]]+jump(8,K,o+60)+sum([cks(c,k,o+62+60*k) for k in range(16)],[])
 for c in [0,1]:emit(lambda o,c=c:ckh(c,o))
 emit(lambda o:bank(labels[12],labels[13],True,o))
 def cms(c,k,o):return [[4,48+16*c+k,0]]+zero(6,o+1)+inc(3)+jump(8,H,o+3)
 def cmh(c,o):return inc(6)+sum([equal(16+16*c+k,6,11,12,8,o+548+5*k,o+1+34*k) for k in range(16)],[])+[[4,80,0]]+jump(8,K,o+546)+sum([cms(c,k,o+548+5*k) for k in range(16)],[])
 for c in [0,1]:emit(lambda o,c=c:cmh(c,o))
 emit(lambda o:[[5,0,0]]+inc(3)+jump(8,H,o+2))
 if priced:code += [[6,0,0]]+inc(3)+jump(8,H,3734)
 return code,lengths
for priced,key in [(False,'U'),(True,'U_P')]:
 book,ls=generate(priced);ref=DATA[key]
 assert len(book)==len(ref),(key,len(book),len(ref))
 diff=[(i+1,a,b) for i,(a,b) in enumerate(zip(book,ref)) if a!=b]
 assert not diff,(key,diff[:10])
 print(key,len(book),'instructions;',sum(x[0]>=3 for x in book),'paid sites; every instruction and target matches; lengths',ls)
