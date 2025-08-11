#!/usr/bin/env python3
"""Self-verifying Thiele Machine artifact.
Stdlib-only script that embeds the fossil record, solves for a per-depth
linear "sphere" model, proves no planar model fits the same data, and can
produce a planar "monster" when depth discreteness is relaxed.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from decimal import Decimal, getcontext
from itertools import combinations
import argparse
import hashlib
import sys
from typing import List, Dict, Tuple

getcontext().prec = 50

@dataclass
class Row:
    name: str
    W: Fraction
    K: Fraction
    d: Fraction
    T: Fraction


def fossil_record() -> List[Row]:
    data = [
        ("Reversal", 5, 5, 1, 1),
        ("Mandelbrot", 5444, 312, 2, 50),
        ("Game of Life", 900, 264, 4, 2),
        ("Axiom of Blindness", 10, 184, 1, 1),
        ("Geometry of Truth", 112, 264, 1, 4),
        ("Lensing", 0, 0, 2, 1),
        ("N-Body and FLRW", 0, 0, 3, 1),
        ("Phyllotaxis", 0, 0, 2, 1),
        ("Universality", 0, 112, 1, 1),
        ("Thiele Machine", 0, 0, 1, 1),
        ("NUSD Law", 0, 72, 1, 1),
        ("Universality Demo", 0, 992, 1, 1),
        ("Physical Realization", 0, 96, 1, 1),
        ("Scale Comparison", 0, 96, 1, 1),
        ("Capstone Demonstration", 0, 224, 1, 1),
        ("Process Isomorphism", 0, 280, 1, 1),
        ("Geometric Logic", 0, 240, 1, 1),
        ("Halting Experiments", 0, 264, 1, 1),
        ("Geometry of Coherence", Fraction('7.46'), 96, 1, 1),
        ("Conclusion", Fraction('7.46'), 96, 1, 1),
    ]
    return [Row(n,Fraction(str(W)),Fraction(K),Fraction(d),Fraction(T)) for n,W,K,d,T in data]

# ---------- utility ----------

def det3(m: List[List[Fraction]]) -> Fraction:
    a,b,c = m[0]
    d,e,f = m[1]
    g,h,i = m[2]
    return a*e*i + b*f*g + c*d*h - c*e*g - b*d*i - a*f*h


def solve3(A: List[List[Fraction]], b: List[Fraction]) -> List[Fraction]:
    M=[row[:] + [b[i]] for i,row in enumerate(A)]
    n=3
    for col in range(n):
        pivot=col
        while pivot<n and M[pivot][col]==0:
            pivot+=1
        if pivot==n:
            raise ValueError('singular')
        if pivot!=col:
            M[col],M[pivot]=M[pivot],M[col]
        pv=M[col][col]
        for j in range(col,n+1):
            M[col][j]/=pv
        for r in range(n):
            if r!=col and M[r][col]!=0:
                fac=M[r][col]
                for j in range(col,n+1):
                    M[r][j]-=fac*M[col][j]
    return [M[i][n] for i in range(n)]

# ---------- transcript logger ----------
class Logger:
    def __init__(self):
        self.lines: List[str] = []
    def log(self, msg: str):
        self.lines.append(msg)
        print(msg)
    def digest(self):
        text='\n'.join(self.lines).encode()
        return hashlib.sha256(text).hexdigest(), text

# ---------- sphere witness ----------

def sphere_witness(rows: List[Row], eps: Decimal, log: Logger) -> Tuple[Dict[int,Tuple[Fraction,Fraction,Fraction]], Decimal]:
    groups: Dict[int,List[Row]]={1:[],2:[],3:[],4:[]}
    for r in rows:
        groups[int(r.d)].append(r)
    theta: Dict[int,Tuple[Fraction,Fraction,Fraction]]={}
    max_res=Decimal('0')
    for depth in sorted(groups):
        grp=groups[depth]
        if not grp:
            theta[depth]=(Fraction(0),Fraction(0),Fraction(0))
            continue
        best=None
        rows_idx=list(range(len(grp)))
        for combo in combinations(rows_idx,3) if len(grp)>=3 else []:
            A=[[grp[i].K,grp[i].T,Fraction(1)] for i in combo]
            if det3(A)==0:
                continue
            b=[grp[i].W for i in combo]
            coeff=solve3(A,b)
            # verify
            res=Decimal('0')
            ok=True
            for r in grp:
                pred=coeff[0]*r.K + coeff[1]*r.T + coeff[2]
                diff=abs(Decimal(pred.numerator)/Decimal(pred.denominator)-Decimal(r.W.numerator)/Decimal(r.W.denominator))
                if diff>eps:
                    ok=False
                if diff>res:
                    res=diff
            if ok and (best is None or res<best[1]):
                best=(coeff,res)
        if best is None:
            # fallback simple fit using first row
            r0=grp[0]
            aK=Fraction(0)
            aT=Fraction(0)
            a0=r0.W
            if r0.K!=0:
                aK=r0.W/r0.K
                a0=Fraction(0)
            elif r0.T!=0:
                aT=r0.W/r0.T
                a0=Fraction(0)
            coeff=(aK,aT,a0)
            res=Decimal('0')
            for r in grp:
                pred=coeff[0]*r.K + coeff[1]*r.T + coeff[2]
                diff=abs(Decimal(pred.numerator)/Decimal(pred.denominator)-Decimal(r.W.numerator)/Decimal(r.W.denominator))
                if diff>res:
                    res=diff
            best=(coeff,res)
        theta[depth]=tuple(best[0])
        if best[1]>max_res:
            max_res=best[1]
    # print theta
    log.log("=== SPHERE WITNESS ===")
    for d in sorted(theta):
        aK,aT,a0=theta[d]
        log.log(f"d={d}: aK={aK} ({float(aK):.6g}), aT={aT} ({float(aT):.6g}), a0={a0} ({float(a0):.6g})")
    log.log(f"max_residual={max_res}")
    return theta,max_res

# ---------- plane certificate ----------

def rref(mat: List[List[Fraction]]) -> Tuple[List[List[Fraction]], List[int]]:
    A=[row[:] for row in mat]
    m=len(A); n=len(A[0])
    pivots=[]
    r=0
    for c in range(n):
        pivot=None
        for i in range(r,m):
            if A[i][c]!=0:
                pivot=i; break
        if pivot is None:
            continue
        A[r],A[pivot]=A[pivot],A[r]
        pv=A[r][c]
        A[r]=[x/pv for x in A[r]]
        for i in range(m):
            if i!=r and A[i][c]!=0:
                fac=A[i][c]
                A[i]=[A[i][j]-fac*A[r][j] for j in range(n)]
        pivots.append(c)
        r+=1
        if r==m:
            break
    return A,pivots

def nullspace(mat: List[List[Fraction]]) -> List[List[Fraction]]:
    rref_mat,pivots=rref(mat)
    m=len(rref_mat); n=len(rref_mat[0])
    free=[c for c in range(n) if c not in pivots]
    basis=[]
    for f in free:
        vec=[Fraction(0) for _ in range(n)]
        vec[f]=1
        for i,p in enumerate(pivots):
            vec[p]=-rref_mat[i][f]
        basis.append(vec)
    return basis


def plane_certificate(rows: List[Row], log: Logger) -> Tuple[List[int], List[Fraction], Fraction, List[Fraction]]:
    indices=list(range(5))
    M=[]; w=[]
    for idx in indices:
        r=rows[idx]
        M.append([r.K,r.d,r.T,Fraction(1)])
        w.append(r.W)
    # solve nullspace of M^T
    A=[[M[i][j] for i in range(len(M))] for j in range(4)]
    basis=nullspace(A)
    lam=basis[0]
    Mtlam=[sum(lam[i]*M[i][j] for i in range(len(M))) for j in range(4)]
    lamw=sum(lam[i]*w[i] for i in range(len(M)))
    log.log("=== PLANE CERTIFICATE ===")
    log.log("rows used: " + ",".join(str(i) for i in indices))
    log.log("lambda:" + ",".join(str(l) for l in lam))
    log.log("lambda_decimal:" + ",".join(f"{float(l):.6g}" for l in lam))
    log.log("M^T lambda:" + ",".join(str(x) for x in Mtlam))
    log.log(f"lambda^T w={lamw} ({float(lamw):.6g})")
    return indices,lam,lamw,Mtlam

# ---------- monster ----------

def planar_fit(rows: List[Row], indices: List[int]) -> List[Fraction]:
    A=[[rows[i].K, rows[i].d, rows[i].T, Fraction(1)] for i in indices]
    b=[rows[i].W for i in indices]
    # solve 4x4 system
    M=[row[:] + [b[i]] for i,row in enumerate(A)]
    n=4
    for col in range(n):
        pivot=col
        while pivot<n and M[pivot][col]==0:
            pivot+=1
        if pivot==n:
            raise ValueError('singular')
        if pivot!=col:
            M[col],M[pivot]=M[pivot],M[col]
        pv=M[col][col]
        for j in range(col,n+1):
            M[col][j]/=pv
        for r in range(n):
            if r!=col and M[r][col]!=0:
                fac=M[r][col]
                for j in range(col,n+1):
                    M[r][j]-=fac*M[col][j]
    return [M[i][n] for i in range(n)]


def monster_run(rows: List[Row], eps: Decimal, log: Logger):
    indices=[0,1,2,3]
    coeff=planar_fit(rows,indices)
    passes=0
    for r in rows:
        pred=coeff[0]*r.K + coeff[1]*r.d + coeff[2]*r.T + coeff[3]
        diff=abs(Decimal(pred.numerator)/Decimal(pred.denominator)-Decimal(r.W.numerator)/Decimal(r.W.denominator))
        if diff<=eps:
            passes+=1
    log.log("=== MONSTER (RELAXED AXIOM) ===")
    log.log("alpha:"+",".join(str(c) for c in coeff))
    log.log("alpha_decimal:"+",".join(f"{float(c):.6g}" for c in coeff))
    log.log(f"rows_within_eps={passes} of {len(rows)}")

# ---------- main ----------

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--prove',action='store_true',default=False)
    p.add_argument('--relax-depth',action='store_true')
    p.add_argument('--epsilon',type=float,default=1e-9)
    p.add_argument('--save-ledger')
    args=p.parse_args()
    rows=fossil_record()
    log=Logger()
    eps=Decimal(str(args.epsilon))
    # Act I: axiom checks
    log.log("=== DATA & AXIOMS ===")
    for idx,r in enumerate(rows):
        if r.W<0 or r.K<0 or r.d<0 or r.T<0:
            log.log(f"AXIOM FAIL: A_nonneg row {idx}"); sys.exit(1)
        if not args.relax_depth and r.d not in (1,2,3,4):
            log.log(f"AXIOM FAIL: A_depth_discrete row {idx}"); sys.exit(1)
        if r.K==0 and r.d==0 and r.T!=0:
            log.log(f"AXIOM FAIL: A_no_pure_time row {idx}"); sys.exit(1)
    log.log(f"rows={len(rows)} pass base axioms")
    if args.prove:
        theta,max_res=sphere_witness(rows,eps,log)
        if max_res>eps:
            log.log("SPHERE: FAIL");
            sha,_=log.digest()
            log.log("PROOF_SHA256:"+sha)
            if args.save_ledger:
                with open(args.save_ledger,'w') as f: f.write('\n'.join(log.lines))
            sys.exit(1)
        indices,lam,lamw,Mtlam=plane_certificate(rows,log)
        if lamw==0:
            log.log("PLANE: INCONCLUSIVE");
            sha,_=log.digest()
            log.log("PROOF_SHA256:"+sha)
            if args.save_ledger:
                with open(args.save_ledger,'w') as f: f.write('\n'.join(log.lines))
            sys.exit(1)
        else:
            log.log("PLANE: UNSAT")
    if args.relax_depth:
        monster_run(rows,eps,log)
    sha,text=log.digest()
    log.log("=== TRANSCRIPT HASH ===")
    log.log("PROOF_SHA256:"+sha)
    if args.save_ledger:
        with open(args.save_ledger,'w') as f:
            f.write(text.decode())

if __name__=='__main__':
    main()
