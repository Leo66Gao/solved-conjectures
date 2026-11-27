#!/usr/bin/env python3
"""Rigorous finite Property B bounds, only exact integer/rational arithmetic.
Optional NumPy accelerates the same cap-safe fixed-point recurrences (uint64).
For example: python verify_high.py 7 131 16384
"""
from fractions import Fraction as F
from math import comb
import sys
def C(n,k): return comb(n,k) if 0<=k<=n else 0
def ceil(x):return -(-x.numerator//x.denominator)
def pos(v,r,m): # sum min of three bounds, with common denominator
    s=r-1;b=C(v-1,s);c=C(v-r,s)
    assert c>0
    arr=[C(i,s) for i in range(v)]
    # Fisher rank, sunflower/non-sunflower degree bound, and Turan.
    w=min(v,max(r*r-r+1,(v-1)//(r-1)))
    k,big=divmod(m,w)
    g=m*m-(w-big)*k*k-big*(k+1)*(k+1)
    a=sum(min(r*m*c*i,r*m*c*j,g*i*j) for i,j in zip(arr,reversed(arr)))
    return F(a,v*b*c)
def degs(r,m,H):
    """Upper vs d on grid. Integral minus unrounded midpoint mean <=1/H,
    since for every realization of link weights the event as a function
    of pivot x is an interval or empty."""
    assert H%2==0
    Q=1<<30; s=r-1; den=(2*H)**s
    vals=[]
    for j in range(H//2):
        a=(2*j+1)**s;b=(2*H-2*j-1)**s
        # lower no-red/no-blue probability; upper neither probability.
        vals.append(((den-a)*Q//den,(den-b)*Q//den,((den-a-b)*Q+den-1)//den))
    sums=[0]*(m+1)
    try:import numpy as np
    except ImportError:np=None
    if np is None:
        for a,b,c in vals:
            A=B=Z=Q
            for d in range(1,m+1):
                A=A*a//Q; B=B*b//Q; Z=(Z*c+Q-1)//Q
                sums[d]+=Q-A-B+Z
    else:
        a,b,c=np.array(vals,dtype=np.uint64).T.copy()
        A=B=Z=np.full(H//2,Q,dtype=np.uint64)
        assert (H//2)*2*Q<2**64 and Q*Q+Q<2**64
        for d in range(1,m+1):
            A=(A*a)>>30; B=(B*b)>>30; Z=(Z*c+(Q-1))>>30
            # all intermediate values nonnegative; total <=(H/2)*2*Q
            sums[d]=int(((Q+Z)-(A+B)).sum(dtype=np.uint64))
    # common denominator H*Q. Symmetry doubles the half-grid; integration
    # error is upper bounded by Q/(H*Q).
    return [2*z+Q for z in sums],H*Q

def hull(xs,lo,hi,tot,v,den):
    """Max over arbitrary fractional distribution of degrees with given mean."""
    hull=[]
    for d in range(lo,hi+1):
        u=xs[d]
        while len(hull)>=2:
            (z,p),(j,q)=hull[-2:]
            if (q-p)*(d-j)>(u-q)*(j-z):break
            hull.pop()
        hull.append((d,u))
    if len(hull)==1:return F(v*hull[0][1],den)
    for (a,b),(c,e) in zip(hull,hull[1:]):
        if a*v<=tot<=c*v:
            return F(b*(c*v-tot)+e*(tot-a*v),den*(c-a))
    raise AssertionError
def check(r,m,H):
    xs,den=degs(r,m,H)
    results={};tested=0
    for v in range(2*r-1,r*m+1):
        if C(v,2)>m*C(r,2):break
        if m*(C(v//2,r)+C((v+1)//2,r))<C(v,r):continue
        # Enough distinct r-sets to extend the pair-covered quotient to m.
        assert C(v,r)>=m
        lo=(v+r-3)//(r-1);total=r*m
        hi=min(m,total-(v-1)*lo)
        if hi<lo:continue
        z=pos(v,r,m);method='position'
        if z>=1:
            z=hull(xs,lo,hi,total,v,den);method='splitting'
        if z>=1:
            raise RuntimeError(f'uncertified (r,m,v)=({r},{m},{v}): {z}')
        if method not in results or z>results[method][0]:results[method]=(z,v)
        tested+=1
    print(f'PASS m({r}) >= {m+1} : {tested} eligible v; grid H={H}.')
    for k,(z,v) in results.items():
        print('   worst',k,'v=',v,'upper',ceil(z*10**9),'/10^9')
    return results
if __name__=='__main__':
    if len(sys.argv)==4:check(*map(int,sys.argv[1:]))
    else:
        for args in [(7,131,16384),(8,268,32768),(9,546,32768),(10,1117,32768),(11,2286,524288),(12,4677,131072)]:
            check(*args)
