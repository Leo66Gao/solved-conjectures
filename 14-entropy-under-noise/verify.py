#!/usr/bin/env python3
"""Exact checks for Shannon entropy along independent refresh dynamics. Python 3 standard library."""
from fractions import Fraction as F
from itertools import product
from math import comb
from collections import defaultdict

def expand(A,B,C,wx,wy,N):
    result=[F(0)]*(N+1)
    for s,t in product((-1,1),repeat=2):
        terms=((wx,A*s),(wy,B*t),(wx+wy,C*s*t)); power={0:F(1)}
        for j in range(1,N+1):
            nxt=defaultdict(F)
            for k,u in power.items():
                for l,v in terms:
                    if k+l<=N:nxt[k+l]+=u*v
            power=nxt
            if j>=2:
                for k,u in power.items(): result[k]+=F((-1)**j,4*j*(j-1))*u
    return result

def mixed(i,j,v):
    if not j:return F(1,i*(i-1))
    return sum(F(comb(j,h)*(-1)**(i-h)*comb(j-2+i-h,i-h),j*(j-1))*v**h for h in range(min(i,j)+1))

def test():
    v=F(5,2);k=F(3,2)
    c=[mixed(12-2*j,j,v) for j in (0,2,4,6)]
    assert c==[F(1,132),F(9,8),F(-45,64),F(1,30)]
    coef=sum(t*k**(2*j) for j,t in enumerate(c))
    assert coef==F(-108313,168960)
    a=F(1,8);b=k*a*a
    assert 1-a-b-v*a*b>0
    assert expand(a,b,v*a*b,1,2,12)[12]==coef*a**12
    print('1:2 weighted coefficient / a^12:',coef)
    # Modest independent exact stress test; not the proof of the infinite family.
    checked=0
    for A,B,C in product([F(i,4) for i in range(-4,5)],repeat=3):
        if min(1+A*s+B*t+C*s*t for s,t in product((-1,1),repeat=2))<0:continue
        out=expand(A,B,C,1,1,20)
        assert all(x>=0 for x in out)
        checked+=1
    print('Two equal rates: admissible test laws with all coefficients nonnegative through degree 20:',checked)
    # 3-bit witness at t=log(16) for f=1+(xy+xz+yz)/2.
    # Scaled (-1)^19 D^(19)/2^19. If a_j is the jth summand in absolute
    # value, bound it above by j^19(3u)^j/[j(j-1)], since
    # (3^j+3)/4 <= 3^j. Successive majorant ratio <= (1+1/j)^19 3u.
    u=F(1,512);J=20
    partial=sum(F(j**19*((-3)**j+3),4*j*(j-1))*u**j for j in range(2,J+1))
    ratio=(1+F(1,J+1))**19*3*u
    rem=F((J+1)**19,(J+1)*J)*(3*u)**(J+1)/(1-ratio)
    assert 0<ratio<1 and F(-95,1000)<partial-rem<=partial+rem<F(-94,1000)
    print('3-bit witness: (-1)^19 D^(19)(log 16)/2^19 strictly between -0.095 and -0.094.')
if __name__=='__main__':test()
