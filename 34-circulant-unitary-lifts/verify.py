#!/usr/bin/env python3
"""Exact cross-checks for two circulant-lifting obstructions, not phase fitting."""
from itertools import product
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from math import isqrt
import sympy as sp

def signcheck(k):
    def corr(e,h):
        return sum(e[i]*e[(i+h)%k]*(1 if i+h<k else -1) for i in range(k))
    count=sum(all(corr(e,h)==0 for h in range(1,k)) for e in product((1,-1),repeat=k))
    assert count==({1:2,2:4}.get(k,0))
    return count

def ring(k):
    # Z[zeta_k] exactly, represented by the coefficient vector of degree < phi(k).
    x=sp.Symbol('x')
    phi=sp.Poly(sp.cyclotomic_poly(k,x),x)
    basis=[sp.Poly(x**j,x).rem(phi) for j in range(k)]
    dim=phi.degree()
    power=tuple(tuple(int(p.nth(i)) for i in range(dim)) for p in basis)
    def ev(c):
        return tuple(sum(a*power[h%k][i] for h,a in c.items()) for i in range(dim))
    return ev

def plus(a,b):
    return a+b
def ip(A,B):
    out=Counter()
    for x,y in zip(A,B):
        for r,a in x.items():
            for s,b in y.items(): out[r-s]+=a*b
    return out

def check_band(k,m):
    n=k*m
    ev=ring(k)
    # W=(5k) U. Every coefficient is an ordinary integer in the cyclotomic ring.
    def elt(i,j):
        a,r=divmod(i,m); b,l=divmod(j,m)
        c=Counter()
        if r==l:
            if a==b: c[0]+=5*k
            c[0]-=2; c[a-b]-=2
        elif (l-r)%m==1: c[-b]+=4
        elif (l-r)%m==m-1: c[a]-=4
        return dict(c)
    W=[[elt(i,j) for j in range(n)] for i in range(n)]
    norm=(5*k)**2
    B=[[ev(ip([x],[x])) for x in row] for row in W]
    for i in range(n):
        for j in range(n):
            assert ev(ip(W[i],W[j]))==ev({0:norm*int(i==j)})
            assert B[i][j]==B[0][(j-i)%n]
    # For all samples lateral squares in the chosen normalization are exactly 16.
    assert all(B[0][j]==ev({0:16}) for j in range(1,n,m))
    scaled_mass=k*sum(Fraction(B[0][j][0],norm) for j in range(1,n,m))
    assert scaled_mass==Fraction(16,25)
    return scaled_mass

def check_even(k):
    # For the displayed a^2=1/2, let W=sqrt(2k) U. Entries are either
    # sqrt(k) on the diagonal or signed cyclotomic monomials otherwise.
    ev=ring(k)
    n=2*k
    def elt(i,j):
        if i==j:return (1,{0:1})
        if i%2==j%2:return (0,{})
        r=i//2;s=j//2
        return (0,{r*s:1}) if i%2==0 else (0,{-r*s:-1})
    W=[[elt(i,j) for j in range(n)] for i in range(n)]
    for i in range(n):
        for j in range(n):
            # Accumulate constant and sqrt(k) parts separately: stronger than
            # necessary when sqrt(k) lies in the cyclotomic field.
            parts=[Counter(),Counter()]
            for (d,v),(f,w) in zip(W[i],W[j]):
                for h,coef in ip([v],[w]).items():
                    parts[(d+f)%2][h]+=coef*(k if d+f==2 else 1)
            assert ev(parts[0])==ev({0:n*int(i==j)}) and ev(parts[1])==ev({})
            d,v=W[i][j]; sq=ip([v],[v]); sq={h:c*(k if d else 1) for h,c in sq.items()}
            assert ev(sq)==ev({0:k if i==j else int((j-i)%2==1)})
    return [Fraction(1,2)]+[Fraction(1,2*k) if j%2 else Fraction(0) for j in range(1,n)]

if __name__=='__main__':
    for k in range(1,15):
        print(f'negacyclic signs k={k}: {signcheck(k)} complete solutions')
    for k in range(2,10):
        p=check_even(k)
        print(f'd={2*k} exact Fourier-block unitarity/moduli OK' + (f'; first row {list(map(str,p))}' if k==3 else ''))
    for k,m in [(2,5),(3,5),(3,7),(5,5),(5,7),(4,5)]:
        print(f'd={k*m}: k={k}, m={m}, exact Gram+every circulant square checked; kM_plus={check_band(k,m)}')
    print('PASS')
