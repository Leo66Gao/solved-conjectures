#!/usr/bin/env python3
"""Deterministic checks of the length/composition term, not of the overlap remainder."""
from fractions import Fraction
from math import ceil, comb, erfc, log, pi, sqrt
from functools import lru_cache

@lru_cache(None)
def pmf(n,k):
    return comb(n,k)/2**n

def cdf_central(n,k):
    if k<0:return 0.
    if 2*k>n: return 1-cdf_central(n,n-k-1)
    h=n//2
    mass=pmf(n,h)
    ans=.5+(mass/2 if n%2==0 else 0)
    for j in range(h,k,-1):
        ans-=mass;mass*=j/(n-j+1)
    return ans

def favor(d,z,p):
    # Exact test q^d (p/q)^z > 1.
    a,b=p.numerator,p.denominator; c=b-a
    if z<0:return c**(d-z)>b**d*a**(-z)
    return c**d*a**z>b**d*c**z

def cutoff(d,p):
    c=-log(1-float(p))/log((1-float(p))/float(p))
    k=int(-c*d)
    while not favor(d,k,p):k-=1
    while favor(d,k+1,p):k+=1
    return k

def h_raw(N,p):
    # normalized mixture restricted to i,d<=28; omitted geometric mass <4e-9 for N>=100.
    z=h=0.
    for d in range(1,29):
        k=cutoff(d,p)
        for i in range(29):
            m=N-i-d
            if m<1:continue
            t=2.**(-2*i-d);z+=t;h+=t*cdf_central(2*m+d,m+k)
    return h/z

if __name__=='__main__':
    p=Fraction(1,3)
    c=-log(1-float(p))/log((1-float(p))/float(p))
    S=.5+sum(2**(-d)*ceil(d*c) for d in range(1,100))
    L=sum(2**(-d)*.5*erfc(d*log(2)/4) for d in range(1,100)) # lambda = 1
    print('Fixed p=1/3: sqrt(pi*N)*(1/2-H_raw) ->',format(S,'.8f'))
    print('Window lambda=1: H_raw ->',format(L,'.8f'))
    print('N    scaled fixed deficit   window fraction')
    for r in (10,20,40,80):
        n=r*r
        print(n,format(sqrt(pi*n)*(.5-h_raw(n,p)),'.8f'),
              format(h_raw(n,Fraction(1,2)-Fraction(1,r)),'.8f'))
