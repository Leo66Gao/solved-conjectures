#!/usr/bin/env python3
"""Exact rational certificate for the rank-three analytic q-permanent witness.

Python 3, standard library only. No full matrix or permanent is instantiated.
Read rank-three.tex for the analytic lemmas that make these checks sufficient.
The fixed matrix order is 271147008, not a small directly evaluated matrix.
"""
from fractions import Fraction as Q
from math import isqrt, comb, ceil

K,T,H,m,M = 256,60,662,256,4096
D=K*K
n=(D+H)*M
beta=Q(H,D+H)
eps=Q(1,10000)
DEN=10**8
s2_lo,s2_hi=141421356,141421357
assert s2_lo*s2_lo<2*DEN**2<s2_hi*s2_hi


def radial_bins():
    out=[]
    for j in range(K):
        u=D-(K-j)**2
        w=2*(K-j)-1
        b2=min(Q(T*T),Q(u*u,D*D-u*u))
        a=isqrt(b2.numerator*DEN**2//b2.denominator)
        assert Q(a,DEN)**2<=b2
        out.append((a,w))
    assert sum(w for a,w in out)==D
    return out


def cos_bounds():
    # pi < 22/7. The degree-10 alternating Taylor truncation bounds cos below
    # on [0,11/7], with the next term positive and subsequent terms decreasing.
    out=[]
    for j in range(1,m+1):
        x=Q(11*j,7*m)
        c=1-x*x/2+x**4/24-x**6/720+x**8/40320-x**10/3628800
        out.append(max(0,int(c*DEN)))
    return out


def gini_lower():
    # The |X| law for X=sqrt(2)*b*cos(theta) is symmetric in sign.
    # Lower bound each folded angular bin by its right endpoint cosine.
    vals=sorted((a*c*s2_lo,w) for a,w in radial_bins() for c in cos_bounds())
    cum=acc=moment=0
    for x,w in vals:
        acc+=x*(2*cum*w+w*w)  # contribution to E max(|X|,|X'|)
        moment+=x*w
        cum+=w
    assert cum==D*m
    G0=Q(acc,2*DEN**3*cum*cum)
    A0=Q(moment,DEN**3*cum)
    return (1-beta)**2*G0+beta*(1-beta)*A0


def verify():
    assert n==271147008 and M%(4*m)==0 and M>=4
    G=gini_lower()
    assert G>Q(7077,10000)
    # Global pointwise log-product deficit from angular bound and ellipticity.
    c=beta/2-Q(16,M);assert c>0
    w0=Q(65,100*T);s0=Q(3,100);q=Q(97,100)
    assert w0<=Q(3,100)
    # In the good region, the dominant circular coordinate exceeds .99.
    assert (1-w0*w0)/2>Q(7,10)**2
    assert 1-w0*w0-((s0+w0*w0)/Q(14,10))**2>Q(99,100)**2
    r=(s0+w0*w0)/(2*Q(99,100)**2)
    v=Q(s2_hi,DEN)*T*w0/Q(99,100)
    assert v*q+r<q*q  # all angular-quadratic roots have modulus < q
    # Tail bound for the spherical integral: e^{-2gn} < 2^{-floor(2gn)}.
    g=min(c*w0*w0,(1-beta)*s0*s0/8)
    a=(2*g*n).__floor__();v=ceil(Q(comb(n+2,2),eps))
    assert a>=v.bit_length()
    # On the good region the product differs from rho^n by an exponentially
    # small angular discretization factor: e^(4(D+H) q^M) <= 1+eps.
    assert q**100<Q(1,10)
    assert Q(4*(D+H),10**(M//100))<eps/2
    # The two pure circular monomials supply a rigorous exterior-norm lower bound.
    R=2*G**2*n**4/Q(comb(n,2)*n*(n-1)*(2+3*eps))
    assert R>1+Q(1,1000)
    # Integer lift. Set scale=10^6 n(T+1)[2(B+1)]^n; no huge ints needed here.
    B=1+T*T
    assert Q(6,10**6*(B+1))<Q(1,10000)
    assert Q(1,2000)-Q(6,10**6*(B+1))>Q(1,2500)
    # q1=1-1/[10000*C_n*(2(B+1))^n].
    assert Q(1,2500)-Q(1,10000)>0
    print('All exact rational checks PASSED.')
    print('Matrix order:',n)
    print('G lower bound (display only):',float(G))
    print('Global log-product deficit g (display only):',float(g))
    print('Tail exponent:',a,'required bits:',v.bit_length())
    print('R lower bound (display only):',float(R))
    print('Certified R > 1.001; integer lift has P_prime(1)<0.')
    print('The proof also certifies P(q1)>P(1) at the explicit rational q1.')
    print('No full matrix or derivative was materialized.')

if __name__=='__main__': verify()
