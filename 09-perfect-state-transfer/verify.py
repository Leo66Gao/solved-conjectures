"""Exact regression checks for the theorems in paper.tex; no time sampling."""
from itertools import combinations
from math import gcd
from fractions import Fraction
from random import Random
import sympy as sy

x = sy.symbols('x')
Z = lambda f: sy.Poly(f, x, domain=sy.ZZ)
phi = lambda d: Z(sy.cyclotomic_poly(d, x))
one = Z(1)
xx = Z(x)
rng = Random(261126)

def vp(a,p):
    a=abs(a)
    assert a
    v=0
    while a%p==0:
        a//=p; v+=1
    return v

def support_test():
    tested=0
    for n in range(2,61):
        divs=[int(d) for d in sy.divisors(n) if d>1]
        mixed=[d for d in divs if len(sy.factorint(d))>1]
        for k in range(len(mixed)+1):
            for omitted in combinations(mixed,k):
                P=one
                for d in omitted: P *= phi(d)
                C=(one-P).exquo(one-xx)
                # Inverse Fourier spectrum numerator, directly from lambda congruence.
                F=Z(sum((j+n*C.nth(j))*x**j for j in range(n)))
                for d in divs:
                    assert F.rem(phi(d)).is_zero == (d in omitted),(n,d,omitted)
                tested+=1
    return tested

def norm_test():
    tested=0
    for d in range(2,41):
        fs=sy.factorint(d)
        if len(fs)!=1: continue
        p=next(iter(fs)); cyc=phi(d)
        for _ in range(16):
            C=Z(sum(rng.randint(-8,8)*x**j for j in range(7)))
            numerator=one+(xx-one)*C
            # Compute the field norm independently as a multiplication determinant.
            R=numerator.rem(cyc); e=cyc.degree()
            M=sy.Matrix(e,e,lambda i,j: ((xx**j)*R).rem(cyc).nth(i))
            A=int(M.det(method='domain-ge'))
            assert A%p==1
            N=Fraction(A,int((-1)**e*cyc.eval(1)))
            assert vp(N.numerator,p)-vp(N.denominator,p)==-1
            tested+=1
    return tested

def orders_check():
    survived=[]
    for n in range(2,10001):
        factors=sy.factorint(n); vals={}
        possible=True
        for p,r in factors.items():
            for j in range(1,r+1):
                v=Fraction(-2,(p-1)*p**(j-1))
                if v.denominator!=1 or (p in vals and vals[p]!=v):
                    possible=False; break
                vals[p]=v
        if n%2==0 and any(int(v)%2 for v in vals.values()): possible=False
        if possible: survived.append(n)
    assert survived==[2,3]
    return survived

def triangles():
    # Inverse DFT, viewed in Q(omega)=Q[x]/(x²+x+1), with x a choice of primitive root.
    Q=lambda y: sy.Poly(y,x,domain=sy.QQ)
    cyc=Q(x*x+x+1)
    omega=Q(x)
    base=(omega-Q(1)).invert(cyc)
    count=0
    for a in range(-8,9):
        for b in range(-8,9):
            m=[3*a,1+3*b,2]
            B=(sum((m[k]*omega**k for k in range(3)),Q(0))/3)
            B=Q(B).rem(cyc)
            assert B==(base+Q(a)+b*omega).rem(cyc) and not B.is_zero
            # Eigenvalue phases at 2*pi/3 are omega^{-k} since m[k]=k mod 3.
            assert [int(i)%3 for i in m]==[0,1,2]
            count+=1
    return count

if __name__=='__main__':
    print('exact prescribed-support constructions n=2..60:', support_test())
    print('prime-power numerator determinant / norm checks:',norm_test())
    print('orders surviving necessary exact tests through 10000:', orders_check())
    print('direct triangle inverse-DFT checks:',triangles())
