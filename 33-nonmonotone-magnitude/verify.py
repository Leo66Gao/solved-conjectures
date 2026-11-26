"""Rational interval certificate for the Pendyala seed at a fixed strict perturbation.
Only Python's standard library. Assertions use exact rationals; decimal text is for reading."""
from fractions import Fraction as F
from dataclasses import dataclass
from itertools import product

@dataclass(frozen=True)
class I:
    lo:F
    hi:F
    def __add__(x,y):
        y=iv(y);return I(x.lo+y.lo,x.hi+y.hi)
    __radd__=__add__
    def __neg__(x): return I(-x.hi,-x.lo)
    def __sub__(x,y): return x+-iv(y)
    def __rsub__(x,y): return iv(y)+-x
    def __mul__(x,y):
        y=iv(y); a=[u*v for u,v in product([x.lo,x.hi],[y.lo,y.hi])];return I(min(a),max(a))
    __rmul__=__mul__
    def __truediv__(x,y):
        y=iv(y);assert y.lo>0;return x*I(1/y.hi,1/y.lo)
def iv(a):return a if isinstance(a,I) else I(F(a),F(a))
def expminus(x):
    assert 0<=x<=1
    term=s=F(1)
    for j in range(1,24): # S23 <= exp(-x) <= S24
        term*=-x/j;s+=term
    return I(s,s-term*x/24)
e=F(1,10**8); a,b,c,d=F(7,8),F(9,8),F(26,21)+e,F(4,7)+e
P=[[int((j-i)%7 in (0,1,3)) for j in range(7)] for i in range(7)]
assert all(sum(P[i][k]*P[j][k] for k in range(7))==1+2*(i==j) for i in range(7) for j in range(7))
def dist(i,j):
    if i==j:return F(0)
    if i>j:return dist(j,i)
    if j<7:return a
    if i>=7:return b
    return c if P[i][j-7] else d
assert all(dist(i,j)+dist(j,k)>=dist(i,k) for i,j,k in product(range(14),repeat=3))
assert a*b-2*(c-d)**2==F(55,576)
def get(t):
    E,G,H,K=[expminus(t*u) for u in (a,b,c,d)]
    A,B,C=1+6*E,1+6*G,3*H+4*K
    Ap,Bp,Cp=-6*a*E,-6*b*G,-3*c*H-4*d*K
    N=7*(A+B-2*C); D=A*B-C*C
    Np=7*(Ap+Bp-2*Cp);Dp=Ap*B+A*Bp-2*C*Cp
    return N/D,(Np*D-N*Dp)/(D*D)
for t,lower,upper in [(F(1,100),F(17364,10000),F(17366,10000)),(F(1,50),F(17338,10000),F(17340,10000))]:
    val,der=get(t)
    assert lower<val.lo<=val.hi<upper
    assert F(-3,10)<der.lo<=der.hi<F(-1,5)
    print('t =',t,': magnitude',float(val.lo),'derivative',float(der.lo),'(both rigorously enclosed)')
f0=get(F(1,100))[0];f1=get(F(1,50))[0]
assert f0.lo**1000 > 4*f1.hi**1000
print('All triangle, CND spectral-gap, interval derivative, and 1000-fold 4x-drop checks passed.')
