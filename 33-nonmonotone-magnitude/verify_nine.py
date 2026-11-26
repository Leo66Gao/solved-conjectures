"""An exact certificate for the nine-point strict-negative-type example. No dependencies."""
from fractions import Fraction as F
from itertools import product
from math import prod
points=list(product(range(2),repeat=3))[1:]+['-','+']
def D(v,w):
    if v==w:return 0
    if isinstance(v,str) and isinstance(w,str): return 4
    if isinstance(v,str): return 1+2*sum(w)
    if isinstance(w,str): return 1+2*sum(v)
    return 2*sum(a!=b for a,b in zip(v,w))
m=[[D(v,w) for w in points] for v in points]
assert all(m[i][k] <=m[i][j]+m[j][k] for i,j,k in product(range(9),repeat=3))
# Integer-vector squared Euclidean realization: duplicate each bit and append a zero;
# both apices use zero bits and last coordinate +1 or -1.
def coordinates(v):
    if isinstance(v,str):return (0,)*6+(1 if v=='+' else -1,)
    return v+v+(0,)
assert all(D(v,w)==sum((a-b)**2 for a,b in zip(coordinates(v),coordinates(w))) for v,w in product(points,repeat=2))
def solve(a,b):
    mat=[[F(c) for c in row]+[F(t)] for row,t in zip(a,b)];n=len(b)
    for j in range(n):
        i=next(i for i in range(j,n) if mat[i][j]);mat[j],mat[i]=mat[i],mat[j]
        p=mat[j][j];mat[j]=[v/p for v in mat[j]]
        for i in range(n):
            if i!=j:
                c=mat[i][j];mat[i]=[v-c*w for v,w in zip(mat[i],mat[j])]
    return [row[-1] for row in mat]
def M(q,beta):
    K=[[q**d*beta if d else F(1) for d in row] for row in m]
    w=solve(K,[1]*9)
    assert all(sum(k*z for k,z in zip(row,w))==1 for row in K)
    return sum(w)
q=F(99,100);beta=1-F(1,10**10)
small=M(q,beta);large=M(q*q,beta*beta)
assert F(141,100)<small<F(142,100)
assert F(138,100)<large<F(140,100)
print('Unperturbed integer squared-distance realization and all triangle inequalities passed.')
print('Strict off-diagonal perturbation: beta=1-10^-10 at t1=log(100/99); t2=2t1.')
print('Exact comparisons: 1.41 < M(t1) < 1.42 and 1.38 < M(t2) < 1.40.')
print('Displayed decimals only:',float(small),float(large))
# Independent rational certificate for full unperturbed magnitude formula: the equations
# below are also checked at more roots than the degree of their polynomial identity.
P=[-9,-18,-27,-24,-31,-26,7,32,32,28,12]
C=[-1,0,-2,0,-4,0,0,0,4,0,2]
def poly(p,x):return sum(c*x**i for i,c in enumerate(p))
def H(x):return poly(P,x)/((1+x)**2*(1+x*x)**2*poly(C,x))
# det(B) degree <= 4*7=28 and the (orbit sum of) cofactors degree <= 21.
# Cross-multiplied expression degree <= max(28+10, 21+16)=38.
for k in range(1,40):
    x=F(k,40)
    assert H(x)==M(x,F(1))
assert H(F(1))==F(3,2)
def der(p,x):return sum(i*c*x**(i-1) for i,c in enumerate(p) if i)
def DD(x):return (1+x)**2*(1+x*x)**2*poly(C,x)
p1=poly(P,F(1));d1=DD(F(1));slope=der(P,F(1))/d1-(p1/d1)*(F(2,2)+F(4,2)+der(C,F(1))/poly(C,F(1)))
assert slope==F(25,2)
print('39 rational samples certify the bounded-degree identity; M(0+)=3/2, M prime(0+)=-25/2.')
