"""Independent integer-only certificate for the polynomial inequalities.
Leo Gao / AI-assisted. Run with an unmodified Python 3 standard library.
Use tensor-product Bernstein coefficients (not the monomial substitution
used by the manuscript verifier). Multivariate interpolation is exact.
"""
from fractions import Fraction as F
from math import comb
from itertools import product
from functools import lru_cache

def nums(a,b,c):
    A=1-b+b*c; B=1-c+c*a; C=1-a+a*b
    U=A*(C+B-A); V=B*(A+C-B); W=C*(A+B-C)
    return [U,V,W]+[3*A*B*C-i-j-k for i,j,k in product(((1-b)*V,c*W),(a*U,(1-c)*W),((1-a)*U,b*V))]
# Every expression is of degree at most 3 in each variable:
# A,B,C multilinear; differences products of at most three multilinears.
D=3
idx=list(product(range(D+1),repeat=3))
G=[[F(comb(D,j))*F(i,D)**j*(1-F(i,D))**(D-j) for j in range(D+1)]+[F(i==j) for j in range(D+1)] for i in range(D+1)]
for j in range(D+1):
    k=next(k for k in range(j,D+1) if G[k][j]);G[j],G[k]=G[k],G[j]
    G[j]=[v/G[j][j] for v in G[j]]
    for i in range(D+1):
        if i!=j:G[i]=[x-G[i][j]*y for x,y in zip(G[i],G[j])]
inv=[r[D+1:] for r in G]
v={ijk:nums(*(F(i,D) for i in ijk)) for ijk in idx}
for axis in range(3):
    z={}
    for ijk in idx:
        ans=[F(0)]*11
        for s in range(D+1):
            q=ijk[:axis]+(s,)+ijk[axis+1:];coef=inv[ijk[axis]][s]
            ans=[x+coef*y for x,y in zip(ans,v[q])]
        z[ijk]=ans
    v=z
for j,name in enumerate(('U','V','W',*map(str,product(range(2),repeat=3)))):
    coeff=[v[ijk][j] for ijk in idx];assert min(coeff)>=0 and max(coeff)>0
    print(name, 'degree-3 Bernstein:', min(coeff), 'to', max(coeff), '; positive:', sum(c>0 for c in coeff), '/64')
print('PASS: all Bernstein basis functions are positive on the open unit cube.')
