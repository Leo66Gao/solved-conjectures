"""Independent exact tensor Bernstein interpolation for the offset inequalities.
Leo Gao, AI-assisted. Runs with Python 3 standard library alone.
"""
from fractions import Fraction as F
from itertools import product
from math import comb

def evaluate(r,A,B):
    # Polynomial values, with no evaluation of a rational expression at r=0.
    Q=(3*A-1)*B-A; W=A+r*B
    J=r*(3*A*(1-B)+(1+2*r)*B)
    T=(1+2*r)*W+J*r*(1-B)
    X=(1+2*r)*Q+J*(2*B-1)
    Y=(r*B+A+A*r*(1-B))*X
    return (
      T*((1+r)*B-Q+A*(2*B-1))-Y,
      T*((1+r)*A-r*Q+r*A*(2*B-1))-r*Y
    )

def invbern(d):
    G=[[comb(d,j)*F(i,d)**j*(1-F(i,d))**(d-j) for j in range(d+1)]
       +[F(i==j) for j in range(d+1)] for i in range(d+1)]
    for j in range(d+1):
        k=next(k for k in range(j,d+1) if G[k][j]);G[j],G[k]=G[k],G[j]
        G[j]=[x/G[j][j] for x in G[j]]
        for i in range(d+1):
            if i!=j:G[i]=[x-G[i][j]*y for x,y in zip(G[i],G[j])]
    return [x[d+1:] for x in G]

dim=(4,2,3);idx=list(product(*(range(d+1) for d in dim)))
vals={p:evaluate(F(p[0],4),(1+F(p[1],2))/2,(1+F(p[2],3))/2) for p in idx}
for k,d in enumerate(dim):
    coeff=invbern(d);new={}
    for p in idx:
        s,t=F(0),F(0)
        for l,v in enumerate(coeff[p[k]]):
            x,y=vals[p[:k]+(l,)+p[k+1:]];s+=v*x;t+=v*y
        new[p]=(s,t)
    vals=new
for k in range(2):
    x=[a[k] for a in vals.values()]
    assert min(x)>=0 and max(x)>0
    print(f'polynomial {k+1}: {sum(a>0 for a in x)} of {len(x)} Bernstein coefficients positive; min {min(x)}, max {max(x)}.')
print('PASS on full closed box: tensor Bernstein basis polynomials are nonnegative.')
