"""Exact finite-dimensional identities plus a high-precision check of the asymptotic profile.
No third-party libraries. The infinite compact statement is proved in PHASE_TRANSITION.md."""
from fractions import Fraction as F
from itertools import product
from decimal import Decimal as D, localcontext

def solve(a):
    d=[[F(x) for x in row]+[F(1)] for row in a]
    for j in range(len(a)):
        i=next(i for i in range(j,len(a)) if d[i][j]);d[i],d[j]=d[j],d[i]
        z=d[j][j];d[j]=[v/z for v in d[j]]
        for i in range(len(a)):
            if i!=j:
                z=d[i][j];d[i]=[v-z*w for v,w in zip(d[i],d[j])]
    return [r[-1] for r in d]
def schur(k,q,alpha):
    h=(1-q*q)**k;ell=(1-q)**k
    return (2/(1+q))**k-ell*ell/h+2*(1-alpha+alpha*ell)**2/((1-alpha*alpha)**2+2*alpha*alpha*h)
for k in (3,4,5):
    vertices=list(product([0,1],repeat=k))[1:];groups=[[v for v in vertices if sum(v)==j] for j in range(1,k+1)]+[['+','-']]
    for num,den in ((1,2),(1,4),(1,1)):
        for z in (F(2,3),F(9,10),F(99,100)):
            q=z**den;alpha=z**num
            def kernel(x,y):
                if x==y:return F(1)
                if isinstance(x,str) and isinstance(y,str):return alpha**4
                if isinstance(x,str):return alpha*q**sum(y)
                if isinstance(y,str):return alpha*q**sum(x)
                return q**sum(a!=b for a,b in zip(x,y))
            B=[[sum(kernel(g[0],y) for y in gg) for gg in groups] for g in groups]
            w=solve(B)
            assert sum(len(g)*v for g,v in zip(groups,w))==schur(k,q,alpha)
print('27 exact finite split-cube Schur identities verified (cube dimensions 3,4,5).')
with localcontext() as ctx:
    ctx.prec=220
    for k in (3,6,10):
        r=D(2)**-22;b=D(1);s=(D(2)**(k-1)*r**(k-2)/b).sqrt()
        for t in (D('0.8'),D(1),D('1.2')):
            val=schur(k,(-r*t).exp(),(-s*r*t).exp());target=1+1/(2*(1+b*t**(k-2)))
            assert abs(val-target)<D('0.00002')
print('High-precision profile spot checks passed (illustrations, not the infinite proof).')
