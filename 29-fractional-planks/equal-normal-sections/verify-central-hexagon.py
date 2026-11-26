"""Independent exact stress test of the constructive central-hexagon proof.
Leo Gao / AI-assisted. No external dependencies.
"""
from itertools import product
from fractions import Fraction as F
from random import Random

q=F(1,2)
V=((F(1),F(0)),(q,F(1)),(-q,F(1)),(-F(1),F(0)),(-q,-F(1)),(q,-F(1)))
def det(a,b,c):
    return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
def hull(P):
    P=sorted(set(P));a=[];b=[]
    for L,PP in [(a,P),(b,P[::-1])]:
        for p in PP:
            while len(L)>1 and det(L[-2],L[-1],p)<=0:L.pop()
            L.append(p)
    return a[:-1]+b[:-1]
def check(s):
    P=hull([tuple((1-s[i])*x+s[i]*y for x,y in zip(V[i],V[(i+1)%6])) for i in range(6)])
    def g(a,b):return a*b/(a+b) if a+b else 0
    h=[g(1-s[i-1],s[i]) for i in range(6)];B=[i for i,n in enumerate(h) if n>F(1,3)]
    parity={i%2 for i in B}
    if len(parity)<=1:
        J=range(1-next(iter(parity),1),6,2);shift=(0,0); difficult=False
    else:
        assert len(B)==2 and (B[0]-B[1])%6==3; difficult=True
        k=min(B,key=h.__getitem__)
        J=[(k+2*j)%6 for j in range(3)];shift=tuple((h[k]-F(1,3))*x for x in V[k])
    X=[tuple(F(2,3)*x-t for x,t in zip(V[j],shift)) for j in J]
    assert len(P)>=3 and len(X)==3
    assert all(det(u,v,x)>=0 for u,v in zip(P,P[1:]+P[:1]) for x in X),(s,P,X)
    return difficult
if __name__=='__main__':
    D=4;grid=[F(i,D) for i in range(D+1)]
    n=sum(check(s) for s in product(grid,repeat=6))
    print(f"PASS {len(grid)**6} exact grid hulls, including {n} opposite-bad configurations")
    rng=Random(0);D=10**7
    n=sum(check(tuple(F(rng.randrange(D+1),D) for _ in range(6))) for _ in range(2000))
    print(f"PASS 2000 exact seeded rational hulls, including {n} opposite-bad configurations")
