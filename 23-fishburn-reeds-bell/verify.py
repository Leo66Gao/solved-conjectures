"""Exact crosschecks of the signed-root/tournament reduction.
Private research, Leo Gao; mathematically and computationally AI-assisted.
No third-party libraries. Give --full to enumerate 2^21 tournaments in D7.
"""
import itertools as it, sys
from fractions import Fraction as F
from math import comb
def Urow(k,i,j,s):
    return tuple((z==i)+s*(z==j) for z in range(k))
def root_direct(k,lam):
    edges=list(it.combinations(range(k),2))
    U=[Urow(k,i,j,s) for i,j in edges for s in (1,-1)]
    M=[[3*sum(z*w for z,w in zip(u,v)) for v in U] for u in U]
    h=len(M); p,q=lam.numerator, lam.denominator
    # Work with 2q(P-lambda I)
    M=[[q*(m//3)-2*p*(i==j) for j,m in enumerate(row)] for i,row in enumerate(M)]
    ans=max(sum(abs(sum(m*s for m,s in zip(row,x))) for row in M)
            for x_ in it.product((-1,1),repeat=h-1) for x in [(1,)+x_])
    return F(ans,2*q)
def predicted(k,lam):
    return 2*(sum(x*x for x in range(k))-lam*comb(k,2)+(k//3)*max(0,3*lam-2))
def tour(k,lams):
    e=list(it.combinations(range(k),2)); n=len(e); qs=[(l.numerator,l.denominator) for l in lams]; mx=[0]*len(qs)
    for W in it.product(*e):
        d=[0]*k
        for w in W: d[w]+=1
        v=nw=0
        for (i,j),w in zip(e,W):
            v+=max(d[i],d[j]); nw+=d[w]>d[i+j-w]
        for t,(p,q) in enumerate(qs): mx[t]=max(mx[t],q*v-p*nw)
    return [F(2*a,q) for a,(_,q) in zip(mx,qs)]
if __name__=='__main__':
    lams=list(map(F,['0','1/3','2/3','7/9','1']))
    for k in (3,4):
        v=[root_direct(k,l) for l in lams]
        assert v==[predicted(k,l) for l in lams]
        print('direct sign-vector matrix enumeration D'+str(k)+':',*[str(a) for a in v])
    for k in range(3,8 if '--full' in sys.argv else 7):
        v=tour(k,lams)
        assert v==[predicted(k,l) for l in lams]
        print('exhaustive tournaments D'+str(k)+':',*[str(a) for a in v])
    for k in (7,8,9,10,11):
        qs=[F(k*(k-1))*(k-1-l)/predicted(k,l) for l in (F(2,3),F(1))]
        print(f'D{k} quantum/local at 2/3,1:',*map(str,qs))
    assert 6*predicted(9,F(2,3))==2160 and 6*predicted(10,F(2,3))==3060
