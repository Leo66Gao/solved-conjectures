"""An independent exact convex-hull stress test for the offset construction.
Leo Gao / AI-assisted. Python 3 standard library only.
This finite test is not the proof of the continuum.
"""
from fractions import Fraction as F
from itertools import product
from random import Random

def cross(a,b,c):
    return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])

def hull(P):
    P=sorted(set(P));H=[]
    for order in [P,P[::-1]]:
        R=[]
        for x in order:
            while len(R)>1 and cross(R[-2],R[-1],x)<=0:R.pop()
            R.append(x)
        H+=R[:-1]
    return H

def check(delta, params):
    D=1-delta; p=[];q=[]
    for i in range(3):
        j,k=(i+1)%3,(i+2)%3
        x=[0,0,0];x[j]=1-D*params[i];x[k]=1+delta-x[j];p.append(x)
        x=[0,0,0];x[i]=1;x[j]=delta*params[i+3];x[k]=delta-x[j];q.append(x)
    a={(i,j):1-p[i][j] for i in range(3) for j in range(3) if i!=j}
    b={(i,j):q[j][i] for i,j in a}
    g={(i,j):a[i,j]*b[i,j]-(a[i,j]*delta+b[i,j]*D)/3 for i,j in a}
    bad=[(i,j) for i,j in a if g[i,j]>0]
    good_sign={ (j-i)%3 for i,j in bad }
    ell=[delta/3]*3; nonzero=False
    if len(good_sign)>1:
        assert len(bad)==2 and bad[0]==bad[1][::-1]
        i,j=min(bad,key=lambda k:g[k]/(a[k]+b[k]))
        k=3-i-j; assert k not in (i,j)
        direction=(j-i)%3
        u0=g[i,j]/a[i,j]
        c=delta-b[j,i]
        v=max(0,(c*(F(2,3)+u0/D)-delta/3+u0)/(1+(b[i,j]/a[i,j])*(1+c/D)))
        u=u0-b[i,j]*v/a[i,j]
        assert 0<=v<=g[i,j]/(a[i,j]+b[i,j])
        ell[i]+=u;ell[j]-=v;ell[k]+=v-u;nonzero=v>0
    else:
        direction=3-next(iter(good_sign),1)
    motifs=[]
    for i in range(3):
        j=(i+direction)%3;k=3-i-j
        x=ell[:];x[j]+=F(2,3);x[k]+=F(1,3);motifs.append(x)
    H=hull([tuple(x[:2]) for x in p+q]);assert len(H)>=3
    assert all(cross(x,y,z)>=0 for x,y in zip(H,H[1:]+H[:1]) for z in motifs),(delta,params,ell,H,motifs)
    return len(good_sign)>1,nonzero

if __name__=='__main__':
    grid=[F(i,3) for i in range(4)]
    for delta in map(F,('0','1/19','1/6','1/3','2/5','9/20','1/2')):
        x=[check(delta,s) for s in product(grid,repeat=6)]
        print(f'delta={delta}: PASS {len(x)} cases; opposite={sum(r for r,v in x)}; positive interpolation={sum(v for r,v in x)}',flush=True)
    rng=Random(10)
    x=[check(F(rng.randrange(5001),10**4),tuple(F(rng.randrange(1001),1000) for _ in range(6))) for i in range(4000)]
    print(f'PASS {len(x)} rational random cases; opposite={sum(r for r,v in x)}; positive interpolation={sum(v for r,v in x)}')
