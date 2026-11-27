"""Optional integer-only sanity check; not used as proof. Python 3 standard library."""
from itertools import product
from random import Random
rng=Random(230278)
def t(a):return a*(a-1)//2%2
def dot(x,y):return sum(a*b for a,b in zip(x,y))
def rank2(rows):
    piv={}
    for x in rows:
        while x:
            j=x.bit_length()-1
            if j not in piv:
                piv[j]=x;break
            x^=piv[j]
    return len(piv)
for x in range(-40,41):
 for y in range(-40,41):
    assert t(x+y)==(t(x)+t(y)+x*y)%2
    assert t(x*y)==(y*t(x)+x*t(y))%2
    assert t(-x)==(t(x)+x)%2

# Fixed y: compute coefficients in the listed column-function basis without
# any evaluation of Q(x-y) or t((x,y)). Then compare to that direct value.
def check(d,r,n):
    B=[[0 for j in range(d)] for i in range(d)]
    for i in range(d):
        for j in range(i,d):
            B[i][j]=B[j][i]=2*rng.randint(-2,2)+int(i!=j and i<r and j<r and i//2==j//2)
    for i in range(d):B[i][i]+=2*sum(abs(B[i][j]) for j in range(d))
    if r<d: B[-1][-1]+=(2-B[-1][-1])%4
    def feat(x):
        bx=[dot(row,x) for row in B]
        q=dot(x,bx)//2;p=[a%2 for a in x]
        features=[1,t(q)]+p+[(t(x[i])+q*x[i])%2 for i in range(r)]
        features.extend(p[i]*p[j] for i in range(r) for j in range(i+1,r))
        return sum(v<<i for i,v in enumerate(features)),q,bx
    def coeff(y,sy,by):
        a=[v%2 for v in by];assert not any(a[r:])
        e=[1^t(sy)]+[1];e.extend((t(by[i])+a[i]*(1+sy)+sy*(B[i][i]//2))%2 for i in range(d));e.extend(a[:r]);e.extend((a[i]*a[j]+sy*B[i][j])%2 for i in range(r) for j in range(i+1,r))
        return sum(v<<i for i,v in enumerate(e))
    pts=[tuple(rng.randrange(-6,7) for i in range(d)) for _ in range(n)]
    X=[feat(x) for x in pts];col=[coeff(y,q,by) for y,(_,q,by) in zip(pts,X)]
    rows=[]
    for x,(f,qx,_) in zip(pts,X):
        res=0
        for j,(g,(_,qy,by)) in enumerate(zip(col,X)):
            direct=1^t(qx+qy-dot(x,by))
            assert ((f&g).bit_count()&1)==direct, (d,r,j)
            res|=direct<<j
        rows.append(res)
    rank=rank2(rows);bound=2+d+r+r*(r-1)//2
    print(f"d={d:2}, r={r:2}: exact kernel rank {rank:3}, bound {bound:3}, tested pairs {n*n}")
    assert rank<=bound
check(3,2,40);check(5,2,40);check(6,6,48);check(23,22,310)
print("PASS: all signed-integer identities and all column factorizations agree.")
