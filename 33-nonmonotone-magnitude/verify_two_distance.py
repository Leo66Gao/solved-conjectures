"""Exact proof for {1,2}-distance metric graphs on <=8 points; see TWO_DISTANCE.md.
Usage: c++ -O2 -std=c++17 enumerate_graphs.cpp -o enum && ./enum | python verify_two_distance.py
Python standard library only; no eigenvalue tolerances, determinant approximations, or sampling."""
from collections import Counter
import sys
from fractions import Fraction

def add(a,b,sgn=1):return [(a[i] if i<len(a) else 0)+sgn*(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))]
def mult(a,b):
    r=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):r[i+j]+=x*y
    return r
def der(a):return [v*i for i,v in enumerate(a) if i]
def matrix_poly(n,w):
    neigh=[[] for _ in range(n)]
    for j in range(n):
        for i in range(j):
            if w&(1<<(j*(j-1)//2+i)):neigh[i].append(j);neigh[j].append(i)
    A=[[int(i==j) for j in range(n)] for i in range(n)];tr=[0];ss=[n]
    for k in range(1,n+1):
        B=[list(map(lambda x:2*x,row)) for row in A]
        for i in range(n):
            for j in neigh[i]:
                for u in range(n):B[i][u]+=A[j][u]
        A=B;tr.append(sum(A[i][i] for i in range(n)));ss.append(sum(map(sum,A)))
    P=[1]
    for k in range(1,n+1):
        raw=sum((-1)**(i-1)*P[k-i]*tr[i] for i in range(1,k+1));assert raw%k==0;P.append(raw//k)
    H=[sum((-1)**i*ss[i]*P[k-i] for i in range(k+1)) for k in range(n)]
    return P[::-1],H[::-1]
def trim(p):
    while len(p)>1 and not p[-1]:p.pop()
    return p
def sign_changes(q):
    s=[v>0 for v in q if v];return sum(x!=y for x,y in zip(s,s[1:]))
def posroots(p):
    p=[Fraction(v) for v in trim(p[:])]
    while p[0]==0:p=p[1:]
    seq=[p,der(p)]
    if not seq[-1]:return 0
    while len(seq[-1])>1:
        x,y=seq[-2][:],seq[-1]
        while len(x)>=len(y):
            a=x[-1]/y[-1];i=len(x)-len(y)
            for j,v in enumerate(y):x[i+j]-=a*v
            trim(x)
            if x==[0]:break
        if x==[0]:break
        seq.append([-v for v in x])
    return sign_changes([p[0] for p in seq])-sign_changes([p[-1] for p in seq])
counts=Counter()
for ln in sys.stdin:
    n,w=map(int,ln.split());counts[n,'all']+=1
    P,H=matrix_poly(n,w)
    if min(H)<0:continue  # H/n is the characteristic polynomial det(zI+C|1perp); all roots are real.
    counts[n,'negative type']+=1
    if n==1:continue
    top=mult([1,2,1],H);bot=add([0]+P,H)
    J=trim(add(mult(der(top),bot),mult(top,der(bot)),-1))
    assert max(J)>0,(n,w)
    if min(J)>=0:counts[n,'coefficient certificate']+=1;continue
    # Exact fallback if needed; not numerical sampling.
    if posroots(J)!=0 or next(v for v in J if v)<0:raise AssertionError(('not certified',n,w,J))
    counts[n,'Sturm']+=1
for n in range(1,9):
    assert counts[n,'all']==[0,1,2,4,11,34,156,1044,12346][n]
    print(n,*(counts[n,k] for k in ('all','negative type','coefficient certificate','Sturm')))
