"""Verify the score of the strongest periodic candidate from tile12.cpp."""
from fractions import Fraction as F
from collections import Counter
with open("tile12-best.txt") as f:
    n,d=map(int,f.readline().split())
    col=list(map(int,f.readline().split()))
    cen=list(map(int,f.readline().split()))
    tab=[tuple(map(int,l.split())) for l in f]
assert len(tab)==1<<(n-d)
assert len(col)==n and len(cen)==1<<(6-d)
def H(x):
    t=0
    for i,c in enumerate(col):
        if (x>>i)&1:t^=c
    return t
assert len(set(H(x) for x in range(1<<n)))==len(tab)
cell={}
for x in range(1<<n):
    t=H(x)
    a,e=tab[t]
    assert H(e)==t^cen[a]
    cell.setdefault((a,x^e),[]).append(x)
assert len(cell)<=64
B=sum((F(sum(sum(1-2*(x>>i&1) for x in A)**2 for i in range(n)),len(A)) for A in cell.values()),F(0))/(1<<n)
print('cells',len(cell),'sizes',sorted(Counter(map(len,cell.values())).items()))
print('exact B',B,float(B),'difference from 6:',B-6)
assert B<6
