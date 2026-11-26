"""Exact short certificate, no graph library or sufficiency theorem is needed."""
from itertools import combinations_with_replacement
from fractions import Fraction as F
for n in range(2,9):
    candidates=[]
    for v in combinations_with_replacement(range(n),n):
        d=tuple(reversed(v));s=sum(d)
        if s%2:continue
        if any(sum(d[:k])>k*(k-1)+sum(min(k,x) for x in d[k:]) for k in range(1,n+1)):continue
        mean=F(s,n);variance=F(sum(x*x for x in d),n)-mean**2
        candidates.append((n-1-mean/2-variance,d))
    low,degs=min(candidates)
    assert low>0
    print(n,len(candidates),low,degs)
