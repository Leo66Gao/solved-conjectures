"""Exhaustive check of the explicit finite packet on all prefixes in [0,8]."""
from itertools import combinations
from math import isqrt

def diff(L):
    return [b-a for a,b in combinations(sorted(L), 2)]

def extend(A, n):
    prior=set(diff(A))
    p=next(p for p in range(2*n+1,4*n+1) if all(p%j for j in range(2,isqrt(p)+1)))
    B=[]
    for d in range(1,n+1):
        if d in prior: continue
        x=(p-d)//2 if d%2 else -d//2
        b=4*p*(d*d%p)+x
        B.extend((b,b+d))
    if not B: return A
    T=max(A)+max(max(A)-min(A), max(B)-min(B))+1-min(B)
    return A+[b+T for b in B]

if __name__=='__main__':
    trials=0
    for k in range(1,10):
        for U in combinations(range(1,10),k):
            before=diff(U)
            if len(before)!=len(set(before)):continue
            for n in (8, 9, 16, 31, 64):
                A=extend(list(U),n)
                D=diff(A)
                assert len(set(D))==len(D)
                assert set(range(1,n+1))<=set(D)
                trials+=1
    print(f'Passed {trials} exact integer extension checks.')
