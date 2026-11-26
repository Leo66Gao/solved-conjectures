"""Exact reproducibility checks. No libraries outside the standard library.

The limit theorem is analytical. These checks independently test the occupancy
model, the recurrence indexing, covariance signs, and the dense deficit bounds.
"""
from itertools import combinations, combinations_with_replacement
from collections import Counter
from fractions import Fraction as F
from functools import cache
from math import prod


def add(a,b):
    return tuple((a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0)
                 for i in range(max(len(a),len(b))))


def qmul(a,l):
    if not a or not l: return ()
    out=[]
    acc=0
    for i in range(len(a)+l-1):
        if i<len(a): acc+=a[i]
        if i>=l: acc-=a[i-l]
        out.append(acc)
    return tuple(out)


@cache
def recurrence(f,n,k):
    if not 0<=k<=n: return ()
    if n==0: return (1,)
    l=({'cA':n-1, 'cB':2*n-1, 'SA':k, 'SB':2*k+1})[f]
    return add(recurrence(f,n-1,k-1),qmul(recurrence(f,n-1,k),l))


def occ(f,n,k):
    d=n-k; first=f[0]=='c'
    widths=tuple({'cA':range(1,n), 'cB':range(1,2*n,2),
                  'SA':range(1,k+1), 'SB':range(1,2*k+2,2)}[f])
    choices=combinations if first else combinations_with_replacement
    return widths,d,choices(range(len(widths)),d)


def main():
    pol=neg=deficits=0
    for n in range(1,10):
        for k in range(n+1):
            for f in ('cA','cB','SA','SB'):
                w,d,C=occ(f,n,k)
                p=(); stats=Counter(); z=D=D2=0
                for c in C:
                    term=(1,); wt=prod(w[i] for i in c)
                    for i in c: term=qmul(term,w[i])
                    p=add(p,term); z+=wt
                    a=Counter(c)
                    for i,x in a.items():
                        stats[i]+=x*wt
                        for j,y in a.items():
                            if i<j: stats[i,j]+=x*y*wt
                    if w:
                        delta=sum(w[-1]-w[i] for i in c)
                        D+=wt*delta; D2+=wt*delta**2
                assert p==recurrence(f,n,k),(f,n,k,p,recurrence(f,n,k))
                pol+=1
                if z:
                    for i,j in combinations(range(len(w)),2):
                        assert z*stats[i,j]<=stats[i]*stats[j],(f,n,k,i,j)
                        neg+=1
                    if w and f[0]=='S':
                        assert D<=z*len(w)*w[-1]
                        assert z*D2-D*D<=z*z*2*len(w)*w[-1]**2
                        deficits+=1
    print(f'{pol} full coefficient-vector comparisons, {neg} covariance signs,')
    print(f'and both weighted-deficit inequalities in {deficits} homogeneous entries passed.')
    for f,n,k in [('cA',18,15),('cB',18,15),('SA',18,15),('SB',18,15)]:
        p=recurrence(f,n,k); z=sum(p)
        mean=F(sum(i*v for i,v in enumerate(p)),z)
        var=F(sum(i*i*v for i,v in enumerate(p)),z)-mean**2
        print(f'{f} n={n} k={k}: mass={z} mean={mean} variance={var}')


if __name__=='__main__': main()
