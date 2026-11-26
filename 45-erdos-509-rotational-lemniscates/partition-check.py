"""Numerical cross-check of the exact one-disk formula against direct set-partition
optimisation for the k radial segments. The lower bound is analytic in proof.md.
"""
from math import pi
from cmath import rect
from itertools import combinations
from functools import lru_cache


def enclosing(points):
    points=set(points)
    cands=list(points)
    cands += [(p+q)/2 for p,q in combinations(points,2)]
    for p,q,r in combinations(points,3):
        a,b=q-p,r-p
        de=2*(a.real*b.imag-a.imag*b.real)
        if abs(de)<1e-10:
            continue
        z=complex((abs(a)**2*b.imag-abs(b)**2*a.imag)/de,
                  (a.real*abs(b)**2-b.real*abs(a)**2)/de)
        cands.append(p+z)
    return min(max(abs(c-x) for x in points) for c in cands)


def optimize(k,a):
    tips=[rect(1,2*pi*j/k) for j in range(k)]
    groups=[0.]+[enclosing([r*z for j,z in enumerate(tips)
                      if (mask>>j)&1 for r in (a,1)]) for mask in range(1,2**k)]
    @lru_cache(None)
    def rec(mask):
        if not mask: return 0.
        sub=mask
        best=groups[mask]
        while sub:
            if sub & -mask == mask & -mask:  # least set bit of mask belongs to this block
                best=min(best,groups[sub]+rec(mask^sub))
            sub=(sub-1)&mask
        return best
    return rec(2**k-1)


if __name__=='__main__':
    count=0
    maxerr=0.
    for k in range(2,9):
        for a in sorted(set([0.,.1,.25,.5,.8,.95,1-2/k])):
            val=optimize(k,a)
            predicted=min(1,k*(1-a)/2)
            err=abs(val-predicted)
            assert err<1e-8,(k,a,val,predicted)
            maxerr=max(maxerr,err)
            count+=1
    print(f'Independent finite partition/circumdisk checks: {count} (k=2..8); maximum error: {maxerr:.3g}')
