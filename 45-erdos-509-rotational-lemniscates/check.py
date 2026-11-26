"""Independent finite consistency checks; the continuum theorem is proved in proof.md.
Only Python 3 standard libraries are required. No external files or network.
"""
from fractions import Fraction as Q
from itertools import combinations_with_replacement
from math import pi, sin, cos
from cmath import rect
from random import Random


def cover_cost(t, rows, k):
    center = max([t] + [b for a, b in rows if a <= t])
    outer = sum(b-a for a, b in rows if a > t)
    return center + Q(k, 2) * outer


def exact_cutoffs():
    # Every multiset of 1..4 nondegenerate radial intervals with integral
    # endpoints 0..4. The radial certificate is exact rational for each one.
    pool = [(a,b) for a in range(4) for b in range(a+1,5)]
    count = 0
    for m in range(1,5):
        for rows in combinations_with_replacement(pool,m):
            ts = sorted(set([0] + [a for a,_ in rows]))
            for k in range(2,11):
                best = min(cover_cost(t, rows, k) for t in ts)
                s = sum(Q(b**k-a**k, 2) for a,b in rows)
                assert best**k <= k*s, (rows,k,best,s)
                count += 1
    return count


def check_root_branches():
    # Dense boundary checks, not a proof. Scale midpoint to one.
    count = 0
    worst = 0.
    for k in range(2,17):
        for r in [.0001,.01,.2,.5,.8,.99,.99999]:
            a=(1-r)**(1/k)
            b=(1+r)**(1/k)
            for j in range(721):
                w=1+rect(r,2*pi*j/720)
                u=w**(1/k)
                ratio=abs(u-(a+b)/2)/((b-a)/2)
                worst=max(worst,ratio)
                assert ratio<1+1e-9, (k,r,j,ratio)
                count+=1
    return count,worst


def check_ray_intercepts():
    # Deterministic samples of the exact intersection-length formula.
    count=0
    rnd=Random(509)
    for k in range(2,17):
        for _ in range(500):
            c=rect(rnd.random()*3, rnd.random()*2*pi)
            total=0.
            for j in range(k):
                t=(c*rect(1,-2*pi*j/k)).real
                disc=1-abs(c)**2+t*t
                if disc < 0: continue
                lo,hi=t-disc**.5,t+disc**.5
                total+=max(0.,hi-max(0.,lo))
            assert total<=k+1e-9, (c,k,total)
            count+=1
    return count


def comb_certificate(k,L):
    # M=L^2, retaining cells from L through M-1, all endpoints exact.
    # Integer power sums keep the finite certificate inexpensive.
    M=L*L
    num=sum((k*j+2)**k-(k*j)**k for j in range(L,M))
    base=Q(num,2*(k*M)**k)
    mass=Q(M-L,M)
    # sin(pi/k)>=2/k by concavity of sine on [0,pi/2].
    lower=mass/(1+Q(k*k,2*L))
    assert 0 < lower <= 1
    assert lower**k <= k*base
    return lower,base,lower**k/base


if __name__=='__main__':
    print('Exact radial-cutoff multisets/exponents:',exact_cutoffs())
    print('Sampled one-disk boundary points, worst radius ratio:',check_root_branches())
    print('Sampled regular-star disk intersections:',check_ray_intercepts())
    print('Finite comb certificate (lower bounds for h(star)^k/h(base); limit k):')
    for k in [2,3,4,6]:
        for L in [25,100,400]:
            low,h,ratio=comb_certificate(k,L)
            print(f'  k={k}, M={L**2:6d}: h(base)={float(h):.7f}, '
                  f'h(star)>={float(low):.7f}, ratio>={float(ratio):.7f}')
    print('Unconditional order-three cost upper bound:', (3*2.59)**(1/3))
