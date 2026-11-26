"""Exact checks of the variational optimum; not a substitute for the proof.
Written with AI assistance; research credit: Leo Gao."""
from fractions import Fraction as F
from itertools import combinations_with_replacement
def need(test):
    if not test: raise ValueError('check failed')
def J(z,alpha):
    return sum(p*q*max(abs(x-y),alpha) for x,p in z for y,q in z)-sum(p*x*x for x,p in z)
def mass(r,a):
    return a/r-F(1,3*r*r)
def equal_law(r):
    return [(F(2*j-r-1,r),F(1,r)) for j in range(1,r+1)]
def parts(n,hi):
    if not n:
        yield []; return
    for x in range(1,min(n,hi)+1):
        for y in parts(n-x,x): yield [x]+y
for a in (F(1,20),F(1,9),F(11,90),F(1,3),F(1,2),F(1)):
    top=max(mass(r,a) for r in range(1,50))
    r=max(range(1,50),key=lambda r:mass(r,a))
    need(J(equal_law(r),a)==F(1,3)+top)
    for part in parts(18,18):
        p=[F(v,18) for v in part]
        need(sum(a*v*v-v**3/3 for v in p)<=top)
    for locs in combinations_with_replacement([-1,F(-2,5),0,F(1,8),F(3,4),1],5):
        need(J([(x,F(1,5)) for x in locs],a)<=F(1,3)+top)
    print('alpha =',a,'maximizing r =',r,'D =',F(2,3)-a+2*top)
a=F(11,90)
need(mass(5,a)==mass(6,a))
need((1-a)/(F(2,3)-a+2*mass(5,a))==F(79,51))
print('r=5/6 intersection, limiting ratio:',F(79,51))
