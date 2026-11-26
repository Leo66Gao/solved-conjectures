"""Independent Shannon-information interval (nats) at p=2/5. Python 3.10+.
Uses integer channel weights throughout; log enclosures use no floating point.
"""
from collections import Counter
from itertools import product
from fractions import Fraction as F
from functools import lru_cache
from math import ceil

n=14
N=1<<n
def encode(a,b,c,d):
    z=(a,b,c,d,2*a+b+c+d,3*a+2*b+c+3*d,3*a+3*b+2*c+d,3*a+b+3*c+2*d)
    return sum(((t%4)^((t%4)>>1))<<(2*i) for i,t in enumerate(z))
C=sorted({w>>2 for t in product(range(4),repeat=4)
                 if ((w:=encode(*t))&1)==0})
assert len(C)==128
cells={c:[] for c in C}
taken=set()
for e in sorted(range(N),key=lambda z:(z.bit_count(),z)):
    for c in C:
        x=c^e
        if x not in taken:
            cells[c].append(x); taken.add(x)
    if len(taken)==N: break
assert {len(xs) for xs in cells.values()}=={128}
h=Counter()
for xs in cells.values():
    mass=[0]*N
    for x in xs: mass[x]=1
    for i in range(n):
        bit=1<<i
        for j in range(0,N,2*bit):
            for a in range(j,j+bit):
                b=a+bit; x,y=mass[a],mass[b]
                mass[a],mass[b]=3*x+2*y,2*x+3*y
    assert sum(mass)==128*5**n
    h.update(mass)

# Enclose log(num/den)*S above and below by integers.
S=1<<60
def up(a,b):return -(-a//b)
def unitlog(a,b):
    assert b<=a<=2*b
    r,t=a-b,a+b         # z=r/t in [0,1/3]
    lo=hi=0; R=r; T=t
    for j in range(1,32,2):
        lo+=2*S*R//(j*T)
        hi+=up(2*S*R,j*T)
        R*=r*r; T*=t*t
    # Remaining odd terms start with z^33/33 and converge geometrically.
    hi+=up(2*S*R*t*t,33*T*(t*t-r*r))
    return lo,hi
L2,U2=unitlog(2,1)
@lru_cache(None)
def logiv(a,b):
    k=0
    while a<b:a*=2;k-=1
    while a>=2*b:b*=2;k+=1
    l,h=unitlog(a,b)
    return l+min(k*L2,k*U2),h+max(k*L2,k*U2)
M=128*5**n
# P(y|u)=w/M, Pr(U=u,Y=y)=w/(128*M), P(y)=1/N.
mi0=mi1=0
for w,t in h.items():
    l,u=logiv(N*w,M)
    mi0+=t*w*l;mi1+=t*w*u
lo=F(mi0,128*M*S);hi=F(mi1,128*M*S)
# coordinate benchmark in nats: 7*(log(2)+(2/5)log(2/5)+(3/5)log(3/5)).
la,ua=logiv(2,5); lb,ub=logiv(3,5)
cl=7*F(5*L2+2*la+3*lb,5*S); ch=7*F(5*U2+2*ua+3*ub,5*S)
gl,gh=lo-ch,hi-cl
assert F(16437,10**9)<gl<gh<F(16439,10**9)
print('Distinct exact conditional channel weights:',len(h))
print('At p=2/5: 0.000016437 < [I(U;Y)-7*C(p)] * ln(2) < 0.000016439.')
print('Interval endpoints in nats:', gl,gh)
