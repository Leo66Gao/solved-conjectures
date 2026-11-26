#!/usr/bin/env python3
"""Independent finite checks; no network access, Python 3 only."""
from collections import Counter, defaultdict, deque
from fractions import Fraction
from itertools import product, combinations
from math import factorial, comb

def components(n, edges):
    p=list(range(n))
    def root(a):
        while a!=p[a]:
            p[a]=p[p[a]]
            a=p[a]
        return a
    for a,b in edges: p[root(a)]=root(b)
    r=[root(x) for x in range(n)]
    return tuple(r.index(i) for i in r)

def parts(n):
    if not n:
        yield ()
        return
    for s in parts(n-1):
        for i in tuple(dict.fromkeys(s))+(n-1,): yield s+(i,)

def below(s,t):
    return all(s[i]!=s[j] or t[i]==t[j] for i in range(len(s)) for j in range(i))

def build(n,internal,ports,m):
    loc=[(n*j+a,n*j+b) for j in range(m) for a,b in internal]
    ext=[(n*j+a,n*((j+1)%m)+b) for j in range(m) for a,b in ports]
    assert len(set(sum(([a,b] for a,b in ext),[])))==2*len(ext)
    return loc,ext

def counts(n,edges):
    # Edge-addition partition DP, keyed by partition and number of failed edges
    states={(tuple(range(n)),0):1}
    for a,b in edges:
        new=defaultdict(int)
        for (s,k),v in states.items():
            new[s,k+1]+=v
            aa,bb=sorted((s[a],s[b]))
            new[tuple(aa if t==bb else t for t in s),k]+=v
        states=new
    return states

def checks(n,internal,ports,m):
    loc,ext=build(n,internal,ports,m)
    cc=counts(n,internal)
    pp=list(parts(n))
    # At negative rational q test integer weights after multiplication by 3^|E|
    # q=-1/3; live weight 4, failed weight -1.
    raw=Counter()
    for (s,k),v in cc.items(): raw[s]+=v*(-1)**k*4**(len(internal)-k)
    for t in pp:
        w=0
        for s in pp:
            if not below(s,t): continue
            mu=1
            for b in set(t):
                a=len({s[i] for i in range(n) if t[i]==b})
                mu*=(-1)**(a-1)*factorial(a-1)
            cut=sum(s[a]!=s[b] for a,b in internal)
            w+=mu*(-1)**cut*3**(len(internal)-cut)
        assert w==raw[t]
    # Check the complete coefficient vector (number of connected configurations by failures)
    # by grouping the within-block connected partitions, and then re-enumerating the cross edges.
    choices=defaultdict(list)
    for (s,k),v in cc.items(): choices[s].append((k,v))
    coeff=Counter()
    for ss in product(choices,repeat=m):
        contracted=[(a+j*n,rep+j*n) for j,s in enumerate(ss) for a,rep in enumerate(s) if a!=rep]
        ccx=Counter()
        for mask in range(1<<len(ext)):
            if not any(components(n*m,contracted+[e for i,e in enumerate(ext) if mask>>i&1])):
                ccx[len(ext)-mask.bit_count()]+=1
        if not ccx: continue
        p=ccx
        for s in ss:
            row=Counter()
            for x,a in p.items():
                for y,b in choices[s]: row[x+y]+=a*b
            p=row
        coeff.update(p)
    direct=counts(n*m,loc+ext)
    expected=Counter({k:v for (s,k),v in direct.items() if not any(s)})
    assert coeff==expected
    print('toy',len(loc)+len(ext),'edges,',len(pp),'partition inversions; full connected counts:',sorted(coeff.items()))

# Two toy cycles of blocks compare polynomial coefficients exactly. They are not asymptotic witnesses.
checks(5,[(0,3),(0,4),(1,2),(1,4)],[(0,2),(1,3)],3)
checks(4,[(0,3),(1,2),(1,3)],[(0,2)],3)

# Larger finite structural example: build the projective-plane incidence graph over F5,
# remove d/2 matching edges and reglue cyclically; independent max-flow check.
def normalized(v,p):
    k=next(j for j in v if j)
    return tuple(a*pow(k,-1,p)%p for a in v)
p=5
P=sorted({normalized(v,p) for v in product(range(p),repeat=3) if any(v)})
n0=len(P); n=2*n0; d=p+1
E=[(i,n0+j) for i,v in enumerate(P) for j,w in enumerate(P) if sum(a*b for a,b in zip(v,w))%p==0]
M=[]
for e in E:
    if set(e).isdisjoint(y for x in M for y in x): M.append(e)
    if len(M)==d//2: break
loc,ext=build(n,[e for e in E if e not in M],M,3)
G=[set() for _ in range(3*n)]
for a,b in loc+ext: G[a].add(b); G[b].add(a)
assert all(len(N)==d for N in G)
assert all((a%n<n0)!=(b%n<n0) for a,b in loc+ext)
assert all({b%n for b in G[a]}=={v for u,v in E if u==a%n}|{u for u,v in E if v==a%n} for a in range(len(G)))
assert all(len(G[a]&G[b])<=1 for a,b in combinations(range(len(G)),2))
def paths(s,t):
    # Node splitting + d augmentations; count internally vertex-disjoint paths.
    nn=len(G); f=defaultdict(dict)
    def add(a,b,c):
        f[a][b]=c; f[b].setdefault(a,0)
    for a,N in enumerate(G):
        add(2*a,2*a+1,1)
        for b in N: add(2*a+1,2*b,d)
    s=2*s+1;t=2*t
    for k in range(d):
        prev={s:None};q=deque([s])
        while q and t not in prev:
            a=q.popleft()
            for b,c in f[a].items():
                if c and b not in prev: prev[b]=a;q.append(b)
        if t not in prev: return k
        b=t
        while b!=s:
            a=prev[b];f[a][b]-=1;f[b][a]+=1;b=a
    return d
# All nonadjacent pairs, up to cyclic rotation of the three blocks.
pairs={(a,b) for a in range(n) for b in range(3*n) if a!=b and b not in G[a]}
assert all(paths(a,b)==d for a,b in pairs)
print('projective-plane C3 cover:',len(G),'vertices,',sum(map(len,G))//2,'edges, bipartite simple, no 4-cycles, degree',d,'; disjoint-path max flows',len(pairs),'→ κ=λ=6')
# Check algebra constants around finite thresholds.
for d0 in range(32,1025):
    f=lambda u: Fraction(u*(d0-1)**2,d0+u-1)-u
    assert min(f(2),f(4*d0))>d0-1
    for u in range(1,8): assert 32*u*(d0-u)>=24*d0+d0*u
    for u in range(8,50): assert 4*u>=24+u
print('elementary cut-bound inequalities verified for all integer d=32,...,1024 (proof is symbolic)')
