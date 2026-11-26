from collections import defaultdict
from math import prod
from itertools import accumulate, product

A = (12,12,12,12,9,9,9,3,3,1,1,1)
B = (12,12,12,12,9,9,7,5,3,2,1)
groupsA = (((1,2,8,10),(3,4,9,11),(5,6,7,12)),
           ((1,5),(2,6),(3,7),(4,8,9,10,11,12)),
           ((1,),(2,),(3,),(4,),(5,8),(6,9),(7,10,11,12)))
groupsB = (((1,2,9,11),(3,5,7),(4,6,8,10)),
           ((1,5),(2,6),(3,7,10),(4,8,9,11)),
           ((1,),(2,),(3,),(4,),(5,9),(6,10,11),(7,8)))

def to_atoms(weights, groups, t=0):
    coords=[]
    for g in groups:
        d = {j:i for i, gg in enumerate(g) for j in gg}
        assert sorted(j for gg in g for j in gg) == list(range(1,len(weights)+1))
        coords.append(d)
    atoms=[(tuple(d[j] for d in coords),w) for j,w in enumerate(weights,1)]
    for z,(k,a,b) in enumerate(product(range(t),range(3),range(4)),7):
        atoms.append(((a,b,z),12))
    return atoms

def check_atoms(atoms, t):
    n=12*t+7
    assert len({c for c,w in atoms})==len(atoms)
    for ix,nout in enumerate((3,4,n)):
        sums=defaultdict(int)
        for c,w in atoms:
            sums[c[ix]]+=w
        assert dict(sums)==dict.fromkeys(range(nout),12*n//nout)

def profile(atoms):
    return tuple(sorted((w for c,w in atoms),reverse=True))

def greedy(n):
    tot=12*n
    caps=[[tot//d]*d for d in (3,4,n)]
    out=[]
    while any(caps[0]):
        indices=[max(range(len(c)),key=c.__getitem__) for c in caps]
        x=min(c[i] for c,i in zip(caps,indices))
        out.append(x)
        for c,i in zip(caps,indices):
            c[i]-=x
    assert all(not any(c) for c in caps)
    return tuple(out)

for t in range(40):
    n=12*t+7
    aa,bb=to_atoms(A,groupsA,t),to_atoms(B,groupsB,t)
    check_atoms(aa,t);check_atoms(bb,t)
    pa,pb=profile(aa),profile(bb)
    assert greedy(n)==pb
    assert pa[:n] == (12,)*(n-3)+(9,)*3
    assert sum(pb[:n+3])==12*(n-3)+35
    if not t: assert prod(x**x for x in pa)>prod(x**x for x in pb)
assert 3**21==10460353203>4*7**7*5**5==10294287500
print('All explicit witness, greedy, and exact-entropy checks pass.')
