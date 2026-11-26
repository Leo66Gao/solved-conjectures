"""Exhaustive small-radius proof of sharpness, and explicit 32-cycle witness."""
from collections import defaultdict
M=152
T=[[0,0,0],[0,1,84],[0,141,121]]
def adj(v):
    i,x=v
    if i<3:return [(j+3,(x+T[i][j])%M) for j in range(3)]
    return [(j,(x-T[j][i-3])%M) for j in range(3)]
def first(L):
    # Each cycle includes a left vertex. Translations by Z/M normalize its coordinate to 0.
    # Every even simple cycle is two equal-length paths with disjoint interiors.
    for i in range(3):
        s=(i,0);ends=defaultdict(list);path=[s];seen={s}
        def f():
            if len(path)==L//2+1:
                v=path[-1];t=frozenset(path[1:-1])
                for q,u in ends[v]:
                    if t.isdisjoint(u):return path+q[-2:0:-1]
                ends[v].append((list(path),t));return
            for w in adj(path[-1]):
                if w not in seen:
                    path.append(w);seen.add(w);c=f()
                    if c:return c
                    seen.remove(w);path.pop()
        c=f()
        if c:return c
for L in (4,8,16,32):
    c=first(L)
    if c:
        assert len(set(c))==len(c)==L and all(w in adj(v) for v,w in zip(c,c[1:]+c[:1]))
    print('C'+str(L)+':',c)
    assert (c is not None)==(L==32)
