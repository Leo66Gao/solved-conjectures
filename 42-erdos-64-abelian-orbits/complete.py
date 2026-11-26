"""Independent support-by-vertex-growth catalogue for larger orbit counts (stdlib)."""
from itertools import combinations,permutations,product
from functools import lru_cache
@lru_cache(None)
def aux(n):
    es=list(combinations(range(n),2)); perms=list(permutations(range(n)))
    op=[tuple(es.index(tuple(sorted((p[i],p[j])))) for i,j in es) for p in perms]
    return es,perms,op
@lru_cache(None)
def supports(n):
    if n==1:return {0}
    es,ps,qs=aux(n);old=aux(n-1)[0];seen={};reps=set()
    for k in supports(n-1):
        base=sum(1<<es.index(e) for i,e in enumerate(old) if k>>i&1)
        for inc in range(1,1<<(n-1)):
            z=base+sum(1<<es.index((i,n-1)) for i in range(n-1) if inc>>i&1)
            if z in seen:continue
            ims={sum(((z>>j)&1)<<i for i,j in enumerate(q)) for q in qs}
            r=min(ims);seen.update(dict.fromkeys(ims,r));reps.add(r)
    return reps
def catalogue(n):
    es,ps,qs=aux(n);out=set()
    for mask in supports(n):
        edges=[(i,j,k) for k,(i,j) in enumerate(es) if mask>>k&1]
        d0=[sum(i==a or i==b for a,b,k in edges) for i in range(n)]
        if any(min(d0[i],d0[j])>=4 for i,j,_ in edges):continue
        stab=[(p,q) for p,q in zip(ps,qs) if all((mask>>i&1)==(mask>>j&1) for i,j in enumerate(q))]
        for vals in product(range(1,4),repeat=len(edges)):
            d=[0]*n;off=[0]*len(es)
            for m,(i,j,k) in zip(vals,edges):d[i]+=m;d[j]+=m;off[k]=m
            if any(min(d[i],d[j])>=4 for i,j,_ in edges):continue
            # If d>=3 no internal orbit necessary. If d=2: one singleton or
            # one antipodal pair. If d=1: two singletons or one pair. If d=0:
            # (3,0),(1,1),(0,2).
            types={0:[(3,0),(1,1),(0,2)],1:[(2,0),(0,1)],2:[(1,0),(0,1)]}
            for local in product(*(types.get(k,[(0,0)]) for k in d)):
                D=[b+s+2*l for b,(s,l) in zip(d,local)]
                if any(min(D[i],D[j])>=4 for i,j,_ in edges):continue
                out.add(min(tuple(local[i] for i in p)+tuple(off[i] for i in q) for p,q in stab))
    return out
