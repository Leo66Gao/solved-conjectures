#!/usr/bin/env python3
"""Enumerate six-orbit templates using simple support graphs and their automorphisms."""
from itertools import permutations, combinations, product
from pathlib import Path
import json,sys,time

def enum(n):
    es=list(combinations(range(n),2));P=list(permutations(range(n)))
    perm=[tuple(es.index(tuple(sorted((p[i],p[j])))) for i,j in es) for p in P]
    out=[];seen=set()
    for mask in range(1<<len(es)):
        if mask in seen:continue
        supp=tuple((mask>>k)&1 for k in range(len(es)))
        seen.update(sum(supp[k]<<j for j,k in enumerate(q)) for q in perm)
        edges=[e for e,t in zip(es,supp) if t]
        reached={0}
        for _ in range(n):reached|={j for e in edges if reached.intersection(e) for j in e}
        if len(reached)<n:continue
        degree=[sum(i in e for e in edges) for i in range(n)]
        if any(degree[i]>3 and degree[j]>3 for i,j in edges):continue
        ids=[i for i,k in enumerate(supp) if k]
        autos=[(p,q) for p,q in zip(P,perm) if tuple(supp[a] for a in q)==supp]
        d=list(degree);M=list(supp)
        def dfs(k):
            if k==len(ids):
                ins=[[(u,v) for u in range(4) for v in range(3) if deg+u+2*v>=3 and (not u or deg+u+2*v==3) and (not v or deg+u+2*v<=4)] for deg in d]
                for C in product(*ins):
                    D=[deg+u+2*v for deg,(u,v) in zip(d,C)]
                    if any(D[i]>3 and D[j]>3 for i,j in edges):continue
                    T=tuple(C)+tuple(M)
                    if all(T<=tuple(C[i] for i in p)+tuple(M[i] for i in q) for p,q in autos):out.append(T)
                return
            ix=ids[k];a,b=es[ix]
            for t in range(3):
                if t:d[a]+=1;d[b]+=1;M[ix]+=1
                if not any(d[i]>3 and d[j]>3 for i,j in edges):dfs(k+1)
            d[a]-=2;d[b]-=2;M[ix]-=2
        dfs(0)
    return sorted(out)
if __name__=='__main__':
    n=int(sys.argv[1]);a=enum(n);print(n,len(a));(Path(__file__).parent/'proofs'/f'templates-{n}.json').write_text(json.dumps(a))
