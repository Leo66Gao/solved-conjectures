#!/usr/bin/env python3
"""Exact cubic multigraph generation by augmenting from connected parents.
Includes one degree-4 vertex kernels via edge contraction.
"""
from functools import lru_cache
from itertools import combinations_with_replacement
import sys

def canon(n, es):
    m=[[0]*n for _ in range(n)]
    for u,v in es:
        m[u][v]+=1
        if u!=v:m[v][u]+=1
    adj=[tuple(w for w in range(n) for _ in range(m[v][w])) for v in range(n)]
    d=[len(adj[v])+m[v][v] for v in range(n)]
    @lru_cache(None)
    def dfs(cols):
        while True:
            signatures=[(cols[v],tuple(sorted(cols[w] for w in adj[v]))) for v in range(n)]
            lab={x:i for i,x in enumerate(sorted(set(signatures)))}
            new=tuple(map(lab.__getitem__,signatures))
            if new==cols:break
            cols=new
        if len(set(cols))==n:
            order=sorted(range(n),key=cols.__getitem__)
            return bytes(m[u][v] for i,u in enumerate(order) for v in order[i:])
        counts=[cols.count(x) for x in set(cols)]
        spl=min((cols.count(x),x) for x in set(cols) if cols.count(x)>1)[1]
        return min(dfs(cols[:i]+(len(counts),)+cols[i+1:]) for i,x in enumerate(cols) if x==spl)
    labels={x:i for i,x in enumerate(sorted(set(zip(d,(m[v][v] for v in range(n))))))}
    c=dfs(tuple(labels[(d[v],m[v][v])] for v in range(n)))
    return tuple((u,v) for (u,v),k in zip(combinations_with_replacement(range(n),2),c) for _ in range(k))

def cubic(n):
    es2={((0,0),(0,1),(1,1)),((0,1),(0,1),(0,1))}
    for k in range(2,n,2):
        parents=es2
        es2=set(); seen=set()
        for es in parents:
            for i in range(len(es)):
                u,v=es[i]
                rem=es[:i]+es[i+1:]
                # Both new vertices on one old edge, then add their link.
                todo=[rem+((u,k),(k,k+1),(k,k+1),(k+1,v)),
                      rem+((u,k),(k,v),(k,k+1),(k+1,k+1))]
                for j in range(i+1,len(es)):
                    a,b=es[j]
                    todo.append(es[:i]+es[i+1:j]+es[j+1:]+((u,k),(k,v),(a,k+1),(k+1,b),(k,k+1)))
                for edges in todo:
                    tup=tuple(sorted(tuple(sorted(e)) for e in edges))
                    if tup not in seen:
                        seen.add(tup);es2.add(canon(k+2,tup))
        print('cubic order',k+2,'count',len(es2), file=sys.stderr, flush=True)
    return es2

def contract(n, es, i):
    u,v=es[i]
    def relabel(w):return (u if w==v else w-int(w>v))
    return tuple(sorted(tuple(sorted((relabel(a),relabel(b)))) for j,(a,b) in enumerate(es) if j!=i))

if __name__=='__main__':
    n = int(sys.argv[1]); cs=cubic(n)
    print(n//2+1)
    odd=set()
    for es in cs:
        for i,(u,v) in enumerate(es):
            if u!=v:odd.add(canon(n-1,contract(n,es,i)))
    print('one degree-four order',n-1,'count',len(odd),file=sys.stderr,flush=True)
    for k,ks in ((n-1,odd),(n,cs)):
        for es in sorted(ks):
            d=[0]*k
            for u,v in es:d[u]+=1;d[v]+=1
            print(k,len(es),*d,*(i for e in es for i in e))
