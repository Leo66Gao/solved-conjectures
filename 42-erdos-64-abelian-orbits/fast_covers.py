#!/usr/bin/env python3
"""Explore dyadic cycles in all semiregular abelian covers of a fixed orbit template."""
import itertools, functools, json, sys, os
from sympy import Matrix
from sympy.matrices.normalforms import hermite_normal_form
from collections import Counter
from pathlib import Path

def templates(n):
    # Tuple of per-vertex (number of self-inverse edge labels, pairs of inverse labels), then cross-edge multiplicities
    E=list(itertools.combinations(range(n),2))
    ans=set()
    for M in itertools.product(range(4),repeat=len(E)):
        cd=[sum(m for m,e in zip(M,E) if i in e) for i in range(n)]
        inn=[[ (a,b) for a in range(4) for b in range(3) if (c+a+2*b>=3 and (not a or c+a+2*b-1<3) and (not b or c+a+2*b-2<3))] for c in cd]
        for I in itertools.product(*inn):
            d=[c+a+2*b for c,(a,b) in zip(cd,I)]
            if any(m and min(d[i],d[j])>3 for m,(i,j) in zip(M,E)):continue
            # need only connected irredundant templates
            seen={0}
            for i in range(n):seen|={j for m,e in zip(M,E) if m and seen.intersection(e) for j in e}
            if len(seen)<n:continue
            T=tuple(I)+M
            mp=dict(zip(E,M))
            if any(tuple(I[i] for i in p)+tuple(mp[tuple(sorted((p[i],p[j])))] for i,j in E)<T for p in itertools.permutations(range(n))):continue
            ans.add(T)
    return sorted(ans)

def matrix_hnf(d,rows):
    if not rows:return ()
    C=hermite_normal_form(Matrix(rows).T).T
    return tuple(tuple(map(int,row)) for row in C.tolist())

class Template:
    def __init__(self,n,T):
        self.n=n;self.T=T
        edges=[];sem=[];V=list(range(n))
        def root(i):
            while V[i]!=i:i=V[i]
            return i
        dim=0
        for m,(i,j) in zip(T[n:],itertools.combinations(range(n),2)):
            for k in range(m):
                if root(i)!=root(j):V[root(i)]=root(j);g=0
                else:dim+=1;g=dim
                edges.append((i,j,g));edges.append((j,i,-g))
        for i,(a,b) in enumerate(T[:n]):
            for k in range(a):
                dim+=1;sem.append(dim);edges.append((i,i,dim))
            for k in range(b):
                dim+=1;edges.extend([(i,i,dim),(i,i,-dim)])
        self.dim=dim;self.zero=(0,)*dim;self.edges=edges
        self.vectors={g:tuple((1 if g>0 else -1) if abs(g)==j+1 else 0 for j in range(dim)) for i,k,g in edges}
        self.initial=matrix_hnf(dim,[tuple(2*x for x in self.vectors[g]) for g in sem])
        self.cache={};self.count=Counter();self.maxlen=0;self.certificate={}
    def process(self,H):
        if H in self.cache:return self.cache[H]
        piv=[(max(i for i,x in enumerate(row) if x!=0),row) for row in reversed(H)]
        def norm(x):
            x=list(x)
            for j,r in piv:
                q=x[j]//r[j]
                if q:x=[a-q*b for a,b in zip(x,r)]
            return tuple(x)
        def plus(x,y):return norm([a+b for a,b in zip(x,y)])
        def minus(x,y):return norm([a-b for a,b in zip(x,y)])
        port=[[] for i in range(self.n)]
        for i,j,g in self.edges:
            port[i].append((j,norm(self.vectors[g])))
        key=str(H)
        if any((i,self.zero) in port[i] or len(set(port[i]))!=len(port[i]) for i in range(self.n)):
            self.count['invalid']+=1;self.cache[H]=True;self.certificate[key]=None;return True
        @functools.lru_cache(None)
        def adj(v):
            i,x=v
            return [(j,plus(x,y)) for j,y in port[i]]
        def diffset(cyc):
            ds=set()
            for (i,x),(j,y) in itertools.combinations(cyc,2):
                if i==j:ds.add(min(minus(x,y),minus(y,x)))
            return ds
        best=None
        def score(ds):
            return len(ds)
        for L in (4,8,16,32):
            for i in range(self.n):
                start=(i,self.zero);path=[start];seen={start}
                # Two disjoint paths of length L/2 give a simple cycle.
                # Cap witnesses explored for choice only, never for proof validity.
                from collections import defaultdict
                halves=defaultdict(list);found=0
                def dfs():
                    nonlocal best,found
                    if found>=20:return
                    if len(path)==1+L//2:
                        inter=frozenset(path[1:-1]);u=path[-1]
                        for old,o in halves[u]:
                            if inter.isdisjoint(o):
                                c=path+old[-2:0:-1]
                                ds=diffset(c);found+=1
                                if best is None or score(ds)<best[0]:best=(score(ds),ds,list(c))
                                if found>=20:return
                        halves[u].append((list(path),inter))
                        return
                    for v in adj(path[-1]):
                        if v not in seen:
                            path.append(v);seen.add(v);dfs();seen.remove(v);path.pop()
                dfs()
                if best and best[0]<=2:break
            if best:break
        if best is None:
            self.count['uncovered']+=1;self.cache[H]=False;self.certificate[key]='open';return False
        _,ds,cyc=best
        self.maxlen=max(self.maxlen,len(cyc));self.count['node']+=1
        self.certificate[key]=cyc
        ok=True
        for v in sorted(ds):
            K=matrix_hnf(self.dim,[*H,v])
            assert K!=H
            if not self.process(K):ok=False
        self.cache[H]=ok;return ok


def smaller(n,T):
    es=list(itertools.combinations(range(n),2))
    for t in range(1,n):
        for vs in itertools.combinations(range(n),t):
            d={i:T[i][0]+2*T[i][1] for i in vs}
            for (i,j),m in zip(es,T[n:]):
                if i in d and j in d:d[i]+=m;d[j]+=m
            if min(d.values())>=3:return vs
    return None

if __name__=='__main__':
    import time
    n=int(sys.argv[1]);out=Path(__file__).parent/'proofs';out.mkdir(exist_ok=True)
    cfg=out/f'templates-{n}.json'
    if not cfg.exists():cfg.write_text(json.dumps(templates(n)))
    ts=[tuple(tuple(x) for x in T[:n])+tuple(T[n:]) for T in json.loads(cfg.read_text())]
    lo,hi=(map(int,sys.argv[2:4]) if len(sys.argv)>3 else (0,len(ts)))
    print('templates',len(ts),flush=True)
    for i in range(lo,min(hi,len(ts))):
        file=out/f'{n}-{i}.json'
        if file.exists() and json.loads(file.read_text()).get('ok'):continue
        red=smaller(n,ts[i]);st=time.time()
        if red is not None:
            o={'n':n,'template':ts[i],'ok':True,'reduce':red}
        else:
            t=Template(n,ts[i]);ok=t.process(t.initial)
            o={'n':n,'template':ts[i],'ok':ok,'states':len(t.cache),'counts':t.count,'maxlen':t.maxlen,'proof':t.certificate}
        file.write_text(json.dumps(o,separators=(',',':')))
        print(i,o['ok'],o.get('states','reduced'),round(time.time()-st,2),flush=True)
