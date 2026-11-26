#!/usr/bin/env python3
"""Standalone exact certificate verifier. Only Python standard library. No cycle search."""
import gzip,ast,itertools,json,pathlib,sys
from functools import lru_cache
from collections import Counter
Z=tuple

def gcd_steps(a,b):
    if b==0:return (abs(a),1 if a>=0 else -1,0)
    g,x,y=gcd_steps(b,a%b)
    return g,y,x-(a//b)*y

def add(x,y,f=1):return tuple(a+f*b for a,b in zip(x,y))

def hnf(rows,dim):
    # Row lattice, pivot = last nonzero column, ascending pivot columns.
    if not rows or dim==0:return ()
    j=dim-1
    allrows=[tuple(x) for x in rows]
    k=next((i for i,r in enumerate(allrows) if r[j]),None)
    if k is None:return hnf(allrows,j)
    p=allrows.pop(k)
    if p[j]<0:p=tuple(-x for x in p)
    out=[]
    for q in allrows:
        if not q[j]:
            out.append(q);continue
        a,b=p[j],q[j]
        g,u,v=gcd_steps(a,b)
        n=tuple(u*x+v*y for x,y in zip(p,q))
        out.append(tuple((-b//g)*x+(a//g)*y for x,y in zip(p,q)))
        p=n
    inner=hnf(out,j)
    return (*inner,remainder(p,inner))

def remainder(v,H):
    for r in H[::-1]:
        i=next(i for i in reversed(range(len(r))) if r[i])
        v=add(v,r,-(v[i]//r[i]))
    return v

def all_templates(n):
    # Enumerate symmetric off-diagonal degree data row-by-row; loops contribute 2,
    # half-loops 1. Retain only deletion-minimal connected representatives.
    es=list(itertools.combinations(range(n),2))
    P=list(itertools.permutations(range(n)))
    ix=[tuple(es.index(tuple(sorted((p[i],p[j])))) for i,j in es) for p in P]
    result=set()
    for off in itertools.product(range(4),repeat=len(es)):
        deg=[0]*n;adj=[set() for i in deg]
        for m,(i,j) in zip(off,es):
            deg[i]+=m;deg[j]+=m
            if m:adj[i].add(j);adj[j].add(i)
        reached={0};work=[0]
        while work:
            v=work.pop()
            for w in adj[v]-reached:work.append(w);reached.add(w)
        if len(reached)!=n:continue
        opts=[]
        for d in deg:
            opts.append([(s,p) for s in range(4) for p in range(3) if d+s+2*p>=3 and (s==0 or d+s+2*p==3) and (p==0 or d+s+2*p<=4)])
        for local in itertools.product(*opts):
            ds=[d+s+2*p for d,(s,p) in zip(deg,local)]
            if any(ds[i]>=4 and ds[j]>=4 and off[h] for h,(i,j) in enumerate(es)):continue
            t=min(tuple(local[j] for j in p)+tuple(off[q] for q in x) for p,x in zip(P,ix))
            result.add(t)
    return result

def normalize_template(raw,n):
    return tuple(tuple(r) for r in raw[:n])+tuple(raw[n:])

def validate(D):
    n=D['n'];T=normalize_template(D['template'],n)
    es=list(itertools.combinations(range(n),2))
    if 'reduce' in D:
        v=D['reduce'];assert len(set(v))==len(v) and 1<=len(v)<n and all(0<=i<n for i in v)
        d={i:T[i][0]+2*T[i][1] for i in v}
        for (i,j),m in zip(es,T[n:]):
            if i in d and j in d:d[i]+=m;d[j]+=m
        assert min(d.values())>=3
        return T,Counter(),0
    ports=[[] for i in range(n)]
    label=0;comp=[{i} for i in range(n)]
    for k,(i,j) in enumerate(es):
        for _ in range(T[n+k]):
            A=next(C for C in comp if i in C);B=next(C for C in comp if j in C)
            if A!=B:A.update(B);comp.remove(B);l=0
            else:label+=1;l=label
            ports[i].append((j,l));ports[j].append((i,-l))
    invols=[]
    for i in range(n):
        for _ in range(T[i][0]):label+=1;ports[i].append((i,label));invols.append(label)
        for _ in range(T[i][1]):label+=1;ports[i]+=[(i,label),(i,-label)]
    z=(0,)*label
    def unit(k):return tuple((1 if k>0 else -1) if abs(k)==i+1 else 0 for i in range(label))
    initial=hnf([tuple(2*x for x in unit(k)) for k in invols],label)
    data={ast.literal_eval(k):v for k,v in D['proof'].items()}
    visited=set();active=set();lengths=Counter();leaves=0
    def walk(H):
        nonlocal leaves
        if H in visited:return
        assert H not in active and H in data
        active.add(H)
        R=lambda x:remainder(x,H)
        net=[[(j,R(unit(l))) for j,l in layer] for layer in ports]
        c=data[H]
        if c is None:
            assert any((i,z) in row or len(set(row))<len(row) for i,row in enumerate(net))
            leaves+=1
        else:
            assert isinstance(c,list) and len(c) in {4,8,16,32,64}
            cycle=[(i,tuple(v)) for i,v in c]
            assert len(cycle)==len(set(cycle))
            for (i,v),(j,w) in zip(cycle,cycle[1:]+cycle[:1]):
                assert 0<=i<n and len(v)==label and R(v)==v
                assert (j,R(add(w,v,-1))) in net[i]
            lengths[len(c)]+=1
            for (i,v),(j,w) in itertools.combinations(cycle,2):
                if i!=j:continue
                X=hnf([*H,add(v,w,-1)],label)
                assert H!=X
                walk(X)
        active.remove(H);visited.add(H)
    walk(initial)
    assert len(visited)==len(data)
    return T,lengths,leaves

if __name__=='__main__':
    assert __debug__, "Run without -O"
    path=pathlib.Path(__file__).parent
    packed=json.loads(gzip.decompress((path/'certificates.json.gz').read_bytes()))
    for n in range(1,(int(sys.argv[1]) if len(sys.argv)>1 else 6)+1):
        if n>=6:
            from complete import catalogue
            E=catalogue(n)
        else:E=all_templates(n)
        W=set();lst=Counter();leaves=0
        for D in packed[str(n)]:
            t,cs,c=validate(D)
            if n==6 and 32 in cs:
                assert t[:6]==((0,0),)*6
                M=t[6:];es=list(itertools.combinations(range(6),2))
                assert all(m==int((i<3)!=(j<3)) for (i,j),m in zip(es,M))
            assert set(cs)<=({4} if n==1 else {4,8,16} if n<=5 else {4,8,16,32})
            assert t not in W;W.add(t);lst+=cs;leaves+=c
        assert E==W,(len(E-W),len(W-E))
        print('orbits',n,'templates',len(W),'cycles by length',dict(sorted(lst.items())),'invalid leaves',leaves)
