#!/usr/bin/env python3
"""Randomized exact-arithmetic regressions, not proof or exhaustive census."""
from fractions import Fraction
from random import Random

def sig(matrix):
    z=[list(map(Fraction,row)) for row in matrix]
    result=0
    while z:
        n=len(z)
        for i in range(n):
            if z[i][i]:
                p=z[i][i]
                result += 1 if p>0 else -1
                z=[[z[u][v]-z[u][i]*z[i][v]/p for v in range(n) if v!=i]
                        for u in range(n) if u!=i]
                break
        else:
            e=next(((u,v) for u in range(n) for v in range(u+1,n) if z[u][v]),None)
            if e is None: break
            i,j=e
            p=z[i][j]
            z=[[z[u][v]-(z[u][i]*z[j][v]+z[u][j]*z[i][v])/p
                     for v in range(n) if v not in e]
                     for u in range(n) if u not in e]
    return result

def graph(k,edges,paths,branches):
    nxt=k
    result=[]
    for (u,v),parts in zip(edges,paths):
        row=[u,*range(nxt,nxt+len(parts)),v]
        result += list(zip(row,row[1:]))
        nxt+=len(parts)
        for r,children in zip(row[1:-1],parts):
            for t in children:
                new=list(range(nxt,nxt+len(t)))
                result.append((r,new[0]))
                result.extend((new[i],new[p]) for i,p in enumerate(t) if i)
                nxt+=len(t)
    for r,children in enumerate(branches):
        for t in children:
            new=list(range(nxt,nxt+len(t)))
            result.append((r,new[0]))
            result.extend((new[i],new[p]) for i,p in enumerate(t) if i)
            nxt+=len(t)
    assert all(u!=v for u,v in result)
    assert len(result)==len(set(map(frozenset,result)))
    return nxt,result

def sig_mtex(n,edges):
    z=[[0]*n for _ in range(n)]
    for i in range(n):z[i][i]=-2
    for u,v in edges:
        z[u][u]+=1;z[v][v]+=1;z[u][v]+=1;z[v][u]+=1
    return sig(z)

def compressed(c,edges,n,mark,states):
    d=[0]*n;P=[[0]*n for _ in range(n)]
    todo=[]
    for (u,v),(has_internal,s) in zip(edges,states):
        d[u]+=1;d[v]+=1
        if has_internal:todo.append((u,v,s))
        else:P[u][v]+=s;P[v][u]+=s
    for i in range(n):P[i][i]+=d[i]-2+2*mark[i]
    for u,v,s in todo:
        for row in P:row.append(0)
        P.append([0]*len(P[0]))
        i=len(P)-1
        P[i][u]+=1;P[u][i]+=1
        P[i][v]+=s;P[v][i]+=s
    return sig(P)-sum(mark)

def tree_state(parents):
    d=len(parents)
    child=[[] for _ in range(d)]
    for i,p in enumerate(parents):
        if i:child[p].append(i)
    out=[]
    for c in child:out.append(None)
    for i in range(d-1,-1,-1):
        terms=[out[j] for j in child[i]]
        a=len(terms)-1-sum(s for _,s in terms)
        rho=1/Fraction(a)
        S=sum(t for t,_ in terms)+(1 if a>0 else -1)
        assert S<=0 and (S!=0 or rho==1) and (S!=-1 or rho>=-1)
        out[i]=(S,rho)
    return out[0]

def decoration(ts):
    return sum(tree_state(t)[0]==-1 for t in ts)==1

def short(k,edges,paths,branches):
    mark=list(map(decoration,branches))
    types=[]
    for (u,v),parts in zip(edges,paths):
        w=list(map(decoration,parts))
        s=1
        while True:
            a=next((i for i in range(len(w)-2) if w[i] and not w[i+1]),-1)
            if a<0:break
            w=w[:a]+[not w[a+2]]+w[a+3:]
            s=-s
        a=next((i for i,x in enumerate(w) if x),len(w))
        s*=(-1)**(a//2);w=w[2*(a//2):]
        if True in w:
            b=w.count(True)
            l=not w[0];r=not w[-1]
            s*=(-1)**(b-1)
            if l:
                mark[u]=not mark[u]
                w=[False] if r else []
            elif r:
                mark[v]=not mark[v]
                w=[]
            else:
                w=[]
            s=-s
        assert len(w)<=1 and True not in w
        types.append((bool(w),s))
    return mark,types

def candidate_graph(k,edges,marks,states):
    # Direct +, direct -, internal +, internal - require respectively
    # path lengths 5,3,6,4 to be usable even on parallel edges and loops.
    paths=[[[]]*(2+2*(s==1)+internal) for internal,s in states]
    branches=[[(None,)] if marked else [] for marked in marks]
    return graph(k,edges,paths,branches)

def ran_case(rng):
    ks=[
        (1,[(0,0),(0,0)]),
        (2,[(0,1),(0,1),(0,1)]),
        (2,[(0,0),(0,1),(1,1)]),
        (4,[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]),
        (4,[(0,0),(0,1),(1,2),(1,2),(2,3),(3,3)]),
    ]
    def rooted():
        s=rng.randrange(1,5)
        return (None,*(rng.randrange(i) for i in range(1,s)))
    def forest():
        x=rng.randrange(10)
        return [] if x<5 else [rooted() for _ in range(1+(x>=9))]
    k,e=rng.choice(ks);c=len(e)-k+1
    p=[[forest() for _ in range(rng.randrange(2,6))] for _ in e]
    b=[forest() for _ in range(k)]
    n,g=graph(k,e,p,b)
    prev=sig_mtex(n,g)
    marks,states=short(k,e,p,b)
    newn,newg=candidate_graph(k,e,marks,states)
    m=compressed(c,e,k,marks,states)
    assert len(newg)-newn==c-1
    assert newn<=19*(c-1)
    assert m==sig_mtex(newn,newg)
    assert m>=prev,(k,e,p,b,marks,states,m,prev)
    return n,newn

if __name__=='__main__':
    rng=Random(20261126)
    s=[ran_case(rng) for _ in range(125)]
    print("125 deterministic decorated paths and pendant forests: all exact normal-form comparisons passed.")
    print("Order limits of sampled original and reconstructed graphs:",max(n for n,_ in s),max(n for _,n in s))
