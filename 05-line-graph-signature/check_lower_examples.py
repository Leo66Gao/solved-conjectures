#!/usr/bin/env python3
"""Independently reconstruct the published cycles-in-a-chain lower examples."""
from check_normal_form import sig

for c in range(1,8):
    edges=[]
    tail=None
    n=0
    for i in range(c):
        cycle_length=5 if i%2==0 else 4
        edges.extend((n+j,n+(j+1)%cycle_length) for j in range(cycle_length))
        if tail is not None:edges.append((tail,n))
        tail=n+1
        n+=cycle_length
    m=len(edges)
    assert m-n+1==c
    edge_sets=list(map(frozenset,edges))
    assert len(set(edge_sets))==m and all(len(e)==2 for e in edge_sets)
    invert=[[int(i!=j and bool(edge_sets[i]&edge_sets[j])) for j in range(m)] for i in range(m)]
    score=sig(invert)
    assert score==(c+1)//2
    print(f'c={c}, order={n}, size={m}, line-graph signature={score}')
