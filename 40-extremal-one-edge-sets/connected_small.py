from itertools import combinations, permutations, product
from fractions import Fraction as Q
from collections import defaultdict
from verify import brute
from verify_connected import W,mean

def canonical(A):
    n=len(A)
    adj=[sum(1<<v for v in x) for x in A]
    colors=[len(x) for x in A]
    while True:
        ks=[(colors[u],tuple(sorted(colors[v] for v in A[u]))) for u in range(n)]
        lab={x:i for i,x in enumerate(sorted(set(ks)))}
        refined=[lab[x] for x in ks]
        if len(set(colors))==len(lab):
            colors=refined;break
        colors=refined
    blocks=[[v for v,x in enumerate(colors) if x==j] for j in range(max(colors)+1)]
    best=None
    for blocks_perm in product(*(permutations(b) for b in blocks)):
        perm=sum(blocks_perm,())
        code=sum((adj[v]>>u & 1)<<((j*(j-1))//2+i) for j,v in enumerate(perm) for i,u in enumerate(perm[:j]))
        if best is None or code<best: best=code
    return best

def advance(gs):
    out={}
    for A in gs:
        n=len(A)
        for mask in range(1,1<<n):
            B=[l[:] for l in A]+[[]]
            for v in range(n):
                if mask>>v&1:
                    B[v].append(n);B[n].append(v)
            out.setdefault(canonical(B),B)
    return out

if __name__=='__main__':
    G={0:[[]]}
    for n in range(2,8):
        G=advance(G.values())
        assert len(G)==[1,2,6,21,112,853][n-2]
        vals=defaultdict(list)
        for i,A in G.items():
            c,s=brute(A)[1];vals[Q(s,c)].append((i,A))
        best=max(vals)
        print('n =',n,'graphs =',len(G),'max =',best,'maximizers =',[t[1] for t in vals[best]],flush=True)
    for n in (8,9):
        vals={ (r,t):mean(n,1,r,t) for r in (1,2) for t in range(r+1)}
        print('n =',n,'candidate values',vals)
